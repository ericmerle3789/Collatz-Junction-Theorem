"""
FunSearch-style evolutionary loop for the Collatz Junction Theorem.

Inspired by Romera-Paredes et al. (2024) "Mathematical discoveries from program
search with large language models", this module implements a deterministic
evolutionary engine that searches for tighter bounds on the Range Exclusion
argument for the Collatz no-nontrivial-cycle problem.

Core mathematical context
-------------------------
For cycle length k, define:
    S(k)     = ceil(k * log2(3))
    d(k)     = 2^S(k) - 3^k
    corrSum  in [cs_min, cs_max]   for monotone compositions of S(k)
    range/d  = O(3^{-0.415 k})    --> 0   (Range Exclusion)

The engine maintains islands of candidate bound-functions, evaluates them
against ground truth for k = 3..200, applies deterministic mutation operators,
and reports the tightest bounds discovered after N generations.

Usage
-----
    python funsearch_loop.py              # runs demo evolution (20 generations)
    python funsearch_loop.py --gens 50    # custom generation count

Author : Eric Merle  (FunSearch adaptation for Collatz Junction Theorem)
License: MIT
"""

from __future__ import annotations

import math
import random
import copy
import argparse
import time
from dataclasses import dataclass, field
from typing import Callable, List, Dict, Optional, Tuple, Any
from functools import lru_cache

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

LOG2_3 = math.log2(3)
"""log2(3) ~ 1.58496..., the fundamental constant linking binary and ternary."""

BASELINE_DECAY = 0.41503749927884376
"""Known decay exponent: range/d ~ 3^{-0.415 k}."""

ISLAND_NAMES = [
    "upper_bound",          # Island 1 : upper bounds on range/d
    "fractional_part",      # Island 2 : lower bounds on {cs_max / d}
    "structural_constraint", # Island 3 : structural constraints on compositions
    "prime_exclusion",      # Island 4 : prime-based exclusion criteria
]

# ---------------------------------------------------------------------------
# Ground-truth arithmetic (exact, using Python arbitrary precision)
# ---------------------------------------------------------------------------


@lru_cache(maxsize=512)
def compute_S(k: int) -> int:
    """Return S(k) = ceil(k * log2(3)), the minimal total shift for cycle length k."""
    return math.ceil(k * LOG2_3)


@lru_cache(maxsize=512)
def compute_d(k: int) -> int:
    """Return d(k) = 2^S(k) - 3^k, the deficit that must absorb corrSum."""
    return 2 ** compute_S(k) - 3 ** k


@lru_cache(maxsize=512)
def compute_range(k: int) -> int:
    """
    Return the width of the corrSum interval: cs_max - cs_min.

    For a monotone composition of S(k) into k parts (each >= 2),
    the range equals 3^r + 1 - 2^{r+1} where r = S(k) - k.
    """
    S = compute_S(k)
    r = S - k
    return 3 ** r + 1 - 2 ** (r + 1)


@lru_cache(maxsize=512)
def compute_cs_max(k: int) -> int:
    """
    Maximum corrSum over all valid compositions.

    cs_max = 3^k + 3^{S mod k} - 2.
    """
    S = compute_S(k)
    r = S % k
    return 3 ** k + 3 ** r - 2


@lru_cache(maxsize=512)
def compute_cs_min(k: int) -> int:
    """
    Minimum corrSum over all valid compositions.

    cs_min = 3^k - 3 + 2^{r+1} where r = S(k) - k.
    """
    S = compute_S(k)
    r = S - k
    return 3 ** k - 3 + 2 ** (r + 1)


def compute_ratio(k: int) -> float:
    """Return range(k) / d(k), the key quantity that must vanish."""
    d = compute_d(k)
    if d == 0:
        return float("inf")
    return float(compute_range(k)) / float(d)


def _smallest_prime_factor(n: int) -> int:
    """Return the smallest prime factor of n, or n itself if prime."""
    if n < 2:
        return n
    if n % 2 == 0:
        return 2
    i = 3
    while i * i <= n:
        if n % i == 0:
            return i
        i += 2
    return n


def _continued_fraction_convergents(alpha: float, depth: int = 20) -> List[Tuple[int, int]]:
    """
    Return the first `depth` convergents p/q of `alpha` as (p, q) pairs.
    Used to detect when k sits near a convergent denominator of log2(3).
    """
    convergents: List[Tuple[int, int]] = []
    a = int(math.floor(alpha))
    p_prev, p_curr = 1, a
    q_prev, q_curr = 0, 1
    convergents.append((p_curr, q_curr))
    remainder = alpha - a
    for _ in range(depth - 1):
        if abs(remainder) < 1e-14:
            break
        remainder = 1.0 / remainder
        a = int(math.floor(remainder))
        p_prev, p_curr = p_curr, a * p_curr + p_prev
        q_prev, q_curr = q_curr, a * q_curr + q_prev
        convergents.append((p_curr, q_curr))
        remainder -= a
    return convergents


# Pre-compute convergent denominators of log2(3) for CF-aware mutations
_CF_CONVERGENTS = _continued_fraction_convergents(LOG2_3, depth=30)
CF_DENOMINATORS = {q for _, q in _CF_CONVERGENTS}
"""Set of convergent denominators of log2(3): {1,1,2,5,12,41,53,...}."""


# ---------------------------------------------------------------------------
# Candidate and EvaluationResult data structures
# ---------------------------------------------------------------------------


@dataclass
class Candidate:
    """
    A candidate bound-function in the evolutionary population.

    Attributes
    ----------
    name : str
        Short unique identifier.
    description : str
        Human-readable description of what this candidate computes.
    island : str
        Which island this candidate belongs to (one of ISLAND_NAMES).
    func : Callable[[int], float]
        The bound function: takes k, returns a numeric value.
    score : float
        Fitness score assigned by the evaluator (higher is better).
    generation : int
        Generation in which this candidate was created.
    parent : Optional[str]
        Name of the parent candidate, if any.
    mutation : str
        Which mutation operator produced this candidate.
    """

    name: str
    description: str
    island: str
    func: Callable[[int], float]
    score: float = 0.0
    generation: int = 0
    parent: Optional[str] = None
    mutation: str = "seed"

    def __repr__(self) -> str:
        return (
            f"Candidate(name={self.name!r}, island={self.island!r}, "
            f"score={self.score:.4f}, gen={self.generation})"
        )


@dataclass
class EvaluationResult:
    """
    Result of evaluating a candidate against ground truth for k in [k_lo, k_hi].

    Attributes
    ----------
    candidate : Candidate
        The evaluated candidate.
    correct_count : int
        Number of k values where the candidate gives a valid (correct) answer.
    wrong_count : int
        Number of k values where the candidate gives a wrong/invalid answer.
    tightness : float
        Average improvement ratio vs. baseline (>1 means tighter than baseline).
    detail : Dict[int, bool]
        Per-k correctness map.
    """

    candidate: Candidate
    correct_count: int = 0
    wrong_count: int = 0
    tightness: float = 0.0
    detail: Dict[int, bool] = field(default_factory=dict)


# ---------------------------------------------------------------------------
# Mutation operators
# ---------------------------------------------------------------------------


def _mutate_scale_exponent(
    cand: Candidate, gen: int, rng: random.Random
) -> Candidate:
    """
    Mutation 1: Scale exponent.

    Replace the baseline decay constant 0.415 with a nearby value drawn
    uniformly from [0.40, 0.45]. The resulting candidate tests whether a
    slightly different exponential decay better fits range/d.
    """
    new_exp = rng.uniform(0.40, 0.45)
    desc = f"range/d ~ 3^{{-{new_exp:.4f} k}}"

    def bound_func(k: int, _exp=new_exp) -> float:
        return 3.0 ** (-_exp * k)

    return Candidate(
        name=f"scale_exp_{new_exp:.4f}_g{gen}",
        description=desc,
        island="upper_bound",
        func=bound_func,
        generation=gen,
        parent=cand.name,
        mutation="scale_exponent",
    )


def _mutate_log_correction(
    cand: Candidate, gen: int, rng: random.Random
) -> Candidate:
    """
    Mutation 2: Add logarithmic correction.

    Transform f(k) -> f(k) * (1 + c / log(k)) for a random constant c in
    [-0.5, 0.5]. This captures sub-exponential corrections that may appear
    in the exact ratio.
    """
    c = rng.uniform(-0.5, 0.5)
    parent_func = cand.func
    desc = f"{cand.description} * (1 + {c:.3f}/log(k))"

    def bound_func(k: int, _c=c, _pf=parent_func) -> float:
        base = _pf(k)
        log_k = math.log(max(k, 2))
        return base * (1.0 + _c / log_k)

    return Candidate(
        name=f"logcorr_{c:.3f}_g{gen}",
        description=desc,
        island=cand.island,
        func=bound_func,
        generation=gen,
        parent=cand.name,
        mutation="log_correction",
    )


def _mutate_polynomial_correction(
    cand: Candidate, gen: int, rng: random.Random
) -> Candidate:
    """
    Mutation 3: Polynomial correction.

    Transform f(k) -> f(k) + c * k^a for random c in [-0.01, 0.01] and
    a in {-2, -1, -0.5, 0.5, 1}. Probes polynomial-order corrections.
    """
    c = rng.uniform(-0.01, 0.01)
    a = rng.choice([-2.0, -1.0, -0.5, 0.5, 1.0])
    parent_func = cand.func
    desc = f"{cand.description} + {c:.4f}*k^{a}"

    def bound_func(k: int, _c=c, _a=a, _pf=parent_func) -> float:
        return _pf(k) + _c * (k ** _a)

    return Candidate(
        name=f"polycorr_{c:.4f}_k{a}_g{gen}",
        description=desc,
        island=cand.island,
        func=bound_func,
        generation=gen,
        parent=cand.name,
        mutation="polynomial_correction",
    )


def _mutate_modular_twist(
    cand: Candidate, gen: int, rng: random.Random
) -> Candidate:
    """
    Mutation 4: Modular twist.

    Evaluate d(k) mod p for a small prime p and check whether the residue
    class constrains corrSum membership. Returns the fraction of k-values
    where d(k) mod p excludes at least one residue class of corrSum.
    """
    p = rng.choice([3, 5, 7, 11, 13, 17, 19, 23, 29, 31])
    desc = f"prime exclusion mod {p}: fraction of k where d(k) mod {p} excludes corrSum"

    def bound_func(k: int, _p=p) -> float:
        d = compute_d(k)
        if d == 0:
            return 0.0
        d_mod = d % _p
        # The corrSum range spans at most range(k) values.
        # If range(k) < d, then corrSum mod d occupies range/d fraction.
        # Modular exclusion: if range(k) mod p < p, some residues are excluded.
        r = compute_range(k)
        r_mod = r % _p
        # Fraction of residue classes that could contain corrSum mod p
        if _p == 0:
            return 0.0
        coverage = min(r_mod + 1, _p) / _p
        return 1.0 - coverage  # exclusion fraction

    return Candidate(
        name=f"modtwist_p{p}_g{gen}",
        description=desc,
        island="prime_exclusion",
        func=bound_func,
        generation=gen,
        parent=cand.name,
        mutation="modular_twist",
    )


def _mutate_cf_aware(
    cand: Candidate, gen: int, rng: random.Random
) -> Candidate:
    """
    Mutation 5: Continued-fraction aware weighting.

    Use the distance of k from the nearest convergent denominator of log2(3)
    to adjust the bound. Near convergent denominators, S(k)/k is very close
    to log2(3) and d(k) is anomalously small, so the ratio range/d may spike.
    """
    weight = rng.uniform(0.5, 2.0)
    parent_func = cand.func
    desc = f"{cand.description} * CF-weight({weight:.2f})"

    def bound_func(k: int, _w=weight, _pf=parent_func) -> float:
        base = _pf(k)
        # Distance to nearest convergent denominator
        min_dist = min(abs(k - q) for q in CF_DENOMINATORS if q > 0)
        # Near a convergent: boost the bound (ratio may be larger)
        cf_factor = 1.0 + _w / (1.0 + min_dist)
        return base * cf_factor

    return Candidate(
        name=f"cfaware_{weight:.2f}_g{gen}",
        description=desc,
        island=cand.island,
        func=bound_func,
        generation=gen,
        parent=cand.name,
        mutation="cf_aware",
    )


def _mutate_crossover(
    cand_a: Candidate, cand_b: Candidate, gen: int, rng: random.Random
) -> Candidate:
    """
    Mutation 6: Crossover.

    Combine two parent candidates by taking a weighted average of their
    outputs. The weight alpha is drawn from [0.2, 0.8] to avoid trivial
    copies.
    """
    alpha = rng.uniform(0.2, 0.8)
    fa, fb = cand_a.func, cand_b.func
    desc = f"crossover({alpha:.2f}*{cand_a.name}, {1-alpha:.2f}*{cand_b.name})"

    def bound_func(k: int, _a=alpha, _fa=fa, _fb=fb) -> float:
        return _a * _fa(k) + (1.0 - _a) * _fb(k)

    island = cand_a.island if rng.random() < 0.5 else cand_b.island

    return Candidate(
        name=f"cross_{alpha:.2f}_g{gen}",
        description=desc,
        island=island,
        func=bound_func,
        generation=gen,
        parent=f"{cand_a.name}+{cand_b.name}",
        mutation="crossover",
    )


def _mutate_diophantine_refinement(
    cand: Candidate, gen: int, rng: random.Random
) -> Candidate:
    """
    Mutation 7: Diophantine refinement.

    Use the three-distance theorem insight: for the fractional parts
    {j * log2(3)} the gap structure constrains which compositions are
    reachable. This mutation adjusts the bound by a factor derived from
    the three-distance distribution.
    """
    shift = rng.uniform(-0.1, 0.1)
    parent_func = cand.func
    desc = f"{cand.description} * 3-distance-factor(shift={shift:.3f})"

    def bound_func(k: int, _s=shift, _pf=parent_func) -> float:
        base = _pf(k)
        # Fractional part of k * log2(3)
        frac = (k * LOG2_3) - math.floor(k * LOG2_3)
        # Three-distance factor: closer to 0 or 1 means tighter constraint
        gap_factor = 1.0 - 2.0 * abs(frac - 0.5)  # in [0, 1]
        return base * (1.0 + _s * gap_factor)

    return Candidate(
        name=f"dioph_{shift:.3f}_g{gen}",
        description=desc,
        island=cand.island,
        func=bound_func,
        generation=gen,
        parent=cand.name,
        mutation="diophantine_refinement",
    )


def _mutate_residue_class_sieve(
    cand: Candidate, gen: int, rng: random.Random
) -> Candidate:
    """
    Mutation 8: Residue class sieve.

    For a random modulus m in {6,8,9,10,12}, check how the residue class
    of k modulo m constrains d(k) and hence the admissible corrSum range.
    Returns a refined bound that is island-aware.
    """
    m = rng.choice([6, 8, 9, 10, 12])
    parent_func = cand.func
    desc = f"{cand.description} * residue-sieve(mod {m})"

    def bound_func(k: int, _m=m, _pf=parent_func) -> float:
        base = _pf(k)
        r_class = k % _m
        # Heuristic: certain residue classes yield smaller d(k)
        # Penalize (increase bound) for classes near convergent-like behavior
        penalty = 1.0 + 0.05 * (1.0 if r_class in {0, 1, _m - 1} else 0.0)
        return base * penalty

    return Candidate(
        name=f"sieve_m{m}_g{gen}",
        description=desc,
        island=cand.island,
        func=bound_func,
        generation=gen,
        parent=cand.name,
        mutation="residue_class_sieve",
    )


# Registry of single-parent mutations
SINGLE_MUTATIONS = [
    _mutate_scale_exponent,
    _mutate_log_correction,
    _mutate_polynomial_correction,
    _mutate_modular_twist,
    _mutate_cf_aware,
    _mutate_diophantine_refinement,
    _mutate_residue_class_sieve,
]


# ---------------------------------------------------------------------------
# Seed (baseline) candidates
# ---------------------------------------------------------------------------


def _seed_upper_bound() -> Candidate:
    """Baseline upper bound: range(k) / d(k) using exact computation."""

    def func(k: int) -> float:
        return compute_ratio(k)

    return Candidate(
        name="baseline_range_over_d",
        description="Exact range(k)/d(k) ratio",
        island="upper_bound",
        func=func,
        mutation="seed",
    )


def _seed_exponential_fit() -> Candidate:
    """Exponential fit: 3^{-0.415 k} as analytic upper bound."""

    def func(k: int) -> float:
        return 3.0 ** (-BASELINE_DECAY * k)

    return Candidate(
        name="baseline_exp_decay",
        description=f"3^{{-{BASELINE_DECAY:.4f} k}} analytic decay",
        island="upper_bound",
        func=func,
        mutation="seed",
    )


def _seed_fractional_part() -> Candidate:
    """Baseline fractional part: (cs_max mod d) / d."""

    def func(k: int) -> float:
        d = compute_d(k)
        if d == 0:
            return 0.0
        cs = compute_cs_max(k)
        return float(cs % d) / float(d)

    return Candidate(
        name="baseline_frac_part",
        description="Exact {cs_max / d} fractional part",
        island="fractional_part",
        func=func,
        mutation="seed",
    )


def _seed_forced_flat() -> Candidate:
    """Forced plateau length: 2k - S(k), a structural constraint."""

    def func(k: int) -> float:
        return float(2 * k - compute_S(k))

    return Candidate(
        name="baseline_forced_flat",
        description="Forced plateau 2k - S(k)",
        island="structural_constraint",
        func=func,
        mutation="seed",
    )


def _seed_prime_factor() -> Candidate:
    """Smallest prime factor of d(k)."""

    def func(k: int) -> float:
        d = compute_d(k)
        if d <= 1:
            return 1.0
        return float(_smallest_prime_factor(d))

    return Candidate(
        name="baseline_spf",
        description="Smallest prime factor of d(k)",
        island="prime_exclusion",
        func=func,
        mutation="seed",
    )


def _seed_range_over_3k() -> Candidate:
    """Normalized range: range(k) / 3^k."""

    def func(k: int) -> float:
        return float(compute_range(k)) / float(3 ** k)

    return Candidate(
        name="baseline_range_norm",
        description="range(k) / 3^k normalization",
        island="upper_bound",
        func=func,
        mutation="seed",
    )


def _seed_structural_ratio() -> Candidate:
    """Ratio of forced flat length to k, measuring compositional freedom."""

    def func(k: int) -> float:
        forced = 2 * k - compute_S(k)
        return float(forced) / float(k)

    return Candidate(
        name="baseline_flat_ratio",
        description="(2k - S(k)) / k structural ratio",
        island="structural_constraint",
        func=func,
        mutation="seed",
    )


def _seed_prime_density() -> Candidate:
    """Count of distinct small prime factors of d(k) up to 100."""

    def func(k: int) -> float:
        d = compute_d(k)
        if d <= 1:
            return 0.0
        count = 0
        for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
                   53, 59, 61, 67, 71, 73, 79, 83, 89, 97]:
            if d % p == 0:
                count += 1
        return float(count)

    return Candidate(
        name="baseline_prime_density",
        description="Count of small prime factors of d(k)",
        island="prime_exclusion",
        func=func,
        mutation="seed",
    )


ALL_SEEDS = [
    _seed_upper_bound,
    _seed_exponential_fit,
    _seed_fractional_part,
    _seed_forced_flat,
    _seed_prime_factor,
    _seed_range_over_3k,
    _seed_structural_ratio,
    _seed_prime_density,
]


# ---------------------------------------------------------------------------
# FunSearch Engine
# ---------------------------------------------------------------------------


class FunSearchEngine:
    """
    FunSearch-style evolutionary engine for Collatz bound discovery.

    Maintains an island-model population of candidate bound-functions,
    evaluates them against exact ground truth, applies deterministic
    mutation operators, and evolves toward tighter bounds.

    Parameters
    ----------
    k_range : Tuple[int, int]
        Range of cycle lengths to evaluate (inclusive).
    population_size : int
        Maximum candidates per island.
    n_islands : int
        Number of islands (must match len(ISLAND_NAMES)).
    elite_fraction : float
        Fraction of top candidates preserved each generation.
    """

    def __init__(
        self,
        k_range: Tuple[int, int] = (3, 200),
        population_size: int = 50,
        n_islands: int = 4,
        elite_fraction: float = 0.3,
    ):
        self.k_lo, self.k_hi = k_range
        self.population_size = population_size
        self.n_islands = n_islands
        self.elite_fraction = elite_fraction

        # Pre-compute ground truth
        self._ground_truth: Dict[int, float] = {}
        for k in range(self.k_lo, self.k_hi + 1):
            self._ground_truth[k] = compute_ratio(k)

        # Islands: island_name -> list of candidates
        self.islands: Dict[str, List[Candidate]] = {
            name: [] for name in ISLAND_NAMES
        }

        # Hall of fame: best candidate ever per island
        self.hall_of_fame: Dict[str, Candidate] = {}

        # History for reporting
        self.generation_stats: List[Dict[str, Any]] = []

    def _seed_population(self) -> None:
        """Initialize islands with baseline candidates."""
        for seed_fn in ALL_SEEDS:
            cand = seed_fn()
            self.islands[cand.island].append(cand)

    def evaluate(self, candidate: Candidate) -> EvaluationResult:
        """
        Test a candidate against ground truth for all k in [k_lo, k_hi].

        Scoring depends on the island:
        - upper_bound: candidate should be >= actual ratio (valid upper bound)
          and as tight as possible.
        - fractional_part: candidate should be in [0, 1) and match exact value.
        - structural_constraint: candidate should be > 0 (positive constraint).
        - prime_exclusion: candidate should be > 1 (nontrivial factor / nonzero).

        Returns
        -------
        EvaluationResult
            Detailed evaluation with correctness counts and tightness.
        """
        result = EvaluationResult(candidate=candidate)
        tightness_sum = 0.0
        n_valid = 0

        for k in range(self.k_lo, self.k_hi + 1):
            try:
                val = candidate.func(k)
            except (ZeroDivisionError, ValueError, OverflowError):
                result.detail[k] = False
                result.wrong_count += 1
                continue

            if math.isnan(val) or math.isinf(val):
                result.detail[k] = False
                result.wrong_count += 1
                continue

            actual = self._ground_truth[k]
            correct = False

            if candidate.island == "upper_bound":
                # Valid if val >= actual (it is indeed an upper bound)
                # Tightness: how close val is to actual (ratio actual/val, closer to 1 is better)
                if val >= actual - 1e-15:
                    correct = True
                    if val > 1e-30:
                        tightness_sum += actual / val  # in (0, 1], higher = tighter
                    else:
                        tightness_sum += 0.0
                    n_valid += 1

            elif candidate.island == "fractional_part":
                # Valid if in [0, 1)
                if 0.0 <= val < 1.0:
                    correct = True
                    # Tightness: how close to the exact fractional part
                    d = compute_d(k)
                    if d > 0:
                        exact_frac = float(compute_cs_max(k) % d) / float(d)
                        tightness_sum += 1.0 - abs(val - exact_frac)
                    n_valid += 1

            elif candidate.island == "structural_constraint":
                # Valid if positive (meaningful constraint)
                if val > 0:
                    correct = True
                    tightness_sum += min(val / k, 1.0)  # normalized
                    n_valid += 1

            elif candidate.island == "prime_exclusion":
                # Valid if > 0 (nontrivial)
                if val > 0:
                    correct = True
                    tightness_sum += min(val / 100.0, 1.0)  # normalized
                    n_valid += 1

            result.detail[k] = correct
            if correct:
                result.correct_count += 1
            else:
                result.wrong_count += 1

        # Compute final tightness
        result.tightness = tightness_sum / max(n_valid, 1)

        # Composite score: correctness (dominant) + tightness (bonus)
        total_k = self.k_hi - self.k_lo + 1
        correctness_ratio = result.correct_count / total_k
        candidate.score = correctness_ratio * 0.7 + result.tightness * 0.3

        # Penalty for any wrong answers
        if result.wrong_count > 0:
            candidate.score *= max(0.0, 1.0 - 0.01 * result.wrong_count)

        return result

    def mutate(self, candidate: Candidate, gen: int, rng: random.Random) -> List[Candidate]:
        """
        Apply mutation operators to generate offspring from a single parent.

        Each call produces 1-3 offspring using randomly selected operators.

        Parameters
        ----------
        candidate : Candidate
            The parent candidate.
        gen : int
            Current generation number.
        rng : random.Random
            The RNG instance for reproducibility.

        Returns
        -------
        List[Candidate]
            List of offspring candidates.
        """
        n_offspring = rng.randint(1, 3)
        children: List[Candidate] = []

        for _ in range(n_offspring):
            op = rng.choice(SINGLE_MUTATIONS)
            try:
                child = op(candidate, gen, rng)
                children.append(child)
            except Exception:
                pass  # skip failed mutations silently

        return children

    def crossover(
        self, gen: int, rng: random.Random
    ) -> List[Candidate]:
        """
        Perform inter-island crossover between top candidates.

        Selects one candidate from each of two random islands and combines them.

        Returns
        -------
        List[Candidate]
            List of crossover offspring (0-2 candidates).
        """
        children: List[Candidate] = []
        populated = [
            name for name, pop in self.islands.items() if len(pop) >= 1
        ]
        if len(populated) < 2:
            return children

        island_a, island_b = rng.sample(populated, 2)
        cand_a = rng.choice(self.islands[island_a])
        cand_b = rng.choice(self.islands[island_b])

        try:
            child = _mutate_crossover(cand_a, cand_b, gen, rng)
            children.append(child)
        except Exception:
            pass

        return children

    def _select_and_trim(self) -> None:
        """Keep only the top candidates per island, up to population_size."""
        for name in ISLAND_NAMES:
            pop = self.islands[name]
            if not pop:
                continue
            # Sort by score descending
            pop.sort(key=lambda c: c.score, reverse=True)
            # Keep top population_size
            self.islands[name] = pop[: self.population_size]
            # Update hall of fame
            best = pop[0]
            if name not in self.hall_of_fame or best.score > self.hall_of_fame[name].score:
                self.hall_of_fame[name] = best

    def evolve(self, n_generations: int = 20, verbose: bool = True) -> List[Candidate]:
        """
        Run the full evolutionary loop.

        Parameters
        ----------
        n_generations : int
            Number of generations to evolve.
        verbose : bool
            Whether to print progress.

        Returns
        -------
        List[Candidate]
            The hall-of-fame candidates (best per island).
        """
        rng = random.Random(42)

        # Step 1: Seed the population
        self._seed_population()

        # Step 2: Evaluate seeds
        for name in ISLAND_NAMES:
            for cand in self.islands[name]:
                self.evaluate(cand)

        self._select_and_trim()

        if verbose:
            print("=" * 72)
            print("FunSearch Evolutionary Loop for Collatz Junction Theorem")
            print(f"  k range: [{self.k_lo}, {self.k_hi}]")
            print(f"  population/island: {self.population_size}")
            print(f"  generations: {n_generations}")
            print("=" * 72)
            print()
            self._print_generation_summary(0)

        # Step 3: Evolution
        for gen in range(1, n_generations + 1):
            new_candidates: List[Candidate] = []

            # Mutate top candidates from each island
            for name in ISLAND_NAMES:
                pop = self.islands[name]
                if not pop:
                    continue
                n_elite = max(1, int(len(pop) * self.elite_fraction))
                elites = pop[:n_elite]
                for elite in elites:
                    offspring = self.mutate(elite, gen, rng)
                    new_candidates.extend(offspring)

            # Crossover (2-4 per generation)
            n_cross = rng.randint(2, 4)
            for _ in range(n_cross):
                cross_children = self.crossover(gen, rng)
                new_candidates.extend(cross_children)

            # Evaluate all new candidates
            for cand in new_candidates:
                self.evaluate(cand)
                self.islands[cand.island].append(cand)

            # Selection
            self._select_and_trim()

            # Record stats
            gen_info = {
                "generation": gen,
                "new_candidates": len(new_candidates),
                "island_sizes": {
                    name: len(pop) for name, pop in self.islands.items()
                },
                "best_scores": {
                    name: pop[0].score if pop else 0.0
                    for name, pop in self.islands.items()
                },
            }
            self.generation_stats.append(gen_info)

            if verbose and (gen % 5 == 0 or gen == n_generations):
                self._print_generation_summary(gen)

        return list(self.hall_of_fame.values())

    def _print_generation_summary(self, gen: int) -> None:
        """Print a one-line-per-island summary for the given generation."""
        print(f"--- Generation {gen} ---")
        for name in ISLAND_NAMES:
            pop = self.islands[name]
            if pop:
                best = pop[0]
                print(
                    f"  {name:25s}  pop={len(pop):3d}  "
                    f"best={best.score:.4f}  ({best.name})"
                )
            else:
                print(f"  {name:25s}  pop=  0  (empty)")
        print()

    def report(self) -> str:
        """
        Generate a comprehensive human-readable report of findings.

        Returns
        -------
        str
            Multi-line report summarizing evolution results, best candidates
            per island, and any mathematical insights discovered.
        """
        lines: List[str] = []
        lines.append("=" * 72)
        lines.append("FUNSEARCH EVOLUTION REPORT - Collatz Junction Theorem")
        lines.append("=" * 72)
        lines.append("")
        lines.append(f"k range evaluated: [{self.k_lo}, {self.k_hi}]")
        lines.append(f"Total k values: {self.k_hi - self.k_lo + 1}")
        lines.append(f"Generations: {len(self.generation_stats)}")
        lines.append("")

        # Hall of fame
        lines.append("-" * 72)
        lines.append("HALL OF FAME (best candidate per island)")
        lines.append("-" * 72)
        for name in ISLAND_NAMES:
            lines.append(f"\n  Island: {name}")
            if name in self.hall_of_fame:
                best = self.hall_of_fame[name]
                result = self.evaluate(best)
                lines.append(f"    Name:        {best.name}")
                lines.append(f"    Description: {best.description}")
                lines.append(f"    Score:       {best.score:.6f}")
                lines.append(f"    Generation:  {best.generation}")
                lines.append(f"    Mutation:    {best.mutation}")
                lines.append(f"    Parent:      {best.parent or '(seed)'}")
                lines.append(f"    Correct:     {result.correct_count}/{self.k_hi - self.k_lo + 1}")
                lines.append(f"    Wrong:       {result.wrong_count}")
                lines.append(f"    Tightness:   {result.tightness:.6f}")
            else:
                lines.append("    (no candidate)")

        # Convergent denominator analysis
        lines.append("")
        lines.append("-" * 72)
        lines.append("CONVERGENT DENOMINATOR ANALYSIS")
        lines.append("-" * 72)
        cf_ks = sorted(q for q in CF_DENOMINATORS if self.k_lo <= q <= self.k_hi)
        if cf_ks:
            lines.append(f"  Convergent denominators in range: {cf_ks}")
            for k in cf_ks:
                ratio = compute_ratio(k)
                d = compute_d(k)
                lines.append(
                    f"    k={k:4d}  ratio={ratio:.6e}  d(k)={d}  "
                    f"spf={_smallest_prime_factor(d) if d > 1 else 'N/A'}"
                )
        else:
            lines.append("  No convergent denominators in range.")

        # Evolution trajectory
        lines.append("")
        lines.append("-" * 72)
        lines.append("EVOLUTION TRAJECTORY (best score per island over time)")
        lines.append("-" * 72)
        if self.generation_stats:
            header = f"  {'Gen':>4s}"
            for name in ISLAND_NAMES:
                short = name[:12]
                header += f"  {short:>12s}"
            lines.append(header)
            for gs in self.generation_stats:
                row = f"  {gs['generation']:4d}"
                for name in ISLAND_NAMES:
                    sc = gs["best_scores"].get(name, 0.0)
                    row += f"  {sc:12.4f}"
                lines.append(row)

        # Key mathematical observations
        lines.append("")
        lines.append("-" * 72)
        lines.append("KEY OBSERVATIONS")
        lines.append("-" * 72)

        # Check monotone decay of ratio
        ratios = [(k, compute_ratio(k)) for k in range(self.k_lo, self.k_hi + 1)]
        non_monotone = []
        for i in range(1, len(ratios)):
            if ratios[i][1] > ratios[i - 1][1]:
                non_monotone.append(ratios[i][0])
        lines.append(
            f"  Ratio range/d is non-monotone at {len(non_monotone)} values of k "
            f"(out of {len(ratios) - 1} consecutive pairs)."
        )
        if non_monotone and len(non_monotone) <= 20:
            lines.append(f"  Non-monotone k values: {non_monotone}")

        # Maximum ratio
        k_max, r_max = max(ratios, key=lambda x: x[1])
        lines.append(f"  Maximum ratio: {r_max:.6e} at k={k_max}")

        # Minimum ratio (excluding k where d=0)
        valid_ratios = [(k, r) for k, r in ratios if r < float("inf") and r > 0]
        if valid_ratios:
            k_min, r_min = min(valid_ratios, key=lambda x: x[1])
            lines.append(f"  Minimum nonzero ratio: {r_min:.6e} at k={k_min}")

        # Ratio below threshold for large k
        threshold = 0.01
        large_k_below = [
            k for k, r in ratios if k >= 50 and r < threshold
        ]
        lines.append(
            f"  For k >= 50: {len(large_k_below)} out of "
            f"{sum(1 for k, _ in ratios if k >= 50)} have ratio < {threshold}"
        )

        lines.append("")
        lines.append("=" * 72)
        lines.append("END OF REPORT")
        lines.append("=" * 72)

        return "\n".join(lines)


# ---------------------------------------------------------------------------
# Main entry point
# ---------------------------------------------------------------------------


def main() -> None:
    """
    Run a demo FunSearch evolution and print the report.

    Usage:
        python funsearch_loop.py [--gens N] [--pop N] [--kmax N]
    """
    parser = argparse.ArgumentParser(
        description="FunSearch evolutionary loop for Collatz Junction Theorem"
    )
    parser.add_argument(
        "--gens", type=int, default=20,
        help="Number of generations (default: 20)"
    )
    parser.add_argument(
        "--pop", type=int, default=50,
        help="Population size per island (default: 50)"
    )
    parser.add_argument(
        "--kmax", type=int, default=200,
        help="Maximum k to evaluate (default: 200)"
    )
    args = parser.parse_args()

    print(f"Starting FunSearch loop: {args.gens} generations, "
          f"pop={args.pop}, k in [3, {args.kmax}]")
    print()

    t0 = time.time()

    engine = FunSearchEngine(
        k_range=(3, args.kmax),
        population_size=args.pop,
    )

    best_candidates = engine.evolve(n_generations=args.gens, verbose=True)

    elapsed = time.time() - t0

    # Final report
    report = engine.report()
    print(report)
    print()
    print(f"Total elapsed time: {elapsed:.2f}s")

    # Summary of hall of fame
    print()
    print("Hall of Fame:")
    for cand in best_candidates:
        print(f"  [{cand.island}] {cand.name}: score={cand.score:.4f} (gen {cand.generation})")


if __name__ == "__main__":
    main()
