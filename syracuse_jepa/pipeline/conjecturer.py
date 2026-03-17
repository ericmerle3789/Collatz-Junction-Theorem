"""
Conjecturer — Pattern Discovery & Hypothesis Formulation

Takes Explorer data and discovers invariants, formulates them as
typed hypotheses that the Formalizer can translate to Lean 4.
"""

import math
from dataclasses import dataclass
from typing import List, Optional
from enum import Enum


class HypothesisType(Enum):
    """Types of hypotheses the conjecturer can produce."""
    AVOIDANCE = "avoidance"           # N_0(d(k)) = 0 for specific k
    AVOIDANCE_FAILS = "avoidance_fails"  # N_0 > 0 (phantom)
    EXACT_VALUE = "exact_value"       # corrSum(A, k) = V
    DIVISIBILITY = "divisibility"     # corrSum(A, k) % d = 0
    CLOSED_FORM = "closed_form"       # corrSum(A, k) = formula(k, v, r)
    PHANTOM = "phantom"               # specific composition is a phantom


class Confidence(Enum):
    """Confidence level of a hypothesis."""
    PROVEN = "proven"           # verified by Lean
    EXHAUSTIVE = "exhaustive"   # checked all cases computationally
    SAMPLED = "sampled"         # checked on sample
    CONJECTURED = "conjectured" # pattern-based guess


@dataclass
class Hypothesis:
    """A formal hypothesis ready for the Formalizer."""
    type: HypothesisType
    confidence: Confidence
    description: str
    # Parameters for Lean generation
    k: Optional[int] = None
    composition: Optional[list] = None
    expected_value: Optional[int] = None
    formula_params: Optional[dict] = None
    # Lean theorem name
    lean_name: Optional[str] = None

    def __repr__(self):
        return f"Hypothesis({self.type.value}, k={self.k}, conf={self.confidence.value})"


def discover_avoidance(exploration_results: list) -> List[Hypothesis]:
    """
    Pattern 1: For which k is N_0 = 0?
    If all compositions have been checked and N_0 = 0, emit an AVOIDANCE hypothesis.
    """
    hypotheses = []
    for r in exploration_results:
        if r['n_zero_residue'] == 0:
            hypotheses.append(Hypothesis(
                type=HypothesisType.AVOIDANCE,
                confidence=Confidence.EXHAUSTIVE,
                description=f"N₀(d({r['k']})) = 0: no monotone composition of "
                            f"S={r['S']} into {r['k']} parts has corrSum ≡ 0 mod {r['d']}",
                k=r['k'],
                lean_name=f"avoidance_k{r['k']}",
            ))
        elif r['n_zero_residue'] > 0:
            hypotheses.append(Hypothesis(
                type=HypothesisType.AVOIDANCE_FAILS,
                confidence=Confidence.EXHAUSTIVE,
                description=f"N₀(d({r['k']})) = {r['n_zero_residue']}: "
                            f"avoidance FAILS for k={r['k']}",
                k=r['k'],
                lean_name=f"avoidance_k{r['k']}_fails",
            ))
            # Also emit phantom hypotheses for each zero-residue composition
            for comp in r.get('zero_compositions', []):
                hypotheses.append(Hypothesis(
                    type=HypothesisType.PHANTOM,
                    confidence=Confidence.EXHAUSTIVE,
                    description=f"Phantom: corrSum({comp}, {r['k']}) ≡ 0 mod {r['d']}",
                    k=r['k'],
                    composition=comp,
                    lean_name=f"phantom_k{r['k']}",
                ))
        # else: n_zero_residue == -1, skipped (too many compositions)
    return hypotheses


def discover_closed_forms(exploration_results: list) -> List[Hypothesis]:
    """
    Pattern 2: Almost-flat closed form.
    For almost-flat A = (v,...,v, v+1,...,v+1):
      corrSum = 2^v * ((3^k - 1)/2 + (3^r - 1)/2)
    Verify this holds and emit hypothesis.
    """
    hypotheses = []
    for r in exploration_results:
        k = r['k']
        v = r['almost_flat_v']
        r_count = r['almost_flat_r']
        S = r['S']

        # Build the almost-flat composition
        if r_count == 0:
            comp = [v] * k
        else:
            comp = [v] * (k - r_count) + [v + 1] * r_count

        # Compute expected value from closed form
        T_k = (3**k - 1) // 2
        T_r = (3**r_count - 1) // 2 if r_count > 0 else 0
        expected = (1 << v) * (T_k + T_r)

        # Compute actual corrSum
        actual = sum(3**(k - 1 - i) * (1 << a) for i, a in enumerate(comp))

        if actual == expected:
            hypotheses.append(Hypothesis(
                type=HypothesisType.CLOSED_FORM,
                confidence=Confidence.EXHAUSTIVE,
                description=f"Almost-flat k={k}: corrSum({comp}) = "
                            f"2^{v} * (T_{k} + T_{r_count}) = {expected}",
                k=k,
                composition=comp,
                expected_value=expected,
                formula_params={'v': v, 'r': r_count, 'T_k': T_k, 'T_r': T_r},
                lean_name=f"almost_flat_k{k}",
            ))

    return hypotheses


def discover_exact_phantom_values(exploration_results: list) -> List[Hypothesis]:
    """
    Pattern 3: For phantoms, compute exact corrSum and show it equals m*d.
    """
    hypotheses = []
    for r in exploration_results:
        for comp in r.get('zero_compositions', []):
            k = r['k']
            d = r['d']
            cs = sum(3**(k - 1 - i) * (1 << a) for i, a in enumerate(comp))
            m = cs // d
            hypotheses.append(Hypothesis(
                type=HypothesisType.EXACT_VALUE,
                confidence=Confidence.EXHAUSTIVE,
                description=f"corrSum({comp}, {k}) = {cs} = {m} * {d}",
                k=k,
                composition=comp,
                expected_value=cs,
                formula_params={'m': m, 'd': d},
                lean_name=f"corrsum_phantom_k{k}_value",
            ))
            # Also: corrSum = m * d
            hypotheses.append(Hypothesis(
                type=HypothesisType.DIVISIBILITY,
                confidence=Confidence.EXHAUSTIVE,
                description=f"corrSum({comp}, {k}) = {m} * d({k})",
                k=k,
                composition=comp,
                expected_value=m,
                lean_name=f"phantom_is_{m}d_k{k}",
            ))
    return hypotheses


def discover_non_divisibility(exploration_results: list) -> List[Hypothesis]:
    """
    Pattern 4: For almost-flat compositions, check d ∤ (T_k + T_r).
    This is the key condition for the quasi-flat avoidance theory.
    """
    hypotheses = []
    for r in exploration_results:
        k = r['k']
        d = r['d']
        v = r['almost_flat_v']
        r_count = r['almost_flat_r']
        T_k = (3**k - 1) // 2
        T_r = (3**r_count - 1) // 2 if r_count > 0 else 0
        combined = T_k + T_r
        residue = combined % d

        if residue != 0 and r['n_zero_residue'] == 0:
            hypotheses.append(Hypothesis(
                type=HypothesisType.EXACT_VALUE,
                confidence=Confidence.EXHAUSTIVE,
                description=f"d({k}) ∤ (T_{k} + T_{r_count}): "
                            f"({T_k} + {T_r}) mod {d} = {residue} ≠ 0",
                k=k,
                expected_value=residue,
                formula_params={'T_k': T_k, 'T_r': T_r, 'combined': combined},
                lean_name=f"nondiv_k{k}",
            ))
    return hypotheses


def run_conjecturer(exploration_results: list) -> List[Hypothesis]:
    """
    Main conjecturer: run all pattern detectors and collect hypotheses.
    Returns hypotheses sorted by priority (avoidance first, then phantoms,
    then closed forms, then exact values).
    """
    print("=" * 70)
    print("  CONJECTURER — Discovering patterns")
    print("=" * 70)

    all_hypotheses = []

    # Pattern 1: Avoidance
    avoidance = discover_avoidance(exploration_results)
    print(f"  Avoidance hypotheses: {len(avoidance)}")
    n_pass = sum(1 for h in avoidance if h.type == HypothesisType.AVOIDANCE)
    n_fail = sum(1 for h in avoidance if h.type == HypothesisType.AVOIDANCE_FAILS)
    n_phantom = sum(1 for h in avoidance if h.type == HypothesisType.PHANTOM)
    print(f"    N₀=0: {n_pass},  N₀>0: {n_fail},  Phantoms: {n_phantom}")
    all_hypotheses.extend(avoidance)

    # Pattern 2: Closed forms
    closed = discover_closed_forms(exploration_results)
    print(f"  Closed form hypotheses: {len(closed)}")
    all_hypotheses.extend(closed)

    # Pattern 3: Phantom exact values
    phantoms = discover_exact_phantom_values(exploration_results)
    print(f"  Phantom value hypotheses: {len(phantoms)}")
    all_hypotheses.extend(phantoms)

    # Pattern 4: Non-divisibility
    nondiv = discover_non_divisibility(exploration_results)
    print(f"  Non-divisibility hypotheses: {len(nondiv)}")
    all_hypotheses.extend(nondiv)

    # Priority sort: AVOIDANCE > PHANTOM > CLOSED_FORM > EXACT_VALUE > DIVISIBILITY
    priority = {
        HypothesisType.AVOIDANCE: 0,
        HypothesisType.AVOIDANCE_FAILS: 1,
        HypothesisType.PHANTOM: 2,
        HypothesisType.CLOSED_FORM: 3,
        HypothesisType.DIVISIBILITY: 4,
        HypothesisType.EXACT_VALUE: 5,
    }
    all_hypotheses.sort(key=lambda h: (priority.get(h.type, 99), h.k or 0))

    print(f"\n  Total hypotheses: {len(all_hypotheses)}")
    return all_hypotheses
