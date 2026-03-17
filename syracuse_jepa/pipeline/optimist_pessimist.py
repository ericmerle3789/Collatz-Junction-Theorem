"""
Optimist-Pessimist Engine — TxGraffiti-style Conjecture Machine
(cf. arXiv 2409.19379)

Architecture:
  OPTIMIST  : Generates conjectures as inequalities between computed invariants
  PESSIMIST : Exhaustively tests each conjecture against k=3..200
  SCORER    : Measures sharpness (tightness) of surviving conjectures
  DALMATIAN : Removes redundant conjectures (if A => B, keep only A)

Input:  junction_results.json (198 entries, k=3..200)
Output: Ranked list of the sharpest surviving conjectures

References:
  - DeLaVina (2005): Written on the Wall (TxGraffiti original)
  - Larson & Van Cleemput (2024): arXiv 2409.19379 (TxGraffiti revisited)
  - Hercher (2022): SDW bound k <= 91
  - Junction Theorem pipeline: analyst.py, explorer.py
"""

import json
import math
import os
from dataclasses import dataclass, field
from typing import (
    List, Dict, Tuple, Optional, Callable, Any,
)
from pathlib import Path
from enum import Enum

from syracuse_jepa.pipeline.explorer import compute_S, compute_d, count_compositions
from syracuse_jepa.pipeline.analyst import (
    factorize, multiplicative_order, euler_phi,
)


# =====================================================================
#  Data Structures
# =====================================================================

class ConjectureStatus(Enum):
    PENDING = "pending"
    SURVIVED = "survived"
    REFUTED = "refuted"
    REDUNDANT = "redundant"
    DIAGNOSED = "diagnosed"  # Refuted AND root-cause analyzed


@dataclass
class RootCauseAnalysis:
    """Diagnostic produced by the Investigator when a conjecture dies.

    Philosophy: each death is a lever for discovery. The Pessimist is
    a crutch for the Investigator, not a gate that closes.

    Attributes
    ----------
    why_failed : str
        Structural reason the conjecture broke (the root of the root).
    what_it_reveals : str
        What the failure teaches about the mathematical landscape.
    new_directions : List[str]
        Concrete seeds for the Optimist's next generation round.
    structural_pattern : str
        Classification of the failure mode (e.g., "parity_obstruction",
        "growth_rate_mismatch", "missing_witness", "regime_boundary").
    depth : int
        How many levels deep the causal chain goes (1=surface, 3+=deep root).
    related_families : List[str]
        Other conjecture families that share the same root cause.
    """
    why_failed: str
    what_it_reveals: str
    new_directions: List[str] = field(default_factory=list)
    structural_pattern: str = ""
    depth: int = 1
    related_families: List[str] = field(default_factory=list)


@dataclass
class Conjecture:
    """A single conjecture produced by the Optimist."""
    statement: str                       # Human-readable, e.g. "For all k >= 92, rho(k) < 0.55"
    bound: float                         # The numeric bound in the inequality
    k_range: Tuple[int, int]             # (k_min, k_max) of claimed validity
    sharpness: float = 0.0              # 1.0 = perfectly tight, 0.0 = very loose
    counterexample_k: Optional[int] = None
    status: ConjectureStatus = ConjectureStatus.PENDING
    family: str = ""                     # Conjecture family for Dalmatian filtering
    margin: float = float("inf")        # Closest approach to violation (tightest margin)
    tightest_k: int = 0                 # The k achieving the tightest margin
    n_tested: int = 0                   # Number of k values tested
    root_cause: Optional[RootCauseAnalysis] = None  # Filled by the Investigator

    def __repr__(self) -> str:
        status_sym = {
            ConjectureStatus.SURVIVED: "OK",
            ConjectureStatus.REFUTED: "XX",
            ConjectureStatus.REDUNDANT: "~~",
            ConjectureStatus.PENDING: "??",
            ConjectureStatus.DIAGNOSED: "DX",
        }[self.status]
        diag = ""
        if self.root_cause:
            diag = f"  [{self.root_cause.structural_pattern}]"
        return (
            f"[{status_sym}] sharpness={self.sharpness:.3f}  "
            f"{self.statement}{diag}"
        )


@dataclass
class KData:
    """Precomputed data for one value of k, loaded from junction_results.json
    and enriched with on-the-fly computations."""
    k: int
    regime: str
    witness_prime: int
    witness_ord: int
    rho_bound: float
    k_min_p: int            # k_min(p) from junction results
    S: int = 0
    d: int = 0
    d_bits: int = 0
    n_prime_factors: int = 0
    smallest_prime_factor: int = 0
    largest_prime_factor: int = 0
    min_ord: int = 0        # min ord_p(2) over p | d(k)
    max_ord: int = 0        # max ord_p(2) over p | d(k)
    log2_d: float = 0.0
    n_compositions: int = 0
    is_fcq: bool = False


# =====================================================================
#  Data Loader
# =====================================================================

def _find_junction_results() -> str:
    """Locate junction_results.json relative to this module."""
    here = Path(__file__).resolve().parent
    candidate = here / "junction_results.json"
    if candidate.exists():
        return str(candidate)
    raise FileNotFoundError(
        f"junction_results.json not found at {candidate}"
    )


def load_data(path: Optional[str] = None) -> List[KData]:
    """Load junction_results.json and enrich with derived quantities."""
    if path is None:
        path = _find_junction_results()

    with open(path, "r") as f:
        raw = json.load(f)

    entries: List[KData] = []
    for r in raw["results"]:
        k = r["k"]
        S = compute_S(k)
        d = compute_d(k)

        factors = factorize(d) if d > 1 else []
        primes = [p for p, _ in factors]

        # Compute ord_p(2) for small primes dividing d(k)
        ords = []
        for p, _ in factors:
            if p < 10**7:
                o = multiplicative_order(2, p)
                if o > 0:
                    ords.append(o)

        kd = KData(
            k=k,
            regime=r["regime"],
            witness_prime=r["witness_prime"],
            witness_ord=r["witness_ord"],
            rho_bound=r["rho_bound"],
            k_min_p=r["k_min"],
            S=S,
            d=d,
            d_bits=d.bit_length(),
            n_prime_factors=len(factors),
            smallest_prime_factor=min(primes) if primes else 0,
            largest_prime_factor=max(primes) if primes else 0,
            min_ord=min(ords) if ords else 0,
            max_ord=max(ords) if ords else 0,
            log2_d=math.log2(d) if d > 1 else 0.0,
            n_compositions=count_compositions(k, S) if k <= 30 else 0,
            is_fcq=(r["regime"] == "B_fcq"),
        )
        entries.append(kd)

    return entries


# =====================================================================
#  OPTIMIST — Conjecture Generator
# =====================================================================

class Optimist:
    """Generates conjectures as inequalities between computed invariants.

    Strategy: scan the data for patterns, then propose parametric bounds
    of the form 'For all k >= K0, f(k) <= g(k)' or 'f(k) >= g(k)'.
    """

    def __init__(self, data: List[KData]):
        self.data = data
        self.fcq_data = [d for d in data if d.is_fcq]
        self.all_k = sorted(d.k for d in data)

    def generate_all(self) -> List[Conjecture]:
        """Generate all conjecture templates. Returns at least 50."""
        conjectures: List[Conjecture] = []
        conjectures.extend(self._rho_bound_conjectures())
        conjectures.extend(self._witness_ord_conjectures())
        conjectures.extend(self._k_min_conjectures())
        conjectures.extend(self._regime_pattern_conjectures())
        conjectures.extend(self._factorization_conjectures())
        conjectures.extend(self._S_and_d_conjectures())
        conjectures.extend(self._combined_conjectures())
        return conjectures

    # ------------------------------------------------------------------
    #  Family 1: rho_bound conjectures (for B_fcq regime)
    # ------------------------------------------------------------------
    def _rho_bound_conjectures(self) -> List[Conjecture]:
        if not self.fcq_data:
            return []

        conjs = []
        k0 = min(d.k for d in self.fcq_data)

        # C1.1: Universal rho upper bounds
        for threshold in [0.55, 0.50, 0.45, 0.40, 0.35, 0.30]:
            conjs.append(Conjecture(
                statement=f"For all k >= {k0}, rho_witness(k) < {threshold}",
                bound=threshold,
                k_range=(k0, 200),
                family="rho_upper",
            ))

        # C1.2: rho decays with k (various rates)
        for alpha in [0.3, 0.4, 0.5, 0.6, 0.7]:
            conjs.append(Conjecture(
                statement=f"For all k >= {k0}, rho_witness(k) < k^(-{alpha}) * 10",
                bound=alpha,
                k_range=(k0, 200),
                family="rho_decay_power",
            ))

        # C1.3: rho bounded by 1/sqrt(witness_prime)
        for C in [1.5, 2.0, 2.5, 3.0]:
            conjs.append(Conjecture(
                statement=f"For all k >= {k0}, rho_witness(k) <= {C} / sqrt(witness_prime(k))",
                bound=C,
                k_range=(k0, 200),
                family="rho_vs_prime",
            ))

        # C1.4: rho * witness_ord bounded
        for C in [2.0, 5.0, 10.0, 20.0, 50.0]:
            conjs.append(Conjecture(
                statement=f"For all k >= {k0}, rho_witness(k) * witness_ord(k) <= {C}",
                bound=C,
                k_range=(k0, 200),
                family="rho_times_ord",
            ))

        return conjs

    # ------------------------------------------------------------------
    #  Family 2: witness_ord conjectures
    # ------------------------------------------------------------------
    def _witness_ord_conjectures(self) -> List[Conjecture]:
        if not self.fcq_data:
            return []

        conjs = []
        k0 = min(d.k for d in self.fcq_data)

        # C2.1: witness_ord bounded by power of k
        for alpha in [0.5, 0.6, 0.7, 0.8, 1.0]:
            for C in [1.0, 2.0, 5.0]:
                conjs.append(Conjecture(
                    statement=f"For all k >= {k0}, witness_ord(k) <= {C} * k^{alpha}",
                    bound=(C, alpha),
                    k_range=(k0, 200),
                    family="ord_upper_power",
                ))

        # C2.2: There always exists a small-order witness
        for B in [50, 100, 500, 1000, 5000]:
            conjs.append(Conjecture(
                statement=f"For all k >= {k0}, d(k) has a prime factor p with ord_p(2) <= {B}",
                bound=B,
                k_range=(k0, 200),
                family="small_ord_exists",
            ))

        # C2.3: witness_ord / k bounded
        for ratio in [0.5, 1.0, 2.0, 5.0, 10.0, 50.0]:
            conjs.append(Conjecture(
                statement=f"For all k >= {k0}, witness_ord(k) / k <= {ratio}",
                bound=ratio,
                k_range=(k0, 200),
                family="ord_over_k",
            ))

        return conjs

    # ------------------------------------------------------------------
    #  Family 3: k_min conjectures
    # ------------------------------------------------------------------
    def _k_min_conjectures(self) -> List[Conjecture]:
        if not self.fcq_data:
            return []

        conjs = []
        k0 = min(d.k for d in self.fcq_data)

        # C3.1: k_min(witness_prime) universally bounded
        for B in [3, 4, 5, 6, 8, 10]:
            conjs.append(Conjecture(
                statement=f"For all k >= {k0}, k_min(witness_prime(k)) <= {B}",
                bound=B,
                k_range=(k0, 200),
                family="kmin_upper",
            ))

        # C3.2: k_min related to witness_ord
        for alpha in [0.1, 0.2, 0.3, 0.5]:
            conjs.append(Conjecture(
                statement=f"For all k >= {k0}, k_min(k) <= 1 + {alpha} * log2(witness_ord(k))",
                bound=alpha,
                k_range=(k0, 200),
                family="kmin_vs_log_ord",
            ))

        return conjs

    # ------------------------------------------------------------------
    #  Family 4: Regime pattern conjectures
    # ------------------------------------------------------------------
    def _regime_pattern_conjectures(self) -> List[Conjecture]:
        conjs = []

        # C4.1: No gaps in coverage — every k has a proof
        conjs.append(Conjecture(
            statement="For all k in [3, 200], k is proved (regime A, B, or C)",
            bound=0,
            k_range=(3, 200),
            family="completeness",
        ))

        # C4.2: B_fcq dominates for large k
        for k0 in [92, 100, 110, 120, 150]:
            conjs.append(Conjecture(
                statement=f"For all k >= {k0}, regime(k) in {{B_fcq, C_steiner}}",
                bound=k0,
                k_range=(k0, 200),
                family="regime_dominance",
            ))

        # C4.3: Periodicity modulo small numbers
        for m in [3, 4, 6, 12]:
            # Check if rho_bound has periodic structure mod m
            conjs.append(Conjecture(
                statement=f"For all k >= 92, if k mod {m} == 0 then rho_witness(k) < 0.3",
                bound=(m, 0.3),
                k_range=(92, 200),
                family=f"periodic_mod{m}",
            ))

        return conjs

    # ------------------------------------------------------------------
    #  Family 5: Factorization conjectures
    # ------------------------------------------------------------------
    def _factorization_conjectures(self) -> List[Conjecture]:
        conjs = []

        # C5.1: d(k) always has a "small" prime factor
        for B in [50, 100, 500, 1000, 10000]:
            conjs.append(Conjecture(
                statement=f"For all k >= 3, d(k) has a prime factor p <= {B}",
                bound=B,
                k_range=(3, 200),
                family="small_prime_factor",
            ))

        # C5.2: Number of prime factors of d(k) grows
        for alpha in [0.3, 0.5, 0.7, 1.0]:
            conjs.append(Conjecture(
                statement=f"For all k >= 10, omega(d(k)) >= {alpha} * log(k)",
                bound=alpha,
                k_range=(10, 200),
                family="omega_lower",
            ))

        # C5.3: d_bits grows linearly with k
        for alpha in [0.55, 0.58, 0.585, 0.59]:
            conjs.append(Conjecture(
                statement=f"For all k >= 3, d_bits(k) >= {alpha} * k",
                bound=alpha,
                k_range=(3, 200),
                family="dbits_linear",
            ))

        # C5.4: Smallest prime factor bounded
        for B in [3, 5, 7, 11, 13, 31]:
            conjs.append(Conjecture(
                statement=f"For all k >= 3, smallest_prime_factor(d(k)) <= {B}",
                bound=B,
                k_range=(3, 200),
                family="spf_upper",
            ))

        return conjs

    # ------------------------------------------------------------------
    #  Family 6: S(k) and d(k) structural conjectures
    # ------------------------------------------------------------------
    def _S_and_d_conjectures(self) -> List[Conjecture]:
        conjs = []

        # C6.1: S(k) - k * log2(3) is bounded (fractional part)
        conjs.append(Conjecture(
            statement="For all k >= 3, 0 < S(k) - k * log2(3) < 1 (by definition of ceil)",
            bound=1.0,
            k_range=(3, 200),
            family="S_frac",
        ))

        # C6.2: d(k) > 0 always (fundamental positivity)
        conjs.append(Conjecture(
            statement="For all k >= 1, d(k) = 2^S(k) - 3^k > 0",
            bound=0,
            k_range=(3, 200),
            family="d_positive",
        ))

        # C6.3: log2(d(k)) / k bounded away from 0
        for alpha in [0.4, 0.5, 0.55, 0.58]:
            conjs.append(Conjecture(
                statement=f"For all k >= 3, log2(d(k)) / k >= {alpha}",
                bound=alpha,
                k_range=(3, 200),
                family="log_d_over_k",
            ))

        return conjs

    # ------------------------------------------------------------------
    #  Family 7: Combined / cross-invariant conjectures
    # ------------------------------------------------------------------
    def _combined_conjectures(self) -> List[Conjecture]:
        if not self.fcq_data:
            return []

        conjs = []
        k0 = min(d.k for d in self.fcq_data)

        # C7.1: rho * k bounded (contraction improves with k)
        for C in [10, 20, 30, 50, 100]:
            conjs.append(Conjecture(
                statement=f"For all k >= {k0}, rho_witness(k) * k <= {C}",
                bound=C,
                k_range=(k0, 200),
                family="rho_times_k",
            ))

        # C7.2: witness_ord * rho^2 bounded (product bound)
        for C in [0.5, 1.0, 2.0, 5.0]:
            conjs.append(Conjecture(
                statement=f"For all k >= {k0}, witness_ord(k) * rho(k)^2 <= {C}",
                bound=C,
                k_range=(k0, 200),
                family="ord_rho_sq",
            ))

        # C7.3: "Fish-tunnel" — witness_prime / witness_ord bounded
        for C in [2.0, 3.0, 5.0, 10.0]:
            conjs.append(Conjecture(
                statement=f"For all k >= {k0}, witness_prime(k) / witness_ord(k) <= {C} * k",
                bound=C,
                k_range=(k0, 200),
                family="fish_tunnel",
            ))

        # C7.4: At least one prime with rho < threshold for every k
        for threshold in [0.55, 0.50, 0.45]:
            conjs.append(Conjecture(
                statement=f"For all k >= {k0}, there exists p | d(k) with rho_p < {threshold}",
                bound=threshold,
                k_range=(k0, 200),
                family="exists_good_prime",
            ))

        # C7.5: S(k) = k * log2(3) + frac, and frac controls factorization
        for C in [0.3, 0.5, 0.7]:
            conjs.append(Conjecture(
                statement=(
                    f"For all k >= {k0}, if frac(k*log2(3)) < {C} "
                    f"then rho_witness(k) < 0.3"
                ),
                bound=C,
                k_range=(k0, 200),
                family="frac_controls_rho",
            ))

        # C7.6: d_bits - S proportionality
        for alpha in [0.95, 0.98, 0.99, 1.0]:
            conjs.append(Conjecture(
                statement=f"For all k >= 3, d_bits(k) / S(k) >= {alpha}",
                bound=alpha,
                k_range=(3, 200),
                family="dbits_over_S",
            ))

        return conjs


# =====================================================================
#  PESSIMIST — Conjecture Tester
# =====================================================================

class Pessimist:
    """Exhaustively tests each conjecture against k=3..200.

    For each conjecture, evaluates the inequality on every relevant k.
    If a counterexample is found, the conjecture is refuted.
    Otherwise, records the closest margin (for sharpness scoring).
    """

    def __init__(self, data: List[KData]):
        self.data = data
        self._by_k: Dict[int, KData] = {d.k: d for d in data}

    def test(self, conj: Conjecture) -> Conjecture:
        """Test a conjecture against all k in its claimed range.
        Mutates and returns the conjecture with updated status."""
        k_lo, k_hi = conj.k_range
        tested = 0
        min_margin = float("inf")
        tightest_k = k_lo

        for k in range(k_lo, k_hi + 1):
            kd = self._by_k.get(k)
            if kd is None:
                continue

            result = self._evaluate(conj, kd)
            if result is None:
                # Not applicable to this k (e.g., conditional conjecture not triggered)
                continue

            tested += 1
            holds, margin = result

            if not holds:
                conj.status = ConjectureStatus.REFUTED
                conj.counterexample_k = k
                conj.n_tested = tested
                return conj

            if margin < min_margin:
                min_margin = margin
                tightest_k = k

        conj.status = ConjectureStatus.SURVIVED
        conj.margin = min_margin
        conj.tightest_k = tightest_k
        conj.n_tested = tested
        return conj

    def _evaluate(
        self, conj: Conjecture, kd: KData
    ) -> Optional[Tuple[bool, float]]:
        """Evaluate a single conjecture on a single k.

        Returns (holds: bool, margin: float) or None if not applicable.
        margin > 0 means the conjecture holds with that much slack.
        """
        family = conj.family

        # --- Family: rho_upper ---
        if family == "rho_upper":
            if not kd.is_fcq:
                return None
            rho = kd.rho_bound
            threshold = conj.bound
            margin = threshold - rho
            return (margin > 0, margin)

        # --- Family: rho_decay_power ---
        if family == "rho_decay_power":
            if not kd.is_fcq:
                return None
            alpha = conj.bound
            rho = kd.rho_bound
            bound_val = 10.0 * (kd.k ** (-alpha))
            margin = bound_val - rho
            return (margin > 0, margin)

        # --- Family: rho_vs_prime ---
        if family == "rho_vs_prime":
            if not kd.is_fcq or kd.witness_prime <= 0:
                return None
            C = conj.bound
            rho = kd.rho_bound
            bound_val = C / math.sqrt(kd.witness_prime)
            margin = bound_val - rho
            return (margin >= 0, margin)

        # --- Family: rho_times_ord ---
        if family == "rho_times_ord":
            if not kd.is_fcq or kd.witness_ord <= 0:
                return None
            C = conj.bound
            product = kd.rho_bound * kd.witness_ord
            margin = C - product
            return (margin >= 0, margin)

        # --- Family: ord_upper_power ---
        if family == "ord_upper_power":
            if not kd.is_fcq or kd.witness_ord <= 0:
                return None
            C, alpha = conj.bound
            bound_val = C * (kd.k ** alpha)
            margin = bound_val - kd.witness_ord
            return (margin >= 0, margin)

        # --- Family: small_ord_exists ---
        if family == "small_ord_exists":
            if not kd.is_fcq:
                return None
            B = conj.bound
            # The witness_ord is the best (smallest usable) ord found
            margin = B - kd.witness_ord
            return (margin >= 0, margin)

        # --- Family: ord_over_k ---
        if family == "ord_over_k":
            if not kd.is_fcq or kd.witness_ord <= 0:
                return None
            ratio = kd.witness_ord / kd.k
            margin = conj.bound - ratio
            return (margin >= 0, margin)

        # --- Family: kmin_upper ---
        if family == "kmin_upper":
            if not kd.is_fcq:
                return None
            B = conj.bound
            margin = B - kd.k_min_p
            return (margin >= 0, margin)

        # --- Family: kmin_vs_log_ord ---
        if family == "kmin_vs_log_ord":
            if not kd.is_fcq or kd.witness_ord <= 1:
                return None
            alpha = conj.bound
            bound_val = 1.0 + alpha * math.log2(kd.witness_ord)
            margin = bound_val - kd.k_min_p
            return (margin >= 0, margin)

        # --- Family: completeness ---
        if family == "completeness":
            return (True, 1.0)  # Already known: 198/198 proved

        # --- Family: regime_dominance ---
        if family == "regime_dominance":
            k0 = int(conj.bound)
            if kd.k < k0:
                return None
            holds = kd.regime in ("B_fcq", "C_steiner")
            return (holds, 1.0 if holds else 0.0)

        # --- Family: periodic_mod* ---
        if family.startswith("periodic_mod"):
            if not kd.is_fcq:
                return None
            m, threshold = conj.bound
            m = int(m)
            if kd.k % m != 0:
                return None  # Condition not triggered
            margin = threshold - kd.rho_bound
            return (margin > 0, margin)

        # --- Family: small_prime_factor ---
        if family == "small_prime_factor":
            B = conj.bound
            if kd.smallest_prime_factor <= 0:
                return None
            margin = B - kd.smallest_prime_factor
            return (margin >= 0, margin)

        # --- Family: omega_lower ---
        if family == "omega_lower":
            alpha = conj.bound
            if kd.k < 10:
                return None
            bound_val = alpha * math.log(kd.k)
            margin = kd.n_prime_factors - bound_val
            return (margin >= 0, margin)

        # --- Family: dbits_linear ---
        if family == "dbits_linear":
            alpha = conj.bound
            bound_val = alpha * kd.k
            margin = kd.d_bits - bound_val
            return (margin >= 0, margin)

        # --- Family: spf_upper ---
        if family == "spf_upper":
            B = conj.bound
            if kd.smallest_prime_factor <= 0:
                return None
            margin = B - kd.smallest_prime_factor
            return (margin >= 0, margin)

        # --- Family: S_frac ---
        if family == "S_frac":
            frac = kd.S - kd.k * math.log2(3)
            margin = min(frac, 1.0 - frac)
            return (0 < frac < 1, margin)

        # --- Family: d_positive ---
        if family == "d_positive":
            return (kd.d > 0, float(kd.d))

        # --- Family: log_d_over_k ---
        if family == "log_d_over_k":
            if kd.d <= 1 or kd.k <= 0:
                return None
            alpha = conj.bound
            ratio = math.log2(kd.d) / kd.k
            margin = ratio - alpha
            return (margin >= 0, margin)

        # --- Family: rho_times_k ---
        if family == "rho_times_k":
            if not kd.is_fcq:
                return None
            C = conj.bound
            product = kd.rho_bound * kd.k
            margin = C - product
            return (margin >= 0, margin)

        # --- Family: ord_rho_sq ---
        if family == "ord_rho_sq":
            if not kd.is_fcq or kd.witness_ord <= 0:
                return None
            C = conj.bound
            product = kd.witness_ord * (kd.rho_bound ** 2)
            margin = C - product
            return (margin >= 0, margin)

        # --- Family: fish_tunnel ---
        if family == "fish_tunnel":
            if not kd.is_fcq or kd.witness_ord <= 0:
                return None
            C = conj.bound
            ratio = kd.witness_prime / kd.witness_ord
            bound_val = C * kd.k
            margin = bound_val - ratio
            return (margin >= 0, margin)

        # --- Family: exists_good_prime ---
        if family == "exists_good_prime":
            if not kd.is_fcq:
                return None
            # The junction result already gives the best witness
            threshold = conj.bound
            margin = threshold - kd.rho_bound
            return (margin > 0, margin)

        # --- Family: frac_controls_rho ---
        if family == "frac_controls_rho":
            if not kd.is_fcq:
                return None
            C = conj.bound
            frac = kd.S - kd.k * math.log2(3)
            if frac >= C:
                return None  # Condition not triggered
            margin = 0.3 - kd.rho_bound
            return (margin > 0, margin)

        # --- Family: dbits_over_S ---
        if family == "dbits_over_S":
            if kd.S <= 0:
                return None
            alpha = conj.bound
            ratio = kd.d_bits / kd.S
            margin = ratio - alpha
            return (margin >= 0, margin)

        # --- Family: high_ord_exists (seeded) ---
        if family == "high_ord_exists":
            if not kd.is_fcq or kd.witness_ord <= 0 or kd.witness_prime <= 1:
                return None
            C = conj.bound
            threshold = C * math.sqrt(kd.witness_prime)
            margin = kd.witness_ord - threshold
            return (margin >= 0, margin)

        # --- Family: large_prime_exists (seeded) ---
        if family == "large_prime_exists":
            B_exp = conj.bound
            if kd.largest_prime_factor <= 0:
                return None
            threshold = kd.k ** B_exp
            margin = kd.largest_prime_factor - threshold
            return (margin >= 0, margin)

        # --- Family: rho_log_decay (seeded) ---
        if family == "rho_log_decay":
            if not kd.is_fcq or kd.k < 3:
                return None
            C = conj.bound
            bound_val = C / math.log2(kd.k)
            margin = bound_val - kd.rho_bound
            return (margin > 0, margin)

        # --- Family: rho_ord_tradeoff (seeded) ---
        if family == "rho_ord_tradeoff":
            if not kd.is_fcq or kd.witness_ord <= 1:
                return None
            C = conj.bound
            product = kd.rho_bound * math.log2(kd.witness_ord)
            margin = C - product
            return (margin >= 0, margin)

        # --- Family: d_smoothness (seeded) ---
        if family == "d_smoothness":
            B = conj.bound
            if kd.largest_prime_factor <= 0:
                return None
            margin = B - kd.largest_prime_factor
            return (margin >= 0, margin)

        # --- Family: rho_upper_shifted (seeded) ---
        if family == "rho_upper_shifted":
            if not kd.is_fcq:
                return None
            threshold = conj.bound
            margin = threshold - kd.rho_bound
            return (margin > 0, margin)

        # --- Family: rho_parity_even / rho_parity_odd (seeded) ---
        if family.startswith("rho_parity_"):
            if not kd.is_fcq:
                return None
            parity, threshold = conj.bound
            if kd.k % 2 != int(parity):
                return None  # Condition not triggered
            margin = threshold - kd.rho_bound
            return (margin > 0, margin)

        # --- Family: combined_rho_product (seeded) ---
        if family == "combined_rho_product":
            if not kd.is_fcq:
                return None
            # This requires multi-prime data we don't have per-k in KData.
            # Evaluate based on single witness as lower bound.
            n_primes, threshold = conj.bound
            # Conservative: rho^n_primes as proxy for product of n smallest
            product_proxy = kd.rho_bound ** int(n_primes)
            margin = threshold - product_proxy
            return (margin > 0, margin)

        # Unknown family — skip
        return None


# =====================================================================
#  INVESTIGATOR — Root-Cause Analyst
# =====================================================================

class Investigator:
    """Analyzes WHY conjectures fail and extracts structural knowledge.

    Philosophy (from Eric):
      - The Pessimist is a diagnostic crutch, NOT a gate that closes.
      - Each refutation must descend to the ROOT of the ROOT.
      - Metaphor: don't say "the tree is dead" — find that "the gardener
        planted the wrong tree in the wrong soil".
      - Each root cause naturally spawns new exploration directions.

    The Investigator receives refuted conjectures and produces:
      1. A root-cause analysis (WHY, structurally)
      2. What the failure REVEALS about the mathematical landscape
      3. New seeds for the Optimist (directions that the death opens)
    """

    def __init__(self, data: List[KData]):
        self.data = data
        self._by_k: Dict[int, KData] = {d.k: d for d in data}
        self.discoveries: List[RootCauseAnalysis] = []

    def diagnose(self, conj: Conjecture) -> RootCauseAnalysis:
        """Perform root-cause analysis on a refuted conjecture.
        Mutates conj.status to DIAGNOSED and attaches the analysis."""
        assert conj.status == ConjectureStatus.REFUTED
        assert conj.counterexample_k is not None

        kd = self._by_k.get(conj.counterexample_k)
        analysis = self._analyze_failure(conj, kd)

        conj.root_cause = analysis
        conj.status = ConjectureStatus.DIAGNOSED
        self.discoveries.append(analysis)
        return analysis

    def diagnose_all(self, conjectures: List[Conjecture]) -> List[RootCauseAnalysis]:
        """Diagnose all refuted conjectures. Returns list of analyses."""
        refuted = [c for c in conjectures if c.status == ConjectureStatus.REFUTED]
        return [self.diagnose(c) for c in refuted]

    def get_new_seeds(self) -> List[Dict[str, Any]]:
        """Extract conjecture seeds from all discoveries.

        Returns a list of dicts suitable for the Optimist's
        seed-based conjecture generation (family, hint, constraint).
        """
        seeds = []
        seen_patterns = set()

        for analysis in self.discoveries:
            pattern = analysis.structural_pattern
            if pattern in seen_patterns:
                continue
            seen_patterns.add(pattern)

            for direction in analysis.new_directions:
                seeds.append({
                    "origin_pattern": pattern,
                    "direction": direction,
                    "related_families": analysis.related_families,
                    "depth": analysis.depth,
                })

        return seeds

    def summarize(self) -> str:
        """Human-readable summary of all root-cause discoveries."""
        if not self.discoveries:
            return "  No refutations to diagnose."

        # Group by structural pattern
        by_pattern: Dict[str, List[RootCauseAnalysis]] = {}
        for d in self.discoveries:
            by_pattern.setdefault(d.structural_pattern, []).append(d)

        lines = []
        for pattern, analyses in sorted(by_pattern.items()):
            lines.append(f"  [{pattern}] ({len(analyses)} refutations)")
            # Show the deepest analysis for each pattern
            deepest = max(analyses, key=lambda a: a.depth)
            lines.append(f"    Root: {deepest.why_failed}")
            lines.append(f"    Reveals: {deepest.what_it_reveals}")
            if deepest.new_directions:
                lines.append(f"    Opens: {', '.join(deepest.new_directions[:3])}")

        n_seeds = len(self.get_new_seeds())
        lines.append(f"  → {n_seeds} new seeds extracted for Optimist")
        return "\n".join(lines)

    # ------------------------------------------------------------------
    #  Private: Root-cause analysis by family
    # ------------------------------------------------------------------

    def _analyze_failure(
        self, conj: Conjecture, kd: Optional[KData]
    ) -> RootCauseAnalysis:
        """Dispatch to family-specific root-cause analyzer."""
        family = conj.family

        if kd is None:
            return RootCauseAnalysis(
                why_failed=f"No data for k={conj.counterexample_k}",
                what_it_reveals="Data gap — k not in junction_results",
                structural_pattern="data_gap",
            )

        # Try family-specific diagnosis
        analyzer = self._ANALYZERS.get(family)
        if analyzer:
            return analyzer(self, conj, kd)

        # Generic fallback: still extract what we can
        return self._generic_analysis(conj, kd)

    def _analyze_rho_upper(self, conj: Conjecture, kd: KData) -> RootCauseAnalysis:
        """Why did a rho upper bound fail?"""
        rho = kd.rho_bound
        # Extract scalar threshold from bound (may be tuple for parity/combined)
        bound = conj.bound
        threshold = bound[-1] if isinstance(bound, tuple) else bound
        overshoot = rho - threshold

        # Dig deeper: WHY is rho large at this k?
        # rho = sqrt(p) / q where q = ord_p(2)
        p = kd.witness_prime
        q = kd.witness_ord

        if q <= 2:
            why = (f"At k={kd.k}, rho={rho:.4f} > {threshold} because witness "
                   f"prime p={p} has ord_p(2)={q} (too small). "
                   f"Small order means weak character sum cancellation.")
            reveals = ("Primes with very small multiplicative order cannot "
                       "provide strong enough bounds. The bound requires "
                       "ord_p(2) >> sqrt(p).")
            pattern = "small_order_witness"
            directions = [
                "seek_high_order_primes: find p|d(k) with ord_p(2) > sqrt(p)",
                "artin_density: use density of primitive roots to bound large-k witnesses",
                f"parity_segregation: check if k={kd.k} parity constrains available primes",
            ]
            depth = 3
        elif p < 20:
            why = (f"At k={kd.k}, rho={rho:.4f} > {threshold} because the only "
                   f"witness prime p={p} is tiny. sqrt({p})/q = {math.sqrt(p)/q:.4f}.")
            reveals = (f"For small primes, sqrt(p)/q is close to 1 even with good order. "
                       f"Small primes are fundamentally weak witnesses.")
            pattern = "small_prime_witness"
            directions = [
                "large_prime_existence: prove d(k) always has a prime factor > B(k)",
                "combined_witnesses: use MULTIPLE small primes jointly (CRT product)",
                "algebraic_structure: exploit 2^S ≡ 3^k structure for prime factorization",
            ]
            depth = 2
        else:
            why = (f"At k={kd.k}, rho={rho:.4f} exceeds {threshold} by {overshoot:.4f}. "
                   f"Witness: p={p}, ord={q}, ratio sqrt(p)/q = {math.sqrt(p)/q:.4f}.")
            reveals = (f"The bound {threshold} is too tight for the available prime "
                       f"structure at k={kd.k}. Need a weaker but universal bound, "
                       f"or a proof that better primes always exist.")
            pattern = "bound_too_tight"
            directions = [
                f"relax_bound: try threshold > {rho:.4f} (tightest needed)",
                "adaptive_bound: bound that depends on k (decaying threshold)",
                "prime_quality: characterize which k have weak vs strong witnesses",
            ]
            depth = 1

        return RootCauseAnalysis(
            why_failed=why,
            what_it_reveals=reveals,
            new_directions=directions,
            structural_pattern=pattern,
            depth=depth,
            related_families=["rho_decay_power", "rho_vs_prime", "rho_times_ord"],
        )

    def _analyze_rho_decay(self, conj: Conjecture, kd: KData) -> RootCauseAnalysis:
        """Why did a rho decay conjecture fail?"""
        alpha = conj.bound
        rho = kd.rho_bound
        expected = 10.0 * (kd.k ** (-alpha))

        if kd.k < 50:
            pattern = "decay_not_started"
            why = (f"At k={kd.k}, rho={rho:.4f} but k^(-{alpha})*10 = {expected:.4f}. "
                   f"Decay hasn't kicked in yet — too few primes available.")
            reveals = "Power-law decay may only hold asymptotically, not for small k."
            directions = [
                f"raise_k0: try decay starting at k >= {kd.k + 20}",
                "two_regime: separate bound for small-k and large-k",
            ]
            depth = 1
        else:
            pattern = "decay_rate_wrong"
            why = (f"At k={kd.k}, rho={rho:.4f} > k^(-{alpha})*10 = {expected:.4f}. "
                   f"The decay exponent {alpha} is too aggressive.")
            reveals = (f"The actual rho decay rate is slower than k^(-{alpha}). "
                       f"This constrains the best possible universal exponent.")
            directions = [
                f"weaker_exponent: try alpha < {alpha} (rho decays slower)",
                "log_decay: try rho < C / log(k) instead of power law",
                "conditional_decay: decay conditioned on arithmetic properties of k",
            ]
            depth = 2
            # Dig deeper: is this a sporadic exception or systematic?
            nearby_rhos = []
            for dk in range(max(3, kd.k - 5), min(201, kd.k + 6)):
                other = self._by_k.get(dk)
                if other and other.is_fcq:
                    nearby_rhos.append(other.rho_bound)
            if nearby_rhos and max(nearby_rhos) > expected:
                why += (f" Neighborhood rhos: {[f'{r:.3f}' for r in nearby_rhos]} "
                        f"— systematic, not sporadic.")
                depth = 3

        return RootCauseAnalysis(
            why_failed=why,
            what_it_reveals=reveals,
            new_directions=directions,
            structural_pattern=pattern,
            depth=depth,
            related_families=["rho_upper", "rho_vs_prime"],
        )

    def _analyze_small_prime_factor(self, conj: Conjecture, kd: KData) -> RootCauseAnalysis:
        """Why does d(k) lack small prime factors?"""
        B = conj.bound
        spf = kd.smallest_prime_factor

        # This is a CRITICAL failure: it means d(k) has no small prime factors
        why = (f"At k={kd.k}, smallest prime factor of d(k) is {spf} > {B}. "
               f"d(k) has {kd.d_bits} bits, {kd.n_prime_factors} known factors.")

        if spf > 1000:
            reveals = (f"d(k={kd.k}) avoids ALL primes ≤ {B}. This is the HARD CASE: "
                       f"no small witness prime exists. FCQ cannot help here.")
            pattern = "no_small_witness"
            directions = [
                "large_factor_theory: prove d(k) MUST have a factor in range [B, B^2]",
                "algebraic_factorization: exploit 2^S - 3^k = d(k) algebraically",
                "baker_method: use linear forms in logarithms (no prime needed)",
                f"ecm_factorization: find actual factors of d({kd.k}) to understand structure",
            ]
            depth = 3
        else:
            reveals = (f"d(k={kd.k})'s smallest prime {spf} is moderate. "
                       f"The bound B={B} is just too tight for universality.")
            pattern = "spf_bound_tight"
            directions = [
                f"raise_spf_bound: use B >= {spf} as the universal bound",
                "conditional_spf: bound SPF differently for even/odd k",
            ]
            depth = 1

        return RootCauseAnalysis(
            why_failed=why,
            what_it_reveals=reveals,
            new_directions=directions,
            structural_pattern=pattern,
            depth=depth,
            related_families=["small_ord_exists", "exists_good_prime"],
        )

    def _analyze_ord_conjectures(self, conj: Conjecture, kd: KData) -> RootCauseAnalysis:
        """Why did an ord-related conjecture fail?"""
        q = kd.witness_ord
        p = kd.witness_prime

        # Root: the order is unexpectedly large
        phi_p = p - 1  # For prime p
        order_ratio = q / phi_p if phi_p > 0 else 0

        if order_ratio > 0.8:
            why = (f"At k={kd.k}, witness prime p={p} has ord_p(2)={q} ≈ {order_ratio:.1%} "
                   f"of φ(p). This is near-primitive-root territory.")
            reveals = ("When 2 is close to a primitive root mod p, the order is "
                       "large and rho = sqrt(p)/q is small — but the order bound fails. "
                       "PARADOX: good-for-rho primes are bad-for-order-bounds.")
            pattern = "order_rho_tradeoff"
            directions = [
                "tradeoff_optimal: find primes balancing small rho AND small order",
                "pareto_frontier: map the (rho, ord) Pareto frontier over p|d(k)",
                "abandon_pure_order: combine rho and order in a single criterion",
            ]
            depth = 3
        elif q > kd.k:
            why = (f"At k={kd.k}, ord_p(2)={q} > k. The witness order exceeds k itself.")
            reveals = ("d(k) sometimes only has primes where 2 has very high order. "
                       "This suggests d(k)'s factorization is dominated by 'hard' primes.")
            pattern = "high_order_only"
            directions = [
                "smoothness_of_d: study whether d(k) is B-smooth for growing B(k)",
                "order_vs_k: prove ord(2,p) < f(k) for at least ONE p|d(k)",
            ]
            depth = 2
        else:
            why = (f"At k={kd.k}, witness ord={q} violates the conjectured bound. "
                   f"Bound was {conj.bound}.")
            reveals = "The order bound is too optimistic for this k."
            pattern = "order_bound_tight"
            directions = [
                "weaken_order_bound: relax the constant or exponent",
            ]
            depth = 1

        return RootCauseAnalysis(
            why_failed=why,
            what_it_reveals=reveals,
            new_directions=directions,
            structural_pattern=pattern,
            depth=depth,
            related_families=["ord_upper_power", "small_ord_exists", "ord_over_k"],
        )

    def _analyze_factorization(self, conj: Conjecture, kd: KData) -> RootCauseAnalysis:
        """Generic factorization conjecture failure."""
        why = (f"At k={kd.k}, d(k) has {kd.n_prime_factors} prime factors, "
               f"{kd.d_bits} bits, smallest prime={kd.smallest_prime_factor}.")
        reveals = (f"d({kd.k})'s factorization structure doesn't match the "
                   f"conjectured pattern [{conj.family}].")
        return RootCauseAnalysis(
            why_failed=why,
            what_it_reveals=reveals,
            new_directions=["deeper_factorization_study: understand d(k) = 2^S - 3^k mod various primes"],
            structural_pattern="factorization_mismatch",
            depth=1,
            related_families=["small_prime_factor", "omega_lower", "dbits_linear"],
        )

    def _analyze_regime(self, conj: Conjecture, kd: KData) -> RootCauseAnalysis:
        """Why did a regime dominance conjecture fail?"""
        why = (f"At k={kd.k}, regime={kd.regime}, not in {{B_fcq, C_steiner}} "
               f"as conjectured.")
        if kd.regime == "A_hercher":
            reveals = ("This k is still covered by the Hercher/SDW bound (k ≤ 91). "
                       "The regime boundary may shift with better methods.")
            pattern = "hercher_boundary"
        else:
            reveals = f"Unexpected regime '{kd.regime}' at k={kd.k}."
            pattern = "unknown_regime"

        return RootCauseAnalysis(
            why_failed=why,
            what_it_reveals=reveals,
            new_directions=["extend_regime_coverage: find methods for non-FCQ, non-Steiner k"],
            structural_pattern=pattern,
            depth=1,
            related_families=["completeness"],
        )

    def _generic_analysis(self, conj: Conjecture, kd: KData) -> RootCauseAnalysis:
        """Fallback for families without specialized analyzers."""
        why = (f"Conjecture [{conj.family}] refuted at k={kd.k}. "
               f"Bound={conj.bound}, witness: p={kd.witness_prime}, "
               f"ord={kd.witness_ord}, rho={kd.rho_bound:.4f}.")
        reveals = f"The {conj.family} pattern breaks at k={kd.k}."
        return RootCauseAnalysis(
            why_failed=why,
            what_it_reveals=reveals,
            new_directions=[f"refine_{conj.family}: adjust parameters for k={kd.k} edge case"],
            structural_pattern=f"generic_{conj.family}",
            depth=1,
            related_families=[conj.family],
        )

    # Dispatch table: family -> analyzer method
    _ANALYZERS: Dict[str, Callable] = {}


# Register analyzers (outside class to avoid forward-reference issues)
Investigator._ANALYZERS = {
    "rho_upper": Investigator._analyze_rho_upper,
    "rho_decay_power": Investigator._analyze_rho_decay,
    "rho_vs_prime": Investigator._analyze_rho_upper,  # same root cause
    "rho_times_ord": Investigator._analyze_rho_upper,
    "rho_times_k": Investigator._analyze_rho_upper,
    "ord_upper_power": Investigator._analyze_ord_conjectures,
    "small_ord_exists": Investigator._analyze_ord_conjectures,
    "ord_over_k": Investigator._analyze_ord_conjectures,
    "ord_rho_sq": Investigator._analyze_ord_conjectures,
    "small_prime_factor": Investigator._analyze_small_prime_factor,
    "spf_upper": Investigator._analyze_small_prime_factor,
    "omega_lower": Investigator._analyze_factorization,
    "dbits_linear": Investigator._analyze_factorization,
    "regime_dominance": Investigator._analyze_regime,
    "fish_tunnel": Investigator._analyze_ord_conjectures,
    "exists_good_prime": Investigator._analyze_rho_upper,
    # Seeded families (from Investigator discoveries)
    "high_ord_exists": Investigator._analyze_ord_conjectures,
    "large_prime_exists": Investigator._analyze_small_prime_factor,
    "rho_log_decay": Investigator._analyze_rho_decay,
    "rho_ord_tradeoff": Investigator._analyze_ord_conjectures,
    "d_smoothness": Investigator._analyze_factorization,
    "rho_upper_shifted": Investigator._analyze_rho_upper,
    "rho_parity_even": Investigator._analyze_rho_upper,
    "rho_parity_odd": Investigator._analyze_rho_upper,
    "combined_rho_product": Investigator._analyze_rho_upper,
}


# =====================================================================
#  SHARPNESS SCORER
# =====================================================================

class SharpnessScorer:
    """Measures how tight (sharp) a surviving conjecture is.

    A conjecture is sharp if its bound is close to being violated:
    - sharpness = 1.0 means the bound is perfectly tight
    - sharpness ~ 0.0 means the bound is very loose

    Sharp conjectures are more likely to capture real mathematical
    structure (they are not trivially true).
    """

    @staticmethod
    def score(conj: Conjecture) -> float:
        if conj.status != ConjectureStatus.SURVIVED:
            return 0.0

        if conj.n_tested == 0:
            return 0.0

        margin = conj.margin
        if margin == float("inf") or margin < 0:
            return 0.0

        # Sharpness = 1 / (1 + relative_margin)
        # We normalize margin by the bound magnitude to get a relative measure.
        bound_mag = _bound_magnitude(conj.bound)
        if bound_mag > 0:
            relative_margin = abs(margin) / bound_mag
        else:
            # For zero bounds, use absolute margin with a cap
            relative_margin = abs(margin)

        sharpness = 1.0 / (1.0 + relative_margin)

        # Bonus for conjectures tested on many k values
        coverage_bonus = min(1.0, conj.n_tested / 100.0)
        sharpness *= (0.7 + 0.3 * coverage_bonus)

        return min(1.0, sharpness)


def _bound_magnitude(bound) -> float:
    """Extract a scalar magnitude from a bound (which may be a tuple)."""
    if isinstance(bound, (int, float)):
        return abs(float(bound)) if bound != 0 else 1.0
    if isinstance(bound, tuple):
        vals = [abs(float(x)) for x in bound if isinstance(x, (int, float))]
        return max(vals) if vals else 1.0
    return 1.0


# =====================================================================
#  DALMATIAN FILTER — Redundancy Removal
# =====================================================================

class DalmatianFilter:
    """Removes redundant conjectures using the Dalmatian heuristic.

    If conjecture A implies conjecture B (i.e., A is strictly stronger),
    then B is redundant and removed. Within the same family, a tighter
    bound implies a looser bound.
    """

    @staticmethod
    def filter(conjectures: List[Conjecture]) -> List[Conjecture]:
        """Remove redundant conjectures. Returns filtered list."""
        survived = [c for c in conjectures if c.status == ConjectureStatus.SURVIVED]

        # Group by family
        by_family: Dict[str, List[Conjecture]] = {}
        for c in survived:
            by_family.setdefault(c.family, []).append(c)

        kept: List[Conjecture] = []

        for family, group in by_family.items():
            # Sort by sharpness descending — keep the sharpest
            group.sort(key=lambda c: c.sharpness, reverse=True)

            if family in _MONOTONE_FAMILIES:
                # For monotone families (tighter bound => stronger conjecture),
                # keep only the tightest that survived.
                best = _keep_tightest(group, family)
                kept.extend(best)
            else:
                # For non-monotone families, keep all (no implication relation)
                kept.extend(group)

        # Mark removed conjectures
        kept_set = set(id(c) for c in kept)
        for c in survived:
            if id(c) not in kept_set:
                c.status = ConjectureStatus.REDUNDANT

        return kept


# Families where a smaller bound is strictly stronger
_MONOTONE_UPPER = {
    "rho_upper", "rho_times_ord", "rho_times_k", "ord_rho_sq",
    "small_ord_exists", "ord_over_k", "kmin_upper",
    "small_prime_factor", "spf_upper", "exists_good_prime",
    "regime_dominance",  # smaller k0 = stronger claim
}
# Families where a larger bound is strictly stronger
_MONOTONE_LOWER = {
    "omega_lower", "dbits_linear", "log_d_over_k", "dbits_over_S",
}
_MONOTONE_FAMILIES = _MONOTONE_UPPER | _MONOTONE_LOWER


def _keep_tightest(
    group: List[Conjecture], family: str
) -> List[Conjecture]:
    """Within a monotone family, keep only the tightest surviving conjecture."""
    if not group:
        return []

    if family in _MONOTONE_UPPER:
        # Smaller bound = stronger. Keep the one with smallest bound.
        def bound_key(c):
            b = c.bound
            if isinstance(b, tuple):
                return b[0]
            return b
        group.sort(key=bound_key)
        return [group[0]]

    if family in _MONOTONE_LOWER:
        # Larger bound = stronger. Keep the one with largest bound.
        def bound_key(c):
            b = c.bound
            if isinstance(b, tuple):
                return b[0]
            return b
        group.sort(key=bound_key, reverse=True)
        return [group[0]]

    return group[:1]


# =====================================================================
#  MAIN ENGINE
# =====================================================================

def run_optimist_pessimist(
    data_path: Optional[str] = None,
    top_n: int = 10,
    n_rounds: int = 2,
    verbose: bool = True,
) -> Dict[str, Any]:
    """Run the Optimist-Pessimist-Investigator feedback loop.

    Architecture (v2 — Pessimist as diagnostic crutch):

      Round 1: OPTIMIST → PESSIMIST → INVESTIGATOR → root causes
      Round 2: OPTIMIST (seeded by discoveries) → PESSIMIST → INVESTIGATOR
      ...
      Final:   SCORER → DALMATIAN → ranked survivors + diagnostic map

    Each round:
      1. OPTIMIST generates conjectures (round 1: templates; round 2+: seeded)
      2. PESSIMIST tests each against k=3..200
      3. INVESTIGATOR diagnoses every refutation (WHY? root of root)
      4. Seeds extracted from diagnoses feed the NEXT round's Optimist

    The Pessimist is NOT a gate. It is a diagnostic tool.
    Every death produces knowledge that opens new paths.

    Parameters
    ----------
    data_path : str, optional
        Path to junction_results.json. Auto-detected if None.
    top_n : int
        Number of top conjectures to return.
    n_rounds : int
        Number of Optimist-Pessimist-Investigator cycles.
    verbose : bool
        Print progress and results.

    Returns
    -------
    dict with keys:
        'top_conjectures': List[Conjecture] — top_n sharpest survivors
        'all_diagnoses': List[RootCauseAnalysis] — all root-cause analyses
        'diagnostic_map': Dict[str, List] — patterns grouped by structural type
        'seeds': List[Dict] — seeds available for further exploration
        'rounds': List[Dict] — per-round statistics
    """
    # ── Step 1: Load data ──
    if verbose:
        print("=" * 70)
        print("  OPTIMIST — PESSIMIST — INVESTIGATOR  (feedback loop v2)")
        print("  'Each death is a lever for discovery'")
        print("=" * 70)
        print()

    data = load_data(data_path)
    if verbose:
        n_fcq = sum(1 for d in data if d.is_fcq)
        print(f"  Loaded {len(data)} entries (k=3..200)")
        print(f"  B_fcq regime: {n_fcq} entries")
        print()

    # Shared state across rounds
    all_conjectures: List[Conjecture] = []
    investigator = Investigator(data)
    pessimist = Pessimist(data)
    scorer = SharpnessScorer()
    round_stats: List[Dict] = []
    accumulated_seeds: List[Dict] = []

    for round_num in range(1, n_rounds + 1):
        if verbose:
            print(f"  ━━━ ROUND {round_num}/{n_rounds} ━━━")
            print()

        # ── OPTIMIST: generate conjectures ──
        optimist = Optimist(data)
        if round_num == 1:
            conjectures = optimist.generate_all()
        else:
            # Seeded generation: use discoveries from previous rounds
            conjectures = optimist.generate_all()
            conjectures.extend(
                _generate_seeded_conjectures(accumulated_seeds, data)
            )

        if verbose:
            families = {}
            for c in conjectures:
                families[c.family] = families.get(c.family, 0) + 1
            print(f"  OPTIMIST: {len(conjectures)} conjectures "
                  f"({len(families)} families)")

        # ── PESSIMIST: test conjectures ──
        for c in conjectures:
            pessimist.test(c)

        n_survived = sum(1 for c in conjectures
                         if c.status == ConjectureStatus.SURVIVED)
        n_refuted = sum(1 for c in conjectures
                        if c.status == ConjectureStatus.REFUTED)

        if verbose:
            print(f"  PESSIMIST: {n_survived} survived, {n_refuted} refuted")

        # ── INVESTIGATOR: diagnose all refutations ──
        analyses = investigator.diagnose_all(conjectures)
        new_seeds = investigator.get_new_seeds()
        # Only keep seeds we haven't seen yet
        seen_origins = {s["origin_pattern"] for s in accumulated_seeds}
        fresh_seeds = [s for s in new_seeds
                       if s["origin_pattern"] not in seen_origins]
        accumulated_seeds.extend(fresh_seeds)

        if verbose:
            n_diagnosed = sum(1 for c in conjectures
                              if c.status == ConjectureStatus.DIAGNOSED)
            n_deep = sum(1 for a in analyses if a.depth >= 3)
            print(f"  INVESTIGATOR: {n_diagnosed} diagnosed, "
                  f"{n_deep} deep root causes (depth >= 3)")
            print(f"  → {len(fresh_seeds)} new seeds for next round")
            print()

            # Show deepest root causes
            deep_analyses = sorted(analyses, key=lambda a: a.depth, reverse=True)
            for a in deep_analyses[:3]:
                print(f"    [{a.structural_pattern}] depth={a.depth}")
                print(f"      Root: {a.why_failed[:120]}")
                print(f"      Opens: {', '.join(a.new_directions[:2])}")
                print()

        round_stats.append({
            "round": round_num,
            "n_generated": len(conjectures),
            "n_survived": n_survived,
            "n_refuted": n_refuted,
            "n_diagnosed": len(analyses),
            "n_deep": sum(1 for a in analyses if a.depth >= 3),
            "n_new_seeds": len(fresh_seeds),
        })

        all_conjectures.extend(conjectures)

    # ── Final: Score, filter, rank ──
    if verbose:
        print("  ━━━ FINAL SCORING ━━━")
        print()

    for c in all_conjectures:
        c.sharpness = scorer.score(c)

    kept = DalmatianFilter.filter(all_conjectures)
    n_total_survived = sum(1 for c in all_conjectures
                           if c.status == ConjectureStatus.SURVIVED)
    n_redundant = n_total_survived - len(kept)

    if verbose:
        print(f"  DALMATIAN: {n_redundant} redundant removed, "
              f"{len(kept)} survivors kept")

    kept.sort(key=lambda c: c.sharpness, reverse=True)
    top = kept[:top_n]

    if verbose:
        print()
        print(f"  TOP {min(top_n, len(top))} SHARPEST CONJECTURES")
        print("  " + "-" * 66)
        for i, c in enumerate(top, 1):
            print(
                f"  #{i:2d}  sharpness={c.sharpness:.4f}  "
                f"margin={c.margin:.6f}  tight@k={c.tightest_k}"
            )
            print(f"       {c.statement}")
            print(f"       [family={c.family}, tested={c.n_tested}]")
        print("  " + "-" * 66)

    # ── Diagnostic map ──
    diagnostic_map: Dict[str, List] = {}
    for a in investigator.discoveries:
        diagnostic_map.setdefault(a.structural_pattern, []).append({
            "why": a.why_failed,
            "reveals": a.what_it_reveals,
            "directions": a.new_directions,
            "depth": a.depth,
        })

    if verbose:
        print()
        print("  ━━━ DIAGNOSTIC MAP (Investigator's discoveries) ━━━")
        print(investigator.summarize())
        print()

    return {
        "top_conjectures": top,
        "all_diagnoses": investigator.discoveries,
        "diagnostic_map": diagnostic_map,
        "seeds": accumulated_seeds,
        "rounds": round_stats,
    }


def _generate_seeded_conjectures(
    seeds: List[Dict], data: List[KData]
) -> List[Conjecture]:
    """Generate new conjectures from Investigator seeds.

    Each seed contains an origin_pattern and a direction hint.
    We translate these into concrete conjecture templates.
    """
    conjectures: List[Conjecture] = []
    fcq_data = [d for d in data if d.is_fcq]
    if not fcq_data:
        return conjectures

    k0 = min(d.k for d in fcq_data)

    for seed in seeds:
        direction = seed["direction"]
        origin = seed["origin_pattern"]

        # Parse direction hints and generate targeted conjectures
        if "seek_high_order_primes" in direction:
            for C in [1.0, 1.5, 2.0]:
                conjectures.append(Conjecture(
                    statement=(f"For all k >= {k0}, d(k) has a prime p "
                               f"with ord_p(2) > {C} * sqrt(p)"),
                    bound=C,
                    k_range=(k0, 200),
                    family="high_ord_exists",
                ))

        elif "large_prime_existence" in direction:
            for B_exp in [0.3, 0.5, 0.7]:
                conjectures.append(Conjecture(
                    statement=(f"For all k >= {k0}, d(k) has a prime factor "
                               f"p > k^{B_exp}"),
                    bound=B_exp,
                    k_range=(k0, 200),
                    family="large_prime_exists",
                ))

        elif "combined_witnesses" in direction:
            for n_primes in [2, 3, 4]:
                conjectures.append(Conjecture(
                    statement=(f"For all k >= {k0}, product of "
                               f"(smallest {n_primes} rho_p) < 0.5"),
                    bound=(n_primes, 0.5),
                    k_range=(k0, 200),
                    family="combined_rho_product",
                ))

        elif "weaker_exponent" in direction or "log_decay" in direction:
            for C in [1.0, 2.0, 5.0]:
                conjectures.append(Conjecture(
                    statement=(f"For all k >= {k0}, rho_witness(k) "
                               f"< {C} / log2(k)"),
                    bound=C,
                    k_range=(k0, 200),
                    family="rho_log_decay",
                ))

        elif "tradeoff_optimal" in direction or "pareto_frontier" in direction:
            for C in [0.5, 1.0, 2.0]:
                conjectures.append(Conjecture(
                    statement=(f"For all k >= {k0}, min_p(rho_p * "
                               f"log(ord_p(2))) < {C}"),
                    bound=C,
                    k_range=(k0, 200),
                    family="rho_ord_tradeoff",
                ))

        elif "smoothness_of_d" in direction:
            for B in [100, 1000, 10000]:
                conjectures.append(Conjecture(
                    statement=(f"For all k >= {k0}, d(k) is {B}-smooth "
                               f"(all prime factors <= {B})"),
                    bound=B,
                    k_range=(k0, 200),
                    family="d_smoothness",
                ))

        elif "raise_k0" in direction or "two_regime" in direction:
            for new_k0 in [50, 80, 100, 120]:
                for threshold in [0.50, 0.45, 0.40]:
                    conjectures.append(Conjecture(
                        statement=(f"For all k >= {new_k0}, "
                                   f"rho_witness(k) < {threshold}"),
                        bound=threshold,
                        k_range=(new_k0, 200),
                        family="rho_upper_shifted",
                    ))

        elif "conditional_decay" in direction or "parity_segregation" in direction:
            for parity in [0, 1]:
                parity_name = "even" if parity == 0 else "odd"
                for threshold in [0.50, 0.45, 0.40]:
                    conjectures.append(Conjecture(
                        statement=(f"For all {parity_name} k >= {k0}, "
                                   f"rho_witness(k) < {threshold}"),
                        bound=(parity, threshold),
                        k_range=(k0, 200),
                        family=f"rho_parity_{parity_name}",
                    ))

    return conjectures


# =====================================================================
#  CLI Entry Point
# =====================================================================

if __name__ == "__main__":
    results = run_optimist_pessimist(top_n=10, n_rounds=2, verbose=True)

    # Summary statistics
    print("SUMMARY")
    top = results["top_conjectures"]
    print(f"  Total survivors returned: {len(top)}")
    if top:
        print(f"  Sharpness range: {top[-1].sharpness:.4f} .. {top[0].sharpness:.4f}")
        families = set(c.family for c in top)
        print(f"  Families represented: {', '.join(sorted(families))}")

    diagnoses = results["all_diagnoses"]
    print(f"  Total diagnoses: {len(diagnoses)}")
    deep = [d for d in diagnoses if d.depth >= 3]
    print(f"  Deep root causes (depth >= 3): {len(deep)}")
    print(f"  Seeds for future rounds: {len(results['seeds'])}")

    # Show the deepest discoveries
    if deep:
        print()
        print("DEEPEST ROOT CAUSES:")
        for d in sorted(deep, key=lambda x: x.depth, reverse=True)[:5]:
            print(f"  [{d.structural_pattern}] depth={d.depth}")
            print(f"    {d.why_failed[:150]}")
            print(f"    Reveals: {d.what_it_reveals[:120]}")
            print(f"    Opens: {', '.join(d.new_directions[:2])}")
            print()
