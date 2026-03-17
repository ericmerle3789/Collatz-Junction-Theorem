"""
Pattern Miner — Cross-k Pattern Discovery (Syracuse-JEPA v2)

Discovers mathematical patterns that could generalize beyond finite k:
- Asymptotic growth rates of d(k), corrSum gaps, prime factor counts
- Modular arithmetic regularities (periodic patterns in factorizations)
- Spectral trends (how contraction rates evolve)
- Structural invariants (properties that hold for ALL observed k)

Outputs conjectures about GENERAL k for the Strategist.
"""

import math
import statistics
from dataclasses import dataclass
from typing import List, Dict, Tuple, Optional

from syracuse_jepa.pipeline.analyst import AnalysisResult, CrossKInsight


@dataclass
class AsymptoticTrend:
    """A detected asymptotic trend in some quantity."""
    quantity: str
    model: str          # "linear", "exponential", "power_law", "logarithmic"
    slope: float        # main coefficient
    intercept: float
    r_squared: float    # fit quality
    extrapolation: str  # what this predicts for large k


@dataclass
class StructuralInvariant:
    """A property that holds for ALL observed k values."""
    property_name: str
    holds_for: str         # range description
    n_verified: int
    exceptions: List[int]  # k values where it fails
    strength: str          # "universal", "almost_universal", "majority"


@dataclass
class GeneralConjecture:
    """A conjecture about all k, generated from observed patterns."""
    statement: str
    evidence_strength: float  # 0 to 1
    n_verified: int
    known_exceptions: List[int]
    proof_approach: str       # suggested proof strategy
    connects_to: str          # research piste
    lean_template: str        # potential Lean formalization


def linear_regression(xs: List[float], ys: List[float]) -> Tuple[float, float, float]:
    """Simple linear regression. Returns (slope, intercept, r_squared)."""
    n = len(xs)
    if n < 2:
        return 0.0, 0.0, 0.0
    mx, my = statistics.mean(xs), statistics.mean(ys)
    num = sum((xs[i] - mx) * (ys[i] - my) for i in range(n))
    den_x = sum((xs[i] - mx) ** 2 for i in range(n))
    den_y = sum((ys[i] - my) ** 2 for i in range(n))
    if den_x == 0 or den_y == 0:
        return 0.0, my, 0.0
    slope = num / den_x
    intercept = my - slope * mx
    r_sq = (num ** 2) / (den_x * den_y)
    return slope, intercept, r_sq


# ═══════════════════════════════════════════════════════════════
#  Trend Detection
# ═══════════════════════════════════════════════════════════════

def detect_trends(results: List[AnalysisResult]) -> List[AsymptoticTrend]:
    """Detect asymptotic trends across k values."""
    trends = []

    ks = [float(r.k) for r in results]

    # 1. d(k) growth: should be ~ (2^{log2(3)} - 3)^k ≈ (0.17)^k ... no, d(k) grows
    # Actually d(k) = 2^{ceil(k·log2(3))} - 3^k. For large k, d(k) ~ γ · 3^k where γ ~ 0.05
    log_ds = [math.log(r.d) for r in results if r.d > 0]
    if len(log_ds) >= 3:
        slope, intercept, r2 = linear_regression(ks[:len(log_ds)], log_ds)
        trends.append(AsymptoticTrend(
            quantity="log(d(k))",
            model="linear",
            slope=slope,
            intercept=intercept,
            r_squared=r2,
            extrapolation=f"d(k) ~ exp({slope:.4f}k) = {math.exp(slope):.4f}^k. "
                          f"Compare 3^k growth rate log(3)={math.log(3):.4f}. "
                          f"Deficit γ = {slope - math.log(3):.4f}"
        ))

    # 2. Number of prime factors of d(k)
    n_factors = [float(r.n_prime_factors) for r in results]
    if len(n_factors) >= 3:
        slope, intercept, r2 = linear_regression(ks, n_factors)
        trends.append(AsymptoticTrend(
            quantity="n_prime_factors(d(k))",
            model="linear",
            slope=slope,
            intercept=intercept,
            r_squared=r2,
            extrapolation=f"Prime factor count grows ~ {slope:.3f}k + {intercept:.1f}. "
                          f"More factors = more spectral components = stronger avoidance"
        ))

    # 3. Product ρ bound
    log_rhos = []
    rho_ks = []
    for r in results:
        if r.product_rho_bound > 0:
            log_rhos.append(math.log(r.product_rho_bound))
            rho_ks.append(float(r.k))
    if len(log_rhos) >= 3:
        slope, intercept, r2 = linear_regression(rho_ks, log_rhos)
        trends.append(AsymptoticTrend(
            quantity="log(Πρ)",
            model="linear",
            slope=slope,
            intercept=intercept,
            r_squared=r2,
            extrapolation=f"Πρ ~ exp({slope:.4f}k). Decay rate = {-slope:.4f}/k. "
                          f"Need -slope > log(3)≈1.099 for N₀=0 (currently {-slope:.4f})"
        ))

    # 4. Max multiplicative order growth
    max_ords = [float(r.max_ord_2) for r in results if r.max_ord_2 > 0]
    if len(max_ords) >= 3:
        slope, intercept, r2 = linear_regression(ks[:len(max_ords)], max_ords)
        trends.append(AsymptoticTrend(
            quantity="max_ord_p(2)",
            model="linear",
            slope=slope,
            intercept=intercept,
            r_squared=r2,
            extrapolation=f"Max ord grows ~ {slope:.2f}k. "
                          f"For LDS (R197): need ord > c·k for transport argument"
        ))

    # 5. Budget ratio trend (R189 gap)
    budgets = [(float(r.k), r.budget_ratio) for r in results if r.budget_ratio > 0]
    if len(budgets) >= 3:
        bks = [b[0] for b in budgets]
        bvals = [b[1] for b in budgets]
        slope, intercept, r2 = linear_regression(bks, bvals)
        trends.append(AsymptoticTrend(
            quantity="budget_ratio",
            model="linear",
            slope=slope,
            intercept=intercept,
            r_squared=r2,
            extrapolation=f"Budget ratio trend: {slope:+.4f}/k. "
                          f"{'IMPROVING' if slope > 0 else 'WORSENING'} with k. "
                          f"At k=100: est. ratio = {100*slope + intercept:.2f}"
        ))

    # 6. Gap decay relative to d
    gaps = [(float(r.k), r.min_gap_rel) for r in results
            if r.min_gap_rel > 0]
    if len(gaps) >= 3:
        gks = [g[0] for g in gaps]
        log_gaps = [math.log(g[1]) for g in gaps]
        slope, intercept, r2 = linear_regression(gks, log_gaps)
        trends.append(AsymptoticTrend(
            quantity="log(min_gap/d)",
            model="linear",
            slope=slope,
            intercept=intercept,
            r_squared=r2,
            extrapolation=f"Relative gap ~ exp({slope:.4f}k). "
                          f"{'DANGER: gap shrinks' if slope < 0 else 'SAFE: gap grows'} with k"
        ))

    return trends


# ═══════════════════════════════════════════════════════════════
#  Invariant Detection
# ═══════════════════════════════════════════════════════════════

def detect_invariants(results: List[AnalysisResult]) -> List[StructuralInvariant]:
    """Find properties that hold for all (or almost all) k values."""
    invariants = []
    n = len(results)

    # 1. N₀(d(k)) = 0 (avoidance)
    avoidance_holds = [r.k for r in results
                       if r.min_gap_abs > 0]  # gap > 0 means N₀ = 0
    avoidance_fails = [r.k for r in results
                       if r.min_gap_abs == 0 and r.min_gap_abs >= 0]
    invariants.append(StructuralInvariant(
        property_name="N₀(d(k)) = 0",
        holds_for=f"k ∈ [{min(avoidance_holds)}..{max(avoidance_holds)}]" if avoidance_holds else "none",
        n_verified=len(avoidance_holds),
        exceptions=avoidance_fails,
        strength="almost_universal" if len(avoidance_fails) <= 1 else "majority"
    ))

    # 2. d(k) > 0 (non-degenerate)
    positive_d = [r.k for r in results if r.d > 0]
    invariants.append(StructuralInvariant(
        property_name="d(k) > 0",
        holds_for=f"k ∈ [{min(positive_d)}..{max(positive_d)}]" if positive_d else "none",
        n_verified=len(positive_d),
        exceptions=[r.k for r in results if r.d <= 0],
        strength="universal" if len(positive_d) == n else "majority"
    ))

    # 3. Product ρ < 1 (contraction)
    contracting = [r.k for r in results if r.product_rho_bound < 1.0]
    invariants.append(StructuralInvariant(
        property_name="Πρ < 1 (spectral contraction)",
        holds_for=f"k ≥ {min(contracting)}" if contracting else "none",
        n_verified=len(contracting),
        exceptions=[r.k for r in results if r.product_rho_bound >= 1.0],
        strength="universal" if len(contracting) == n else
                 "almost_universal" if len(contracting) >= n - 2 else "majority"
    ))

    # 4. At least 2 prime factors
    multi_prime = [r.k for r in results if r.n_prime_factors >= 2]
    invariants.append(StructuralInvariant(
        property_name="ω(d(k)) ≥ 2 (multiple prime factors)",
        holds_for=f"k ≥ {min(multi_prime)}" if multi_prime else "none",
        n_verified=len(multi_prime),
        exceptions=[r.k for r in results if r.n_prime_factors < 2],
        strength="almost_universal" if len(multi_prime) >= n - 3 else "majority"
    ))

    # 5. 3 ∈ ⟨2⟩ for at least one prime
    has_three_in_two = [r.k for r in results
                        if any(pa.three_in_two_group for pa in r.prime_analyses)]
    invariants.append(StructuralInvariant(
        property_name="∃ p|d: 3 ∈ ⟨2⟩ mod p",
        holds_for=f"k ∈ {has_three_in_two[:5]}..." if has_three_in_two else "none",
        n_verified=len(has_three_in_two),
        exceptions=[r.k for r in results
                    if not any(pa.three_in_two_group for pa in r.prime_analyses)],
        strength="universal" if len(has_three_in_two) == n else "majority"
    ))

    # 6. FCQ R(p,k) < 1 for at least one prime
    fcq_works = [r.k for r in results
                 if any(R < 1.0 for R in r.fcq_R_values.values())]
    invariants.append(StructuralInvariant(
        property_name="∃ p|d: R(p,k) < 1 (FCQ contraction)",
        holds_for=f"k ≥ {min(fcq_works)}" if fcq_works else "none",
        n_verified=len(fcq_works),
        exceptions=[r.k for r in results
                    if not any(R < 1.0 for R in r.fcq_R_values.values())],
        strength="universal" if len(fcq_works) == n else "majority"
    ))

    return invariants


# ═══════════════════════════════════════════════════════════════
#  Conjecture Generation
# ═══════════════════════════════════════════════════════════════

def generate_conjectures(results: List[AnalysisResult],
                         trends: List[AsymptoticTrend],
                         invariants: List[StructuralInvariant],
                         insights: List[CrossKInsight]) -> List[GeneralConjecture]:
    """Generate mathematical conjectures about general k from patterns."""
    conjectures = []
    n = len(results)
    k_max = max(r.k for r in results)

    # C1: Avoidance for all k ≥ 3 except k=4
    avoidance_inv = next((inv for inv in invariants
                          if inv.property_name == "N₀(d(k)) = 0"), None)
    if avoidance_inv and avoidance_inv.n_verified >= n - 2:
        conjectures.append(GeneralConjecture(
            statement=f"N₀(d(k)) = 0 for all k ≥ 3, k ≠ 4",
            evidence_strength=min(0.95, avoidance_inv.n_verified / (k_max - 2)),
            n_verified=avoidance_inv.n_verified,
            known_exceptions=avoidance_inv.exceptions,
            proof_approach=(
                "THREE-PRONGED: "
                "(1) Small k by native_decide (current pipeline), "
                "(2) Medium k by n_min + Steiner argument (R171), "
                "(3) Large k by spectral contraction (R189 operator framework). "
                "GAP: connecting (2) to (3) — the 1.35x budget gap"
            ),
            connects_to="MAIN OBJECTIVE: Stage II Conjecture M",
            lean_template="theorem avoidance_general (k : Nat) (hk : k ≥ 3) (hk4 : k ≠ 4) : "
                          "N_zero_residue k = 0"
        ))

    # C2: Spectral contraction conjecture
    rho_trend = next((t for t in trends if t.quantity == "log(Πρ)"), None)
    if rho_trend and rho_trend.slope < -0.5:
        conjectures.append(GeneralConjecture(
            statement=f"Πρ(k) ≤ exp({rho_trend.slope:.3f}k) for all k ≥ 3",
            evidence_strength=rho_trend.r_squared,
            n_verified=n,
            known_exceptions=[],
            proof_approach=(
                "Weil bounds give |ρ_p| ≤ (k-1)/√p per prime. "
                "Need: (a) lower bound on number of prime factors of d(k) — "
                "use entropy deficit γ≈0.05, (b) lower bound on typical prime size — "
                "use Mertens' theorem + structure of 2^S-3^k"
            ),
            connects_to="R189 Operator Framework + R196 LDS",
            lean_template="theorem spectral_decay (k : Nat) (hk : k ≥ K₀) : "
                          "product_rho k ≤ exp(-α * k)"
        ))

    # C3: Prime factor count growth
    pf_trend = next((t for t in trends if t.quantity == "n_prime_factors(d(k))"), None)
    if pf_trend and pf_trend.slope > 0.1:
        conjectures.append(GeneralConjecture(
            statement=f"ω(d(k)) ≥ {pf_trend.slope:.2f}k for k large",
            evidence_strength=pf_trend.r_squared * 0.8,
            n_verified=n,
            known_exceptions=[],
            proof_approach=(
                "d(k) = 2^S - 3^k with S ~ k·log₂3. This is a Mersenne-like number "
                "with two exponential terms. Algebraic factorization (Aurifeuillean?) "
                "plus analytic number theory (Erdős-Kac for smooth numbers). "
                "Literature: Wagstaff (2021) on factorization of numbers of this form"
            ),
            connects_to="Needed for R189 operator framework (more factors = more decay)",
            lean_template="-- Requires analytic NT, unlikely to formalize directly"
        ))

    # C4: FCQ contraction threshold
    fcq_data = [(r.k, min(r.fcq_R_values.values()) if r.fcq_R_values else 999)
                for r in results]
    threshold_k = next((k for k, R in fcq_data if R < 0.1), None)
    if threshold_k:
        conjectures.append(GeneralConjecture(
            statement=f"R(p,k) < 0.1 for all p|d(k), k ≥ {threshold_k}",
            evidence_strength=0.7,
            n_verified=sum(1 for _, R in fcq_data if R < 0.1),
            known_exceptions=[k for k, R in fcq_data if R >= 0.1 and k >= threshold_k],
            proof_approach=(
                "FCQ (R196-R197): R = ord_p(2) · ρ_p^{k-1}. "
                "Since ρ_p < 1 (proved R191), R→0 exponentially. "
                "Need: uniform ρ_p < 1-ε for ε > 0 independent of p. "
                "This is exactly the 1.35x gap question"
            ),
            connects_to="R196-R197 FCQ + R189 Gap 1.35x",
            lean_template="-- FCQ contraction verifiable per k by native_decide"
        ))

    # C5: Gap growth conjecture
    gap_trend = next((t for t in trends if t.quantity == "log(min_gap/d)"), None)
    if gap_trend:
        if gap_trend.slope > 0:
            conjectures.append(GeneralConjecture(
                statement=f"min_gap(k)/d(k) grows exponentially (slope {gap_trend.slope:.4f})",
                evidence_strength=gap_trend.r_squared * 0.7,
                n_verified=n,
                known_exceptions=[4],
                proof_approach=(
                    "If gaps grow relative to d, avoidance STRENGTHENS with k. "
                    "This would follow from uniform equidistribution of corrSum mod d. "
                    "Connects to Weyl-type bounds on exponential sums with monotone constraint"
                ),
                connects_to="R189 + Conjecture M: exponential gap growth = strong form of N₀=0",
                lean_template="-- Asymptotic, not directly formalizable for finite k"
            ))

    # C6: d(k) never a prime power for k ≥ 5
    prime_power_ks = [r.k for r in results
                      if r.n_prime_factors == 1 and r.d > 1]
    non_pp_ks = [r.k for r in results if r.n_prime_factors >= 2]
    if len(non_pp_ks) > len(results) * 0.8:
        conjectures.append(GeneralConjecture(
            statement=f"d(k) has ≥ 2 distinct prime factors for k ≥ {min(non_pp_ks) if non_pp_ks else '?'}",
            evidence_strength=0.6,
            n_verified=len(non_pp_ks),
            known_exceptions=prime_power_ks,
            proof_approach=(
                "d(k) = 2^S - 3^k. If d(k) = p^a, then 2^S ≡ 3^k mod p^a. "
                "This is a very special Diophantine condition. "
                "Zsygmondy's theorem might apply (primitive divisors of a^n - b^n)"
            ),
            connects_to="Structural: more factors = more spectral components",
            lean_template="-- Number-theoretic, would need Zsygmondy formalization"
        ))

    return conjectures


def mine_patterns(results: List[AnalysisResult],
                  insights: List[CrossKInsight]) -> dict:
    """Full pattern mining pipeline."""
    print("┌─ PATTERN MINER v2 ───────────────────────────────────────┐")

    trends = detect_trends(results)
    invariants = detect_invariants(results)
    conjectures = generate_conjectures(results, trends, invariants, insights)

    print(f"  Trends detected:    {len(trends)}")
    print(f"  Invariants found:   {len(invariants)}")
    print(f"  Conjectures formed: {len(conjectures)}")

    # Display key findings
    for t in trends:
        fit = "●" * int(t.r_squared * 5) + "○" * (5 - int(t.r_squared * 5))
        print(f"  TREND [{fit}] {t.quantity}: {t.model} slope={t.slope:.4f}")

    for inv in invariants:
        strength_icon = {"universal": "███", "almost_universal": "██░",
                         "majority": "█░░"}.get(inv.strength, "░░░")
        print(f"  INVARIANT [{strength_icon}] {inv.property_name} "
              f"({inv.n_verified} verified, {len(inv.exceptions)} exceptions)")

    for c in conjectures:
        conf = int(c.evidence_strength * 10)
        bar = "█" * conf + "░" * (10 - conf)
        print(f"  CONJECTURE [{bar}] {c.statement}")

    print(f"└─────────────────────────────────────────────────────────┘\n")

    return {
        'trends': trends,
        'invariants': invariants,
        'conjectures': conjectures,
    }
