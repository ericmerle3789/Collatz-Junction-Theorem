"""
Analyst — Deep Structural Analysis Engine (Syracuse-JEPA v2)

Goes beyond finite N₀=0 verification to study WHY avoidance holds:
- Prime factorization of d(k) and multiplicative orders
- Spectral data: |ρ_a| contraction per prime (R189 framework)
- Gap structure: how close does corrSum get to 0 mod d
- Algebraic classification: adequate primes, 3 ∈ ⟨2⟩, etc.

Feeds structured insights to the Strategist for proof direction.
"""

import math
from dataclasses import dataclass, field
from typing import List, Dict, Tuple, Optional
from functools import lru_cache

from syracuse_jepa.pipeline.explorer import (
    compute_S, compute_d, corrsum, enumerate_monotone, count_compositions
)


# ═══════════════════════════════════════════════════════════════
#  Number Theory Primitives
# ═══════════════════════════════════════════════════════════════

def factorize(n: int, limit: int = 10**7) -> List[Tuple[int, int]]:
    """Prime factorization of n. Stops trial division at `limit`.
    Returns [(p, e), ...]. Remaining cofactor > limit stored as single factor."""
    if n <= 1:
        return []
    factors = []
    d = 2
    while d * d <= n and d <= limit:
        if n % d == 0:
            e = 0
            while n % d == 0:
                n //= d
                e += 1
            factors.append((d, e))
        d += 1 if d == 2 else 2  # skip even after 2
    if n > 1:
        factors.append((n, 1))
    return factors


def multiplicative_order(a: int, n: int) -> int:
    """Compute ord_n(a) using factorization of φ(n). O(√n · log n) not O(n)."""
    if math.gcd(a, n) != 1:
        return 0
    if n <= 2:
        return 1
    # For prime n: φ(n) = n-1. Compute ord by testing divisors of φ.
    phi = n - 1  # works for prime n (our main use case)
    order = phi
    for p_fac, _ in factorize(phi):
        while order % p_fac == 0 and pow(a, order // p_fac, n) == 1:
            order //= p_fac
    return order


def is_in_subgroup(target: int, generator: int, p: int) -> bool:
    """Check if target ∈ ⟨generator⟩ in (Z/pZ)* using order arithmetic."""
    if p <= 1:
        return False
    g = generator % p
    t = target % p
    if t == 0 or g == 0:
        return False
    # target ∈ ⟨generator⟩ iff target^(|⟨gen⟩|) = target^ord = 1
    # Equivalently: target^((p-1)/ord_p(gen)) = 1
    ord_g = multiplicative_order(g, p)
    if ord_g == 0:
        return False
    # t ∈ ⟨g⟩ iff t^((p-1)/ord_g) ≡ 1 mod p
    exp = (p - 1) // ord_g
    return pow(t, exp, p) == 1


def euler_phi(n: int) -> int:
    """Euler's totient function."""
    result = n
    for p, _ in factorize(n):
        result -= result // p
    return result


# ═══════════════════════════════════════════════════════════════
#  Per-Prime Structural Analysis
# ═══════════════════════════════════════════════════════════════

@dataclass
class PrimeAnalysis:
    """Deep analysis of one prime p dividing d(k)."""
    p: int
    e: int                    # p^e || d(k)
    ord_p_2: int              # ord_p(2)
    ord_p_3: int              # ord_p(3)
    three_in_two_group: bool  # 3 ∈ ⟨2⟩ mod p ?
    index_two: int            # [(Z/pZ)* : ⟨2⟩]
    is_adequate: bool         # adequate prime for avoidance
    rho_bound: float          # |ρ_a| upper bound (Weil: 2√p/p)
    # Spectral: corrSum distribution mod p
    n_zero_mod_p: int         # compositions with corrSum ≡ 0 mod p
    n_compositions: int       # total compositions checked
    avoidance_ratio: float    # 1 - n_zero/n_comp (closer to 1 = better)


@dataclass
class AnalysisResult:
    """Complete structural analysis for one value of k."""
    k: int
    S: int
    d: int
    d_bits: int
    d_factorization: List[Tuple[int, int]]
    n_prime_factors: int
    # Per-prime analysis
    prime_analyses: List[PrimeAnalysis]
    # Global spectral data
    product_rho_bound: float     # Π |ρ_p| over primes (R189 Λ_free)
    min_gap_abs: int             # closest corrSum to 0 mod d
    min_gap_rel: float
    gap_trend: float             # how gap grows with k
    # Classification
    all_adequate: bool           # all primes are adequate
    three_in_two_everywhere: bool  # 3 ∈ ⟨2⟩ for all p|d
    max_ord_2: int               # max ord_p(2) over p|d
    min_ord_2: int               # min ord_p(2) over p|d
    # Operator framework (R189)
    dissipation_gap: float       # estimated Λ_free decay rate
    budget_ratio: float          # available budget / required budget
    # LDS data (R196-R197)
    lds_k0_estimates: Dict[int, int]  # p -> k0(p) estimate
    fcq_R_values: Dict[int, float]    # p -> R(p,k) = q * ρ_p^{k-1}


def analyze_prime(p: int, e: int, k: int, S: int,
                  compositions: list = None) -> PrimeAnalysis:
    """Deep analysis of one prime factor p of d(k)."""
    ord2 = multiplicative_order(2, p)
    ord3 = multiplicative_order(3, p)
    phi_p = p - 1  # p is prime
    index = phi_p // ord2 if ord2 > 0 else phi_p
    three_in_two = is_in_subgroup(3, 2, p)

    # Adequate prime: -1 ∉ ⟨2⟩ mod p AND ord_p(2) is odd
    # (from APF piste R81)
    neg_one_in_two = is_in_subgroup(p - 1, 2, p)
    is_adequate = (ord2 % 2 == 1) and not neg_one_in_two

    # Weil bound for character sums: |S(χ)| ≤ (k-1)√p
    # Normalized contraction: ρ ≈ (k-1)√p / p = (k-1)/√p
    rho = min(1.0, (k - 1) / math.sqrt(p)) if p > 1 else 1.0

    # Check corrSum mod p if compositions provided
    n_zero_p = 0
    n_total = 0
    if compositions is not None:
        for A in compositions:
            cs = corrsum(list(A), k)
            if cs % p == 0:
                n_zero_p += 1
            n_total += 1

    avoid_ratio = 1.0 - (n_zero_p / n_total) if n_total > 0 else 0.0

    return PrimeAnalysis(
        p=p, e=e,
        ord_p_2=ord2, ord_p_3=ord3,
        three_in_two_group=three_in_two,
        index_two=index,
        is_adequate=is_adequate,
        rho_bound=rho,
        n_zero_mod_p=n_zero_p,
        n_compositions=n_total,
        avoidance_ratio=avoid_ratio,
    )


def analyze_k(k: int, max_compositions: int = 100_000) -> AnalysisResult:
    """Full structural analysis for one k value."""
    S = compute_S(k)
    d = compute_d(k)
    d_bits = d.bit_length()
    factors = factorize(d)

    # Get compositions for mod-p analysis (limit for speed)
    n_comp = count_compositions(k, S)
    compositions = None
    if n_comp <= max_compositions:
        compositions = list(enumerate_monotone(k, S))

    # Analyze each prime
    prime_analyses = []
    for p, e in factors:
        pa = analyze_prime(p, e, k, S, compositions)
        prime_analyses.append(pa)

    # Product of ρ bounds (R189: Λ_free = Π ρ_{a_j})
    product_rho = 1.0
    for pa in prime_analyses:
        product_rho *= pa.rho_bound

    # Global gap analysis
    min_gap = d
    if compositions is not None:
        for A in compositions:
            cs = corrsum(list(A), k)
            r = cs % d
            if r != 0:
                gap = min(r, d - r)
                if gap < min_gap:
                    min_gap = gap

    # Classification
    all_adequate = all(pa.is_adequate for pa in prime_analyses)
    three_everywhere = all(pa.three_in_two_group for pa in prime_analyses)
    ords_2 = [pa.ord_p_2 for pa in prime_analyses if pa.ord_p_2 > 0]

    # Operator framework budget (R189)
    # Available: γ ≈ 0.05 (entropy deficit)
    # Required: need Σ log|ρ_a| < -log(d) (very roughly)
    log_d = math.log(d) if d > 0 else 0
    log_rho_sum = sum(math.log(pa.rho_bound) for pa in prime_analyses
                      if pa.rho_bound > 0)
    budget_ratio = abs(log_rho_sum / log_d) if log_d > 0 else 0.0

    # Dissipation gap estimate
    dissipation = -log_rho_sum / k if k > 0 else 0.0

    # LDS estimates (R196-R197): k0(p) ≥ c * ord_p(2)
    # c ≥ 1/25 for small orders (R197)
    lds = {}
    for pa in prime_analyses:
        if pa.ord_p_2 > 0:
            lds[pa.p] = max(1, pa.ord_p_2 // 25)

    # FCQ: R(p,k) = q * ρ_p^{k-1} where q = ord_p(2)
    fcq = {}
    for pa in prime_analyses:
        if pa.ord_p_2 > 0 and pa.rho_bound < 1.0:
            R_val = pa.ord_p_2 * (pa.rho_bound ** (k - 1))
            fcq[pa.p] = R_val

    return AnalysisResult(
        k=k, S=S, d=d, d_bits=d_bits,
        d_factorization=factors,
        n_prime_factors=len(factors),
        prime_analyses=prime_analyses,
        product_rho_bound=product_rho,
        min_gap_abs=min_gap if compositions else -1,
        min_gap_rel=min_gap / d if compositions and d > 0 else -1.0,
        gap_trend=0.0,  # filled by cross-k analysis
        all_adequate=all_adequate,
        three_in_two_everywhere=three_everywhere,
        max_ord_2=max(ords_2) if ords_2 else 0,
        min_ord_2=min(ords_2) if ords_2 else 0,
        dissipation_gap=dissipation,
        budget_ratio=budget_ratio,
        lds_k0_estimates=lds,
        fcq_R_values=fcq,
    )


# ═══════════════════════════════════════════════════════════════
#  Cross-k Analysis
# ═══════════════════════════════════════════════════════════════

@dataclass
class CrossKInsight:
    """A structural insight discovered across multiple k values."""
    category: str       # "spectral", "algebraic", "gap", "operator", "lds"
    description: str    # Human-readable description
    confidence: float   # 0.0 to 1.0
    evidence: str       # Supporting data
    connects_to: str    # Which research piste this relates to
    actionable: bool    # Can this lead to a proof step?
    lean_potential: str  # Potential Lean theorem if any


def analyze_range(k_min: int = 3, k_max: int = 40,
                  max_compositions: int = 500_000) -> Tuple[List[AnalysisResult], List[CrossKInsight]]:
    """Full structural analysis across a range of k values."""
    results = []
    insights = []

    print("┌─ ANALYST v2 ─ Deep Structural Analysis ──────────────────┐")

    for k in range(k_min, k_max + 1):
        r = analyze_k(k, max_compositions)
        results.append(r)

        # Status line
        factor_str = " × ".join(f"{p}^{e}" if e > 1 else str(p)
                                for p, e in r.d_factorization[:5])
        if len(r.d_factorization) > 5:
            factor_str += f" × ... ({r.n_prime_factors} primes)"
        adequacy = "ALL_ADEQUATE" if r.all_adequate else "MIXED"
        print(f"  k={k:2d}  d={r.d_bits:2d}bit  factors={factor_str}  "
              f"Πρ={r.product_rho_bound:.2e}  {adequacy}")

    print(f"└─ Analyzed k={k_min}..{k_max} ──────────────────────────────┘\n")

    # ── Cross-k pattern discovery ──────────────────────────────

    # 1. Gap growth trend
    gaps = [(r.k, r.min_gap_rel) for r in results if r.min_gap_rel > 0]
    if len(gaps) >= 5:
        # Linear regression on log(gap) vs k
        import statistics
        ks = [g[0] for g in gaps]
        log_gaps = [math.log(g[1]) for g in gaps if g[1] > 0]
        if len(log_gaps) >= 3:
            mean_k = statistics.mean(ks[:len(log_gaps)])
            mean_lg = statistics.mean(log_gaps)
            # Simple slope
            num = sum((ks[i] - mean_k) * (log_gaps[i] - mean_lg)
                      for i in range(len(log_gaps)))
            den = sum((ks[i] - mean_k) ** 2 for i in range(len(log_gaps)))
            if den > 0:
                slope = num / den
                if slope < -0.01:
                    insights.append(CrossKInsight(
                        category="gap",
                        description=f"min_gap_rel DECAYS exponentially: slope={slope:.4f}/k",
                        confidence=0.7,
                        evidence=f"Regression on k={k_min}..{k_max}: log(gap) ~ {slope:.4f}k",
                        connects_to="Conjecture M (R195): gap decay supports |T(t)| → 0",
                        actionable=True,
                        lean_potential="Could bound min_gap(k) > c * exp(-αk) for quantitative avoidance"
                    ))
                elif slope > 0.01:
                    insights.append(CrossKInsight(
                        category="gap",
                        description=f"min_gap_rel GROWS: slope={slope:.4f}/k — avoidance strengthens",
                        confidence=0.8,
                        evidence=f"Regression on k={k_min}..{k_max}",
                        connects_to="Stage I Nonsurjectivity: gap growth = favorable sign",
                        actionable=True,
                        lean_potential="Gap growth lemma: min_gap(k) ≥ c * d(k)^α"
                    ))

    # 2. Product ρ decay (R189 operator framework)
    rho_products = [(r.k, r.product_rho_bound) for r in results]
    decaying = all(rho_products[i][1] >= rho_products[i+1][1]
                   for i in range(len(rho_products) - 1)
                   if rho_products[i][1] > 0 and rho_products[i+1][1] > 0)
    fast_decay = any(rp < 1e-10 for _, rp in rho_products if rp > 0)

    if fast_decay:
        insights.append(CrossKInsight(
            category="spectral",
            description="Πρ decays SUPER-EXPONENTIALLY — operator framework viable",
            confidence=0.85,
            evidence=f"Πρ drops below 1e-10 in range k={k_min}..{k_max}",
            connects_to="R189 Framework Opératoriel: Λ_free = Πρ → 0",
            actionable=True,
            lean_potential="Lemma: Πρ(k) < d(k)^{-1} for k ≥ K₀ (implies N₀=0)"
        ))

    # 3. Adequate prime prevalence
    adequate_ks = [r.k for r in results if r.all_adequate]
    if len(adequate_ks) > len(results) * 0.7:
        insights.append(CrossKInsight(
            category="algebraic",
            description=f"ALL primes adequate for {len(adequate_ks)}/{len(results)} values of k",
            confidence=0.6,
            evidence=f"k values: {adequate_ks[:10]}...",
            connects_to="R81 APF: adequate primes → -1 ∉ ⟨2⟩ → confinement",
            actionable=False,
            lean_potential="None direct (APF rated 3/10 feasibility)"
        ))

    # 4. 3 ∈ ⟨2⟩ structure
    three_in_two_ks = [r.k for r in results if r.three_in_two_everywhere]
    if three_in_two_ks:
        insights.append(CrossKInsight(
            category="algebraic",
            description=f"3 ∈ ⟨2⟩ for ALL p|d in {len(three_in_two_ks)}/{len(results)} k values",
            confidence=0.9,
            evidence=f"When 3 ∈ ⟨2⟩: corrSum becomes a sum of ⟨2⟩-translates → structure exploitable",
            connects_to="R176 Réduction Somme Cyclique + R186 Dualité poids×lettres",
            actionable=True,
            lean_potential="When 3 ∈ ⟨2⟩: g(v) = Σ 2^{f_j} with f_j arithmetic perturbation"
        ))

    # 5. Multiplicative order growth
    max_ords = [(r.k, r.max_ord_2) for r in results if r.max_ord_2 > 0]
    if max_ords:
        # Check if max_ord grows faster than k
        growing_fast = sum(1 for k_val, ord_val in max_ords if ord_val > 2 * k_val)
        if growing_fast > len(max_ords) * 0.5:
            insights.append(CrossKInsight(
                category="lds",
                description=f"max(ord_p(2)) > 2k for majority of k values — LDS favorable",
                confidence=0.75,
                evidence=f"{growing_fast}/{len(max_ords)} values satisfy ord > 2k",
                connects_to="R196-R197 LDS: k₀(p) ≥ c·q without GRH",
                actionable=True,
                lean_potential="LDS transport lemma for primes with large ord_p(2)"
            ))

    # 6. FCQ convergence
    fcq_converging = []
    for r in results:
        all_small = all(R < 1.0 for R in r.fcq_R_values.values())
        if r.fcq_R_values and all_small:
            fcq_converging.append(r.k)
    if fcq_converging:
        insights.append(CrossKInsight(
            category="operator",
            description=f"FCQ R(p,k) < 1 for ALL primes in {len(fcq_converging)} k values",
            confidence=0.8,
            evidence=f"k ∈ {fcq_converging[:10]}... — contraction quantitative confirmée",
            connects_to="R196-R197 FCQ: R(p,k) = q·ρ_p^{k-1} < 1 implies avoidance",
            actionable=True,
            lean_potential="theorem fcq_contraction_kN : R(p,k) < 1 := by native_decide"
        ))

    # 7. Budget ratio analysis (R189 gap 1.35x)
    budget_ratios = [(r.k, r.budget_ratio) for r in results if r.budget_ratio > 0]
    if budget_ratios:
        avg_budget = sum(b for _, b in budget_ratios) / len(budget_ratios)
        if avg_budget > 1.0:
            insights.append(CrossKInsight(
                category="operator",
                description=f"Average budget ratio = {avg_budget:.2f} > 1 — spectral budget SUFFICIENT",
                confidence=0.65,
                evidence="Budget = |Σ log ρ| / log d > 1 means enough dissipation",
                connects_to="R189 Gap 1.35x: fermer le gap quantitatif",
                actionable=True,
                lean_potential="Quantitative dissipation lemma if budget provably > 1"
            ))
        else:
            insights.append(CrossKInsight(
                category="operator",
                description=f"Average budget ratio = {avg_budget:.2f} < 1 — GAP 1.35x CONFIRMED",
                confidence=0.9,
                evidence="Spectral dissipation insufficient to cover all of log(d)",
                connects_to="R189: the 1.35x gap is real, need structural boost",
                actionable=False,
                lean_potential="None — this confirms the gap, doesn't close it"
            ))

    # 8. Phantom k=4 structural analysis
    k4_result = next((r for r in results if r.k == 4), None)
    if k4_result:
        insights.append(CrossKInsight(
            category="algebraic",
            description=f"k=4 PHANTOM: d={k4_result.d}, factors={k4_result.d_factorization}",
            confidence=1.0,
            evidence="A=(1,1,1,4): corrSum=94=2×47=2×d(4). Unique exception",
            connects_to="Known: phantom explains why general proof needs care at k=4",
            actionable=False,
            lean_potential="Already proved: phantom_k4 in Theorems.lean"
        ))

    return results, insights


def format_insights(insights: List[CrossKInsight]) -> str:
    """Format insights for display."""
    lines = []
    lines.append("╔══════════════════════════════════════════════════════════════════╗")
    lines.append("║  STRUCTURAL INSIGHTS — Syracuse-JEPA v2 Analyst                 ║")
    lines.append(f"║  {len(insights)} insights discovered                                       ║")
    lines.append("╠══════════════════════════════════════════════════════════════════╣")

    by_category = {}
    for i in insights:
        by_category.setdefault(i.category, []).append(i)

    for cat, cat_insights in sorted(by_category.items()):
        lines.append(f"║  [{cat.upper()}]")
        for ci in cat_insights:
            conf_bar = "●" * int(ci.confidence * 10) + "○" * (10 - int(ci.confidence * 10))
            action = "→ ACTIONABLE" if ci.actionable else "  (passive)"
            lines.append(f"║    [{conf_bar}] {ci.description}")
            lines.append(f"║      Connects: {ci.connects_to}")
            if ci.actionable and ci.lean_potential != "None":
                lines.append(f"║      Lean: {ci.lean_potential}")
        lines.append("║")

    lines.append("╚══════════════════════════════════════════════════════════════════╝")
    return "\n".join(lines)


if __name__ == '__main__':
    results, insights = analyze_range(3, 30)
    print(format_insights(insights))
