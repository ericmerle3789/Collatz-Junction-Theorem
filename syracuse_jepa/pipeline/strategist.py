"""
Strategist — Proof Direction Generator (Syracuse-JEPA v2)

The brain of the pipeline. Synthesizes:
- Structural analysis (Analyst)
- Pattern discoveries (Pattern Miner)
- Research history (Knowledge Base)

Outputs ranked proof strategies with concrete next steps.
"""

from dataclasses import dataclass
from typing import List, Dict, Optional

from syracuse_jepa.pipeline.analyst import AnalysisResult, CrossKInsight
from syracuse_jepa.pipeline.pattern_miner import (
    AsymptoticTrend, StructuralInvariant, GeneralConjecture
)
from syracuse_jepa.pipeline.knowledge import (
    build_knowledge_base, get_relevant_pistes, check_not_closed,
    ResearchPiste, ProvedResult
)


@dataclass
class ProofStrategy:
    """A ranked proof strategy with concrete steps."""
    name: str
    score: float           # 0-100 overall viability
    feasibility: float     # 0-10
    impact: float          # 0-10
    data_support: float    # 0-10 (how well the data supports this approach)
    description: str
    concrete_steps: List[str]
    required_lemmas: List[str]
    lean_targets: List[str]
    blockers: List[str]
    connects_to_pistes: List[str]
    based_on_evidence: List[str]


@dataclass
class StrategistReport:
    """Complete output of the Strategist."""
    strategies: List[ProofStrategy]
    critical_question: str
    data_summary: str
    recommended_action: str
    lean_roadmap: List[str]


def score_strategy(feasibility: float, impact: float,
                   data_support: float) -> float:
    """Score = geometric mean × 10 to avoid one low dimension dominating."""
    return (feasibility * impact * data_support) ** (1/3) * 10


# ═══════════════════════════════════════════════════════════════
#  Strategy Generation
# ═══════════════════════════════════════════════════════════════

def generate_strategies(
    analysis_results: List[AnalysisResult],
    insights: List[CrossKInsight],
    trends: List[AsymptoticTrend],
    invariants: List[StructuralInvariant],
    conjectures: List[GeneralConjecture],
) -> StrategistReport:
    """Generate ranked proof strategies from all available data."""

    kb = build_knowledge_base()
    strategies = []

    # ── Strategy 1: LDS + FCQ Combined Attack ─────────────────

    # Check data support for FCQ
    fcq_insight = next((i for i in insights if "FCQ" in i.description), None)
    fcq_conjecture = next((c for c in conjectures if "R(p,k)" in c.statement), None)
    rho_trend = next((t for t in trends if t.quantity == "log(Πρ)"), None)

    fcq_data_support = 5.0
    if fcq_insight and fcq_insight.confidence > 0.7:
        fcq_data_support += 2.0
    if fcq_conjecture and fcq_conjecture.evidence_strength > 0.5:
        fcq_data_support += 1.5
    if rho_trend and rho_trend.slope < -1.0:
        fcq_data_support += 1.5

    strategies.append(ProofStrategy(
        name="LDS + FCQ Combined Attack",
        score=score_strategy(8.0, 9.5, fcq_data_support),
        feasibility=8.0,
        impact=9.5,
        data_support=fcq_data_support,
        description=(
            "Use LDS (Diophantine lever) to handle primes with small ord_p(2) "
            "via transport argument, and FCQ (quantitative complementarity) "
            "for primes with large ord_p(2) where ρ_p^{k-1} → 0 fast. "
            "Together they cover ALL primes dividing d(k)."
        ),
        concrete_steps=[
            "1. PARTITION primes of d(k) into S_small = {p : ord_p(2) ≤ T} and S_large = {p : ord_p(2) > T}",
            "2. For S_small: apply LDS transport (k₀(p) ≥ ord_p(2)/25, proved R197). "
            "   Need: verify that k > k₀(p) for all small-order primes",
            "3. For S_large: apply FCQ (R(p,k) = ord_p(2) · ρ_p^{k-1}). "
            "   Need: prove uniform ρ_p ≤ 1 - c/√p for constant c",
            "4. COMBINE: if both S_small and S_large are handled, CRT gives N₀(d) = 0",
            "5. FORMALIZE: Lean theorems for each step",
        ],
        required_lemmas=[
            "Uniform ρ_p bound: ρ_p ≤ 1 - c/√p (THE key missing piece)",
            "LDS transport completeness for small-order primes",
            "CRT combination lemma: N₀(d) = 0 if N₀(p) = 0 for all p|d",
        ],
        lean_targets=[
            "theorem lds_transport (p k : Nat) (h_ord : ord_p_2 p ≤ T) (h_k : k > k0 p) : ...",
            "theorem fcq_contraction (p k : Nat) (h_ord : ord_p_2 p > T) : R p k < 1",
            "theorem avoidance_combined (k : Nat) (hk : k ≥ K₀) : N_zero k = 0",
        ],
        blockers=[
            "CRITICAL: uniform ρ_p bound. Currently ρ_p < 1 proved but no uniformity",
            "LDS threshold T needs to be determined",
            "CRT combination requires careful treatment of prime powers p^e || d",
        ],
        connects_to_pistes=["LDS (R196-R197)", "FCQ (R196-R197)", "Framework Opératoriel (R189)"],
        based_on_evidence=[
            f"FCQ contraction observed for {fcq_conjecture.n_verified if fcq_conjecture else '?'} k values",
            f"Πρ decay rate: {rho_trend.slope:.4f}/k" if rho_trend else "Πρ trend not computed",
        ],
    ))

    # ── Strategy 2: Operator Framework + Gap Closure ──────────

    budget_trend = next((t for t in trends if t.quantity == "budget_ratio"), None)
    spectral_insight = next((i for i in insights
                             if "spectral" in i.category.lower()), None)

    op_data_support = 5.0
    if budget_trend and budget_trend.slope > 0:
        op_data_support += 2.0
    if spectral_insight and spectral_insight.confidence > 0.7:
        op_data_support += 2.0

    strategies.append(ProofStrategy(
        name="Operator Framework + Gap 1.35x Closure",
        score=score_strategy(7.0, 10.0, op_data_support),
        feasibility=7.0,
        impact=10.0,
        data_support=op_data_support,
        description=(
            "The operator framework (R189) gives Λ_free = Π ρ_{a_j} and proves |ρ_a| < 1. "
            "The 1.35x gap means available budget (~1.17k log 2) is 1.35x short of required "
            "(~1.585k log 2). Four sub-paths to close it: "
            "(A) multiplicative structure of ⟨3⟩ orbits, "
            "(B) spectral compression from R185, "
            "(C) double counting orbits+partitions, "
            "(D) Berry-Esseen on operators."
        ),
        concrete_steps=[
            "1. COMPUTE: budget ratio for k=3..100 — identify if it improves with k",
            "2. ANALYZE: which sub-path (A/B/C/D) has best empirical support",
            "3. For sub-path A: study orbit structure of ⟨3⟩ acting on Z/pZ for primes p|d(k)",
            "4. For sub-path D: check if Berry-Esseen CLT applies to the product of transfer matrices",
            "5. If budget ratio → ∞ with k: the gap CLOSES asymptotically (most favorable)",
            "6. FORMALIZE: quantitative dissipation lemma in Lean",
        ],
        required_lemmas=[
            "Quantitative dissipation: |Λ_free| ≤ C · exp(-αk) with α > log(3)",
            "Budget accumulation lemma: each new prime factor adds > ε to budget",
            "Berry-Esseen bound for product of constrained random matrices",
        ],
        lean_targets=[
            "theorem dissipation_quantitative (k : Nat) (hk : k ≥ K₁) : ...",
            "theorem budget_sufficient (k : Nat) (hk : k ≥ K₂) : budget_ratio k > 1",
        ],
        blockers=[
            "The 1.35x gap is REAL — not an artifact. Closing it requires new math",
            "Sub-path A (orbits ⟨3⟩) depends on Artin's conjecture for ord_p(3)",
            "Sub-path D (Berry-Esseen) requires bounding operator norms",
        ],
        connects_to_pistes=["Framework Opératoriel (R189)", "Gap 1.35x (R189)", "Conjecture M (R195)"],
        based_on_evidence=[
            f"Budget trend: {budget_trend.slope:+.4f}/k" if budget_trend else "Not computed",
            f"Spectral decay: {rho_trend.slope:.4f}/k" if rho_trend else "Not computed",
        ],
    ))

    # ── Strategy 3: DBA + F_Z Analytical Route ────────────────

    strategies.append(ProofStrategy(
        name="DBA (Baker) + F_Z Complete Resolution",
        score=score_strategy(8.0, 7.0, 7.0),
        feasibility=8.0,
        impact=7.0,
        data_support=7.0,
        description=(
            "F_Z = 4^m - 9^m - 17·6^{m-1} controls whether specific cycle lengths exist. "
            "Verified ≠0 for k ≤ 10001. Gap = 0.0088% of k values. "
            "Baker-Wüstholz bounds (DBA) can prove |F_Z| > d^{1-ε} for m > m₀ effective. "
            "This would reduce the problem to finite verification."
        ),
        concrete_steps=[
            "1. IMPLEMENT Baker-Wüstholz bound computation for F_Z",
            "2. DETERMINE effective m₀ beyond which |F_Z| > d(k)^{1-ε}",
            "3. VERIFY: finite check for m ≤ m₀ (already done up to 10001)",
            "4. ANALYZE: the 0.0088% gap — are the remaining k values handleable?",
            "5. FORMALIZE: Baker bound as Lean theorem (conditional on DBA)",
        ],
        required_lemmas=[
            "Baker-Wüstholz: |4^m - 9^m - 17·6^{m-1}| > exp(-C·log(m)^2)",
            "Effective m₀ computation",
            "Finite verification closure for m ≤ m₀",
        ],
        lean_targets=[
            "theorem f_z_nonzero (m : Nat) (hm : m ≥ 2) : f_z m ≠ 0",
        ],
        blockers=[
            "Baker bounds are technically intensive (3-6 month estimate)",
            "Impact is 7/10 not 10/10: F_Z handles specific cycle lengths, not ALL",
            "Does not directly prove Conjecture M",
        ],
        connects_to_pistes=["DBA (R197)", "F_Z non-annulation (R195-R198)"],
        based_on_evidence=[
            "F_Z ≠ 0 verified for k ≤ 10001",
            "Gap reduced to 0.0088% via MCE correction (R198)",
        ],
    ))

    # ── Strategy 4: Hybrid Multi-scale (NEW — pipeline-driven) ─

    gap_trend = next((t for t in trends if "min_gap" in t.quantity), None)
    pf_trend = next((t for t in trends if "prime_factors" in t.quantity), None)

    hybrid_support = 4.0
    if gap_trend and gap_trend.slope > 0:
        hybrid_support += 2.0
    if pf_trend and pf_trend.slope > 0.2:
        hybrid_support += 2.0
    if any(c.evidence_strength > 0.8 for c in conjectures):
        hybrid_support += 2.0

    strategies.append(ProofStrategy(
        name="Hybrid Multi-scale (Pipeline-Driven Discovery)",
        score=score_strategy(6.0, 10.0, hybrid_support),
        feasibility=6.0,
        impact=10.0,
        data_support=hybrid_support,
        description=(
            "USE THE PIPELINE ITSELF as a discovery engine: "
            "extend k range progressively (40 → 100 → 200), compute spectral data "
            "at each scale, identify the EXACT threshold k₀ where avoidance becomes "
            "'easy' (all primes contract). Then use this threshold to split the proof: "
            "finite verification for k < k₀, analytical for k ≥ k₀."
        ),
        concrete_steps=[
            "1. EXTEND: run Analyst for k=41..100 (compute d(k) factorizations, spectral data)",
            "2. IDENTIFY: threshold k₀ where budget_ratio > 1 consistently",
            "3. STUDY: transition zone — what changes algebraically at k₀?",
            "4. FORMALIZE: k < k₀ by native_decide (extend current Lean proofs)",
            "5. PROVE: k ≥ k₀ by the strategy with best data support at that scale",
            "6. ITERATE: if k₀ is too large, find structure that reduces it",
        ],
        required_lemmas=[
            "Threshold identification lemma: ∃ k₀ such that budget > 1 for k ≥ k₀",
            "All finite k < k₀ verified by native_decide or n_min argument",
            "Analytical closure for k ≥ k₀ via operator framework or FCQ",
        ],
        lean_targets=[
            "-- Progressive: extend native_decide theorems to higher k",
            "-- Eventually: split theorem by k₀",
        ],
        blockers=[
            "Scalability: native_decide slows exponentially with k",
            "k₀ might be too large for finite verification",
            "Analytical proof still needed for k ≥ k₀",
        ],
        connects_to_pistes=["All open pistes — this is a META-strategy"],
        based_on_evidence=[
            f"Gap trend: {gap_trend.extrapolation}" if gap_trend else "Gap not computed",
            f"Prime factor growth: {pf_trend.slope:.3f}/k" if pf_trend else "Not computed",
        ],
    ))

    # ── Strategy 5: Monotonicity Exploitation (Battement Impossible) ─

    strategies.append(ProofStrategy(
        name="Battement Impossible (Resonance Obstruction)",
        score=score_strategy(7.0, 9.0, 6.0),
        feasibility=7.0,
        impact=9.0,
        data_support=6.0,
        description=(
            "From R189: g(v) - (3^k-1)/2 as restricted representation in mixed {3,2} numeration. "
            "The MONOTONICITY constraint on compositions creates a triple obstruction: "
            "sublattices 3^{k-1-j}·Z with monotone coefficients CANNOT resonate with d(k). "
            "This is a geometric argument about the impossibility of alignment."
        ),
        concrete_steps=[
            "1. FORMALIZE: the triple obstruction from monotonicity",
            "2. COMPUTE: alignment metrics — how far are compositions from resonance?",
            "3. PROVE: monotone compositions in mixed base {2,3} avoid lattice points of d·Z",
            "4. CONNECT: to operator framework (monotonicity = dissipation source)",
        ],
        required_lemmas=[
            "Mixed base representation: g(v) = Σ 3^{k-1-j} · 2^{B_j} with B monotone",
            "Resonance impossibility: monotone B cannot satisfy Σ ... ≡ 0 mod d",
            "Lattice distance lower bound from monotonicity",
        ],
        lean_targets=[
            "-- Requires formalizing mixed base + monotonicity constraints",
        ],
        blockers=[
            "The 'triple obstruction' is heuristic, not proved",
            "Monotonicity alone was shown to be 'not the real blocker' (R76)",
            "Need to combine with arithmetic structure of 2^S - 3^k",
        ],
        connects_to_pistes=["Battement impossible (R189)", "Dualité poids×lettres (R186)"],
        based_on_evidence=[
            "Triple obstruction described in R189",
            "Gap data supports resonance avoidance for all observed k",
        ],
    ))

    # ── Sort strategies by score ──────────────────────────────
    strategies.sort(key=lambda s: s.score, reverse=True)

    # ── Determine critical question ───────────────────────────
    critical = kb['strategy']['critical_open_question']

    # ── Data summary ──────────────────────────────────────────
    k_range = f"{min(r.k for r in analysis_results)}..{max(r.k for r in analysis_results)}"
    n_insights = len(insights)
    n_conjectures = len(conjectures)
    n_invariants = sum(1 for inv in invariants if inv.strength == "universal")

    data_summary = (
        f"Analyzed k={k_range}. {n_insights} structural insights, "
        f"{n_conjectures} conjectures, {n_invariants} universal invariants. "
        f"Key trends: Πρ decay {rho_trend.slope:.3f}/k, "
        f"prime factors grow {pf_trend.slope:.2f}/k. " if rho_trend and pf_trend else
        f"Analyzed k={k_range}. {n_insights} insights, {n_conjectures} conjectures."
    )

    # ── Recommended action ────────────────────────────────────
    best = strategies[0]
    recommended = (
        f"PRIORITY: {best.name} (score {best.score:.1f}/100). "
        f"NEXT STEP: {best.concrete_steps[0]}. "
        f"CRITICAL BLOCKER: {best.blockers[0] if best.blockers else 'none identified'}."
    )

    # ── Lean roadmap ──────────────────────────────────────────
    lean_roadmap = [
        "PHASE 1 (IMMEDIATE): Extend native_decide avoidance to k=41..68 (SdW range)",
        "PHASE 2 (SHORT-TERM): Formalize LDS transport lemma in Lean 4",
        "PHASE 3 (MEDIUM-TERM): Formalize FCQ contraction for specific primes",
        "PHASE 4 (LONG-TERM): Connect LDS+FCQ to prove uniform ρ bound",
        "PHASE 5 (GOAL): Prove N₀(d(k))=0 for all k ≥ 3 except phantom k=4",
    ]

    return StrategistReport(
        strategies=strategies,
        critical_question=critical,
        data_summary=data_summary,
        recommended_action=recommended,
        lean_roadmap=lean_roadmap,
    )


def format_report(report: StrategistReport) -> str:
    """Format the strategist report for display."""
    lines = []
    lines.append("")
    lines.append("╔══════════════════════════════════════════════════════════════════╗")
    lines.append("║  SYRACUSE-JEPA v2 — STRATEGIST REPORT                          ║")
    lines.append("║  Proof Direction Analysis                                       ║")
    lines.append("╠══════════════════════════════════════════════════════════════════╣")
    lines.append(f"║  {report.data_summary[:64]}")
    lines.append("╠══════════════════════════════════════════════════════════════════╣")

    lines.append("║")
    lines.append("║  CRITICAL OPEN QUESTION:")
    lines.append(f"║  {report.critical_question[:64]}")
    lines.append(f"║  {report.critical_question[64:128]}" if len(report.critical_question) > 64 else "║")
    lines.append("║")

    for i, s in enumerate(report.strategies):
        bar_len = int(s.score / 10)
        bar = "█" * bar_len + "░" * (10 - bar_len)
        lines.append(f"║  #{i+1} [{bar}] {s.name} (score={s.score:.1f})")
        lines.append(f"║      Feasibility={s.feasibility:.0f}  Impact={s.impact:.0f}  DataSupport={s.data_support:.0f}")
        lines.append(f"║      Next: {s.concrete_steps[0][:58]}")
        if s.blockers:
            lines.append(f"║      Blocker: {s.blockers[0][:56]}")
        lines.append("║")

    lines.append("╠══════════════════════════════════════════════════════════════════╣")
    lines.append("║  LEAN ROADMAP:")
    for step in report.lean_roadmap:
        lines.append(f"║    {step[:62]}")
    lines.append("║")
    lines.append("╠══════════════════════════════════════════════════════════════════╣")
    lines.append(f"║  RECOMMENDED: {report.recommended_action[:52]}")
    lines.append("╚══════════════════════════════════════════════════════════════════╝")

    return "\n".join(lines)
