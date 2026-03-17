"""
Knowledge Base — Research Map Integration (Syracuse-JEPA v2)

Encodes the state of research from RESEARCH_MAP.md:
- Open pistes with feasibility/impact ratings
- Closed pistes with reasons
- Key results (proved theorems, known bounds)
- Connections between pistes

This prevents the AI from re-exploring dead ends.
"""

from dataclasses import dataclass
from typing import List, Optional


@dataclass
class ResearchPiste:
    """One research direction from the map."""
    name: str
    description: str
    status: str          # "open", "closed", "proved", "conditional"
    feasibility: int     # 1-10
    impact: int          # 1-10
    round_ref: str       # R-number reference
    key_result: str      # what was established
    blocker: str         # what prevents progress
    connects_to: List[str]  # related pistes


@dataclass
class ProvedResult:
    """A mathematically proved result."""
    name: str
    statement: str
    proof_type: str      # "native_decide", "analytical", "conditional"
    condition: str       # "" if unconditional
    round_ref: str


# ═══════════════════════════════════════════════════════════════
#  Knowledge Base Construction
# ═══════════════════════════════════════════════════════════════

def build_knowledge_base() -> dict:
    """Build the complete knowledge base from research history."""

    # ── PROVED RESULTS ────────────────────────────────────────

    proved = [
        ProvedResult(
            name="Nonsurjectivity",
            statement="C(k) < d(k) for k ≥ 18 (entropy deficit γ ≈ 0.05)",
            proof_type="analytical",
            condition="",
            round_ref="R194"
        ),
        ProvedResult(
            name="Junction Theorem",
            statement="SdW (k ≤ 68) ∪ entropic (k ≥ 18) covers all k ≥ 2",
            proof_type="analytical",
            condition="",
            round_ref="R194"
        ),
        ProvedResult(
            name="Finite verification k=3..20",
            statement="N₀(d(k)) = 0 for k = 3..20 (except k=4 phantom)",
            proof_type="native_decide",
            condition="",
            round_ref="R194"
        ),
        ProvedResult(
            name="n_min argument k=21..41",
            statement="N₀(d(k)) = 0 for k = 21..41 via Steiner n_min bound",
            proof_type="analytical",
            condition="",
            round_ref="R171"
        ),
        ProvedResult(
            name="|ρ_a| < 1",
            statement="Strict dissipation: |ρ_a| < 1 unconditionally for all a",
            proof_type="analytical",
            condition="",
            round_ref="R191"
        ),
        ProvedResult(
            name="Λ_free factorization",
            statement="Λ_free = Π ρ_{a_j} factorizes over prime components",
            proof_type="analytical",
            condition="",
            round_ref="R191"
        ),
        ProvedResult(
            name="Gap 1.35x structural",
            statement="Monotonicity creates structural gap of factor 1.35x",
            proof_type="analytical",
            condition="",
            round_ref="R191"
        ),
        ProvedResult(
            name="LDS k₀(p) ≥ c·q",
            statement="k₀(p) ≥ (1/25)·ord_p(2) without GRH",
            proof_type="analytical",
            condition="",
            round_ref="R197"
        ),
        ProvedResult(
            name="FCQ ρ₅ = 1/4",
            statement="ρ₅ = 1/4 exactly, R(5,18) ≈ 2.3×10⁻¹⁰",
            proof_type="analytical",
            condition="",
            round_ref="R197"
        ),
        ProvedResult(
            name="ord_p(2) ≥ 3",
            statement="For all p|d(k): ord_p(2) ≥ 3",
            proof_type="analytical",
            condition="",
            round_ref="R197"
        ),
        ProvedResult(
            name="Duality discrepancy/reachability",
            statement="Monotonicity HELPS reachability, HURTS discrepancy",
            proof_type="analytical",
            condition="",
            round_ref="R192"
        ),
        ProvedResult(
            name="F_Z non-annulation",
            statement="F_Z = 4^m - 9^m - 17·6^{m-1} ≠ 0 verified k ≤ 10001",
            proof_type="native_decide",
            condition="Gap 0.0088% of k remain",
            round_ref="R198"
        ),
        ProvedResult(
            name="Filet 3 mailles",
            statement="168 primes tested, 0 failures",
            proof_type="analytical",
            condition="",
            round_ref="R195"
        ),
    ]

    # ── OPEN PISTES (ranked by score = feasibility × impact) ──

    open_pistes = [
        ResearchPiste(
            name="Framework Opératoriel (dissipation)",
            description="Operator propagation, transfer matrix, spectral gap, dissipation rate Λ_a",
            status="open",
            feasibility=7, impact=10,
            round_ref="R189-R191",
            key_result="12 proved, |ρ_a|<1 unconditional, gap 1.35x quantified",
            blocker="Closing the 1.35x quantitative gap (budget ~1.17 vs required ~1.585)",
            connects_to=["Gap 1.35x", "Opérateur Λ(s)", "Bornes de Weil"]
        ),
        ResearchPiste(
            name="Opérateur Λ(s) et méthode du col",
            description="N_cycle = (1/d)Σ_s Λ(s). Bound Λ(s) for s≥1 suffices",
            status="open",
            feasibility=7, impact=10,
            round_ref="R189",
            key_result="Second moment recovers k≥42 (coherent with Block 1)",
            blocker="Saddle point analysis on Λ(s) beyond second moment",
            connects_to=["Framework Opératoriel", "Conjecture M"]
        ),
        ResearchPiste(
            name="LDS (Levier Diophantien Structurel)",
            description="k₀(p) ≥ c·q WITHOUT GRH via continued fractions of θ=log₂3",
            status="open",
            feasibility=8, impact=10,
            round_ref="R196-R197",
            key_result="c ≥ 1/25 for q ≤ 15600, ord_p(2)≥3 proved, P₀ bypassed",
            blocker="Extending to all primes, connecting to full avoidance",
            connects_to=["FCQ", "Transport affine", "Conjecture M"]
        ),
        ResearchPiste(
            name="FCQ (Fronde Complémentarité Quantitative)",
            description="R(p,k) = q·ρ_p^{k-1} < 1 implies avoidance",
            status="open",
            feasibility=8, impact=9,
            round_ref="R196-R197",
            key_result="R(5,18) ≈ 2.3×10⁻¹⁰, ρ₅=1/4 exact, gap p=5 CLOSED",
            blocker="Uniform ρ_p < 1-ε across all primes",
            connects_to=["LDS", "Framework Opératoriel"]
        ),
        ResearchPiste(
            name="DBA (Baker sur F_Z)",
            description="Baker-Wüstholz bounds on |F_Z| > d^{1-ε}",
            status="open",
            feasibility=8, impact=9,
            round_ref="R197",
            key_result="Scheme designed, connects to Bennett 2004 Pillai",
            blocker="Technical execution (3-6 months estimate)",
            connects_to=["F_Z non-annulation", "Conjecture M"]
        ),
        ResearchPiste(
            name="Conjecture M (borne lacunaire T(t))",
            description="|T(t)| ≤ C·k^{-δ} for t ≠ 0. THE MAIN BLOCKER",
            status="open",
            feasibility=6, impact=10,
            round_ref="R195-R196",
            key_result="CGT 5-6.5/10, PRC 7/10 exploits lacunarity",
            blocker="|G(a)| ≤ √r FALSE in regime r < √p. Artin potentially bypassable via LDS",
            connects_to=["Framework Opératoriel", "LDS", "FCQ", "PRC"]
        ),
        ResearchPiste(
            name="Fermer le gap 1.35x",
            description="Close the quantitative gap in operator framework",
            status="open",
            feasibility=7, impact=10,
            round_ref="R189",
            key_result="4 sub-paths: (A) orbits ⟨3⟩, (B) spectral compression, (C) double counting, (D) Berry-Esseen",
            blocker="None of the 4 sub-paths completed yet",
            connects_to=["Framework Opératoriel", "Bornes de Weil"]
        ),
        ResearchPiste(
            name="Dualité poids × lettres (Horner)",
            description="Automate Horner, duality ord_p(3) × ord_p(2)",
            status="open",
            feasibility=6, impact=9,
            round_ref="R186",
            key_result="12 results proved. Cosets imposed: z_1∈⟨2⟩, z_{k-1}∈-3⁻¹⟨2⟩",
            blocker="Not tested in combined form",
            connects_to=["Noyau impair h(v)", "Cône monotone"]
        ),
        ResearchPiste(
            name="Filet 3 mailles (rigoreux)",
            description="Transport affine + contraction convolution + poissons fantômes",
            status="open",
            feasibility=6, impact=9,
            round_ref="R195",
            key_result="168 primes, 0 failures. Barrier density E≤C·q³/2^q",
            blocker="Making the density barrier rigorous",
            connects_to=["LDS", "FCQ"]
        ),
        ResearchPiste(
            name="F_Z non-annulation analytique",
            description="F_Z=4^m-9^m-17·6^{m-1} ≠ 0 for all m",
            status="open",
            feasibility=8, impact=7,
            round_ref="R195-R198",
            key_result="Gap reduced to 0.0088% of k. 7 dangerous k eliminated",
            blocker="Baker (DBA) = bottleneck 3-6 months",
            connects_to=["DBA", "Conjecture M"]
        ),
    ]

    # ── CLOSED PISTES (top reasons) ────────────────────────────

    closed_reasons = {
        "Sommes de Gauss / CRT": "6 attempts fail. Lock = exponential sums on partitions (open TAN)",
        "Géométrie des nombres / réseaux": "Additive/multiplicative mismatch irreducible",
        "Compression spectrale pure": "Aliasing standard, no quantitative gain",
        "Anneau Quotient": "Formal-arithmetic gap insurmountable without (2,3) specificity",
        "Weyl/Weil/Large Sieve direct": "Simplex ≠ interval, not applicable",
        "Contraction par étape": "REFUTED: norms GROW (average ratio 1.578)",
        "K-lite as universal tool": "Model discrepancy: ⟨g²⟩ ≠ ⟨2⟩",
        "Produit scalaire périodique-monotone": "Rebranding of g(v)≡0 mod p",
        "Voie bilinéaire courte": "5 tools all circular in O(log p) regime",
        "GSE / ALO / RP": "Too weak or technically blocked",
        "×2-closure Im_int(g)": "IRREPARABLE by combinatorial shift (R195)",
    }

    # ── STRATEGIC SYNTHESIS ────────────────────────────────────

    strategy = {
        "top_3_pistes": [
            ("LDS + FCQ combined", 8.5, "R196-R197",
             "Transport for small primes + FCQ contraction for large primes"),
            ("Operator Framework + Gap closure", 7.0, "R189-R191",
             "If gap 1.35x can be closed via sub-path A/B/C/D"),
            ("DBA + F_Z analytique", 8.0, "R197-R198",
             "Baker bounds on F_Z plus finite verification"),
        ],
        "recommended_next_steps": [
            "1. COMPUTE: spectral data (ord_p(2), ρ_p) for d(k) up to k=100",
            "2. VERIFY: FCQ R(p,k)<1 threshold — exact k₀ where all primes contract",
            "3. ANALYZE: gap 1.35x sub-paths — which has best data support?",
            "4. FORMALIZE: LDS transport lemma in Lean 4",
            "5. CONNECT: link DBA scheme to existing F_Z computations",
        ],
        "critical_open_question":
            "Can we prove uniform ρ_p < 1-ε for ALL p|d(k)? "
            "This is the single question that, if answered, closes everything via FCQ.",
    }

    return {
        'proved': proved,
        'open_pistes': open_pistes,
        'closed_reasons': closed_reasons,
        'strategy': strategy,
    }


def get_relevant_pistes(insights: list, conjectures: list) -> List[ResearchPiste]:
    """Filter pistes relevant to discovered insights and conjectures."""
    kb = build_knowledge_base()
    relevant = []

    # Match by keyword in connects_to
    keywords = set()
    for i in insights:
        if hasattr(i, 'connects_to'):
            keywords.update(i.connects_to.lower().split())
    for c in conjectures:
        if hasattr(c, 'connects_to'):
            keywords.update(c.connects_to.lower().split())

    for piste in kb['open_pistes']:
        name_lower = piste.name.lower()
        if any(kw in name_lower for kw in keywords if len(kw) > 3):
            relevant.append(piste)

    # Always include top-rated pistes
    for piste in kb['open_pistes']:
        if piste.feasibility * piste.impact >= 70 and piste not in relevant:
            relevant.append(piste)

    return relevant


def check_not_closed(approach: str) -> Optional[str]:
    """Check if an approach matches a closed piste. Returns reason if closed."""
    kb = build_knowledge_base()
    approach_lower = approach.lower()
    for name, reason in kb['closed_reasons'].items():
        if any(word in approach_lower for word in name.lower().split()
               if len(word) > 4):
            return f"CLOSED ({name}): {reason}"
    return None
