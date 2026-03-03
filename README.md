# Entropic Barriers and Nonsurjectivity in the 3x+1 Problem: The Junction Theorem

**Author:** Eric Merle
**Date:** February 2026
**Status:** Preprint
**MSC 2020:** 11B83 (primary), 37A45, 94A17 (secondary)

---

## Abstract

We study the subproblem of nonexistence of nontrivial positive cycles in the Collatz dynamics. By revisiting Steiner's equation (1977) through the lens of information theory, we identify a universal entropic deficit:

$$\gamma = 1 - h\!\left(\frac{1}{\log_2 3}\right) \approx 0.0500$$

where $h$ denotes binary Shannon entropy. This deficit implies that the modular evaluation map $\mathrm{Ev}_d$ cannot be surjective for any cycle candidate of length $k \geq 18$ (**unconditional**). Combined with the computational bound of Simons and de Weger (2005) for $k \leq 68$, we obtain a **Junction Theorem**: for every $k \geq 2$, at least one obstruction -- computational or entropic -- applies.

The residual question -- excluding the specific residue $0$ from the image -- is formulated as an **Exponential Equidistribution Hypothesis** (H), approached via character sum analysis, Weil-type bounds, and the Mellin--Fourier bridge. The complete analysis reduces the nonexistence of cycles to a single quantitative condition (**Theorem Q**): $|\sum T(t)| \leq 0.041 C$.

## Key Results

| Result | Statement | Status |
|--------|-----------|--------|
| **Theorem 1** (Nonsurjectivity) | For $k \geq 18$: $\binom{S-1}{k-1} < 2^S - 3^k$ | Unconditional |
| **Theorem 2** (Junction) | For every $k \geq 2$: computational OR entropic obstruction | Unconditional |
| **Peeling Lemma** | $N_0(p) \leq (k{-}1)/(S{-}1) \cdot C \approx 0.63\,C$ | Unconditional |
| **Parseval cost** | If a cycle exists: $\sum\|T(t)\|^2 \geq (p-C)^2/(p-1)$ | Unconditional |
| **Mellin--Fourier bridge** | Exact decomposition of $T(t)$ via multiplicative characters | Unconditional |
| **Square root barrier** | No purely spectral method closes the gap when $p \sim C^{1+o(1)}$ | Unconditional |
| **Prop. 22.1** | $N_0(d) = 0$ for $k = 3, \ldots, 17$ (exhaustive) | Unconditional |
| **corrSum parity** | $\mathrm{corrSum}(A)$ is always odd and never divisible by 3 | Unconditional |
| **Theorem Q** | If $\|\sum T(t)\| \leq 0.041 C$ for all $p \mid d$: no cycles | Conditional |
| **Conjecture M** | $\|T(t)\| \leq C \cdot k^{-\delta}$ for all $t, p \mid d$ | Open |

## Repository Structure

```
Collatz-Junction-Theorem/
├── .github/workflows/lean-check.yml    # CI: Lean 4 verification
├── .github/workflows/sp10-phase1.yml   # CI: SP10 Phase I (Q) k=69..500
├── LICENSE                             # MIT (code)
├── LICENSE-PAPER                       # CC-BY 4.0 (paper)
├── README.md
├── INVENTAIRE.md                       # Complete file catalog
│
├── paper/
│   ├── preprint_en.tex                 # English preprint (principal)
│   ├── preprint_fr.tex                 # French preprint (original)
│   ├── preprint.md                     # Markdown reference
│   └── Merle_2026_*.pdf                # Compiled PDF
│
├── lean/
│   ├── verified/                       # 73 theorems, 0 sorry, 0 axiom
│   │   └── CollatzVerified/Basic.lean  # Lean 4.15.0, no Mathlib
│   ├── skeleton/                       # ~58 theorems, 1 sorry, 1 axiom
│   │   ├── JunctionTheorem.lean        # Junction Theorem
│   │   ├── SyracuseHeight.lean         # Syracuse height (0 sorry)
│   │   ├── BinomialEntropy.lean        # Entropy bounds
│   │   ├── EntropyBound.lean           # Entropy via tangent
│   │   ├── ConcaveTangent.lean         # Concave tangent inequality
│   │   ├── LegendreApprox.lean         # Legendre contrapositive
│   │   └── FiniteCases.lean            # k in [18, 200] (183 cases)
│   ├── lakefile.lean                   # Mathlib v4.29.0-rc2
│   └── lean-toolchain                  # Lean 4.29.0-rc2
│
├── scripts/
│   ├── core/                           # Published verification (10 scripts)
│   │   ├── verify_nonsurjectivity.py   # Theorem 1 (k in [18, 500])
│   │   ├── multidimensional_mold.py    # Phase 14
│   │   ├── interdimensional_tension.py # Phase 15
│   │   ├── analytical_obstruction.py   # Phase 16
│   │   ├── keyhole_geometry.py         # Phase 17
│   │   ├── programme_merle.py          # Phase 18
│   │   ├── radar_mellin.py             # Phase 19
│   │   ├── verify_condition_q.py        # Condition (Q) for k=18..28
│   │   ├── stress_test.py              # 402 stress tests
│   │   └── numerical_audit.py          # 152 audit checks
│   └── exploration/                    # Research exploration (32 scripts)
│       ├── phase20_*.py                # CRT, mixing, type classification
│       ├── phase21_*.py                # Mellin spectral, second moment, etc.
│       ├── phase22_*.py                # CRT amplification, spectral bounds
│       ├── sp6_ghost_fish.py           # Ghost fish analysis (17 hard primes)
│       ├── sp6_ghost_fish_large.py     # Ghost fish for large primes (p > 10^6)
│       ├── sp6_tunnel_factors.py       # Tunnel: ord_p(2) of d(k) factors
│       ├── sp6_three_mesh_net.py       # Three-mesh net (168 primes, 0 failures)
│       ├── sp6_mersenne_direct.py      # Mersenne direct verification (q ≤ 127)
│       ├── sp7_*.py                    # Junction geology, gap scan
│       ├── sp8_*.py                    # Fish nature scan, tunnel analysis
│       ├── sp9_*.py                    # Extension k→500, D28 analysis, Voie 4
│       ├── sp10_*.py                   # Condition (Q) regime analysis (L1-L9)
│       ├── phase_a1_exhaustive_k18_25.py  # Phase A1: exhaustive DP k=18..25
│       ├── phase_a2_regime_b_extension.py # Phase A2: regime classification k=18..67
│       ├── phase_a2plus_ecm_cofactors.py  # Phase A2+: ECM factorization (12 cofactors)
│       └── phase_b3_PU_verify.py       # Phase B3: Proportion Uniformity verification
│
├── research_log/                       # Complete research journal
│   ├── phase10c--10m                   # Foundations (red team to crystal clash)
│   ├── phase11a--11c                   # Algebraic obstruction, LLL reduction
│   ├── phase12                         # Junction Theorem
│   ├── phase13                         # Self-audit (rejected attempt)
│   ├── phase14--19                     # Analytical development
│   ├── phase20--20d                    # 4 strategic approaches
│   ├── phase21                         # Mellin master + spectral analysis
│   ├── phase22                         # Lacunary bounds + CRT
│   ├── phase23--23f                    # Barriers, bypasses, additive energy
│   ├── sp5_investigation.md            # SP5: Condition (Q) via GPS methodology
│   ├── sp6_ghost_fish.md               # SP6: Ghost fish + three-mesh net (4/5)
│   ├── sp7_junction_geology.md         # SP7: Junction geology (4.75/5)
│   ├── sp8_fish_nature.md              # SP8: Fish nature in d(k) (4.85/5)
│   ├── sp9_formalization_and_extension.md # SP9: Extension k→500, D28-D30 (4.85/5)
│   ├── sp10_motor_b2_investigation.md  # SP10: Condition (Q) regime analysis (L1-L9)
│   ├── sp10_synthese_formelle.md       # SP10: Formal synthesis (propositions)
│   └── ERRATA.md                       # Corrections
│
├── audits/
│   ├── AUDIT_V1_CERTIFICATION.md       # Initial certification
│   ├── AUDIT_V2_CERTIFICATION.md       # Ultra-severe re-certification
│   ├── AUDIT_V3_CERTIFICATION.md       # DO-178C/IEC 61508 level
│   └── AUDIT_V4_MATHEMATIQUE.md        # Mathematical chain verification
│
└── docs/
    └── plans/                          # Design documents
        └── 2026-02-27-phase20-4-pistes-design.md
```

## Quick Start

### Read the paper

- **English preprint:** [`paper/preprint_en.tex`](paper/preprint_en.tex) (principal)
- **French preprint:** [`paper/preprint_fr.tex`](paper/preprint_fr.tex) (original)
- **Markdown:** [`paper/preprint.md`](paper/preprint.md)

### Reproduce the computations

```bash
# Core verification scripts (Phases 14--19)
python3 scripts/core/verify_nonsurjectivity.py
python3 scripts/core/analytical_obstruction.py
python3 scripts/core/programme_merle.py
python3 scripts/core/radar_mellin.py
python3 scripts/core/stress_test.py
python3 scripts/core/numerical_audit.py

# Condition (Q) verification (SP5 investigation)
python3 scripts/core/verify_condition_q.py

# Exploration scripts (Phases 20--22)
python3 scripts/exploration/phase22_exploration.py

# SP6: Three-mesh net verification
python3 scripts/exploration/sp6_three_mesh_net.py
python3 scripts/exploration/sp6_mersenne_direct.py
```

### Lean 4 formalization

**Verified core** (`lean/verified/`, Lean 4.15.0, no Mathlib):
- **73 theorems, 0 sorry, 0 axiom**
- Nonsurjectivity for k = 18--25, exhaustive zero-exclusion for q3
- Parity, coset classification, Parseval, CRT, Mellin radar
- CI: GitHub Actions (`lean-check.yml`)

**Research skeleton** (`lean/skeleton/`, Lean 4.29.0-rc2, Mathlib4):
- ~58 theorems, 1 residual sorry (k >= 201, numerically verified to 10^6)
- 1 axiom (Simons--de Weger, published result)
- Crystal nonsurjectivity proved for k in [18, 200] via 183 `native_decide` cases

## Numerical Evidence for Condition (Q)

A systematic investigation (GPS methodology, 6 phases, ~30 experiments) has verified the key quantitative condition:

| Component | Status | Details |
|-----------|--------|---------|
| Condition (Q): $\|\sum T(t)\| \leq 0.041 C$ | **Verified** k=18..28 | 25 cases, 0 failures |
| Coset orbit structure | **Verified** | $N_r$ approx. constant on $\langle 2 \rangle$-orbits (max deviation 2.2%) |
| Multi-scale decomposition | **Semi-rigorous** | 3 regimes (trivial / Cauchy-Schwarz / residual) |
| Cauchy-Schwarz covers p > 10 | **Verified** | 95% of cases, margin 7x-2800x |
| Decay rate for p = 7 | **Observed** | $\sim k^{-6.3}$, verified k=22..38 |
| Three-mesh net (SP6) | **Verified** | 168 primes (m ≤ 100), 0 failures |
| Ghost fish (SP6) | **Verified** | 72/72 hard primes are ghosts in danger zone |
| Mersenne direct (SP6) | **Verified** | All M_q with q ≤ 127, up to 3738 k-values |
| Two Barriers (SP6) | **Heuristic** | E ≤ Cq³/2^q → 0 super-exponentially |
| K_MAX = 63 (SP7) | **Verified** | Junction overlap [63,68] confirmed (168 primes) |
| Cat A geology (SP7) | **Verified** | 89 primes (ord>100, p<20000), ρ_max=0.280 |
| Fish-Tunnel (SP7) | **Verified** | 11 danger primes (ρ>0.5) absent from all d(k) |
| Gap scan (SP7) | **Verified** | 242 primes (k∈[69,120]), all pass |
| Fish nature (SP8) | **Verified** | 247 primes (k∈[69,300]), ρ_max=0.225, all pass |
| Orbit constraint (SP8) | **Proved** | 3^k ∈ ⟨2⟩ mod p for all p \| d(k) |
| Ratio bound (SP8) | **Verified** | p/m² ≤ 1.13 for all 247 effective primes |
| Cross-verification (SP8) | **Verified** | Top 5 cases confirmed with mpmath (50 digits) |
| Extended scan (SP9) | **Verified** | 541 primes (k∈[69,500]), ρ_max=0.255, all pass |
| Reduced divisibility D28 (SP9) | **Proved** | p \| (2^r − 3^k) with r = S mod m < m |
| Ratio bound extended (SP9) | **Verified** | p/m² ≤ 2.73 (1 outlier), 96.1% < 0.10 |
| Weil sufficient (SP9) | **Verified** | 529/541 (97.8%) have ρ\_Weil < 0.5 |
| Cross-verification (SP9) | **Verified** | All new worst cases confirmed with mpmath (50 digits) |
| Voie 4 bypass (SP9) | **Dead end** | No arithmetic obstruction for p ≥ 5 |
| **SP10 Regime A** (Di Benedetto) | **Verified** | k=69..200: 116/132 PASS, 0 FAIL; CI k=69..500 |
| **SP10 Regime B** (generic) | **Proved** | N(p,k\_crit)=0 via Beatty counting (n₃=(p-1)/m) |
| **SP10 Regime B** (general) | **N ≤ 1** | Three Distances Theorem (Steinhaus 1957) |
| **SP10 n₃ structure** | **Verified** | n₃·m \| p-1 (284/284), regime B empirically empty (0/284) |
| **SP10 3 ∈ ⟨2⟩** | **Verified** | 183/284 in regime A, 0 in regime B |
| **Complete factorization k=18..67** | **Verified** | d(k) fully factored (trial div + ECM), 190 primes |
| **Regime classification k=18..67** | **Verified** | 190/190 Regime A, 0/190 Regime B |
| **Regime B empty (extended)** | **Verified** | 0/474 pairs (k,p) for k ∈ [18,150] |

Worst case: k=22, p=7, ratio=0.013, margin=3.2x. See [`scripts/core/verify_condition_q.py`](scripts/core/verify_condition_q.py), [`research_log/sp5_investigation.md`](research_log/sp5_investigation.md), [`research_log/sp6_ghost_fish.md`](research_log/sp6_ghost_fish.md), [`research_log/sp7_junction_geology.md`](research_log/sp7_junction_geology.md), [`research_log/sp8_fish_nature.md`](research_log/sp8_fish_nature.md), and [`research_log/sp9_formalization_and_extension.md`](research_log/sp9_formalization_and_extension.md).

## Honest Assessment

This work establishes an **unconditional** structural obstruction (nonsurjectivity of the evaluation map) but does **not** prove the full nonexistence of cycles.

The gap between "the evaluation map omits residues" and "the evaluation map omits 0 specifically" is quantified precisely:

- The **Peeling Lemma** gives $N_0(p) \leq 0.63\,C$ (unconditional).
- The **Square Root Barrier** shows no purely spectral method suffices when $p \sim C^{1+o(1)}$.
- **Theorem Q** reduces the complete conjecture to the single condition $|\sum T(t)| \leq 0.041\,C$.
- Three precise conjectures (Horner equidistribution, spectral gap, uniform proportion) form a conditional chain toward the full resolution.
- The **three-mesh net** (SP6) covers all 168 tested primes with zero failures: affine transport (24), convolution (72), ghost fish (72).
- The **Two Barriers theorem** shows that for Mersenne primes M_q, the expected number of dangerous divisibilities is ≤ Cq³/2^q, super-exponentially small.
- **K_MAX = 63** (SP7): the worst prime (M_13) requires convolution only from k ≥ 63, providing a 6-rank overlap with Simons--de Weger (k ≤ 68).
- **Fish-Tunnel Incompatibility** (SP7): the 11 primes with ρ > 0.5 and ord > 100 are all ghost fish — none divides any d(k). Among 242 primes actually dividing d(k) for k ∈ [69, 120], all have ρ < 0.23.
- **Fish Nature** (SP8): extended to k ∈ [69, 300] with 247 primes, ρ_max = 0.225, ALL pass condition (Q). The orbit constraint 3^k ∈ ⟨2⟩ mod p is proved, and p/m² ≤ 1.13 observed universally. Cross-verified with mpmath (50 digits).
- **Formalization & Extension** (SP9): extended to k ∈ [69, 500] with 541 primes (119% increase), ρ_max = 0.255, ALL pass. New reduced divisibility theorem D28: p | (2^r − 3^k) with r < m. New worst ρ = 0.255 (D29). First p/m² > 1.5 found: p/m² = 2.73 (D30, 1 outlier out of 541). Voie 4 (arithmetic bypass) confirmed dead end for p ≥ 5.

The SP9 investigation confirms feasibility at **4.85/5**. The extended scan (541 primes, k → 500) with zero failures strengthens the empirical case substantially. The D30 discovery (p/m² = 2.73) partially refutes the SP8 hypothesis p/m² ≤ 1.25, but Weil remains sufficient for 97.8% of primes and ρ stays well below 0.5 even for outliers.

**Phase A2/A2+ (gap closure k=18..67):** Complete factorization of d(k) for all k ∈ [18, 67] by trial division + ECM reveals **190 prime factors, all in Regime A (0 in Regime B)**. This extends the "Regime B empty" pattern from k ∈ [69, 150] (284 pairs) to k ∈ [18, 150] (**474 pairs**, zero exceptions). For k ≤ 68, this provides independent structural confirmation complementing Simons--de Weger (2005). See [`scripts/exploration/phase_a2_regime_b_extension.py`](scripts/exploration/phase_a2_regime_b_extension.py) and [`scripts/exploration/phase_a2plus_ecm_cofactors.py`](scripts/exploration/phase_a2plus_ecm_cofactors.py).

**SP10** (Condition Q via Beatty sequences and Three Distances Theorem, L1--L9) provides the deepest analysis yet:
- **Regime A** (p < m⁴): closed by Di Benedetto et al. (2020) + finite verification (k=69..200, 0 failures, CI running k=69..500).
- **Regime B** (p ≥ m⁴, generic case n₃ = (p-1)/m): **closed** by Beatty counting argument showing k\_crit < n₃, hence N(p,k\_crit) = 0 rigorously.
- **Regime B** (general): N ≤ 1 by the Three Distances Theorem (Steinhaus 1957). Empirically N = 0 for all tested cases.
- **Key discovery**: among 284 pairs (k,p) with p | d(k), k=69..150, **zero** are in Regime B. The regime is empirically empty.
- **n₃ structure**: n₃·m | p-1 verified 100% (284/284). The argument requires only the trivial bound ρ ≤ 1 - 1/m — no BGK effectivity needed.

The complete factorization of d(k) for k ∈ [18, 67] raises the feasibility to **4.90/5**. Regime B is now empirically empty over 474 tested divisibility pairs. The residual gap is extremely narrow: proving N = 0 (instead of N ≤ 1) for non-generic n₃ in Regime B for k ≥ 69. Possible closures: (a) Baker p-adic to exclude the single candidate, (b) effective ρ < 1 - c/m^α with α < 1, (c) structural argument that 3 ∉ ⟨2⟩ for p ≥ m⁴, (d) effective Bourgain--Glibichuk--Konyagin with c ≥ 0.36.

We believe in transparent science: see [`research_log/phase13_audit_kolmogorov_baker.md`](research_log/phase13_audit_kolmogorov_baker.md) for a detailed self-audit of a rejected proof attempt, [`research_log/sp5_investigation.md`](research_log/sp5_investigation.md) for the SP5 investigation, [`research_log/sp6_ghost_fish.md`](research_log/sp6_ghost_fish.md) for the SP6 ghost fish analysis, [`research_log/sp7_junction_geology.md`](research_log/sp7_junction_geology.md) for the junction geology, [`research_log/sp8_fish_nature.md`](research_log/sp8_fish_nature.md) for the fish nature in d(k), [`research_log/sp9_formalization_and_extension.md`](research_log/sp9_formalization_and_extension.md) for the formalization and extension to k = 500, and [`research_log/sp10_synthese_formelle.md`](research_log/sp10_synthese_formelle.md) for the SP10 Condition (Q) regime analysis with Beatty sequences and Three Distances Theorem.

## License

- **Code** (Lean proofs, Python scripts): [MIT License](LICENSE)
- **Paper** (preprints, documentation): [CC-BY 4.0](LICENSE-PAPER)

## References

1. R. E. Crandall, "On the 3x + 1 problem", *Math. Comp.* **32** (1978), 1281--1292.
2. S. Eliahou, "The 3x + 1 problem: new lower bounds on nontrivial cycle lengths", *Discrete Math.* **118** (1993), 45--56.
3. J. C. Lagarias, "The 3x + 1 problem and its generalizations", *Amer. Math. Monthly* **92** (1985), 3--23.
4. M. Laurent, M. Mignotte, Y. Nesterenko, "Formes lineaires en deux logarithmes et determinants d'interpolation", *J. Number Theory* **55** (1995), 285--321.
5. D. Simons, B. de Weger, "Theoretical and computational bounds for m-cycles of the 3n + 1 problem", *Acta Arith.* **117** (2005), 51--70.
6. R. P. Steiner, "A theorem on the Syracuse problem", *Proc. 7th Manitoba Conf. Numer. Math.* (1977), 553--559.
7. T. Tao, "Almost all orbits of the Collatz map attain almost bounded values", *Forum Math. Pi* **10** (2022), e12.
8. T. Barina, "Convergence verification of the Collatz problem", *J. Supercomput.* **77** (2021), 2681--2688.
9. D. Applegate, J. C. Lagarias, "The 3x + 1 semigroup", *J. Number Theory* **117** (2006), 146--159.
10. K. Soundararajan, "Moments of the Riemann zeta function", *Ann. Math.* **170** (2009), 981--993.
11. F. Di Benedetto, M. Z. Garaev, V. C. Garcia, D. Gonzalez-Sanchez, I. E. Shparlinski, C. A. Trujillo, "Exponential sums over small subgroups of F_p*", *J. Number Theory* **215** (2020), 261--274.
12. V. T. Sos, "On the distribution mod 1 of the sequence nα", *Annales Univ. Sci. Budapest.* **1** (1958), 127--134. (Three Distances Theorem)
