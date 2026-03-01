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
│   └── exploration/                    # Research exploration (17 scripts)
│       ├── phase20_*.py                # CRT, mixing, type classification
│       ├── phase21_*.py                # Mellin spectral, second moment, etc.
│       └── phase22_*.py                # CRT amplification, spectral bounds
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

A systematic investigation (GPS methodology, 6 deliverables) has verified the key quantitative condition:

| Component | Status | Details |
|-----------|--------|---------|
| Condition (Q): $\|\sum T(t)\| \leq 0.041 C$ | **Verified** k=18..28 | 25 cases, 0 failures |
| Coset orbit structure | **Verified** | $N_r$ approx. constant on $\langle 2 \rangle$-orbits (max deviation 2.2%) |
| Multi-scale decomposition | **Semi-rigorous** | 3 regimes (trivial / Cauchy-Schwarz / residual) |
| Cauchy-Schwarz covers p > 10 | **Verified** | 95% of cases, margin 7x-2800x |
| Decay rate for p = 7 | **Observed** | $\sim k^{-6.3}$, verified k=22..38 |
| **Residual lock** | Open | Prove $\|p \cdot N_0(7) - C\|/C \to 0$ at rate $\geq k^{-1}$ |

Worst case: k=22, p=7, ratio=0.013, margin=3.2x. See [`scripts/core/verify_condition_q.py`](scripts/core/verify_condition_q.py) and [`research_log/sp5_investigation.md`](research_log/sp5_investigation.md).

## Honest Assessment

This work establishes an **unconditional** structural obstruction (nonsurjectivity of the evaluation map) but does **not** prove the full nonexistence of cycles.

The gap between "the evaluation map omits residues" and "the evaluation map omits 0 specifically" is quantified precisely:

- The **Peeling Lemma** gives $N_0(p) \leq 0.63\,C$ (unconditional).
- The **Square Root Barrier** shows no purely spectral method suffices when $p \sim C^{1+o(1)}$.
- **Theorem Q** reduces the complete conjecture to the single condition $|\sum T(t)| \leq 0.041\,C$.
- Three precise conjectures (Horner equidistribution, spectral gap, uniform proportion) form a conditional chain toward the full resolution.

A hybrid strategy combining direct DP verification (k <= 40) and asymptotic decay (k >= 41) appears feasible (estimated 3.5/5) for establishing Condition (Q) for all k >= 18.

We believe in transparent science: see [`research_log/phase13_audit_kolmogorov_baker.md`](research_log/phase13_audit_kolmogorov_baker.md) for a detailed self-audit of a rejected proof attempt, and [`research_log/sp5_investigation.md`](research_log/sp5_investigation.md) for the full SP5 investigation log.

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
