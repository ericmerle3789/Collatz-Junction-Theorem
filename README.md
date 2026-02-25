# Entropic Barriers and Nonsurjectivity in the 3x+1 Problem: The Junction Theorem

**Author:** Eric Merle
**Date:** February 2026
**Status:** Preprint
**MSC 2020:** 11B83 (primary), 37P35, 94A17 (secondary)

---

## Abstract

We study the subproblem of nonexistence of nontrivial positive cycles in the Collatz dynamics. By revisiting Steiner's equation (1977) through the lens of information theory, we identify a universal entropic deficit:

$$\gamma = 1 - h\!\left(\frac{1}{\log_2 3}\right) \approx 0.0500$$

where $h$ denotes binary Shannon entropy. This deficit implies that the modular evaluation map $\mathrm{Ev}_d$ cannot be surjective for any cycle candidate of length $k \geq 18$ (**unconditional**). Combined with the computational bound of Simons and de Weger (2005) for $k < 68$, we obtain a **Junction Theorem**: for every $k \geq 2$, at least one obstruction — computational or entropic — applies.

The residual question — excluding the specific residue $0$ from the image — is formulated as an **Exponential Equidistribution Hypothesis** (H), supported by extensive numerical evidence and motivated by Weil-type character sum cancellation.

## Key Results

| Result | Statement | Status |
|--------|-----------|--------|
| **Theorem 1** | For $k \geq 18$ with $d > 0$: $\binom{S-1}{k-1} < d$ | Unconditional |
| **Theorem 2** (Junction) | For every $k \geq 2$: computational OR entropic obstruction applies | Unconditional |
| **Hypothesis (H)** | $0 \notin \mathrm{Im}(\mathrm{Ev}_d)$ for $k \geq 68$ | Conditional |

### The Three Regimes

| Regime | Convergents | $C/d$ | Elimination |
|--------|------------|-------|-------------|
| Residual | $q_3 = 5$ | 2.69 | Simons-de Weger |
| Frontier | $q_5 = 41$ | 0.596 | Both (overlap zone) |
| Crystalline | $q_7 = 306$ | $\approx 2^{-20}$ | Nonsurjectivity |

## Repository Structure

```
Collatz-Junction-Theorem/
├── README.md                    # This file
├── LICENSE                      # MIT License
├── paper/
│   ├── preprint.md              # Full manuscript (French, Markdown)
│   ├── preprint.tex             # LaTeX stub (amsart, ready for full conversion)
│   └── Merle_2026_*.pdf         # PDF preprint
├── lean/
│   ├── SyracuseHeight.lean      # Lean 4 skeleton: Syracuse height formalization
│   └── JunctionTheorem.lean     # Lean 4 skeleton: Junction Theorem (7 sorry + 1 axiom)
├── scripts/
│   └── verify_nonsurjectivity.py  # Reproducible verification of all key computations
└── research_log/
    ├── phase10c_red_team.md       # Adversarial audit of early attempts
    ├── phase10d–10m_*.md          # Exploration phases (10 documents)
    ├── phase11a_obstruction_algebrique.md   # Newton polygon analysis
    ├── phase11b_verification_computationnelle.md  # Computational verification
    ├── phase11c_reduction_lll.md   # LLL lattice reduction
    ├── phase12_junction_theorem.md # Junction Theorem formulation
    └── phase13_audit_kolmogorov_baker.md  # Self-audit of rejected approach
```

## Quick Start

### Reproduce the computations

```bash
python3 scripts/verify_nonsurjectivity.py
```

This script independently verifies:
- $\gamma = 0.0500444728\ldots$
- $C(S-1,k-1) < d$ for all $k \in [18, 500]$ with $d > 0$
- Only 3 exceptions: $k \in \{3, 5, 17\}$ (all $< 68$, covered by Simons-de Weger)
- The threshold $K_0 = 18$

### Read the paper

The full manuscript is available in two formats:
- **PDF:** [`paper/Merle_2026_Barrieres_Entropiques_Collatz.pdf`](paper/Merle_2026_Barrieres_Entropiques_Collatz.pdf)
- **Markdown:** [`paper/preprint.md`](paper/preprint.md)

### Lean 4 formalization

The `lean/` directory contains Lean 4 skeletons with:
- Full type signatures for all theorems
- `sorry` placeholders with difficulty ratings (★ to ★★★★★)
- Dependency chain for filling the proofs
- One `axiom` for Simons-de Weger (external published result)

## Mathematical Framework

### Steiner's Equation (1977)

Any positive Collatz cycle of length $k$ satisfies:

$$n_0 \cdot (2^S - 3^k) = \sum_{i=0}^{k-1} 3^{k-1-i} \cdot 2^{A_i}$$

where $(A_0, \ldots, A_{k-1})$ is a composition of $S - k$ with $A_0 = 0$.

### The Entropic Deficit

The number of admissible compositions satisfies:

$$\log_2 \binom{S-1}{k-1} \approx S \cdot h\!\left(\frac{1}{\log_2 3}\right) = S \cdot (1 - \gamma)$$

while the crystal module has size $\log_2 d \approx S$. The gap $\gamma S$ grows linearly, making $C/d \to 0$ exponentially.

### The Junction

$$[1, 67] \cup [18, +\infty) = [1, +\infty)$$

The overlap $[18, 67]$ ensures complete coverage of all cycle lengths $k \geq 1$.

## Honest Assessment

This work establishes an **unconditional** structural obstruction (nonsurjectivity) but does **not** prove the full nonexistence of cycles. The gap between "the evaluation map misses residues" and "the evaluation map misses $0$ specifically" requires Hypothesis (H), which remains open.

We believe in transparent science: see [`research_log/phase13_audit_kolmogorov_baker.md`](research_log/phase13_audit_kolmogorov_baker.md) for a detailed self-audit of a rejected proof attempt.

## References

1. R. E. Crandall, "On the 3x + 1 problem", *Math. Comp.* **32** (1978), 1281-1292.
2. S. Eliahou, "The 3x + 1 problem: new lower bounds on nontrivial cycle lengths", *Discrete Math.* **118** (1993), 45-56.
3. J. C. Lagarias, "The 3x + 1 problem and its generalizations", *Amer. Math. Monthly* **92** (1985), 3-23.
4. M. Laurent, M. Mignotte, Y. Nesterenko, "Formes lineaires en deux logarithmes et determinants d'interpolation", *J. Number Theory* **55** (1995), 285-321.
5. D. Simons, B. de Weger, "Theoretical and computational bounds for m-cycles of the 3n + 1 problem", *Acta Arith.* **117** (2005), 51-70.
6. R. P. Steiner, "A theorem on the Syracuse problem", *Proc. 7th Manitoba Conf. Numer. Math.* (1977), 553-559.
7. T. Tao, "Almost all orbits of the Collatz map attain almost bounded values", *Forum Math. Pi* **10** (2022), e12.
8. T. Barina, "Convergence verification of the Collatz problem", *J. Supercomput.* **77** (2021), 2681-2688.

## License

This work is released under the MIT License. See [LICENSE](LICENSE) for details.
