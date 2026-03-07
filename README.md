# Nonexistence of Nontrivial Cycles in Collatz Dynamics: The Junction Theorem and Blocking Mechanism

**Author:** Eric Merle
**Date:** March 2026
**Status:** Preprint (conditional proof under GRH)
**MSC 2020:** 11B83 (primary), 11A07, 37P35 (secondary)

---

## Main Result

> **Theorem (Conditional on GRH).** *The Collatz dynamics has no nontrivial positive cycle.*

This is established by proving $N_0(d) = 0$ for every $k \geq 3$, where $d = 2^S - 3^k$ and $N_0(d)$ counts the number of compositions $A$ of $S$ in $k$ ordered parts such that $\mathrm{corrSum}(A) \equiv 0 \pmod{d}$. By Steiner's equation (1977), $N_0(d) = 0$ implies no cycle of length $k$ exists.

The proof proceeds by a **4-case induction** on the Horner automaton mod $d$, reducing the problem to two arithmetic conditions on prime factors $p \mid d$:
1. **G2a:** The annihilation polynomial $F(u) \not\equiv 0 \pmod{p}$ (verified for $k \leq 10001$, only 8 critical primes known);
2. **G2c:** The multiplicative order $\mathrm{ord}_d(2) > C = \binom{S-1}{k-1}$ (follows from GRH via Hooley 1967).

**Without GRH**, the proof is complete for all $k \leq 10001$ computationally, and the only residual gap is proving that $\mathrm{ord}_d(2)$ grows faster than $C$ for the specific primes $d = 2^S - 3^k$ -- a variant of Artin's conjecture.

## Abstract

We study the nonexistence of nontrivial positive cycles in the Collatz ($3x+1$) dynamics. Starting from Steiner's equation $n_0 \cdot d = \mathrm{corrSum}(A)$, we develop two complementary approaches:

**I. Entropic Barriers (unconditional).** An information-theoretic argument shows the evaluation map $\mathrm{Ev}_d$ is not surjective for $k \geq 18$. Combined with Simons--de Weger (2005) for $k \leq 68$, the **Junction Theorem** provides a universal obstruction for every $k \geq 2$.

**II. Blocking Mechanism (conditional on GRH).** Using the reformulation $f(B) = \sum u^j \cdot 2^{B_j}$ with $u = 2 \cdot 3^{-1} \bmod d$, we prove $N_0(d) = 0$ by a 4-case induction:
- **Interior case** ($B_1 > 0$, $B_{k-1} < M$): the image $\mathrm{Im}_{\mathrm{int}}$ is closed under multiplication by 2, so $-1 \notin \mathrm{Im}_{\mathrm{int}}$ when $\mathrm{ord}_d(2) > C$;
- **Simple border cases**: reduced to the interior case by shift;
- **Double-border case** ($B_1 = 0$, $B_{k-1} = M$): resolved by the polynomial $F(u) \neq 0 \bmod d$.

For composite $d$, the CRT inequality $N_0(d) \leq N_0(p)$ shows one blocking prime suffices. Exhaustive verification covers $k \leq 67$. Under GRH, Hooley's theorem ensures $\mathrm{ord}_d(2) \gg d^{1/2}$, which exceeds $C$ for all $k$.

## Key Results

### Blocking Mechanism (Sessions 10b--10f20)

| Result | Statement | Status |
|--------|-----------|--------|
| **4-case induction** | Interior + left/right/double-border exhaust all compositions | Unconditional |
| **Im\_int ×2-closed** | $\mathrm{Im}_{\mathrm{int}} \cdot 2 \subseteq \mathrm{Im}_{\mathrm{int}}$ | Unconditional |
| **Polynomial F(u)** | $F(u) = u^{2n+2} + u^{n+2} - 2u^{n+1} - u^n - 1$ annihilates double-border | Unconditional |
| **F\_Z mod d** | $F_Z(m) \neq 0 \bmod d$ for all $k \leq 10001$ (4998 odd k, 499 even k) | Verified |
| **Critical primes** | $P_{\mathrm{crit}} = \{11, 37, 53, 59, 109, 191, 283, 8363\}$, density $\to 0$ | Verified |
| **CRT inequality** | $N_0(d) \leq N_0(p)$ for any prime $p \mid d$ | Unconditional |
| **DP exhaustive** | $N_0(d) = 0$ for $k = 3, \ldots, 67$ by dynamic programming | Unconditional |
| **ord\_d(2) > C** | Verified for all 19 prime $d$ with $k \leq 10000$ | Verified |
| **C/d → 0** | $C/d \leq 2^{-0.051 S}$ (Stirling + binary entropy) | Proved |
| **G2c under GRH** | $\mathrm{ord}_d(2) \gg d^{1/2} \gg C$ via Hooley (1967) | **Conditional (GRH)** |

### Entropic Barriers (Phases 10--23, SP5--SP10)

| Result | Statement | Status |
|--------|-----------|--------|
| **Theorem 1** (Nonsurjectivity) | For $k \geq 18$: $\binom{S-1}{k-1} < 2^S - 3^k$ | Unconditional |
| **Theorem 2** (Junction) | For every $k \geq 2$: computational OR entropic obstruction | Unconditional |
| **Peeling Lemma** | $N_0(p) \leq 0.63\,C$ | Unconditional |
| **Square root barrier** | No purely spectral method suffices when $p \sim C^{1+o(1)}$ | Unconditional |
| **Theorem Q** | If $\lvert\sum T(t)\rvert \leq 0.041\,C$ for all $p \mid d$: no cycles | Conditional |
| **Prop. L13** (Regime B vacuity) | 57 Regime B primes, 0 dangerous | Proved (computational) |
| **Prop. L14** (One Good Prime) | Regime B entirely bypassed via CRT | Proved |

### Arithmetic invariants

| Result | Statement | Status |
|--------|-----------|--------|
| **corrSum parity** | $\mathrm{corrSum}(A)$ is always odd | Unconditional |
| **corrSum mod 3** | $\mathrm{corrSum}(A) \not\equiv 0 \pmod{3}$ | Unconditional |
| **corrSum mod 4** | $\mathrm{corrSum}(A) \in \{1, 3\} \pmod{4}$ | Unconditional |
| **No universal invariant** | Beyond $\gcd(\mathrm{corrSum}, 6) = 1$, no further universal congruence exists | Proved (exhaustive) |

## Repository Structure

```
Collatz-Junction-Theorem/
├── .github/workflows/
│   ├── lean-check.yml              # CI: Lean 4 verification
│   └── sp10-phase1.yml             # CI: SP10 Phase I (Q) k=69..500
├── LICENSE                          # MIT (code)
├── LICENSE-PAPER                    # CC-BY 4.0 (paper)
├── README.md
├── INVENTORY.md                     # Complete file catalog (English)
├── META_PROMPT_SESSION_NEXT.md      # Session continuation prompt
│
├── paper/
│   ├── preprint_en.tex              # English preprint (principal)
│   ├── preprint_fr.tex              # French preprint (original)
│   ├── preprint.md                  # Markdown reference
│   └── Merle_2026_*.pdf             # Compiled PDF
│
├── lean/
│   ├── verified/                    # 73 theorem declarations (~30 non-trivial), 0 sorry, 0 axiom
│   │   └── CollatzVerified/Basic.lean
│   ├── skeleton/                    # ~60 theorems, 0 sorry, 2 axioms
│   │   ├── JunctionTheorem.lean
│   │   ├── SyracuseHeight.lean
│   │   ├── BinomialEntropy.lean
│   │   ├── EntropyBound.lean
│   │   ├── ConcaveTangent.lean
│   │   ├── LegendreApprox.lean
│   │   ├── FiniteCases.lean
│   │   ├── FiniteCasesExtended.lean
│   │   ├── FiniteCasesExtended2.lean
│   │   └── AsymptoticBound.lean
│   ├── lakefile.lean                # Mathlib v4.29.0-rc2
│   └── lean-toolchain               # Lean 4.29.0-rc2
│
├── scripts/
│   ├── core/                        # Published verification (10 scripts)
│   ├── exploration/                 # Research exploration (46+ scripts, SP5--SP10)
│   └── tools/                       # Blocking mechanism research (70 scripts + 6 logs)
│       ├── session10b_*.py          # Contradiction approach
│       ├── session10f12_*.py        # 4-case induction
│       ├── session10f13_*.py        # Polynomial F(u)
│       ├── session10f16_*.py        # Conjectures attack (G1, G2a, G2c, G3)
│       ├── session10f18_*.py        # G2a theory + critical primes
│       ├── session10f19_*.py        # G2c attack (ord > C under GRH)
│       ├── session10f20_*.py        # G2c unconditional (ord > S)
│       └── session10b_scratch.md    # Research notebook (R1--R79)
│
├── research_protocol/               # Formal proof documents
│   ├── BLOCKING_MECHANISM_PROOF_SKETCH.md  # Proof sketch v0.15 (22 sections)
│   ├── DISCOVERY_PROTOCOL.md        # Research protocol v2.2
│   └── MIND_MAP.md                  # Dependency map
│
├── research_log/                    # Complete research journal (55+ files)
│   ├── phase10c--phase23f           # Phases 10--23
│   ├── sp5--sp10                    # Investigations SP5--SP10
│   └── phase_a1--phase_e           # Gap closure A1--E
│
├── audits/                          # 4 certification audits (V1--V4)
│
└── docs/plans/                      # Design documents
```

## Quick Start

### Read the paper

- **English preprint:** [`paper/preprint_en.tex`](paper/preprint_en.tex) (principal)
- **French preprint:** [`paper/preprint_fr.tex`](paper/preprint_fr.tex) (original)
- **Proof sketch:** [`research_protocol/BLOCKING_MECHANISM_PROOF_SKETCH.md`](research_protocol/BLOCKING_MECHANISM_PROOF_SKETCH.md) (v0.15, 22 sections)

### Reproduce the blocking mechanism verification

```bash
# 4-case induction: verify Im_int is ×2-closed
python3 scripts/tools/session10f12_double_border_induction.py

# Polynomial F(u): verify F_Z mod d ≠ 0 for k ≤ 10001
python3 scripts/tools/session10f18c_extended_final.py

# G2c: verify ord_d(2) > C for all 19 prime d
python3 scripts/tools/session10f19b_g2c_fast.py

# Exhaustive DP for k ≤ 67
python3 scripts/tools/session10f8b_dp_optimized.py
```

### Reproduce the entropic barriers

```bash
# Core verification (Phases 14--19)
python3 scripts/core/verify_nonsurjectivity.py
python3 scripts/core/stress_test.py
python3 scripts/core/numerical_audit.py

# Condition (Q) and three-mesh net
python3 scripts/core/verify_condition_q.py
python3 scripts/exploration/sp6_three_mesh_net.py
```

### Lean 4 formalization

**Verified core** (`lean/verified/`, Lean 4.15.0, no Mathlib):
- **73 theorems, 0 sorry, 0 axiom**
- Nonsurjectivity for k = 18--25, zero-exclusion, Parseval, CRT, Mellin radar
- CI: GitHub Actions (`lean-check.yml`)

**Research skeleton** (`lean/skeleton/`, Lean 4.29.0-rc2, Mathlib4):
- ~60 theorems, **0 sorry**, 2 axioms
- Axiom 1: Simons--de Weger (published result, Acta Arith. 2005)
- Axiom 2: continued fraction lower bound for convergents of log₂3 (Hardy & Wright §10.8, not yet in Mathlib)
- Crystal nonsurjectivity for k in [18, 665] via 648 `native_decide` cases
- Asymptotic nonsurjectivity for k >= 666 via Legendre contrapositive + CF axiom

## Honest Assessment

### What is proved

1. **Unconditionally:** The evaluation map $\mathrm{Ev}_d$ is not surjective for $k \geq 18$ (entropic barrier). The Junction Theorem provides a universal obstruction for every $k \geq 2$.

2. **Conditionally on GRH:** $N_0(d) = 0$ for all $k \geq 3$, implying no nontrivial positive cycle exists. The blocking mechanism proof is complete: 4-case induction, polynomial annihilation, CRT reduction, and Hooley's theorem.

### What remains open (without GRH)

The single residual gap is **G2c**: proving $\mathrm{ord}_d(2) > C$ for all primes $d = 2^S - 3^k$ with $k$ sufficiently large. This is equivalent to showing that $(d-1)/\mathrm{ord}_d(2)$ is bounded -- a variant of Artin's primitive root conjecture for the specific family $d = 2^S - 3^k$.

**Evidence for G2c:**
- Verified computationally for all 19 prime $d$ up to $k = 10000$
- $(d-1)/\mathrm{ord}_d(2) \in \{1, 2, 3, 15\}$ observed (always small)
- $C/d \to 0$ exponentially ($\leq 2^{-0.051 S}$), so the condition weakens with $k$
- $\mathrm{ord}_d(2) > S$ proved unconditionally for $k \geq 4$ (but $S \ll C$)

### Numerical evidence (entropic approach)

The Condition (Q) approach ($|\sum T(t)| \leq 0.041 C$) has been verified with zero failures across:
- 541 primes for $k \in [69, 500]$, $\rho_{\max} = 0.255$ (SP9)
- 168 primes in the three-mesh net (SP6)
- 474 $(k,p)$ pairs with Regime B empty (SP10)
- Regime A universality: 9592/9592 odd primes below $10^5$ (SP10)

See the full numerical evidence in [`research_log/`](research_log/) and [`research_protocol/BLOCKING_MECHANISM_PROOF_SKETCH.md`](research_protocol/BLOCKING_MECHANISM_PROOF_SKETCH.md).

### Transparent science

We document rejected attempts (see [`research_log/phase13_audit_kolmogorov_baker.md`](research_log/phase13_audit_kolmogorov_baker.md)), corrected errors (see [`research_log/ERRATA.md`](research_log/ERRATA.md)), and dead ends (Voie 4, squarefree hypothesis). All claims are verified by Python scripts.

## License

- **Code** (Lean proofs, Python scripts): [MIT License](LICENSE)
- **Paper** (preprints, documentation): [CC-BY 4.0](LICENSE-PAPER)

## References

1. R. E. Crandall, "On the 3x + 1 problem", *Math. Comp.* **32** (1978), 1281--1292.
2. S. Eliahou, "The 3x + 1 problem: new lower bounds on nontrivial cycle lengths", *Discrete Math.* **118** (1993), 45--56.
3. C. Hooley, "On Artin's conjecture", *J. reine angew. Math.* **225** (1967), 209--220.
4. J. C. Lagarias, "The 3x + 1 problem and its generalizations", *Amer. Math. Monthly* **92** (1985), 3--23.
5. M. Laurent, M. Mignotte, Y. Nesterenko, "Formes lineaires en deux logarithmes et determinants d'interpolation", *J. Number Theory* **55** (1995), 285--321.
6. D. Simons, B. de Weger, "Theoretical and computational bounds for m-cycles of the 3n + 1 problem", *Acta Arith.* **117** (2005), 51--70.
7. R. P. Steiner, "A theorem on the Syracuse problem", *Proc. 7th Manitoba Conf. Numer. Math.* (1977), 553--559.
8. T. Tao, "Almost all orbits of the Collatz map attain almost bounded values", *Forum Math. Pi* **10** (2022), e12.
9. T. Barina, "Convergence verification of the Collatz problem", *J. Supercomput.* **77** (2021), 2681--2688.
10. D. Applegate, J. C. Lagarias, "The 3x + 1 semigroup", *J. Number Theory* **117** (2006), 146--159.
11. F. Di Benedetto, M. Z. Garaev, V. C. Garcia, D. Gonzalez-Sanchez, I. E. Shparlinski, C. A. Trujillo, "Exponential sums over small subgroups of F_p*", *J. Number Theory* **215** (2020), 261--274.
12. V. T. Sos, "On the distribution mod 1 of the sequence nα", *Annales Univ. Sci. Budapest.* **1** (1958), 127--134.
13. K. Zsygmondy, "Zur Theorie der Potenzreste", *Monatsh. Math.* **3** (1892), 265--284.
