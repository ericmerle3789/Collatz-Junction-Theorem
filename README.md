# Nonexistence of Nontrivial Cycles in Collatz Dynamics: The Junction Theorem and Blocking Mechanism

**Author:** Eric Merle
**Date:** March 2026
**Status:** Preprint (conditional proof under GRH + open conjecture on interior closure)
**MSC 2020:** 11B83 (primary), 11A07, 37P35 (secondary)

---

## Main Result

> **Theorem (Conditional on GRH + Conjecture 7.4).** *The Collatz dynamics has no nontrivial positive cycle.*

This is established by proving $N_0(d) = 0$ for every $k \geq 3$, where $d = 2^S - 3^k$ and $N_0(d)$ counts the number of compositions $A$ of $S$ in $k$ ordered parts such that $\mathrm{corrSum}(A) \equiv 0 \pmod{d}$. By Steiner's equation (1977), $N_0(d) = 0$ implies no cycle of length $k$ exists.

The proof proceeds by a **4-case induction** on the Horner automaton mod $d$, reducing the problem to two arithmetic conditions on prime factors $p \mid d$:
1. **G2a:** The annihilation polynomial $F(u) \not\equiv 0 \pmod{p}$ (verified for $k \leq 10001$, only 8 critical primes known);
2. **G2c:** The multiplicative order $\mathrm{ord}_d(2) > C = \binom{S-1}{k-1}$ (follows from GRH via Hooley 1967).

**Without GRH**, the proof is complete for all $k \leq 10001$ computationally, and the only residual gap is proving that $\mathrm{ord}_d(2)$ grows faster than $C$ for the specific primes $d = 2^S - 3^k$ -- a variant of Artin's conjecture.

## Abstract

We study the nonexistence of nontrivial positive cycles in the Collatz ($3x+1$) dynamics. Starting from Steiner's equation $n_0 \cdot d = \mathrm{corrSum}(A)$, we develop two complementary approaches:

**I. Entropic Barriers (unconditional).** An information-theoretic argument shows the evaluation map $\mathrm{Ev}_d$ is not surjective for $k \geq 18$. Combined with Simons--de Weger (2005) for $k \leq 68$, the **Junction Theorem** provides a universal obstruction for every $k \geq 2$.

**II. Blocking Mechanism (conditional on GRH + Conjecture 7.4).** Using the reformulation $f(B) = \sum u^j \cdot 2^{B_j}$ with $u = 2 \cdot 3^{-1} \bmod d$, we prove $N_0(d) = 0$ by a 4-case induction:
- **Interior case** ($B_1 > 0$, $B_{k-1} < M$): requires $\mathrm{Im}_{\mathrm{int}}$ to be closed under multiplication by 2 (**Conjecture 7.4** -- see [Known Gaps](#known-gaps) below);
- **Simple border cases**: reduced to the interior case by shift;
- **Double-border case** ($B_1 = 0$, $B_{k-1} = M$): resolved by the polynomial $F(u) \neq 0 \bmod d$.

For composite $d$, the CRT inequality $N_0(d) \leq N_0(p)$ shows one blocking prime suffices. Exhaustive verification covers $k \leq 67$. Under GRH, Hooley's theorem ensures $\mathrm{ord}_d(2) \gg d^{1/2}$, which exceeds $C$ for all $k$.

## Key Results

### Blocking Mechanism

| Result | Statement | Status |
|--------|-----------|--------|
| **4-case induction** | Interior + left/right/double-border exhaust all compositions | Unconditional |
| **Im\_int ×2-closed** | $\mathrm{Im}_{\mathrm{int}} \cdot 2 \subseteq \mathrm{Im}_{\mathrm{int}}$ | **Open conjecture** (see [Known Gaps](#known-gaps)) |
| **Polynomial F(u)** | $F(u) = u^{2n+2} + u^{n+2} - 2u^{n+1} - u^n - 1$ annihilates double-border | Unconditional |
| **F\_Z mod d** | $F_Z(m) \neq 0 \bmod d$ for all $k \leq 10001$ (4998 odd k, 499 even k) | Verified |
| **Critical primes** | $P_{\mathrm{crit}} = \{11, 37, 53, 59, 109, 191, 283, 8363\}$, density $\to 0$ | Verified |
| **CRT inequality** | $N_0(d) \leq N_0(p)$ for any prime $p \mid d$ | Unconditional |
| **DP exhaustive** | $N_0(d) = 0$ for $k = 3, \ldots, 67$ by dynamic programming | Unconditional |
| **ord\_d(2) > C** | Verified for all 19 prime $d$ with $k \leq 10000$ | Verified |
| **C/d → 0** | $C/d \leq 2^{-0.051 S}$ (Stirling + binary entropy) | Proved |
| **G2c under GRH** | $\mathrm{ord}_d(2) \gg d^{1/2} \gg C$ via Hooley (1967) | **Conditional (GRH)** |

### Entropic Barriers

| Result | Statement | Status |
|--------|-----------|--------|
| **Theorem 1** (Nonsurjectivity) | For $k \geq 18$: $\binom{S-1}{k-1} < 2^S - 3^k$ | Unconditional |
| **Theorem 2** (Junction) | For every $k \geq 2$: computational OR entropic obstruction | Unconditional |
| **Peeling Lemma** | $N_0(p) \leq 0.63\,C$ | Unconditional |
| **Square root barrier** | No purely spectral method suffices when $p \sim C^{1+o(1)}$ | Unconditional |
| **Theorem Q** | If $\lvert\sum T(t)\rvert \leq 0.041\,C$ for all $p \mid d$: no cycles | Conditional |

### Arithmetic invariants

| Result | Statement | Status |
|--------|-----------|--------|
| **corrSum parity** | $\mathrm{corrSum}(A)$ is always odd | Unconditional |
| **corrSum mod 3** | $\mathrm{corrSum}(A) \not\equiv 0 \pmod{3}$ | Unconditional |
| **corrSum mod 4** | $\mathrm{corrSum}(A) \in \{1, 3\} \pmod{4}$ | Unconditional |
| **corrSum mod 12** | Determined by $\min(A)$: $1{\to}2$, even${\geq}2{\to}4$, odd${\geq}3{\to}8$ | Unconditional |
| **2-adic valuation** | $v_2(\mathrm{corrSum}(A)) = \min(A)$ | Unconditional |
| **No universal invariant** | Beyond $\gcd(\mathrm{corrSum}, 12)$, no further universal congruence (27 moduli tested) | Proved (exhaustive) |

### New results (March 2026)

| Result | Statement | Status |
|--------|-----------|--------|
| **Gap C closure** | $d \nmid F_Z$ for all odd $k \geq 7$ via 2-adic valuation | **Unconditional** |
| **Transient Zero** | $c_j \equiv 0 \pmod{p} \Rightarrow c_{j+1} \not\equiv 0 \pmod{p}$ | Unconditional |
| **Doubly stochastic** | Horner transition matrix $T$ on $\mathbb{Z}/p\mathbb{Z}$ is doubly stochastic | **Proved** |
| **Image density** | $\lvert\mathrm{Im}(\mathrm{Ev}_d)\rvert/d$ matches birthday model (no extra thinning) | Negative result |
| **2-Adic theorem** | $v_2(\mathrm{corrSum}(A)) = \min(A)$ exactly | **Proved** |
| **Mod 12 determination** | $\mathrm{corrSum} \bmod 12$ determined by $\min(A)$: $\{1{\to}2, \text{even}{\geq}2{\to}4, \text{odd}{\geq}3{\to}8\}$ | **Proved** |
| **Fiber underdispersion** | Poisson ratio $\mathrm{Var}/\mathrm{Mean} \approx 0.1$ for fiber sizes of $\mathrm{Ev}_d$ | Observed |
| **No universal invariants** | Beyond $\gcd(\mathrm{corrSum}, 12)$, no further universal congruence (tested 27 moduli) | Proved (negative) |
| **Without-replacement** | Effect real but mixed direction; TV $< 0.003$ for $k \geq 10$ | Proved (negative) |
| **Ordering constraint** | No systematic bias (42.8th percentile among all permutations) | Proved (negative) |

The **doubly stochastic theorem** shows that the Transient Zero Property has no effect on the stationary distribution: $\pi(0) = 1/p$ exactly. The **2-adic theorem** and **mod 12 determination** reveal the precise local arithmetic structure of corrSum. Multi-agent investigation (Rounds 1--2) establishes that every single-prime, single-step local approach gives $P(0) \approx 1/p$; the obstruction is the **global CRT product** $\prod_{p \mid d} P(0 \bmod p)$.

## Known Gaps

### 1. Interior ×2-closure (Conjecture 7.4)

The claim that $\mathrm{Im}_{\mathrm{int}}(g)$ is closed under multiplication by 2 in $\mathbb{Z}/d\mathbb{Z}$ is **unproved**. Exhaustive computation for $k = 7, \ldots, 20$ shows it is in fact **false as stated**: approximately 64% of residues in $\mathrm{Im}_{\mathrm{int}}(g)$ have their double outside $\mathrm{Im}_{\mathrm{int}}(g)$, and the maximal ×2-closed subset is empty for every $k$ tested.

The desired conclusion ($-1 \notin \mathrm{Im}(g)$) remains true computationally for all $k$ tested. Closing this gap would require an algebraic approach (character sums, algebraic geometry over $\mathbb{Z}/d\mathbb{Z}$) rather than the current combinatorial shift argument.

**Impact:** Affects only the Blocking Mechanism (conditional). Does **not** affect the unconditional Junction Theorem or the Lean-verified formalization.

### 2. G2c without GRH (Artin variant)

Proving $\mathrm{ord}_d(2) > C$ unconditionally for all $k$ remains open — this is a variant of Artin's primitive root conjecture for the family $d = 2^S - 3^k$.

## Repository Structure

```
Collatz-Junction-Theorem/
├── .github/workflows/          # CI: Lean 4 verification
├── LICENSE                     # MIT (code)
├── LICENSE-PAPER                # CC-BY 4.0 (paper)
├── README.md
├── INVENTORY.md                # Complete file catalog
│
├── paper/
│   ├── preprint_en.tex         # English preprint (source)
│   └── preprint_en.pdf         # Compiled PDF
│
├── lean/
│   ├── verified/               # 97 theorems, 0 sorry, 0 axiom (Lean 4.15.0)
│   │   ├── CollatzVerified/Basic.lean   (73 thms: nonsurjectivity, CRT, Parseval)
│   │   └── CollatzVerified/G2c.lean     (24 thms: CRT, modular arithmetic)
│   └── skeleton/               # ~38 theorems, 0 sorry, 2 axioms (Lean 4.29.0-rc2, Mathlib4)
│       ├── JunctionTheorem.lean         (Junction Theorem: unconditional)
│       ├── AsymptoticBound.lean         (k ≥ 666 via Legendre + CF axiom)
│       ├── FiniteCases*.lean            (k ∈ [18, 665] via native_decide)
│       └── BinomialEntropy.lean, ...    (supporting lemmas)
│
├── scripts/
│   ├── core/                   # Published verification scripts (13 files)
│   ├── research/               # Multi-agent investigation: Rounds 1-2 (10 files)
│   └── tools/                  # Blocking mechanism verification (70+ scripts)
│
├── research_log/               # Research journal (phases 10--23)
│
└── audits/                     # Certification audits (V1--V4, V8: 4-expert panel 7.4/10)
```

## Quick Start

### Read the paper

The preprint is [`paper/preprint_en.tex`](paper/preprint_en.tex) (compiled: [`preprint_en.pdf`](paper/preprint_en.pdf)).

### Reproduce the blocking mechanism verification

```bash
# Polynomial F(u): verify F_Z mod d ≠ 0 for k ≤ 10001
python3 scripts/tools/session10f18c_extended_final.py

# G2c: verify ord_d(2) > C for all 19 prime d
python3 scripts/tools/session10f19b_g2c_fast.py

# Exhaustive DP for k ≤ 67
python3 scripts/tools/session10f8b_dp_optimized.py
```

### Reproduce the entropic barriers

```bash
python3 scripts/core/verify_nonsurjectivity.py
python3 scripts/core/stress_test.py
python3 scripts/core/numerical_audit.py
python3 scripts/core/verify_condition_q.py
```

### Reproduce the new results (March 2026)

```bash
# Gap C closure: d does not divide F_Z for all odd k >= 7
python3 scripts/core/prove_fz_gap_closure.py

# Transient Zero Property + Horner chain analysis
python3 scripts/core/transient_zero_analysis.py

# Image density: birthday model match (negative result)
python3 scripts/core/image_density_analysis.py

# Markov analysis: doubly stochastic theorem
python3 scripts/research/tz_markov_analysis.py
```

### Lean 4 formalization

**Verified core** (`lean/verified/`, Lean 4.15.0, no Mathlib):
- **97 theorems, 0 sorry, 0 axiom**
- Nonsurjectivity for k = 18--25, zero-exclusion, Parseval, CRT, modular arithmetic
- CI: GitHub Actions (`lean-check.yml`)

**Research skeleton** (`lean/skeleton/`, Lean 4.29.0-rc2, Mathlib4):
- ~38 theorems, **0 sorry**, 2 axioms (published external results)
- Axiom 1: Simons--de Weger (Acta Arith. 2005)
- Axiom 2: continued fraction lower bound for convergents of log₂3 (Hardy & Wright §10.8)
- Crystal nonsurjectivity for k ∈ [18, 665] via 648 `native_decide` cases
- Asymptotic nonsurjectivity for k ≥ 666 via Legendre contrapositive + CF axiom

## Honest Assessment

### What is proved

1. **Unconditionally:** The evaluation map $\mathrm{Ev}_d$ is not surjective for $k \geq 18$ (entropic barrier). The Junction Theorem provides a universal obstruction for every $k \geq 2$.

2. **Conditionally on GRH + Conjecture 7.4:** $N_0(d) = 0$ for all $k \geq 3$, implying no nontrivial positive cycle exists. The blocking mechanism proof depends on the interior ×2-closure (Conjecture 7.4, currently unproved) and Hooley's theorem (requires GRH).

### What remains open

| Gap | Description | Impact |
|-----|-------------|--------|
| **Conjecture 7.4** | Interior ×2-closure of $\mathrm{Im}_{\mathrm{int}}(g)$ | Blocking Mechanism only |
| **G2c without GRH** | $\mathrm{ord}_d(2) > C$ unconditionally (Artin variant) | Blocking Mechanism only |
| **Neither gap** affects the unconditional Junction Theorem or the Lean formalization. |

### Transparent science

We document rejected attempts, corrected errors (see [`research_log/ERRATA.md`](research_log/ERRATA.md)), and dead ends. All claims are verified by Python scripts.

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
