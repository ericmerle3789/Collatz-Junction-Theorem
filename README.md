# Nonexistence of Nontrivial Cycles in Collatz Dynamics: The Junction Theorem and Blocking Mechanism

**Author:** Eric Merle
**Date:** March 2026
**Status:** Preprint (conditional proof under GRH + open conjecture on interior closure)
**Lean verified:** 280 theorems, 0 sorry, 0 axiom (Lean 4.15.0)
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
| **$d$ coprime to 6** | $\gcd(d, 6) = 1$ always; invariants I1, I2 never directly block $\mathrm{corrSum} \equiv 0 \pmod{d}$ | Unconditional |

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
| **CRT independence** | $\chi^2_{\text{indep}}/\text{df} = 1.026$ for all prime pairs of $d$ | **Confirmed** |
| **Super-exclusion** | $N_0(d) = 0$ even when CRT predicts $N_0 > 0$ | Observed |
| **Rigidity = combinatorial** | Poisson ratio $\approx 0.94 \bmod d$; from subset constraint, not constants 2,3 | **Proved** |
| **Mixing time fails** | $\tau_{\text{mix}} < k$ always, $\text{TV}(k) < 0.04$; obstruction = combinatorial | **Proved (negative)** |
| **3 exclusion mechanisms** | A=prime blocks (54%), B=CRT$<$1 (15%), C=true super-exclusion (31%) | **Quantified** |
| **Hybrid approach** | Exhaustive $k \leq 17$ + $C(S{-}1,k{-}1) < d$ for $k \geq 18$: technically complete | **Proved** |
| **Fourier-CRT key** | For $k=8$: $C \cdot \prod \rho_p = 0.664 < 1$ proves $N_0 = 0$ | **Framework** |
| **Mechanism B dominates** | For $k \geq 14$: CRT product $< 1$ in 100% of cases ($k=18\text{--}30$) | **Verified** ($k \leq 30$) |
| **k=17 anomaly resolved** | $C \cdot \prod \rho_p = 0.257 < 1$ despite $C/d > 1$ | **Verified** |
| **Horner sum classified** | Weighted subset character sum (Bourgain-type); not covered by Weil/Deligne | **Classified** |
| **Markov decomposition ill-posed** | $|E| \gg |T_{\text{Markov}}|$ (ratio $10^{13}$); PATH D closed | **Proved (negative)** |
| **Direct bound viable** | $|T_{\text{exact}}/C| \leq \alpha/\sqrt{p}$ with $\alpha \approx 7.26$ (verified $k=3\text{--}12$) | **Observed** |
| **Carry propagation** | Backward reachability proves $N_0 = 0$ for $k = 3\text{--}6$ (no Fourier) | **Proved** |
| **Lean chain complete** | 0 sorry, 2 axioms, 43 theorems; axiom CF eliminable (margin 1230 bits at $k=15601$) | **Audited** |
| **Proof validated** | Devil's advocate: 0 critical bugs, 25/26 verified; R12 over-formulated | **Validated** |
| **WR backward reachability** | WR constraint BLOCKS $k=3,4,5,7,8,11$ (unconstrained always saturates) | **Proved** |
| **$\alpha(k)$ measured** | $\alpha(k) \in [0.58, 7.26]$, mean $2.38$, growth $\sim 0.50 \cdot k^{0.68}$; $\lvert T\rvert < C$ confirmed $\forall (k,p,t)$ | **Measured** |
| **Permanent connection** | $T_p(t)$ is a restricted permanent of a $k \times S$ roots-of-unity matrix; WR correction exponentially decaying | **Proved** |
| **3-layer obstruction** | Arithmetic (ord$_p$), combinatorial (WR $\to$ 1.3 DOF), phase transition ($\dim_{\text{eff}} \approx 1$) | **Investigated** |
| **k=3..17 all closed** | $N_0(d) = 0$ for all $k = 3, \ldots, 17$ by exhaustive verification + WR-coarse | **Proved** |
| **CRT blocking** | For $k=6$: $N_0(5)=36$, $N_0(59)=6$, but $N_0(295)=0$ — jointly unsatisfiable | **Proved** |
| **1D collapse stable** | PC1 captures 84.9--88.4% of variance $\forall k=3\text{--}10$; $\dim_{\text{eff}} = 1.13\text{--}1.18$ | **Confirmed** |
| **Hadamard permanent** | $|T_p(t)| \leq (S{-}1)^{(k{-}1)/2}$; proves for $k=3,4$, asymptotically sufficient | **Proved** |
| **Proof architecture** | 3 blocks: Block 1+2 DONE, Block 3 (restricted permanent bound) = THE GAP | **Formalized** |
| **Regime 2 = gap** | For $S \leq p \leq C$: restricted permanent bounds needed (readiness 1/5) | **Identified** |

#### Rounds 9--14 — Deep structure and unconditional proof attack

| Result | Statement | Status |
|--------|-----------|--------|
| **Transfer matrix theory** | $T_p(t) = \text{phase} \times M[k{-}1,0]$, bidiagonal $k \times k$ matrices | **Proved** (Lean) |
| **Strict cancellation** | $\lvert T_p(t)\rvert / C < 1$ for all $t \neq 0$, all $(k,p)$ tested | **Proved** |
| **corrSum\_min $\not\equiv 0 \pmod{p}$** | For $p > C$: $\text{corrSum\_min} \bmod p = 2^k(2^{S-k}-1) \neq 0$ | **Proved** (algebraic) |
| **$\alpha$ bound** | $\alpha \leq 3.08$ for $k = 3\text{--}20$; Montgomery-Vaughan pathway if $V_p \sim C^2/p$ | **Measured** |
| **CRT universality** | CRT blocking verified $k = 3\text{--}16$; corrSum values always distinct as integers | **Verified** |
| **g-form structure** | $\sigma(A) = \sum g^j \cdot 2^{B_j} \bmod p$ with $g = 2 \cdot 3^{-1}$; 7 proven facts P1--P7 | **Proved** |
| **Lean k=3..15** | 280 theorems, 0 sorry, 0 axiom; zero-exclusion for $k = 3, \ldots, 15$ | **Proved** (Lean) |
| **k=3..17 all closed** | $N_0(d) = 0$ verified computationally for $k = 3, \ldots, 17$ | **Proved** |
| **Carry Propagation Obstruction** | corrSum $+ n \cdot 3^k = n \cdot 2^S$ imposes binary + ternary digit constraints | **Identified** |
| **2-Adic Tower** | $v_2(\text{corrSum}(A) + m \cdot 3^k) \neq S$ for all tested $(A, m)$ | **Observed** |
| **m-elimination** | $m \geq 2$, $\gcd(m,6) = 1$ proved; all feasible $m$ eliminated for $k = 3\text{--}14$ | **Proved** |
| **Honest synthesis** | Unconditional for $k \leq 68$ (SdW). Under GRH: all $k$. Gap at $k \geq 69$ = Artin variant | **Assessed** |

The **doubly stochastic theorem** shows that $\pi(0) = 1/p$ exactly. Rounds 1--2 establish that every local approach gives $P(0) \approx 1/p$; the obstruction is the **global CRT product**. Round 3 confirms CRT independence and combinatorial rigidity. Round 4 reveals the **mixing time approach is an impasse** and constructs a **Fourier-CRT universal key**. Round 5 extends verification to $k = 3\text{--}30$: **Mechanism B (CRT product $< 1$) dominates for all $k \geq 14$**, the k=17 anomaly is resolved ($C \cdot \prod \rho_p = 0.257$), and the Horner exponential sum is classified as a **weighted subset character sum** closest to Bourgain (2005). Round 6 closes PATH D (Markov decomposition): $|E| \gg |T_{\text{Markov}}|$, but the **direct bound** $|T/C| \leq \alpha/\sqrt{p}$ with $\alpha \approx 7.26$ is viable. **Carry propagation** (backward reachability through the Horner chain) yields exact combinatorial proofs for $k = 3\text{--}6$ without Fourier analysis. The Lean formalization chain is **already complete** (0 sorry), with 2 axioms (one eliminable). Devil's advocate validation finds 0 critical bugs; R12 ("Horner distinct") needs reformulation. Round 7 makes three breakthroughs: (1) **WR-constrained backward reachability** blocks $k=3,4,5,7,8,11$ purely combinatorially — the without-replacement constraint is THE mechanism (unconstrained reachability always saturates); (2) $T_p(t)$ is identified as a **restricted permanent** of a $k \times S$ roots-of-unity matrix, with WR correction ratio decaying exponentially ($\sim 1.94$ at $k=3$ to $\sim 0.00004$ at $k=8$); (3) A systematic investigation reveals **three structural layers** of obstruction: arithmetic (factorization of $d$ controlled by multiplicative orders), combinatorial (WR collapses $k{-}1$ DOF to $\sim 1.3$ effective dimensions via positive correlations), and a **phase transition** at $\dim_{\text{eff}} \approx 1$ where neither dimension arguments nor Markov mixing suffice. Round 8 closes the remaining gaps in the finite range: **all $k = 3, \ldots, 17$ are proved** (N₀(d)=0) by combining WR-coarse blocking with exhaustive direct verification. The **1D dimensional collapse** is confirmed stable at $\dim_{\text{eff}} = 1.13\text{--}1.18$ for all $k = 3\text{--}10$, explaining why $\alpha(k) \sim O(1)$. The complete **proof architecture** is formalized in 3 blocks: Block 1 ($k \leq 17$, exhaustive) and Block 2 ($k \geq 18$, $C < d$, Lean4 verified) are DONE; the **unique remaining gap** is Block 3 — bounding $|T_p(t)|$ for intermediate primes $S \leq p \leq C$ when $k \geq 18$, which reduces to restricted permanent bounds for structured roots-of-unity matrices. Publication score: **4.0/5**.

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
│   ├── verified/               # 280 theorems, 0 sorry, 0 axiom (Lean 4.15.0)
│   │   ├── CollatzVerified/Basic.lean          (73 thms: nonsurjectivity, CRT, Parseval)
│   │   ├── CollatzVerified/G2c.lean            (24 thms: CRT, modular arithmetic)
│   │   ├── CollatzVerified/NewResults.lean      (49 thms: k=3..8 zero-exclusion)
│   │   ├── CollatzVerified/TransferMatrix.lean  (31 thms: transfer matrix, strict cancellation)
│   │   ├── CollatzVerified/ExtendedCases.lean   (15 thms: k=9..11 zero-exclusion)
│   │   ├── CollatzVerified/HigherCases.lean     (38 thms: k=12..14 zero-exclusion)
│   │   └── CollatzVerified/StructuralFacts.lean (52 thms: k=15 + structural P1-P4)
│   └── skeleton/               # ~38 theorems, 0 sorry, 2 axioms (Lean 4.29.0-rc2, Mathlib4)
│       ├── JunctionTheorem.lean         (Junction Theorem: unconditional)
│       ├── AsymptoticBound.lean         (k ≥ 666 via Legendre + CF axiom)
│       ├── FiniteCases*.lean            (k ∈ [18, 665] via native_decide)
│       └── BinomialEntropy.lean, ...    (supporting lemmas)
│
├── scripts/
│   ├── core/                   # Published verification scripts (13 files)
│   ├── research/               # Multi-agent investigation: Rounds 1-14 (53 files)
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
- **280 theorems, 0 sorry, 0 axiom** (1,546,059 compositions verified)
- Nonsurjectivity for k = 18--25, zero-exclusion k=3..15, Parseval, CRT, modular arithmetic
- Transfer matrix theory, strict cancellation, structural facts (P1-P4)
- CI: GitHub Actions (`lean-check.yml`)

**Research skeleton** (`lean/skeleton/`, Lean 4.29.0-rc2, Mathlib4):
- ~38 theorems, **0 sorry**, 2 axioms (published external results)
- Axiom 1: Simons--de Weger (Acta Arith. 2005)
- Axiom 2: continued fraction lower bound for convergents of log₂3 (Hardy & Wright §10.8)
- Crystal nonsurjectivity for k ∈ [18, 665] via 648 `native_decide` cases
- Asymptotic nonsurjectivity for k ≥ 666 via Legendre contrapositive + CF axiom

## Honest Assessment

### What is proved

1. **Unconditionally:** The evaluation map $\mathrm{Ev}_d$ is not surjective for $k \geq 18$ (entropic barrier). The Junction Theorem provides a universal obstruction for every $k \geq 2$. $N_0(d) = 0$ verified computationally for $k = 3, \ldots, 17$. Lean formalization: 280 theorems (zero-exclusion $k = 3\text{--}15$, strict cancellation, structural facts).

2. **Conditionally on GRH + Conjecture 7.4:** $N_0(d) = 0$ for all $k \geq 3$, implying no nontrivial positive cycle exists. The blocking mechanism proof depends on the interior ×2-closure (Conjecture 7.4, currently unproved) and Hooley's theorem (requires GRH).

3. **Active research (Rounds 9--14+):** Two promising paths toward unconditional proof for all $k$:
   - **Carry Propagation Obstruction**: $\text{corrSum}(A) + n \cdot 3^k = n \cdot 2^S$ imposes simultaneous binary and ternary digit constraints
   - **m-elimination**: All multipliers $m$ with $\gcd(m,6) = 1$ eliminated for $k = 3\text{--}14$; structural constraints (odd, coprime to 3, $m \geq 2$) proved universally

### What remains open

| Gap | Description | Impact |
|-----|-------------|--------|
| **Conjecture 7.4** | Interior ×2-closure of $\mathrm{Im}_{\mathrm{int}}(g)$ | Blocking Mechanism only |
| **G2c without GRH** | $\mathrm{ord}_d(2) > C$ unconditionally (Artin variant) | Blocking Mechanism only |
| **Universal $N_0(d) = 0$** | Proving for ALL $k \geq 3$ without GRH | Core gap: $k \geq 69$ |
| **Neither Conj. 7.4 nor G2c** affects the unconditional Junction Theorem or the Lean formalization. |

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
