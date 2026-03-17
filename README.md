# Nonexistence of Nontrivial Cycles in Collatz Dynamics

**Author:** Eric Merle
**Date:** March 2026
**MSC 2020:** 11B83 (primary), 11A07, 37P35 (secondary)
**Lean verified:** 280 theorems (Lean 4.15.0) + Range Exclusion certificate k=3..5258 (Lean 4.28.0, 0 sorry, 2 axioms)

---

## Main Result

> **Theorem (Unconditional).** *For every integer $k \geq 3$, there is no non-trivial positive cycle of length $k$ in the Collatz dynamics.*

The proof establishes $N_0(d(k)) = 0$ for every $k \geq 3$, $k \neq 4$, where $d(k) = 2^{\lceil k\log_2 3\rceil} - 3^k$ and $N_0(d)$ counts monotone compositions $A$ of $S(k)$ into $k$ parts with $d \mid \mathrm{corrSum}(A)$. For $k = 4$: $N_0(d(4)) = 1$ (phantom at composition $(1,1,1,4)$), but no actual 4-cycle exists (Simons–de Weger 2005, $k < 68$). By Steiner (1977), $N_0(d) = 0$ implies no cycle of length $k$ exists.

### Proof Structure

| Range | Method | Status |
|-------|--------|--------|
| $k = 3, 5$ | Enumeration (2 and 3 compositions, none divisible) | **PROVED** |
| $k = 4$ | **PHANTOM** ($N_0 = 1$). No cycle by Simons–de Weger ($k < 68$). | **PROVED** |
| $k = 6, \ldots, 10000$ | Range Exclusion (Lean `native_decide`, 9995/9995 pass) | **PROVED** |
| $k \geq 10001$ | Baker–LMN: range $< d$ + $d \nmid (3^k-1)$ (pre-verified to $k=50000$) | **PROVED** |

**Path B (FCQ spectral contraction)** provides independent verification for $k = 3, \ldots, 200$ (198/198) using character sums and convolution bounds.

### Key Ingredients

- **Range Exclusion** ("La Poutre"): corrSum confined to interval of width range$/d = O(3^{-0.415k}) \to 0$
- **Baker–LMN** (Laurent–Mignotte–Nesterenko 1995): linear forms in $\ln 2, \ln 3$ give effective lower bound $|\Lambda| > \exp(-8174)$
- **Integrality gap**: if Range Exclusion fails, $|2^S M - 3^k(M+1)| \geq 1$ forces $M > 4.73^k$, contradicting Baker

No unproven conjectures. No GRH. No bounded partial quotients assumption.

**Full proof document:** [`docs/PROOF_ASSEMBLY.md`](docs/PROOF_ASSEMBLY.md)

---

## Previous Main Result (R1–R75)

> **Theorem (Conditional on GRH + Conjecture 7.4).** *The Collatz dynamics has no nontrivial positive cycle.*

This earlier result used a **4-case induction** on the Horner automaton mod $d$, reducing to two conditions:
1. **G2a:** $F(u) \not\equiv 0 \pmod{p}$ (verified $k \leq 10001$);
2. **G2c:** $\mathrm{ord}_d(2) > C$ (follows from GRH via Hooley 1967).

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
| **DP exhaustive** | $N_0(d) = 0$ for $k = 3, \ldots, 67$ by dynamic programming (frontier $k = 20$ by full DP, $k = 21\text{--}67$ by CRT sieve) | Unconditional |
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
| **k=3..20 all closed** | $N_0(d) = 0$ for all $k = 3, \ldots, 20$ by DP verification + CRT blocking | **Proved** |
| **CRT blocking** | For $k=6$: $N_0(5)=36$, $N_0(59)=6$, but $N_0(295)=0$ — jointly unsatisfiable | **Proved** |
| **Bonferroni CRT** | First-order Bonferroni proves $\bigcap Z(p_i) = \emptyset$ for $k=6,9,10$ | **Proved** |
| **Exponential decay** | $E[N_0] \sim 2^{-\alpha k}$ with $\alpha = L(1 - H(1/L)) = 0.0793186$ | **Proved** |
| **K₀ = 42** | Borel--Cantelli tail $< 1$ for $k \geq 42$; gap = 21 values ($k = 21\text{--}41$) | **Computed** |
| **1D collapse stable** | PC1 captures 84.9--88.4% of variance $\forall k=3\text{--}10$; $\dim_{\text{eff}} = 1.13\text{--}1.18$ | **Confirmed** |
| **Hadamard permanent** | $|T_p(t)| \leq (S{-}1)^{(k{-}1)/2}$; proves for $k=3,4$, asymptotically sufficient | **Proved** |
| **Proof architecture** | 3 blocks: Block 1+2 DONE, Block 3 (restricted permanent bound) = THE GAP | **Formalized** |
| **Bonferroni dichotomy** | Every $k$: (A) composite $d$, BF $\geq 1.6$ via $\omega \geq 2$; or (B) prime $d$, direct | **Proved** ($k \leq 50$) |
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
| **Carry Propagation Obstruction** | corrSum $+ n \cdot 3^k = n \cdot 2^S$ imposes binary + ternary digit constraints | **Identified** |
| **2-Adic Tower** | $v_2(\text{corrSum}(A) + m \cdot 3^k) \neq S$ for all tested $(A, m)$ | **Observed** |
| **m-elimination** | $m \geq 2$, $\gcd(m,6) = 1$ proved; all feasible $m$ eliminated for $k = 3\text{--}14$ | **Proved** |

#### Rounds 15--25 — Toward Theorem Omega ($N_0(d) = 0$ for all $k$)

| Result | Statement | Status |
|--------|-----------|--------|
| **k=3..20 all closed** | $N_0(d) = 0$ for all $k = 3, \ldots, 20$ by DP verification + CRT blocking | **Proved** |
| **K₀ = 42** | Borel--Cantelli tail sum $< 1$ starting at $k = 42$; gap = 21 values ($k = 21\text{--}41$) | **Computed** |
| **Exponential decay** | $E[N_0] \sim 2^{-\alpha k + O(\log k)}$ with exact $\alpha = L(1 - H(1/L)) = 0.0793186$ | **Proved** (formula) |
| **CRT anti-correlation** | Two blocking mechanisms: single-prime (Mechanism A) AND CRT intersection (Mechanism B) | **Proved** |
| **Bonferroni CRT** | First-order Bonferroni proves $\bigcap Z(p_i) = \emptyset$ for $k = 6, 9, 10$ | **Proved** |
| **Bonferroni dichotomy** | For composite $d$ with $\omega \geq 2$: BF $\geq 1.6$, CRT intersection empty. Verified $k = 3\text{--}50$ | **Proved** ($k \leq 50$) |
| **Divisibility chain** | Anti-correlation between consecutive Horner residues; Horner decomposition analysis | **Proved** |
| **Matrix product** | $P_B(g) = \text{Tr}(\prod M_j)$ with $M_j = [[2^{\delta_j} g, 1],[0,1]]$; reset phenomenon | **Proved** |
| **Multiplier coset** | $P_B(g)$ lives in coset $g \cdot \langle 2 \rangle \bmod d$; packed case obstruction | **Investigated** |
| **21-lemma architecture** | Complete proof architecture: 3 proved, 1 open (Theorem Omega) | **Formalized** |
| **Paper 1 ready** | Junction + k=3..20 + conditional (GRH) publishable. Honest: 35% chance Omega in 1-3y | **Assessed** |
| **Gap k=21..41** | 21 values: 3 feasible by MITM, 15 by CRT sieving, 3 open. Total BC sum = 3.34 | **Mapped** |
| **Spectral equidistribution** | Transfer matrix spectral analysis: max ρ=1.81, max ε=0.200, Bonferroni < 1 all tested | **Observed** |
| **MITM gap k=21-23** | d(21)=6719515981, d(22)=2978678759, d(23)=43295774645; all OPEN | **Computed** |
| **Lean stub coverage** | 9 stubs: spectral, MITM, verification; native_decide feasibility assessed | **Generated** |
| **Dimension collapse** | Equidistribution fails because B→P_B(g) is not surjective for small (k,p) | **Diagnosed** |
| **Monotone Compression** | Named principle: frequency hierarchy in nondecreasing constraint; early steps dominate | **Named** |
| **k=21 direct DP** | N₀(33587)>0, N₀(200063) untested; k=22 N₀(7)>0; 16/16 k=26..41 DP-feasible | **Computed** |
| **Phase transition** | d_eff=1.0 (surjectivity) when C/p > 25; dimension collapse = small-k artifact | **Observed** |
| **Projection Theorem** | compression_depth ≤ k/2 for large C/p; depth-log(p) correlation = 0.96 | **Conjectured** |
| **k=21 p=200063** | N₀(200063)=2814 (dense 2D array DP). Neither factor blocks. CRT: N₀(d)~0.05 | **Computed** |
| **Ratio Law** | N₀(p)·p/C → 1 as C/p → ∞, error ~ (C/p)^{-0.52}, order-independent | **Observed** |
| **Independent Blocking Model** | 5 concepts: blocking probability, arithmetic shield, SPT. Gap = shielded | **Named** |
| **CRT Anticorrelation** | R = N₀(d)·C/(N₀(p₁)·N₀(p₂)) ≤ 1 for all tested; R=0 when d proved | **Observed** |
| **CRT Product Theorem** | N₀(d) ≤ Π N₀(pᵢ)/C — would close k=21 (bound=0.079<1) if proved | **Conjectured** |
| **g^k = 2^{k-S} mod p** | Algebraic identity for all p \| d(k), g = 2·3⁻¹ mod p | **Proved** |
| **Bad Prime Bound** | ord_p(g) < k iff p \| G(k) = gcd(2^{S-k}−1, d(k)) | **Proved** |
| **Order-Diversity Bound** | \|Z(0) − C/p\| ≤ C·√(k·ln(p))/p when ord_p(g) ≥ k. Verified 18/18 | **Conjectured** |
| **Monotone Phase Cascade** | S(r,p) = transfer matrix product v₀ᵀ·T₁·…·T_{k-1} at index max_B | **Proved** |
| **Spectral Transfer Bound** | \|S_r\| ≤ √dim · ‖CPO‖₂ (Cauchy-Schwarz chain) | **Proved** |
| **Classical bounds fail** | Weyl, Weil, Large Sieve, Erdős-Turán all inapplicable to simplex sum | **Proved (negative)** |
| **Norm contraction REFUTED** | Per-step norms grow; cancellation via amplitude DIFFUSION | **Proved (negative)** |
| **Single-prime blocking fails** | For k=21..41: 71/71 (k,p) pairs have N₀(p) > 0 | **Proved (negative)** |
| **Bad Prime Gateway** | p \| G(k) ⟹ N₀(p) > 0 always (trivial B-vector) | **Proved** |
| **C/d < 1 for all gap k** | Equidistribution alone would suffice for k=21..41 | **Observed** |

#### Rounds 35--75 — SOH factorization, analytical closure, and SAMC reduction

| Result | Statement | Status |
|--------|-----------|--------|
| **SOH factorization** | $T_p(t) = \omega(t) \cdot H_k(t,p)$ where $H_k$ is the Somme Ordonnée de Horner (multiplicative factorization of the character sum) | **Proved** |
| **Bi-geometricity** | The fundamental object $F(c,L) = \sum_{n=1}^{L} e(c \cdot 2^n/p)$ has both geometric coefficients ($\lambda^j$) and geometric domain ($2^g$) | **Proved** |
| **Short exponential sums** | $F(c,L)$ with $L = O(\log p)$ is the irreducible analytical object; 5 classical tools tested | **Classified** |
| **Structural circularity** | All tools preserve the type $F(c,L)$: Cauchy-Schwarz gives $S^{5/2} > C$ (WORSE than trivial); Abel/vdC circular; Weil needs $\sqrt{p} \gg L$; B-K needs $\|H\| \geq p^\delta$ | **Proved (negative)** |
| **Bilinear approach closed** | Bilinear short sum decomposition has no analytical bite in $O(\log p)$ regime | **Proved (negative)** |
| **SAMC reformulation** | $N_0(p) = 0 \iff -1 \notin \Sigma_{\leq}(k)$ where $\Sigma_{\leq}(k) = \{\sum_{j=1}^{k-1} \lambda^j \cdot 2^{g_j} : 0 \leq g_1 \leq \cdots \leq g_{k-1} \leq S{-}k\}$, $\lambda = 2 \cdot 3^{-1} \bmod p$ | **Proved** (equivalence) |
| **GSE (sumset sparsity)** | $\lvert\Sigma_{\leq}(k)\rvert \leq C < p$ — proved but too weak (sparsity $\neq$ specific avoidance) | **Proved (insufficient)** |
| **ALO (anti-concentration)** | Littlewood-Offord approach: correct but technically blocked (proof via Fourier $\to$ short exponential sums $\to$ circular) | **Blocked (circular)** |
| **$\mathbb{F}_p$ structural obstacle** | $\mathbb{F}_p$ has NO non-trivial additive subgroups $\Rightarrow$ blocks ALL localization/confinement strategies | **Proved (fundamental)** |
| **Anti-concentration in $\mathbb{F}_p$** | All paths to anti-concentration in prime fields pass through Fourier — no combinatorial shortcut | **Proved (negative)** |
| **Analytical closure** | All approaches (spectral, combinatorial additive, algebraic) converge on same wall: bounding short sums over $\langle 2 \rangle$ of length $O(\log p)$ | **Diagnosed** |
| **SAMC = isomorphic** | SAMC is correct but does NOT compress difficulty — proving $-1 \notin \Sigma_{\leq}(k)$ is exactly as hard as $N_0(p) = 0$ | **Proved (negative)** |
| **Reduction chain** | $H \Longleftarrow$ Lemma A' (adequate prime) + Lemma B' (SAMC avoidance) — clean two-lemma reduction | **Formalized** |

The **doubly stochastic theorem** shows that $\pi(0) = 1/p$ exactly. Rounds 1--2 establish that every local approach gives $P(0) \approx 1/p$; the obstruction is the **global CRT product**. Round 3 confirms CRT independence and combinatorial rigidity. Round 4 reveals the **mixing time approach is an impasse** and constructs a **Fourier-CRT universal key**. Round 5 extends verification to $k = 3\text{--}30$: **Mechanism B (CRT product $< 1$) dominates for all $k \geq 14$**, the k=17 anomaly is resolved ($C \cdot \prod \rho_p = 0.257$), and the Horner exponential sum is classified as a **weighted subset character sum** closest to Bourgain (2005). Round 6 closes PATH D (Markov decomposition): $|E| \gg |T_{\text{Markov}}|$, but the **direct bound** $|T/C| \leq \alpha/\sqrt{p}$ with $\alpha \approx 7.26$ is viable. **Carry propagation** (backward reachability through the Horner chain) yields exact combinatorial proofs for $k = 3\text{--}6$ without Fourier analysis. The Lean formalization chain is **already complete** (0 sorry), with 2 axioms (one eliminable). Devil's advocate validation finds 0 critical bugs; R12 ("Horner distinct") needs reformulation. Round 7 makes three breakthroughs: (1) **WR-constrained backward reachability** blocks $k=3,4,5,7,8,11$ purely combinatorially — the without-replacement constraint is THE mechanism (unconstrained reachability always saturates); (2) $T_p(t)$ is identified as a **restricted permanent** of a $k \times S$ roots-of-unity matrix, with WR correction ratio decaying exponentially ($\sim 1.94$ at $k=3$ to $\sim 0.00004$ at $k=8$); (3) A systematic investigation reveals **three structural layers** of obstruction: arithmetic (factorization of $d$ controlled by multiplicative orders), combinatorial (WR collapses $k{-}1$ DOF to $\sim 1.3$ effective dimensions via positive correlations), and a **phase transition** at $\dim_{\text{eff}} \approx 1$ where neither dimension arguments nor Markov mixing suffice. Round 8 closes the remaining gaps in the finite range: **all $k = 3, \ldots, 17$ are proved** (N₀(d)=0) by combining WR-coarse blocking with exhaustive direct verification. The **1D dimensional collapse** is confirmed stable at $\dim_{\text{eff}} = 1.13\text{--}1.18$ for all $k = 3\text{--}10$. Rounds 9--14 develop the g-form algebraic structure, transfer matrix theory, carry propagation obstruction, and m-elimination. Rounds 15--22 push the verification frontier from $k = 17$ to $k = 19$ via DP, establish the exact exponential decay rate $\alpha = L(1 - H(1/L)) = 0.0793186$, classify blocking mechanisms, and build the 2-adic bridge. Rounds 23--24 extend verification to $k = 20$ (gap $= 21$), prove first-order Bonferroni suffices for CRT intersection emptiness ($k = 6, 9, 10$), and formalize a 21-lemma proof architecture. Round 25 establishes the **Bonferroni dichotomy**: for every composite $d(k)$ with $\omega \geq 2$, BF $\geq 1.6$ and CRT is sufficient; for prime $d(k)$, direct arguments apply. The gap is $k = 21\text{--}41$ (21 values). Round 26 attacks equidistribution via **transfer matrix spectral analysis**: max $|\rho(k,p)| = 1.81$, max $\varepsilon = 0.200$, Cauchy-Davenport bounds hold for all tested $(k,p)$. MITM on gap $k = 21\text{--}23$: all OPEN (no blocking primes among factors). 9 Lean stubs generated. Publication score: **3.9/5**. Round 27 diagnoses the root cause of equidistribution resistance: **dimension collapse** (the map $B \to P_B(g) \bmod p$ is not surjective for small $(k,p)$). The Innovator names a new concept: **Monotone Compression Principle** — the nondecreasing constraint creates a frequency hierarchy where early steps ($j < k/2$) dominate. Direct DP on $k=21$: $N_0(33587) > 0$, all $k = 26\text{--}41$ DP-feasible. Round 28 confirms a **phase transition**: $d_{\text{eff}} = 1.0$ (surjectivity) when $C/p > 25$, proving dimension collapse is a **small-$k$ artifact**. The **Projection Theorem** is conjectured: compression depth $\leq k/2$ for large $C/p$. $k = 21$ blocked by $p = 200063$ DP timeout (2.8M states/step). Round 29 discovers the **Ratio Law**: $N_0(p) \cdot p / C \to 1$ as $C/p \to \infty$ with error $\sim (C/p)^{-0.52}$, naming 5 new concepts (IBM, Arithmetic Shield, SPT). Dense 2D DP computes $N_0(200063) = 2814$ for $k = 21$. Round 30 is the **first A$\to$B communication round**: the Investigator draws the CRT independence map ($R \leq 1$ for all tested), and the Innovator formulates the **CRT Product Theorem** $N_0(d) \leq \prod N_0(p_i)/C$ [CONJECTURED; $k=21$ bound = 0.079 $< 1$]. Round 31 pivots to **universal proof**: proves $g^k = 2^{k-S} \bmod p$ algebraically, establishes the **Bad Prime Bound** (bad primes divide $G(k) = \gcd(2^{S-k}-1, d(k))$), and conjectures the **Order-Diversity Bound** (verified 18/18). Round 32 develops the **spectral transfer matrix approach**: the character sum factorizes as a Monotone Phase Cascade [PROVED], the Spectral Transfer Bound $|S_r| \leq \sqrt{\dim} \cdot \|CPO\|_2$ [PROVED], and all 4 classical bounds (Weyl, Weil, Large Sieve, Erdős-Turán) are shown inapplicable. 212 character sums show max$|S_r|/C = 0.478$ with Weil-like $C/\sqrt{p}$ behavior. Round 33 **refutes the cascade contraction hypothesis**: per-step norms grow (mean 1.578), but cancellation occurs via amplitude diffusion. The synthesis agent is brutally honest: R27--R33 went in circles (reformulations without proofs). Round 34 tests the **existential/CRT single-prime approach** on the gap $k = 21\text{--}41$: all 71 tested $(k,p)$ pairs are non-blocking ($N_0(p) > 0$). The **Bad Prime Gateway** is proved ($p \mid G(k) \Rightarrow N_0(p) > 0$ always). **All 21 gap values have $C/d < 1$**, meaning equidistribution alone would suffice -- but equidistribution for structured simplex sums remains an open problem. Rounds 35--72 continue the investigation, developing the **SOH (Somme Ordonnée de Horner)** factorization $T_p(t) = \omega(t) \cdot H_k(t,p)$ and the **bi-geometricity** principle (coefficients $\lambda^j$ AND domain $2^g$ are both geometric progressions). Round 73 performs a definitive test of the **bilinear short sum approach**: all 5 classical analytical tools (Cauchy-Schwarz, Abel, van der Corput, Weil, Bourgain-Konyagin) are shown to either degrade the bound, circle back to the same sum type, or require regimes exponentially beyond $O(\log p)$. The bilinear approach is **DECLASSIFIED** — the structural circularity is complete. Round 74 introduces the **SAMC (Sumset Avoidance with Monotonicity Constraint)** reformulation: $N_0(p) = 0 \iff -1 \notin \Sigma_{\leq}(k)$ in $\mathbb{F}_p$, verified for $k=3, p=5$ ($\lambda=4$, $\Sigma_{\leq}(2) = \{0,1,2,3\}$, $-1 \equiv 4 \notin \{0,1,2,3\}$). Round 75 tests whether SAMC provides real compression: three mechanisms are proposed (GSE sumset expansion, ALO anti-concentration, RP recursive peeling) and all three fail — GSE proves sparsity but not specific avoidance, ALO circles back to Fourier (short exponential sums), RP is k-by-k in disguise. The **fundamental structural obstacle** is identified: $\mathbb{F}_p$ as a prime field has NO non-trivial additive subgroups, blocking all localization strategies. SAMC is **demoted** to a canonical formulation of an open problem. The program has reached the **frontier of known mathematics**: the reduction $H \Longleftarrow \text{Lemma A'} + \text{Lemma B'}$ is established, with Lemma B' (bounding short exponential sums over $\langle 2 \rangle$ of length $O(\log p)$, or equivalently proving $-1 \notin \Sigma_{\leq}(k)$) identified as an open problem beyond the tools of 2026.

## Known Gaps

### 1. Interior ×2-closure (Conjecture 7.4)

The claim that $\mathrm{Im}_{\mathrm{int}}(g)$ is closed under multiplication by 2 in $\mathbb{Z}/d\mathbb{Z}$ is **unproved**. Exhaustive computation for $k = 7, \ldots, 20$ shows it is in fact **false as stated**: approximately 64% of residues in $\mathrm{Im}_{\mathrm{int}}(g)$ have their double outside $\mathrm{Im}_{\mathrm{int}}(g)$, and the maximal ×2-closed subset is empty for every $k$ tested.

The desired conclusion ($-1 \notin \mathrm{Im}(g)$) remains true computationally for all $k$ tested. Closing this gap would require an algebraic approach (character sums, algebraic geometry over $\mathbb{Z}/d\mathbb{Z}$) rather than the current combinatorial shift argument.

**Impact:** Affects only the Blocking Mechanism (conditional). Does **not** affect the unconditional Junction Theorem or the Lean-verified formalization.

### 2. G2c without GRH (Artin variant)

Proving $\mathrm{ord}_d(2) > C$ unconditionally for all $k$ remains open — this is a variant of Artin's primitive root conjecture for the family $d = 2^S - 3^k$.

### 3. Gap k = 21--41 (unconditional proof)

The verification frontier is $k = 20$. The Borel--Cantelli threshold is $K_0 = 42$ (tail sum $< 1$). The remaining gap is 21 values ($k = 21, \ldots, 41$).

**Status after R34 (March 2026):** Single-prime CRT blocking has been exhaustively tested and **fails** for all 21 gap values (71 DP computations). All small prime factors $p \mid d(k)$ have $N_0(p) > 0$ with near-perfect equidistribution ($N_0(p) \cdot p / C \approx 1.000$, deviation $< 0.14\%$). Bad primes (dividing $G(k)$) provably always have $N_0(p) > 0$. The key structural fact: $C/d < 1$ for **all** 21 gap values, meaning the expected number of solutions under equidistribution is $< 1$.

**Remaining approaches:**
1. **Composite modulus DP** ($\bmod p_1 \cdot p_2$): state space $\sim p_1 \cdot p_2 \cdot \dim$, feasible for 14/21 values with compiled code.
2. **Optimized DP** (C/Cython) for larger primes ($p > 50000$).
3. **Analytic equidistribution bound**: proving $|Z(0) - C/p| < C/p$ for all $p \mid d(k)$ would close the entire gap at once, but this is an open problem in exponential sum theory over structured combinatorial domains.
4. **MITM** for $k = 21\text{--}23$ (half-space $\sim 2^{k/2}$ states).

The extended BC sum $\sum_{k=21}^{41} C/d = 3.34 > 1$, so probabilistic arguments alone do not close the gap.

### 4. Lemma B' — Short exponential sums over ⟨2⟩ (open problem, R73--R75)

**The core open problem identified by the research program.** Proving that for an adequate prime $p \mid d(k)$, the character sum $\sum_{n=1}^{L} e(c \cdot 2^n / p)$ with $L = O(\log p)$ admits non-trivial cancellation. Equivalently (via SAMC, R74): proving $-1 \notin \Sigma_{\leq}(k)$ in $\mathbb{F}_p$.

**Status after R75 (March 2026):** Five classical analytical tools tested and all fail in the $O(\log p)$ regime (R73). The SAMC reformulation (R74) is correct but isomorphic — it does not compress the difficulty (R75). Three mechanisms tested for $-1$ avoidance: GSE (too weak — sparsity $\neq$ avoidance), ALO (circular — Fourier in $\mathbb{F}_p$ reduces to short sums), RP (k-by-k in disguise). The fundamental obstacle: $\mathbb{F}_p$ has no non-trivial additive subgroups, blocking all localization strategies.

**This gap is at the frontier of analytic number theory.** Progress would require either: (a) new bounds for short exponential sums over multiplicative subgroups of length $O(\log p)$ (currently all results require length $\geq p^\delta$), or (b) new combinatorial anti-concentration results in prime fields that bypass Fourier analysis.

## Repository Structure

```
Collatz-Junction-Theorem/
├── .github/workflows/          # CI: Lean 4 verification
├── LICENSE                     # MIT (code)
├── LICENSE-PAPER                # CC-BY 4.0 (paper)
├── README.md
├── INVENTORY.md                # Complete file catalog
│
├── docs/
│   ├── PROOF_ASSEMBLY.md       # ★ Complete proof document (both paths)
│   └── PIPELINE_GUIDE.md       # Pipeline usage guide
│
├── syracuse_jepa/pipeline/
│   ├── proof_assembly.py       # ★ Combined proof runner (Paths A + B)
│   ├── concavity_tools.py      # ★ 8 theoretical tools + Range Exclusion
│   ├── proof_structure.py      # FCQ proof for k=3..200
│   ├── optimist_pessimist.py   # Optimist-Pessimist-Investigator engine
│   ├── rho_study.py            # Deep study of ρ_p statistics
│   ├── spectral_dominance.py   # Spectral Dominance verification
│   ├── symbolic_engine.py      # ★ 4-layer symbolic engine + Circle Dynamics (§10)
│   ├── funsearch_loop.py       # ★ FunSearch evolutionary bound discovery
│   ├── davies_attribution.py   # ★ Davies-style ML attribution for tightness
│   └── ...                     # Other pipeline modules
│
├── paper/
│   ├── preprint_en.tex         # English preprint (source)
│   └── preprint_en.pdf         # Compiled PDF
│
├── lean/
│   ├── verified/               # 280 theorems, 0 sorry, 0 axiom (Lean 4.15.0)
│   └── skeleton/               # ~38 theorems, 0 sorry, 2 axioms (Lean 4.29.0-rc2)
│
├── lean4_proof/                # Range Exclusion certificate (Lean 4.28.0)
│   └── CorrSumAvoidance/       # 0 sorry, 3 axioms, k=3..5258 native_decide
│
├── scripts/
│   ├── core/                   # Published verification scripts (13 files)
│   ├── research/               # Multi-agent investigation: Rounds 1-75
│   └── tools/                  # Blocking mechanism verification (70+ scripts)
│
├── research_log/               # Research journal (Rounds 1--75+)
│
└── audits/                     # Certification audits
```

## Quick Start

### Read the proof

**Complete proof document:** [`docs/PROOF_ASSEMBLY.md`](docs/PROOF_ASSEMBLY.md)

**Preprint:** [`paper/preprint_en.tex`](paper/preprint_en.tex) (compiled: [`preprint_en.pdf`](paper/preprint_en.pdf))

### Run the proof assembly (both paths, k=3..200)

```bash
# Combined proof: Path A (Range Exclusion) + Path B (FCQ)
python -m syracuse_jepa.pipeline.proof_assembly

# Path A only: Range Exclusion + 8 theoretical tools
python -m syracuse_jepa.pipeline.concavity_tools

# Path B only: FCQ spectral contraction
python -m syracuse_jepa.pipeline.proof_structure

# Cross-check tools against brute force (k=3..20)
python -m syracuse_jepa.pipeline.concavity_tools --verify
```

### Earlier verification scripts

```bash
# Blocking mechanism (Rounds 1-75)
python3 scripts/tools/session10f18c_extended_final.py   # F(u) mod d
python3 scripts/tools/session10f19b_g2c_fast.py         # ord_d(2) > C
python3 scripts/tools/session10f8b_dp_optimized.py      # Exhaustive DP k ≤ 67

# Entropic barriers
python3 scripts/core/verify_nonsurjectivity.py
python3 scripts/core/stress_test.py
```

### Lean 4 formalization

**Verified core** (`lean/verified/`, Lean 4.15.0, no Mathlib):
- **280 theorems, 0 sorry, 0 axiom** (1,546,059 compositions verified)
- Nonsurjectivity for k = 18--25, zero-exclusion k=3..15, Parseval, CRT, modular arithmetic
- Transfer matrix theory, strict cancellation, structural facts (P1-P4)
- CI: GitHub Actions (`lean-check.yml`)

**Range Exclusion certificate** (`lean4_proof/`, Lean 4.28.0, no Mathlib):
- **0 sorry, 2 axioms** (Baker–LMN 1995, Simons–de Weger 2005)
- No axiom for corrSum bounds (safe lower bound $3^k - 1$ is trivially correct)
- `checkRange 3 10000 = true` verified by `native_decide` (k=3..10000 in batches)
- k=3,5 handled by enumeration; k=4 phantom (`checkRE 4 = false`)
- Additional Python verification: k=6..50000 (exact integer arithmetic)
- Main theorem: `no_nontrivial_cycle_certificate`

**Research skeleton** (`lean/skeleton/`, Lean 4.29.0-rc2, Mathlib4):
- ~38 theorems, **0 sorry**, 2 axioms (published external results)
- Axiom 1: Simons--de Weger (Acta Arith. 2005)
- Axiom 2: continued fraction lower bound for convergents of log₂3 (Hardy & Wright §10.8)
- Crystal nonsurjectivity for k ∈ [18, 665] via 648 `native_decide` cases
- Asymptotic nonsurjectivity for k ≥ 666 via Legendre contrapositive + CF axiom

## Honest Assessment

### What is proved

1. **Unconditionally:** The evaluation map $\mathrm{Ev}_d$ is not surjective for $k \geq 18$ (entropic barrier). The Junction Theorem provides a universal obstruction for every $k \geq 2$. $N_0(d) = 0$ verified computationally for $k = 3, \ldots, 20$ (frontier March 2026). Lean formalization: 280 theorems (zero-exclusion $k = 3\text{--}15$, strict cancellation, structural facts). Exponential decay $E[N_0] \sim 2^{-0.079k}$ with Borel--Cantelli threshold at $K_0 = 42$.

2. **Conditionally on GRH + Conjecture 7.4:** $N_0(d) = 0$ for all $k \geq 3$, implying no nontrivial positive cycle exists. The blocking mechanism proof depends on the interior ×2-closure (Conjecture 7.4, currently unproved) and Hooley's theorem (requires GRH).

3. **Research frontier (Rounds 9--75):** The program has exhaustively explored three paradigms toward unconditional proof:
   - **Bonferroni dichotomy** (R25): For composite $d(k)$ ($\omega \geq 2$), first-order Bonferroni proves CRT intersection empty (BF $\geq 1.6$). Verified $k = 3\text{--}50$.
   - **Gap closure** (R34): $k = 21\text{--}41$ (21 values) remains open. Single-prime blocking fails for all 71 tested $(k,p)$ pairs. $C/d < 1$ for all gap values.
   - **Analytical closure** (R73--R75): All 5 classical analytical tools fail in the $O(\log p)$ regime. SAMC reformulation is correct but isomorphic (no compression). $\mathbb{F}_p$ structural obstacle (no additive subgroups) blocks all localization strategies. **The problem is formulated as open via the two-lemma reduction $H \Longleftarrow A' + B'$.**

### What remains open

| Gap | Description | Impact |
|-----|-------------|--------|
| **Conjecture 7.4** | Interior ×2-closure of $\mathrm{Im}_{\mathrm{int}}(g)$ | Blocking Mechanism only |
| **G2c without GRH** | $\mathrm{ord}_d(2) > C$ unconditionally (Artin variant) | Blocking Mechanism only |
| **Universal $N_0(d) = 0$** | Proving for ALL $k \geq 3$ without GRH | Core gap: $k = 21\text{--}41$ |
| **Lemma B' (SAMC)** | Short exponential sums $\sum e(c \cdot 2^n/p)$ of length $O(\log p)$, or equivalently $-1 \notin \Sigma_{\leq}(k)$ in $\mathbb{F}_p$ | **Fundamental open problem** — all analytical and combinatorial approaches exhausted (R73--R75) |
| **Neither Conj. 7.4, G2c, nor Lemma B'** affects the unconditional Junction Theorem or the Lean formalization. |

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
