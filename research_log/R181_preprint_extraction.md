# R181 -- Deep Structural Extraction from Preprint (preprint_en.tex)

Date: 2026-03-15

---

## 1. COMPLETE LIST OF THEOREMS/PROPOSITIONS

### Definitions
| Label | Name | Line | Summary |
|-------|------|------|---------|
| Def 2.1 | Admissible composition | ~260 | Comp(S,k) = strictly increasing sequences A_0=0 < A_1 < ... < A_{k-1} <= S-1; |Comp|=C=binom(S-1,k-1) |
| Def 3.1 | Entropic deficit | ~355 | gamma = 1 - h(1/log_2(3)) where h = binary Shannon entropy |
| Def 2.3 | Evaluation map | ~330 | Ev_d: Comp(S,k) -> Z/dZ, A |-> corrSum(A) mod d |
| Def 5.1 | N_r(p) and T(t) | ~580 | N_r = #{A : corrSum(A) = r mod p}; T(t) = sum_A e(t*corrSum(A)/p) |
| Def 5.3 | M(chi) | ~670 | Multiplicative sum = sum_{corrSum != 0} chi(corrSum(A) mod p) |
| Def 6.1 | Hypothesis (H) | ~744 | N_0(d) = 0 for all k >= 3 |
| Def 7.2 | Horner image g(B) | ~1186 | g(B) = sum_{j=1}^{k-1} u^j * 2^{B_j} mod d, u = 2*3^{-1} mod d |
| Def 7.5 | Boundary classification | ~1253 | Interior / Left-border / Right-border / Double-border |
| Def 7.8 | Annihilation polynomial F(u) | ~1466 | F(u) = u^{2n+2} + u^{n+2} - 2u^{n+1} - u^n - 1, n=(k-3)/2 |

### Propositions and Lemmas
| Label | Name | Line | Summary |
|-------|------|------|---------|
| Prop 2.2 | Steiner's equation | ~271 | n_0 * d = corrSum(A), corrSum(A) = sum_{i=0}^{k-1} 3^{k-1-i} * 2^{A_i} |
| Rem 2.4 | corrSum arithmetic | ~309 | corrSum(A) is always odd; 3 does not divide corrSum(A) |
| Prop 3.2 | gamma value | ~363 | gamma = 0.05004... > 0 |
| Lem 3.3 | Binomial-entropy | ~386 | log_2 C <= (S-1)*h(alpha), alpha=(k-1)/(S-1) |
| Prop 3.4 | Linear deficit | ~406 | log_2(d) - log_2(C) >= (S-1)*gamma - epsilon(k), epsilon(k) = O(log k) |
| Prop 5.2 | Inversion formula | ~595 | N_0(p) = C/p + R(p), R(p) = p^{-1} sum_{t=1}^{p-1} T(t) |
| Prop 5.3 | Parseval identity | ~612 | sum |T(t)|^2 = p * sum N_r(p)^2 |
| Lem 6.2 | Peeling lemma | ~770 | N_0(p) <= (k-1)/(S-1) * C, provided ord_p(2) >= S |
| Cor 6.3 | Peeling corollary | ~795 | N_0(p) <= 0.631*C asymptotically |
| Prop 6.5 | M implies H (sketch) | ~814 | Under Conj M, N_0(p) = 0 for large k (sketch only, caveat on p growing exponentially) |
| Prop 6.7 | Barrier | ~873 | No moment method can prove N_0(p)=0 when p ~ C^{1+eta} |
| Lem 7.3 | Horner equivalence | ~1198 | N_0(d) = #{B : g(B) = -1 mod d}; bijection A_j |-> B_j = A_j - j |
| Lem 7.4 | Shift identity | ~1238 | g(B+1) = 2*g(B) mod d |
| Lem 7.7 | Iterated peeling | ~1437 | Double-border equation reduces to 1+P+Q = 0 mod d |
| Prop 7.9 | Polynomial criterion | ~1474 | Double-border has solution iff F(u) = 0 mod d |
| Lem 7.10 | sigma-zero equivalence | ~1564 | sigma_tilde(u) = 0 iff d | (3^{k-1} - 2^{k-1}) |
| Prop 7.11 | Zsygmondy classification | ~1579 | Among prime d, sigma_tilde=0 only for k=3 and k=5 |
| Prop 7.12 | Coupling G1-G2a | ~1602 | If sigma_tilde=0 then F(u) != 0 mod d |
| Prop 7.13 | CRT inequality | ~1623 | N_0(d) <= N_0(p) for any p|d |

### Theorems
| Label | Name | Line | Status | Summary |
|-------|------|------|--------|---------|
| Thm 3.5 | Nonsurjectivity | ~451 | **Unconditional, Lean-verified** | C(k) < d(k) for all k >= 18 |
| Thm 4.1 | Simons-de Weger | ~490 | External (Acta Arith 2005) | No cycles with k <= 68 |
| Thm 4.2 | Junction Theorem | ~508 | **Unconditional, Lean-verified** | For every k >= 2, at least one obstruction applies |
| Thm 5.4 | Parseval cost | ~626 | **Unconditional, NOT formalized** | If N_0(p)>=1, then sum |T(t)|^2 >= (p-C)^2/(p-1) |
| Thm 5.5 | Mellin-Fourier bridge | ~684 | **Unconditional, NOT formalized** | T(t) decomposition into multiplicative characters via Gauss sums |
| Thm 5.6 | Multiplicative Parseval | ~720 | **Unconditional, NOT formalized** | sum_{chi != chi_0} |M(chi)|^2 = (p-1) sum_{n!=0} N_n^2 - (C-N_0)^2 |
| Thm 7.14 | Integer evaluation F_Z | ~1491 | **Unconditional** | F_Z = 4^m - 9^m - 17*6^{m-1}; odd, coprime to 3, negative for m>=2, = 3 mod 5 |
| Thm 7.15 | Blocking Mechanism | ~1654 | **Conditional on GRH + gaps** | N_0(d) = 0 for all k >= 3 |
| Prop 8.1 | Theorem Q | ~1804 | **Conditional** | If |sum T(t)| <= 0.041*C and d has a prime > 1.041*C, then no cycles |
| Conj 6.4 | Conjecture M | ~805 | **Conjecture** | |T(t)| <= c*C*k^{-delta} for some delta > 0 |
| Conj 7.6 | Interior closure | ~1268 | **FALSE (disproved computationally!)** | Im_int(g) is NOT x2-closed; fraction ~63% fail |
| Prop 8.2 | Effective Regime B vacuity | ~2088 | Computational | 57 Regime B primes for m<=300, all verified |
| Prop 8.3 | One Good Prime Suffices | ~2138 | Computational + asymptotic | Only need Cond Q for a single Regime A prime |

---

## 2. ALPHA-DIOPHANTINE APPROACH -- Extracted Ingredients

### 2.1 Exact formula for corrSum(B) = g(v)

**Steiner's corrective sum** (Prop 2.2, line ~279):
```
corrSum(A) = sum_{i=0}^{k-1} 3^{k-1-i} * 2^{A_i}
```
where A = (A_0=0, A_1, ..., A_{k-1}) with 0 = A_0 < A_1 < ... < A_{k-1} <= S-1.

**Weights**: The i-th term has weight `3^{k-1-i}` (geometric, decreasing in i) times `2^{A_i}` (exponential in position).

**Horner reformulation** (Def 7.2, line ~1190): After change of variables B_j = A_j - j:
```
g(B) = sum_{j=1}^{k-1} u^j * 2^{B_j}  (mod d)
```
where u = 2 * 3^{-1} mod d, and B is non-decreasing in {0,...,M}, M = S-k.

**Key identity** (Lem 7.3, line ~1224):
```
3^{-(k-1)} * corrSum(A) = 1 + g(B)  (mod d)
```
So corrSum(A) = 0 mod d  iff  g(B) = -1 mod d.

### 2.2 Bounds on g(v)

**Peeling lemma** (Lem 6.2, line ~770): If ord_p(2) >= S, then
```
N_0(p) <= (k-1)/(S-1) * C
```
Proof technique: fix all components except A_{k-1}; the term 2^{A_{k-1}} takes distinct values mod p (since ord_p(2) >= S), so at most one value works. Count of partial choices = binom(S-2, k-2) = (k-1)/(S-1)*C.

**Archimedean analysis**: The paper does NOT bound the archimedean size of g(v) directly. The only size information is:
- corrSum(A) > 0 always (all terms positive)
- corrSum(A) is odd (Rem 2.4)
- corrSum(A) is coprime to 3 (Rem 2.4)
- For the double-border case: F_Z = 4^m - 9^m - 17*6^{m-1} < 0 for m >= 2 (Thm 7.14)

### 2.3 Image of g: achievable residues mod d

**What is known**:
- 0 in Im(Ev_d) iff cycle exists (by definition)
- corrSum is always odd and coprime to 3, so Im(Ev_d) subset {r in Z/dZ : r odd, gcd(r,3)=1}
- |Im(Ev_d)| <= C < d for k >= 18 (nonsurjectivity)
- For k=2: N_0(7)=1 (the composition (0,2) gives corrSum=7, so 0 in Im)
- For k=3,...,20: N_0(d)=0 verified exactly
- The x2-closure of Im_int(g) is EMPTY for all k tested (Rem 7.8, line ~1331) -- this is a crucial negative finding

### 2.4 Ingredients for Alpha-Diophantine

The **annihilation polynomial** F(u) = u^{2n+2} + u^{n+2} - 2u^{n+1} - u^n - 1 (line ~1469) reduces the double-border case to a Diophantine question: does d | F_Z where F_Z = 4^m - 9^m - 17*6^{m-1}?

Key facts:
- F_Z = 3 mod 5 always (so 5 never divides F_Z)
- F_Z is odd and coprime to 3
- |F_Z|/d < 5 for typical k, and mod-8 analysis eliminates quotients n=1,2,3,4
- Only 8 "critical primes" p in {11, 37, 53, 59, 109, 191, 283, 8363} ever satisfy p | F_Z and p | d simultaneously
- Verified d does not divide F_Z for all odd k <= 10001

**The u^k identity** (line ~1433): u^k = 2^{-M} mod d. This connects the multiplicative structure to the Diophantine approximation of log_2(3).

---

## 3. EXPONENTIAL SUMS APPROACH -- Extracted Ingredients

### 3.1 Condition Q (exact statement)

**Theorem Q** (Prop 8.1, line ~1804): Condition Q is the pair:
1. For every prime p | d(k): |sum_{t=1}^{p-1} T(t)| <= 0.041 * C
2. d(k) has at least one prime factor p > 1.041 * C(k)

The threshold 0.041 comes from: N_0(p) = C/p + R(p) is a non-negative integer; if C/p < 1 and |R(p)| < 1 - C/p, then N_0(p) = 0. With p > 1.041*C, we get C/p < 1/1.041 ~ 0.959, leaving margin 0.041 for |R(p)|.

**Status**: Condition (2) is NOT universally satisfied -- only 8/83 values of k in [18,100] have max prime factor > 1.041*C. This is a genuine hypothesis.

### 3.2 Character sum estimates in the paper

**Mellin-Fourier bridge** (Thm 5.5, line ~684):
```
T(t) = N_0(p) - (C-N_0(p))/(p-1) + (1/(p-1)) * sum_{chi != chi_0} tau(bar{chi}) * chi(t) * M(chi)
```

**Multiplicative Parseval** (Thm 5.6, line ~720):
```
sum_{chi != chi_0} |M(chi)|^2 = (p-1) * sum_{n!=0} N_n(p)^2 - (C-N_0)^2
```

**Parseval cost** (Thm 5.4, line ~626): If N_0(p) >= 1:
```
sum_{t=1}^{p-1} |T(t)|^2 >= (p-C)^2 / (p-1)
```
In crystalline regime (C << p), this is ~ p. So a solution forces large Fourier energy.

**Spectral concentration for Mersenne primes** (line ~2240):
- rho(M_q) -> 2^{-1/4} ~ 0.8409 as q -> infinity
- No moment-based bound can prove rho -> 0 for Mersenne primes
- This is a fundamental negative result for the exponential sums approach

### 3.3 Peeling lemma adaptation for character sums

The peeling lemma (Lem 6.2) works by fixing all but one variable and exploiting injectivity of 2^{A_{k-1}} mod p when ord_p(2) >= S.

**Adaptation potential**: The same variable-by-variable elimination could work for M(chi): fix (A_1,...,A_{k-2}), vary A_{k-1}. Then
```
M(chi) = sum_{partial} chi(C_partial + 2^{A_{k-1}})
```
where C_partial is the partial corrSum. The inner sum over A_{k-1} is a "twisted" character sum over powers of 2. If ord_p(2) >= S, these are S distinct elements, and incomplete character sum bounds (Polya-Vinogradov type) apply.

### 3.4 Results about ord_p(2)

- GRH implies ord_d(2) ~ d-1 for prime d (Hooley 1967, Artin's conjecture)
- Peeling requires ord_p(2) >= S (much weaker than Artin)
- Interior blocking requires ord_d(2) > C (stronger; C ~ 2^{0.95*S})
- Computational: for the 17 prime d with k in [3, 10000] where d-1 could be factored, (d-1)/ord_d(2) in {1, 2, 3, 15}
- **Regime A vs B**: defined by p < m^4 vs p >= m^4 where m = ord_p(2)
  - Regime A: Di Benedetto et al. (2020) gives rho <= C_1 * m^{-31/2880}
  - Regime B: only trivial bound rho <= 1 - 1/m
  - Empirically: 474/474 divisibility pairs are Regime A (0 Regime B)

---

## 4. CUMULATIVE ERROR APPROACH -- Extracted Ingredients

### 4.1 The ratio S/k and convergents of log_2(3)

**S = ceil(k * log_2(3))** (Notation 1.1, line ~218).

The fractional part theta = S - k*log_2(3) in [0,1) controls d:
```
d = 2^S - 3^k = 2^S(1 - 2^{-theta})
```
So log_2(d) = S + log_2(1 - 2^{-theta}).

For theta small (k near a convergent of log_2(3)), d is small relative to 2^S, which means the deficit between d and C shrinks. The paper handles this in Prop 3.4 (line ~406):
- If k is NOT a convergent: theta >= c/k, so log_2(d) >= S - O(log k)
- For convergents q_n: theta is small but alpha = (k-1)/(S-1) is closer to 1/log_2(3), improving the entropy bound

### 4.2 The three regimes (Remark 4.3, line ~552)

| Regime | Convergents | C/d | Elimination method |
|--------|------------|-----|-------------------|
| **Residual** | q_1=1, q_3=5 | >= 1 | Simons-de Weger (computational) |
| **Frontier** | q_5=41 | ~ 0.60 | Both methods (overlap zone [18,68]) |
| **Crystalline** | q_7=306, ... | << 1 | Nonsurjectivity (+ Hypothesis H) |

The convergents of log_2(3) = [1; 1, 1, 2, 2, 3, 1, 5, 2, 23, ...] give:
q_0=0, q_1=1, q_2=1, q_3=2, q_4=5, q_5=12, q_6=41 (?), q_7=53(?), ...

Note: The paper lists q_1=1, q_3=5, q_5=41, q_7=306 as the relevant convergents. The frontier regime at q_5=41 is in the overlap zone [18,68].

### 4.3 Connection d = 2^S - 3^k to convergents

The paper uses continued fraction theory in two places:
1. **Lean skeleton axiom**: CF lower bound for convergents of log_2(3) (Hardy & Wright S10.8)
2. **Asymptotic nonsurjectivity for k >= 666**: uses Legendre contrapositive for non-convergent ratios

The **epsilon(k) = O(log k)** error term in Prop 3.4 arises precisely from the Diophantine approximation quality. At convergents, theta ~ 1/q_{n+1}, so epsilon(q_n) ~ log(q_{n+1}).

---

## 5. STRUCTURAL RESULTS ABOUT d

### 5.1 Factorization and special forms
- d = 2^S - 3^k where S = ceil(k*log_2(3))
- d is always odd (since 2^S is even and 3^k is odd... wait, 2^S - 3^k: 2^S even, 3^k odd, so d is odd). Confirmed: d coprime to 6 (Notation 7.1).
- d > 0 for k >= 2 (since S = ceil(k*log_2(3)) > k*log_2(3), so 2^S > 3^k)
- d has the form 2^m - 1 when 3^k = 1 mod appropriate power... actually d = 2^S - 3^k is more general. But primes dividing d divide 2^S - 3^k, meaning 2^S = 3^k mod p, so 3^k is in <2> mod p iff n_3 | k.

### 5.2 Complete factorization data
- k in [18,67]: 190 prime factors found (127 small + 38 prime cofactors + 25 ECM primes)
- ALL 190 are Regime A (p < m^4)
- k in [69,150]: 284 additional pairs, all Regime A
- k in [69,200]: every prime factor satisfies p/m^4 < 0.087

### 5.3 The n_3 structure
For prime p: n_3(p) = min{j >= 1 : 3^j in <2> mod p}.
- p | d(k) forces n_3 | k (modular filter)
- If n_3 = (p-1)/m (generic case, 51% of observed instances): k_crit < n_3 for m >= 4, so no dangerous k exists
- For Mersenne primes: n_3(M_q) >= ceil(q/log_2(3)) ~ 0.631*q (Lem 8.4, structural bound)

---

## 6. OVERLOOKED CONNECTIONS BETWEEN SECTIONS

### 6.1 Peeling <-> Character sums
The peeling lemma (Sec 6) and the Mellin bridge (Sec 5) are essentially dual perspectives on the same structure. The peeling lemma bounds N_0(p) combinatorially by exploiting the injectivity of the last variable; the character sum approach bounds N_0(p) spectrally by bounding T(t). **A hybrid bound** -- using peeling to reduce the effective dimension from k-1 to k-2, then applying character sums to the remaining variables -- could yield stronger estimates. This is not pursued in the paper.

### 6.2 F_Z polynomial <-> Cumulative error
The integer F_Z = 4^m - 9^m - 17*6^{m-1} encodes the double-border obstruction. Its growth rate is dominated by 9^m = 3^{k-1}, while d ~ 2^S ~ 3^k * 2^theta. So |F_Z|/d ~ (9/3)^m / 2^theta ~ 3^{m-1}/2^theta. For theta small (convergents), d is small and |F_Z|/d could be large -- but the mod-8 analysis eliminates small quotients. **This connects the double-border case directly to the Diophantine approximation quality of log_2(3)**.

### 6.3 Interior closure failure <-> Spectral concentration
The computed failure rate of x2-closure (63% for k=18, converging to 1/log_2(3)) has the SAME limiting ratio as the peeling bound alpha = (k-1)/(S-1) -> 1/log_2(3). This is not coincidental: when B_{k-1} = M-1, shifting B+1 puts B_{k-1}+1 = M (right border), and the fraction of interior sequences with B_{k-1} = M-1 is exactly (k-1)/(S-1) by a stars-and-bars argument. **The interior closure failure is structurally linked to the peeling ratio**.

### 6.4 Conjecture M vs Theorem Q
Conjecture M asks for pointwise decay |T(t)| <= c*C*k^{-delta}. Theorem Q asks only for aggregate cancellation |sum T(t)| <= 0.041*C. The Mellin bridge shows that pointwise T(t) is controlled by Gauss sums and M(chi). But the aggregate sum cancellation could come from oscillation of chi(t) over t, even without pointwise decay. **Theorem Q is fundamentally weaker than Conjecture M**, and the right approach may be to prove cancellation in the sum directly rather than bounding individual T(t).

### 6.5 CRT anti-correlation <-> Additive energy
Remark 7.14 (line ~1638) notes that N_0(p_i) > 0 for all factors can still give N_0(d) = 0 due to CRT anti-correlation. This phenomenon is structurally similar to the additive energy constraint: the corrSum function has specific algebraic structure (geometric weights * powers of 2) that creates non-trivial correlations between residues mod different primes. **The additive energy E(<2>) = 2q^2 - q for Mersenne primes (Lem 8.3) quantifies exactly how constrained the image is**.

### 6.6 Shift identity <-> Multiplicative orbit
The shift identity g(B+1) = 2*g(B) mod d means the Horner image is organized into orbits under multiplication by 2. This is the SAME structure that appears in the exponential sum: the subgroup <2> mod p determines the spectral decomposition of T(t). **Any result about the size of <2>-orbits in Im(g) directly translates to bounds on the Fourier coefficients**.

---

## 7. CONJECTURAL OR INCOMPLETELY PROVED RESULTS

1. **Interior x2-closure (Conj 7.6)**: DISPROVED computationally. The paper acknowledges this gap explicitly (Rem 7.8). The blocking mechanism is incomplete here.

2. **Conjecture M** (Conj 6.4): Open. The multiplicative reformulation (Rem 6.8) requires |M(chi)| <= C^{1-epsilon}.

3. **Non-vanishing of F_Z mod d** beyond k=10001: Verified computationally only. Partial mod-8 argument eliminates quotients 1-4. Complete analytical proof open.

4. **Zsygmondy classification for composite d** (Prop 7.11): Proved only for prime d. The composite case relies on computation.

5. **Condition (2) of Theorem Q**: Not universally satisfied. Only 8/83 values in [18,100].

6. **Regime A universality**: Empirically 474/474, but not proved. The hypothesis that all prime factors of d(k) are Regime A is open.

7. **Three open conjectures** (line ~2348):
   - Horner equidistribution: |N_r(p) - C/p| <= C * p^{-1/2-delta}
   - Strong spectral gap: Delta_eff >= delta_1 * S/k
   - Uniform proportion (Conj PU): ordering constraint asymptotically independent of residue class

---

## 8. BIBLIOGRAPHY -- Relevant References for the Three Approaches

### For Alpha-Diophantine:
- **Laurent-Mignotte-Nesterenko (1995)**: Linear forms in two logarithms -- controls |2^S - 3^k| (used by Simons-de Weger)
- **Hardy-Wright (2008)**: Continued fraction theory, S10.8 -- convergent bounds
- **Zsygmondy (1892)**: Primitive divisors of a^n - b^n
- **Steiner (1977)**, **Crandall (1978)**: Original Steiner equation

### For Exponential Sums:
- **Bourgain-Glibichuk-Konyagin (2006)**: Sum-product estimates in F_p -- the key paper for closing Regime B; need effective constant c >= 0.36
- **Konyagin (2003)**: Character sum estimates for subgroups -- rho bound exp(-c*(log p)^{1/3}) for |H| >= p^{1/4+eps}
- **Di Benedetto et al. (2020)**: Bounds on ord_p(g) -- gives rho <= C_1 * m^{-31/2880} for Regime A
- **Hooley (1967)**: Artin's conjecture under GRH -- controls ord_d(2)

### For Cumulative Error:
- **Cover-Thomas (2006)**: Information theory, entropy bounds on binomial
- **Sos (1958)**: Distribution mod 1 of n*alpha (three-distance theorem, relevant to convergent structure)
- **Tao (2022)**: Almost all orbits -- probabilistic/ergodic methods

---

## 9. KEY QUANTITATIVE CONSTANTS

| Constant | Value | Where used |
|----------|-------|------------|
| gamma (entropic deficit) | 0.05004... | Nonsurjectivity threshold |
| alpha = 1/log_2(3) | 0.63093... | Peeling ratio, entropy |
| h(alpha) | 0.94996... | Shannon entropy at alpha |
| C/d critical threshold | k=18 first C < d | Junction overlap [18,68] |
| K_MAX | 63 | Max k_crit over all primes with ord <= 100 |
| rho(M_q) limit | 2^{-1/4} ~ 0.8409 | Spectral concentration barrier |
| c_min (Konyagin) | 0.3572 (at k=69) | Needed effective constant for BGK |
| Borel-Cantelli K_0 | 42 | sum_{k>=42} C/d < 1 |
| F_Z mod 5 | always 3 | 5 never divides F_Z |
| Critical primes | {11,37,53,59,109,191,283,8363} | Primes that can divide both F_Z and d |

---

## 10. SPECIFIC INGREDIENTS FOR EACH APPROACH

### Alpha-Diophantine: What to exploit
1. **F_Z = 4^m - 9^m - 17*6^{m-1}**: This is an explicit integer. The question d | F_Z is a pure Diophantine divisibility problem. Since |F_Z| ~ 9^m and d ~ 2^S ~ 3^k * 2^theta, the ratio |F_Z|/d ~ (9/3)^m / 2^theta = 3^m / 2^theta. For most k, theta ~ 1/k, so |F_Z|/d ~ 3^m * k. This grows, so eventually d cannot divide F_Z simply because |F_Z| < d... WAIT, that's wrong: 9^m > 3^k for m = (k-1)/2 iff 3^{k-1} > 3^k, which is false. Actually 9^m = 3^{2m} = 3^{k-1}, so |F_Z| ~ 3^{k-1} while d ~ 2^S - 3^k ~ 3^k * (2^theta - 1). So |F_Z|/d ~ 3^{k-1} / (3^k * theta * ln2) ~ 1/(3*theta*ln2). Since theta >= c/k typically, |F_Z|/d ~ k/(3c*ln2). For convergents, theta ~ 1/q_{n+1}, giving |F_Z|/d ~ q_{n+1}/(3*ln2). This can be large but finite. **The mod-8 argument gives structural constraints independent of size**.

2. **The identity u^k = 2^{-M} mod d** (line ~1433): Since u = 2/3 mod d and M = S-k, this says (2/3)^k = 2^{-(S-k)} = 2^{k-S} mod d. Equivalently 2^k * 3^{-k} = 2^{k-S}, i.e., 2^S = 3^k mod d, which is tautological. But the factored form u^k = 2^{-M} controls the degree of the annihilation polynomial.

3. **Zsygmondy's theorem** provides primitive divisors of 3^{k-1} - 2^{k-1} for k >= 9. Could be strengthened by ABC-type estimates on rad(3^{k-1} - 2^{k-1}) to bound the number of solutions to d | (3^{k-1} - 2^{k-1}).

### Exponential Sums: What to exploit
1. **The Mellin bridge decomposition** is already the right framework. The key unknowns are the sizes |M(chi)|.
2. **Parseval cost >= (p-C)^2/(p-1) ~ p** is a strong constraint: if a solution exists, the total Fourier energy is at least p, distributed over p-1 frequencies. On average, |T(t)|^2 >= p/(p-1) ~ 1. But we need more: we need the specific sum sum_t T(t) to be small.
3. **The observed decay rate ~ k^{-6.3}** for the ratio |p*N_0 - C|/C at p=7 is much faster than Conjecture M requires (polynomial decay). This suggests significant cancellation.
4. **The spectral concentration rho(M_q) -> 2^{-1/4}** is a HARD BARRIER for Mersenne primes. But the CRT bypass (Prop 8.3) means we never need to handle Mersenne primes directly -- only Regime A primes.

### Cumulative Error: What to exploit
1. **The three-regime structure** shows that the hardest cases are near convergents q_n of log_2(3). The "frontier" regime (k ~ 41) is where C/d ~ 0.6 -- nonsurjectivity holds but barely.
2. **The error epsilon(k) = O(log k)** versus the linear gain (S-1)*gamma means the deficit grows without bound. But the constant matters: for k near a convergent q_n with large partial quotient a_{n+1}, the error is ~ log(a_{n+1}), which can be large.
3. **Beatty sequences**: The condition ceil(k*theta) = S gives a Beatty-type structure. The values of k for which p | d(k) form a sub-sequence determined by 3^k mod p, which is controlled by the subgroup structure of <2> and <3> in F_p*.
4. **Baker-Matveev bounds** control |S*log2 - k*log3| but not the mod-p arithmetic. The paper explicitly notes this limitation (line ~2292).
