# R200 -- Agent A2 (INNOVATEUR DEDUCTIF) : New Cancellation Tools
**Date :** 16 mars 2026
**Round :** R200
**Role :** Innovateur Deductif -- inventer de nouveaux outils theoriques pour prouver N_0(p) = 0 sans p > C(k)
**Prerequis :** R199 (CRT blocked: no prime p | d(k) exceeds C(k) for k >= 18), R198 (architecture 4/10), R199 Red Team (structural impossibility of CRT+contraction)
**Mission :** Develop at least 3 new theoretical tools/approaches to prove N_0(p) = 0 for some prime p | d(k) WITHOUT requiring p > C(k)

---

## 0. EXECUTIVE SUMMARY

The R199 Red Team established a devastating fact: for k >= 18, EVERY prime factor p of d(k) = 2^S - 3^k satisfies p < C(k) = C(S-1, k-1). The standard Fourier/contraction argument gives N_0(p) = C/p + O(rho^{k-1}) which is >> 0 when p < C. We need fundamentally new ideas.

This document develops **8 theoretical tools** (Directions A-H), ranging from algebraic-structural to analytic-geometric. The most promising are:

1. **Tool C (Generating Function Nullstellensatz)** -- Feasibility 5/10 -- reformulates N_0(p) = 0 as a polynomial identity over F_p
2. **Tool E (Logarithmic Orbit Exclusion)** -- Feasibility 4/10 -- exploits the multiplicative structure of corrSum exponents
3. **Tool H (Monotone Cone Exclusion)** -- Feasibility 6/10 -- directly attacks the image of monotone compositions in F_p

**Honest assessment:** None of these tools is ready to close the gap. Each represents a genuine new angle, but each faces serious obstacles. The problem of proving N_0(p) = 0 for p < C appears to be of comparable difficulty to major open problems in additive combinatorics.

---

## 1. TOOL A: ALGEBRAIC STRUCTURE OF corrSum OVER F_p

### 1.1 Concept

The corrSum is a LINEAR FORM over F_p:

corrSum(A) = sum_{j=1}^{k} 3^{k-1-j} * 2^{a_j} mod p

where A = (a_1 < a_2 < ... < a_k = S) is admissible. Since p | d(k), we have the algebraic constraint 2^S = 3^k mod p. Write q = ord_p(2), r = ord_p(3). Then q | S (from 2^S = 3^k and 3^k in <2>) and r | k.

Define alpha = 2 mod p, beta = 3 mod p. Then beta = alpha^L where L = log_2(3) mod q (the discrete logarithm).

corrSum(A) = sum_j alpha^{L(k-1-j) + a_j} = sum_j alpha^{e_j}

where e_j = a_j + L(k-1-j) mod q.

### 1.2 The Effective Exponents

The "effective exponent" of the j-th term is:

e_j = a_j + L(k-1-j) mod q

The constraint a_k = S gives e_k = S + 0 = S = 0 mod q (since 2^S = 1 * 3^k and q | S in the Mersenne case; more precisely, S*1 = k*L mod q from 2^S = 3^k = alpha^{kL}).

Wait -- let me be precise. We have alpha^S = beta^k = alpha^{kL}, so S = kL mod q. Therefore:

e_k = a_k + L(k-1-k) = S - L = kL - L = (k-1)L mod q

And for general j:

e_j = a_j + L(k-1-j) mod q

### 1.3 What This Would Prove

**Claim (Tool A).** If the set {e_1, ..., e_k} mod q, ranging over all admissible A, never produces sum_{j=1}^k alpha^{e_j} = 0 mod p, then N_0(p) = 0.

This is a RESTATEMENT of the problem in multiplicative language over F_p. The question becomes: can k powers of alpha (with specific constraints on the exponents) sum to 0?

### 1.4 Structure of Exponent Constraints

The exponents e_j = a_j + L(k-1-j) are constrained by:
- a_1 < a_2 < ... < a_k = S (monotonicity)
- a_j >= j (each a_j is at least j)
- sum a_j = S (from the definition: total of S even steps distributed among k groups)

Wait -- actually a_j are CUMULATIVE sums: a_j = s_1 + ... + s_j where s_i >= 1 are the even steps in each group. So a_j >= j and a_k = S, with a_1 < a_2 < ... < a_k.

The map j -> e_j = a_j + L(k-1-j) transforms the monotone sequence (a_j) by adding a DECREASING arithmetic progression L(k-1-j). The result may or may not be monotone, depending on whether the "slope" of (a_j) exceeds L (the discrete log of 3 base 2 in F_q).

### 1.5 Obstacles

1. **The restatement does not obviously simplify.** We have replaced "corrSum = 0 mod p" with "sum of k specific powers of alpha = 0 mod p." The latter is a standard problem in additive combinatorics over F_p, and these problems are generally HARD.

2. **The constraint set is complex.** The monotonicity + boundary conditions on (a_j) make the exponent set (e_j) highly structured but hard to analyze.

3. **For small q = ord_p(2),** the exponents wrap around mod q, creating many collisions. When q is small (say q = 3 for p = 7), the sum of k terms from {alpha^0, alpha^1, alpha^2} = {1, 2, 4} mod 7 can easily be 0.

**Feasibility: 3/10.** This is a reformulation, not a solution. It might help if combined with Tools C or E.

---

## 2. TOOL B: p-ADIC VALUATION APPROACH

### 2.1 Concept

Work in Q_p instead of F_p. The corrSum is an INTEGER:

corrSum(A) = sum_{j=1}^k 3^{k-1-j} * 2^{a_j}

This is a positive integer (all terms are positive). The question N_0(p) = 0 becomes: does p divide corrSum(A) for any admissible A?

In p-adic terms: is v_p(corrSum(A)) >= 1 possible?

### 2.2 Lower Bound on corrSum

The minimum value of corrSum over admissible A occurs when a_j = j for j = 1, ..., k-1 and a_k = S:

corrSum_min = sum_{j=1}^{k-1} 3^{k-1-j} * 2^j + 2^S
            = sum_{j=1}^{k-1} (2/3)^j * 3^{k-1} + 2^S

For large k, corrSum_min ~ 3^{k-1} * (2/3) / (1 - 2/3) + 2^S = 2 * 3^{k-2} + 2^S ~ 2^S (since 2^S ~ 3^k >> 3^{k-2}).

The maximum value:

corrSum_max occurs when a_1 = S - k + 1, a_2 = S - k + 2, ..., a_k = S:

corrSum_max = sum_{j=1}^k 3^{k-1-j} * 2^{S-k+j}
            = 2^{S-k} * sum_{j=1}^k (2/3)^j * 3^{k-1} * ...

Actually, let me recompute. If a_j = S - k + j:

corrSum_max = sum_{j=1}^k 3^{k-1-j} * 2^{S-k+j}
            = 2^{S-k} * sum_{j=1}^k 3^{k-1-j} * 2^j
            = 2^{S-k} * 3^{k-1} * sum_{j=1}^k (2/3)^j
            = 2^{S-k} * 3^{k-1} * (2/3) * (1 - (2/3)^k) / (1 - 2/3)
            = 2^{S-k} * 3^{k-1} * 2 * (1 - (2/3)^k)
            = 2^{S-k+1} * (3^{k-1} - 2^k/3)
            ~ 2^{S-k+1} * 3^{k-1}

### 2.3 The p-adic Approach

For p | d = 2^S - 3^k, we know v_p(2^S - 3^k) >= 1. Write 2^S = 3^k + d with v_p(d) >= 1.

Substitute into corrSum using the fact that the last term is 2^S = 3^k + d:

corrSum(A) = sum_{j=1}^{k-1} 3^{k-1-j} * 2^{a_j} + 2^S
           = sum_{j=1}^{k-1} 3^{k-1-j} * 2^{a_j} + 3^k + d

Therefore:

corrSum(A) = 3^k + d + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{a_j}

Modulo p (since p | d):

corrSum(A) = 3^k + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{a_j} mod p

This is the "reduced corrSum" which does NOT depend on d. It depends on the first k-1 positions a_1, ..., a_{k-1} (with 1 <= a_1 < ... < a_{k-1} < S).

### 2.4 The Reduced Problem

Define:

G(A') = 3^k + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{a_j}

where A' = (a_1, ..., a_{k-1}) with 1 <= a_1 < ... < a_{k-1} < S = ceil(k * log_2(3)).

Then N_0(p) = #{A' : G(A') = 0 mod p}.

Note: G(A') = 3^k + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{a_j} is a SUM of k positive terms:
- The constant term 3^k
- The k-1 variable terms 3^{k-1-j} * 2^{a_j}

### 2.5 p-adic Valuation Strategy

For G(A') = 0 mod p, we need:

3^k + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{a_j} = 0 mod p

Since p does not divide 3 (because d = 2^S - 3^k and 3 | d would require 3 | 2^S, impossible), we can divide by 3^{k-1}:

3 + sum_{j=1}^{k-1} 3^{-j} * 2^{a_j} = 0 mod p

i.e., 3 + sum_{j=1}^{k-1} (2^{a_j} / 3^j) = 0 mod p

Using 2/3 mod p = 2 * 3^{-1} mod p, this becomes:

3 + sum_{j=1}^{k-1} (2/3)^{a_j} * 3^{a_j - j} = 0 mod p

Hmm, this doesn't simplify cleanly because a_j and j are different.

### 2.6 Alternative: Horner-like Structure

There is a well-known Horner representation of corrSum. Given the step sequence s_1, ..., s_k (with s_j >= 1, sum s_j = S), the corrSum satisfies:

corrSum = 2^{s_k} * (2^{s_{k-1}} * (... (2^{s_1} * 0 + 3^{k-1}) + 3^{k-2} ...) + 3^0)

More precisely, define the ITERATIVE corrSum:

C_0 = 0
C_j = 2^{s_j} * C_{j-1} + 3^{k-j}  for j = 1, ..., k

Then corrSum = C_k.

This is a COMPOSITION of affine maps x -> 2^{s_j} * x + 3^{k-j}, applied left to right. Each map is x -> 2^{s_j} x + 3^{k-j} in F_p.

### 2.7 p-adic Analysis of the Composition

In Q_p, each affine map f_j(x) = 2^{s_j} * x + 3^{k-j} has:
- Contraction factor |2^{s_j}|_p = 1 (since p is odd and p does not divide 2)
- Translation 3^{k-j} with |3^{k-j}|_p = 1 (since p does not divide 3)

Therefore the composition is an ISOMETRY of Q_p, not a contraction. The p-adic approach gives no extra leverage because the map preserves p-adic distances.

### 2.8 Verdict

The p-adic approach does NOT help because the affine maps are isometries in Q_p (since p does not divide 2 or 3). The distribution of corrSum mod p is controlled by the ALGEBRAIC structure of the composition, not by p-adic contraction.

**Feasibility: 2/10.** The p-adic structure is too uniform (isometric) to provide cancellation.

---

## 3. TOOL C: GENERATING FUNCTION / POLYNOMIAL NULLSTELLENSATZ

### 3.1 Concept

Define the generating polynomial over F_p:

Phi(x) = sum_{A admissible} x^{corrSum(A) mod p}

More precisely, using the discrete Fourier transform, for omega = primitive p-th root of unity:

N_0(p) = (1/p) * sum_{t=0}^{p-1} F(omega^t)

where F(z) = sum_{A admissible} z^{corrSum(A)}.

The key identity: F(z) factors due to the PRODUCT structure of the step choices.

### 3.2 Factored Form

Using the Horner structure C_j = 2^{s_j} * C_{j-1} + 3^{k-j}, the generating function for corrSum tracks the partial sums C_j as s_j ranges over {1, 2, ..., S - k + 1 - (already used)}.

Actually, the factorization is more subtle because the choices s_1, ..., s_k are NOT independent (they must satisfy sum s_j = S and s_j >= 1). But we can use the COMPOSITION variable a_j = s_1 + ... + s_j.

The admissible set is {A = (a_1, ..., a_k) : 1 <= a_1 < a_2 < ... < a_k = S}, which is in bijection with the set of (k-1)-element subsets of {1, 2, ..., S-1} (the positions a_1, ..., a_{k-1}).

### 3.3 The Key Polynomial

Define, for t in F_p*:

T(t) = sum_{A admissible} omega^{t * corrSum(A)}

where omega = e^{2*pi*i/p}. Then:

T(t) = sum_{1 <= a_1 < ... < a_{k-1} < S} omega^{t * G(a_1, ..., a_{k-1})}

where G(A') = 3^k + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{a_j} (from Section 2.4).

Factor out the constant:

T(t) = omega^{t * 3^k} * sum_{1 <= a_1 < ... < a_{k-1} < S} prod_{j=1}^{k-1} omega^{t * 3^{k-1-j} * 2^{a_j}}

### 3.4 Product Form

Since the a_j are DISTINCT elements of {1, ..., S-1}, the sum over subsets factorizes:

T(t) = omega^{t * 3^k} * sum_{B subset {1,...,S-1}, |B|=k-1} prod_{b in B} omega^{t * w(b)}

where the WEIGHT function w(b) depends on which position j the element b occupies.

**CRITICAL ISSUE:** The weight w(b) depends on the RANK of b within the ordered subset B. Specifically, if b is the j-th smallest element of B, then its weight is 3^{k-1-j} * 2^b. Since the weight depends on the rank, the sum does NOT factor into independent products.

This is the fundamental obstruction to a clean product formula. The weights couple the choices.

### 3.5 Rank-Independent Reformulation

What if we could decouple the rank? Define:

gamma_b = 2^b mod p (for b = 1, ..., S-1)

If the weight were simply 2^{a_j} (ignoring the 3^{k-1-j} factor), then:

T(t) = omega^{t * 3^k} * e_{k-1}(omega^{t*gamma_1}, ..., omega^{t*gamma_{S-1}})

where e_{k-1} is the (k-1)-th elementary symmetric polynomial. This WOULD factor via the generating polynomial:

prod_{b=1}^{S-1} (1 + x * omega^{t*gamma_b}) = sum_{m=0}^{S-1} e_m(...) * x^m

and T(t) would be the coefficient of x^{k-1} times omega^{t*3^k}.

But the 3^{k-1-j} factor BREAKS this factorization because the coefficient depends on which elements are chosen AND their relative order.

### 3.6 A Partial Factorization via Iterated Sums

Consider the Horner iteration C_j = 2^{s_j} C_{j-1} + 3^{k-j}. View this as choosing s_j in {1, ..., R_j} where R_j = S - (k - j) - (a_{j-1}) (remaining budget). The transfer matrix for step j is:

M_j(t) = sum_{s=1}^{R_j} omega^{t * 3^{k-j}} * (omega^{t * ...})^{2^s}

This is a sum of powers of omega, and the composition of the k steps gives T(t) as a product-like object. But the variable ranges R_j depend on previous choices, preventing a clean product.

### 3.7 What This Would Prove (If It Worked)

**Claim (Tool C -- aspirational).** If we can express T(t) as a product of k terms, each involving a sum over a bounded range, then |T(t)| can be bounded by the product of k individual sums. Each individual sum is a GEOMETRIC sum or KLOOSTERMAN-like sum, and for p | d(k), the specific algebraic relation 2^S = 3^k mod p forces cancellation in each factor.

The product bound would give |T(t)| <= prod_j |factor_j|, and if each factor is < p^{1/2} (by Weil's bound on character sums), then |T(t)| < p^{k/2}. For N_0(p) = 0, we need |T(t)| < C/(p-1), i.e., p^{k/2} < C(S-1,k-1)/(p-1).

Since C ~ (S-1)^{k-1} / (k-1)! and S ~ k*log_2(3) ~ 1.585k, we get C ~ (1.585k)^{k-1}/(k-1)!. By Stirling, C ~ (1.585 * e)^{k-1} / sqrt(k) ~ 4.31^{k-1} / sqrt(k).

We need p^{k/2} < 4.31^{k-1}/sqrt(k), i.e., p < 4.31^{2(k-1)/k} / k^{1/k} ~ 4.31^2 ~ 18.6 for large k.

**This means:** if the Weil-type bound applies, we can only handle primes p <= 18. This is EXACTLY the small-prime regime (Etage 1)! The Weil bound would give an ALTERNATIVE proof of Etage 1, but would NOT extend to larger primes.

### 3.8 Beyond Weil: The Need for EXACT Cancellation

For p > 18, we cannot rely on generic bounds on character sums. We need the SPECIFIC algebraic constraint 2^S = 3^k mod p to force ADDITIONAL cancellation beyond what Weil provides.

**Key Observation:** When 2^S = 3^k mod p, the weights 3^{k-1-j} * 2^{a_j} satisfy:

3^{k-1-j} * 2^{a_j} = 2^{L(k-1-j) + a_j} mod p

where L is the discrete log of 3 base 2 mod p (with respect to the cyclic group <2> of order q in F_p*).

The effective exponents e_j = L(k-1-j) + a_j lie in Z/qZ. The constraint a_k = S = kL mod q gives e_k = (k-1)L, as computed in Tool A.

For corrSum = 0 mod p, we need:

sum_{j=1}^k 2^{e_j} = 0 mod p

where e_j = a_j + L(k-1-j) mod q, with a_1 < a_2 < ... < a_k = S.

This is a SUM OF POWERS OF A PRIMITIVE ROOT problem with structured exponents.

### 3.9 Obstacles and Feasibility

1. **The rank-dependent weights prevent clean factorization.** This is the main technical obstacle.
2. **The Weil bound gives p < ~18, insufficient for the problem.**
3. **Exact cancellation requires understanding the arithmetic of e_j mod q for specific p.**
4. **The problem resembles zero-sum theory over F_p** (Davenport constant, etc.), but with additional structure.

**Feasibility: 5/10.** The polynomial viewpoint is the most structured approach. The Weil bound limitation is disappointing but honest. The path forward would require a STRUCTURAL result about sums of powers with monotone-constrained exponents, which is novel in additive combinatorics.

---

## 4. TOOL D: SYMMETRY BREAKING

### 4.1 Concept

The admissible set Comp(S, k) = {A : 1 <= a_1 < ... < a_k = S} has C = C(S-1, k-1) elements. Without the constraint a_k = S, the set would be all (k)-element subsets of {1, ..., S}, which has the SYMMETRIC GROUP S_S acting on it. The constraint a_k = S breaks this symmetry.

The corrSum function corrSum(A) = sum_j 3^{k-1-j} * 2^{a_j} is NOT symmetric in the a_j because of the weights 3^{k-1-j}. So even without the constraint a_k = S, the function is asymmetric.

### 4.2 The "Bias" Phenomenon

Experimentally (from preprint data), the distribution of corrSum mod p is NOT uniform. It concentrates away from 0 for certain primes. Can we prove this concentration?

The AVERAGE of corrSum over all admissible A is:

E[corrSum] = sum_{j=1}^k 3^{k-1-j} * E[2^{a_j}]

By symmetry of the uniform distribution on (k-1)-element subsets of {1,...,S-1} (for the first k-1 positions):

E[2^{a_j}] for the j-th order statistic of a (k-1)-element subset of {1,...,S-1} with the additional constraint a_k = S...

This is getting complicated. The point is that E[corrSum] is a specific nonzero value, and we want to show the distribution is tightly concentrated around this value (in the sense that it avoids 0 mod p).

### 4.3 Variance Analysis

The variance of corrSum mod p could be computed as:

Var(corrSum) = E[corrSum^2] - E[corrSum]^2

If the standard deviation is much smaller than p, then the distribution is concentrated in a small arc of Z/pZ, potentially avoiding 0. But for p < C, the distribution wraps around Z/pZ many times, so concentration arguments in R do not directly translate to concentration in Z/pZ.

### 4.4 What Symmetry Breaking Could Prove

**Claim (Tool D -- weak form).** If E[corrSum] mod p is far from 0 and the "effective spread" of corrSum mod p is less than p/2, then N_0(p) = 0.

The effective spread is related to the circular variance of the distribution on Z/pZ. This is a STRONG condition that is unlikely to hold for all p.

### 4.5 Obstacles

1. **Circular concentration does not follow from linear concentration.** The distribution of corrSum mod p wraps around, destroying any linear concentration.
2. **For p < C, the distribution covers Z/pZ many times.** Each residue class gets approximately C/p elements.
3. **The "bias" is real but weak.** The mean of corrSum is nonzero but much larger than p, so its residue mod p is essentially random.

**Feasibility: 2/10.** Symmetry breaking provides intuition but not proofs. The circular nature of residues modulo p defeats linear concentration arguments.

---

## 5. TOOL E: LOGARITHMIC ORBIT EXCLUSION (LOE)

### 5.1 Concept

This is the most novel tool. It combines the algebraic structure (Tool A) with a dynamical systems perspective.

Recall from Tool A: corrSum = sum_j alpha^{e_j} where e_j = a_j + L(k-1-j) mod q, and q = ord_p(2), L = log_2(3) mod q.

The key insight: the sequence e_1, e_2, ..., e_k is obtained from the monotone sequence a_1 < a_2 < ... < a_k by adding a DECREASING arithmetic progression L(k-1), L(k-2), ..., L*0.

The "slope" of the arithmetic progression is -L per step, while the monotone sequence (a_j) increases by at least 1 per step. So:

e_{j+1} - e_j = (a_{j+1} - a_j) - L >= 1 - L mod q

### 5.2 The Orbit Picture

Think of the exponents e_j as points on the "clock" Z/qZ. Starting from e_1 = a_1 + L(k-1), each subsequent exponent is obtained by:

e_{j+1} = e_j + (a_{j+1} - a_j) - L

where a_{j+1} - a_j >= 1 (the gap). So the successive differences e_{j+1} - e_j are in {1-L, 2-L, 3-L, ...} mod q.

The sequence (e_j) traces a PATH on the cycle Z/qZ with steps of size >= 1-L. If L is close to 1 (which happens when log_2(3) ~ 1.585 is close to L/q * q), then the minimum step is close to 0, and the path can be nearly stationary.

But if L is NOT close to 1 mod q (i.e., the discrete log of 3 differs from 1), the path has a strong DRIFT, and the exponents e_j are spread out on Z/qZ.

### 5.3 The Sum-Zero Condition

For corrSum = 0 mod p, we need sum_j alpha^{e_j} = 0 in F_p. If the exponents e_j are WELL-DISTRIBUTED on Z/qZ, then the sum is an exponential sum that tends to cancel out (be small), and in particular has a hard time being EXACTLY 0.

Conversely, if the exponents cluster on a small arc of Z/qZ, the sum is close to k * alpha^{e_avg}, which is nonzero.

**The dichotomy:** Either the exponents are spread (sum cancels to something small but not 0) or clustered (sum is large and nonzero). In BOTH cases, the sum avoids 0.

### 5.4 Formalization Attempt

**Proposition (LOE -- aspirational).** Let p | d(k) with q = ord_p(2) >= q_0. Let alpha be a primitive q-th root of unity in F_p. Let L = log_2(3) mod q. Suppose the exponents e_j = a_j + L(k-1-j) mod q satisfy:

(a) SPREAD condition: max_r #{j : e_j = r} <= k/q + epsilon, OR
(b) CLUSTER condition: there exists r_0 such that #{j : e_j in [r_0, r_0 + q/3]} >= 2k/3.

Then |sum_j alpha^{e_j}| >= c(k, q) > 0 for an explicit constant c.

**Case (a):** If the exponents are well-distributed, the sum is an exponential sum over a well-distributed set. By the large sieve inequality:

|sum_j alpha^{e_j}|^2 <= k * max_r #{j : e_j = r} <= k * (k/q + epsilon)

Hmm, this gives an UPPER bound on |sum|, not a lower bound. The large sieve goes the wrong way!

**Case (b):** If the exponents cluster, then sum ~ k * alpha^{r_0} (since most terms are close to alpha^{r_0}). This gives |sum| ~ k, which is nonzero. But we need to show it's nonzero mod p, not just nonzero as a complex number.

### 5.5 The Critical Difficulty

The transition between cases (a) and (b) is not sharp, and in the intermediate regime, the sum COULD be close to 0. More fundamentally:

- We need |sum| != 0 in F_p, not in C
- Even if the complex magnitude is nonzero, the sum could be 0 in F_p
- The large sieve gives UPPER bounds on |sum|, not lower bounds
- Lower bounds on exponential sums are MUCH harder than upper bounds

### 5.6 A Hopeful Special Case

For q PRIME and L a primitive root mod q, the exponents e_j cycle through all residues mod q as the a_j range. In this case:

- The k exponents e_1, ..., e_k are a SUBSET of Z/qZ
- If k < q, the subset has missing elements
- The sum alpha^{e_1} + ... + alpha^{e_k} is a partial sum of roots of unity
- By the Chebotarev-type result (or Vinogradov's bound), such partial sums satisfy |sum| >= 1 when the subset is "generic"

But "generic" is not guaranteed here. The subset is constrained by the monotonicity of (a_j).

### 5.7 Connection to the Erdos-Ginzburg-Ziv Theorem

The Erdos-Ginzburg-Ziv (EGZ) theorem states: any 2p-1 integers contain a p-element subset summing to 0 mod p. The INVERSE problem: when do n < 2p-1 integers fail to contain a p-element zero-sum subset?

Our problem is related but different: we have k elements of F_p* (the powers alpha^{e_j}), and we ask whether their SUM (not a subset sum) is 0. The EGZ machinery does not directly apply.

However, the Davenport constant D(Z/pZ) = p, meaning that any sequence of p elements of Z/pZ contains a nonempty subsequence summing to 0. But we are summing ALL k elements, not a subsequence. This is simpler but also harder to control: the full sum is a SINGLE value, and we need it to be nonzero.

### 5.8 Obstacles

1. **Lower bounds on exponential sums are extremely hard.** There is no general technique for proving |sum of roots of unity| > 0.
2. **The large sieve and other tools give UPPER bounds, not lower bounds.**
3. **The monotonicity constraint is hard to exploit analytically.**
4. **For small q, the exponents have many collisions, making the sum predictable but not necessarily nonzero.**

**Feasibility: 4/10.** The orbit picture is genuinely new and provides intuition. The main obstacle is that lower bounds on exponential sums are a known hard problem. A breakthrough here would have implications beyond Collatz.

---

## 6. TOOL F: EXACT CANCELLATION / REPRESENTATION THEORY

### 6.1 Concept

Instead of bounding |T(t)| for individual t, study the FULL Fourier decomposition:

N_0(p) = (1/p) * sum_{t=0}^{p-1} T(t) = C/p + (1/p) * sum_{t=1}^{p-1} T(t)

We want N_0(p) = 0, which requires:

sum_{t=1}^{p-1} T(t) = -C

This is an EXACT equation. Can the algebraic structure of the problem force this?

### 6.2 Representation-Theoretic Reformulation

The sum sum_{t=1}^{p-1} T(t) can be written as:

sum_{t=1}^{p-1} T(t) = sum_{t=1}^{p-1} sum_{A} omega^{t * corrSum(A)}
                      = sum_A sum_{t=1}^{p-1} omega^{t * corrSum(A)}
                      = sum_A (p * [corrSum(A) = 0 mod p] - 1)
                      = p * N_0(p) - C

So sum_{t=1}^{p-1} T(t) = p * N_0(p) - C. For N_0(p) = 0, we need sum = -C. This is TAUTOLOGICAL -- it restates N_0(p) = 0.

### 6.3 A Non-Tautological Approach: Character Sums over the Group

Consider the action of the multiplicative group (Z/pZ)* on the set of corrSum values. For each character chi of (Z/pZ)*, define:

S(chi) = sum_{A admissible} chi(corrSum(A))

Then by character orthogonality:

N_0(p) + N_1(p) + ... = C (total)

and for each r in F_p*:

N_r(p) = (1/(p-1)) * sum_{chi} bar{chi}(r) * S(chi)

The question N_0(p) = 0 requires special treatment because the trivial character does not distinguish residue 0 from nonzero residues. But:

C - N_0(p) = sum_{r != 0} N_r(p) = (1/(p-1)) * sum_{chi} S(chi) * sum_{r != 0} bar{chi}(r) = ...

Only the trivial character chi_0 contributes to sum_{r != 0} bar{chi_0}(r) = p - 1. So:

sum_{r != 0} N_r(p) = C

Wait, that's just C - N_0(p). This is circular again.

### 6.4 A Deeper Angle: Gauss Sums and Jacobi Sums

For p | d(k), the relation 2^S = 3^k mod p connects the Gauss sums g(chi, 2) and g(chi, 3). Specifically, for a multiplicative character chi of order dividing q = ord_p(2):

chi(2^S) = chi(3^k) implies chi(2)^S = chi(3)^k

Since chi(2) is a q-th root of unity and chi(3) = chi(2)^L, we get:

chi(2)^S = chi(2)^{kL}

which gives S = kL mod q. This is the same constraint as before (Section 1.2). No new information.

### 6.5 The Jacobi Sum Connection

The corrSum involves PRODUCTS of powers of 2 and 3. The Jacobi sum J(chi, psi) = sum_{a+b=1} chi(a)*psi(b) relates to products. But our sum is of the form sum alpha^{e_j}, not a Jacobi sum.

However, consider the MODIFIED sum:

S_m = sum_{A admissible} chi_m(corrSum(A))

where chi_m is the character chi_m(x) = (x/p)^m (Legendre symbol to the m-th power, or equivalently, the m-th power of a generator of the character group).

For m = (p-1)/2 (the Legendre symbol):

S_{Legendre} = sum_A (corrSum(A) / p)

This counts the QUADRATIC CHARACTER of corrSum. If we could show that all corrSum(A) are quadratic residues (or all non-residues), then the sum would be C or -C, and N_0(p) = 0 would follow from the distribution being one-sided.

### 6.6 Quadratic Residue Approach

**Claim (Tool F -- aspirational).** If for a prime p | d(k), every admissible corrSum(A) is a quadratic residue mod p, then N_0(p) = 0.

**Proof sketch:** If corrSum(A) is always a QR, then corrSum(A) never equals 0 (since 0 is neither QR nor QNR). Hence N_0(p) = 0. QED.

**The question is:** can we prove that corrSum is always a QR for specific p?

The corrSum is a sum of k terms, each of the form 3^{k-1-j} * 2^{a_j}. Each term is 2^{a_j} * 3^{k-1-j}. The QR character of the product:

(3^{k-1-j} * 2^{a_j} / p) = (3/p)^{k-1-j} * (2/p)^{a_j}

By QR, a SUM of QR need not be QR. So this approach does not directly work.

### 6.7 Obstacles

1. **The representation-theoretic reformulation is tautological at the additive level.**
2. **The Gauss/Jacobi sum machinery gives constraints between characters but not directly on N_0.**
3. **The QR approach fails because sums of QR are not necessarily QR.**
4. **There is no known "exact cancellation mechanism" for sums of roots of unity over structured index sets.**

**Feasibility: 3/10.** The representation theory provides a rich language but the specific problem structure (sum of rank-weighted powers with monotonicity constraint) does not align with known character sum identities.

---

## 7. TOOL G: ALGEBRAIC GEOMETRY / WEIL CONJECTURES

### 7.1 Concept

Reinterpret the counting problem N_0(p) as a point-counting problem on an algebraic variety over F_p, then apply Weil's theorem (Deligne's proof).

### 7.2 The Variety

The corrSum = 0 condition is:

sum_{j=1}^k 3^{k-1-j} * 2^{a_j} = 0 mod p

with the constraints 1 <= a_1 < a_2 < ... < a_k = S on the INTEGER variables a_j.

To make this an algebraic variety, introduce variables x_j = 2^{a_j} in F_p*. Then:

sum_j 3^{k-1-j} * x_j = 0

with the constraint that each x_j is a POWER OF 2, and the exponents satisfy monotonicity and a_k = S (so x_k = 2^S = 3^k mod p).

The equation sum_j 3^{k-1-j} * x_j = 0 defines a HYPERPLANE in (F_p*)^k. The constraint x_j in <2> = {2^0, 2^1, ..., 2^{q-1}} and x_k = 3^k restricts the variety to a SUBVARIETY.

### 7.3 Intersection of Hyperplane with Structured Set

The number of points is:

N_0(p) = #{(a_1, ..., a_{k-1}) in Z^{k-1} : 1 <= a_1 < ... < a_{k-1} < S, sum_j 3^{k-1-j} * 2^{a_j} = 0 mod p, a_k = S}

This is the intersection of a HYPERPLANE in (F_p)^k with a highly structured subset (the image of the monotone lattice under the exponential map a -> 2^a).

### 7.4 Why Weil Might Apply

If we could express N_0(p) as the number of F_p-rational points on a smooth projective variety V/F_p, then by Weil-Deligne:

|N_0(p) - p^{dim V}| <= b * p^{(dim V - 1)/2}

where b is the sum of Betti numbers. For dim V = k-2 (the hyperplane in the (k-1)-dimensional parameter space), this would give:

|N_0(p) - p^{k-2}| <= b * p^{(k-3)/2}

For N_0(p) = 0, we need p^{k-2} < b * p^{(k-3)/2}, i.e., p^{(k-1)/2} < b. Since b ~ O(1) for a hyperplane, this requires p < O(1), which is USELESS.

### 7.5 The Problem with Weil

The Weil bounds give APPROXIMATE point counts with error terms proportional to sqrt(p)^{dim}. For N_0(p) = 0, we need the point count to be EXACTLY 0, which requires the main term to be 0 AND the error term to be 0. The Weil bound cannot achieve this.

The only case where Weil gives EXACT results is when the variety has NO points for structural reasons (e.g., the variety is empty over the algebraic closure). But our hyperplane always has points over the algebraic closure.

### 7.6 Alternative: Exponential Sums over Finite Fields

The more appropriate tool is the EXPONENTIAL SUM framework. The sum T(t) = sum_A omega^{t*corrSum(A)} is an exponential sum. Deligne's theorem bounds:

|sum_{x in V(F_p)} psi(f(x))| <= (deg f - 1) * p^{dim V / 2}

for a polynomial f on a variety V. But our sum is over a DISCRETE set (monotone tuples), not a variety, so Deligne's theorem does not directly apply.

### 7.7 Obstacles

1. **The monotone constraint is combinatorial, not algebraic.** There is no algebraic variety whose F_p-points are exactly the monotone tuples.
2. **Weil bounds give approximate counts, not exact results.**
3. **Deligne's exponential sum bounds apply to sums over algebraic varieties, not over combinatorial sets.**
4. **The dimension of the parameter space (k-1) grows with k, making Weil-type bounds progressively weaker.**

**Feasibility: 2/10.** The algebraic geometry approach is a MISMATCH with the combinatorial nature of the monotone constraint. It would require a breakthrough in "algebraic combinatorics over finite fields" to bridge this gap.

---

## 8. TOOL H: MONOTONE CONE EXCLUSION (MCE-Alg)

### 8.1 Concept (The Most Promising Direction)

Attack N_0(p) = 0 DIRECTLY by studying the IMAGE of the monotone set in F_p.

Define the MAP:

Phi: Comp(S, k) -> F_p
Phi(A) = corrSum(A) mod p

The set Im(Phi) = {corrSum(A) mod p : A admissible} is a SUBSET of F_p. If 0 is not in Im(Phi), then N_0(p) = 0.

Since |Comp(S, k)| = C = C(S-1, k-1) and |F_p| = p, and C >> p for k >= 18, the map Phi is MANY-TO-ONE. The image Im(Phi) could be as small as 1 (if all corrSums are congruent mod p) or as large as min(C, p) = p.

### 8.2 The Key Question

Is Im(Phi) = F_p (surjective), or does Im(Phi) miss some elements (including 0)?

If Im(Phi) is a PROPER subset of F_p, then there exist residues not represented, and 0 MIGHT be among them. If Im(Phi) = F_p, then N_0(p) > 0 and this approach fails.

### 8.3 Surjectivity Analysis

For GENERIC linear forms over F_p evaluated on large subsets of F_p^n, surjectivity is expected when the subset is large enough. Specifically, if we have C >> p elements mapping to F_p, and the distribution is "spread out," then surjectivity is expected.

**Counter-argument:** The corrSum is NOT a generic linear form. It has specific coefficients 3^{k-1-j} * 2^{a_j} with algebraic relations. The constraint 2^S = 3^k mod p creates DEPENDENCIES that could prevent surjectivity.

### 8.4 The Cone Structure

The admissible tuples (a_1, ..., a_k) form a SIMPLEX in R^k:

Delta = {(a_1, ..., a_k) : 1 <= a_1 < a_2 < ... < a_k = S, a_j in Z}

This is an integer polytope of dimension k-1 (since a_k = S is fixed). The corrSum is a LINEAR FUNCTION on this polytope:

corrSum(a_1, ..., a_k) = sum_j w_j * 2^{a_j}

where w_j = 3^{k-1-j}. The image of the integer points of Delta under this linear function is a set of integers in [corrSum_min, corrSum_max].

### 8.5 Image Gaps in Z

In Z, the image of corrSum might have GAPS: not every integer in [corrSum_min, corrSum_max] is representable. But modulo p, these gaps might or might not include 0.

More precisely, the set {corrSum(A) : A admissible} is a SUBSET of the integers in [corrSum_min, corrSum_max]. The density of this set in the interval is C / (corrSum_max - corrSum_min).

We have corrSum_max - corrSum_min ~ 3^{S-2k} * 3^k ~ 3^{S-k} (from R199 arc analysis). And C = C(S-1, k-1) ~ (S-1 choose k-1).

### 8.6 Modular Arithmetic and the Step Structure

Consider the STEP-BY-STEP construction of corrSum via Horner's form:

C_0 = 0
C_j = 2^{s_j} * C_{j-1} + 3^{k-j}

where s_j = a_j - a_{j-1} >= 1 (with a_0 = 0).

At each step, the choice of s_j MULTIPLIES the current value by 2^{s_j} and ADDS 3^{k-j}. In F_p:

C_j = 2^{s_j} * C_{j-1} + 3^{k-j} mod p

This is an ITERATED AFFINE MAP on F_p. The question is: what is the image of 0 under all possible compositions of these affine maps?

### 8.7 Affine Maps and Orbit Analysis

For each step j, the set of possible affine maps is:

{f_{j,s} : x -> 2^s * x + 3^{k-j} mod p : s >= 1, s <= R_j}

where R_j is the remaining budget of even steps.

The image after step 1 is:

Im_1 = {2^s * 0 + 3^{k-1} : s = 1, ..., S-k+1} = {3^{k-1} * (mod p)}

Wait -- C_0 = 0, so C_1 = 2^{s_1} * 0 + 3^{k-1} = 3^{k-1} regardless of s_1. This means the FIRST step is always the same value 3^{k-1} mod p!

Actually no -- C_1 = 3^{k-1} for ANY choice of s_1. The choice of s_1 only affects the remaining budget for later steps.

Hmm, let me reconsider. The Horner form is:

corrSum = 3^{k-1} * 2^{a_1} + 3^{k-2} * 2^{a_2} + ... + 3^0 * 2^{a_k}

This is NOT the same as the iterative form I wrote above. Let me redo:

Define D_k = corrSum = sum_{j=1}^k 3^{k-j} * 2^{a_j} (note: 3^{k-j}, not 3^{k-1-j} -- I need to be careful with indexing).

Actually, from the original definition: corrSum(A) = sum_{j=1}^k 3^{k-1-j} * 2^{a_j}. With the convention that the last term (j=k) has coefficient 3^{-1}? No, k-1-j with j=k gives 3^{-1}. That can't be right.

Let me re-examine. The standard Collatz cycle equation gives:

n_0 * d = sum_{j=1}^k 3^{k-j} * 2^{a_j}

where d = 2^S - 3^k. So the corrSum should be:

corrSum(A) = sum_{j=1}^k 3^{k-j} * 2^{a_j}

with the j-th coefficient being 3^{k-j}, giving coefficients 3^{k-1}, 3^{k-2}, ..., 3^0 for j = 1, 2, ..., k.

The iterative Horner form is then:

D_0 = 0
D_j = 3 * D_{j-1} + 2^{a_j}  for j = 1, ..., k

Check: D_1 = 2^{a_1}. D_2 = 3 * 2^{a_1} + 2^{a_2}. D_k = 3^{k-1} * 2^{a_1} + 3^{k-2} * 2^{a_2} + ... + 2^{a_k}. Yes, this is correct.

Wait, that's not right either. Let me be very careful:

D_j = sum_{i=1}^j 3^{j-i} * 2^{a_i}

So D_j = 3 * D_{j-1} + 2^{a_j}. And corrSum = D_k = sum_{i=1}^k 3^{k-i} * 2^{a_i}. Yes.

### 8.8 The Correct Horner Iteration

D_0 = 0
D_j = 3 * D_{j-1} + 2^{a_j}  (j = 1, ..., k)

At each step j, D_j is obtained from D_{j-1} by:
- Multiply by 3 (fixed)
- Add 2^{a_j} (where a_j > a_{j-1} and a_j in {a_{j-1}+1, ..., S - (k-j)})

The key observation: the multiplication by 3 is FIXED at each step. Only the ADDITION varies. In F_p, multiplication by 3 is a fixed automorphism (since p does not divide 3), and the addition is one of several values 2^a for allowed a.

### 8.9 Reachability in F_p

The image Im_k = {D_k mod p : A admissible} is the set of reachable values after k steps of the iterated map.

After step 1: Im_1 = {2^{a_1} mod p : a_1 = 1, ..., S-k+1}
             = {2, 4, 8, ..., 2^{S-k+1}} mod p
             = {2^a mod p : a = 1, ..., S-k+1}

This is a SUBSET of the cyclic group <2> in F_p*.

After step 2: Im_2 = {3*x + 2^{a_2} mod p : x in Im_1, a_2 > a_1}

The map x -> 3x + c is bijective on F_p for any c. So Im_2 consists of translates and scalings of Im_1.

### 8.10 The Expanding Map Heuristic

At each step, the image set grows (by branching on the choice of a_j) and contracts (by the constraint a_j > a_{j-1}). After k steps, the image has C = C(S-1, k-1) preimages but might cover only a portion of F_p.

**Claim (Tool H -- main).** There exist primes p | d(k) for which the iterated affine map starting from 0 CANNOT reach 0 after k steps. This is because:

1. After step 1, the image is a COSET of a subgroup of F_p* (specifically, a set of consecutive powers of 2).
2. After step 2, the image is a translate of a dilate of the step-1 image, united over allowed branches.
3. The key constraint: a_k = S forces 2^{a_k} = 2^S = 3^k mod p. So the LAST addition is fixed: D_k = 3 * D_{k-1} + 3^k mod p.

Therefore: D_k = 0 mod p requires D_{k-1} = -3^{k-1} mod p.

And D_{k-1} = 0 requires D_{k-2} = -3^{k-2} * something... No, D_{k-1} = 3 * D_{k-2} + 2^{a_{k-1}}, so D_{k-1} = -3^{k-1} requires 3 * D_{k-2} + 2^{a_{k-1}} = -3^{k-1} mod p.

### 8.11 Backward Induction: The Target Set Shrinks

Define the TARGET sets backward:

T_k = {0} (we want D_k = 0 mod p)
T_{k-1} = {x : 3x + 3^k = 0 mod p} = {-3^{k-1} mod p}  (size 1, since a_k = S is fixed)
T_{k-2} = {x : 3x + 2^a = -3^{k-1} mod p for some valid a_{k-1}}
        = {(-3^{k-1} - 2^a) / 3 mod p : a in {a_{k-2}+1, ..., S-1}}

The size of T_{k-2} is at most S-1-a_{k-2} (the number of valid choices for a_{k-1}). But a_{k-2} is not yet fixed at this stage; it depends on earlier choices.

This backward induction gives:

T_{k-j} = {x : there exists a path from x to 0 through j steps}

The size of T_{k-j} grows with j (more paths), but is bounded by the product of branch numbers.

### 8.12 What This Proves (Potentially)

If we can show that |T_0| = 0 (i.e., there is no way to start from D_0 = 0 and reach D_k = 0 through valid steps), then N_0(p) = 0.

T_0 is the set of INITIAL values that lead to D_k = 0. Since D_0 = 0 is fixed, we need 0 in T_0.

The backward induction gives T_0 as the preimage of {0} under the full composition. The QUESTION is whether 0 is in this preimage.

### 8.13 The Counting Argument

|T_0| is exactly N_0(p). So asking whether 0 in T_0 is the same as asking whether N_0(p) > 0. This is CIRCULAR.

BUT the backward induction provides a NEW STRUCTURAL INSIGHT: the target set at each backward step is determined by the INTERSECTION of a set of affine images with the allowed range.

Specifically:

T_{k-1} = {-3^{k-1}} (a single point)
T_{k-2} = {(-3^{k-1} - 2^a) * 3^{-1} : a ranges over allowed values}

This is a set of at most S - k elements of F_p. If these elements are UNIFORMLY distributed in F_p, the probability that any particular point (like the required D_{k-2} from a valid path) is in this set is ~ (S-k)/p.

After j backward steps, the target set has size at most product_{i=1}^j (branch number at step k-i), which grows exponentially. But modulo p, the set wraps around and potentially covers all of F_p.

### 8.14 The Small-Branching Regime

For the FIRST few backward steps (from step k), the branching is LIMITED:

- Step k: a_k = S (forced), 1 branch
- Step k-1: a_{k-1} in {k-1, ..., S-1}, at most S-k+1 branches
- Step k-2: a_{k-2} in {k-2, ..., a_{k-1}-1}, at most a_{k-1}-k+1 branches

In the backward direction, the EARLY steps have limited branching. If p is large enough relative to the branching, the target set T_{k-j} does not cover all of F_p, and it might miss 0.

Concretely, after j backward steps, |T_{k-j}| <= (S-k+1)^j / j! (approximately, accounting for monotonicity constraints). For this to NOT cover F_p, we need:

(S-k+1)^j / j! < p

For j = k (all the way back), this is C(S-1, k-1) < p, which is C < p, which FAILS for k >= 18.

BUT: for intermediate j (say j = k/2), we might have (S-k+1)^{k/2} / (k/2)! < p. Whether this is useful depends on the specific values.

### 8.15 The Hybrid Approach

**Idea:** Run backward induction for j steps (until the target set is "small"), then show that the FORWARD image from step 0 through step k-j MISSES the target set.

This requires:
1. Backward: T_{k-j} has size << p (for j sufficiently large but < k)
2. Forward: Im_{k-j} (forward image after k-j steps from D_0=0) has size << p
3. Intersection: T_{k-j} intersect Im_{k-j} is EMPTY

If both sets have size << p and are "random-looking" in F_p, then the probability of intersection is ~ |T| * |Im| / p, which is small when |T| * |Im| < p.

For this to work: |T_{k-j}| * |Im_{k-j}| < p for some j.

The size of Im_{k-j} after k-j forward steps from 0 is at most C(a_{k-j}, k-j) for the maximal a_{k-j}. And |T_{k-j}| <= C(S-1-k+j, j-1) (number of monotone sequences for the last j positions).

We need: C(S-1-k+j, j-1) * C(a_{max}, k-j) < p.

By the Vandermonde identity: sum_j C(S-1-k+j, j-1) * C(k-j+something, k-j) = C(S-1, k-1) = C. So the PRODUCT at the optimal j is approximately C^{2/k} (by AM-GM type argument).

We need C^{2/k} < p. Since C ~ 4.31^k (from Section 3.7), C^{2/k} ~ 4.31^2 ~ 18.6. This again gives p < ~18, the SAME threshold as the Weil bound!

### 8.16 The Fundamental Barrier

The number 18.6 keeps appearing because C ~ alpha^k and the "square root barrier" gives alpha^{k * (1/k)} = alpha ~ 4.31 as the threshold. This is the POLYA-VINOGRADOV / square-root barrier for character sums, manifesting in a different guise.

To break this barrier, we need:
- Either a method that does NOT rely on the size of C (i.e., a STRUCTURAL argument), or
- A method that exploits the SPECIFIC algebraic structure of the problem (not just generic bounds)

### 8.17 Obstacles

1. **The square-root barrier (~p < 18) appears universally across Tools C, G, and H.** This suggests a deep obstruction.
2. **The backward induction is CIRCULAR as a counting argument** (|T_0| = N_0(p)).
3. **The hybrid approach runs into the same p < 18 barrier.**
4. **Breaking the barrier requires structural arguments, not size arguments.**

However, **the backward induction framework is the most CONCRETE of all tools.** It reduces the problem to a question about the intersection of two explicitly constructed sets in F_p. Even if generic bounds fail, specific computations for individual primes might succeed.

**Feasibility: 6/10.** The most promising tool, primarily because it is the most CONCRETE and suggests a computational strategy: for each specific p | d(k), construct the backward target sets and forward image sets and check for intersection. This can be done for k = 18, ..., 41 if the sets are small enough.

---

## 9. COMPARATIVE ASSESSMENT

| Tool | Name | Feasibility | Why |
|:---:|:---|:---:|:---|
| A | Algebraic Structure | 3/10 | Reformulation, not solution |
| B | p-adic Valuation | 2/10 | Affine maps are isometries in Q_p |
| C | Generating Function Nullstellensatz | 5/10 | Structured, but Weil bound gives p < 18 |
| D | Symmetry Breaking | 2/10 | Circular concentration fails modulo p |
| E | Logarithmic Orbit Exclusion | 4/10 | Novel, but lower bounds on exp sums are hard |
| F | Exact Cancellation / Rep Theory | 3/10 | Tautological at the additive level |
| G | Algebraic Geometry / Weil | 2/10 | Monotone constraint is combinatorial, not algebraic |
| H | Monotone Cone Exclusion | **6/10** | Most concrete; backward induction framework |

### The Recurrent Barrier: p < 18

Three independent approaches (Weil bound in Tool C, hybrid counting in Tool H, and generic character sum bounds) all converge on the same threshold: **methods based on the SIZE of C relative to p can only handle p < ~18.**

This is the **square-root barrier** for this problem. Any method that treats corrSum values as "generic" elements of F_p and relies on counting arguments will hit this barrier.

### What Would Break the Barrier

To handle p > 18 (which is ALL primes of interest for k >= 18), we need:

1. **A structural prohibition:** Some algebraic identity or congruence that forces corrSum != 0 mod p for ALL admissible A, regardless of C vs p. This would require discovering a hidden ALGEBRAIC structure in the monotone corrSum.

2. **An amplification trick:** A way to reduce the problem to a SMALLER effective C. For example, if we could show that most admissible A contribute corrSum in a specific coset of F_p, then the effective C for the remaining residues would be smaller.

3. **A multi-prime sieve:** Instead of proving N_0(p) = 0 for a SINGLE prime, show that for any COMBINATION of small primes p_1, ..., p_m dividing d(k), the simultaneous congruence corrSum = 0 mod (p_1 * ... * p_m) has no solution. This is the CRT approach but using PRODUCTS of small primes instead of a single large prime.

4. **An entirely different invariant:** Instead of corrSum, find a different function of the admissible tuple A that (a) equals 0 iff corrSum = 0 mod d, and (b) is easier to analyze. For example, the PARITY of some combinatorial invariant of A.

---

## 10. TOOL H-PRIME: MULTI-PRIME SIEVE (NEW DEVELOPMENT)

### 10.1 Concept

This is an extension of Tool H that exploits the CRT more aggressively.

Instead of finding ONE prime p | d(k) with N_0(p) = 0, show that for a PRODUCT m = p_1 * p_2 * ... * p_r of prime factors of d(k), N_0(m) = 0.

By CRT: N_0(m) = 0 iff there is no A with corrSum = 0 mod p_i for ALL i = 1, ..., r simultaneously.

If the events "corrSum = 0 mod p_i" were INDEPENDENT, then:

N_0(m) ~ C * prod_i (1/p_i) = C / m

For N_0(m) = 0, we need C / m < 1, i.e., m > C. But m | d and d < C for k >= 18 (this is the whole problem). So even using ALL prime factors (m = d), the heuristic gives N_0(d) ~ C/d > 1.

### 10.2 Exploiting Dependence

The events "corrSum = 0 mod p_i" are NOT independent. The correlation between them depends on the algebraic relations between the primes.

If the primes are "independent" (i.e., the Chinese Remainder Theorem makes the conditions independent), then N_0(m) ~ C / m as above.

But if the primes are "correlated" (because they all divide d, and d has specific structure), then the actual count could be LOWER than the heuristic.

### 10.3 The Cross-Correlation

For two primes p_1, p_2 dividing d(k), both satisfy 2^S = 3^k mod p_i. This creates a COMMON algebraic constraint on the admissible A.

The corrSum mod p_1 and corrSum mod p_2 are DIFFERENT linear functions of the same variables (a_1, ..., a_{k-1}). They share the same COMBINATORIAL structure (monotonicity) but live in different fields (F_{p_1} vs F_{p_2}).

The probability of joint zero is:

Prob(corrSum = 0 mod p_1 AND corrSum = 0 mod p_2)
= Prob(corrSum = 0 mod p_1*p_2) by CRT (assuming gcd(p_1, p_2) = 1)
~ 1/(p_1 * p_2) if independent

The CROSS-CORRELATION could make this probability lower. If corrSum mod p_1 = 0 constrains the admissible A to a specific subset, and this subset has a BIASED distribution of corrSum mod p_2, then the joint probability could be much lower.

### 10.4 Formal Statement

**Claim (Tool H' -- aspirational).** For specific k in [18, 41], there exists a subset S_k of prime factors of d(k) such that:

N_0(prod_{p in S_k} p) = 0

even though N_0(p) > 0 for each individual p in S_k.

**What this requires:** The simultaneous congruence system corrSum = 0 mod p for all p in S_k has NO admissible solution. This is STRONGER than having a solution for each p individually.

### 10.5 Obstacles

1. **The heuristic N_0(m) ~ C/m > 0 suggests solutions exist.**
2. **Proving non-existence of solutions to a system of congruences with combinatorial constraints is equivalent to the original problem.**
3. **The cross-correlations are hard to compute analytically.**
4. **This approach reduces to the original problem (prove N_0(d) = 0) when S_k contains all prime factors.**

However, the sieve perspective suggests a COMPUTATIONAL strategy: for each k in [18, 41], enumerate solutions to corrSum = 0 mod p for each small prime p | d(k), and check if the solutions INTERSECT across primes. If the intersection is empty, N_0(d) = 0 is proved.

**Feasibility: 5/10.** The multi-prime sieve is computationally concrete and could work for specific k. The obstacle is that for large k, the enumeration becomes infeasible. But for k in [18, 41], the compositions number C <= 10^17, and sieving by multiple small primes could reduce this to a manageable computation.

---

## 11. META-ANALYSIS: THE LANDSCAPE OF APPROACHES

### 11.1 The Three Families

All tools fall into three families:

**Family 1: Generic Bounds (Tools B, C, D, G)**
- Rely on the SIZE of C vs p
- Hit the square-root barrier at p ~ 18
- Cannot handle the regime of interest (p > 18)

**Family 2: Structural Arguments (Tools A, E, F)**
- Try to exploit specific algebraic properties of corrSum
- Face the difficulty of proving LOWER bounds on exponential sums
- No complete argument, but the most theoretically promising

**Family 3: Constructive / Computational (Tools H, H')**
- Directly construct the target sets or enumerate solutions
- Can work for specific (k, p) pairs
- Limited by computational complexity for large k

### 11.2 Recommended Strategy

1. **Short term (for the preprint):** Use Tool H (backward induction) COMPUTATIONALLY for k = 18, ..., 41 and small primes p | d(k). This would provide a FINITE VERIFICATION resolving these cases. Combined with the arc argument (k >= 42 with delta < 0.415) and Baker bounds (k >= K_0), this could close the gap.

2. **Medium term:** Develop Tool E (Logarithmic Orbit Exclusion) theoretically. This is the most promising GENERAL approach that could work for all k and p.

3. **Long term:** Investigate whether the square-root barrier (p ~ 18) can be broken by representation-theoretic methods (Tool F extended) or additive combinatorics techniques (Freiman-Ruzsa theorem, sum-product estimates).

### 11.3 Connection to Known Open Problems

The problem of proving N_0(p) = 0 for p < C is closely related to:

1. **The Waring problem over F_p:** How many powers of a fixed base are needed to represent every element of F_p? Our problem asks whether 0 is representable by a SPECIFIC number of powers.

2. **The sum-product conjecture (Erdos-Szemeredi):** Sets with multiplicative structure (like {2^a : a monotone}) have large sumsets. If the sumset of our weighted powers avoids 0, N_0(p) = 0.

3. **Additive combinatorics of exponential sets:** The set {2^1, 2^2, ..., 2^{S-1}} in F_p is a GEOMETRIC PROGRESSION. Sums of subsets of geometric progressions have been studied (Bourgain, Konyagin), and strong sum-product estimates apply. However, our sum has WEIGHTS (3^{k-j}), complicating the application.

4. **The hidden subgroup problem:** The distribution of corrSum mod p could be related to a hidden subgroup of some abelian group, and quantum algorithms could detect this structure. (This is speculative.)

---

## 12. CONCLUSION

### 12.1 What We Found

Eight tools were developed, spanning algebraic, analytic, combinatorial, and computational approaches. The most significant findings are:

1. **The square-root barrier at p ~ 18** is a fundamental obstruction for all SIZE-based methods. This explains why Etage 1 (small primes p <= 97) is tractable but extension to larger primes is blocked.

2. **The backward induction framework (Tool H)** is the most concrete approach, reducing the problem to intersection of explicitly constructable sets in F_p. For specific k, this could be computationally feasible.

3. **The Logarithmic Orbit Exclusion (Tool E)** is the most theoretically novel approach, connecting the problem to lower bounds on exponential sums with structured exponents. This is a HARD problem but has connections to active research in additive combinatorics.

4. **The multi-prime sieve (Tool H')** offers a middle ground: using CRT with PRODUCTS of small primes, rather than requiring a single large prime. The heuristic N_0(m) ~ C/m is pessimistic, but cross-correlations from the shared constraint 2^S = 3^k mod p_i could reduce the count below the heuristic.

### 12.2 Honest Assessment

**Distance to a complete proof via any of these tools: LARGE.**

No tool provides a ready-made proof of N_0(p) = 0 for p < C. The best case (Tool H, computational) could work for SPECIFIC k values but requires significant computation and may fail if the target sets grow too quickly. The best theoretical tool (Tool E) requires breakthroughs in exponential sum lower bounds.

**However:** The identification of the square-root barrier at p ~ 18 is itself a CONTRIBUTION. It explains WHY the CRT approach fails and what kind of argument is needed to go beyond it. Any successful approach must be STRUCTURAL (exploiting the specific algebraic relations in Collatz) rather than GENERIC (treating corrSum as a random variable).

### 12.3 Recommendation for R201

Focus on **Tool H applied computationally to k = 18**: Factor d(18) = 137 * 1,090,879. For p = 137 (small) and p = 1,090,879 (larger), construct the backward target sets and forward image sets. Determine whether 0 is in the forward image (i.e., whether N_0(p) > 0 or N_0(p) = 0). If N_0(p) > 0 for BOTH primes, then the CRT approach is definitively blocked for k = 18, and we need to pivot to the Barina/arc approach (which DOES resolve k = 18..111 as shown in R199).

---

## REFERENCES

- Deligne, P. (1974). La conjecture de Weil I. Publ. Math. IHES, 43, 273-307.
- Erdos, P., Ginzburg, A., Ziv, A. (1961). Theorem in additive number theory. Bull. Research Council Israel, 10F, 41-43.
- Bourgain, J. (2005). Estimates on exponential sums related to Diffie-Hellman distributions. GAFA, 15, 1-34.
- Konyagin, S. (2003). Bounds of exponential sums over subgroups and Gauss sums. Proc. 4th Int. Conf. Modern Problems of Number Theory.
- Lopez de Prado, M. (2018). Advances in Financial Machine Learning. Wiley.
- Steiner, R.P. (1977). A theorem on the Syracuse problem. Proc. 7th Manitoba Conf.
- Simons, J. & de Weger, B. (2005). Theoretical and computational bounds for m-cycles. Acta Arith., 117(1), 51-70.
- Barina, D. (2020). Convergence verification of the Collatz problem. J. Supercomputing, 77(3), 2681-2688.
- Tao, T. & Vu, V. (2006). Additive Combinatorics. Cambridge University Press.
- Freiman, G. (1973). Foundations of a Structural Theory of Set Addition. AMS Translations.

---

*R200 Innovateur Deductif complete. 8 theoretical tools developed, square-root barrier at p ~ 18 identified as fundamental obstruction. Most promising direction: Tool H (backward induction, computational) for finite verification of specific k. No tool provides unconditional proof for general k.*
