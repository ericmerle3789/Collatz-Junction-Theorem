# R172 — THE WORD SPACE AND TRANSFER MATRIX APPROACH

**Date:** 15 mars 2026 | **Statut:** [ANALYSE STRUCTURELLE] [PISTES OUVERTES + OBSTRUCTIONS IDENTIFIEES]

**Suite de:** R171 (exploration autonome), R162 (TPE), R160 (role du +1)

---

## 1. THE TRANSFER MATRIX FORMULATION: MAKING IT PRECISE

### 1.1 Affine Collatz maps as 2x2 matrices

The Collatz function acts on integers by two affine maps:
- **Odd step:** n -> (3n + 1)  (multiply by 3, add 1)
- **Even step:** n -> n/2  (divide by 2)

A k-cycle with parity vector v = (v_0, ..., v_{k-1}) and composition s = (s_0, ..., s_{k-1}) with S = sum(s_j) performs, at step j:
- If v_j = 1: one odd step (3n+1) followed by s_j divisions by 2: n -> (3n+1)/2^{s_j}
- If v_j = 0: s_j divisions by 2: n -> n/2^{s_j}

In homogeneous coordinates [n; 1], the affine map n -> (an + b) is represented by the matrix [[a, b], [0, 1]]. So:

**M_j = [[3/2^{s_j}, 1/2^{s_j}], [0, 1]]** if v_j = 1

**M_j = [[1/2^{s_j}, 0], [0, 1]]** if v_j = 0

### 1.2 The product formula

The cycle condition requires M = M_{k-1} ... M_1 M_0 to satisfy M [n; 1]^T = [n; 1]^T.

The product matrix has the form:

**M = [[3^x / 2^S, b/2^S], [0, 1]]**

where x = |{j : v_j = 1}| is the number of odd steps, and b is the accumulated affine constant.

The cycle equation M [n; 1]^T = [n; 1]^T gives:

**(3^x / 2^S) n + b/2^S = n**

Hence **n (2^S - 3^x) = b**, i.e., **n = b / d** where d = 2^S - 3^x.

### 1.3 Explicit computation of b

The affine constant b accumulates through matrix multiplication. Let us track it carefully.

Writing M_j = [[a_j, b_j], [0, 1]] where:
- a_j = 3^{v_j} / 2^{s_j}, b_j = v_j / 2^{s_j}

The product M_{k-1} ... M_0 has entries:
- (1,1): prod(a_j) = 3^x / 2^S
- (1,2): sum_{j=0}^{k-1} b_j * prod_{i=j+1}^{k-1} a_i

Computing the (1,2) entry:

b = sum_{j: v_j=1} (1/2^{s_j}) * prod_{i=j+1}^{k-1} (3^{v_i} / 2^{s_i})

= sum_{j: v_j=1} (1/2^{s_j}) * 3^{x_{>j}} / 2^{S_{>j}}

where x_{>j} = |{i > j : v_i = 1}| and S_{>j} = sum_{i>j} s_i.

Thus: b = sum_{j: v_j=1} 3^{x_{>j}} / 2^{s_j + S_{>j}}

Multiplying numerator and denominator by 2^S:

**2^S * b = sum_{j: v_j=1} 3^{x_{>j}} * 2^{S - s_j - S_{>j}}**

= sum_{j: v_j=1} 3^{x_{>j}} * 2^{B_j}

where B_j = sum_{i < j} s_i (the partial sum of divisions before step j).

**This is precisely g(v) = corrSum(v, s).**

So n = g(v) / d, confirming the classical formula. The transfer matrix approach recovers corrSum as the affine accumulation constant.

---

## 2. THE WORD SPACE: CORRSUM AS A FUNCTION ON BINARY WORDS

### 2.1 The evaluation map

Define the evaluation map:

**g: W(k, x, S) -> Z/dZ**

where W(k, x, S) is the set of all valid pairs (v, s) with v in {0,1}^k of weight x and s a strict composition of S into k parts (each s_j >= 1), and:

g(v, s) = sum_{j: v_j=1} 3^{x_{>j}} * 2^{B_j}  (mod d)

The cycle existence question is: **does 0 lie in Image(g)?**

### 2.2 Size of the domain

The number of parity vectors: C(k, x) where x = number of ones.

The number of compositions: C(S-1, k-1) (stars and bars with s_j >= 1).

For S = ceil(x * log_2(3)), the domain is typically huge for moderate k, but the target d grows exponentially.

### 2.3 The hidden symmetry: 2^S = 3^x (mod d)

This is the KEY algebraic fact. In Z/dZ:

**2^S ≡ 3^x (mod d)**

This means the two "bases" 2 and 3 are NOT independent modulo d. Define r = ord_d(2) (the multiplicative order of 2 mod d). Then 3^x = 2^S = 2^{S mod r} in (Z/dZ)^*.

If gcd(x, r) allows it, we can write 3 ≡ 2^{S/x} (mod d) — but S/x is not generally an integer. More precisely, 3 is a power of 2 modulo d if and only if 3 belongs to the subgroup <2> in (Z/dZ)^*.

**Lemma (R162 uniformizer):** When gcd(S, x) = 1 (Bezout gives aS + bx = 1), define zeta = 2^a * 3^{-b} mod d. Then 2 = zeta^x and 3 = zeta^S in Z/dZ. This was established in R162 and transforms corrSum into a univariate polynomial in zeta.

### 2.4 Rewriting corrSum as a polynomial

Under the uniformizer substitution (when it exists):

g(v, s) = sum_{j: v_j=1} zeta^{S * x_{>j}} * zeta^{x * B_j}

= sum_{j: v_j=1} zeta^{S * x_{>j} + x * B_j}

Define the **phase exponents** e_j = S * x_{>j} + x * B_j for j with v_j = 1.

Then g(v,s) = sum_{j: v_j=1} zeta^{e_j}.

The cycle condition g(v,s) ≡ 0 (mod d) becomes: **the "phase polynomial" P(zeta) = sum zeta^{e_j} vanishes at a primitive element of Z/dZ**.

---

## 3. THE LATTICE VIEWPOINT

### 3.1 The lattice of g-values

Consider the set G = {g(v, s) mod d : (v, s) in W(k, x, S)} as a subset of Z/dZ.

This is NOT a subgroup in general (g is a sum of products, not a linear map). However, we can study its additive structure.

Each g-value is a sum of x terms from the set:

T = {3^a * 2^b mod d : 0 <= a < x, 0 <= b < S}

More precisely, the j-th odd step contributes 3^{x_{>j}} * 2^{B_j} where the exponents are constrained by:
- x_{>j} decreases from x-1 to 0 as j ranges over odd positions (left to right)
- B_j increases strictly

So g(v,s) is NOT an arbitrary x-element subset sum from T. The ordering constraints (x_{>j} decreasing, B_j increasing) impose a RIGID STRUCTURE.

### 3.2 The monotonicity constraint

For the exponents e_j = S * x_{>j} + x * B_j, as j increases through odd positions:
- x_{>j} decreases by 1 each time (from x-1 to 0)
- B_j increases by at least 1 each time

So the increment: e_{j+1} - e_j = S * (x_{>j+1} - x_{>j}) + x * (B_{j+1} - B_j) = -S + x * delta_j

where delta_j = B_{j+1} - B_j >= 1 (the gap in partial sums).

The sign of the increment depends on whether x * delta_j > S or < S.

Since S >= ceil(x * log_2(3)) ~ 1.585x, we need delta_j > S/x ~ 1.585 for the exponent to increase. For delta_j = 1 (minimum gap), the increment is x - S < 0 (exponent decreases). For delta_j = 2, increment is 2x - S which is positive iff S < 2x, i.e., log_2(3) < 2, which is true.

**So the exponent sequence e_j is NOT monotone in general.** It depends on the composition s. This non-monotonicity is precisely what makes the problem hard.

### 3.3 The lattice L = d * Z inside Z

The cycle condition is g(v,s) in d * Z (as integers, not mod d). The set of all g-values (over all valid v, s) forms a subset of Z. The question is whether this subset hits the sublattice d * Z at any point other than possibly 0.

Since g(v,s) > 0 always (it is a sum of positive terms), and the smallest g-value is bounded below, we need g(v,s) >= d for a non-trivial cycle.

**Known bound (Steiner/Simons-de Weger):** For k >= 2, the minimum starting value of any k-cycle satisfies n >= 2^{k/2}. Combined with n = g(v,s)/d, this means g(v,s) >= d * 2^{k/2}.

---

## 4. THE TRANSFER MATRIX AS A SEMIGROUP ACTION

### 4.1 The semigroup of Collatz matrices

Define the matrices (over Q):
- T_1(s) = [[3/2^s, 1/2^s], [0, 1]] for an odd step with s divisions
- T_0(s) = [[1/2^s, 0], [0, 1]] for an even step with s divisions

The set of all products of these matrices forms a semigroup under multiplication.

The cycle condition is: there exists a product P of k such matrices (with the correct type sequence v and total exponent S) such that P has eigenvalue 1 at an integer eigenvector [n; 1].

### 4.2 Integer formulation

Clearing denominators, work over Z. Define:
- **T_1^(s) = [[3, 1], [0, 2^s]]** (odd step: [n, 1] -> [3n+1, 2^s])
- **T_0^(s) = [[1, 0], [0, 2^s]]** (even step: [n, 1] -> [n, 2^s])

The product P = T_{v_{k-1}}^(s_{k-1}) ... T_{v_0}^(s_0) has the form:

**P = [[3^x, g(v,s)], [0, 2^S]]**

The cycle condition P [n; 1]^T = lambda [n; 1]^T (with lambda = 2^S from the (2,2) entry) gives:
- 3^x n + g(v,s) = 2^S n
- Hence (2^S - 3^x) n = g(v,s), i.e., n = g(v,s) / d. QED.

### 4.3 Spectral interpretation

The matrix P has eigenvalues 3^x and 2^S. The eigenvectors are:
- [1; 0] with eigenvalue 3^x (this is the "trivial" eigenvector)
- [g(v,s)/d; 1] with eigenvalue 2^S (this is the "cycle" eigenvector)

A cycle exists iff the second eigenvector is an INTEGER vector, i.e., d | g(v,s).

**Observation:** The matrix P lies in the upper triangular group over Z. The (1,1) and (2,2) entries are FIXED by (x, S). The ONLY free parameter is g(v,s), the upper-right entry. The question is entirely about the upper-right entry of the product.

---

## 5. STRUCTURAL ANALYSIS: WHY d SHOULD NOT DIVIDE g(v,s)

### 5.1 The carry propagation argument

Write g(v,s) in base 2. Each term 3^{x_{>j}} * 2^{B_j} is a number whose binary representation is that of 3^{x_{>j}} shifted left by B_j positions.

When we add x such terms, carry propagation occurs. The final result g(v,s) has a binary representation determined by the interaction of these shifted copies of powers of 3.

Now d = 2^S - 3^x. In binary, d has the form: 1 followed by S zeros, minus 3^x. The binary representation of d is highly structured.

For d | g(v,s), the binary representation of g(v,s) must be "compatible" with d in a very specific way. The carry structure of the sum constrains this.

**However, this is essentially the automata-theoretic viewpoint, and the ghost cycle paper (arXiv:2601.12772) proves that Presburger/automata approaches are provably insufficient.** The carry structure, being expressible in Presburger arithmetic, cannot capture the full obstruction.

### 5.2 The mixed-power structure

Each term in g(v,s) has the form 3^a * 2^b. The set of such "mixed powers" is:

{3^a * 2^b : a >= 0, b >= 0} = the multiplicative semigroup generated by {2, 3}.

This is the set of 6-smooth numbers (or rather, numbers whose only prime factors are 2 and 3). By the Stormer-type theorems, these are SPARSE in Z.

The g-values are sums of x such 6-smooth numbers with specific constraints. The number d = 2^S - 3^x is NOT 6-smooth (for k >= 2, d has prime factors other than 2 and 3).

**Key structural point:** g(v,s) is a sum of x numbers from the 6-smooth semigroup, while d is NOT 6-smooth. For d | g(v,s), the quotient n = g(v,s)/d must be a positive integer, meaning g(v,s) = n * d = n * (2^S - 3^x) = n * 2^S - n * 3^x.

So: **sum_{j} 3^{x_{>j}} * 2^{B_j} = n * 2^S - n * 3^x**

The left side is a sum of 6-smooth numbers. The right side is n * 2^S - n * 3^x, which is a DIFFERENCE of two terms, each of which is n times a 6-smooth number.

### 5.3 The valuation obstruction (a new angle)

For any prime p | d (with p != 2, 3), consider the p-adic valuation v_p.

v_p(d) >= 1. For d | g(v,s), we need v_p(g(v,s)) >= v_p(d).

But v_p(3^a * 2^b) = 0 for all a, b (since p != 2, 3). So each term in g has p-adic valuation 0.

A sum of x terms each with v_p = 0 can have v_p >= 1, but only if the terms "conspire" to cancel modulo p. The probability heuristic gives roughly 1/p chance per prime.

**For the COMPOSITE d:** if d = p_1^{e_1} * ... * p_m^{e_m}, we need simultaneous cancellation modulo all p_i^{e_i}. By CRT, this is roughly independent, so the "probability" is approximately 1/d.

The number of valid (v, s) pairs is roughly C(k, x) * C(S-1, k-1). For this to be < 1 when divided by d, we need:

C(k, x) * C(S-1, k-1) < d = 2^S - 3^x

For large k, the left side grows polynomially in S (for fixed k), while d grows exponentially. So for k >= some threshold, no cycles exist "for density reasons."

**But this is a HEURISTIC, not a proof.** The terms are not independent.

### 5.4 The image of g modulo a single prime

For p | d, the map g: W(k,x,S) -> Z/pZ sends each (v,s) to sum_{j: v_j=1} 3^{x_{>j}} * 2^{B_j} mod p.

We proved (computationally, for k = 3..14) that for no single prime factor p of d is the fiber g^{-1}(0 mod p) empty. This means the proof MUST use the composite structure of d, or a non-modular argument.

---

## 6. THE POLYNOMIAL RING APPROACH

### 6.1 corrSum as an element of Z[2, 3] / (2^S - 3^x)

In the quotient ring R = Z[alpha] / (alpha^S - 3^x) where alpha represents 2, we can write:

g(v,s) = sum_{j: v_j=1} 3^{x_{>j}} * alpha^{B_j}

This is a polynomial in alpha of degree at most S-1 (since B_j <= S - 1).

The cycle condition g ≡ 0 in R is equivalent to: the polynomial P(alpha) = sum_{j: v_j=1} 3^{x_{>j}} * alpha^{B_j} is divisible by the minimal polynomial of 2 in R, which is alpha^S - 3^x.

But deg(P) <= S - 1 < S = deg(alpha^S - 3^x), so P CANNOT be divisible by alpha^S - 3^x as a polynomial... UNLESS P is the zero polynomial.

**Wait — this argument is WRONG as stated.** We don't need P divisible by alpha^S - 3^x as a polynomial. We need P(2) divisible by d = 2^S - 3^x as an integer. These are different conditions.

However, this suggests a polynomial approach:

Define F(X) = sum_{j: v_j=1} 3^{x_{>j}} * X^{B_j} in Z[X].

Then g(v,s) = F(2) and d = 2^S - 3^x.

We want to determine: when does (2^S - 3^x) | F(2)?

By polynomial division: F(X) = Q(X) * (X^S - 3^x) + R(X) where deg(R) < S.

Then F(2) = Q(2) * d + R(2), so d | F(2) iff d | R(2).

But R(X) = F(X) mod (X^S - 3^x). Since deg(F) < S (because B_j <= S - s_{k-1} <= S - 1), we have R(X) = F(X). So we're back to d | F(2).

**The polynomial formulation does not immediately simplify things because F already has degree < S.**

### 6.2 The cyclotomic connection (via the uniformizer)

When gcd(S, x) = 1, the uniformizer zeta = 2^a * 3^{-b} (from R162) satisfies zeta^x ≡ 2 and zeta^S ≡ 3 mod d.

Substituting: F(X) at X = zeta^x gives g = sum zeta^{e_j} where e_j = S * x_{>j} + x * B_j.

Now d | g iff the "phase polynomial" P(Z) = sum Z^{e_j} satisfies d | P(zeta).

Since zeta has multiplicative order dividing lcm(ord_d(2), ord_d(3)) in Z/dZ, the polynomial P is evaluated at a specific root of unity in Z/dZ.

**Connection to cyclotomic polynomials:** If zeta has order r in (Z/dZ)^*, then P(zeta) ≡ 0 mod d iff P(Z) ≡ 0 mod (Phi_r(Z), d) in Z[Z]/(Phi_r(Z)).

This is the R162 "univariate collapse" reformulated in ring-theoretic language.

---

## 7. THE KEY STRUCTURAL OBSTRUCTION: A NEW FORMULATION

### 7.1 The "weight" of g(v,s)

Each term 3^{x_{>j}} * 2^{B_j} has a "logarithmic weight" w_j = x_{>j} * ln(3) + B_j * ln(2).

The monotonicity constraint on (v, s) forces:
- x_{>j} is a DECREASING sequence (x-1, x-2, ..., 0) along odd positions
- B_j is an INCREASING sequence along odd positions

So w_j = (x - 1 - rank_j) * ln(3) + B_j * ln(2) where rank_j is the rank of position j among odd positions (0-indexed).

The total g(v,s) = sum of terms with these constrained weights. The LARGEST term dominates exponentially.

### 7.2 Size bound on g(v,s)

The largest term in g(v,s) is 3^{x-1} * 2^{B_0} (the first odd step, with highest power of 3 and lowest power of 2).

Actually, this is the SMALLEST term if B_0 is small. The competition is between decreasing powers of 3 and increasing powers of 2.

More precisely: the j-th odd step (rank r_j = 0, 1, ..., x-1) contributes:
T_j = 3^{x-1-r_j} * 2^{B_{pos(r_j)}}

The maximum term is the one that maximizes (x-1-r) * ln(3) + B * ln(2). Since ln(3)/ln(2) ~ 1.585, each unit increase in the 3-exponent is worth 1.585 units of 2-exponent. Since the 3-exponent decreases by 1 per step while B increases by at least 1, the "net gain" per step is at least ln(2) - ln(3) < 0... wait, the 3-exponent DECREASES while B INCREASES. So:

Change in log-weight per step: delta(ln T) = -ln(3) + delta_B * ln(2)

This is negative when delta_B < ln(3)/ln(2) ~ 1.585, i.e., when delta_B = 1. And positive when delta_B >= 2.

For S ~ 1.585x (the minimum), the average gap is S/k ~ 1.585x/k. For the minimum composition (all s_j = 1 except one s_j = S - k + 1), the terms have very unequal sizes.

### 7.3 The "balance" obstruction

For g(v,s) to be divisible by d = 2^S - 3^x, we need g(v,s) >= d (since g > 0).

Now d = 2^S - 3^x ~ 2^S (1 - 3^x/2^S). Since S = ceil(x * log_2(3)), we have 3^x/2^S is slightly less than 1, so d is a SMALL FRACTION of 2^S.

Meanwhile, g(v,s) is bounded above by:
g(v,s) = sum_{j} 3^{x_{>j}} * 2^{B_j} <= sum_{r=0}^{x-1} 3^r * 2^{S-1} = 2^{S-1} * (3^x - 1)/2

= (3^x - 1) * 2^{S-2}

And d = 2^S - 3^x.

So g(v,s) / d <= (3^x - 1) * 2^{S-2} / (2^S - 3^x) ~ 2^{S-2} * 3^x / 2^S = 3^x / 4.

This means n = g(v,s)/d <= 3^x / 4 approximately. So the starting value of any k-cycle is bounded by roughly 3^x / 4.

Combined with lower bounds on starting values (e.g., Eliahou 1993: n > 2^{40k}), this gives contradictions for large k. But this doesn't work for moderate k.

---

## 8. THE AUTOMATA VIEWPOINT: TRANSDUCERS AND CARRIES

### 8.1 Collatz as a transducer

The Collatz function on binary representations can be modeled as a finite-state transducer. The state tracks the current "carry" from the 3n+1 operation.

For a cycle, the transducer must return to its initial state after processing k symbols. This is equivalent to a path in the de Bruijn-like graph that returns to its starting node.

### 8.2 The carry structure of corrSum

When computing g(v,s) = sum 3^{x_{>j}} * 2^{B_j} in binary, each term 3^a * 2^b is the binary representation of 3^a shifted left by b positions.

The binary representation of 3^a has floor(a * log_2(3)) + 1 bits. The most significant bit is at position floor(a * log_2(3)).

When we add x such terms (shifted by different amounts B_j), the carries propagate through the binary representation. The key question is whether these carries can conspire to produce a result divisible by d.

### 8.3 Limitation (ghost cycle barrier)

As noted in arXiv:2601.12772, the carry structure is expressible in Presburger arithmetic. The ghost cycle paper constructs explicit "ghost cycles" — solutions to the modular equations that satisfy all Presburger-definable constraints but are not actual cycles. This proves that NO approach based purely on finite automata / carry analysis / Presburger arithmetic can resolve the cycle question.

**Therefore, the automata viewpoint ALONE is provably insufficient.** It must be combined with a number-theoretic or algebraic argument that goes beyond Presburger arithmetic.

---

## 9. SYNTHESIS: WHAT THE WORD SPACE APPROACH REVEALS

### 9.1 What we gained

1. **The transfer matrix formulation cleanly separates the problem:** The (1,1) and (2,2) entries of the product matrix are FIXED (3^x and 2^S). The entire cycle question reduces to the (1,2) entry g(v,s). This is a well-defined linear algebra problem.

2. **The polynomial reformulation (Section 6)** shows that g(v,s) = F(2) for an explicit polynomial F in Z[X] of degree < S. The condition d | F(2) is a DIVISIBILITY CONDITION on the evaluation of a polynomial at X = 2. This connects to interpolation theory and height bounds.

3. **The uniformizer approach (Section 6.2)** reduces to evaluating a sum of roots of unity. But this was already established in R162 (the TPE).

### 9.2 The genuine new insight: polynomial height vs. divisor size

Consider F(X) = sum_{j: v_j=1} 3^{x_{>j}} * X^{B_j}.

This polynomial has:
- Exactly x non-zero coefficients (the values 3^{x-1}, 3^{x-2}, ..., 3^0 = 1)
- Degree at most S - 1
- Coefficients that are powers of 3, hence all positive

**The Mahler measure and height:** The naive height H(F) = max |coeff| = 3^{x-1}. The L^1-norm ||F||_1 = sum 3^{x_{>j}} = (3^x - 1)/2.

For d | F(2), since F(2) > 0, we need F(2) >= d. We computed F(2) <= (3^x - 1) * 2^{S-2}.

The KEY RATIO is:

**F(2) / d ~ 3^x * 2^{S-2} / 2^S = 3^x / 4**

For a cycle to exist, we need F(2)/d = n (integer) satisfying 1 <= n <= 3^x/4.

So the question becomes: **among all polynomials F of the constrained form (x positive coefficients that are consecutive powers of 3, at specific positions determined by a composition), can F(2) be a MULTIPLE of d?**

### 9.3 A promising structural argument (OPEN)

**Claim (to be proved or disproved):** For k >= 3 and S = S_min(x, k), the polynomial F(X) = sum_{r=0}^{x-1} 3^r * X^{B_{x-1-r}} satisfies:

gcd(F(2), 2^S - 3^x) divides some explicit function of k that is smaller than d.

**Approach via resultants:** The resultant Res_X(F(X), X^S - 3^x) is an integer that is divisible by d whenever F(2) is divisible by d (since 2 is a root of X^S - 3^x - d, hence a root of X^S - 3^x modulo d).

Actually: Res_X(F(X), X^S - 3^x) = prod_{alpha : alpha^S = 3^x} F(alpha) = prod F(3^{x/S} * omega_j)

where omega_j are S-th roots of unity.

This resultant is an integer. If we can show that |Res| < d^x (which is the maximum possible when d | F(2)), then we get a contradiction.

**Size estimate:** Each factor |F(alpha)| <= ||F||_1 * max(1, |alpha|)^{deg F} = (3^x-1)/2 * (3^{x/S})^{S-1}.

The product of S factors: |Res| <= ((3^x-1)/2)^S * 3^{x(S-1)/S * S} ... this grows too fast. The naive bound doesn't work.

### 9.4 Directions that remain open

1. **Refined resultant bounds:** Use the STRUCTURE of F (it has only x << S non-zero terms) to get better bounds on the resultant. Sparse polynomial theory (Descartes' rule, Khovanskii) may help.

2. **The Wronskian approach (R165):** The quotient polynomial Q(X) = F(X) / (X^S - 3^x) in Q[X] has specific properties. Its evaluation Q(2) = n (the cycle start). The Wronskian W(F, X^S - 3^x) evaluated at X = 2 gives a relation between n and d.

3. **Height bounds on n:** If n = F(2)/d, and F has constrained form, then n itself satisfies constraints. For example, n < 3^x/4 (from Section 7.3). Combined with lower bounds like n > 2^{40k} (Eliahou), this gives k-dependent contradictions.

4. **The composite structure of d:** Since no single prime factor of d gives N_0 = 0 (proved for k = 3..14), the obstruction MUST come from the interaction of prime factors. The CRT decomposition g ≡ 0 mod p_i for all p_i | d imposes simultaneous constraints. Even though each is individually satisfiable, the JOINT constraint (with the same v, s) may be impossible.

    This is analogous to the Chinese Remainder Theorem creating a "bottleneck": the same polynomial F must vanish modulo all prime factors of d simultaneously, at the same point X = 2. This is a SIMULTANEOUS ROOT condition.

5. **The semigroup approach:** The matrices T_0(s), T_1(s) generate a semigroup in GL_2(Q). The cycle condition requires a specific element of this semigroup to have an integer eigenvector. The structure of this semigroup (is it free? does it satisfy identities?) may provide obstructions.

---

## 10. ASSESSMENT AND CONCLUSION

### What this investigation establishes

- The transfer matrix approach is a CLEAN REFORMULATION but does not by itself provide new obstructions. It reduces to the same n = g(v,s)/d formula.
- The word space / polynomial approach connects corrSum to sparse polynomial evaluation, which is a well-studied area.
- The automata approach is PROVABLY INSUFFICIENT by the ghost cycle paper.
- The resultant approach is promising but naive bounds are too weak.

### The fundamental difficulty

The problem lies at the intersection of:
1. **Arithmetic:** d = 2^S - 3^x has specific prime factorization
2. **Combinatorics:** the composition s constrains which polynomials F arise
3. **Analysis:** the evaluation point X = 2 is specific

No single approach captures all three simultaneously. The modular approach captures (1) but not (2). The polynomial approach captures (2) and (3) but struggles with (1). The automata approach captures (2) but is provably limited.

### Most promising continuation

**The simultaneous root condition (9.4, point 4)** seems the most viable:

For each prime p | d, the set of (v, s) giving F(2) ≡ 0 mod p is non-empty but has specific structure. The INTERSECTION over all primes p | d may be empty due to incompatible structural constraints on (v, s). This would require understanding how the "zero fiber" g^{-1}(0 mod p) depends on p — whether different primes "cut" different parts of the word space W(k, x, S).

This is essentially a **sieving argument on the word space**, combining CRT with the combinatorial structure of valid pairs (v, s).

**Verdict: PISTE OUVERTE.** The word space formulation is correct and well-founded, but does not yet yield a proof. The most promising sub-direction is the simultaneous CRT sieving on the word space, which requires understanding the structure of zero fibers g^{-1}(0 mod p) as subsets of the word space, and proving their intersection is empty for the composite d.

---

## REFERENCES

- Knight (2025): Christoffel words and Collatz cycles
- R162 (this project): Theoreme de Parametrisation Endogene (uniformizer)
- R165 (this project): Wronskien and quotient polynomial
- R160 (this project): Role of the +1
- arXiv:2601.12772: Ghost cycles and Presburger insufficiency
- Eliahou (1993): Lower bounds on cycle starting values
- Steiner (1977): k-cycle non-existence for small k
- Simons & de Weger (2005): Extended k-cycle non-existence
- Mahler measure and sparse polynomial theory: Amoroso-Masser, Bombieri-Vaaler
- Bourgain-Katz-Tao (2004): Sum-product estimates
