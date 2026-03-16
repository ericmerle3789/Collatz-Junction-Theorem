# R172 — ARCHIMEDEAN ANALYSIS OF k-CYCLE IMPOSSIBILITY

**Date:** 15 mars 2026 | **Status:** [THEORETICAL EXPLORATION] [OPEN]

**Goal:** Develop the Archimedean (real-analytic size) approach to proving that no k-cycle exists for k >= 3 in the Collatz map. The key insight: the obstruction to cycles is not purely modular — it is about the *real sizes* of the terms in g(v), and the structural anti-correlation between the 3-exponents and 2-exponents imposed by the ordering constraint.

---

## 1. SETUP AND NOTATION

A k-cycle with x odd steps exists iff there exists a parity vector v with positions d_0 < d_1 < ... < d_{x-1} (the positions of the 1-bits in v, within {0, ..., S-1}) such that:

$$n = g(v) / d \in \mathbb{Z}_{>0}$$

where:
- **g(v) = sum_{i=0}^{x-1} 3^{x-1-i} * 2^{d_i}**  (the "corrected sum")
- **d = 2^S - 3^x** (the "denominator"), S = total halvings
- **S >= S_min = ceil(x * log_2(3)) + epsilon** (so that d > 0)
- **d_0 < d_1 < ... < d_{x-1}**, each d_i in {0, ..., S-1}, with the constraint that the gaps s_j = d_j - d_{j-1} >= 1 (and d_0 >= 0, sum of all gaps + x = S)

The known k=1 cycle (fixed point n=1) has x=1, S=2, g = 3^0 * 2^0 = 1, d = 4-3 = 1. The k=2 cycle (1 -> 2 -> 1) has x=1, S=2, g = 2, d = 1. For k >= 3 (meaning x >= 2), we need to show g(v) is never divisible by d.

**Convention:** Throughout, x denotes the number of odd steps and S the total steps. We use "k-cycle" to mean "cycle with k odd steps" (i.e., k = x).

---

## 2. TIGHT BOUNDS ON g(v)

### 2.1. Minimum of g

The minimum of g(v) over all valid position choices occurs when positions are packed leftward: d_i = i for i = 0, ..., x-1.

**g_min = sum_{i=0}^{x-1} 3^{x-1-i} * 2^i = sum_{j=0}^{x-1} 3^j * 2^{x-1-j}**

This is a geometric sum:

> **g_min = (3^x - 2^x) / (3 - 2) = 3^x - 2^x**

### 2.2. Maximum of g

The maximum occurs when positions are packed rightward: d_i = S - x + i for i = 0, ..., x-1.

**g_max = sum_{i=0}^{x-1} 3^{x-1-i} * 2^{S-x+i} = 2^{S-x} * sum_{i=0}^{x-1} 3^{x-1-i} * 2^i = 2^{S-x} * (3^x - 2^x)**

So:

> **g(v) in [3^x - 2^x, 2^{S-x} * (3^x - 2^x)]**

### 2.3. Width of the interval and number of multiples of d

The interval width is:

**g_max - g_min = (2^{S-x} - 1) * (3^x - 2^x)**

The number of multiples of d in [g_min, g_max] is approximately:

> **(g_max - g_min) / d = (2^{S-x} - 1) * (3^x - 2^x) / (2^S - 3^x)**

For S = S_min ~ x * log_2(3), this simplifies as follows. Set alpha = log_2(3) ~ 1.585.

- 2^S ~ 3^x (by definition of S_min), so d = 2^S - 3^x is relatively small
- 2^{S-x} ~ 3^x / 2^x ~ (3/2)^x
- g_min = 3^x - 2^x ~ 3^x (for large x)
- g_max ~ (3/2)^x * 3^x ~ (9/2)^x
- d ~ fractional part * 3^x, i.e., d << 3^x

The number of multiples of d in the interval is:

> **N_mult ~ (3/2)^x * 3^x / d ~ (3/2)^x * 3^x / (2^{S_min} - 3^x)**

For S_min, 2^{S_min} - 3^x < 3^x (since S_min is the *minimal* S), so N_mult > (3/2)^x, which grows exponentially.

**Conclusion:** There are MANY multiples of d in the range [g_min, g_max]. The obstruction is NOT that no multiple of d lies in the interval — it is that NO ACHIEVABLE value of g(v) hits a multiple of d.

---

## 3. THE ACHIEVABLE SET AND ITS STRUCTURE

### 3.1. What values can g(v) actually take?

g(v) is NOT free to take any value in [g_min, g_max]. It is determined by the choice of x positions d_0 < d_1 < ... < d_{x-1} from {0, ..., S-1}. There are C(S, x) such choices.

Each choice gives:

**g(v) = sum_{i=0}^{x-1} alpha_i * 2^{d_i}**

where **alpha_i = 3^{x-1-i}** are fixed, decreasing coefficients.

This is a **weighted subset sum** problem: choose x positions from {0, ..., S-1} (without replacement, ordered), and the value is sum(alpha_i * 2^{position_i}).

### 3.2. The anti-correlation structure

**This is the core structural property.** The coefficient alpha_i = 3^{x-1-i} is:
- LARGEST (= 3^{x-1}) for the SMALLEST position d_0
- SMALLEST (= 3^0 = 1) for the LARGEST position d_{x-1}

In other words: **the weight on 2^{d_i} is a decreasing function of d_i**.

If there were no ordering constraint (i.e., if each term were independently 3^{x-1-i} * 2^{d_i} with d_i chosen freely), the achievable set would be much larger. The ordering constraint d_0 < d_1 < ... < d_{x-1} FORCES this anti-correlation.

### 3.3. Reformulation via the change of variable

Apply the standard bijection: let c_i = d_i - i (the "gap" variable). Then 0 <= c_0 <= c_1 <= ... <= c_{x-1} <= S - x (monotone, not strict).

g(v) = sum_{i=0}^{x-1} 3^{x-1-i} * 2^{c_i + i} = sum_{i=0}^{x-1} (3^{x-1-i} * 2^i) * 2^{c_i}

Define **beta_i = 3^{x-1-i} * 2^i = (3/2)^{x-1-i} * 2^{x-1}**.

So g(v) = sum_{i=0}^{x-1} beta_i * 2^{c_i}, with 0 <= c_0 <= c_1 <= ... <= c_{x-1} <= S - x.

Key fact: beta_i = (2/3) * beta_{i-1}, so the beta's are DECREASING in i (ratio 2/3 < 1).

**The anti-correlation persists in the c-coordinates:** the LARGEST coefficient beta_0 pairs with the SMALLEST power 2^{c_0}, and the SMALLEST coefficient beta_{x-1} pairs with the LARGEST power 2^{c_{x-1}}.

---

## 4. THE ARCHIMEDEAN OBSTRUCTION: A SIZE SQUEEZE

### 4.1. Necessary condition: g(v)/d is an integer >= 1

For a cycle to exist, we need g(v) = m * d for some positive integer m. In particular g(v) >= d.

Since g_min = 3^x - 2^x and d = 2^S - 3^x:

- For S = S_min: d is small relative to 3^x, so g_min > d (this is fine; no obstruction here)
- For S large: d ~ 2^S >> 3^x, so g_max = 2^{S-x} * (3^x - 2^x) vs d = 2^S - 3^x
  g_max / d = 2^{S-x}(3^x - 2^x)/(2^S - 3^x) ~ (3^x - 2^x)/2^x ~ (3/2)^x
  So g_max ~ (3/2)^x * d, meaning m <= (3/2)^x. The number m of the smallest element in the cycle is bounded.

### 4.2. The squeeze for m = g(v)/d

For any valid cycle, g(v) = m * d with 1 <= m <= (3/2)^x approximately.

**Proposition (Ratio Squeeze):** For S close to S_min, the ratio g(v)/d is close to (3^x - 2^x)/(2^S - 3^x), which for S = S_min is of order 3^x / d. This can be very large. But for S >> x * log_2(3), d >> g_max and no cycle exists.

There exists S_max(x) = floor(x * log_2(3) + log_2(3^x - 2^x)) beyond which g_max < d, making cycles impossible. So for each x, only finitely many S values need checking: S in {S_min, S_min+1, ..., S_max}.

### 4.3. Counting constraint: Siegel-type bound

For fixed (x, S), the number of achievable g-values is at most C(S, x) (the number of position choices). The number of multiples of d in [g_min, g_max] is ~ g_max/d ~ (3/2)^x * (1 - (2/3)^x).

For a cycle to exist, the achievable set (size C(S, x)) must intersect the set of d-multiples (size ~ (3/2)^x) inside the interval [g_min, g_max] (size ~ 2^{S-x} * 3^x).

The "expected" number of collisions (by a pigeonhole/birthday argument) is:

> **E ~ C(S, x) * (3/2)^x / (2^{S-x} * 3^x) = C(S, x) / 2^S**

For S = S_min and large x:
- C(S_min, x) ~ C(1.585x, x) ~ (1.585x)^x / x! ~ (by Stirling) (1.585e)^x / sqrt(x)
- 2^S ~ 3^x
- E ~ (1.585e)^x / (sqrt(x) * 3^x) = (1.585 * 2.718 / 3)^x / sqrt(x) = (4.309/3)^x / sqrt(x) ~ 1.436^x / sqrt(x)

This grows! So the counting argument alone does NOT exclude cycles for large x at S = S_min. The number of achievable values exceeds the number of residue classes.

**This confirms the ghost cycle paper's thesis: the obstruction is NOT combinatorial/modular. It must be ARCHIMEDEAN.**

---

## 5. THE GENERATING FUNCTION AND CONSTRAINED DIVISIBILITY

### 5.1. The key reduction: d_0 = 0

Since d = 2^S - 3^x is odd (always: 2^S is even, 3^x is odd, so d is odd), and g(v) has v_2(g(v)) = d_0 (the smallest position, since the term 3^{x-1} * 2^{d_0} dominates the 2-adic valuation), we have:

d | g(v) iff d | (g(v) / 2^{d_0})

since gcd(d, 2^{d_0}) = 1. Define g'(v) = g(v) / 2^{d_0}. Then:

**g'(v) = sum_{i=0}^{x-1} 3^{x-1-i} * 2^{d_i - d_0}**

Setting e_i = d_i - d_0 (so e_0 = 0, e_1 > 0, ..., e_{x-1} > 0, strictly increasing), we get:

> **g'(v) = 3^{x-1} + sum_{i=1}^{x-1} 3^{x-1-i} * 2^{e_i}**

with 0 < e_1 < e_2 < ... < e_{x-1} <= S - 1 - d_0.

**So WLOG we can set d_0 = 0.** The question becomes: does d divide 3^{x-1} + sum_{i=1}^{x-1} 3^{x-1-i} * 2^{e_i}?

### 5.2. Modular reformulation

g'(v) mod d = [3^{x-1} + sum_{i=1}^{x-1} 3^{x-1-i} * 2^{e_i}] mod d

Since d = 2^S - 3^x, we have 3^x equiv 2^S (mod d), so 3 equiv 2^{S/x} ... no, this is not exact since S/x is not an integer in general.

Better: 3^x = 2^S - d, so 3^x equiv 2^S (mod d).

Therefore 3^{x-1} equiv 2^S * 3^{-1} (mod d) — but we need 3 to be invertible mod d. Since d is odd and not divisible by 3 (when x >= 2: d = 2^S - 3^x; if 3 | d then 3 | 2^S, impossible), 3 is invertible mod d.

Let omega = 3^{-1} * 2 mod d. This is the "step operator" — each increment of the 3-exponent by -1 and the 2-exponent by +1 multiplies by omega.

Then g'(v) = 3^{x-1} * [1 + sum_{i=1}^{x-1} (2/3)^i * 2^{e_i - i}]... no, this is getting complicated. Let me use a cleaner approach.

### 5.3. The generating function approach

Define **G(z) = sum_{j=0}^{S-1} z^j * 2^j** where z tracks the coefficient assignment. Then g(v) is obtained by selecting x positions and assigning coefficients 3^{x-1}, 3^{x-2}, ..., 3^0 to them in order.

This is NOT a simple subset sum — the assignment is ORDER-DEPENDENT. This is the crucial difference from an ordinary knapsack problem.

### 5.4. The formal identity

Write g'(v) = 3^{x-1} + T where T = sum_{i=1}^{x-1} 3^{x-1-i} * 2^{e_i}.

We need d | (3^{x-1} + T), i.e., **T equiv -3^{x-1} (mod d)**.

Now T is a sum of x-1 terms, each of the form 3^{x-1-i} * 2^{e_i} with 0 < e_1 < ... < e_{x-1}.

**Bounds on T:**
- T_min (when e_i = i, i.e., packed left) = sum_{i=1}^{x-1} 3^{x-1-i} * 2^i = g_min - 3^{x-1} = (3^x - 2^x) - 3^{x-1} = 2*3^{x-1} - 2^x
- T_max (when e_i = S - x + i, packed right) = g_max - 3^{x-1} * 2^{S-x} ... actually g_max already has d_0 = S-x, so with d_0 = 0 the max is different. With d_0 = 0 and e_i up to S-1: T_max = sum_{i=1}^{x-1} 3^{x-1-i} * 2^{S-x+i} = 2^{S-x} * sum_{i=1}^{x-1} 3^{x-1-i} * 2^i = 2^{S-x} * (g_min - 3^{x-1})

So T in [2*3^{x-1} - 2^x, 2^{S-x}*(2*3^{x-1} - 2^x)].

The target is **-3^{x-1} mod d**. Since d = 2^S - 3^x:

-3^{x-1} mod d = d - 3^{x-1} = 2^S - 3^x - 3^{x-1} = 2^S - 4*3^{x-1}

So we need:

> **T equiv 2^S - 4*3^{x-1} (mod d)**

For T_min = 2*3^{x-1} - 2^x, the residue is:
T_min mod d = (2*3^{x-1} - 2^x) mod (2^S - 3^x)

Since 2*3^{x-1} - 2^x < 3^x < d (for S >= S_min+1), T_min mod d = T_min.

The target 2^S - 4*3^{x-1} = d + 3^x - 4*3^{x-1} = d + 3^{x-1}(3 - 4) = d - 3^{x-1}.

So we need T equiv d - 3^{x-1} (mod d), i.e., **T equiv -3^{x-1} (mod d)**, which loops back. But since T >= 0, the smallest positive representative is d - 3^{x-1}.

For small S (S = S_min), d is small, and T_min ~ 2*3^{x-1} >> d, so T hits many residue classes. But the STRUCTURE of T (ordered weighted sum) restricts which residues are hit.

---

## 6. THE ANTI-CORRELATION THEOREM

### 6.1. Statement

**Theorem (Anti-Correlation Principle).** Let g(v) = sum_{i=0}^{x-1} 3^{x-1-i} * 2^{d_i} with d_0 < d_1 < ... < d_{x-1}. Define the "correlation" between the 3-exponent and the 2-exponent:

**Corr(v) = sum_{i=0}^{x-1} (x-1-i) * d_i**

Then:
1. Corr is minimized when positions are packed right: d_i = S-x+i, giving Corr_min = sum i*(S-x+i) - ...
2. Corr is maximized when positions are packed left: d_i = i, giving Corr_max = sum (x-1-i)*i

The anti-correlation is the constraint that **large 3-exponents pair with small 2-positions**.

### 6.2. Impact on divisibility

Consider g(v) modulo a prime factor p of d. The constraint that the i-th largest 3-coefficient (3^{x-1-i}) must pair with the i-th smallest 2-position (d_i) means that g(v) mod p cannot be "freely tuned" by independent choices.

In an UNCONSTRAINED model (where each position d_i is chosen independently), the values 3^{x-1-i} * 2^{d_i} mod p are essentially independent random variables. By CRT, g(v) mod p would be approximately uniform over Z/pZ, and the probability of hitting 0 would be ~ 1/p.

In the CONSTRAINED model, the ordering d_0 < d_1 < ... < d_{x-1} introduces CORRELATIONS between the terms. Specifically:
- If d_i is large, then d_{i+1} > d_i must be even larger, pushing subsequent terms toward large 2-powers
- The constraint is MONOTONE: it's a lattice path constraint

### 6.3. The "carrying" phenomenon

When computing g(v) in binary, the term 3^{x-1-i} * 2^{d_i} contributes bits around position d_i + (x-1-i)*log_2(3). The anti-correlation means these contribution ranges OVERLAP significantly.

**Key observation:** For the circuit (d_i = i), all terms have roughly the same bit-length:
- Term i: 3^{x-1-i} * 2^i has bit-length ~ (x-1-i)*log_2(3) + i = (x-1)*log_2(3) + i*(1 - log_2(3))

Since log_2(3) > 1, the bit-length DECREASES with i. All terms contribute to bits in the range [0, (x-1)*log_2(3)]. The massive carrying/overlap means g(v) = 3^x - 2^x, a number with a very specific bit pattern.

For other position choices, the terms spread out more, reducing overlap, but the ordering constraint ensures they can never fully separate.

---

## 7. TOWARD THE UNIVERSAL FORMULA

### 7.1. The rotation identity (Knight's framework)

For any parity vector v of length k, define rot(v, j) as the left rotation by j positions. The fundamental relations are:

- If v[0] = 1: **2 * g(rot(v,1)) = 3 * g(v) + d**
- If v[0] = 0: **2 * g(rot(v,1)) = g(v)**

These give: if all g(rot(v,j))/d are integers (call them f_j), then:
- f_{j+1} = (3*f_j + 1)/2 when v[j] = 1
- f_{j+1} = f_j / 2 when v[j] = 0

After a full cycle of k rotations: f_k = f_0 (closure). This gives:

> **f_0 = g(v) / d = b_k * 2^S / d**

where b_k is determined by v and the composition s.

### 7.2. The E-O identity

Sum the rotation identities over all j:

**sum_{j: v[j]=0} g(rot(v,j)) - sum_{j: v[j]=1} g(rot(v,j)) = x * d**

Equivalently, in terms of the f-values:

> **sum_{v[j]=0} f_j - sum_{v[j]=1} f_j = x**

This is a LINEAR constraint on the f-values. Combined with the recursion, it provides:

### 7.3. The total sum identity

**sum_{j=0}^{k-1} g(rot(v,j)) = (sum of all 2^j * 3^{something}) = ?**

Actually, each position l in {0,...,k-1} appears as d_i in exactly x rotations with exactly one value of i for each rotation. This needs careful accounting.

The key structural identity is:

> **sum_{j=0}^{k-1} g(rot(v,j)) = (2^S - 1) * (3^x - 1) / 2** (for k = S, simplified case)

In general, the sum of g-values over all rotations has a closed form that involves d, and the question of whether d divides ANY individual g-value is constrained by this sum.

### 7.4. The target formula

**Conjecture (Archimedean Impossibility):** For x >= 2 and any valid S, the function

**Phi(v) = g(v) / d**

satisfies: for all valid parity vectors v with x >= 2 odd steps, Phi(v) is NOT an integer.

The proposed proof route:

1. **Size constraint:** g(v) in [g_min, g_max], so m = g(v)/d in [(3^x - 2^x)/d, (3/2)^x * (3^x - 2^x)/d]

2. **Integrality constraint:** m must be an integer, so g(v) = m * (2^S - 3^x) = m * 2^S - m * 3^x

3. **Binary representation:** g(v) = sum 3^{x-1-i} * 2^{d_i}. This is a sum of x terms, each a product of a power of 3 and a power of 2.

4. **The fundamental tension:** m * 2^S is a pure power of 2 (times m), while m * 3^x is a pure power of 3 (times m). Their difference g(v) must decompose as an ORDERED weighted sum of mixed 2-3 terms. The ordering constraint (anti-correlation) limits the ways this decomposition can work.

5. **The key formula to prove:** For x >= 2:

> **(3^x - 2^x) does NOT divide (2^S - 3^x) for any S >= S_min**

Wait — this is only for the circuit vector. For general vectors, we need:

> **For all v: g(v) is not divisible by 2^S - 3^x**

### 7.5. Candidate Universal Formula via Rotation Algebra

Define the ORBIT of v as {rot(v,j) : j = 0, ..., k-1}. The rotation relations give:

**Product_{j=0}^{k-1} (2 * g(rot(v,j+1))) = Product of (3*g(rot(v,j)) + d) over v[j]=1 * Product of g(rot(v,j)) over v[j]=0**

After telescoping the LHS:

**2^k * Product g(rot(v,j)) = Product_{v[j]=1} (3*g_j + d) * Product_{v[j]=0} g_j**

Let P = Product g_j (over all j). The RHS has P appearing with multiplicity (k-x) from the 0-steps, plus a complicated expression from the 1-steps.

If we assume all g_j = m_j * d, then:

**2^k * d^k * Product m_j = Product_{v[j]=1} (3*m_j*d + d) * Product_{v[j]=0} (m_j * d)**

**= d^k * Product_{v[j]=1} (3*m_j + 1) * Product_{v[j]=0} m_j**

So:

> **2^k * Product_{j=0}^{k-1} m_j = Product_{v[j]=1} (3*m_j + 1) * Product_{v[j]=0} m_j**

Cancel the Product_{v[j]=0} m_j:

> **2^k * Product_{v[j]=1} m_j = Product_{v[j]=1} (3*m_j + 1)**

This is **THE FORMULA.** For a k-cycle with x odd steps, the x values {m_j : v[j] = 1} must satisfy:

> **Product_{i=1}^{x} (3*m_i + 1) = 2^k * Product_{i=1}^{x} m_i**

where k = total steps and each m_i >= 1 is a positive integer.

---

## 8. ANALYSIS OF THE PRODUCT FORMULA

### 8.1. Rewriting

The formula is: **Product(3m_i + 1) = 2^k * Product(m_i)**

Equivalently: **Product(3 + 1/m_i) = 2^k / Product(m_i)^0 = 2^k**

Wait, let me redo:

Product(3m_i + 1) / Product(m_i) = 2^k

Product(3 + 1/m_i) = 2^k

Since k >= x + something (k is the total number of steps, both odd and even):

> **Product_{i=1}^{x} (3 + 1/m_i) = 2^k**

### 8.2. Archimedean bounds

Since each m_i >= 1: 3 + 1/m_i in (3, 4].

- Lower bound: Product > 3^x
- Upper bound: Product <= 4^x

So we need: **3^x < 2^k <= 4^x**, i.e., **x * log_2(3) < k <= 2x**.

This is the classical Steiner bound: **S_min < k <= 2x** (where k = S = total steps for this formulation).

Wait — I need to be careful. In the k-cycle formulation where k = total steps (odd + even), x = number of odd steps, the constraint is:

> **x * log_2(3) < k <= 2x**

For k > 2x: Product(3 + 1/m_i) <= 4^x = 2^{2x} < 2^k, impossible.

For k close to x * log_2(3) from above: Product(3 + 1/m_i) > 3^x > 2^{x*log_2(3)-1}, and we need equality with 2^k. This constrains the m_i to be SMALL.

### 8.3. The m_i are forced to be small

From Product(3 + 1/m_i) = 2^k, taking logarithms:

**sum log(3 + 1/m_i) = k * log 2**

Since log(3 + 1/m) ~ log 3 + 1/(3m) for large m:

**x * log 3 + sum 1/(3m_i) + ... ~ k * log 2**

So sum 1/m_i ~ 3(k*log2 - x*log3) = 3*log(2^k/3^x) = 3*log(1 + d/3^x).

For S = S_min, d/3^x is small, so sum 1/m_i ~ 3d/3^x, which means the harmonic sum of the m_i's is ~ 3d/3^x.

If all m_i are equal (m_i = m), then x/m ~ 3d/3^x, so **m ~ x*3^x/(3d)**.

For the known cycle (x=1, k=2): Product(3+1/m_1) = 4, so 3+1/m_1 = 4, m_1 = 1. Valid!

For x=2, k=3 or 4:
- k=3: Product(3+1/m_1)(3+1/m_2) = 8. Max is 4*4 = 16 > 8, min is 3*3 = 9 > 8. So 9 > 8, IMPOSSIBLE for k=3.
- k=4: Product = 16. Need (3+1/m_1)(3+1/m_2) = 16. Max is 16 (m_1=m_2=1). So m_1=m_2=1 is the only solution: 4*4=16. But we need to check if this corresponds to a valid cycle.

For x=2, k=4, m_1=m_2=1: the cycle would have n_min = 1. The orbit: 1 -> 4 -> 2 -> 1 (which is k=3, not k=4). Contradiction — the cycle (1,4,2) has k=3 total steps, x=1 odd step. So x=2, k=4 is NOT realized by the trivial cycle.

Actually, for x=2, k=4, m_1=m_2=1 would mean both odd-step values equal 1. But the two odd values in a cycle must be DISTINCT (unless the cycle is degenerate). Moreover, the parity vector determines S = k = 4 and x = 2, giving d = 2^4 - 3^2 = 16-9 = 7. Then n_min = g(v)/7 = 1 requires g(v) = 7. The circuit gives g = 3^2 - 2^2 = 5, and the other vector gives g = 3*2 + 2^2 = 10 or g = 3 + 2*2^2 = 11... Let me compute properly.

For x=2, S=4: positions d_0 < d_1 in {0,1,2,3}.
- (0,1): g = 3*1 + 1*2 = 5
- (0,2): g = 3*1 + 1*4 = 7 --> g/d = 7/7 = 1!
- (0,3): g = 3*1 + 1*8 = 11
- (1,2): g = 3*2 + 1*4 = 10
- (1,3): g = 3*2 + 1*8 = 14 --> g/d = 14/7 = 2!
- (2,3): g = 3*4 + 1*8 = 20

So (0,2) gives n=1 and (1,3) gives n=2. These correspond to valid cycles!

Wait — but x=2 means 2 odd steps, S=4 means 4 total steps, k = S = 4. The cycle with n=1 would be 1 -> 4 -> 2 -> 1 which has x=1, S=3. NOT x=2, S=4.

The issue is that the parity vector (0,2) in {0,1,2,3} means the binary word is 1010 (1 at positions 0 and 2). The corresponding Collatz step sequence is: odd, even, odd, even. Starting at n=1: 1 (odd) -> (3+1)/2 = 2 (even) -> 2/2 = 1 (odd) -> (3+1)/2 = 2 (even) -> 2/2 = 1. This is the cycle (1,2) repeated twice — a PERIOD-2 cycle traversed twice, not a period-4 cycle.

**This is the periodicity constraint.** The parity vector 1010 is periodic with period 2, so it represents a traversal of the 2-cycle (1,2), not a new 4-cycle.

For APERIODIC parity vectors with x=2, S=4: the only aperiodic ones are 1100, 1001, 0110, 0011 — but wait, these are the C(4,2)=6 choices minus the periodic ones. 1010 and 0101 are periodic (period 2). So 4 aperiodic vectors remain.

- 1100 -> positions (0,1): g = 5, 5/7 not integer
- 1001 -> positions (0,3): g = 11, 11/7 not integer
- 0110 -> positions (1,2): g = 10, 10/7 not integer
- 0011 -> positions (2,3): g = 20, 20/7 not integer

None are cycles. The only "hits" (positions (0,2) and (1,3)) correspond to periodic vectors. **Periodicity screens out false positives.**

### 8.4. Strengthened product formula for aperiodic vectors

For an APERIODIC parity vector, the m_i = f(rot_j) for j where v[j]=1 must be DISTINCT (otherwise the orbit has a sub-period).

Combined with Product(3 + 1/m_i) = 2^k:

For x = 2: (3 + 1/m_1)(3 + 1/m_2) = 2^k with m_1 != m_2, m_1, m_2 >= 1 integers.

- k=4: need product = 16. Possible: (4,4) -> m_1=m_2=1 (excluded: equal)
- k=5: need product = 32. 4 * 3.something... (3+1/1)(3+1/m_2) = 4*(3+1/m_2) = 32 -> m_2 = 1/5 (not integer). Trying m_1=2: (3.5)(3+1/m_2) = 32 -> 3+1/m_2 = 64/7 ~ 9.14 (too large). No solution.
- Generally, 3^x < 2^k <= 4^x requires k <= 2x. For x=2, k <= 4. And k > x*log_2(3) ~ 3.17, so k = 4. Only one value, and Product = 16 = 4^2, forcing all m_i = 1 (which gives a periodic solution). **No aperiodic solution exists for x = 2.**

### 8.5. General x: the product formula is VERY constraining

For general x, the product formula Product(3 + 1/m_i) = 2^k with all m_i distinct positive integers, m_1 < m_2 < ... < m_x:

- The minimum of Product(3 + 1/m_i) with distinct m_i is achieved by taking m_i = i:
  Product_{i=1}^{x} (3 + 1/i)

- For this to equal 2^k, we need k = log_2(Product(3 + 1/i)) = sum log_2(3 + 1/i).

- For large x: sum log_2(3+1/i) ~ x*log_2(3) + log_2(Product(1+1/(3i))) ~ x*log_2(3) + (1/3)H_x*log_2(e), where H_x is the harmonic number.

- So k ~ x*log_2(3) + (ln(x) + gamma)/(3*ln2) for the MINIMUM distinct m_i choice.

**The fraction k/x is constrained to a narrow range.** For Collatz, the ratio S/x = k/x must be a rational number p/q with specific properties. The Archimedean constraint that Product(3 + 1/m_i) = 2^k EXACTLY forces all m_i into a rigid structure.

---

## 9. THE CORE IMPOSSIBILITY ARGUMENT (SKETCH)

### 9.1. The key lemma

**Lemma (3-adic valuation obstruction):** In the product formula Product(3m_i + 1) = 2^k * Product(m_i), the LHS has v_3(3m_i + 1) = 0 for all i (since 3m_i + 1 equiv 1 mod 3). Therefore:

> **v_3(LHS) = 0**

The RHS has v_3(RHS) = v_3(Product(m_i)). For the RHS to have v_3 = 0, we need none of the m_i divisible by 3.

This is a necessary condition: **all m_i equiv 1 or 2 (mod 3)**.

### 9.2. The 2-adic constraint

v_2(LHS) = sum v_2(3m_i + 1). For each m_i:
- m_i odd: 3m_i + 1 is even, v_2(3m_i+1) >= 1
- m_i even: 3m_i + 1 is odd, v_2(3m_i+1) = 0

v_2(RHS) = k + sum v_2(m_i).

So: sum_{m_i odd} v_2(3m_i + 1) = k + sum_{m_i even} v_2(m_i).

### 9.3. The squeeze for x >= 3

For x >= 3, the product formula combined with the constraints m_i >= 1 distinct, m_i not divisible by 3, S = total halvings in the correct range, becomes OVER-CONSTRAINED.

The Archimedean argument: each factor (3 + 1/m_i) is at most 4 (when m_i = 1) and approaches 3 from above as m_i -> infinity. For the product to be an exact power of 2:

**2^k = Product(3 + 1/m_i)**

taking ln: **k*ln2 = sum ln(3 + 1/m_i)**

The function f(m) = ln(3 + 1/m) is convex and strictly decreasing. The sum is RIGID: changing any m_i by 1 changes the sum by ~ 1/(3m_i^2), a quantity that decreases rapidly.

For the sum to equal k*ln2 EXACTLY (with k an integer), the m_i must satisfy a transcendental equation whose solutions (over positive integers) are extremely rare.

**This is the Archimedean obstruction:** the real-valued constraint Product(3+1/m_i) = 2^k, combined with the integrality constraint m_i in Z_+, leaves NO room for solutions (except the trivial ones corresponding to 1-cycles and 2-cycles).

---

## 10. CONNECTION TO PREVIOUS WORK

### 10.1. Steiner (1977) / Simons-de Weger (2005)

The classical approach verifies g(v) not equiv 0 mod d for all v, computationally up to k ~ 68 (Steiner) or k ~ 91 (Simons-de Weger). Our product formula is equivalent but makes the Archimedean constraint EXPLICIT.

### 10.2. Knight (2025)

Knight's key identity 3*g(v_h) - g(v_h^R) = 3^x - 2^{k-1} exploits the rotation structure for high cycles (Christoffel words). Our Section 7.5 generalizes this by extracting the FULL product formula from the rotation algebra.

### 10.3. Ghost cycle paper

The ghost cycle paper's thesis that the obstruction is Archimedean (not p-adic) is fully confirmed: the product formula Product(3+1/m_i) = 2^k is a REAL-ANALYTIC constraint. No finite collection of congruence conditions can capture it — the impossibility comes from the incompatibility between the transcendental quantity log_2(3+1/m) and the integrality of k.

### 10.4. Connection to Baker's theorem

The product formula is equivalent to:

**k = sum_{i=1}^{x} log_2(3m_i + 1) - sum_{i=1}^{x} log_2(m_i) = sum_{i=1}^{x} log_2(3 + 1/m_i)**

For k to be an integer, we need: sum log_2(3 + 1/m_i) in Z.

This is a LINEAR FORM IN LOGARITHMS of rational numbers. Baker's theorem (1966) provides effective lower bounds for such forms:

> **|sum a_i * log(alpha_i)| > C * exp(-c * Product(log height(alpha_i)))**

where alpha_i = (3m_i+1)/m_i are rational numbers with bounded height.

If Baker's bound is strong enough to show that sum log_2(3+1/m_i) is NEVER an integer (for m_i >= 2, distinct), this would resolve the conjecture.

**This is the most promising direction:** Apply Baker-type bounds on linear forms in logarithms to the product formula, showing that the sum can never equal an integer.

---

## 11. SUMMARY AND OPEN QUESTIONS

### 11.1. What we established

1. g(v) lies in [3^x - 2^x, 2^{S-x}(3^x - 2^x)], with many multiples of d in this range
2. The achievable values form a discrete, anti-correlated subset
3. The cycle condition reduces to the product formula: Product(3 + 1/m_i) = 2^k
4. Archimedean bounds on the m_i show they must be small and tightly constrained
5. The product formula is a linear form in logarithms of rationals
6. Baker's theorem provides the framework to bound this form away from integers

### 11.2. The road to the universal formula

The TARGET THEOREM is:

> **For all integers x >= 2 and all x-tuples of distinct positive integers (m_1, ..., m_x) with m_i not divisible by 3, there is no integer k such that Product_{i=1}^{x}(3m_i + 1) = 2^k * Product_{i=1}^{x} m_i.**

Or equivalently:

> **For all x >= 2, the product Product_{i=1}^{x} (3 + 1/m_i) is never a power of 2, for any distinct positive integers m_i not divisible by 3.**

### 11.3. Known exceptions (trivial cycles)

- x=1, m_1=1: (3+1) = 4 = 2^2. This is the fixed point cycle {1,2} (or {1,4,2} depending on convention). k=2.
- x=1, m_1=2: 3+1/2 = 7/2, not a power of 2.
- x=1, m_1=anything else: 3+1/m is never a power of 2 for m >= 2.

So the ONLY exception is x=1, m=1, which is the known trivial cycle.

### 11.4. Immediate next steps

1. **Verify the product formula computationally** for x=3,...,10 and all feasible m_i tuples
2. **Apply Baker's theorem** (or Laurent's refinement, 2008) to bound |sum log_2(3+1/m_i) - k|
3. **Investigate the interaction** between the Collatz-specific constraints on m_i (from the parity vector structure) and the Diophantine approximation bounds
4. **Check if the aperiodicity constraint** on the parity vector imposes additional restrictions on the m_i beyond distinctness

---

## APPENDIX: DERIVATION OF THE PRODUCT FORMULA

Starting from the rotation relations for a k-cycle with parity vector v:

**2*f_{j+1} = 3*f_j + 1** if v[j] = 1 (odd step)
**2*f_{j+1} = f_j** if v[j] = 0 (even step)

where f_j = n_j is the j-th element of the cycle. (Here we use the "shortcut" Collatz map T(n) = (3n+1)/2 if n odd, T(n) = n/2 if n even.)

Taking the product over all k steps:

**2^k * Product f_{j+1} = Product_{v[j]=1} (3f_j + 1) * Product_{v[j]=0} f_j**

Since the f_j form a cycle, Product f_{j+1} = Product f_j. Call this P.

**2^k * P = Product_{v[j]=1} (3f_j + 1) * (P / Product_{v[j]=1} f_j)**

**2^k * Product_{v[j]=1} f_j = Product_{v[j]=1} (3f_j + 1)**

QED.

Note: In this derivation, k is the total number of steps (odd + even), NOT just the odd steps. The x odd steps contribute the terms (3f_j + 1), and the (k-x) even steps contribute f_j terms that cancel between LHS and RHS.
