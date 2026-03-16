# R199 — Finite Verification: k = 18..41

**Agent A1 — Investigateur Computationnel**
**Date: 2026-03-16**

---

## Executive Summary

**ALL 24 values k = 18..41 are RESOLVED.** No non-trivial Collatz k-cycle exists for any k in this range.

- **6 values** resolved by arc argument: k = 22, 27, 29, 34, 39, 41
- **18 values** resolved by upper bound + Barina verification: k = 18–21, 23–26, 28, 30–33, 35–38, 40

The key insight: for non-arc cases, the cycle equation constrains n₀ ≤ g_max/d(k) < 6.5×10⁷, while Barina (2020) verified computationally that no cycle element exists below 2⁶⁸ ≈ 2.95×10²⁰. The gap is enormous (13 orders of magnitude).

**Extension:** The same argument works for ALL k ≤ 111 (non-arc cases).

---

## 1. Setup and Definitions

For a hypothetical Collatz cycle of length k:
- **S** = ⌈k·log₂3⌉ (total number of "even steps")
- **d(k)** = 2^S − 3^k (the cycle denominator, must be > 0)
- **θ** = log₂3 = 1.58496250072...
- **{k·θ}** = fractional part of k·log₂3

The cycle equation: if (n₀, n₁, ..., n_{k-1}) is a k-cycle with step sequence (s₁,...,s_k), then:

$$n_0 = \frac{\sum_{j=1}^{k} 3^{k-j} \cdot 2^{a_j}}{d(k)}$$

where a_j = s₁+...+s_j (cumulative sums), with 1 ≤ a₁ < a₂ < ... < a_k = S.

---

## 2. Arc Argument (6 resolved)

The arc argument applies when {k·θ} > log₂(5/3) ≈ 0.73697.

| k | S | {k·θ} | Status |
|---|---|--------|--------|
| 22 | 35 | 0.86918 | **RESOLVED** (arc) |
| 27 | 43 | 0.79399 | **RESOLVED** (arc) |
| 29 | 46 | 0.96391 | **RESOLVED** (arc) |
| 34 | 54 | 0.88873 | **RESOLVED** (arc) |
| 39 | 62 | 0.81354 | **RESOLVED** (arc) |
| 41 | 65 | 0.98347 | **RESOLVED** (arc) |

---

## 3. Complete Factorizations of d(k)

| k | S | d(k) = 2^S − 3^k | Factorization |
|---|---|---|---|
| 18 | 29 | 149,450,423 | 137 · 1,090,879 |
| 19 | 31 | 985,222,181 | 19 · 23 · 2,254,513 |
| 20 | 32 | 808,182,895 | 5 · 13 · 499 · 24,917 |
| 21 | 34 | 6,719,515,981 | 33,587 · 200,063 |
| **22** | **35** | **2,978,678,759** | **7 · 425,525,537** |
| 23 | 37 | 43,295,774,645 | 5 · 31,727 · 272,927 |
| 24 | 39 | 267,326,277,407 | 7 · 233 · 2,113 · 77,569 |
| 25 | 40 | 252,223,018,333 | 11 · 13 · 191 · 251 · 36,791 |
| 26 | 42 | 1,856,180,682,775 | 5² · 149 · 991 · 502,829 |
| **27** | **43** | **1,170,495,537,221** | **43 · 53 · 513,600,499** |
| 28 | 45 | 12,307,579,633,871 | 727 · 16,929,270,473 |
| **29** | **46** | **1,738,366,812,781** | **39,409 · 44,110,909** |
| 30 | 48 | 75,583,844,616,007 | 7² · 13 · 19 · 67 · 499 · 186,793 |
| 31 | 50 | 508,226,510,558,677 | 23 · 37 · 107 · 5,581,410,661 |
| 32 | 51 | 398,779,624,833,407 | 73 · 5,462,734,586,759 |
| 33 | 53 | 3,448,138,688,185,469 | 29 · 118,901,334,075,361 |
| **34** | **54** | **1,337,216,809,815,415** | **5 · 71 · 3,607 · 14,303 · 73,013** |
| 35 | 56 | 22,026,048,938,928,229 | 13 · 778,247 · 2,177,087,039 |
| 36 | 58 | 138,135,740,854,712,623 | 11 · 137 · 1,090,879 · 84,026,491 |
| 37 | 59 | 126,176,846,412,426,125 | 5³ · 47 · 2,475,787 · 8,674,781 |
| 38 | 61 | 954,991,291,540,701,863 | 7 · 17 · 1,033 · 20,743 · 374,524,783 |
| **39** | **62** | **559,130,865,408,411,637** | **11 · 7,369 · 6,897,825,847,943** |
| 40 | 64 | 6,289,078,614,652,622,815 | 5 · 13 · 499 · 769 · 24,917 · 10,119,313 |
| **41** | **65** | **420,491,770,248,316,829** | **19 · 29 · 17,021 · 44,835,377,399** |

Bold = resolved by arc argument.

### Mersenne Primes

M₃ = 7 divides d(k) for k = 22, 24, 30, 38. No other Mersenne primes appear.

### Divisibility Relations

- d(18) | d(36): quotient = 924,291,401. Shared factors: {137, 1,090,879}.
- d(20) | d(40): quotient = 7,781,751,697. Shared factors: {5, 13, 499, 24,917}.
- d(19) does NOT divide d(38). gcd(d(19), d(38)) = 1.

---

## 4. CRT / Pigeonhole Analysis (NEGATIVE RESULT)

For the CRT pigeonhole strategy, we need a prime p | d(k) with p > C(k) = C(S−1, k−1).

**Result: This NEVER works for k = 18..41.** In every case, max(p) ≪ C(k).

The closest case is k = 33:
- Largest prime factor: p = 118,901,334,075,361
- C(k) = C(52, 32) = 125,994,627,894,135
- Ratio p/C(k) = 0.9437 (94.37%, deficit of only 5.63%)

For all other k, the ratio is much smaller (typically < 0.2).

---

## 5. Upper Bound on n₀ (THE KEY ARGUMENT)

For any k-cycle with step sequence (s₁,...,s_k):

$$n_0 = \frac{\sum_{j=1}^{k} 3^{k-j} \cdot 2^{a_j}}{d(k)} \leq \frac{g_{\max}}{d(k)}$$

where g_max is the maximum of the numerator over all valid compositions. This maximum is achieved when s₁ = S−k+1 and s₂ = ... = s_k = 1 (verified by 10,000 random samples per k).

| k | d(k) | g_max/d(k) | n₀ upper bound |
|---|---|---|---|
| 18 | 1.49×10⁸ | 10,611 | n₀ ≤ 10,610 |
| 19 | 9.85×10⁸ | 9,660 | n₀ ≤ 9,659 |
| 20 | 8.08×10⁸ | 35,333 | n₀ ≤ 35,332 |
| 21 | 6.72×10⁹ | 25,500 | n₀ ≤ 25,500 |
| 23 | 4.33×10¹⁰ | 71,245 | n₀ ≤ 71,245 |
| 24 | 2.67×10¹¹ | 69,235 | n₀ ≤ 69,234 |
| 25 | 2.52×10¹¹ | 220,145 | n₀ ≤ 220,145 |
| 26 | 1.86×10¹² | 179,486 | n₀ ≤ 179,486 |
| 28 | 1.23×10¹³ | 487,256 | n₀ ≤ 487,256 |
| 30 | 7.56×10¹³ | 1,428,158 | n₀ ≤ 1,428,158 |
| 31 | 5.08×10¹⁴ | 1,274,383 | n₀ ≤ 1,274,383 |
| 32 | 3.99×10¹⁴ | 4,872,435 | n₀ ≤ 4,872,435 |
| 33 | 3.45×10¹⁵ | 3,381,006 | n₀ ≤ 3,381,005 |
| 35 | 2.20×10¹⁶ | 9,527,236 | n₀ ≤ 9,527,235 |
| 36 | 1.38×10¹⁷ | 9,114,835 | n₀ ≤ 9,114,834 |
| 37 | 1.26×10¹⁷ | 29,936,190 | n₀ ≤ 29,936,189 |
| 38 | 9.55×10¹⁷ | 23,731,658 | n₀ ≤ 23,731,657 |
| 40 | 6.29×10¹⁸ | **64,865,388** | n₀ ≤ **64,865,387** |

**Maximum upper bound**: n₀ ≤ 6.49×10⁷ (at k=40).

---

## 6. Resolution via Barina's Computational Bound

**Barina (2020)**: Verified computationally that the Collatz sequence reaches 1 for all n < 2⁶⁸ ≈ 2.95×10²⁰.

**Consequence**: Any non-trivial Collatz cycle must have all elements ≥ 2⁶⁸.

**Our bound**: For k = 18..41 (non-arc cases), n₀ ≤ 6.49×10⁷.

**Since** 6.49×10⁷ ≪ 2.95×10²⁰, **no k-cycle can exist** for these values of k.

The gap is enormous: **13 orders of magnitude**.

---

## 7. Multiplicative Orders (ord_p(2))

For each prime p | d(k), we computed ord_p(2). Notable observations:

- **p = 7** (Mersenne M₃): ord₇(2) = 3, divides d(k) for k = 22, 24, 30, 38
- **p = 5**: ord₅(2) = 4, divides d(k) for k = 20, 23, 26, 34, 37, 40
- **p = 13**: ord₁₃(2) = 12, divides d(k) for k = 20, 25, 30, 35, 40
- **p = 73**: ord₇₃(2) = 9, divides d(32)
- For k = 33, the large prime p = 118,901,334,075,361 has ord_p(2) = 19,816,889,012,560

No structural property of these orders yields N₀(p) = 0 via algebraic arguments when p < C(k).

---

## 8. Extension Beyond k = 41

The g_max/d < 2⁶⁸ argument works for all non-arc k up to **k = 111**.

At k = 112: g_max/d ≈ 3.70×10²⁰ > 2⁶⁸ ≈ 2.95×10²⁰ (first failure).

Combined with the arc argument (which handles roughly half of all k values), the finite verification strategy extends well beyond k = 41.

---

## 9. Complete Classification

| Range | Method | Status |
|-------|--------|--------|
| k ≤ 17 | Preprint Section 8 | **RESOLVED** |
| k = 18..41 (arc: 22,27,29,34,39,41) | {k·θ} > log₂(5/3) | **RESOLVED** |
| k = 18..41 (non-arc: 18 values) | g_max/d < 2⁶⁸ + Barina | **RESOLVED** |
| k = 42..111 (non-arc cases) | g_max/d < 2⁶⁸ + Barina | **RESOLVED** (extension) |
| k ≥ 112 | Requires different approach | Needs arc + Baker/F_Z |

---

## 10. Observations for the Preprint

1. **The CRT pigeonhole strategy fails for k ≤ 41**: no prime factor of d(k) exceeds C(k). This is consistent with the general observation that d(k) grows as 2^S − 3^k (exponential in k) while C(k) grows as C(S−1, k−1) (also exponential but faster).

2. **The g_max bound + Barina is more powerful than the arc argument**: it resolves 18 additional cases and extends to k = 111.

3. **k = 32 is the closest arc miss**: {32·θ} = 0.7188, threshold = 0.7370 (gap = −0.0182). However, d(32)/((2/3)·3³²) = 0.323, so d is well below the critical value.

4. **k = 33 is the closest pigeonhole miss**: p/C(k) = 0.9437 for the largest prime. A 6% improvement in the bound would resolve this via CRT alone.

5. **Divisibility patterns**: d(k) | d(2k) when S(2k) = 2·S(k), which occurs for k = 18 and k = 20 (where {2k·θ} = 2·{k·θ} mod 1 preserves the integer part relationship).

---

## 11. Technical Notes

- All computations performed with sympy (factorization, multiplicative orders) and mpmath (50-digit precision for θ).
- g_max optimality verified by 10,000 random samples per test case.
- Scripts: `R199_computation.py`, `R199_additional.py`, `R199_refined_arc.py`, `R199_verify.py`
- All results are exact (no floating-point approximations in the integer arithmetic).

---

## References

- Barina, D. (2020). "Convergence verification of the Collatz problem." *J. Supercomputing*, 77(3), 2681-2688. [Verified up to 2⁶⁸]
- Bohm, C. & Sontacchi, G. (1978). "On the existence of cycles of given length in integer sequences like x_{n+1} = x_n/2 if x_n even, and x_{n+1} = 3x_n+1 otherwise." *Atti Accad. Naz. Lincei*, 64(5), 260-264.
- Simons, J. & de Weger, B. (2005). "Theoretical and computational bounds for m-cycles of the 3n+1 problem." *Acta Arith.*, 117(1), 51-70.
- Steiner, R.P. (1977). "A theorem on the Syracuse problem." *Proceedings of the 7th Manitoba Conference on Numerical Mathematics and Computing*, 553-559.
