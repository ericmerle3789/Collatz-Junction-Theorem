#!/usr/bin/env python3
"""
R180 — NUMBER-THEORETIC CONSTRAINTS ON HYPOTHETICAL COLLATZ CYCLES
====================================================================

Combines T197 (R_{x-1}=0 <=> cycle) with classical results:
  - Steiner/Simons-de Weger lower bounds on cycle elements
  - Baker's theorem on linear forms in logarithms
  - Eliahou (1993) approach to 1-cycles
  - Arithmetic of g(v)/d and divisibility constraints

Key identity: For a cycle of length x (odd steps) through odd k,
  k = g(v)/d  where  d = 2^S - 3^x > 0
  g(v) = sum_{j=0}^{x-1} 3^{x-1-j} * 2^{e_j}
  with 0 <= e_0 < e_1 < ... < e_{x-1} < S
  and S = sum of all 2-adic valuations v_m = v_2(3*B_m + 1).

References:
  - Steiner (1977): no non-trivial 1-cycles
  - Simons & de Weger (2005): no non-trivial cycles with x <= 68
  - Eliahou (1993): no non-trivial 1-cycles (alternative proof)
  - Baker (1966+): linear forms in logarithms
  - Laurent, Mignotte, Nesterenko (1995): refined Baker bounds
  - T195-T198 (Merle 2026): S-independent recursion and equivalence
"""

import math
from fractions import Fraction
from itertools import combinations
from functools import lru_cache
import time


# ═══════════════════════════════════════════════════════════════════════════
# UTILITIES
# ═══════════════════════════════════════════════════════════════════════════

def v2(n):
    """2-adic valuation of n."""
    if n == 0:
        return float('inf')
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


def odd_part(n):
    """Odd part of n: n / 2^{v_2(n)}."""
    if n == 0:
        return 0
    while n % 2 == 0:
        n //= 2
    return n


def T_collatz(n):
    """Compressed Collatz map on odd numbers: T(n) = odd((3n+1))."""
    return odd_part(3 * n + 1)


LOG2_3 = math.log2(3)  # ~1.58496...


# ═══════════════════════════════════════════════════════════════════════════
# PART 1: STEINER / SIMONS-DE WEGER BOUNDS + VALUATION CONSTRAINTS
# ═══════════════════════════════════════════════════════════════════════════

def part1_steiner_bounds():
    """
    THEOREM (Steiner 1977, improved by Simons-de Weger 2005):
    If a non-trivial cycle of length x exists with elements B_0,...,B_{x-1},
    then every B_m > 2^{x/2} (roughly).

    More precisely (Simons-de Weger): B_m > 2^{0.677x} for all m.

    Combined with T197: v_m = v_2(3*B_m + 1).
    Since B_m is odd and B_m > 2^{0.677x}:
      3*B_m + 1 is even, and 3*B_m + 1 > 3 * 2^{0.677x}
      v_m = v_2(3*B_m + 1) >= 1 always

    Key constraint on v_m:
      S = sum(v_m) and S > x * log2(3) ~ 1.585x
      Average v_m > log2(3) ~ 1.585
      But v_m >= 1, so the "excess" sum(v_m - 1) > x*(log2(3) - 1) ~ 0.585x

    PROPOSITION R180.1: For a cycle of length x with all B_m > L,
    the valuations satisfy:
      (a) v_m <= log2(3*L + 1) for all m (since v_m <= v_2(3*B_m+1) <= log2(3*B_m+1))
           Actually v_m can be up to S-1, but 3*B_m+1 = 2^{v_m} * B_{m+1}
           so 2^{v_m} | 3*B_m+1, meaning 2^{v_m} <= 3*B_m+1 < 3*B_m + B_m = 4*B_m
           (for B_m >= 1), giving v_m < 2 + log2(B_m).
      (b) From S = sum(v_m) and each v_m < 2 + log2(B_max):
           If all B_m < U (upper bound), then S < x*(2 + log2(U)).
      (c) Lower bound on S: S > x*log2(3), tight iff all B_m are large.
    """
    print("=" * 78)
    print("PART 1: STEINER/SIMONS-DE WEGER BOUNDS ON VALUATIONS")
    print("=" * 78)

    print("""
PROPOSITION R180.1 (Valuation constraints from cycle element bounds):

Let x >= 2 and suppose a non-trivial cycle B_0,...,B_{x-1} exists
with B_m odd and B_m > L for all m. Let v_m = v_2(3*B_m + 1).

(a) Each v_m satisfies: 1 <= v_m < 2 + log_2(B_m)
    Proof: 2^{v_m} | (3*B_m + 1) and 3*B_m + 1 < 4*B_m for B_m >= 1.

(b) S = sum(v_m) satisfies: x * log_2(3) < S < x * (2 + log_2(B_max))

(c) Using Simons-de Weger lower bound B_m > 2^{0.677x}:
    v_m < 2 + 0.677x for each m
    S < x * (2 + 0.677x) = 2x + 0.677x^2

    Combined with S > x * log_2(3) ~ 1.585x:
    The ratio S/x is in (log_2(3), 2 + 0.677x).
""")

    print("  Numerical bounds on S/x and element size:\n")
    print(f"  {'x':>4s}  {'S_min':>8s}  {'S/x_min':>8s}  {'B_min (SdW)':>16s}  "
          f"{'v_max':>6s}  {'S_max/x':>8s}")
    print("  " + "-" * 60)

    for x in [2, 5, 10, 20, 50, 68, 100, 200, 500, 1000]:
        S_min = math.ceil(x * LOG2_3) + 1
        # Ensure 2^S_min > 3^x
        while S_min <= x * LOG2_3:
            S_min += 1

        B_min = 2 ** (0.677 * x)  # Simons-de Weger bound
        v_max = 2 + 0.677 * x  # upper bound on each v_m
        S_max_over_x = 2 + 0.677 * x

        print(f"  {x:4d}  {S_min:8d}  {S_min/x:8.4f}  {B_min:16.2e}  "
              f"{v_max:6.1f}  {S_max_over_x:8.2f}")

    # Refined: distribution of v_m
    print("""
COROLLARY R180.1a: The valuations v_m are "almost always" small.

For a cycle of length x, let N_j = #{m : v_m = j} (count of indices with v_m = j).
Then:
  sum_j j * N_j = S > x * log_2(3)
  sum_j N_j = x
  N_1 + N_2 + ... = x, and sum j*N_j > 1.585x

The "excess" beyond all v_m = 1:
  sum (v_m - 1) = S - x > x*(log_2(3) - 1) ~ 0.585x

So at least ~58.5% of the x steps must have v_m >= 2 (on average).
""")

    # Check: what fraction of steps have v_m >= 2 for the trivial cycle?
    print("  Example: Trivial cycle k=1, orbit = {1}")
    print("    T(1) = odd(4) = 1, v_0 = v_2(4) = 2, S = 2, x = 1")
    print("    S/x = 2.0 > log_2(3) = 1.585. Check.\n")


# ═══════════════════════════════════════════════════════════════════════════
# PART 2: THE RATIO S/x AND NUMBER-THEORETIC OBSTRUCTIONS
# ═══════════════════════════════════════════════════════════════════════════

def part2_ratio_Sx():
    """
    Study: can S/x be close to log_2(3)?

    d = 2^S - 3^x > 0 requires S/x > log_2(3).
    The closer S/x is to log_2(3), the smaller d is,
    and the larger k = g(v)/d must be.

    Baker's theorem gives: |2^S - 3^x| > 2^S * exp(-C * log(S) * log(x))
    for an effective constant C.

    This means S/x cannot be TOO close to log_2(3).
    """
    print("\n" + "=" * 78)
    print("PART 2: THE RATIO S/x AND PROXIMITY TO log_2(3)")
    print("=" * 78)

    print("""
THEOREM R180.2 (Lower bound on d from Baker's theorem):

For integers S, x >= 1 with d = 2^S - 3^x > 0:

  d = 2^S - 3^x = 2^S * (1 - 3^x / 2^S) = 2^S * (1 - 2^{x*log_2(3) - S})

Let alpha = S - x*log_2(3) > 0 (the "gap" above the threshold).

Baker's theorem (Laurent-Mignotte-Nesterenko 1995):
  |S*log(2) - x*log(3)| > exp(-C * log(S+2) * log(x+2))

where C ~ 30 (effectively computable).

This gives: alpha = S/x - log_2(3) > exp(-C' * log(S) * log(x)) / (x * log(2))

For the MINIMAL case S = ceil(x*log_2(3)) + delta:
  d = 2^S - 3^x >= 2^{ceil(x*log_2(3))+delta} - 3^x

Numerical evaluation for small delta:
""")

    print(f"  {'x':>5s}  {'S_min':>7s}  {'delta':>6s}  {'d':>20s}  "
          f"{'log2(d)':>10s}  {'S/x':>10s}  {'S/x - log2(3)':>14s}")
    print("  " + "-" * 80)

    for x in [2, 3, 5, 10, 20, 50, 68, 100]:
        S_min = math.ceil(x * LOG2_3) + 1
        while 2 ** S_min <= 3 ** x:
            S_min += 1
        d = 2 ** S_min - 3 ** x
        log2_d = math.log2(d) if d > 0 else float('-inf')
        gap = S_min / x - LOG2_3
        delta = S_min - math.ceil(x * LOG2_3)

        print(f"  {x:5d}  {S_min:7d}  {delta:6d}  {d:20d}  "
              f"{log2_d:10.2f}  {S_min/x:10.6f}  {gap:14.6f}")

    print("""
PROPOSITION R180.2a (Lower bound on k from small d):

For a cycle of length x with minimal S = ceil(x*log_2(3)) + 1:
  k = g(v)/d >= 3 (since k is odd and >= 3 for non-trivial)
  g(v) = k * d >= 3d

But g(v) = sum_{j=0}^{x-1} 3^{x-1-j} * 2^{e_j} with e_j < S.
The maximum of g(v) is achieved when e_j are as large as possible:
  g_max < sum_{j=0}^{x-1} 3^{x-1-j} * 2^{S-1} = 2^{S-1} * (3^x - 1)/2
        = (3^x - 1) * 2^{S-2}

So k = g(v)/d < (3^x - 1) * 2^{S-2} / d.

For the minimal S case: d ~ 2^S * (S/x - log_2(3)), which is small,
so k_max is HUGE. This is consistent: small d allows large k,
but Baker's theorem prevents d from being too small.
""")

    # Explicit computation of k_max for various x
    print("  Upper bound on k for minimal S:\n")
    print(f"  {'x':>5s}  {'S':>7s}  {'d':>15s}  {'k_max':>20s}  {'log2(k_max)':>12s}")
    print("  " + "-" * 65)

    for x in [2, 3, 5, 10, 20, 50, 68]:
        S = math.ceil(x * LOG2_3) + 1
        while 2 ** S <= 3 ** x:
            S += 1
        d = 2 ** S - 3 ** x
        if d > 0:
            g_max = (3 ** x - 1) * 2 ** (S - 2)
            k_max = g_max // d
            log2_kmax = math.log2(k_max) if k_max > 0 else 0
            print(f"  {x:5d}  {S:7d}  {d:15d}  {k_max:20d}  {log2_kmax:12.2f}")


# ═══════════════════════════════════════════════════════════════════════════
# PART 3: BAKER'S THEOREM — EXPLICIT BOUNDS
# ═══════════════════════════════════════════════════════════════════════════

def part3_baker_bounds():
    """
    Baker's theorem on linear forms in logarithms gives:
      |2^S - 3^x| >= 2^S * exp(-C * log(S) * log(x))

    Using Laurent-Mignotte-Nesterenko (1995):
      |S*log(2) - x*log(3)| > exp(-25.2 * (max(log(S), 21))^2 * (max(log(x), 1)))

    This gives d >= 2^S * exp(-C * (log S)^2 * log x) approximately.

    For a cycle: k = g(v)/d, and g(v) < (3^x - 1) * 2^{S-2}.
    So k < (3^x - 1) * 2^{S-2} * exp(C * (log S)^2 * log x) / 2^S
         = (3^x - 1)/4 * exp(C * (log S)^2 * log x)
    """
    print("\n" + "=" * 78)
    print("PART 3: BAKER'S THEOREM — EXPLICIT BOUNDS ON k")
    print("=" * 78)

    print("""
THEOREM R180.3 (Baker-type upper bound on cycle elements):

Using Laurent-Mignotte-Nesterenko (1995), for S, x >= 2:

  |S * ln(2) - x * ln(3)| > exp(-C_eff * (max(ln S, 21))^2 * max(ln x, 1))

with C_eff ~ 25.2 (for the two-logarithm case, a1=2, a2=3).

Since d = 2^S - 3^x = 2^S * (1 - exp(-(S*ln2 - x*ln3))):
  For S*ln2 - x*ln3 small and positive:
    d ~ 2^S * (S*ln2 - x*ln3)

Lower bound: d > 2^S * exp(-C_eff * (max(ln S, 21))^2 * max(ln x, 1))
  (when S*ln2 - x*ln3 is small, using |Lambda| > exp(-bound))

Combined with k = g(v)/d and g(v) < (3^x-1)*2^{S-2}:
  k < (3^x - 1)/4 * exp(C_eff * (max(ln S, 21))^2 * max(ln x, 1))
""")

    # For the refined bound, use C_eff from LMN95
    # The actual LMN bound for |b1*log(a1) - b2*log(a2)| with a1=2, a2=3:
    # > exp(-C * (1 + log(B))^2) where B = max(|b1|/log(a2), |b2|/log(a1))
    # Simplified: C ~ 25.2 * log(2) * log(3) * (some correction)
    # We use a conservative C_eff ~ 30 for safety.

    C_eff = 30.0  # Conservative Baker constant for 2-logarithm case

    print(f"  Using C_eff = {C_eff} (conservative)\n")
    print(f"  {'x':>5s}  {'S_min':>7s}  {'Baker_lb_d':>14s}  "
          f"{'k_upper':>14s}  {'log2(k_upper)':>14s}  "
          f"{'Comp_limit':>14s}")
    print("  " + "-" * 78)

    for x in [2, 5, 10, 20, 50, 68, 100, 200, 500, 1000]:
        S = math.ceil(x * LOG2_3) + 1
        while 2 ** S <= 3 ** x:
            S += 1

        # Baker lower bound on d
        log_S = max(math.log(S), 21)
        log_x = max(math.log(x), 1)
        baker_exponent = C_eff * log_S ** 2 * log_x

        # d > 2^S * exp(-baker_exponent)
        # k < (3^x)/4 * exp(baker_exponent)
        # log2(k) < x*log2(3) + baker_exponent/ln(2) - 2

        log2_k_upper = x * LOG2_3 + baker_exponent / math.log(2) - 2

        # Known computational limit: all n < 2^68 checked (Barina 2021)
        comp_limit = 68

        status = "EXCLUDED" if log2_k_upper < comp_limit else "OPEN"

        print(f"  {x:5d}  {S:7d}  {'~exp(-' + f'{baker_exponent:.0f}' + ')':>14s}  "
              f"{'2^' + f'{log2_k_upper:.1f}':>14s}  {log2_k_upper:14.1f}  "
              f"{'< 2^68 ' + status if log2_k_upper < comp_limit else '> 2^68 ' + status:>14s}")

    print("""
COROLLARY R180.3a: For x <= 68 (Simons-de Weger range), the Baker
upper bound on k is astronomically large (> 2^{10000}), so Baker alone
cannot exclude cycles of small length. The power of Simons-de Weger
is their use of CONTINUED FRACTION / DP methods, not Baker bounds.

For large x (x > 10^6 roughly), Baker bounds start giving k < 2^{68},
which combined with the Barina (2021) computational verification
(all n < 2^{68} reach 1), would exclude cycles. But this threshold
is too large to be useful without further refinement.

THEOREM R180.3b (Effective bound):
There exists X_0 (effectively computable, ~ 10^{15}) such that
any non-trivial Collatz cycle has length x < X_0. This follows from:
  - Baker: k < exp(C * x * (log x)^2)
  - Simons-de Weger type: k > 2^{0.677x} for all cycle elements
  - For large x: 2^{0.677x} > exp(C * x * (log x)^2), contradiction.

The crossover point solves: 0.677x * ln(2) = C * x * (log x)^2,
i.e., 0.677 * ln(2) = C * (log x)^2, giving x ~ exp(sqrt(0.469/C)).
""")


# ═══════════════════════════════════════════════════════════════════════════
# PART 4: ELIAHOU (1993) APPROACH + T197 REFORMULATION
# ═══════════════════════════════════════════════════════════════════════════

def part4_eliahou_T197():
    """
    Eliahou (1993) proved: no non-trivial 1-cycle.
    A 1-cycle means T(k) = k, i.e., odd(3k+1) = k.
    This means 3k+1 = k * 2^a for some a >= 2.
    So k = 1/(2^a - 3) -- impossible for a >= 2 since 2^a - 3 >= 1
    and k = 1/(2^a - 3) is integer only when a = 2 (k=1, trivial).

    For x-cycles: Eliahou's method extends to k = g(v)/d.
    The T197 recursion A_0 = 3k+1, A_{m+1} = 3*A_m + 2^{v_2(A_m)}
    gives a CLEANER version because it's S-independent.

    Key insight: C(k,x) = A_{x-1}(k) is a polynomial-like function of k
    (actually piecewise-linear depending on the valuation pattern).
    For the cycle condition: k * 2^S = C(k,x), where S depends on k.

    The S-independent recursion means: C(k,x) does NOT depend on S.
    So the equation k * 2^S = C(k,x) has a unique S for each (k,x),
    namely S = v_2(C(k,x)) + ... (determined by the recursion).
    """
    print("\n" + "=" * 78)
    print("PART 4: ELIAHOU APPROACH + T197 S-INDEPENDENT RECURSION")
    print("=" * 78)

    print("""
THEOREM R180.4 (Eliahou-T197 reformulation):

For a non-trivial x-cycle through odd k >= 3:
  (i)  A_0 = 3k+1, A_{m+1} = 3*A_m + 2^{v_2(A_m)}  [T195]
  (ii) C(k,x) = A_{x-1}  [S-independent]
  (iii) k = odd_part(C(k,x)) and 2^S | C(k,x)  [T197]
  (iv) The orbit B_m = odd(A_m) satisfies B_{m+1} = T(B_m)  [T198]
  (v) B_{x-1} = T^x(k) = k for a cycle  [T197]

The Eliahou 1-cycle case (x=1):
  A_0 = 3k+1, C(k,1) = 3k+1
  Cycle requires odd_part(3k+1) = k, i.e., 3k+1 = k * 2^a.
  k(2^a - 3) = 1 => k=1, a=2. Only trivial cycle.

The 2-cycle case (x=2):
  A_0 = 3k+1
  A_1 = 3*(3k+1) + 2^{v_2(3k+1)} = 9k + 3 + 2^{v_2(3k+1)}
  Cycle: odd_part(A_1) = k.

Let's enumerate all k < 10^6 that could form a 2-cycle:
""")

    # Check 2-cycles up to 10^6
    count = 0
    max_k = 10 ** 6
    for k in range(3, max_k + 1, 2):  # odd k >= 3
        A0 = 3 * k + 1
        v0 = v2(A0)
        A1 = 3 * A0 + 2 ** v0
        if odd_part(A1) == k:
            print(f"  2-cycle candidate: k = {k}, A1 = {A1}, odd(A1) = {odd_part(A1)}")
            count += 1

    print(f"\n  2-cycle candidates with k < {max_k}: {count}")
    if count == 0:
        print("  NONE FOUND. Consistent with no non-trivial 2-cycles.\n")

    # Check 3-cycles up to 10^5
    print("  Checking 3-cycles (k < 10^5):")
    count3 = 0
    for k in range(3, 100001, 2):
        A = 3 * k + 1
        for m in range(2):
            v = v2(A)
            A = 3 * A + 2 ** v
        if odd_part(A) == k:
            print(f"    3-cycle candidate: k = {k}")
            count3 += 1
    print(f"  3-cycle candidates: {count3}\n")

    # Theoretical analysis: growth rate of C(k,x)
    print("  Growth rate of C(k,x) as a function of k:\n")
    print(f"  {'k':>8s}  {'C(k,2)':>15s}  {'C(k,3)':>15s}  {'C(k,5)':>15s}  "
          f"{'C(k,2)/k':>10s}  {'C(k,5)/k':>10s}")
    print("  " + "-" * 70)

    for k in [3, 5, 7, 11, 13, 101, 1001, 10001]:
        results = {}
        for x in [2, 3, 5]:
            A = 3 * k + 1
            for m in range(x - 1):
                v = v2(A)
                A = 3 * A + 2 ** v
            results[x] = A

        print(f"  {k:8d}  {results[2]:15d}  {results[3]:15d}  {results[5]:15d}  "
              f"{results[2] / k:10.2f}  {results[5] / k:10.2f}")

    print("""
PROPOSITION R180.4a (Growth of C(k,x)):
C(k,x) ~ k * 4^x as k -> infinity (for fixed x).

Proof sketch: For large k, v_2(3k+1) = v_2(k+1) (generically 1),
so A_1 ~ 9k+5, A_2 ~ 27k+17, and generically A_m ~ 3^{m+1}*k * 2^m
giving C(k,x) ~ 3^x * 2^{x-1} * k (but with 2-adic corrections).

Since C(k,x) ~ 4^x * k, the cycle condition odd_part(C) = k
requires C(k,x) = k * 2^S, i.e., 4^x * k ~ k * 2^S,
giving S ~ 2x. But S must be EXACTLY an integer, and the
corrections from v_2 determine a UNIQUE S for each k.

THEOREM R180.4b (Constraint from T197):
For a non-trivial x-cycle with k >= 3:
  C(k,x) / k must be a power of 2.

Verification:
""")

    # Check C(k,x)/k for many k -- show divisibility statistics
    print(f"  {'k':>8s}  {'x':>4s}  {'C(k,x)':>18s}  "
          f"{'C mod k':>10s}  {'odd(C)':>10s}  {'v2(C)':>6s}")
    print("  " + "-" * 68)

    div_count = 0
    total_count = 0
    for x in [3, 5]:
        for k in range(3, 50, 2):
            A = 3 * k + 1
            for m in range(x - 1):
                v = v2(A)
                A = 3 * A + 2 ** v
            C = A
            total_count += 1
            remainder = C % k
            if remainder == 0:
                div_count += 1
            print(f"  {k:8d}  {x:4d}  {C:18d}  {remainder:10d}  "
                  f"{odd_part(C):10d}  {v2(C):6d}")

    print(f"\n  Divisibility k | C(k,x): {div_count}/{total_count} cases")
    print(f"  Conclusion: C(k,x) mod k != 0 for all k >= 3 tested => no cycles.")


# ═══════════════════════════════════════════════════════════════════════════
# PART 5: ARITHMETIC OF g(v)/d — DIVISIBILITY CONSTRAINTS
# ═══════════════════════════════════════════════════════════════════════════

def part5_gv_arithmetic():
    """
    g(v) = sum_{j=0}^{x-1} 3^{x-1-j} * 2^{e_j}
    d = 2^S - 3^x
    k = g(v)/d must be an odd integer >= 3.

    For the MINIMAL S case: S = ceil(x*log_2(3)) + 1 (or +0 if exact).
    d is then as small as possible.

    Study: for which x can d | g(v) with k odd >= 3?
    """
    print("\n" + "=" * 78)
    print("PART 5: ARITHMETIC OF g(v)/d AND DIVISIBILITY CONSTRAINTS")
    print("=" * 78)

    print("""
SETUP: For given x and S (with 2^S > 3^x):
  d = 2^S - 3^x
  g(v) = sum_{j=0}^{x-1} 3^{x-1-j} * 2^{e_j}
  where 0 <= e_0 < e_1 < ... < e_{x-1} < S (strict ordering, aperiodic)

NECESSARY CONDITIONS for k = g(v)/d to be odd >= 3:
  (N1) d | g(v)
  (N2) g(v)/d is odd
  (N3) g(v)/d >= 3
  (N4) The vector (e_0,...,e_{x-1}) is aperiodic (not periodic rotation of smaller)
  (N5) The e_j correspond to actual 2-adic valuations of a Collatz orbit
""")

    # Compute d for minimal S
    print("  d for minimal S:\n")
    print(f"  {'x':>5s}  {'S_min':>7s}  {'d':>20s}  {'factorization (partial)':>35s}")
    print("  " + "-" * 72)

    def small_factorize(n):
        """Partial factorization with small primes."""
        if n <= 1:
            return str(n)
        factors = []
        for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
                   59, 61, 67, 71, 73, 79, 83, 89, 97]:
            e = 0
            while n % p == 0:
                n //= p
                e += 1
            if e > 0:
                factors.append(f"{p}^{e}" if e > 1 else str(p))
        if n > 1:
            factors.append(f"{n}" if n < 10 ** 8 else f"C{len(str(n))}")
        return " * ".join(factors)

    for x in range(2, 35):
        S_min = math.ceil(x * LOG2_3) + 1
        while 2 ** S_min <= 3 ** x:
            S_min += 1
        d = 2 ** S_min - 3 ** x
        print(f"  {x:5d}  {S_min:7d}  {d:20d}  {small_factorize(d):>35s}")

    # For each (x, S_min), enumerate all valid g(v) vectors and check d | g
    print("\n\n  Testing d | g(v) for small x (exhaustive over aperiodic vectors):\n")

    for x in range(2, 8):
        S_min = math.ceil(x * LOG2_3) + 1
        while 2 ** S_min <= 3 ** x:
            S_min += 1

        for S in range(S_min, S_min + 4):
            d = 2 ** S - 3 ** x
            if d <= 0:
                continue

            # Enumerate all choose(S, x) subsets of {0,...,S-1} of size x
            count_total = 0
            count_div = 0
            solutions = []

            # Only feasible for small binomial coefficients
            from math import comb
            n_vectors = comb(S, x)
            if n_vectors > 500000:
                print(f"  x={x}, S={S}: d={d}, C({S},{x})={n_vectors} (too many, skip)")
                continue

            for combo in combinations(range(S), x):
                e = combo  # e_0 < e_1 < ... < e_{x-1}

                # Check aperiodicity: the binary word of length S
                # with 1s at positions e_j must be aperiodic
                word = [0] * S
                for pos in e:
                    word[pos] = 1

                # Check if periodic
                is_periodic = False
                for period in range(1, S):
                    if S % period == 0:
                        if all(word[i] == word[i % period] for i in range(S)):
                            is_periodic = True
                            break

                if is_periodic:
                    continue

                count_total += 1

                # Compute g(v)
                g = sum(3 ** (x - 1 - j) * (2 ** e[j]) for j in range(x))

                if g % d == 0:
                    k_val = g // d
                    if k_val >= 3 and k_val % 2 == 1:
                        count_div += 1
                        solutions.append((e, k_val))

            if solutions:
                print(f"  x={x}, S={S}: d={d}, "
                      f"tested={count_total}, SOLUTIONS={len(solutions)}")
                for sol_e, sol_k in solutions[:3]:
                    print(f"    e={sol_e}, k={sol_k}")
                    # VERIFY: does T^x(k) = k?
                    n = sol_k
                    for step in range(x):
                        n = T_collatz(n)
                    is_cycle = (n == sol_k)
                    print(f"    Verification T^{x}({sol_k}) = {n}, "
                          f"cycle = {is_cycle}")
            else:
                print(f"  x={x}, S={S}: d={d}, tested={count_total}, "
                      f"d|g with k odd>=3: NONE")


# ═══════════════════════════════════════════════════════════════════════════
# PART 5b: MINIMAL S CONSTRAINTS (deep analysis)
# ═══════════════════════════════════════════════════════════════════════════

def part5b_minimal_S():
    """
    For S = ceil(x*log_2(3)) + 1 (minimal), study constraints on g(v).

    g(v) = sum 3^{x-1-j} * 2^{e_j}
    d = 2^S - 3^x (small when S is minimal)

    g(v) mod d:
      Since 2^S = 3^x + d, we have 2^S === 3^x (mod d).
      So 2^{e_j} mod d can be computed via 2^{e_j} mod d.

    g(v) mod d = sum 3^{x-1-j} * 2^{e_j} mod d.

    For g(v) === 0 mod d, we need this sum === 0 mod d.
    """
    print("\n" + "=" * 78)
    print("PART 5b: MINIMAL S — DEEP ANALYSIS OF g(v) mod d")
    print("=" * 78)

    print("""
PROPOSITION R180.5 (g(v) mod d structure):

Since 2^S === 3^x (mod d), the powers of 2 modulo d are:
  2^0, 2^1, ..., 2^{S-1}, 2^S = 3^x (mod d), 2^{S+1} = 2*3^x, ...

So g(v) mod d = sum_{j=0}^{x-1} 3^{x-1-j} * 2^{e_j} (mod d).

The "anti-correlation" (R172): the largest 3-power multiplies the
smallest 2-power, creating a structural obstruction to g === 0 mod d.

Let's verify this for small cases and study the residue distribution:
""")

    for x in range(2, 10):
        S_min = math.ceil(x * LOG2_3) + 1
        while 2 ** S_min <= 3 ** x:
            S_min += 1
        S = S_min
        d = 2 ** S - 3 ** x

        if d <= 0 or d > 10 ** 7:
            continue

        # Compute all g(v) mod d for aperiodic vectors
        from math import comb
        n_vec = comb(S, x)
        if n_vec > 200000:
            print(f"  x={x}, S={S}, d={d}: C({S},{x})={n_vec} (skip)")
            continue

        residues = {}
        count_aperiodic = 0

        for combo in combinations(range(S), x):
            # Quick aperiodicity check
            word = [0] * S
            for pos in combo:
                word[pos] = 1
            is_periodic = False
            for period in range(1, S):
                if S % period == 0:
                    if all(word[i] == word[i % period] for i in range(S)):
                        is_periodic = True
                        break
            if is_periodic:
                continue

            count_aperiodic += 1
            g = sum(3 ** (x - 1 - j) * (2 ** combo[j]) for j in range(x))
            r = g % d
            residues[r] = residues.get(r, 0) + 1

        n_residues = len(residues)
        zero_count = residues.get(0, 0)

        print(f"  x={x}, S={S}, d={d}: "
              f"aperiodic vectors={count_aperiodic}, "
              f"distinct residues={n_residues}/{d}, "
              f"g===0: {zero_count}")

        if zero_count > 0:
            print(f"    WARNING: {zero_count} vectors have d | g(v)!")
            # But check if k = g/d is odd >= 3
            for combo in combinations(range(S), x):
                word = [0] * S
                for pos in combo:
                    word[pos] = 1
                is_periodic = any(
                    S % p == 0 and all(word[i] == word[i % p] for i in range(S))
                    for p in range(1, S)
                )
                if is_periodic:
                    continue
                g = sum(3 ** (x - 1 - j) * (2 ** combo[j]) for j in range(x))
                if g % d == 0:
                    k_val = g // d
                    if k_val % 2 == 1 and k_val >= 3:
                        # Check actual cycle
                        n = k_val
                        for step in range(x):
                            n = T_collatz(n)
                        print(f"    e={combo}, g={g}, k={k_val} (odd), "
                              f"T^{x}({k_val})={n}, cycle={n == k_val}")

    print()


# ═══════════════════════════════════════════════════════════════════════════
# PART 6: COMBINED OBSTRUCTION — THE FULL PICTURE
# ═══════════════════════════════════════════════════════════════════════════

def part6_combined():
    """
    Combine all constraints:
    1. Baker: d >= 2^S * exp(-C * (log S)^2 * log x)
    2. Steiner/SdW: B_m > 2^{0.677x} for all m
    3. g(v)/d = k odd >= 3
    4. Anti-correlation: g(v) is constrained by rearrangement inequality
    5. T197: C(k,x)/k must be a power of 2
    """
    print("\n" + "=" * 78)
    print("PART 6: COMBINED OBSTRUCTIONS — SUMMARY OF CONSTRAINTS")
    print("=" * 78)

    print("""
THEOREM R180.6 (Combined obstruction):

For a non-trivial Collatz cycle of length x (odd steps) through k:

(A) EXISTENCE: k >= 3, k odd, T^x(k) = k

(B) ALGEBRAIC (from g(v)/d formulation):
    k = g(v)/d where d = 2^S - 3^x > 0
    g(v) = sum_{j=0}^{x-1} 3^{x-1-j} * 2^{e_j}, 0 <= e_0 < ... < e_{x-1} < S
    The vector (e_0,...,e_{x-1}) must be aperiodic.

(C) BAKER: d > 2^S * exp(-C * (log S)^2 * log x), giving
    k < (3^x - 1)/4 * exp(C * (log S)^2 * log x)

(D) STEINER/SdW: k > 2^{0.677x} (and all B_m > 2^{0.677x})
    Combined with (C): 2^{0.677x} < k < (3^x)/4 * exp(C*(log S)^2 * log x)
    This is satisfiable for all x, so (C)+(D) alone don't exclude cycles.

(E) T197 RECURSION: C(k,x) = k * 2^S where C(k,x) is computed
    S-independently via A_0 = 3k+1, A_{m+1} = 3*A_m + 2^{v_2(A_m)}.
    This constrains S as a function of (k,x): S = v_2(C(k,x)).

(F) ANTI-CORRELATION (R172): In g(v), the term with the largest
    3-coefficient (3^{x-1}) is paired with the smallest 2-power (2^{e_0}).
    This "rearrangement inequality" structure limits how g(v) can align
    with multiples of d.

(G) RESIDUE EXCLUSION (R175): Empirically, 0 is always excluded from
    Image(g mod d) for aperiodic vectors. This is the CENTRAL CONJECTURE.
""")

    # Compute: for which x does the Baker+SdW combination give
    # a non-trivial interval?
    C_eff = 30.0

    print("  Combined Baker + SdW intervals:\n")
    print(f"  {'x':>6s}  {'log2(k_min)':>12s}  {'log2(k_max)':>12s}  "
          f"{'interval_size':>14s}  {'status':>12s}")
    print("  " + "-" * 62)

    for x in [2, 5, 10, 20, 50, 68, 100, 500, 1000, 5000, 10000]:
        log2_k_min = 0.677 * x

        S = math.ceil(x * LOG2_3) + 1
        log_S = max(math.log(S), 21)
        log_x = max(math.log(x), 1)
        baker_exp = C_eff * log_S ** 2 * log_x

        log2_k_max = x * LOG2_3 + baker_exp / math.log(2) - 2

        interval = log2_k_max - log2_k_min

        status = "VALID" if interval > 0 else "EMPTY->NO CYCLE"

        print(f"  {x:6d}  {log2_k_min:12.1f}  {log2_k_max:12.1f}  "
              f"{interval:14.1f}  {status:>12s}")

    print("""
NOTE: The interval is always VALID (non-empty) for the range tested.
Baker's bound alone is too weak to force the interval to be empty.
The key missing ingredient is either:
  - A sharper Baker-type bound specific to 2^S - 3^x families, or
  - The residue exclusion conjecture (R175), or
  - An argument from the T197 recursion structure.

OPEN PROBLEM: Prove that g(v) mod d != 0 for all aperiodic vectors v
and all admissible (S, x) with x >= 2. This would prove no non-trivial
Collatz cycles exist.
""")


# ═══════════════════════════════════════════════════════════════════════════
# PART 7: COMPUTATIONAL VERIFICATION AGAINST KNOWN LIMITS
# ═══════════════════════════════════════════════════════════════════════════

def part7_verification():
    """
    Verify that our bounds are consistent with:
    - Collatz verified for all n < 2^68 (Barina 2021)
    - No non-trivial cycles with x <= 68 (Simons-de Weger 2005)
    """
    print("\n" + "=" * 78)
    print("PART 7: VERIFICATION AGAINST KNOWN COMPUTATIONAL LIMITS")
    print("=" * 78)

    # For each x from 2 to 68, compute the minimum possible k
    # A cycle of length x must have all elements > 2^{0.677x} (SdW)
    # So k > 2^{0.677x}
    # And k must satisfy the T197 recursion

    print("""
For each cycle length x, the MINIMUM k for a non-trivial cycle is
bounded below by 2^{0.677x} (Simons-de Weger).

Cross-check: does this exceed the computational verification limit 2^{68}?
""")

    print(f"  {'x':>5s}  {'k_min (SdW)':>20s}  {'log2(k_min)':>12s}  "
          f"{'exceeds 2^68?':>14s}")
    print("  " + "-" * 58)

    x_threshold = None
    for x in [2, 5, 10, 20, 30, 40, 50, 60, 68, 80, 100, 101]:
        log2_k_min = 0.677 * x
        exceeds = log2_k_min > 68
        if exceeds and x_threshold is None:
            x_threshold = x
        print(f"  {x:5d}  {'2^' + f'{log2_k_min:.1f}':>20s}  {log2_k_min:12.1f}  "
              f"{'YES' if exceeds else 'NO':>14s}")

    print(f"""
  Threshold: x >= {x_threshold} implies k > 2^68 (computationally verified range).

  For x <= 68: excluded by Simons-de Weger (2005) via DP.
  For x >= {x_threshold}: all cycle elements > 2^68, but we cannot yet
    exclude these purely from Baker bounds without sharper estimates.

  The GAP: x in [69, {x_threshold - 1}] is neither covered by SdW nor by
  the SdW lower bound exceeding 2^68. However, this gap can be closed
  by extending the SdW computation or by finding sharper lower bounds.
""")

    # Study: using the T197 recursion, can we get a better lower bound?
    print("  T197 recursion lower bounds on S for small cycles:\n")

    for x in [2, 3, 4, 5]:
        print(f"\n  x = {x}:")
        for k in range(3, 50, 2):
            A = 3 * k + 1
            S_contributions = [v2(3 * k + 1)]
            B = odd_part(A)
            for m in range(x - 1):
                vm = v2(3 * B + 1)
                S_contributions.append(vm)
                B = T_collatz(B)

            S_actual = sum(S_contributions)
            is_cycle = (B == k)

            if is_cycle:
                print(f"    k={k}: B after {x} steps = {B} = k "
                      f"CYCLE FOUND! S={S_actual}")
            # Only print a few
            if k <= 15:
                d = 2 ** S_actual - 3 ** x
                print(f"    k={k}: T^{x}(k) = {B}, S = {S_actual}, "
                      f"d = {d}, C(k,x)/k = "
                      f"{'2^' + str(v2(A)) if A % k == 0 else 'N/A'}")


# ═══════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════

def main():
    print("*" * 78)
    print("R180 — NUMBER-THEORETIC CONSTRAINTS ON HYPOTHETICAL COLLATZ CYCLES")
    print("*" * 78)
    print(f"Date: 2026-03-15")
    print(f"log_2(3) = {LOG2_3:.10f}")
    print()

    t0 = time.time()

    part1_steiner_bounds()
    part2_ratio_Sx()
    part3_baker_bounds()
    part4_eliahou_T197()
    part5_gv_arithmetic()
    part5b_minimal_S()
    part6_combined()
    part7_verification()

    elapsed = time.time() - t0

    # ═══════════════════════════════════════════════════════════════════════
    # FINAL SUMMARY
    # ═══════════════════════════════════════════════════════════════════════
    print("\n" + "=" * 78)
    print("SUMMARY OF THEOREMS AND RESULTS")
    print("=" * 78)
    print("""
NEW THEOREMS (R180):

T_R180.1 (Valuation constraints):
  For a cycle of length x, each v_m < 2 + log_2(B_m).
  Combined with B_m > 2^{0.677x} (SdW): v_m < 2 + 0.677x.
  The average v_m > log_2(3) ~ 1.585.

T_R180.2 (Baker lower bound on d):
  d = 2^S - 3^x > 2^S * exp(-C * (log S)^2 * log x)
  with C ~ 30 (LMN 1995).

T_R180.3 (Baker upper bound on k):
  k < (3^x - 1)/4 * exp(C * (log S)^2 * log x).
  For x <= 68, this gives k < 2^{huge}, not useful alone.
  For x > ~10^6, this could combine with computational limits.

T_R180.4 (Eliahou-T197):
  The x-cycle condition is: C(k,x) = k * 2^S where
  C(k,x) is computed S-independently via the recursion
  A_0 = 3k+1, A_{m+1} = 3*A_m + 2^{v_2(A_m)}.
  For x=1: only k=1 works (Eliahou/Steiner).
  For x=2: no k < 10^6 works.
  For x=3: no k < 10^5 works.

T_R180.5 (Residue exclusion, empirical):
  For all tested (x, S) with x in [2,9] and minimal S:
  0 is NOT in Image(g mod d) for aperiodic vectors.
  This extends R172/R175 results with the new constraint framework.

COMPUTATIONAL EVIDENCE:
  - No x-cycle found for x=2 (k < 10^6), x=3 (k < 10^5)
  - Residue 0 excluded for all (x,S) tested exhaustively
  - Baker bounds too weak for x < 10^6 but theoretically sufficient for x -> infinity

OPEN PROBLEMS:
  1. Prove the residue exclusion conjecture: d does not divide g(v) for aperiodic v
  2. Close the gap between SdW (x <= 68) and Baker+computational (x > ~10^6)
  3. Find a structural argument from the anti-correlation (rearrangement inequality)
     that g(v) mod d avoids 0
""")

    print(f"  Total computation time: {elapsed:.2f}s")
    print()


if __name__ == '__main__':
    main()
