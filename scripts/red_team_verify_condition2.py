#!/usr/bin/env python3
"""RED TEAM audit: Verify the claim "8 out of 83 k in [18,100] satisfy Condition (2)"
where Condition (2) is: max prime factor of d(k) > 1.041 * C(k).

d(k) = 2^S - 3^k,  S = ceil(k * log2(3)),  C(k) = C(S-1, k-1).

Uses sympy.factorint for factoring large integers.
"""
import math
import sys
import time

try:
    from sympy import factorint
    HAS_SYMPY = True
except ImportError:
    HAS_SYMPY = False
    print("WARNING: sympy not available, will use trial division (slow for large k)")

def S_of_k(k):
    """S(k) = ceil(k * log2(3))."""
    return math.ceil(k * math.log2(3))

def d_of_k(k):
    """d(k) = 2^S - 3^k (exact integer)."""
    S = S_of_k(k)
    return (1 << S) - 3**k

def C_of_k(k):
    """C(k) = C(S-1, k-1)."""
    S = S_of_k(k)
    return math.comb(S - 1, k - 1)

def largest_prime_factor_sympy(n):
    """Return the largest prime factor of |n| using sympy."""
    if n == 0:
        return 0
    factors = factorint(abs(n))
    if not factors:
        return 1
    return max(factors.keys())

def largest_prime_factor_trial(n):
    """Fallback: trial division (extremely slow for large n)."""
    if n == 0:
        return 0
    n = abs(n)
    largest = 1
    d = 2
    while d * d <= n:
        while n % d == 0:
            largest = d
            n //= d
        d += 1
    if n > 1:
        largest = n
    return largest

def main():
    k_min = 18
    k_max = 100

    print("=" * 80)
    print("  RED TEAM AUDIT: Condition (2) of Theorem Q")
    print(f"  Range: k in [{k_min}, {k_max}] ({k_max - k_min + 1} values)")
    print("  Condition: max prime factor of d(k) > 1.041 * C(k)")
    print("=" * 80)

    if HAS_SYMPY:
        factor_func = largest_prime_factor_sympy
        print("  Using sympy.factorint for factorization\n")
    else:
        factor_func = largest_prime_factor_trial
        print("  Using trial division (WARNING: very slow for large k)\n")

    satisfying_k = []
    failing_k = []

    print(f"  {'k':>4} {'S':>5} {'digits(d)':>10} {'max_pf':>20} {'1.041*C':>20} {'ratio':>12} {'Cond2':>6}")
    print("  " + "-" * 85)

    t_start = time.time()

    for k in range(k_min, k_max + 1):
        S = S_of_k(k)
        d = d_of_k(k)
        C = C_of_k(k)
        threshold = 1.041 * C

        if d <= 0:
            print(f"  {k:>4} {S:>5}  d(k) <= 0, SKIP")
            continue

        digits_d = len(str(d))

        t0 = time.time()
        max_pf = factor_func(d)
        t1 = time.time()

        ratio = max_pf / threshold if threshold > 0 else float('inf')
        cond2 = max_pf > threshold

        status = "PASS" if cond2 else "fail"

        # For display, truncate large numbers
        max_pf_str = str(max_pf) if max_pf < 10**18 else f"{max_pf:.6e}"
        thresh_str = f"{threshold:.2e}" if threshold > 10**15 else f"{threshold:.0f}"

        elapsed = t1 - t0
        time_str = f" [{elapsed:.1f}s]" if elapsed > 1.0 else ""

        print(f"  {k:>4} {S:>5} {digits_d:>10} {max_pf_str:>20} {thresh_str:>20} {ratio:>12.4f} {status:>6}{time_str}")

        if cond2:
            satisfying_k.append(k)
        else:
            failing_k.append(k)

    t_total = time.time() - t_start

    print("\n" + "=" * 80)
    print(f"  RESULTS")
    print("=" * 80)
    print(f"  Total k values tested: {len(satisfying_k) + len(failing_k)}")
    print(f"  Condition (2) SATISFIED: {len(satisfying_k)} values")
    print(f"  Condition (2) FAILED:    {len(failing_k)} values")
    print(f"  k values satisfying: {satisfying_k}")
    print(f"  Total time: {t_total:.1f}s")

    # Compare with paper's claim
    print(f"\n  PAPER CLAIMS: 8 out of 83")
    print(f"  ACTUAL COUNT: {len(satisfying_k)} out of {len(satisfying_k) + len(failing_k)}")

    if len(satisfying_k) == 8 and len(satisfying_k) + len(failing_k) == 83:
        print(f"  VERDICT: MATCHES paper's claim")
    else:
        print(f"  VERDICT: *** DISCREPANCY DETECTED ***")
        if len(satisfying_k) + len(failing_k) != 83:
            print(f"    Expected 83 values, got {len(satisfying_k) + len(failing_k)}")
        if len(satisfying_k) != 8:
            print(f"    Expected 8 satisfying, got {len(satisfying_k)}")

    print("\n" + "=" * 80)

if __name__ == "__main__":
    main()
