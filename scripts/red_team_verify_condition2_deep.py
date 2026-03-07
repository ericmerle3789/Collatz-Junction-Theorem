#!/usr/bin/env python3
"""RED TEAM deep audit: Adversarial checks on Condition (2) verification.

Checks:
1. S(k) = ceil(k*log2(3)) computed correctly (no floating point errors)
2. d(k) = 2^S - 3^k is positive for all k in [18, 100]
3. Factorization cross-check: product of factors == d(k)
4. The 1.041 threshold — does the paper actually say 1.041*C or d^(2/3)?
5. Near-boundary cases: k values where max_pf is close to threshold
6. Cross-check: is 2^S > 3^k (i.e., S = ceil(k*log2(3)) correct)?
"""
import math
from fractions import Fraction
from sympy import factorint, isprime, Integer, ceiling, log as symlog, Rational

def S_of_k_float(k):
    """Float version."""
    return math.ceil(k * math.log2(3))

def S_of_k_exact(k):
    """Exact version using comparison 2^S >= 3^k.
    S = min integer S such that 2^S >= 3^k.
    """
    # 2^S >= 3^k  <=>  S >= k * log2(3)
    # Find by direct comparison
    s = int(k * math.log2(3))  # floor
    # Check if 2^s >= 3^k
    if (1 << s) >= 3**k:
        return s
    else:
        return s + 1

def main():
    print("=" * 80)
    print("  RED TEAM DEEP AUDIT: Adversarial checks on Condition (2)")
    print("=" * 80)

    # CHECK 1: S(k) correctness
    print("\n  CHECK 1: S(k) = ceil(k*log2(3)) — float vs exact comparison")
    print("  " + "-" * 60)
    s_errors = []
    for k in range(18, 101):
        s_float = S_of_k_float(k)
        s_exact = S_of_k_exact(k)
        if s_float != s_exact:
            s_errors.append((k, s_float, s_exact))
            print(f"  *** MISMATCH at k={k}: float={s_float}, exact={s_exact}")

    if not s_errors:
        print("  OK: All S(k) values match (float == exact) for k in [18, 100]")
    else:
        print(f"  FAIL: {len(s_errors)} mismatches found!")

    # CHECK 2: d(k) > 0 for all k
    print("\n  CHECK 2: d(k) = 2^S - 3^k > 0 for all k")
    print("  " + "-" * 60)
    all_positive = True
    for k in range(18, 101):
        S = S_of_k_exact(k)
        d = (1 << S) - 3**k
        if d <= 0:
            print(f"  *** NEGATIVE d(k) at k={k}: d = {d}")
            all_positive = False
    if all_positive:
        print("  OK: All d(k) > 0 for k in [18, 100]")

    # CHECK 3: Factorization cross-check
    print("\n  CHECK 3: Factorization verification (product of factors == d)")
    print("  " + "-" * 60)
    factor_errors = []
    for k in range(18, 101):
        S = S_of_k_exact(k)
        d = (1 << S) - 3**k
        factors = factorint(d)
        reconstructed = 1
        for p, e in factors.items():
            reconstructed *= p**e
        if reconstructed != d:
            factor_errors.append(k)
            print(f"  *** FACTORIZATION ERROR at k={k}: product != d(k)")

    if not factor_errors:
        print("  OK: All factorizations verified (product == d) for k in [18, 100]")
    else:
        print(f"  FAIL: {len(factor_errors)} factorization errors!")

    # CHECK 4: Verify the 8 specific k values
    print("\n  CHECK 4: Detailed verification of the 8 satisfying k values")
    print("  " + "-" * 60)
    satisfying = []

    for k in range(18, 101):
        S = S_of_k_exact(k)
        d = (1 << S) - 3**k
        C = math.comb(S - 1, k - 1)
        threshold = Fraction(1041, 1000) * C  # Exact 1.041

        factors = factorint(d)
        max_pf = max(factors.keys())

        if max_pf > threshold:
            satisfying.append(k)
            ratio_exact = Fraction(max_pf, C)
            print(f"  k={k:>3}: S={S}, max_pf = {max_pf}")
            print(f"         C = {C}")
            print(f"         max_pf / C = {float(ratio_exact):.6f}")
            print(f"         max_pf > 1.041*C? {max_pf > threshold}")
            print(f"         max_pf is prime? {isprime(max_pf)}")
            print()

    print(f"  Satisfying k values: {satisfying}")
    print(f"  Count: {len(satisfying)}")

    # CHECK 5: Near-boundary cases
    print("\n  CHECK 5: Near-boundary cases (ratio between 0.5 and 2.0)")
    print("  " + "-" * 60)
    for k in range(18, 101):
        S = S_of_k_exact(k)
        d = (1 << S) - 3**k
        C = math.comb(S - 1, k - 1)
        threshold = 1.041 * C

        factors = factorint(d)
        max_pf = max(factors.keys())
        ratio = max_pf / threshold

        if 0.5 <= ratio <= 2.0:
            print(f"  k={k}: max_pf={max_pf}, 1.041*C={threshold:.2e}, ratio={ratio:.6f}")

    # CHECK 6: Does the paper use 1.041*C or d^(2/3)?
    print("\n  CHECK 6: Comparison 1.041*C vs d^(2/3)")
    print("  " + "-" * 60)
    print("  The paper says: 'prime factor p > 1.041*C(k)'")
    print("  The user asked about: 'prime factor > d(k)^(2/3)'")
    print("  These are DIFFERENT conditions. Let's compare:")
    print()

    satisfying_041 = []
    satisfying_23 = []

    for k in range(18, 101):
        S = S_of_k_exact(k)
        d = (1 << S) - 3**k
        C = math.comb(S - 1, k - 1)

        factors = factorint(d)
        max_pf = max(factors.keys())

        cond_041 = max_pf > 1.041 * C
        # d^(2/3) approximation using exact arithmetic
        # d^(2/3) = exp(2/3 * ln(d))
        import mpmath
        d_23 = float(mpmath.power(d, mpmath.mpf(2)/3))
        cond_23 = max_pf > d_23

        if cond_041:
            satisfying_041.append(k)
        if cond_23:
            satisfying_23.append(k)

    print(f"  Condition max_pf > 1.041*C: {len(satisfying_041)} values: {satisfying_041}")
    print(f"  Condition max_pf > d^(2/3): {len(satisfying_23)} values: {satisfying_23}")
    print()

    if satisfying_041 != satisfying_23:
        only_041 = set(satisfying_041) - set(satisfying_23)
        only_23 = set(satisfying_23) - set(satisfying_041)
        if only_041:
            print(f"  In 1.041*C but NOT d^(2/3): {sorted(only_041)}")
        if only_23:
            print(f"  In d^(2/3) but NOT 1.041*C: {sorted(only_23)}")

    # CHECK 7: Verify with strict threshold (0.041 gives 1.041)
    print("\n  CHECK 7: Sensitivity analysis — threshold sweep")
    print("  " + "-" * 60)
    for multiplier in [1.0, 1.01, 1.02, 1.03, 1.04, 1.041, 1.05, 1.1, 1.5, 2.0]:
        count = 0
        for k in range(18, 101):
            S = S_of_k_exact(k)
            d = (1 << S) - 3**k
            C = math.comb(S - 1, k - 1)
            factors = factorint(d)
            max_pf = max(factors.keys())
            if max_pf > multiplier * C:
                count += 1
        print(f"  Threshold {multiplier:.3f}*C: {count} out of 83 satisfy")

    print("\n" + "=" * 80)
    print("  AUDIT COMPLETE")
    print("=" * 80)

if __name__ == "__main__":
    main()
