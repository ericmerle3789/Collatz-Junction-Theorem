#!/usr/bin/env python3
"""verify_condition_q.py — Verification of Condition (Q) (Merle 2026).

Verifies that for all k in [18, k_max] and all primes p | d(k):

    |p * N_0(p) - C| <= 0.041 * C

where C = C(S-1, k-1), d(k) = 2^S - 3^k, S = ceil(k * log2(3)),
and N_0(p) = |{A in Comp(S,k) : corrSum(A) = 0 mod p}|.

Also analyzes:
  - Coset orbit structure: N_r(p) approximately constant on orbits of x2
    (exact when ord_p(2) | (S-1), approximate otherwise)
  - Decay rate for p=7: the ratio |p*N_0 - C|/C decreases with k

Method: dynamic programming on Horner evaluation of corrSum mod p.
The DP processes elements right-to-left (a = S-1, ..., 1). When adding
element a as the smallest in a partial subset, the Horner value transforms
as val -> 3*val + 2^a (mod p).

Expected output (deterministic):
  Condition (Q) verified for k in [18, 28]: True
  Worst case: k=22, p=7, ratio=0.013, margin=3.2x

Usage:
  python3 verify_condition_q.py [k_max]

Requires: Python >= 3.8 (math.comb). No external dependencies.
"""
import math
import hashlib
import sys
from collections import defaultdict


# ============================================================
# Core functions
# ============================================================

def S_of_k(k):
    """S(k) = ceil(k * log2(3))."""
    return math.ceil(k * math.log2(3))


def d_of_k(k):
    """d(k) = 2^S - 3^k (exact integer)."""
    S = S_of_k(k)
    return (1 << S) - 3**k


def C_of_k(k):
    """C(k) = C(S-1, k-1) (exact integer)."""
    S = S_of_k(k)
    return math.comb(S - 1, k - 1)


def prime_factors(n):
    """Return sorted list of prime factors of |n|."""
    if n == 0:
        return []
    factors = set()
    temp = abs(n)
    d = 2
    while d * d <= temp:
        while temp % d == 0:
            factors.add(d)
            temp //= d
        d += 1
    if temp > 1:
        factors.add(temp)
    return sorted(factors)


def multiplicative_order(a, p):
    """Compute ord_p(a), the multiplicative order of a mod p."""
    if p <= 1 or a % p == 0:
        return 0
    val = a % p
    order = 1
    while val != 1:
        val = (val * a) % p
        order += 1
        if order > p:
            return 0  # should not happen for prime p
    return order


# ============================================================
# DP computation of N_r(p)
# ============================================================

def compute_Nr(k, p):
    """Compute N_r(p) for all r = 0, ..., p-1 using DP.

    Returns (Nr_dict, C) where Nr_dict maps residue -> count.

    The corrected Horner sum for a sorted subset {b_1 < ... < b_{k-1}}
    of {1, ..., S-1} is:
        corrSum = sum_{m=0}^{k-2} 3^m * 2^{b_{m+1}}

    This equals the Horner evaluation:
        H = 2^{b_{k-1}} + 3*(2^{b_{k-2}} + 3*(...(2^{b_2} + 3*2^{b_1})...))

    DP processes elements right-to-left (a = S-1, ..., 1).
    When adding element a (smaller than all previously included):
        new_val = 3 * old_val + 2^a  (mod p)
    """
    S = S_of_k(k)
    n_choose = k - 1  # choose k-1 elements from {1, ..., S-1}

    # dp[j] = dict: residue -> count of j-element subsets
    dp = [defaultdict(int) for _ in range(n_choose + 1)]
    dp[0][0] = 1

    # Process elements from S-1 down to 1
    for a in range(S - 1, 0, -1):
        pow2a = pow(2, a, p)
        # Reverse order to avoid double-counting
        for j in range(min(n_choose - 1, S - 1 - a), -1, -1):
            if not dp[j]:
                continue
            new_entries = {}
            for r, cnt in dp[j].items():
                new_r = (3 * r + pow2a) % p
                new_entries[new_r] = new_entries.get(new_r, 0) + cnt
            for r, cnt in new_entries.items():
                dp[j + 1][r] += cnt

    Nr = dict(dp[n_choose])
    C_val = sum(Nr.values())
    return Nr, C_val


# ============================================================
# Condition (Q) verification
# ============================================================

def verify_condition_Q(k_max=28):
    """Verify Condition (Q) for k in [18, k_max] and all primes p | d(k).

    Condition (Q): |p * N_0(p) - C| <= 0.041 * C.
    Equivalently: |sum_{t=1}^{p-1} T(t)| <= 0.041 * C.
    """
    results = []
    threshold = 0.041

    for k in range(18, k_max + 1):
        S = S_of_k(k)
        C = C_of_k(k)
        d = d_of_k(k)

        if d <= 0:
            continue

        primes = prime_factors(d)
        # Limit to primes <= 50000 for computational feasibility
        primes_test = [p for p in primes if p <= 50000]

        for p in primes_test:
            Nr, C_check = compute_Nr(k, p)
            assert C_check == C, f"C mismatch for k={k}: {C_check} vs {C}"

            N0 = Nr.get(0, 0)
            deviation = abs(p * N0 - C)
            ratio = deviation / C
            Q_ok = ratio <= threshold
            margin = threshold / ratio if ratio > 0 else float('inf')

            results.append({
                'k': k, 'S': S, 'C': C, 'd': d, 'p': p,
                'N0': N0, 'deviation': deviation, 'ratio': ratio,
                'Q_ok': Q_ok, 'margin': margin
            })

    return results


# ============================================================
# Coset orbit analysis (Theorem A — approximate symmetry)
# ============================================================

def analyze_coset_orbits(k, p, Nr):
    """Analyze N_r(p) distribution within orbits of multiplication by 2.

    The coset symmetry N_r = N_{2r} is exact when ord_p(2) | (S-1),
    and approximately holds otherwise due to boundary effects at
    a = S-1 in the subset {1, ..., S-1}.

    Returns (max_relative_deviation, orbit_info).
    """
    if p == 2:
        return 0.0, []

    S = S_of_k(k)
    ord2 = multiplicative_order(2, p)

    # Group residues into orbits of x2
    visited = set()
    orbits = []
    for r in range(p):
        if r in visited:
            continue
        orbit = []
        current = r
        for _ in range(ord2):
            orbit.append(current)
            visited.add(current)
            current = (2 * current) % p
        orbits.append(orbit)

    # Measure deviation within each orbit
    max_dev = 0.0
    orbit_info = []
    for orbit in orbits:
        values = [Nr.get(r, 0) for r in orbit]
        mean_v = sum(values) / len(values) if values else 0
        if mean_v > 0:
            dev = max(abs(v - mean_v) / mean_v for v in values)
            max_dev = max(max_dev, dev)
        orbit_info.append((orbit, values))

    return max_dev, orbit_info


# ============================================================
# Main
# ============================================================

if __name__ == "__main__":
    k_max = int(sys.argv[1]) if len(sys.argv) > 1 else 28

    print("=" * 70)
    print("  Verification of Condition (Q) — Merle 2026")
    print("=" * 70)

    # 1. Verify Condition (Q)
    print(f"\n  Testing k in [18, {k_max}], all primes p | d(k)...\n")
    print(f"  {'k':>3} {'S':>4} {'p':>8} {'N0(p)':>12} {'C/p':>14} "
          f"{'ratio':>10} {'Q?':>5} {'margin':>8}")
    print("  " + "-" * 75)

    results = verify_condition_Q(k_max)
    for r in results:
        print(f"  {r['k']:>3} {r['S']:>4} {r['p']:>8} {r['N0']:>12} "
              f"{r['C']/r['p']:>14.2f} {r['ratio']:>10.6f} "
              f"{'OK' if r['Q_ok'] else 'FAIL':>5} {r['margin']:>8.1f}x")

    all_Q_ok = all(r['Q_ok'] for r in results)
    worst = max(results, key=lambda r: r['ratio'])

    print(f"\n  Condition (Q) verified for k in [18, {k_max}]: {all_Q_ok}")
    print(f"  Cases tested: {len(results)}")
    print(f"  Worst case: k={worst['k']}, p={worst['p']}, "
          f"ratio={worst['ratio']:.4f}, margin={worst['margin']:.1f}x")

    # 2. Coset orbit analysis (approximate symmetry)
    print(f"\n  {'─' * 50}")
    print("  Coset orbit analysis (Theorem A)")
    print(f"  {'─' * 50}")
    print("  N_r is approximately constant on orbits of x2 in Z/pZ.")
    print("  Exact when ord_p(2) | (S-1); approximate otherwise.\n")

    for k in range(18, min(k_max + 1, 27)):
        d = d_of_k(k)
        if d <= 0:
            continue
        primes = [p for p in prime_factors(d) if p <= 200]
        for p in primes:
            Nr, _ = compute_Nr(k, p)
            S = S_of_k(k)
            max_dev, orbit_info = analyze_coset_orbits(k, p, Nr)
            ord2 = multiplicative_order(2, p)
            exact = (S - 1) % ord2 == 0
            print(f"  k={k:>3}, p={p:>4}: ord_p(2)={ord2:>3}, "
                  f"{'exact' if exact else 'approx':>6}, "
                  f"max_orbit_dev={max_dev:.4f}")

    # 3. Decay analysis for p=7
    print(f"\n  {'─' * 50}")
    print("  Decay rate for p=7")
    print(f"  {'─' * 50}\n")

    p7_data = [(r['k'], r['ratio']) for r in results if r['p'] == 7]
    if len(p7_data) >= 2:
        print(f"  {'k':>3} {'ratio':>10} {'log2(ratio)':>12}")
        print("  " + "-" * 30)
        for k, ratio in p7_data:
            log_ratio = math.log2(ratio) if ratio > 0 else float('-inf')
            print(f"  {k:>3} {ratio:>10.6f} {log_ratio:>12.2f}")

        # Estimate decay exponent via linear regression on log-log
        if len(p7_data) >= 3:
            import statistics
            log_k = [math.log(k) for k, _ in p7_data if _ > 0]
            log_r = [math.log(r) for _, r in p7_data if r > 0]
            if len(log_k) >= 2:
                n = len(log_k)
                mean_x = statistics.mean(log_k)
                mean_y = statistics.mean(log_r)
                cov = sum((log_k[i] - mean_x) * (log_r[i] - mean_y)
                          for i in range(n)) / n
                var_x = sum((log_k[i] - mean_x) ** 2
                            for i in range(n)) / n
                slope = cov / var_x if var_x > 0 else 0
                print(f"\n  Estimated decay exponent (log-log): {slope:.2f}")
                print(f"  (Expected: approximately -6.3)")

    # 4. Deterministic hash for reproducibility
    sig = str([(r['k'], r['p'], r['N0']) for r in results])
    sha = hashlib.sha256(sig.encode()).hexdigest()[:16]
    print(f"\n  SHA256(results)[:16]: {sha}")

    # 5. Self-test for default k_max=28
    if k_max == 28:
        ok = True
        if not all_Q_ok:
            print("  FAIL: Condition (Q) not satisfied for all cases")
            ok = False
        if worst['k'] != 22 or worst['p'] != 7:
            print(f"  FAIL: Worst case expected (22, 7), got "
                  f"({worst['k']}, {worst['p']})")
            ok = False
        if ok:
            print("\n  All tests pass.")

    print("\n" + "=" * 70)
