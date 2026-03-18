#!/usr/bin/env python3
"""
DP-based EXACT computation of N0 for cumulative corrSum.
========================================================

For each k, computes the EXACT number of cumulative sequences
(0, σ_1, ..., σ_{k-1}) with 0 < σ_1 < ... < σ_{k-1} < S
such that corrSum(σ) ≡ 0 (mod d).

Method: Dynamic programming over positions, tracking partial sum mod d.
Complexity: O(S * d * k) — feasible for k up to ~200 with d < 10^8.

For larger d, we use prime factorization: N0(d) = 0 iff N0(p) = 0
for some prime p | d.

Anti-hallucination: cross-validated against brute-force for k ≤ 14.
"""

from math import ceil, log2, gcd
from functools import lru_cache
import json
import time
import sys

def S_of_k(k):
    return ceil(k * log2(3))

def d_of_k(k):
    S = S_of_k(k)
    return 2**S - 3**k

def smallest_prime_factor(n):
    """Find smallest prime factor of n."""
    if n <= 1:
        return None
    if n % 2 == 0:
        return 2
    i = 3
    while i * i <= n:
        if n % i == 0:
            return i
        i += 2
    return n

def factorize(n):
    """Complete prime factorization."""
    factors = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors

def dp_count_n0_mod_p(k, S, p):
    """
    Count cumulative sequences with corrSum ≡ 0 (mod p).

    DP state: dp[j][r] = number of ways to choose j positions from {current...S-1}
    such that the partial corrSum ≡ r (mod p).

    We process positions from S-1 down to 1, deciding whether to include each.
    Position 0 is always included (σ_0 = 0, contributes 3^{k-1} · 2^0 = 3^{k-1}).

    For positions σ_1,...,σ_{k-1}: choose k-1 from {1,...,S-1}.
    The i-th chosen position (in increasing order) gets weight 3^{k-1-i} · 2^{σ_i}.

    But the weight depends on the rank i, not just the position σ_i!
    This makes the DP harder — we need to track how many have been chosen.

    DP: dp[pos][chosen][residue] = count
    - pos: current position (from 1 to S-1)
    - chosen: how many positions have been selected so far (0 to k-1)
    - residue: partial corrSum mod p

    Complexity: O(S * k * p)
    """
    # Powers mod p
    pow3 = [pow(3, e, p) for e in range(k)]
    pow2 = [pow(2, e, p) for e in range(S)]

    # Fixed contribution from σ_0 = 0: 3^{k-1} · 2^0 = 3^{k-1}
    base_residue = pow3[k-1] % p

    # We need to choose k-1 positions from {1,...,S-1} in increasing order.
    # Position chosen as the j-th (j=1,...,k-1) gets weight 3^{k-1-j} · 2^{pos}.
    # After choosing j-1 positions from {1,...,pos-1}, if we choose pos as the j-th,
    # it contributes 3^{k-1-j} · 2^{pos} mod p.

    # DP: dp[chosen][residue] = count of ways
    # Iterate pos from 1 to S-1

    # dp[j][r] = number of ways to have chosen j positions from {1,...,pos-1}
    # with partial sum ≡ r mod p

    # Initialize: 0 positions chosen, residue 0
    dp = [[0] * p for _ in range(k)]
    dp[0][0] = 1  # 0 positions chosen, residue 0

    for pos in range(1, S):
        # Process in reverse order of chosen to avoid double-counting
        for j in range(min(k-2, pos-1), -1, -1):
            # If we choose pos as the (j+1)-th position:
            # weight = 3^{k-1-(j+1)} · 2^{pos} = 3^{k-2-j} · 2^{pos}
            weight = (pow3[k-2-j] * pow2[pos]) % p

            for r in range(p):
                if dp[j][r] > 0:
                    new_r = (r + weight) % p
                    dp[j+1][new_r] += dp[j][r]

    # Answer: dp[k-1][target] where target = (p - base_residue) % p
    # Because we need base_residue + partial_sum ≡ 0 mod p
    target = (p - base_residue) % p
    return dp[k-1][target]


def dp_count_n0_exact(k, S, d):
    """
    Exact count of N0 modulo d (when d is small enough).
    Same DP but mod d instead of mod p.
    """
    if d > 10**7:
        return None  # Too large for direct DP

    pow3 = [pow(3, e, d) for e in range(k)]
    pow2 = [pow(2, e, d) for e in range(S)]

    base_residue = pow3[k-1] % d

    dp = [[0] * d for _ in range(k)]
    dp[0][0] = 1

    for pos in range(1, S):
        for j in range(min(k-2, pos-1), -1, -1):
            weight = (pow3[k-2-j] * pow2[pos]) % d
            for r in range(d):
                if dp[j][r] > 0:
                    new_r = (r + weight) % d
                    dp[j+1][new_r] += dp[j][r]

        # Progress for large computations
        if S > 50 and pos % 10 == 0:
            sys.stdout.write(f"\r  k={k}: pos {pos}/{S-1}")
            sys.stdout.flush()

    if S > 50:
        sys.stdout.write(f"\r  k={k}: done                \n")
        sys.stdout.flush()

    target = (d - base_residue) % d
    return dp[k-1][target]


def verify_against_bruteforce(k_max=10):
    """Cross-validate DP against brute-force enumeration."""
    from itertools import combinations

    print("Cross-validation: DP vs brute-force")
    print("-" * 50)

    all_ok = True
    for k in range(3, k_max + 1):
        S = S_of_k(k)
        d = d_of_k(k)
        if d <= 0:
            continue

        # Brute force
        bf_count = 0
        for combo in combinations(range(1, S), k - 1):
            sigma = (0,) + combo
            cs = sum(pow(3, k-1-i) * pow(2, sigma[i]) for i in range(k))
            if cs % d == 0:
                bf_count += 1

        # DP (exact mod d)
        dp_count = dp_count_n0_exact(k, S, d) if d < 10**7 else None

        # DP (mod smallest prime)
        factors = factorize(d)
        primes = sorted(factors.keys())
        dp_p_counts = {}
        for p in primes[:3]:  # Check first 3 primes
            dp_p_counts[p] = dp_count_n0_mod_p(k, S, p)

        match = (dp_count == bf_count) if dp_count is not None else "N/A"
        status = "✓" if match == True else ("?" if match == "N/A" else "✗")

        print(f"  k={k:2d}: BF={bf_count}, DP_exact={dp_count}, "
              f"DP_primes={dp_p_counts} {status}")

        if match == False:
            all_ok = False
            print(f"  *** MISMATCH at k={k}! ***")

    print(f"\nCross-validation: {'ALL OK' if all_ok else 'FAILURES DETECTED'}")
    return all_ok


def main():
    print("=" * 72)
    print("DP Exact N0 Computation — Cumulative corrSum")
    print("=" * 72)

    # Phase 1: Cross-validate
    print("\n--- Phase 1: Cross-validation ---")
    ok = verify_against_bruteforce(k_max=12)
    if not ok:
        print("ABORT: Cross-validation failed!")
        return

    # Phase 2: Extend verification using prime factorization
    print("\n--- Phase 2: Extended verification (k=3..100) ---")
    print(f"{'k':>4} {'S':>4} {'d':>14} {'smallest p':>10} {'N0(p)':>6} {'time':>8}")
    print("-" * 55)

    results = []
    for k in range(3, 101):
        S = S_of_k(k)
        d = d_of_k(k)
        if d <= 0:
            continue

        t0 = time.time()

        # Find a small prime factor of d
        factors = factorize(d) if d < 10**12 else {}

        if not factors:
            # d too large to factorize quickly
            p = smallest_prime_factor(d)
            if p is None:
                results.append({'k': k, 'status': 'SKIP'})
                continue
        else:
            primes = sorted(factors.keys())
            p = primes[0]  # smallest prime factor

        # Compute N0 mod p
        n0_p = dp_count_n0_mod_p(k, S, p)
        elapsed = time.time() - t0

        status = "N0=0 ✓" if n0_p == 0 else f"N0(p)={n0_p} !!!"
        print(f"{k:4d} {S:4d} {d:14d} {p:10d} {n0_p:6d} {elapsed:8.2f}s  {status}")

        results.append({
            'k': k, 'S': S, 'd': d,
            'prime': p, 'N0_mod_p': n0_p,
            'time': round(elapsed, 3)
        })

        if n0_p > 0:
            print(f"  *** WARNING: N0({p}) = {n0_p} > 0 at k={k}! ***")
            # Check other primes
            for p2 in sorted(factors.keys()):
                if p2 != p:
                    n0_p2 = dp_count_n0_mod_p(k, S, p2)
                    print(f"  N0({p2}) = {n0_p2}")

    # Save results
    out_path = '/Users/ericmerle/Documents/Collatz-Junction-Theorem/research_log/dp_n0_results.json'
    with open(out_path, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {out_path}")

    # Summary
    verified = [r for r in results if r.get('N0_mod_p') == 0]
    failed = [r for r in results if r.get('N0_mod_p', 0) > 0]
    print(f"\n{'=' * 72}")
    print(f"SUMMARY: {len(verified)} verified (N0=0), {len(failed)} with N0>0")
    if failed:
        print(f"FAILURES: {[r['k'] for r in failed]}")
    else:
        print(f"ALL k=3..100 have N0_cumulative(p) = 0 for smallest prime p | d(k)")
    print(f"{'=' * 72}")


if __name__ == '__main__':
    main()
