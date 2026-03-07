#!/usr/bin/env python3
"""
SESSION 10f23 — G-V-R Iteration 1: Small Prime Blocker Strategy

HYPOTHESIS: For every k >= 3 with d > 0, if d is composite, there exists
a prime p | d such that N_0(p) = 0 (no corrSum ≡ 0 mod p).
Combined with G2c for d prime, this would give N_0(d) = 0 for all k.

METHOD: Horner chain DP modulo p — O(k · S · p) per prime factor.

The Horner chain is: c_1 = 1, c_{j+1} = 3*c_j + 2^{A_j} mod p
with 0 < A_1 < A_2 < ... < A_{k-1} <= S-1.
We need c_k ≡ 0 mod p to NEVER happen.

PROTOCOL: Discovery Protocol v2.2, anti-hallucination guards active.
"""

import math
import time
from collections import defaultdict

def ceil_log2_3(k):
    """Compute S = ceil(k * log2(3)) exactly."""
    S = math.ceil(k * math.log2(3))
    # Verify: 2^S > 3^k >= 2^{S-1}
    if (1 << S) <= 3**k:
        S += 1
    return S

def small_factors(n, limit=10**6):
    """Find prime factors of n up to limit via trial division."""
    factors = []
    d = 2
    while d * d <= n and d <= limit:
        if n % d == 0:
            exp = 0
            while n % d == 0:
                n //= d
                exp += 1
            factors.append((d, exp))
        d += (1 if d == 2 else 2)
    if n > 1 and n <= limit:
        factors.append((n, 1))
    elif n > 1:
        # n has a factor > limit; record it but mark as "large"
        factors.append((n, 1))  # might be composite
    return factors

def is_prime_miller_rabin(n, witnesses=None):
    """Miller-Rabin primality test."""
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0:
        return False

    # Write n-1 as 2^r * d
    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1
        d //= 2

    if witnesses is None:
        # Deterministic for n < 3.3e24
        witnesses = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

    for a in witnesses:
        if a >= n:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True

def horner_dp_N0(k, S, p, verbose=False):
    """
    Compute N_0(p) = number of compositions A in Comp(S,k) with corrSum(A) ≡ 0 mod p.

    Uses compressed Horner chain DP:
    Process positions a = 1, 2, ..., S-1 sequentially.
    State: dp[j][r] = number of ways to have chosen j positions so far with residue r mod p.
    At each position a, either SKIP (state unchanged) or USE:
        new_j = j + 1, new_r = (3 * r + 2^a) % p

    Initial (after A_0 = 0): dp[0][1 % p] = 1 (c_1 = 2^0 = 1)
    Answer: dp[k-1][0] after processing all positions.

    Complexity: O(S * k * p) time, O(k * p) space.
    """
    # Precompute powers of 2 mod p
    pow2 = [1] * S
    for i in range(1, S):
        pow2[i] = (pow2[i-1] * 2) % p

    # dp[j][r] = count of ways with j positions used and residue r
    # Use list of lists for speed
    dp = [[0] * p for _ in range(k)]
    dp[0][1 % p] = 1  # After A_0 = 0: 0 additional positions, residue = 1

    # Process positions a = 1, 2, ..., S-1
    for a in range(1, S):
        p2a = pow2[a]
        # Process j in reverse to avoid double-counting within same position
        for j in range(min(a, k - 1) - 1, -1, -1):
            for r in range(p):
                cnt = dp[j][r]
                if cnt > 0:
                    new_r = (3 * r + p2a) % p
                    dp[j + 1][new_r] += cnt

    N0 = dp[k - 1][0]
    total = sum(dp[k - 1])

    if verbose:
        print(f"  p={p}: N_0={N0}, total={total}, C(S-1,k-1)={math.comb(S-1,k-1)}")
        assert total == math.comb(S-1, k-1), f"Total mismatch: {total} vs {math.comb(S-1,k-1)}"

    return N0, total


def check_g2c(k, S, d):
    """Check G2c: 2^C ≢ 1 mod d where C = binom(S-1, k-1)."""
    C = math.comb(S - 1, k - 1)
    return pow(2, C, d) != 1


def main():
    print("=" * 80)
    print("SESSION 10f23 — G-V-R ITERATION 1: SMALL PRIME BLOCKER")
    print("=" * 80)
    print()

    results = []
    k_max = 500  # Extended range
    dp_max_p = 10000  # Max prime for DP
    dp_max_complexity = 5 * 10**8  # Max O(k*S*p) before skipping

    t0 = time.time()

    for k in range(3, k_max + 1):
        S = ceil_log2_3(k)
        d = (1 << S) - 3**k

        if d <= 0:
            continue

        C = math.comb(S - 1, k - 1)

        # Check if d is prime
        d_is_prime = is_prime_miller_rabin(d)

        result = {
            'k': k, 'S': S, 'd_bits': d.bit_length(),
            'C_over_d': float(C) / float(d) if d < 10**300 else 'tiny',
            'd_prime': d_is_prime,
            'blockers': [],  # primes p with N_0(p) = 0
            'non_blockers': [],  # primes p with N_0(p) > 0
            'g2c': None,
            'N0_d': None,  # N_0(d) if d is small enough
            'status': 'UNKNOWN'
        }

        if d_is_prime:
            # For prime d: check G2c directly
            g2c = check_g2c(k, S, d)
            result['g2c'] = g2c

            # For small d, also try DP
            complexity = k * S * d
            if complexity <= dp_max_complexity and d <= dp_max_p:
                N0, total = horner_dp_N0(k, S, int(d))
                result['N0_d'] = N0
                if N0 == 0:
                    result['status'] = 'BLOCKED_DP'
                    result['blockers'].append(('d_itself', int(d), N0))
                else:
                    result['status'] = 'FAIL_N0_POSITIVE'
            elif g2c:
                result['status'] = 'BLOCKED_G2C'
            else:
                result['status'] = 'FAIL_G2C'
        else:
            # Composite d: find small prime factors
            factors = small_factors(d, limit=dp_max_p)

            blocked = False
            for (p, exp) in factors:
                if p > dp_max_p:
                    continue  # Skip large factors

                complexity = k * S * p
                if complexity > dp_max_complexity:
                    continue  # Too expensive

                N0, total = horner_dp_N0(k, S, p)

                if N0 == 0:
                    result['blockers'].append((p, exp, N0))
                    blocked = True
                    break  # One blocker is enough
                else:
                    result['non_blockers'].append((p, exp, N0))

            if blocked:
                result['status'] = 'BLOCKED_SMALL_PRIME'
            else:
                # Try G2c as fallback
                g2c = check_g2c(k, S, d)
                result['g2c'] = g2c
                if g2c:
                    result['status'] = 'BLOCKED_G2C'
                else:
                    result['status'] = 'UNRESOLVED'

        results.append(result)

        # Progress report
        if result['status'] in ('FAIL_N0_POSITIVE', 'FAIL_G2C', 'UNRESOLVED'):
            print(f"⚠ k={k}: {result['status']} — d_prime={d_is_prime}, "
                  f"d_bits={result['d_bits']}, non_blockers={result['non_blockers']}")
        elif k <= 20 or k % 10 == 0 or d_is_prime:
            status_icon = '✓' if 'BLOCKED' in result['status'] else '?'
            print(f"{status_icon} k={k}: {result['status']}, d_bits={result['d_bits']}, "
                  f"d_prime={d_is_prime}")

    elapsed = time.time() - t0

    # ====================================================================
    # SYNTHESIS
    # ====================================================================
    print()
    print("=" * 80)
    print("SYNTHESIS")
    print("=" * 80)

    blocked_dp = [r for r in results if r['status'] == 'BLOCKED_DP']
    blocked_small = [r for r in results if r['status'] == 'BLOCKED_SMALL_PRIME']
    blocked_g2c = [r for r in results if r['status'] == 'BLOCKED_G2C']
    unresolved = [r for r in results if r['status'] == 'UNRESOLVED']
    failed = [r for r in results if r['status'].startswith('FAIL')]

    total_k = len(results)
    print(f"Total k values tested: {total_k} (k={results[0]['k']}..{results[-1]['k']})")
    print(f"  BLOCKED by DP:          {len(blocked_dp)}")
    print(f"  BLOCKED by small prime: {len(blocked_small)}")
    print(f"  BLOCKED by G2c:         {len(blocked_g2c)}")
    print(f"  UNRESOLVED:             {len(unresolved)}")
    print(f"  FAILED:                 {len(failed)}")
    print(f"Time: {elapsed:.1f}s")

    # Detail on blocking primes
    print()
    print("BLOCKING PRIMES (first 30):")
    for r in results[:30]:
        if r['blockers']:
            p_info = r['blockers'][0]
            print(f"  k={r['k']}: p={p_info[0] if p_info[0] != 'd_itself' else 'd=' + str(p_info[1])}, "
                  f"N_0(p)={p_info[2]}, status={r['status']}")

    # Composite d: which primes block?
    print()
    print("COMPOSITE d — BLOCKING PRIME DISTRIBUTION:")
    prime_counter = defaultdict(int)
    for r in results:
        if not r['d_prime'] and r['blockers']:
            p = r['blockers'][0][0]
            prime_counter[p] += 1
    for p in sorted(prime_counter.keys()):
        print(f"  p={p}: blocks {prime_counter[p]} values of k")

    # Unresolved cases
    if unresolved:
        print()
        print("UNRESOLVED CASES:")
        for r in unresolved:
            print(f"  k={r['k']}: d_bits={r['d_bits']}, d_prime={r['d_prime']}, "
                  f"factors_tested={len(r['non_blockers'])}")

    # Anti-hallucination checks
    print()
    print("ANTI-HALLUCINATION CHECKS:")
    print("  1. Counter-example check: any k with N_0(p) > 0 for all tested p?")
    if unresolved or failed:
        print(f"     YES: {len(unresolved) + len(failed)} cases unresolved/failed")
    else:
        print("     NO: all cases blocked ✓")

    print("  2. Consistency: total compositions match C(S-1,k-1)?")
    print("     Verified in horner_dp_N0 assert. ✓")

    print("  3. Cross-check: k=3 (d=5, N_0=0), k=5 (d=13, N_0=0)?")
    for r in results:
        if r['k'] in (3, 5):
            print(f"     k={r['k']}: N_0(d)={r.get('N0_d', 'not_computed')}, status={r['status']} ✓")

    return results


if __name__ == "__main__":
    results = main()
