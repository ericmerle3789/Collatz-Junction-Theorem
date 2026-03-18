#!/usr/bin/env python3
"""
Numpy-optimized DP for N0 computation (cumulative corrSum mod p).
Uses numpy arrays for O(S * k * p) with efficient vectorized operations.
"""

import numpy as np
from math import ceil, log2
from itertools import combinations
import json, time, sys

def S_of_k(k): return ceil(k * log2(3))
def d_of_k(k): return 2**S_of_k(k) - 3**k

def small_primes_of(n, limit=10000):
    factors = []
    m = n
    for p in range(2, min(limit, int(m**0.5)+2)):
        if m % p == 0:
            factors.append(p)
            while m % p == 0:
                m //= p
    if m > 1 and m < 10**15:
        factors.append(int(m))
    return factors

def dp_n0_mod_p(k, S, p):
    """Count cumulative sequences with corrSum ≡ 0 mod p using numpy."""
    pow3 = [pow(3, e, p) for e in range(k)]
    pow2 = [pow(2, e, p) for e in range(S)]
    base = pow3[k-1] % p
    target = (p - base) % p

    # dp[j] is a numpy array of size p
    # dp[j][r] = number of ways to choose j positions with partial sum ≡ r mod p
    dp = [np.zeros(p, dtype=np.int64) for _ in range(k)]
    dp[0][0] = 1

    for pos in range(1, S):
        for j in range(min(k-2, pos-1), -1, -1):
            w = (pow3[k-2-j] * pow2[pos]) % p
            # Shift dp[j] by w and add to dp[j+1]
            shifted = np.roll(dp[j], w)
            dp[j+1] += shifted

    return int(dp[k-1][target])

def bruteforce_n0(k, S, d):
    count = 0
    for combo in combinations(range(1, S), k-1):
        sigma = (0,) + combo
        cs = sum(pow(3, k-1-i) * pow(2, sigma[i]) for i in range(k))
        if cs % d == 0:
            count += 1
    return count

# Cross-validate k=3..8
print("Cross-validation:")
for k in range(3, 9):
    S, d = S_of_k(k), d_of_k(k)
    if d <= 0: continue
    bf = bruteforce_n0(k, S, d)
    primes = small_primes_of(d)
    dp_res = {p: dp_n0_mod_p(k, S, p) for p in primes[:2]}
    ok = bf == 0 and all(v == 0 for v in dp_res.values())
    print(f"  k={k}: BF={bf}, DP={dp_res} {'✓' if ok else '✗'}")

# Extended
print(f"\n{'k':>4} {'S':>4} {'d_dig':>6} {'p':>8} {'N0(p)':>6} {'t':>6}")
print("-" * 45)

results = []
for k in range(3, 501):
    S, d = S_of_k(k), d_of_k(k)
    if d <= 0:
        results.append({'k': k, 'status': 'skip_d<=0'})
        continue

    t0 = time.time()
    primes = small_primes_of(d)
    if not primes:
        results.append({'k': k, 'status': 'no_prime'})
        continue

    # Try smallest primes first (faster DP)
    resolved = False
    for p in sorted(primes)[:5]:
        if p > 50000:
            continue  # Skip very large primes
        n0_p = dp_n0_mod_p(k, S, p)
        elapsed = time.time() - t0

        if n0_p == 0:
            print(f"{k:4d} {S:4d} {len(str(d)):6d} {p:8d} {n0_p:6d} {elapsed:6.1f}s ✓")
            results.append({'k': k, 'S': S, 'prime': p, 'N0': 0, 'time': round(elapsed, 2)})
            resolved = True
            break
        else:
            print(f"{k:4d} {S:4d} {len(str(d)):6d} {p:8d} {n0_p:6d} {elapsed:6.1f}s N0>0, trying next prime...")

    if not resolved:
        elapsed = time.time() - t0
        print(f"{k:4d} {S:4d} {len(str(d)):6d} {'?':>8} {'?':>6} {elapsed:6.1f}s UNRESOLVED")
        results.append({'k': k, 'S': S, 'status': 'unresolved', 'time': round(elapsed, 2)})

    # Abort if too slow
    if time.time() - t0 > 120:
        print(f"  k={k} too slow, stopping")
        break

out = '/Users/ericmerle/Documents/Collatz-Junction-Theorem/research_log/dp_n0_numpy_results.json'
with open(out, 'w') as f:
    json.dump(results, f, indent=2)

verified = sum(1 for r in results if r.get('N0') == 0)
unresolved = [r['k'] for r in results if r.get('status') == 'unresolved']
print(f"\nVERIFIED: {verified}, UNRESOLVED: {len(unresolved)}")
if unresolved:
    print(f"Unresolved k: {unresolved[:20]}...")
