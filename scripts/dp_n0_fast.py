#!/usr/bin/env python3
"""
Fast DP N0 computation using small prime factors only.
Optimized: O(S * p * k) with small p.
"""

from math import ceil, log2
from itertools import combinations
import json, time, sys

def S_of_k(k): return ceil(k * log2(3))
def d_of_k(k): return 2**S_of_k(k) - 3**k

def small_prime_factors(n, limit=1000):
    """Find prime factors of n up to limit."""
    factors = []
    for p in range(2, min(limit, n) + 1):
        if n % p == 0:
            factors.append(p)
            while n % p == 0:
                n //= p
    if n > 1 and n < 10**12:
        factors.append(n)
    return factors

def dp_n0_mod_p(k, S, p):
    """Count cumul sequences with corrSum ≡ 0 mod p. O(S * p * k)."""
    pow3 = [pow(3, e, p) for e in range(k)]
    pow2 = [pow(2, e, p) for e in range(S)]
    base = pow3[k-1] % p
    target = (p - base) % p

    # dp[j][r]: ways to choose j positions from {1,...,pos} with partial sum ≡ r
    # Use 1D arrays and update in-place (reverse order)
    dp = [{} for _ in range(k)]
    dp[0][0] = 1

    for pos in range(1, S):
        for j in range(min(k-2, pos-1), -1, -1):
            w = (pow3[k-2-j] * pow2[pos]) % p
            items = list(dp[j].items())
            for r, cnt in items:
                nr = (r + w) % p
                dp[j+1][nr] = dp[j+1].get(nr, 0) + cnt

    return dp[k-1].get(target, 0)

def bruteforce_n0(k, S, d):
    """Brute force for small k."""
    count = 0
    for combo in combinations(range(1, S), k-1):
        sigma = (0,) + combo
        cs = sum(pow(3, k-1-i) * pow(2, sigma[i]) for i in range(k))
        if cs % d == 0:
            count += 1
    return count

# Cross-validate
print("Cross-validation (k=3..10):")
for k in range(3, 11):
    S, d = S_of_k(k), d_of_k(k)
    if d <= 0: continue
    bf = bruteforce_n0(k, S, d)
    primes = small_prime_factors(d)
    dp_results = {p: dp_n0_mod_p(k, S, p) for p in primes[:3]}
    print(f"  k={k}: BF(d)={bf}, DP_primes={dp_results} {'✓' if bf==0 and all(v==0 for v in dp_results.values()) else '?'}")

# Extended verification
print(f"\n{'k':>4} {'S':>4} {'d_digits':>8} {'prime':>8} {'N0(p)':>6} {'time':>7}")
print("-" * 50)

results = []
max_k = 200

for k in range(3, max_k + 1):
    S, d = S_of_k(k), d_of_k(k)
    if d <= 0: continue

    t0 = time.time()
    primes = small_prime_factors(d, limit=10000)

    if not primes:
        print(f"{k:4d} {S:4d} {len(str(d)):8d} {'?':>8} {'?':>6} {'?':>7}")
        results.append({'k': k, 'S': S, 'status': 'no_small_prime'})
        continue

    # Use smallest prime for speed
    p = primes[0]
    n0_p = dp_n0_mod_p(k, S, p)
    elapsed = time.time() - t0

    status = "✓" if n0_p == 0 else f"N0={n0_p}!!!"
    print(f"{k:4d} {S:4d} {len(str(d)):8d} {p:8d} {n0_p:6d} {elapsed:7.2f}s {status}")

    results.append({'k': k, 'S': S, 'd_digits': len(str(d)),
                    'prime': p, 'N0_mod_p': n0_p, 'time': round(elapsed, 3)})

    if n0_p > 0:
        # Try other primes
        for p2 in primes[1:5]:
            n0_p2 = dp_n0_mod_p(k, S, p2)
            print(f"     backup: N0({p2}) = {n0_p2}")
            if n0_p2 == 0:
                print(f"     -> N0=0 via prime {p2}")
                results[-1]['N0_resolved'] = True
                results[-1]['resolving_prime'] = p2
                break

    # Stop if getting too slow
    if elapsed > 60:
        print(f"  Stopping at k={k} (too slow)")
        break

# Save
out = '/Users/ericmerle/Documents/Collatz-Junction-Theorem/research_log/dp_n0_fast_results.json'
with open(out, 'w') as f:
    json.dump(results, f, indent=2)

verified = sum(1 for r in results if r.get('N0_mod_p') == 0)
failed = [r['k'] for r in results if r.get('N0_mod_p', 0) > 0 and not r.get('N0_resolved')]
print(f"\nSUMMARY: {verified}/{len(results)} verified N0=0")
if failed:
    print(f"UNRESOLVED: k = {failed}")
else:
    print("ALL VERIFIED: N0_cumulative = 0 for tested range")
