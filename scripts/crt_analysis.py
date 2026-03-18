#!/usr/bin/env python3
"""
CRT Interference Analysis for Cumulative CorrSum.
Investigates why N0(d) = 0 despite N0(p) > 0 for all p | d.
"""

from itertools import combinations
from math import ceil, log2, gcd
import json

def S_of_k(k): return ceil(k * log2(3))
def d_of_k(k): return 2**S_of_k(k) - 3**k

def corrsum_cum(sigma, k):
    return sum(3**(k-1-i) * 2**sigma[i] for i in range(k))

def factorize(n):
    factors = {}
    d = 2
    while d*d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors

def analyze_k(k):
    """Deep CRT analysis for a specific k."""
    S = S_of_k(k)
    d = d_of_k(k)
    if d <= 0:
        return None

    factors = factorize(d)
    primes = sorted(factors.keys())

    # Enumerate all cumulative sequences
    sequences = []
    corrsums = []
    for combo in combinations(range(1, S), k-1):
        sigma = (0,) + combo
        cs = corrsum_cum(sigma, k)
        sequences.append(sigma)
        corrsums.append(cs)

    C = len(corrsums)

    result = {
        'k': k, 'S': S, 'd': d, 'C': C, 'C_over_d': C/d,
        'factors': factors,
    }

    # For each prime factor, find which sequences have corrSum ≡ 0 mod p
    zero_sets = {}
    for p in primes:
        zero_indices = [i for i, cs in enumerate(corrsums) if cs % p == 0]
        zero_sets[p] = set(zero_indices)
        result[f'N0({p})'] = len(zero_indices)
        result[f'frac_0({p})'] = len(zero_indices) / C

    # CRT analysis: intersection of zero sets
    if len(primes) >= 2:
        # Pairwise intersections
        for i, p1 in enumerate(primes):
            for p2 in primes[i+1:]:
                inter = zero_sets[p1] & zero_sets[p2]
                result[f'N0({p1}*{p2})'] = len(inter)
                expected = len(zero_sets[p1]) * len(zero_sets[p2]) / C
                result[f'expected({p1}*{p2})'] = round(expected, 2)

    # Full intersection (= N0(d) for squarefree d)
    if primes:
        full_inter = zero_sets[primes[0]]
        for p in primes[1:]:
            full_inter = full_inter & zero_sets[p]
        result['N0(d)'] = len(full_inter)

    # Analyze the corrSum distribution mod d
    residues = [cs % d for cs in corrsums]
    result['residues_hit'] = len(set(residues))
    result['coverage'] = len(set(residues)) / d

    # Check: which residues are NOT hit?
    all_residues = set(range(d))
    hit_residues = set(residues)
    missed = all_residues - hit_residues
    result['missed_count'] = len(missed)

    # Is 0 among missed?
    result['0_is_missed'] = (0 in missed)

    # Check: what is the minimum |corrSum mod d| (closest to 0)?
    min_residue = min(min(r, d - r) for r in residues)
    result['min_dist_to_0'] = min_residue

    # Geometric analysis: what is corrSum/d for each sequence?
    quotients = [cs // d for cs in corrsums]
    result['q_min'] = min(quotients)
    result['q_max'] = max(quotients)

    return result

print("=" * 72)
print("CRT INTERFERENCE ANALYSIS — Cumulative CorrSum")
print("=" * 72)

results = []
for k in range(3, 15):
    r = analyze_k(k)
    if r is None:
        continue

    results.append(r)
    print(f"\n--- k={k}, S={r['S']}, d={r['d']}, C={r['C']} (C/d={r['C_over_d']:.4f}) ---")
    print(f"  Factors: {r['factors']}")
    print(f"  Residues hit: {r['residues_hit']}/{r['d']} ({r['coverage']:.4f})")
    print(f"  Missed: {r['missed_count']} residues")
    print(f"  0 is missed: {r['0_is_missed']}")
    print(f"  Min distance to 0: {r['min_dist_to_0']}")
    print(f"  corrSum/d range: [{r['q_min']}, {r['q_max']}]")

    for p in sorted(r['factors'].keys()):
        n0p = r.get(f'N0({p})', '?')
        frac = r.get(f'frac_0({p})', '?')
        print(f"  N0({p}) = {n0p} ({frac:.3f})")

    print(f"  N0(d) = {r['N0(d)']}")

    # Check CRT
    primes = sorted(r['factors'].keys())
    if len(primes) >= 2:
        for i, p1 in enumerate(primes):
            for p2 in primes[i+1:]:
                n0 = r.get(f'N0({p1}*{p2})', '?')
                exp = r.get(f'expected({p1}*{p2})', '?')
                print(f"  N0({p1}·{p2}) = {n0} (expected: {exp})")

# Key pattern analysis
print("\n" + "=" * 72)
print("PATTERN ANALYSIS")
print("=" * 72)

for r in results:
    k = r['k']
    d = r['d']
    C = r['C']
    missed = r['missed_count']
    min_dist = r['min_dist_to_0']
    print(f"k={k:2d}: C/d={C/d:.4f}, missed={missed}/{d}, "
          f"min_dist_to_0={min_dist}, 0_missed={'✓' if r['0_is_missed'] else '✗'}")

# Save
with open('/Users/ericmerle/Documents/Collatz-Junction-Theorem/research_log/crt_analysis_results.json', 'w') as f:
    json.dump(results, f, indent=2, default=str)
print(f"\nResults saved.")
