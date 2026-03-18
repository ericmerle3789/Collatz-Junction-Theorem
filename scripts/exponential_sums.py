#!/usr/bin/env python3
"""
Exponential Sum Analysis for Cumulative CorrSum.
Computes G(a) = Σ_σ exp(2πi·a·corrSum(σ)/d) for all a.
If max_{a≠0} |G(a)| < 1 - C/d, then N0 = 0 unconditionally.

This is the KEY theoretical approach: bounding character sums
to prove equidistribution of corrSum mod d.
"""

import numpy as np
from itertools import combinations
from math import ceil, log2, pi
import json

def S_of_k(k): return ceil(k * log2(3))
def d_of_k(k): return 2**S_of_k(k) - 3**k

def compute_exponential_sums(k):
    """Compute all G(a) for a=0,...,d-1."""
    S = S_of_k(k)
    d = d_of_k(k)
    if d <= 0:
        return None

    # Enumerate all corrSum values
    corrsums = []
    for combo in combinations(range(1, S), k-1):
        sigma = (0,) + combo
        cs = sum(3**(k-1-i) * 2**sigma[i] for i in range(k))
        corrsums.append(cs)

    C = len(corrsums)

    # Compute G(a) = Σ exp(2πi·a·cs/d) for each a
    # Using numpy for efficiency
    cs_array = np.array(corrsums, dtype=np.float64)
    G = np.zeros(d, dtype=complex)
    for a in range(d):
        phases = 2 * pi * a * cs_array / d
        G[a] = np.sum(np.exp(1j * phases))

    # G(0) should equal C
    assert abs(G[0] - C) < 0.01, f"G(0) = {G[0]}, expected {C}"

    # |G(a)| for a ≠ 0
    G_abs = np.abs(G)
    G_abs_nonzero = G_abs[1:]
    max_G = np.max(G_abs_nonzero)
    mean_G = np.mean(G_abs_nonzero)

    # N0 = (1/d) * (G(0) + Σ_{a≠0} G(a))
    # = C/d + (1/d) * Σ_{a≠0} G(a)
    N0_exact = np.sum(G).real / d  # Should be integer (0)

    # Bound: |N0 - C/d| ≤ (1/d) * Σ_{a≠0} |G(a)| ≤ (d-1)/d * max|G|
    bound = (d-1) * max_G / d

    # Better bound using L2:
    # Σ |G(a)|^2 = d * C (Parseval for indicator functions... not exactly)
    # Actually: Σ_{a=0}^{d-1} |G(a)|^2 = d * #{(σ,σ') : corrSum(σ) ≡ corrSum(σ') mod d}
    parseval = np.sum(G_abs**2).real
    collision_count = parseval / d

    # L2 bound: (Σ_{a≠0} |G(a)|)^2 ≤ (d-1) * Σ_{a≠0} |G(a)|^2 (Cauchy-Schwarz)
    # Σ_{a≠0} |G(a)|^2 = parseval - C^2
    sum_G2_nonzero = parseval - C**2
    cauchy_schwarz_bound = np.sqrt((d-1) * sum_G2_nonzero)
    l2_bound = cauchy_schwarz_bound / d

    result = {
        'k': k, 'S': S, 'd': d, 'C': C,
        'C_over_d': C/d,
        'N0_exact': round(N0_exact, 6),
        'max_G_nonzero': round(max_G, 6),
        'mean_G_nonzero': round(mean_G, 6),
        'linf_bound': round(bound, 6),
        'l2_bound': round(l2_bound, 6),
        'collision_count': round(collision_count, 2),
        'parseval': round(parseval, 2),
        'threshold': round(1 - C/d, 6),  # Need max|G|/d < this
        'proof_via_linf': max_G < d * (1 - C/d),  # max|G| < d - C
        'proof_via_l2': l2_bound < 1 - C/d,
    }

    return result, G_abs

print("=" * 72)
print("EXPONENTIAL SUM ANALYSIS — Cumulative CorrSum")
print("=" * 72)

results = []
for k in range(3, 15):
    r, G_abs = compute_exponential_sums(k) or (None, None)
    if r is None:
        continue

    results.append(r)
    d = r['d']
    C = r['C']

    print(f"\nk={k}, S={r['S']}, d={d}, C={C}, C/d={r['C_over_d']:.4f}")
    print(f"  N0 (exact) = {r['N0_exact']}")
    print(f"  max|G(a)| (a≠0) = {r['max_G_nonzero']:.2f}")
    print(f"  mean|G(a)| (a≠0) = {r['mean_G_nonzero']:.2f}")
    print(f"  L∞ bound on |N0-C/d|: {r['linf_bound']:.4f}")
    print(f"  L2 bound on |N0-C/d|: {r['l2_bound']:.4f}")
    print(f"  Threshold for proof: max|G| < d-C = {d-C}")
    print(f"  Proof via L∞: {'✓ YES' if r['proof_via_linf'] else '✗ NO'} "
          f"(need max|G| < {d-C}, got {r['max_G_nonzero']:.2f})")
    print(f"  Proof via L2: {'✓ YES' if r['proof_via_l2'] else '✗ NO'}")

    # Distribution of |G(a)| for a ≠ 0
    G_nonzero = G_abs[1:]
    max_val = float(max(G_nonzero))
    bins = sorted(set([0, 0.5, 1, 2, 5, 10, 50, max(max_val+1, 51)]))
    hist, _ = np.histogram(G_nonzero, bins=bins)
    print(f"  |G(a)| distribution: ", end="")
    for i, (lo, hi) in enumerate(zip(bins[:-1], bins[1:])):
        if hist[i] > 0:
            print(f"[{lo:.0f},{hi:.0f}):{hist[i]} ", end="")
    print()

    # KEY: ratio max|G|/sqrt(C)
    print(f"  max|G|/√C = {r['max_G_nonzero']/C**0.5:.4f}")

# Summary
print("\n" + "=" * 72)
print("SUMMARY: Can exponential sums prove N0=0?")
print("=" * 72)
print(f"{'k':>3} {'C/d':>8} {'max|G|':>8} {'d-C':>8} {'proof?':>8} {'max|G|/√C':>10}")
print("-" * 50)
for r in results:
    print(f"{r['k']:3d} {r['C_over_d']:8.4f} {r['max_G_nonzero']:8.2f} "
          f"{r['d']-r['C']:8d} {'YES' if r['proof_via_linf'] else 'NO':>8} "
          f"{r['max_G_nonzero']/r['C']**0.5:10.4f}")

# Save
with open('/Users/ericmerle/Documents/Collatz-Junction-Theorem/research_log/exponential_sum_results.json', 'w') as f:
    json.dump(results, f, indent=2)
print(f"\nSaved to research_log/exponential_sum_results.json")
