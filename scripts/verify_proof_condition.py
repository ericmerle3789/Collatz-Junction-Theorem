#!/usr/bin/env python3
"""
Verify the correct sufficient condition for N0=0 via exponential sums.

The CORRECT condition is: (d-1) * max|G(a)| < d - C  (excludes N0 >= 1).
NOT: max|G(a)| < d - C (which is weaker and what I tested before).

Also check the L2 (Parseval) approach.
"""

import numpy as np
from itertools import combinations
from math import ceil, log2

def S_of_k(k): return ceil(k * log2(3))
def d_of_k(k): return 2**S_of_k(k) - 3**k

print("CORRECT PROOF CONDITIONS CHECK")
print("=" * 75)
print(f"{'k':>3} {'C':>8} {'d':>10} {'C/d':>7} {'max|G|':>9} {'(d-C)/(d-1)':>12} {'L∞?':>5} {'L2 Δ':>12} {'L2?':>5}")
print("-" * 75)

for k in range(3, 15):
    S = S_of_k(k)
    d = d_of_k(k)
    if d <= 0: continue

    # Compute corrSum residues
    hist = np.zeros(d, dtype=np.float64)
    C = 0
    for combo in combinations(range(1, S), k-1):
        sigma = (0,) + combo
        cs = sum(3**(k-1-i) * 2**sigma[i] for i in range(k))
        hist[cs % d] += 1
        C += 1

    # FFT
    G = np.conj(np.fft.fft(hist))
    G_abs = np.abs(G)
    max_G = float(np.max(G_abs[1:]))

    # L∞ condition: (d-1)*max|G| < d-C
    linf_threshold = (d - C) / (d - 1) if d > 1 else 0
    linf_proof = max_G < linf_threshold

    # L2 (Parseval) approach
    # Σ count^2
    collision = np.sum(hist**2)
    # Δ = d*collision - C^2
    Delta = d * collision - C**2
    # Need: (d-C)^2 > (d-1)*Δ
    l2_proof = (d - C)**2 > (d - 1) * Delta if d > C else False

    # Uniformity metric
    nonzero_residues = np.sum(hist > 0)
    if nonzero_residues > 0:
        mean_count = C / nonzero_residues
        variance = np.sum((hist[hist > 0] - mean_count)**2) / nonzero_residues
    else:
        variance = 0

    print(f"{k:3d} {C:8d} {d:10d} {C/d:7.4f} {max_G:9.2f} {linf_threshold:12.6f} "
          f"{'YES' if linf_proof else 'NO':>5} {Delta:12.1f} {'YES' if l2_proof else 'NO':>5}")

    if l2_proof:
        margin = (d-C)**2 / ((d-1)*Delta) - 1
        print(f"    L2 margin: {margin:.4f} ({margin*100:.1f}%)")

print()
print("KEY: L∞ needs max|G| < ≈1 (impossible for large C).")
print("     L2 needs (d-C)^2 > (d-1)·(d·Σcount^2 - C^2).")
print("     L2 works if distribution is approximately uniform over d-1 residues.")
