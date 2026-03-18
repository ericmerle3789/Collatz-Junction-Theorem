#!/usr/bin/env python3
"""Exponential sums G(a) for k=3..11 using FFT-based approach."""

import numpy as np
from itertools import combinations
from math import ceil, log2, pi

def S_of_k(k): return ceil(k * log2(3))
def d_of_k(k): return 2**S_of_k(k) - 3**k

print("EXPONENTIAL SUM ANALYSIS (k=3..11)")
print("=" * 60)

for k in range(3, 12):
    S = S_of_k(k)
    d = d_of_k(k)
    if d <= 0:
        continue

    # Compute corrSum mod d for all cumulative sequences
    residues = []
    for combo in combinations(range(1, S), k-1):
        sigma = (0,) + combo
        cs = sum(3**(k-1-i) * 2**sigma[i] for i in range(k))
        residues.append(cs % d)

    C = len(residues)

    # Build histogram of residues
    hist = np.zeros(d, dtype=np.float64)
    for r in residues:
        hist[r] += 1

    # G(a) = Σ exp(2πi·a·r/d) over r in residues = DFT of hist
    # Use numpy FFT (computes Σ hist[r]·exp(-2πi·a·r/d))
    # We need Σ hist[r]·exp(+2πi·a·r/d) = conjugate of FFT at index a
    G = np.conj(np.fft.fft(hist))

    G_abs = np.abs(G)
    max_G = np.max(G_abs[1:])  # exclude a=0
    mean_G = np.mean(G_abs[1:])
    threshold = d - C  # need max|G| < d - C

    # N0 verification
    N0 = hist[0]  # direct count
    N0_via_fft = G.sum().real / d

    # Can the L-infinity bound prove N0 = 0?
    proof = max_G < threshold

    print(f"\nk={k}, d={d}, C={C}, C/d={C/d:.4f}")
    print(f"  N0 = {int(N0)} (direct), {N0_via_fft:.6f} (FFT)")
    print(f"  max|G(a≠0)| = {max_G:.2f}")
    print(f"  mean|G(a≠0)| = {mean_G:.2f}")
    print(f"  Threshold d-C = {threshold}")
    print(f"  max|G|/√C = {max_G/C**0.5:.4f}")
    print(f"  max|G|/C = {max_G/C:.4f}")
    print(f"  L∞ proof: {'✓ YES' if proof else '✗ NO'}")

    # Key ratio: max|G(a)|/C for a≠0
    # If this ratio → 0 as k→∞, then the L∞ bound eventually proves N0=0
    # since threshold/C = (d-C)/C = d/C - 1 → ∞

print("\n" + "=" * 60)
print("SUMMARY: max|G|/√C ratio (key for asymptotics)")
print("=" * 60)
print(f"{'k':>3} {'C':>8} {'d':>10} {'C/d':>7} {'max|G|':>9} {'max|G|/√C':>10} {'d/C':>8}")
print("-" * 65)

for k in range(3, 12):
    S = S_of_k(k)
    d = d_of_k(k)
    if d <= 0: continue
    residues = []
    for combo in combinations(range(1, S), k-1):
        sigma = (0,) + combo
        cs = sum(3**(k-1-i) * 2**sigma[i] for i in range(k))
        residues.append(cs % d)
    C = len(residues)
    hist = np.zeros(d, dtype=np.float64)
    for r in residues:
        hist[r] += 1
    G = np.conj(np.fft.fft(hist))
    G_abs = np.abs(G)
    max_G = float(np.max(G_abs[1:]))
    print(f"{k:3d} {C:8d} {d:10d} {C/d:7.4f} {max_G:9.2f} {max_G/C**0.5:10.4f} {d/C:8.2f}")
