#!/usr/bin/env python3
"""Extended exponential sum computation for k=3..14 using FFT."""

import numpy as np
from itertools import combinations
from math import ceil, log2, comb
import time, sys

def S_of_k(k): return ceil(k * log2(3))
def d_of_k(k): return 2**S_of_k(k) - 3**k

print("EXTENDED EXPONENTIAL SUM ANALYSIS (k=3..14)")
print("=" * 65)
print(f"{'k':>3} {'C':>9} {'d':>10} {'C/d':>7} {'max|G|/C':>9} {'d-C':>10} {'proof':>6} {'time':>6}")
print("-" * 65)

for k in range(3, 15):
    S = S_of_k(k)
    d = d_of_k(k)
    if d <= 0: continue

    C_expected = comb(S-1, k-1)
    t0 = time.time()

    # Build histogram of corrSum mod d
    hist = np.zeros(d, dtype=np.float64)
    count = 0
    for combo in combinations(range(1, S), k-1):
        sigma = (0,) + combo
        cs = sum(3**(k-1-i) * 2**sigma[i] for i in range(k))
        hist[cs % d] += 1
        count += 1
        if count % 100000 == 0:
            sys.stderr.write(f"\r  k={k}: {count}/{C_expected} sequences...")
            sys.stderr.flush()

    if count > 100000:
        sys.stderr.write(f"\r  k={k}: done ({count} sequences)    \n")
        sys.stderr.flush()

    # FFT to get G(a)
    G = np.conj(np.fft.fft(hist))
    G_abs = np.abs(G)

    N0 = int(hist[0])
    max_G = float(np.max(G_abs[1:]))
    ratio = max_G / count
    threshold = d - count
    proof = max_G < threshold and threshold > 0
    elapsed = time.time() - t0

    print(f"{k:3d} {count:9d} {d:10d} {count/d:7.4f} {ratio:9.4f} {threshold:10d} "
          f"{'YES' if proof else 'NO':>6} {elapsed:6.1f}s")

    # For proof cases, check the actual bound gap
    if proof:
        gap = threshold - max_G
        print(f"    -> gap = d-C - max|G| = {gap:.1f} (margin: {gap/threshold:.2%})")
