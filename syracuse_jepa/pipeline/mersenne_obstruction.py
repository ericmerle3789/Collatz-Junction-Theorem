#!/usr/bin/env python3
"""
MERSENNE OBSTRUCTION — Can d divide 2^Δ - 1 for small Δ?
==========================================================

Each atomic swap correction involves (2^Δ - 1) where Δ = δ_i - δ_{i+1}.
If d ∤ (2^Δ - 1) for all Δ in {1,...,S-k}: every swap is nonzero.

d | (2^Δ - 1) ⟺ 2^Δ ≡ 1 mod d ⟺ ord_d(2) | Δ.

So the question reduces to: is ord_d(2) > S-k?

If YES: no individual swap vanishes → total correction = sum of nonzero terms.
But sum of nonzero terms CAN be zero mod d. Need more structure.

If NO: some swaps might vanish, but others don't.

Let's compute ord_d(2) and compare with S-k.

DEEPER: Even if individual swaps don't vanish, the TOTAL correction
F(sorted) - F(unsorted) is what matters. The bubble sort decomposition
is not the only way to compute it.

DIRECT FORMULA:
F(sorted) - F(unsorted) = Σ_{i=1}^{k-1} ρ^i · (2^{sorted_δ_i} - 2^{δ_i})

where sorted_δ is the sorted version of δ.

Each term ρ^i · (2^{sorted_δ_i} - 2^{δ_i}) is nonzero when sorted_δ_i ≠ δ_i.
The terms form a SIGNED sum (some positive, some negative in Z/dZ).
"""

import sys, os
from math import ceil, log2, gcd

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import compute_S, compute_d


def compute_ord(base, mod):
    """Compute multiplicative order of base mod mod using factorization of phi."""
    if mod <= 1: return 1
    if gcd(base, mod) != 1: return -1
    # Euler's theorem: base^phi(mod) ≡ 1. ord divides phi(mod).
    # Compute phi(mod)
    phi = mod
    n = mod
    d = 2
    while d * d <= n:
        if n % d == 0:
            phi = phi // d * (d - 1)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        phi = phi // n * (n - 1)
    # ord divides phi. Find smallest divisor of phi that works.
    result = phi
    # Factor phi
    factors = []
    n = phi
    d = 2
    while d * d <= n:
        if n % d == 0:
            factors.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: factors.append(n)
    # Reduce result by removing prime factors
    for p in factors:
        while result % p == 0 and pow(base, result // p, mod) == 1:
            result //= p
    return result


def ord_analysis(k_max=20):
    print("ord_d(2) vs S-k ANALYSIS")
    print("=" * 60)
    print(f"{'k':>3} {'S':>4} {'d':>12} {'ord_d(2)':>10} {'S-k':>5} {'ord>S-k':>8} {'individual':>12}")
    print("-" * 65)

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue

        ord2 = compute_ord(2, d)
        sk = S - k
        safe = ord2 > sk if ord2 > 0 else False

        # If ord2 > S-k: every individual swap correction is nonzero
        indiv = "ALL nonzero" if safe else f"gaps at {[m for m in range(1,sk+1) if ord2 > 0 and m % ord2 == 0][:3]}"

        print(f"{k:3d} {S:4d} {d:12d} {ord2:10d} {sk:5d} {'✓' if safe else '✗':>8} {indiv:>12}")


if __name__ == '__main__':
    ord_analysis()
