#!/usr/bin/env python3
"""
VANDERMONDE APPROACH — Polynomial root analysis of sorting corrections
========================================================================

Each free solution δ defines a correction polynomial:
Q_δ(X) = Σ_{i=1}^{k-1} (2^{sorted_δ_i} - 2^{δ_i}) · X^i

The correction is Q_δ(ρ) where ρ = 2/3 mod d.
Q_δ(ρ) = 0 mod d iff ρ is a root of Q_δ modulo d.

APPROACH: For each free solution, Q_δ is a SPECIFIC polynomial.
If none of them has ρ as a root mod d: all corrections nonzero → N₀=0.

This reduces to: is ρ = 2/3 in the ROOT SET of Q_δ mod d for any δ?

For d prime: each Q_δ of degree ≤ k-2 has at most k-2 roots.
There are N_free ≈ total/d solutions, each with its own Q.
The UNION of root sets has size at most N_free · (k-2).
If N_free · (k-2) < d: the union doesn't cover all of Z/dZ,
so there exist values NOT in any root set.
But we need the SPECIFIC value ρ to be outside all root sets.

This is a RANDOM-LOOKING condition — no algebraic reason
why ρ should be in any specific root set.

HOWEVER: ρ IS algebraically related to d (both involve 2 and 3).
The Q_δ also involve powers of 2. So the roots of Q_δ mod d
are related to ρ in a non-random way.

Let me compute: for each solution, what ARE the roots of Q_δ mod d?
If ρ is NEVER among them: that's the proof.
"""

import sys, os
from math import ceil, log2, gcd
from itertools import product as cart_product

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import compute_S, compute_d


def find_polynomial_roots(coeffs, d):
    """Find all roots of Σ coeffs[i] · X^i mod d (brute force for small d)."""
    if d > 10000: return None  # Too large
    roots = []
    for x in range(d):
        val = sum(c * pow(x, i, d) for i, c in enumerate(coeffs)) % d
        if val == 0:
            roots.append(x)
    return roots


def analyze_root_structure(k_max=7):
    """For each free solution, find roots of Q_δ mod d and check if ρ is among them."""
    print("VANDERMONDE ROOT ANALYSIS")
    print("=" * 60)

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        max_delta = S - k

        inv3 = pow(3, -1, d)
        rho = (2 * inv3) % d
        rho_pow = [pow(rho, i, d) for i in range(k)]
        two_pow = [pow(2, j, d) for j in range(max_delta + 1)]

        total = (max_delta + 1)**(k-1)
        if total > 500000: continue

        print(f"\nk={k}, d={d}, ρ={rho}")

        all_root_sets = []
        rho_never_root = True

        for deltas in cart_product(range(max_delta + 1), repeat=k-1):
            f_val = (1 + sum(rho_pow[i+1] * two_pow[deltas[i]] % d for i in range(k-1))) % d
            if f_val != 0: continue

            sorted_d = tuple(sorted(deltas))
            # Q coefficients: c_0 = 0 (constant term), c_i = 2^{s_i} - 2^{δ_i}
            coeffs = [0]  # X^0 term
            for i in range(k-1):
                c = (two_pow[sorted_d[i]] - two_pow[deltas[i]]) % d
                coeffs.append(c)

            # Find roots
            if d <= 5000:
                roots = find_polynomial_roots(coeffs, d)
                is_rho_root = rho in roots if roots is not None else None
            else:
                # Just check ρ
                val = sum(coeffs[i] * rho_pow[i] % d for i in range(len(coeffs))) % d
                is_rho_root = (val == 0)
                roots = ['?']

            if is_rho_root:
                rho_never_root = False
                print(f"  *** ρ IS a root of Q_δ for δ={deltas}! ***")

            all_root_sets.append({
                'delta': deltas,
                'n_roots': len(roots) if roots != ['?'] else '?',
                'rho_is_root': is_rho_root,
            })

            # Print first few
            if len(all_root_sets) <= 5:
                deg = len(coeffs) - 1
                n_r = len(roots) if roots != ['?'] else '?'
                print(f"  δ={deltas}: Q deg={deg}, {n_r} roots, ρ∈roots={is_rho_root}")

        print(f"  TOTAL: {len(all_root_sets)} free solutions")
        print(f"  ρ NEVER a root: {rho_never_root}")
        if rho_never_root:
            print(f"  ✓ This proves all corrections ≠ 0 for k={k}")

        # Statistics on root counts
        if d <= 5000:
            root_counts = [r['n_roots'] for r in all_root_sets if r['n_roots'] != '?']
            if root_counts:
                print(f"  Root count stats: min={min(root_counts)}, max={max(root_counts)}, "
                      f"mean={sum(root_counts)/len(root_counts):.1f}")
                print(f"  Max possible roots: {k-2} (degree bound)")


if __name__ == '__main__':
    analyze_root_structure()
