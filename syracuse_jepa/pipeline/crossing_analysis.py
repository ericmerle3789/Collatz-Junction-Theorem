#!/usr/bin/env python3
"""
CROSSING ANALYSIS — Why do ALL free solutions have ordering violations?
========================================================================

For each free (unordered) δ-sequence hitting the target:
check if it's weakly increasing (ordered) or has "crossings" (δ_i > δ_{i+1}).

If EVERY free solution has at least one crossing: ordering blocks ALL of them.
This is what we observe. Can we prove it?
"""

import sys, os
from math import ceil, log2
from itertools import product as cart_product, combinations_with_replacement

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import compute_S, compute_d


def analyze_crossings(k_max=8):
    print("CROSSING ANALYSIS: Do ALL free solutions have crossings?")
    print("=" * 70)

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        max_delta = S - k

        inv3 = pow(3, -1, d)
        rho = (2 * inv3) % d
        rho_pow = [pow(rho, i, d) for i in range(k)]
        two_pow = [pow(2, j, d) for j in range(max_delta + 1)]
        target = (-1) % d

        if (max_delta + 1)**(k-1) > 500000:
            print(f"  k={k}: too many free sequences, skipping")
            continue

        # Find ALL free solutions
        free_solutions = []
        for deltas in cart_product(range(max_delta + 1), repeat=k-1):
            inner = sum(rho_pow[i+1] * two_pow[deltas[i]] % d for i in range(k-1)) % d
            if inner == target:
                free_solutions.append(deltas)

        if not free_solutions:
            print(f"  k={k}: no free solutions (N₀=0 trivially)")
            continue

        # Check each: is it ordered (weakly increasing)?
        n_ordered = 0
        n_crossed = 0
        for sol in free_solutions:
            is_ordered = all(sol[i] <= sol[i+1] for i in range(len(sol)-1))
            if is_ordered:
                n_ordered += 1
            else:
                n_crossed += 1

        print(f"  k={k}, d={d}: {len(free_solutions)} free solutions, "
              f"{n_ordered} ordered, {n_crossed} crossed")

        if n_ordered == 0:
            print(f"    ★ ALL solutions have crossings → ordering blocks ALL → N₀=0")

        # Detailed analysis of crossings
        for sol in free_solutions[:5]:
            crossings = [(i, sol[i], sol[i+1]) for i in range(len(sol)-1) if sol[i] > sol[i+1]]
            sorted_sol = tuple(sorted(sol))
            # What's the ordered version's value?
            ordered_val = sum(rho_pow[i+1] * two_pow[sorted_sol[i]] % d for i in range(k-1)) % d
            print(f"    sol={sol}, crossings at {[(i, f'{sol[i]}>{sol[i+1]}') for i in range(len(sol)-1) if sol[i]>sol[i+1]]}")
            print(f"      sorted → {sorted_sol}, F(sorted) mod d = {ordered_val} (target={target})")

    # The KEY question for a proof:
    print("\n" + "=" * 70)
    print("KEY INSIGHT: Every solution to F ≡ 0 mod d with FREE δ has crossings.")
    print("The ORDERING constraint (δ weakly increasing) eliminates all of them.")
    print()
    print("To prove this for ALL k: need to show that the polynomial")
    print("F(ρ) = Σ ρ^i · 2^{δ_i} with weakly increasing δ")
    print("is ALGEBRAICALLY CONSTRAINED to avoid F ≡ 0 mod d.")
    print()
    print("The sorting of δ changes the value mod d because ρ ≠ 1:")
    print("permuting the 2^{δ_i} factors among the ρ^i positions")
    print("changes the sum. If ρ = 1: all permutations give the same sum")
    print("and ordering wouldn't matter. So ord(ρ) > 1 is essential.")


if __name__ == '__main__':
    analyze_crossings()
