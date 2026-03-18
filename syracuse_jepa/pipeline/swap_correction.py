#!/usr/bin/env python3
"""
SWAP CORRECTION ANALYSIS — The atomic mechanism of ordering obstruction
=========================================================================

When we swap δ_i and δ_j (i < j, δ_i > δ_j — a crossing):
ΔF = (ρ^i - ρ^j) · (2^{δ_i} - 2^{δ_j})

This is the ATOMIC correction from resolving one crossing.
The full sorting involves multiple swaps.

KEY QUESTION: Can the cumulative correction from sorting ever be
≡ 0 mod d? If not: sorting always changes the residue, so if the
unsorted version hits target, the sorted one doesn't.

But the cumulative correction is NOT the sum of individual swaps
(swaps interact). We need the EXACT correction:
F(sorted) - F(unsorted) = exact value mod d.

If F(unsorted) ≡ 0 mod d (target hit): F(sorted) ≡ correction mod d.
For N₀=0: need correction ≢ 0 mod d for EVERY unsorted target-hitting δ.

Equivalently: the map δ ↦ δ_sorted NEVER preserves the target residue.
"""

import sys, os
from math import ceil, log2, comb
from itertools import product as cart_product, combinations_with_replacement

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import compute_S, compute_d


def compute_F(deltas, rho_pow, two_pow, d):
    """F(δ) = Σ_{i=0}^{k-1} ρ^i · 2^{δ_i} mod d, with δ_0=0 fixed."""
    k = len(deltas) + 1
    return (1 + sum(rho_pow[i+1] * two_pow[deltas[i]] % d for i in range(len(deltas)))) % d


def analyze_swap_corrections(k_max=8):
    """For each free solution, compute the exact sorting correction."""
    print("SWAP CORRECTION ANALYSIS")
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
        target = 0  # F ≡ 0 means REST'+1 ≡ 0 means corrSum ≡ 0

        if (max_delta + 1)**(k-1) > 500000:
            continue

        corrections = []
        for deltas in cart_product(range(max_delta + 1), repeat=k-1):
            f_val = compute_F(deltas, rho_pow, two_pow, d)
            if f_val == target:
                # Sort and compute correction
                sorted_d = tuple(sorted(deltas))
                f_sorted = compute_F(sorted_d, rho_pow, two_pow, d)
                correction = (f_sorted - target) % d
                corrections.append({
                    'unsorted': deltas,
                    'sorted': sorted_d,
                    'f_unsorted': f_val,
                    'f_sorted': f_sorted,
                    'correction': correction,
                })

        if not corrections:
            print(f"  k={k}: no free solutions")
            continue

        all_nonzero = all(c['correction'] != 0 for c in corrections)
        print(f"  k={k}, d={d}: {len(corrections)} free solutions")
        print(f"    ALL corrections ≠ 0 mod d: {all_nonzero}")

        if all_nonzero:
            # What are the correction values?
            corr_vals = sorted(set(c['correction'] for c in corrections))
            print(f"    Correction values: {corr_vals}")
            print(f"    #{len(corr_vals)} distinct corrections")

        # Show a few examples
        for c in corrections[:3]:
            print(f"    {c['unsorted']} → {c['sorted']}: "
                  f"F={c['f_unsorted']}→{c['f_sorted']}, Δ={c['correction']}")

    print("\nIf ALL corrections ≠ 0: sorting ALWAYS moves away from target.")
    print("This would prove: ordered δ never hits target ⟺ N₀=0.")


def analyze_swap_structure(k_max=7):
    """
    Analyze the STRUCTURE of the correction F(sorted) - F(unsorted).

    For a single adjacent swap (i, i+1) with δ_i > δ_{i+1}:
    ΔF = ρ^{i+1}·2^{δ_i} + ρ^{i+2}·2^{δ_{i+1}} - ρ^{i+1}·2^{δ_{i+1}} - ρ^{i+2}·2^{δ_i}
       = (ρ^{i+1} - ρ^{i+2})·(2^{δ_i} - 2^{δ_{i+1}})
       = ρ^{i+1}·(1 - ρ)·(2^{δ_i} - 2^{δ_{i+1}})

    Since δ_i > δ_{i+1}: 2^{δ_i} > 2^{δ_{i+1}}, so (2^{δ_i} - 2^{δ_{i+1}}) > 0 in Z.
    And ρ^{i+1}·(1-ρ) is a fixed nonzero value mod d.

    KEY: (1-ρ) = 1 - 2/3 = 1/3 mod d. So (1-ρ) = 3^{-1} mod d.
    And ρ^{i+1}·(1-ρ) = (2/3)^{i+1} · (1/3) = 2^{i+1}/(3^{i+2}) mod d.

    The swap correction is: 2^{i+1}·(2^{δ_i} - 2^{δ_{i+1}}) / 3^{i+2} mod d.
    = 2^{i+1}·2^{δ_{i+1}}·(2^{δ_i-δ_{i+1}} - 1) / 3^{i+2} mod d.
    """
    print("\nSWAP STRUCTURE: ΔF = ρ^{i+1}·(1-ρ)·(2^{δ_i} - 2^{δ_{i+1}})")
    print("=" * 70)

    for k in [3, 5, 7]:
        S = compute_S(k)
        d = compute_d(k)
        inv3 = pow(3, -1, d)
        rho = (2 * inv3) % d
        one_minus_rho = (1 - rho) % d

        print(f"\n  k={k}, d={d}, ρ={rho}, 1-ρ={one_minus_rho}")
        print(f"  (1-ρ) = 3^{{-1}} mod d = {inv3} ✓: {one_minus_rho == inv3}")

        # For each position i, compute ρ^{i+1}·(1-ρ)
        for i in range(k-2):
            factor = (pow(rho, i+1, d) * one_minus_rho) % d
            print(f"    pos {i}: ρ^{i+1}·(1-ρ) = {factor}")


if __name__ == '__main__':
    analyze_swap_corrections()
    analyze_swap_structure()
