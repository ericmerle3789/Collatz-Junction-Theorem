#!/usr/bin/env python3
"""
CORRECTION STRUCTURE — Is there a pattern in F(sorted) - F(unsorted)?
=======================================================================

F(sorted) - F(unsorted) = Σ_{i=1}^{k-1} ρ^i · (2^{sorted_δ_i} - 2^{δ_i})

The correction is a LINEAR COMBINATION of ρ^i with coefficients (2^{s_i} - 2^{δ_i}).

The coefficients depend on HOW the sorting permutes the δ values.

KEY: The sorting permutation σ (not to be confused with cumulative positions)
sends δ to sorted(δ). The correction is:
Σ ρ^i · (2^{δ_{σ⁻¹(i)}} - 2^{δ_i}) = Σ ρ^i · 2^{δ_i} · (2^{Δ_i} - 1)
where Δ_i = δ_{σ⁻¹(i)} - δ_i (the displacement of position i under sorting).

Hmm, this is getting complex. Let me think differently.

The SIMPLEST case: k=3 (one swap).
δ = (δ_1, δ_2) with δ_1 > δ_2 (one crossing).
sorted = (δ_2, δ_1).
F(sorted) = 1 + ρ·2^{δ_2} + ρ²·2^{δ_1}
F(unsorted) = 1 + ρ·2^{δ_1} + ρ²·2^{δ_2}
Correction = ρ·(2^{δ_2} - 2^{δ_1}) + ρ²·(2^{δ_1} - 2^{δ_2})
           = (ρ - ρ²)·(2^{δ_2} - 2^{δ_1})
           = ρ·(1 - ρ)·(2^{δ_2} - 2^{δ_1})

Since δ_1 > δ_2: (2^{δ_2} - 2^{δ_1}) < 0 in Z, but in Z/dZ it's well-defined.
ρ·(1-ρ) = (2/3)·(1/3) = 2/9 mod d.

Correction = (2/9)·(2^{δ_2} - 2^{δ_1}) mod d.
= -(2/9)·2^{δ_2}·(2^{δ_1-δ_2} - 1) mod d.

For this to be 0 mod d: need d | 2^{δ_2}·(2^{δ_1-δ_2}-1).
Since gcd(2,d)=1: need d | (2^{δ_1-δ_2}-1).
Since ord_d(2) > S-k ≥ δ_1-δ_2: this NEVER happens.
QED for k=3!

For k=4: multiple possible swaps. The sorting is more complex.
But the same structure applies: each swap contributes a factor of (2^Δ - 1)
with Δ < S-k, and ord_d(2) > S-k ensures nonvanishing.

WAIT: For k=4 with 2 swaps: the corrections are NOT simply additive.
Sorting (3,2,1) to (1,2,3) requires 3 adjacent swaps (or 1 reversal).
The total correction is NOT the sum of 3 individual swap corrections
because intermediate states differ.

BUT: the DIRECT formula F(sorted) - F(unsorted) is always valid:
= Σ ρ^i · (2^{sorted_δ_i} - 2^{δ_i})
This is exact, no matter how many swaps.

For k=4, δ = (3,2,1), sorted = (1,2,3):
Correction = ρ·(2^1-2^3) + ρ²·(2^2-2^2) + ρ³·(2^3-2^1)
           = ρ·(-6) + 0 + ρ³·(6)
           = 6·(ρ³ - ρ)
           = 6·ρ·(ρ² - 1)

For this to be 0 mod d=47: need 47 | 6·ρ·(ρ²-1).
ρ = 32 mod 47. ρ² = 1024 mod 47 = 1024-21·47 = 1024-987 = 37. ρ²-1 = 36.
6·32·36 = 6912. 6912 mod 47 = 6912 - 147·47 = 6912-6909 = 3.
So correction = 3 ≢ 0 mod 47. ✓

The correction involves ρ^j - ρ^i factors (differences of ρ-powers).
These are related to the CHEBYSHEV structure of ρ in Z/dZ.

KEY THEOREM ATTEMPT:
If ρ is a primitive root mod d (or more generally, if ρ generates a
large subgroup), then the ρ-power differences are "generic" and
the correction sum cannot vanish.
"""

import sys, os
from math import ceil, log2, gcd
from itertools import product as cart_product

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import compute_S, compute_d


def analyze_correction_factors(k_max=8):
    """Decompose F(sorted) - F(unsorted) into ρ-power differences."""
    print("CORRECTION FACTOR ANALYSIS")
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

        if (max_delta + 1)**(k-1) > 500000: continue

        print(f"\nk={k}, d={d}, ρ={rho}")

        for deltas in cart_product(range(max_delta + 1), repeat=k-1):
            f_val = (1 + sum(rho_pow[i+1] * two_pow[deltas[i]] % d for i in range(k-1))) % d
            if f_val != 0: continue

            # Found a free solution. Analyze the correction.
            sorted_d = tuple(sorted(deltas))
            f_sorted = (1 + sum(rho_pow[i+1] * two_pow[sorted_d[i]] % d for i in range(k-1))) % d

            # Direct correction terms
            terms = [(rho_pow[i+1] * ((two_pow[sorted_d[i]] - two_pow[deltas[i]]) % d)) % d
                     for i in range(k-1)]
            total_corr = sum(terms) % d

            print(f"  δ={deltas} → sorted={sorted_d}, correction={total_corr}")

            # Factor analysis: which positions contribute?
            for i in range(k-1):
                if deltas[i] != sorted_d[i]:
                    diff_2 = (two_pow[sorted_d[i]] - two_pow[deltas[i]]) % d
                    term = (rho_pow[i+1] * diff_2) % d
                    print(f"    pos {i+1}: ρ^{i+1}·(2^{sorted_d[i]}-2^{deltas[i]}) = "
                          f"{rho_pow[i+1]}·{diff_2} = {term} mod {d}")


if __name__ == '__main__':
    analyze_correction_factors()
