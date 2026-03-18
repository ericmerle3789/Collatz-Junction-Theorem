#!/usr/bin/env python3
"""
NONVANISHING PROOF — Can we prove the sorting correction is always ≠ 0?
=========================================================================

The sorting of δ = (δ_1,...,δ_{k-1}) to get sorted(δ) produces:
F(sorted) - F(unsorted) = Σ over swaps of ρ^{i+1}·(1-ρ)·(2^{a}-2^{b})

For a SINGLE adjacent swap at position i with δ_i > δ_{i+1}:
ΔF = ρ^{i+1} · 3^{-1} · 2^{δ_{i+1}} · (2^{δ_i - δ_{i+1}} - 1) mod d

This is a product of:
- ρ^{i+1}: a UNIT (since gcd(ρ,d) = gcd(2·3^{-1}, d) = 1, as gcd(6,d)=1)
- 3^{-1}: a UNIT
- 2^{δ_{i+1}}: a UNIT (since gcd(2,d) = 1, d is odd)
- (2^{δ_i - δ_{i+1}} - 1): THIS could be 0 mod d only if 2^{δ_i-δ_{i+1}} ≡ 1 mod d,
  i.e., ord_d(2) | (δ_i - δ_{i+1}).

Since δ_i - δ_{i+1} ≥ 1 and δ_i ≤ S-k: the gap is at most S-k.
ord_d(2) = S (since 2^S ≡ 3^k ≡ 0 + 3^k ≢ 1 mod d in general... wait).

Actually: ord_d(2) is the multiplicative order. 2^S = 3^k + d, so
2^S ≡ 3^k mod d, not ≡ 1. So ord_d(2) ≠ S in general.

But for a SINGLE swap: (2^m - 1) ≡ 0 mod d iff d | (2^m - 1) iff ord_d(2) | m.
Since m = δ_i - δ_{i+1} ≤ S-k < S, and ord_d(2) is typically large:
it's UNLIKELY that ord_d(2) | m. But not impossible.

However: even if one swap has ΔF = 0, other swaps might be nonzero.
The TOTAL correction is the CUMULATIVE effect of all swaps.

For bubble sort: we resolve crossings one at a time. Each swap either
contributes a nonzero ΔF or doesn't change F. The total correction
is the sum of all nonzero contributions.

QUESTION: Can the sum of nonzero contributions be ≡ 0 mod d?

This is a CANCELLATION question. Even if individual swaps are nonzero,
they could cancel each other mod d.

For small d: less room for cancellation.
For large d: more room, but also more swaps.

Let me analyze the STRUCTURE of the total correction more carefully.

Actually, the total correction F(sorted) - F(unsorted) can be computed
DIRECTLY without decomposing into swaps:

F(sorted) - F(unsorted) = Σ_{i=1}^{k-1} (ρ^{rank_sorted(i)} - ρ^{rank_unsorted(i)}) · 2^{δ_values(i)}

where rank(i) is the position of the i-th δ value in each arrangement.

Hmm, this is complex. Let me just verify more k values and look for patterns.
"""

import sys, os
from math import ceil, log2, comb, gcd
from itertools import product as cart_product

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import compute_S, compute_d


def extended_verification(k_max=10):
    """Verify nonvanishing for larger k using only the target-hitting free sequences."""
    print("EXTENDED NONVANISHING VERIFICATION")
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

        # Need: for every δ with F(δ) ≡ 0 mod d, F(sorted(δ)) ≢ 0 mod d.
        # Equivalently: the image of the "sorted map" avoids 0.

        total_free = (max_delta + 1) ** (k - 1)
        if total_free > 2000000:
            print(f"  k={k}: {total_free} free sequences, too many. Using sampling.")
            # Sample random δ sequences, check if any sorted ones hit 0
            import random
            random.seed(42)
            n_samples = min(500000, total_free)
            n_sorted_zero = 0
            for _ in range(n_samples):
                deltas = tuple(random.randint(0, max_delta) for _ in range(k-1))
                sorted_d = tuple(sorted(deltas))
                f_sorted = (1 + sum(rho_pow[i+1] * two_pow[sorted_d[i]] % d
                                   for i in range(k-1))) % d
                if f_sorted == 0:
                    n_sorted_zero += 1

            print(f"  k={k}, d={d}: sampled {n_samples}, sorted F=0: {n_sorted_zero}")
            if n_sorted_zero == 0:
                print(f"    ✓ No sorted sequence hits 0 (in sample)")
            continue

        # Exhaustive
        n_free_zero = 0
        n_sorted_zero = 0
        all_corrections_nonzero = True

        for deltas in cart_product(range(max_delta + 1), repeat=k-1):
            f_val = (1 + sum(rho_pow[i+1] * two_pow[deltas[i]] % d
                            for i in range(k-1))) % d
            if f_val == 0:
                n_free_zero += 1
                sorted_d = tuple(sorted(deltas))
                f_sorted = (1 + sum(rho_pow[i+1] * two_pow[sorted_d[i]] % d
                                   for i in range(k-1))) % d
                if f_sorted == 0:
                    n_sorted_zero += 1
                    all_corrections_nonzero = False
                    print(f"  *** k={k}: sorted δ={sorted_d} ALSO hits 0! ***")

        print(f"  k={k}, d={d}: free_zero={n_free_zero}, sorted_zero={n_sorted_zero}, "
              f"corrections_all_nonzero={all_corrections_nonzero}")


def analyze_ord_d_2(k_max=30):
    """Compute ord_d(2) for each k. This controls when individual swaps can vanish."""
    print("\n═══ ord_d(2) ANALYSIS ═══")
    print(f"{'k':>3} {'d':>12} {'ord_d(2)':>10} {'S-k':>5} {'ord>S-k':>8}")
    print("-" * 45)

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue

        # Compute ord_d(2)
        x = 2 % d
        ord2 = 1
        while x != 1 and ord2 < d:
            x = (x * 2) % d
            ord2 += 1
        if x != 1:
            ord2 = -1  # Should not happen

        sk = S - k
        ord_gt = ord2 > sk if ord2 > 0 else False

        print(f"{k:3d} {d:12d} {ord2:10d} {sk:5d} {'✓' if ord_gt else '✗':>8}")

        # If ord_d(2) > S-k: no individual swap can have (2^m-1) ≡ 0 mod d
        # because m ≤ S-k < ord_d(2), so 2^m ≢ 1 mod d.
        # This means EVERY individual swap correction is nonzero!

        if ord_gt:
            pass  # Great: individual swaps always nonzero
        else:
            # There exist m ≤ S-k with ord_d(2) | m.
            # Individual swaps at those gaps might vanish.
            divisors = [m for m in range(1, sk+1) if m % ord2 == 0]
            if divisors:
                print(f"      WARNING: gaps {divisors[:5]} have 2^m ≡ 1 mod d")


if __name__ == '__main__':
    extended_verification()
    analyze_ord_d_2()
