#!/usr/bin/env python3
"""
REARRANGEMENT PROOF ATTEMPT
=============================

Hardy-Littlewood Rearrangement: for two sequences sorted oppositely,
Σ a_i · b_i is MINIMIZED.

Our case: a_i = 3^{k-1-i} (decreasing), b_i = 2^{σ_i} (increasing).
The ordered sum IS the minimum over all permutations of the a-weights.

For a cycle: we need Σ a_{π(i)} · b_i ≡ target mod d for SOME permutation π.
The ordered case (identity permutation) gives the minimum.

If we can show that the MINIMUM over permutations already exceeds
the target in a suitable sense, then no permutation (including identity) works.

BUT: we're working mod d, so "minimum" doesn't directly apply.
The rearrangement gives a bound in Z, not Z/dZ.

REFINED APPROACH: The gap between the ORDERED sum and the UNORDERED sums
is bounded. If this gap is < d, then the mod d residues of ordered and
unordered sums differ by < d → the target can only be hit by the ordered
sum if it's also "close" to being hit in Z.

Actually: the rearrangement inequality gives:
S_ordered ≤ S_π ≤ S_reversed (for any permutation π).

S_ordered = Σ 3^{k-1-i} · 2^{σ_i} (decreasing × increasing = anti-aligned)
S_reversed = Σ 3^{i} · 2^{σ_i} (increasing × increasing = aligned)

The gap: S_reversed - S_ordered = Σ (3^i - 3^{k-1-i}) · 2^{σ_i}

For i < (k-1)/2: 3^i < 3^{k-1-i}, so contribution is negative.
For i > (k-1)/2: 3^i > 3^{k-1-i}, so contribution is positive.
Net effect: dominated by the large terms (i near k-1 and i near 0).

The gap is O(3^{k-1} · 2^{σ_{k-1}}) ≈ O(3^k · 2^S / 3) which is >> d.
So the rearrangement gap is MUCH larger than d.

This means: the mod d residues of S_ordered and S_reversed are UNRELATED.
The rearrangement inequality in Z doesn't constrain the mod d behavior.

DEAD END? Not necessarily. The rearrangement tells us about the STRUCTURE
of the ordered sum, even if the mod d residues are "free".

NEW IDEA: Instead of the rearrangement inequality, use the SPECIFIC
structure of a_i = 3^{k-1-i} and b_i = 2^{σ_i}.

The ordered sum: Σ 3^{k-1-i} · 2^{σ_i} with σ strictly increasing.
Factor: = 3^{k-1} · Σ (2/3)^{σ_i} · 3^{σ_i-i} = 3^{k-1} · Σ (2/3)^{σ_i} · 3^{δ_i}

where δ_i = σ_i - i ≥ 0 (weakly increasing).

Using ρ = 2/3 and 3ρ = 2:
= 3^{k-1} · Σ ρ^{σ_i} · 3^{δ_i} = 3^{k-1} · Σ (3ρ)^{δ_i} · ρ^i
= 3^{k-1} · Σ 2^{δ_i} · ρ^i

THIS IS THE REST' + 1 FORMULA!
REST' + 1 = Σ 2^{δ_i} · ρ^i (working mod d with ρ = 2/3).

Now: the δ_i are weakly increasing with δ_0 = 0.
REST' + 1 = 1 + ρ·2^{δ_1} + ρ²·2^{δ_2} + ... + ρ^{k-1}·2^{δ_{k-1}}

The ORDERING constraint means: δ_i ≤ δ_{i+1} (weakly increasing).
And the unordered case allows ANY assignment of δ values to positions.

The key: REST' + 1 is a POLYNOMIAL in ρ with coefficients 2^{δ_i}.
Since ρ^S ≡ 3^{k-S} mod d (from α^S = 3^k, ρ = α/3):
The polynomial is evaluated at ρ, a specific algebraic number mod d.

FOR THE TARGET REST' + 1 = 0 mod d:
We need Σ 2^{δ_i} · ρ^i ≡ 0 mod d.
This is a POLYNOMIAL IN ρ evaluated at ρ = 2/3 mod d.
The polynomial has coefficients 2^{δ_i} (positive powers of 2).

CLAIM: A polynomial with POSITIVE power-of-2 coefficients, evaluated
at ρ = 2/3 mod d (where d = 2^S - 3^k), cannot be 0 mod d.

WHY? Because in Z: the sum Σ 2^{δ_i} · (2/3)^i is a POSITIVE rational.
Multiplied by 3^{k-1}: corrSum = 3^{k-1} · (REST'+1) is a positive integer.
In Z/dZ: the positivity of the real evaluation CONSTRAINS the mod d residue.

But we already know corrSum > d (L1 true universally), so the mod d residue
of corrSum can be anything in {1,...,d-1}... OR 0. We need to exclude 0.

The POSITIVITY of coefficients + the algebraic constraint ρ^S = 3^{k-S}
might create a FORMAL algebraic obstruction. Let me test specific cases.
"""

import sys, os
from math import ceil, log2, comb, gcd
from itertools import combinations, permutations
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


def test_ordering_vs_free(k_max=8):
    """
    For each k, compare:
    1. Ordered sums (σ monotone → a-weights anti-aligned with b-values)
    2. Free sums (any permutation of a-weights)

    Does the ordering always exclude the target?
    """
    print("ORDERING vs FREE: Does ordering ALWAYS block the target?")
    print("=" * 70)

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 500: continue  # Need to enumerate permutations too

        base = pow(3, k-1)
        target = (-base) % d

        # Ordered residues
        ordered = set()
        for sigma in enumerate_cumulative_sequences(k, S):
            var = sum(pow(3, k-1-i) * pow(2, sigma[i]) for i in range(1, k))
            ordered.add(var % d)

        # Free residues (k-1 values chosen, any weight assignment)
        free = set()
        weights = [pow(3, k-2-j) for j in range(k-1)]

        for combo in combinations(range(1, S), k-1):
            values = [pow(2, v) for v in combo]
            # Try all permutations of weights (or values)
            for perm in permutations(range(k-1)):
                s = sum(weights[perm[j]] * values[j] for j in range(k-1))
                free.add(s % d)

        # Only in free but not in ordered:
        free_only = free - ordered

        print(f"  k={k}: ordered {len(ordered)}/{d}, free {len(free)}/{d}")
        print(f"    Target {target}: ordered={'✗' if target not in ordered else '!!!'}, "
              f"free={'✓ HIT' if target in free else '✗'}")
        print(f"    Free-only residues: {len(free_only)}")
        if target in free_only:
            print(f"    ★ Target is EXCLUSIVELY in free (ordering blocks it)")


if __name__ == '__main__':
    test_ordering_vs_free()
