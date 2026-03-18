#!/usr/bin/env python3
"""
ORDERING FORMALIZATION — Why does ordering block the target?
==============================================================

Setup: REST'+1 = Σ_{i=0}^{k-1} ρ^i · 2^{δ_i} where δ weakly increasing, δ_0=0.
Target: REST'+1 ≡ 0 mod d (i.e., corrSum ≡ 0 mod d).

The UNORDERED version: choose k values from {0}∪{2^j : j≥0} and multiply
by ARBITRARY assignment of {ρ^0,...,ρ^{k-1}}.

KEY ALGEBRAIC FACT to exploit:
In Z/dZ, ρ = 2·3^{-1}, so 3ρ = 2, and ρ^S = 2^S·3^{-S} = 3^{k-S} mod d.

The polynomial Σ ρ^i · 2^{δ_i} with δ weakly increasing can be written as:
P(ρ) = Σ ρ^i · 2^{δ_i} = Σ ρ^i · (3ρ)^{δ_i} = Σ 3^{δ_i} · ρ^{i+δ_i}
     = Σ 3^{δ_i} · ρ^{σ_i}   (since σ_i = i + δ_i)

This is a sum of terms 3^{δ_i} · ρ^{σ_i} where:
- σ_i are STRICTLY INCREASING (cumulative positions)
- δ_i are WEAKLY INCREASING (excesses)
- 3^{δ_i} are weakly increasing (BIGGER for later positions)
- ρ^{σ_i}: in Z, these DECREASE (|ρ|=2/3 < 1). In Z/dZ, no ordering.

In Z: the terms 3^{δ_i} · (2/3)^{σ_i} = 3^{δ_i-σ_i} · 2^{σ_i} = 3^{-i} · 2^{σ_i}
which INCREASE with i (since σ_i increases and 3^{-i} decreases slower than 2^{σ_i} grows).

Actually 3^{-i}·2^{σ_i}: since σ_i ≥ i, this is ≥ (2/3)^i → 0 but the 2^{σ_i}
factor dominates for σ_i > i·log₂(3).

Hmm, let me try a more concrete approach.

APPROACH: Generating function.
Define F_δ(X) = Σ_{i=0}^{k-1} X^i · 2^{δ_i} where δ weakly increasing, δ_0=0.

The ORDERED constraint is: δ_i ≥ δ_{i-1} (weakly increasing).

F_δ(ρ) = REST'+1. We need F_δ(ρ) ≢ 0 mod d for all valid δ.

The set of all valid F_δ(ρ) mod d is the IMAGE of the "ordered evaluation map".
We need to show 0 ∉ Image.

The UNORDERED version has much larger image (covers everything mod d).
The ordering RESTRICTS the image.

CONCRETE TEST: For k=3, there are very few δ sequences.
k=3, S=5: δ = (0, δ₁, δ₂) with 0 ≤ δ₁ ≤ δ₂ ≤ 2 (since σ₂ < S and σ₂ = 2+δ₂, so δ₂ ≤ 2).
Wait: σ₂ < S=5 and σ₂ = 2 + δ₂, so δ₂ ≤ 2.
δ₁ ≤ δ₂ and δ₁ ≥ 0.

Possible δ: (0,0,0), (0,0,1), (0,0,2), (0,1,1), (0,1,2), (0,2,2). That's 6.

F_δ(ρ) = 1 + ρ·2^{δ₁} + ρ²·2^{δ₂} mod 5.
ρ = 2/3 mod 5 = 2·2 = 4 mod 5 (since 3^{-1} = 2 mod 5).
ρ² = 16 mod 5 = 1.

F values:
(0,0,0): 1 + 4·1 + 1·1 = 6 ≡ 1 mod 5
(0,0,1): 1 + 4·1 + 1·2 = 7 ≡ 2 mod 5
(0,0,2): 1 + 4·1 + 1·4 = 9 ≡ 4 mod 5
(0,1,1): 1 + 4·2 + 1·2 = 11 ≡ 1 mod 5
(0,1,2): 1 + 4·2 + 1·4 = 13 ≡ 3 mod 5
(0,2,2): 1 + 4·4 + 1·4 = 21 ≡ 1 mod 5

Values mod 5: {1, 2, 3, 4}. Missing: {0}. ✓
Target 0 is avoided!

Note: ρ² = 1 mod 5 (since ord_5(ρ) = ord_5(4) = 2).
So F = 1 + 4·2^{δ₁} + 2^{δ₂} mod 5.
For F = 0: 4·2^{δ₁} + 2^{δ₂} ≡ 4 mod 5.

2^{δ} mod 5 cycles: 1, 2, 4, 3, 1, ...
So for valid δ₁ ∈ {0,1,2}: 2^{δ₁} mod 5 ∈ {1,2,4}.
And δ₂ ∈ {δ₁,...,2}: 2^{δ₂} ∈ {1,2,4}.

Need: 4·X + Y ≡ 4 mod 5 where X ∈ {1,2,4}, Y ∈ {X,...,4} (weakly increasing δ).

4·1 + Y ≡ 4: Y ≡ 0 mod 5 — impossible (Y ∈ {1,2,4})
4·2 + Y ≡ 4: Y ≡ -4 ≡ 1 mod 5 — Y=1, need 2^{δ₂}=1, δ₂=0. But δ₂ ≥ δ₁=1, so δ₂ ≥ 1, 2^{δ₂} ∈ {2,4} ≠ 1. BLOCKED by ordering!
4·4 + Y ≡ 4: Y ≡ -12 ≡ 3 mod 5 — Y=3, need 2^{δ₂}=3, δ₂=3. But δ₂ ≤ 2. BLOCKED by range!

★★★ For k=3: the ordering AND range constraints together block ALL solutions!
The case (δ₁=1, need δ₂=0 but ordering forces δ₂≥1) is the PURE ordering block.
The case (δ₁=2, need δ₂=3 but range forces δ₂≤2) is a RANGE block.

This is a COMPLETE ALGEBRAIC PROOF for k=3!
"""

import sys, os
from math import ceil, log2, comb, gcd
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


def algebraic_proof_attempt(k):
    """Try to construct an explicit algebraic proof for a given k."""
    S = compute_S(k)
    d = compute_d(k)
    if d <= 0: return

    inv3 = pow(3, -1, d)
    rho = (2 * inv3) % d  # ρ = 2/3 mod d

    # Order of ρ mod d
    ord_rho = 1
    x = rho
    while x != 1 and ord_rho < d:
        x = (x * rho) % d
        ord_rho += 1

    print(f"\nk={k}, S={S}, d={d}, ρ={rho}, ord(ρ)={ord_rho}")

    # Enumerate all δ sequences and compute F_δ(ρ) mod d
    max_delta = S - k  # δ_{k-1} ≤ S-k
    print(f"  δ range: [0, {max_delta}]")

    # For the target F=0: need Σ ρ^i · 2^{δ_i} ≡ 0 mod d
    # with 0 = δ_0 ≤ δ_1 ≤ ... ≤ δ_{k-1} ≤ max_delta

    # Compute ρ^i mod d and 2^j mod d tables
    rho_pow = [pow(rho, i, d) for i in range(k)]
    two_pow = [pow(2, j, d) for j in range(max_delta + 1)]

    # For each possible (δ_1,...,δ_{k-1}) weakly increasing in [0, max_delta]:
    # F = 1 + Σ_{i=1}^{k-1} ρ^i · 2^{δ_i}
    # Need F ≡ 0: Σ ρ^i · 2^{δ_i} ≡ -1 mod d

    target = (-1) % d

    # For small k, enumerate all and check
    from itertools import combinations_with_replacement

    n_total = 0
    n_target = 0
    blocking_reasons = []

    for deltas in combinations_with_replacement(range(max_delta + 1), k - 1):
        # δ = (0, deltas[0], deltas[1], ..., deltas[k-2])
        inner_sum = sum(rho_pow[i+1] * two_pow[deltas[i]] % d for i in range(k-1)) % d
        n_total += 1
        if inner_sum == target:
            n_target += 1
            # This would mean F = 0 → cycle exists!
            print(f"  *** TARGET HIT! δ = (0, {', '.join(map(str, deltas))})")
            print(f"      inner_sum = {inner_sum} = target {target}")

    print(f"  Total δ sequences: {n_total}")
    print(f"  Target hits: {n_target}")
    if n_target == 0:
        print(f"  ✓ No δ sequence hits target → N₀=0 for k={k}")

    # Now try WITHOUT ordering constraint (arbitrary δ, not necessarily increasing)
    from itertools import product as cart_product
    n_free = 0
    n_free_target = 0
    if (max_delta + 1)**(k-1) <= 100000:
        for deltas in cart_product(range(max_delta + 1), repeat=k-1):
            inner_sum = sum(rho_pow[i+1] * two_pow[deltas[i]] % d for i in range(k-1)) % d
            n_free += 1
            if inner_sum == target:
                n_free_target += 1

        print(f"  Free (unordered) δ: {n_free} sequences, {n_free_target} hits target")
        if n_free_target > 0 and n_target == 0:
            print(f"  ★ Ordering BLOCKS {n_free_target} solutions that exist without it!")


if __name__ == '__main__':
    print("ALGEBRAIC PROOF VIA δ-SEQUENCES")
    print("=" * 60)
    for k in range(3, 12):
        algebraic_proof_attempt(k)
