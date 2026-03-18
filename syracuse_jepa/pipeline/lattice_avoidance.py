#!/usr/bin/env python3
"""
LATTICE AVOIDANCE — corrSum viewed as lattice points avoiding d·Z
===================================================================

corrSum(σ) = Σ 3^{k-1-i} · 2^{σ_i} where σ strictly increasing, σ_0=0.

The set {corrSum(σ)} ⊂ Z is a SPECIFIC finite set of positive integers.
The lattice d·Z = {0, d, 2d, 3d, ...} is a regular grid.

N₀ = 0 iff {corrSum(σ)} ∩ d·Z = ∅.

NEW APPROACH: Think of corrSum as a WEIGHTED BINARY SUM.

Define weights w_v = 0 for v=0, and for v=1,...,S-1:
w_v = 3^{k-1-rank(v)} where rank(v) is the position of v when v is chosen.

Wait, the weight depends on the RANK, not the value. This makes it complex.

SIMPLER: corrSum = 3^{k-1} + Σ_{v∈T} 3^{k-1-rank_T(v)} · 2^v

where T = {σ_1,...,σ_{k-1}} ⊂ {1,...,S-1} is the chosen set,
and rank_T(v) = position of v in T (1-indexed).

The CRITICAL observation: the weight of 2^v depends on WHERE v falls
in the ordered set T. A value near the beginning gets a high 3-weight;
a value near the end gets a low 3-weight.

This creates a MULTIPLICATIVE interaction between the position and the value.

THOUGHT EXPERIMENT: What if the weights were INDEPENDENT of rank?
If corrSum = 3^{k-1} + c · Σ_{v∈T} 2^v for some constant c:
then corrSum = 3^{k-1} + c · (2^{σ_1} + ... + 2^{σ_{k-1}}).
The sum Σ 2^{σ_i} for T ⊂ {1,...,S-1}, |T|=k-1, ranges over all numbers
with exactly k-1 ones in binary positions 1,...,S-1.
This is a well-understood combinatorial set.
And asking if d | (3^{k-1} + c·Σ2^{σ_i}) for some T is a NUMBER-THEORETIC
question about the set of (k-1)-element subsets of {1,...,S-1} weighted by 2^v.

The ACTUAL problem has rank-dependent weights, which makes it harder.
But maybe the rank dependence HELPS (creates more structure, more constraint).

Let me investigate: what is the BINARY REPRESENTATION of corrSum?
corrSum = 3^{k-1}·1 + 3^{k-2}·2^{σ_1} + ... + 1·2^{σ_{k-1}}

In binary: 3^{k-1} has binary representation with O(k) bits.
The other terms shift it by σ_i positions and scale by 3^{k-1-i}.

The binary structure of corrSum encodes the CARRY pattern.
"""

import sys, os
from math import ceil, log2, comb
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


def binary_analysis(k_max=10):
    """Analyze the binary structure of corrSum values."""
    print("BINARY STRUCTURE OF corrSum")
    print("=" * 60)

    for k in [3, 5, 7]:
        S = compute_S(k)
        d = compute_d(k)
        C = count_cumulative_sequences(k, S)
        if C > 1000: continue

        print(f"\nk={k}, S={S}, d={d} = {bin(d)}")
        print(f"  d in binary: {bin(d)[2:]}")

        for sigma in enumerate_cumulative_sequences(k, S):
            cs = corrsum_cumulative(sigma, k)
            r = cs % d
            q = cs // d
            print(f"  σ={sigma}: cs={cs} = {q}·{d} + {r}")
            # Binary of cs
            cs_bin = bin(cs)[2:]
            d_bin = bin(d)[2:]
            # Highlight multiples of d
            marker = " *** DIV ***" if r == 0 else ""
            # Show binary alignment
            print(f"    cs = {cs_bin}{marker}")


def subset_sum_perspective(k_max=10):
    """
    Reformulate: corrSum = constant + weighted_subset_sum(T).

    For a fixed k, the "constant" part is 3^{k-1} (from σ_0=0).
    The "variable" part is Σ_{i=1}^{k-1} 3^{k-1-i}·2^{σ_i}.

    The variable part is a RANK-WEIGHTED subset sum.

    Question: does the set of achievable variable-part values,
    shifted by 3^{k-1}, ever hit d·Z?

    This is a GENERALIZED SUBSET SUM problem with weighted selection.
    """
    print("\nSUBSET SUM PERSPECTIVE")
    print("=" * 60)

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        C = count_cumulative_sequences(k, S)
        if C > 200000: continue

        base = pow(3, k-1)
        target_mod = (-base) % d  # Variable part must be ≡ this mod d

        # Compute all achievable variable-part values mod d
        var_residues = set()
        for sigma in enumerate_cumulative_sequences(k, S):
            var = sum(pow(3, k-1-i) * pow(2, sigma[i]) for i in range(1, k))
            var_residues.add(var % d)

        hits_target = target_mod in var_residues
        n_residues = len(var_residues)
        coverage = n_residues / d

        print(f"k={k}: target={target_mod}, {n_residues}/{d} residues achieved ({coverage:.3f})")
        print(f"  Target achieved: {hits_target}")
        if not hits_target:
            print(f"  ✓ Variable part NEVER hits the target → N₀=0")

        # What's the distance from target to nearest achieved?
        if not hits_target:
            min_dist = min(min(abs(r - target_mod), d - abs(r - target_mod))
                         for r in var_residues)
            print(f"  Min distance to target: {min_dist}")


def generalized_frobenius(k_max=10):
    """
    FROBENIUS NUMBER perspective:
    The Frobenius number of {a_1,...,a_n} is the largest integer NOT
    representable as a non-negative integer combination of a_1,...,a_n.

    Our problem: can corrSum ≡ 0 mod d? This is a REPRESENTABILITY question.
    corrSum = Σ c_i · 2^{σ_i} where c_i = 3^{k-1-i}.

    Not a standard subset sum (rank-dependent weights), but related.

    If d > Frobenius number of {c_1·2^v mod d : v=1..S-1}, then every
    residue mod d is achievable → 0 is achievable → N₀ > 0.

    If d < Frobenius: some residues are NOT achievable → maybe 0 is among them.

    For large k: d >> the "generators" → Frobenius argument suggests all
    residues are achievable. But our data shows 0 is NOT achieved!

    This means: the RANK-DEPENDENCE of weights prevents 0 from being achieved,
    even though individual generators can produce any residue.
    """
    print("\nGENERALIZED FROBENIUS ANALYSIS")
    print("=" * 60)

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 200000: continue

        # The "generators" (ignoring rank): {2^v mod d : v=1..S-1}
        gen = set(pow(2, v, d) for v in range(1, S))
        print(f"\nk={k}: |generators 2^v mod d| = {len(gen)} (out of {d-1} possible non-zero)")

        # Can we reach ALL non-zero residues using k-1 of these generators
        # (with rank-dependent 3-weights)?
        # If yes: N₀ should be > 0. But it's NOT!
        # The rank-dependence is the KEY constraint.

        # Specifically: choosing v_1 < v_2 < ... < v_{k-1},
        # the weighted sum is 3^{k-2}·2^{v_1} + 3^{k-3}·2^{v_2} + ... + 2^{v_{k-1}}
        # The FIRST chosen value gets the HIGHEST 3-weight.
        # The LAST chosen value gets weight 1.

        # If we could choose the weights INDEPENDENTLY of order:
        # any permutation of weights would give a different sum.
        # But the ordering constraint σ_1 < σ_2 < ... < σ_{k-1} FIXES the weight assignment.

        # Number of (unordered) ways to choose k-1 values from {1,...,S-1}: C(S-1,k-1)
        # Number of (ordered) ways: (S-1)! / (S-k)! (much more)
        # The ordering constraint REDUCES the number of achievable sums.

        # What fraction of residues mod d can be achieved WITHOUT the ordering constraint?
        # (i.e., allowing any assignment of 3-weights to chosen values)
        all_residues_unordered = set()
        from itertools import permutations
        if C <= 500:
            for combo in combinations(range(1, S), k-1):
                # Try all permutations of 3-weights
                weights = [pow(3, k-2-j) for j in range(k-1)]
                for perm in permutations(range(k-1)):
                    val = sum(weights[perm[j]] * pow(2, combo[j]) for j in range(k-1)) % d
                    all_residues_unordered.add(val)

            ordered_residues = set()
            for sigma in enumerate_cumulative_sequences(k, S):
                var = sum(pow(3, k-1-i) * pow(2, sigma[i]) for i in range(1, k))
                ordered_residues.add(var % d)

            target = (-pow(3, k-1)) % d
            print(f"  Ordered residues: {len(ordered_residues)}/{d}, "
                  f"unordered: {len(all_residues_unordered)}/{d}")
            print(f"  Target {target} in ordered: {target in ordered_residues}")
            print(f"  Target {target} in unordered: {target in all_residues_unordered}")

            if target in all_residues_unordered and target not in ordered_residues:
                print(f"  ★ ORDERING CONSTRAINT is what blocks the target!")


if __name__ == '__main__':
    subset_sum_perspective()
    generalized_frobenius()
