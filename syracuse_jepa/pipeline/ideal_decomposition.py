#!/usr/bin/env python3
"""
IDEAL DECOMPOSITION — The prime ideal (α-2) in Z[α]
=====================================================

When X^S - 3^k is irreducible over Q and d = N(α-2):
(d) = (α-2)·(α·ζ-2)·...·(α·ζ^{S-1}-2) in Z[α] (up to units).

If d is prime: (d) = (α-2) is already prime. Simple case.
If d is composite: (d) decomposes into multiple prime ideals.

The KEY question: does P_σ(α) belong to the prime ideal p = (α-2, d)?

In Z[α]/p ≅ Z/dZ (when d is prime): P_σ(α) mod p = P_σ(2) mod d.
So P_σ(α) ∈ p ⟺ P_σ(2) ≡ 0 mod d. This is exactly our question!

The ideal-theoretic approach gives a DIFFERENT perspective:
Instead of asking "is corrSum divisible by d?", ask
"does the algebraic integer P_σ(α) lie in the prime ideal (α-2, d)?"

This connects to:
- The Frobenius endomorphism of Z[α] at the prime d
- The splitting behavior of d in K = Q(α)
- The class group of Z[α] (if Z[α] ≠ O_K)

For a UNIVERSAL proof: we need to show that the SET
{P_σ(α) : σ ∈ Comp_cum(S,k)} never intersects the ideal p = (α-2, d).

This is a GEOMETRIC statement about a set of lattice points in Z[α]
avoiding a specific prime ideal. Similar to Minkowski's theorem in
the geometry of numbers, but with a SPECIFIC set instead of a generic one.

APPROACH: Compute the image of {P_σ(α)} in Z[α]/p for small k
and look for STRUCTURAL reasons it avoids 0.
"""

import sys, os
from math import ceil, log2, comb, gcd
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


def analyze_image_in_residue_field(k):
    """
    Compute the image of {P_σ(α)} in Z[α]/(α-2) ≅ Z/dZ.
    This is just {corrSum mod d} — same as before.

    But NOW think of it as: the image of an algebraic set in a residue field.
    The set {P_σ} is parameterized by σ ∈ Comp_cum(S,k).
    P_σ(X) = Σ 3^{k-1-i} · X^{σ_i}.

    In Z[α], each P_σ is a FIXED algebraic integer.
    The evaluation at α = 2 gives the image in Z/dZ.

    KEY: P_σ(α) = Σ 3^{k-1-i} · α^{σ_i}.
    In Z[α], α^S = 3^k. No reduction needed since σ_i < S.

    The structure of P_σ: it's a SUM of terms 3^{k-1-i} · α^{σ_i}
    where each term lies in the MONOMIAL LATTICE Z·3^a·α^b.

    The set of all corrSum values = {P_σ(2)} = evaluations of these
    lattice points at α = 2.

    INSIGHT: In Z[α], the element α is a ROOT OF UNITY times 3^{k/S}.
    The "distance" between α and 2 (in the sense of the ideal (α-2))
    is measured by d = N(α-2) = 2^S - 3^k.

    P_σ(α) - P_σ(2) = Σ 3^{k-1-i} · (α^{σ_i} - 2^{σ_i}).
    Each term α^{σ_i} - 2^{σ_i} is divisible by (α-2) in Z[α] (since
    X^n - Y^n = (X-Y)(X^{n-1} + ... + Y^{n-1})).

    So P_σ(α) ≡ P_σ(2) mod (α-2) in Z[α]. Which we already knew.

    The DEEPER question: what is the FULL ideal factorization of P_σ(α)?
    If (α-2) never appears in the factorization, then P_σ(2) ≢ 0 mod d.
    """
    S = compute_S(k)
    d = compute_d(k)
    if d <= 0: return

    # For each σ, compute corrSum and analyze its divisibility
    # The "ideal structure" in Z[α] is encoded by the divisibility of P_σ(2) by factors of d

    print(f"\nk={k}, S={S}, d={d}, K = Q(α), α^{S} = {3**k}")

    C = count_cumulative_sequences(k, S)
    if C > 50000:
        print(f"  C={C} too large")
        return

    # In Z[α], P_σ(α) = Σ 3^{k-1-i} · α^{σ_i}
    # The KEY structure: each term is a MONOMIAL in {3, α}.
    # 3^{k-1-i} · α^{σ_i} = 3^{k-1-i} · α^{σ_i}
    #
    # Using α^S = 3^k: we can write α = 3^{k/S} (formally).
    # So each term = 3^{k-1-i} · 3^{k·σ_i/S} = 3^{k-1-i + k·σ_i/S}.
    # But k·σ_i/S is NOT in general an integer!
    #
    # In the NUMBER FIELD K: 3 and α are algebraically related by α^S = 3^k.
    # The LATTICE of exponents {(a, b) : 3^a · α^b} with relation (k, -S) ~ (0, 0).

    # Let me compute: for each σ, what is corrSum mod d^2?
    # (This detects whether corrSum is "close to" a multiple of d in a deeper sense.)

    d2 = d * d
    residues_mod_d = []
    residues_mod_d2 = []

    for sigma in enumerate_cumulative_sequences(k, S):
        cs = corrsum_cumulative(sigma, k)
        residues_mod_d.append(cs % d)
        residues_mod_d2.append(cs % d2)

    n_zero_d = sum(1 for r in residues_mod_d if r == 0)
    n_zero_d2 = sum(1 for r in residues_mod_d2 if r == 0)

    # How many are ≡ 0 mod d but not mod d^2?
    # (These would give n₀ not divisible by d, which is extra information.)

    print(f"  N₀(d) = {n_zero_d}, N₀(d²) = {n_zero_d2}")
    print(f"  (N₀(d²) = 0 is stronger than N₀(d) = 0)")

    # COMPUTE: what is the distribution of corrSum/d mod d?
    # (For corrSum divisible by d: corrSum = n₀·d, and n₀ mod d gives the "second layer".)
    # Since N₀(d) = 0, this is vacuous. But let's look at corrSum/d as a rational:

    quotients = [corrsum_cumulative(sigma, k) // d for sigma in enumerate_cumulative_sequences(k, S)]
    q_residues = [q % d for q in quotients]
    n_distinct = len(set(q_residues))

    print(f"  corrSum/d (rounded): {min(quotients)}..{max(quotients)}")
    print(f"  corrSum//d mod d: {n_distinct} distinct values out of {d}")

    # THE ALLEGORY: Think of corrSum/d as the "height" of P_σ(α) above the ideal (α-2).
    # If this height is never exactly an integer, the ideal is never reached.
    # The height is "quantized" — it can only take values in a DISCRETE set.
    # The question is: does this discrete set include any integers?


def investigate_common_factor_pattern(k_max=12):
    """
    For each σ, compute gcd(P_σ(2), d) and look for patterns.
    We know gcd = d iff corrSum ≡ 0 mod d (never happens).
    But the DISTRIBUTION of gcd values might reveal structure.

    HYPOTHESIS: gcd(corrSum, d) is always a PROPER divisor of d,
    and the set of achieved gcds has a specific pattern.
    """
    print("\n═══ GCD PATTERN DEEP DIVE ═══")

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 200000: continue

        gcd_set = set()
        for sigma in enumerate_cumulative_sequences(k, S):
            cs = corrsum_cumulative(sigma, k)
            g = gcd(cs, d)
            gcd_set.add(g)

        # What divisors of d are achieved?
        all_divisors = set(i for i in range(1, d+1) if d % i == 0)
        achieved = gcd_set
        not_achieved = all_divisors - achieved

        print(f"\n  k={k}, d={d}: {len(achieved)}/{len(all_divisors)} divisors achieved as gcd(corrSum,d)")
        if d in not_achieved:
            print(f"    d={d} NOT achieved ✓ (= N₀(d)=0)")

        # KEY: is d ALWAYS the only large divisor not achieved?
        large_not = [x for x in not_achieved if x > d/2]
        print(f"    Large unachieved (> d/2): {sorted(large_not)}")

        # Check: is d the ONLY unachieved divisor?
        if not_achieved == {d}:
            print(f"    ★ d is the UNIQUE unachieved divisor!")
        elif len(not_achieved) <= 5:
            print(f"    Unachieved: {sorted(not_achieved)}")


if __name__ == '__main__':
    print("IDEAL DECOMPOSITION ANALYSIS")
    print("=" * 60)

    for k in range(3, 11):
        analyze_image_in_residue_field(k)

    investigate_common_factor_pattern()
