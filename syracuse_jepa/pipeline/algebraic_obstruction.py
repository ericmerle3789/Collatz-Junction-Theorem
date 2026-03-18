#!/usr/bin/env python3
"""
ALGEBRAIC OBSTRUCTION — Why REST avoids -3^{k-1} mod d
========================================================

AUTONOMOUS LOOP: Decompose → Test → Mutate → Prove

corrSum = 3^{k-1} + REST where REST = Σ_{i=1}^{k-1} 3^{k-1-i} · 2^{σ_i}
corrSum ≡ 0 mod d ⟺ REST ≡ -3^{k-1} mod d

In Z/dZ where 2^S ≡ 3^k:
  REST = Σ_{i=1}^{k-1} 3^{k-1-i} · 2^{σ_i}
  target = -3^{k-1} mod d

DEEP QUESTION: What algebraic property prevents REST from hitting target?

APPROACH: Decompose REST using the relation 2^S = 3^k mod d.
For σ_i < S: 2^{σ_i} = 2^{σ_i} mod d (no reduction needed since σ_i < S and 2^S ≡ 3^k).

KEY OBSERVATION: In Z/dZ, define ρ = 2/3 (i.e., ρ = 2·3^{-1} mod d).
Then 3^{k-1-i}·2^{σ_i} = 3^{k-1}·ρ^{σ_i}·(3/2)^{σ_i-i}... no, this doesn't simplify.

Let me try: 3^{k-1-i}·2^{σ_i} = 3^{k-1}·(2/3)^i·2^{σ_i-i}... still messy.

Better: define REST' = REST/3^{k-1} = Σ_{i=1}^{k-1} 3^{-i}·2^{σ_i} in Z/dZ.
Then corrSum = 3^{k-1}·(1 + REST'), and corrSum ≡ 0 mod d ⟺ REST' ≡ -1 mod d/gcd(3^{k-1},d).
Since gcd(3,d) = 1: gcd(3^{k-1},d) = 1. So REST' ≡ -1 mod d.

SO: THE QUESTION REDUCES TO:
  Can Σ_{i=1}^{k-1} (2/3)^{σ_i} · 3^{σ_i-i} ≡ -1 mod d?
  where (2/3) is computed as 2·3^{-1} mod d.

No wait, let me redo this carefully.
REST' = Σ_{i=1}^{k-1} 3^{-i} · 2^{σ_i} mod d
      = Σ_{i=1}^{k-1} (3^{-1})^i · 2^{σ_i} mod d

Let γ = 3^{-1} mod d and α = 2 mod d. Then:
REST' = Σ_{i=1}^{k-1} γ^i · α^{σ_i}

And the constraint 2^S ≡ 3^k mod d means α^S ≡ γ^{-k} mod d.
i.e., (αγ)^S · γ^{S-k} · ... hmm, no.
α^S = 3^k = γ^{-k} mod d. So α^S · γ^k = 1 mod d. Let ρ = α·γ = 2·3^{-1} mod d.
Then ρ^k · γ^{S-k} · ... no.

Actually: α^S = γ^{-k} means (α^S)·(γ^k) = 1, i.e., 2^S · 3^{-k} ≡ 1 mod d.
Which is (2^S/3^k) ≡ 1 mod d, i.e., (2/3)^S · 3^{S-k} ≡ 1... still messy.

Let me just compute directly. ρ = 2·3^{-1} mod d. Then ρ^S = 2^S · 3^{-S} mod d.
And 2^S ≡ 3^k mod d. So ρ^S = 3^k · 3^{-S} = 3^{k-S} mod d.
Since S > k: ρ^S = 3^{-(S-k)} = γ^{S-k} mod d.

REST' = Σ_{i=1}^{k-1} γ^i · α^{σ_i}
      = γ · α^{σ_1} + γ^2 · α^{σ_2} + ... + γ^{k-1} · α^{σ_{k-1}}

Each term: γ^i · α^{σ_i} = (γ·α^{σ_i/i})^i · ... no.

Since ρ = α·γ: α = ρ·γ^{-1} = ρ·3. So α^{σ_i} = (ρ·3)^{σ_i} = ρ^{σ_i} · 3^{σ_i}.

Then: γ^i · α^{σ_i} = 3^{-i} · ρ^{σ_i} · 3^{σ_i} = 3^{σ_i - i} · ρ^{σ_i}

REST' = Σ_{i=1}^{k-1} 3^{σ_i - i} · ρ^{σ_i}

Let δ_i = σ_i - i ≥ 0 (the "excess" of each cumulative position over its rank).
Then σ_i = i + δ_i, with δ weakly increasing and δ_{k-1} < S - (k-1).

REST' = Σ_{i=1}^{k-1} 3^{δ_i} · ρ^{i + δ_i}
      = Σ_{i=1}^{k-1} (3ρ)^{δ_i} · ρ^i
      = Σ_{i=1}^{k-1} ρ^i · (3ρ)^{δ_i}

Now 3ρ = 3·2/3 = 2. So (3ρ) = α = 2 mod d!

REST' = Σ_{i=1}^{k-1} ρ^i · α^{δ_i}
      = Σ_{i=1}^{k-1} ρ^i · 2^{δ_i}

where δ_i = σ_i - i ≥ 0, weakly increasing, δ_{k-1} < S - k + 1.

THIS IS A BEAUTIFUL SIMPLIFICATION!
REST' = Σ ρ^i · 2^{δ_i} where ρ = 2/3 mod d and δ is weakly increasing from {0,...,S-k}.

The constraint ρ^S = 3^{-(S-k)} is equivalent to (2/3)^S = 3^{k-S} mod d.

AND: corrSum ≡ 0 mod d ⟺ REST' ≡ -1 mod d
⟺ Σ_{i=1}^{k-1} ρ^i · 2^{δ_i} ≡ -1 mod d

where ρ = 2·3^{-1} mod d.

NOW: if all δ_i = 0 (which happens when σ_i = i, the "minimal" sequence):
REST'_min = Σ_{i=1}^{k-1} ρ^i · 1 = ρ·(ρ^{k-1} - 1)/(ρ - 1)

And ρ^k = (2/3)^k. Since 2^S ≡ 3^k mod d: (2/3)^k ≡ 3^k/3^k · 2^k/3^k... no.
ρ^k = 2^k · 3^{-k} mod d. And 3^{-k} = 2^{-S} mod d (since 3^k ≡ 2^S).
So ρ^k = 2^k · 2^{-S} = 2^{k-S} mod d.

For k < S: ρ^k = 2^{k-S} = (2^{-1})^{S-k} = (2^{-1})^{S-k} mod d.

ANYWAY, the key result is the simplification:
  REST' = Σ_{i=1}^{k-1} ρ^i · 2^{δ_i}
  with δ weakly increasing in {0,...,S-k}

This connects to a "ρ-geometric sum with 2-powers at delays".
"""

import sys, os
from math import ceil, log2, comb, gcd
from itertools import combinations
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


def verify_rest_prime_formula(k_max=12):
    """Verify the REST' = Σ ρ^i · 2^{δ_i} formula."""
    print("VERIFICATION: REST' = Σ ρ^i · 2^{δ_i}")
    print("=" * 60)

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 100000: continue

        inv3 = pow(3, -1, d)
        rho = (2 * inv3) % d  # ρ = 2/3 mod d

        mismatches = 0
        target = (-1) % d  # REST' ≡ -1 mod d for cycle

        for sigma in enumerate_cumulative_sequences(k, S):
            # Direct REST'
            rest_prime_direct = sum(pow(inv3, i, d) * pow(2, sigma[i], d)
                                   for i in range(1, k)) % d

            # Via δ formula
            deltas = [sigma[i] - i for i in range(1, k)]
            rest_prime_delta = sum(pow(rho, i, d) * pow(2, deltas[i-1], d)
                                  for i in range(1, k)) % d

            if rest_prime_direct != rest_prime_delta:
                mismatches += 1

        status = "✓" if mismatches == 0 else f"✗ {mismatches} mismatches"
        # Count how many hit the target
        n_target = 0
        for sigma in enumerate_cumulative_sequences(k, S):
            rest_prime = sum(pow(inv3, i, d) * pow(2, sigma[i], d)
                           for i in range(1, k)) % d
            if rest_prime == target:
                n_target += 1

        print(f"  k={k}, ρ={rho} mod {d}: formula {status}, target_hits={n_target}")


def analyze_rho_structure(k_max=12):
    """Analyze the structure of ρ = 2/3 mod d."""
    print("\n═══ ρ = 2·3⁻¹ mod d STRUCTURE ═══")

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue

        inv3 = pow(3, -1, d)
        rho = (2 * inv3) % d

        # Order of ρ in (Z/dZ)*
        ord_rho = 1
        x = rho
        while x != 1 and ord_rho < d:
            x = (x * rho) % d
            ord_rho += 1
        if x != 1:
            ord_rho = -1

        # ρ^k mod d
        rho_k = pow(rho, k, d)
        # Should be 2^{k-S} mod d
        expected_rho_k = pow(2, k - S, d) if k < S else pow(pow(2, -1, d), S - k, d)

        # ρ^S mod d
        rho_S = pow(rho, S, d)

        print(f"  k={k}: ρ={rho}, ord(ρ)={ord_rho}, ρ^k={rho_k}, ρ^S={rho_S}")

        # KEY: the sum Σ ρ^i for i=1..k-1 (the "all-zeros δ" case)
        if rho != 1:
            geometric_sum = (rho * (pow(rho, k-1, d) - 1) * pow(rho - 1, -1, d)) % d
        else:
            geometric_sum = (k - 1) % d
        print(f"       Σρ^i (i=1..{k-1}) = {geometric_sum}, target = {(-1) % d}")
        print(f"       Gap from target: {(geometric_sum - (-1)) % d}")


def search_algebraic_identity(k_max=12):
    """
    Search for an algebraic identity that explains why REST' ≠ -1 mod d.

    The sum REST' = Σ ρ^i · 2^{δ_i} with constraints on δ.

    Idea: maybe REST' + 1 has a specific factorization?
    REST' + 1 = 1 + Σ ρ^i · 2^{δ_i}
    = 1 + ρ·2^{δ₁} + ρ²·2^{δ₂} + ... + ρ^{k-1}·2^{δ_{k-1}}

    For all δ_i = 0: REST' + 1 = 1 + Σρ^i = (ρ^k - 1)/(ρ - 1)
    In Z/dZ: ρ^k = 2^k·3^{-k} = 2^k·2^{-S} = 2^{k-S} mod d.

    So REST'_min + 1 = (2^{k-S} - 1)/(ρ - 1) mod d.

    2^{k-S} - 1 = -(1 - 2^{k-S}) mod d.
    And 1 - 2^{k-S} = (2^S - 2^k)/2^S = (2^S - 2^k)·2^{-S} mod d.

    Since d = 2^S - 3^k: 2^S = d + 3^k. So:
    2^S - 2^k = d + 3^k - 2^k.

    Hmm, this is getting complex but tractable. Let me compute.
    """
    print("\n═══ ALGEBRAIC IDENTITY SEARCH ═══")

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 200000: continue

        inv3 = pow(3, -1, d)
        rho = (2 * inv3) % d

        # Compute REST' + 1 for ALL sequences
        values_rest_plus_1 = []
        for sigma in enumerate_cumulative_sequences(k, S):
            deltas = [sigma[i] - i for i in range(1, k)]
            rest_prime = sum(pow(rho, i, d) * pow(2, deltas[i-1], d)
                           for i in range(1, k)) % d
            val = (rest_prime + 1) % d
            values_rest_plus_1.append(val)

        # Is REST' + 1 always nonzero mod d?
        n_zero = values_rest_plus_1.count(0)
        assert n_zero == 0, f"k={k}: REST'+1 = 0 found! This means a cycle exists!"

        # What's the GCD pattern of REST'+1 with d?
        gcd_values = Counter(gcd(v, d) for v in values_rest_plus_1)

        # Factor analysis of REST'+1
        # For the minimal sequence (all δ=0):
        if rho != 1:
            rest_min = (rho * (pow(rho, k-1, d) - 1) * pow(rho - 1, -1, d)) % d
        else:
            rest_min = (k - 1) % d
        rest_min_plus_1 = (rest_min + 1) % d
        g_min = gcd(rest_min_plus_1, d)

        print(f"  k={k}: REST'+1 never 0 ✓, gcd_pattern={dict(gcd_values)}")
        print(f"       min_seq: REST'+1 = {rest_min_plus_1}, gcd with d = {g_min}")

        # CRUCIAL: is REST'+1 always in a specific SUBGROUP of Z/dZ?
        # Check: is REST'+1 always in <2> (the subgroup generated by 2)?
        # This would mean REST'+1 = 2^m for some m.
        ord2 = 1
        x = 2 % d
        subgroup_2 = {1}
        while x != 1 and ord2 < d:
            subgroup_2.add(x)
            x = (x * 2) % d
            ord2 += 1
        if x == 1:
            subgroup_2.add(1)

        in_subgroup = sum(1 for v in values_rest_plus_1 if v in subgroup_2)
        print(f"       REST'+1 in <2>: {in_subgroup}/{C} ({in_subgroup/C:.3f})")
        print(f"       |<2>| = {len(subgroup_2)}, d = {d}")

        # Check: is 0 in <2>? (it shouldn't be, and if <2> doesn't contain 0,
        # and REST'+1 is always in <2>, then REST'+1 ≠ 0)
        # 0 is NOT in any multiplicative subgroup (it's not a unit).
        # But REST'+1 might not be in <2> either.
        if in_subgroup == C:
            print(f"       ★★★ REST'+1 is ALWAYS in <2> mod d!")
            print(f"       Since 0 ∉ <2>, this PROVES REST' ≠ -1, hence N₀ = 0!")


if __name__ == '__main__':
    verify_rest_prime_formula()
    analyze_rho_structure()
    search_algebraic_identity()
