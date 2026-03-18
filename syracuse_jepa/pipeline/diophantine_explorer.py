#!/usr/bin/env python3
"""
DIOPHANTINE EXPLORER — The Deepest Level
==========================================

Key observation from deep_explorer: the fractional part of corrSum/d
approaches 0 but NEVER reaches it. This is the Diophantine signature.

For a cycle to exist: corrSum/d must be EXACTLY an integer.
But corrSum = Σ 3^{k-1-i} · 2^{σ_i} and d = 2^S - 3^k.

The ratio corrSum/d is a RATIO OF S-SMOOTH EXPRESSIONS.
For this to be an integer, very specific arithmetic conditions must hold.

THIS MODULE EXPLORES: What makes corrSum/d irrational-like?
"""

import sys, os
from math import ceil, log2, comb, gcd
from itertools import combinations
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


def explore_near_misses(k_max=12):
    """
    For each k, find the σ that gives corrSum CLOSEST to a multiple of d.
    Analyze WHY it misses. What prevents the last step to exactness?
    """
    print("═══ NEAR-MISS ANALYSIS ═══")
    print(f"{'k':>3} {'d':>10} {'closest σ':>30} {'cs':>12} {'cs%d':>8} {'dist':>6} {'n₀':>6} {'residual':>10}")
    print("-" * 95)

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 500000: continue

        best_dist = d
        best_sigma = None
        best_cs = None

        for sigma in enumerate_cumulative_sequences(k, S):
            cs = corrsum_cumulative(sigma, k)
            r = cs % d
            dist = min(r, d - r)
            if dist < best_dist:
                best_dist = dist
                best_sigma = sigma
                best_cs = cs

        r = best_cs % d
        n0_nearest = round(best_cs / d)
        residual = best_cs - n0_nearest * d

        print(f"{k:3d} {d:10d} {str(best_sigma):>30} {best_cs:12d} {r:8d} {best_dist:6d} "
              f"{n0_nearest:6d} {residual:10d}")

        # DEEP: analyze the residual
        # residual = corrSum - n₀·d = corrSum - n₀·(2^S - 3^k)
        # = corrSum - n₀·2^S + n₀·3^k
        # = (Σ 3^{k-1-i}·2^{σ_i}) - n₀·2^S + n₀·3^k
        # = n₀·3^k + (Σ 3^{k-1-i}·2^{σ_i}) - n₀·2^S
        # The Steiner equation says this = 0 for a cycle.
        # The residual measures HOW FAR from a cycle we are.

        # Factor the residual
        if residual != 0:
            g = gcd(abs(residual), d)
            print(f"      gcd(residual, d) = {g}, residual/gcd = {residual//g}")

            # Factor residual
            res_abs = abs(residual)
            factors = []
            n = res_abs
            for p in [2, 3, 5, 7, 11, 13]:
                while n % p == 0:
                    factors.append(p)
                    n //= p
            if n > 1:
                factors.append(n)
            print(f"      |residual| = {res_abs} = {'·'.join(str(f) for f in factors)}")


def explore_steiner_structure(k_max=12):
    """
    The Steiner equation: n₀·(2^S - 3^k) = Σ 3^{k-1-i}·2^{σ_i}

    Rewrite as: n₀·2^S = n₀·3^k + corrSum

    This says: n₀·2^S ≡ corrSum mod 3^k (since n₀·3^k ≡ 0 mod 3^k)
    And:       n₀·3^k ≡ -corrSum mod 2^S (since n₀·2^S ≡ 0 mod 2^S... NO)

    Wait: n₀·2^S is divisible by 2^S but corrSum is ODD.
    So: n₀·3^k + corrSum must be divisible by 2^S.

    Since corrSum is odd: n₀·3^k must be odd (which it is, both odd).
    So n₀·3^k + corrSum is even. How many times divisible by 2?

    corrSum = 3^{k-1} + Σ_{i≥1} 3^{k-1-i}·2^{σ_i}
    The first term is odd. The others are even with v₂ = σ_i.
    So v₂(corrSum) = 0.

    n₀·3^k is odd (v₂ = 0).
    n₀·3^k + corrSum = (odd) + (odd) = even. v₂ ≥ 1.

    For Steiner: n₀·2^S = n₀·3^k + corrSum.
    LHS has v₂ = S.
    RHS must also have v₂ = S.

    v₂(n₀·3^k + corrSum) = S.

    This means: n₀·3^k + corrSum ≡ 0 mod 2^S.
    i.e., n₀·3^k ≡ -corrSum mod 2^S.
    i.e., n₀ ≡ -corrSum · (3^k)^{-1} mod 2^S.

    Since 3^k is odd, (3^k)^{-1} mod 2^S exists.

    THIS IS A VERY STRONG CONSTRAINT: n₀ is determined modulo 2^S!
    And 2^S > d (since d = 2^S - 3^k < 2^S), so n₀ is determined
    modulo a number LARGER than the possible range of n₀ = corrSum/d.

    For n₀ ≤ corrSum_max/d ≈ C(S-1,k-1):
    If 2^S > corrSum_max/d, then n₀ is UNIQUELY determined by the
    congruence n₀ ≡ -corrSum · (3^k)^{-1} mod 2^S.

    But n₀ also must satisfy: n₀ = corrSum/d (exact division).

    These two constraints (congruence mod 2^S AND exact division by d)
    are COMPATIBLE only if the congruence value equals the exact quotient.
    """
    print("\n═══ STEINER STRUCTURAL CONSTRAINT ═══")
    print("For a cycle: n₀·3^k ≡ -corrSum mod 2^S")
    print("This DETERMINES n₀ mod 2^S.\n")

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 200000: continue

        inv_3k = pow(3**k, -1, 2**S)  # (3^k)^{-1} mod 2^S

        # For each σ, the required n₀ mod 2^S is:
        # n₀ ≡ -corrSum · inv_3k mod 2^S
        required_n0_set = set()
        valid_count = 0

        for sigma in enumerate_cumulative_sequences(k, S):
            cs = corrsum_cumulative(sigma, k)
            required_n0 = (-cs * inv_3k) % (2**S)

            # n₀ must also equal cs/d (integer)
            if cs % d == 0:
                actual_n0 = cs // d
                if actual_n0 == required_n0:
                    valid_count += 1
                    print(f"  k={k}: VALID CYCLE! σ={sigma}, n₀={actual_n0}")

            # Check: is required_n0 in the valid range?
            n0_max = cs // d + 1
            if required_n0 <= n0_max:
                # Check if cs = required_n0 · d
                if required_n0 * d == cs:
                    valid_count += 1

            required_n0_set.add(required_n0)

        # How many DISTINCT required_n0 values?
        n_distinct = len(required_n0_set)
        print(f"  k={k}: {C} sequences → {n_distinct} distinct required n₀ mod 2^{S} "
              f"(out of 2^{S} = {2**S})")
        print(f"    Valid cycles found: {valid_count}")

        # KEY METRIC: are the required n₀ values EVER equal to corrSum/d?
        # We know N0=0, so the answer is NO. But WHY?

        # The required n₀ is a function of corrSum via the modular inverse.
        # For n₀ to work: required_n0 · d = corrSum.
        # i.e., (-corrSum · inv_3k) mod 2^S · (2^S - 3^k) = corrSum
        # This is a DIOPHANTINE equation in corrSum.

        # Let's check: for each possible n₀ in {1, 3, 5, ..., 2·corrSum_max/d},
        # how many satisfy the 2^S congruence AND give corrSum = n₀·d
        # that is achievable by some σ?

        cs_max = max(corrsum_cumulative(sigma, k)
                     for sigma in enumerate_cumulative_sequences(k, S))
        n0_bound = cs_max // d + 1

        achievable_cs = set(corrsum_cumulative(sigma, k)
                           for sigma in enumerate_cumulative_sequences(k, S))

        potential_cycles = 0
        for n0 in range(1, n0_bound + 1, 2):  # odd n₀ only
            target_cs = n0 * d
            if target_cs in achievable_cs:
                # Also check 2^S congruence
                required = (-target_cs * inv_3k) % (2**S)
                if required == n0:
                    potential_cycles += 1
                    print(f"    *** POTENTIAL CYCLE: n₀={n0}, corrSum={target_cs} ***")

        print(f"    Potential cycles (all constraints): {potential_cycles}")
        if potential_cycles == 0:
            print(f"    ✓ No cycle exists for k={k}")
        print()


def explore_gcd_pattern(k_max=12):
    """
    For each k, compute gcd(corrSum, d) for all σ.
    If gcd is always < d, then d ∤ corrSum.
    The PATTERN of gcd values might reveal the algebraic obstruction.
    """
    print("\n═══ GCD PATTERN ANALYSIS ═══")

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 200000: continue

        gcd_values = defaultdict(int)
        for sigma in enumerate_cumulative_sequences(k, S):
            cs = corrsum_cumulative(sigma, k)
            g = gcd(cs, d)
            gcd_values[g] += 1

        # The GCD can only be a divisor of d
        divisors_hit = sorted(gcd_values.keys())
        max_gcd = max(divisors_hit)

        print(f"  k={k}, d={d}: {len(divisors_hit)} distinct gcd values")
        print(f"    max gcd = {max_gcd} ({max_gcd/d:.4f} of d)")
        print(f"    gcd=1: {gcd_values.get(1, 0)} ({gcd_values.get(1, 0)/C:.3f})")
        print(f"    gcd=d: {gcd_values.get(d, 0)} (this is N0)")

        # CRUCIAL: what fraction of d is the max gcd?
        # If max_gcd/d < 1 always, then d never divides corrSum
        if max_gcd < d:
            # Find: what is max_gcd in terms of d's factorization?
            # max_gcd divides d, so it's a product of some prime powers of d
            remaining = d // max_gcd
            print(f"    d/max_gcd = {remaining} → corrSum misses top {remaining}x of d")


if __name__ == '__main__':
    print("DIOPHANTINE EXPLORER — Why corrSum/d is never integer")
    print("=" * 70)
    explore_near_misses()
    explore_steiner_structure()
    explore_gcd_pattern()
