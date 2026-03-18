#!/usr/bin/env python3
"""
COSET ANALYSIS — Why do n₀ candidates and corrSum/d values live in disjoint cosets?
=====================================================================================

From the abductive reasoner: the set of valid n₀ (odd + orbit congruences)
never intersects the set {corrSum(σ)/d : σ ∈ Comp}.

QUESTION: What MODULAR structure separates these two sets?

The candidates n₀ satisfy: n₀ ≡ c_{e₁} mod 2^{e₁} for each possible e₁.
The achievable n₀ values are: corrSum(σ)/d for σ with σ₁ = e₁.

If these two sets live in DIFFERENT cosets mod some modulus m:
the intersection is empty.

Find the SMALLEST m that separates them.
"""

import sys, os
from math import ceil, log2, comb, gcd
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


def find_separating_modulus(k, max_m=100):
    """Find the smallest modulus m that separates n₀ candidates from achievable."""
    S = compute_S(k)
    d = compute_d(k)
    if d <= 0: return None
    C = count_cumulative_sequences(k, S)
    if C > 200000: return None

    # Achievable quotients (corrSum / d, rounded — but we need EXACT)
    # For corrSum ≡ 0 mod d: quotient = corrSum/d. But since N₀=0, no exact quotient.
    # Instead: compute corrSum/d for ALL σ and look at the FRACTIONAL parts.
    # The achievable "would-be n₀" values are floor(corrSum/d) and ceil(corrSum/d).

    achievable_quotients = set()
    for sigma in enumerate_cumulative_sequences(k, S):
        cs = corrsum_cumulative(sigma, k)
        q = cs // d  # Floor quotient
        achievable_quotients.add(q)
        if cs % d != 0:
            achievable_quotients.add(q + 1)  # Ceil quotient

    # Valid n₀ candidates (odd + orbit)
    cs_min = min(corrsum_cumulative(sigma, k) for sigma in enumerate_cumulative_sequences(k, S))
    cs_max = max(corrsum_cumulative(sigma, k) for sigma in enumerate_cumulative_sequences(k, S))
    n0_min = cs_min // d + (1 if cs_min % d else 0)
    n0_max = cs_max // d

    orbit_valid = set()
    for e1 in range(1, S - k + 2):
        required = ((pow(2, e1) - 1) * pow(3, -1, pow(2, e1))) % pow(2, e1)
        for n0 in range(max(1, n0_min), n0_max + 1):
            if n0 % 2 == 1 and n0 % pow(2, e1) == required:
                orbit_valid.add(n0)

    # For each modulus m: check if orbit_valid and achievable_quotients
    # land in DIFFERENT cosets mod m
    for m in range(2, max_m + 1):
        orbit_cosets = set(n0 % m for n0 in orbit_valid)
        achiev_cosets = set(q % m for q in achievable_quotients)
        if orbit_cosets.isdisjoint(achiev_cosets):
            return {
                'k': k, 'm': m,
                'orbit_cosets': sorted(orbit_cosets),
                'achiev_cosets': sorted(achiev_cosets),
                'separates': True,
            }

    # No small separating modulus found
    return {
        'k': k, 'm': None,
        'orbit_n': len(orbit_valid),
        'achiev_n': len(achievable_quotients),
        'overlap_mod2': len(set(n % 2 for n in orbit_valid) & set(q % 2 for q in achievable_quotients)),
    }


def analyze_quotient_structure(k_max=12):
    """Analyze the mod-structure of corrSum/d values."""
    print("COSET ANALYSIS — Separating n₀ candidates from achievable quotients")
    print("=" * 70)

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 200000: continue

        result = find_separating_modulus(k)
        if result is None: continue

        if result.get('separates'):
            print(f"k={k}: SEPARATED by m={result['m']}")
            print(f"  n₀ candidates mod {result['m']}: {result['orbit_cosets']}")
            print(f"  achievable q mod {result['m']}: {result['achiev_cosets']}")
        else:
            print(f"k={k}: NO small separating modulus (tested up to 100)")
            print(f"  n₀ candidates: {result['orbit_n']}, achievable: {result['achiev_n']}")

    # DEEPER: analyze corrSum mod d distribution vs n₀·d candidates
    print(f"\n{'='*70}")
    print("DEEPER: corrSum mod d vs n₀·d for specific n₀ values")
    print(f"{'='*70}")

    for k in [3, 5, 7]:
        S = compute_S(k)
        d = compute_d(k)
        C = count_cumulative_sequences(k, S)
        if C > 50000: continue

        achievable_cs = set(corrsum_cumulative(sigma, k)
                           for sigma in enumerate_cumulative_sequences(k, S))

        print(f"\nk={k}, d={d}: |achievable| = {len(achievable_cs)}")

        # For each odd n₀ in valid range: check why n₀·d ∉ achievable
        cs_list = sorted(achievable_cs)
        for n0 in range(1, min(20, max(cs_list) // d + 2)):
            if n0 % 2 == 0: continue  # Skip even
            target = n0 * d
            # Find nearest achievable to target
            nearest = min(cs_list, key=lambda cs: abs(cs - target))
            gap = target - nearest
            in_set = target in achievable_cs
            print(f"  n₀={n0:3d}: target={target:8d}, nearest={nearest:8d}, "
                  f"gap={gap:+6d}, in_set={in_set}")


if __name__ == '__main__':
    analyze_quotient_structure()
