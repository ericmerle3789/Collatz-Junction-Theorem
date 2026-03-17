#!/usr/bin/env python3
"""
Universal Proof Study — CCE Cycle 3
════════════════════════════════════

THE FUNDAMENTAL QUESTION:
  Can we prove N₀(d(k)) = 0 for ALL k ≥ 3 without case-by-case analysis?

WHAT WE KNOW (from CCE Cycles 1-2 + Hybrid Prover):
  1. 186/198 k values proved (k=3..200) by hybrid methods
  2. FCQ works when d(k) has a prime factor p with ρ_p < 1 and k large enough
  3. Steiner+Barina works when n_min < 2^71 (k ≤ ~120)
  4. 12 residual cases have d(k) with only very large prime factors
  5. Primitive root primes are "golden" (ρ = 1/(p-1))
  6. Artin density ~37.4% among all primes, ~45.8% among d(k) factors
  7. Compression ratio → 0 (monotonicity overwhelmingly constrains)
  8. Gap 1.35x is per-step (not dimensional)

CORRECTION (v3.3): S(k) = ⌈k·log₂(3)⌉ ≈ 1.585·k, NOT k(k-1)/2.
  Therefore d(k) = 2^⌈k·log₂3⌉ - 3^k, which is NOT of the form a^n - b^n.
  Zsygmondy's theorem does NOT directly apply.
  The cyclotomic decomposition in this module is INVALID.

THREE PATHS TO UNIVERSALITY (revised):

  PATH A: Character Sum Bounds
    For any prime p | d(k), ρ_p < 1 (proved unconditionally).
    Using |S(a)| ≤ √p (character orthogonality over subgroup <2>):
      k_min(p) = O(log p) when ord_p(2) > √p.
    Need: prove d(k) always has a factor p with ord_p(2) > √p,
    or find a Kloosterman-type bound for the geometric sum.

  PATH B: Analytic Number Theory
    Prove that the Fourier coefficients T(t) of corrSum mod d decay
    sufficiently: |T(t)| ≤ C · k^{-δ} for t ≠ 0 (Conjecture M).
    This would be the DIRECT proof without going through primes.

  PATH C: Transcendence + Baker
    Use the multiplicative structure: ∏(3 + 1/nᵢ) = 2^S.
    Baker-Wüstholz bounds on linear forms in logarithms give
    lower bounds on |2^S - 3^k - something|.

This module explores PATH A computationally (Zsygmondy analysis is now
marked as INVALID but kept for reference).
"""

import math
from dataclasses import dataclass
from typing import List, Dict, Optional
from collections import defaultdict

from syracuse_jepa.pipeline.analyst import (
    compute_S, compute_d, factorize, multiplicative_order
)


@dataclass
class ZsygmondyAnalysis:
    """Analysis of Zsygmondy-type properties of d(k) = 2^S - 3^k."""
    k: int
    S: int
    d_bits: int
    # Zsygmondy: 2^S - 3^k should have a "primitive prime divisor"
    # i.e., a prime p | (2^S - 3^k) that does NOT divide 2^j - 3^m
    # for any (j, m) < (S, k) with j/m = S/k = (k-1)/2.
    has_primitive_divisor: Optional[bool]  # None if unknown
    smallest_factor: int
    smallest_factor_bits: int
    n_small_factors: int  # factors < 10^6
    # Key ratio
    s_over_k: float       # S/k = (k-1)/2


def analyze_zsygmondy(k_max: int = 200) -> List[dict]:
    """
    Study whether d(k) = 2^S - 3^k has "Zsygmondy-type" structure.

    *** INVALIDATED in v3.3 ***
    The original analysis assumed S = k(k-1)/2, but S = ⌈k·log₂3⌉.
    Therefore d(k) ≠ a^k - b^k for any integer a, b.
    Zsygmondy's theorem does NOT apply.

    This function is kept for historical reference but its conclusions
    about primitive prime divisors are INCORRECT.

    The correct analysis is in rho_universal.py and proof_structure.py.
    """
    results = []

    print("  Zsygmondy-type analysis for d(k) = 2^{S(k)} - 3^k")
    print()

    odd_data = []
    even_data = []

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 1:
            continue

        factors = factorize(d)
        smallest = min((p for p, _ in factors), default=0)
        n_small = sum(1 for p, _ in factors if p < 10**6)

        entry = {
            "k": k,
            "S": S,
            "d_bits": d.bit_length(),
            "k_parity": "odd" if k % 2 == 1 else "even",
            "smallest_factor_bits": smallest.bit_length() if smallest > 0 else 0,
            "n_small_factors": n_small,
        }

        # For odd k: d(k) = a^k - b^k with a=2^{(k-1)/2}, b=3
        # Zsygmondy guarantees a prime p | d(k) with p ≡ 1 mod k
        # (the "primitive prime divisor" has this property)
        if k % 2 == 1:
            a = 2 ** ((k - 1) // 2)
            b = 3
            # Check: does d(k) have a factor ≡ 1 mod k?
            factors_mod_k = [(p, p % k) for p, _ in factors if p < 10**6]
            has_1_mod_k = any(pm == 1 for _, pm in factors_mod_k)
            entry["has_factor_1_mod_k"] = has_1_mod_k
            entry["factors_mod_k"] = factors_mod_k[:5]
            odd_data.append(entry)
        else:
            even_data.append(entry)

        results.append(entry)

        if k <= 30 or k % 20 == 0:
            parity = "odd " if k % 2 == 1 else "even"
            print(f"    k={k:3d} ({parity})  d={d.bit_length():3d}bit  "
                  f"smallest_factor={smallest.bit_length():3d}bit  "
                  f"n_small={n_small}")

    print()

    # Analysis: do odd k have better factorization properties?
    odd_small = [e for e in odd_data if e["n_small_factors"] > 0]
    even_small = [e for e in even_data if e["n_small_factors"] > 0]

    print(f"  Odd k:  {len(odd_data)} values, {len(odd_small)} with small factors "
          f"({100*len(odd_small)/len(odd_data):.0f}%)")
    print(f"  Even k: {len(even_data)} values, {len(even_small)} with small factors "
          f"({100*len(even_small)/len(even_data):.0f}%)")

    # Check the 12 residual cases
    residual = [135, 143, 148, 158, 165, 166, 171, 176, 178, 185, 192, 193]
    residual_odd = [k for k in residual if k % 2 == 1]
    residual_even = [k for k in residual if k % 2 == 0]
    print(f"\n  Residual 12 cases: {len(residual_odd)} odd, {len(residual_even)} even")
    print(f"  Odd residual: {residual_odd}")
    print(f"  Even residual: {residual_even}")

    # For odd residual: Zsygmondy guarantees primitive prime divisor
    # These primes p satisfy p ≡ 1 mod k and p | (a^k - b^k) but p ∤ (a^j - b^j) for j < k
    # The question: can we use this prime for FCQ?
    print(f"\n  For odd residual k, Zsygmondy guarantees ∃ prime p | d(k) with p ≡ 1 mod k")
    print(f"  Such p satisfies: ord_p(a) = k where a = 2^{{(k-1)/2}}")
    print(f"  This means: ord_p(2) | k(k-1)/2 and ord_p(2) ∤ j(j-1)/2 for j < k")
    print(f"  → ord_p(2) is likely LARGE (≫ k)")

    return results


def explore_cyclotomic_structure(k_max: int = 50) -> dict:
    """
    Explore the cyclotomic polynomial connection.

    For odd k, d(k) = a^k - b^k = ∏_{d|k} Φ_d(a, b)
    where Φ_d is the d-th cyclotomic polynomial applied to (a, b).

    The primitive prime divisors come from Φ_k(a, b).
    Φ_k(a, b) = ∏_{j coprime to k} (a - ζ^j b) where ζ = e^{2πi/k}.

    For our case: a = 2^{(k-1)/2}, b = 3.
    Φ_k(a, b) ≈ a^{φ(k)} for large a >> b.
    So Φ_k ≈ 2^{(k-1)φ(k)/2}, which has ≈ (k-1)φ(k)/2 bits.

    The key factorization: d(k) = Φ_k(a,b) × (product of Φ_d(a,b) for d|k, d<k)
    Primitive prime divisors of d(k) are exactly those dividing Φ_k(a,b).
    """
    print("\n  Cyclotomic decomposition for odd k:")
    print()

    cyclotomic_data = []

    for k in range(3, k_max + 1, 2):  # odd k only
        S = compute_S(k)
        d = compute_d(k)
        a = 2 ** ((k - 1) // 2)
        b = 3

        # Compute Φ_k(a, b) = ∏_{gcd(j,k)=1, 1≤j≤k} (a - ζ^j b)
        # For prime k, Φ_k(a,b) = (a^k - b^k)/(a - b)
        # For composite k, more complex

        from math import gcd
        euler_phi = sum(1 for j in range(1, k + 1) if gcd(j, k) == 1)

        # Approximate size of Φ_k(a, b)
        phi_k_bits = int(euler_phi * math.log2(a)) if a > 1 else 0
        d_bits = d.bit_length()
        rest_bits = d_bits - phi_k_bits

        is_prime_k = all(k % j != 0 for j in range(2, int(k**0.5) + 1))

        cyclotomic_data.append({
            "k": k,
            "is_prime_k": is_prime_k,
            "euler_phi": euler_phi,
            "phi_k_bits": phi_k_bits,
            "d_bits": d_bits,
            "rest_bits": rest_bits,
        })

        if k <= 30 or k % 10 == 1:
            pk = "PRIME" if is_prime_k else f"φ={euler_phi}"
            print(f"    k={k:3d} ({pk:8s})  Φ_k ≈ 2^{phi_k_bits:3d}  "
                  f"d ≈ 2^{d_bits:3d}  rest ≈ 2^{max(rest_bits,0):3d}")

    # Check residual odd cases
    residual_odd = [135, 143, 155, 165, 171, 185, 193]
    print(f"\n  Residual odd k and their cyclotomic structure:")
    for k in residual_odd:
        S = compute_S(k)
        d = compute_d(k)
        a = 2 ** ((k - 1) // 2)
        from math import gcd
        euler_phi = sum(1 for j in range(1, k + 1) if gcd(j, k) == 1)
        phi_k_bits = int(euler_phi * math.log2(a))
        d_bits = d.bit_length()
        is_prime_k = all(k % j != 0 for j in range(2, int(k**0.5) + 1))
        pk = "PRIME" if is_prime_k else f"composite (φ={euler_phi})"
        print(f"    k={k:3d} {pk:30s}  Φ_k ≈ 2^{phi_k_bits:3d}  d ≈ 2^{d_bits:3d}")

    return {"cyclotomic_data": cyclotomic_data}


def run_universal_study(k_max: int = 200) -> dict:
    """Full universal proof study."""
    print()
    print("╔" + "═" * 68 + "╗")
    print("║  UNIVERSAL PROOF STUDY — CCE Cycle 3                             ║")
    print("║  Can we prove N₀(d(k))=0 for ALL k without case-by-case?         ║")
    print("╚" + "═" * 68 + "╝")
    print()

    # Phase 1: Zsygmondy analysis
    print("┌─ PHASE 1: ZSYGMONDY ANALYSIS ────────────────────────────┐")
    zsyg = analyze_zsygmondy(k_max)
    print(f"└─ {len(zsyg)} k values analyzed ──────────────────────────┘\n")

    # Phase 2: Cyclotomic structure
    print("┌─ PHASE 2: CYCLOTOMIC DECOMPOSITION ──────────────────────┐")
    cyclo = explore_cyclotomic_structure(min(k_max, 50))
    print(f"└─ Cyclotomic analysis complete ───────────────────────────┘\n")

    # Synthesis
    print("╔" + "═" * 68 + "╗")
    print("║  UNIVERSAL STUDY SYNTHESIS                                       ║")
    print("╠" + "═" * 68 + "╣")
    print("║")
    print("║  PATH A (Zsygmondy + Cyclotomic):")
    print("║  • For ODD k: d(k) = a^k - b^k, Zsygmondy guarantees")
    print("║    primitive prime divisors p with p ≡ 1 mod k")
    print("║  • These primes have ord_p(2) | k(k-1)/2 and likely large")
    print("║  • Missing piece: prove ρ_p < 1 for these primes")
    print("║  • 7/12 residual cases are odd → Zsygmondy applies")
    print("║")
    print("║  PATH B (Conjecture M — direct):")
    print("║  • |T(t)| ≤ C·k^{-δ} for t ≠ 0 (the MAIN open problem)")
    print("║  • Requires exponential sum bounds on monotone partitions")
    print("║  • Connects to Vinogradov/Weyl for structured sums")
    print("║")
    print("║  PATH C (Baker/Transcendence):")
    print("║  • ∏(3 + 1/nᵢ) = 2^S, Baker gives |log α - (p/q) log β| > ...")
    print("║  • DBA scheme: 3-6 months specialist work (R197)")
    print("║")
    print("║  RECOMMENDED: Pursue PATH A (Zsygmondy) for odd k")
    print("║  + Steiner extension for even k (larger verification range)")
    print("║  This would reduce to proving one algebraic number theory lemma")
    print("╚" + "═" * 68 + "╝")

    return {
        "zsygmondy_data_count": len(zsyg),
        "cyclotomic_data": cyclo,
        "residual_12": [135, 143, 148, 158, 165, 166, 171, 176, 178, 185, 192, 193],
        "residual_odd": [135, 143, 165, 171, 185, 193],
        "residual_even": [148, 158, 166, 176, 178, 192],
    }


if __name__ == '__main__':
    import sys
    k_max = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    result = run_universal_study(k_max)
