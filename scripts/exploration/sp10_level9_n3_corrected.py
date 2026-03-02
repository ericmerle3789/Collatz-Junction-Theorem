#!/usr/bin/env python3
"""
SP10 L9 — Investigation structurelle n₃ (VERSION CORRIGEE)
==========================================================

BUG FIX: n₃ = ord(3) / gcd(ord(3), m), NOT gcd(ord(3), q)
         Test 3 ∈ ⟨2⟩: 3^m ≡ 1 (mod p), NOT 3^q ≡ 1

Key findings:
- 3 ∈ ⟨2⟩ occurs in 64.4% of (k,p) pairs with p | d(k)
  BUT all in regime W/A. ZERO in regime B.
- n₃·m | p-1 verified 100% (284/284)
- Generic case n₃ = (p-1)/m: 51.1%
- REGIME B IS EMPIRICALLY EMPTY for p | d(k), k=69..150
"""

import math
import sys
from sympy import factorint, isprime
from sympy.ntheory import n_order

sys.set_int_max_str_digits(100000)
theta = math.log2(3)


def compute_n3_correct(p, m):
    """
    Compute n₃ = min j ≥ 1 such that 3^j ∈ ⟨2⟩ mod p.

    CORRECT formula: n₃ = ord(3) / gcd(ord(3), m)

    Proof: 3^j ∈ ⟨2⟩ iff (3^j)^m = 1 iff 3^{jm} = 1
    iff ord(3) | jm iff (ord(3)/gcd(ord(3),m)) | j
    """
    # Check 3 ∈ ⟨2⟩ directly first
    if pow(3, m, p) == 1:
        return 1
    ord3 = n_order(3, p)
    return ord3 // math.gcd(ord3, m)


def main():
    print("=" * 72)
    print("SP10 L9 — Investigation n₃ (CORRIGEE)")
    print("=" * 72)

    # Q1: Among factors of 2^m - 1, how many have 3 ∈ ⟨2⟩?
    print("\n1. FACTEURS DE 2^m - 1 AVEC 3 ∈ ⟨2⟩")
    print("   (test CORRECT: 3^m ≡ 1 mod p)")
    print("-" * 55)

    all_primes_tested = 0
    found_3_in = []

    for m in range(5, 80):
        M = pow(2, m) - 1
        factors = factorint(M, limit=10**8)
        for p in factors:
            if p < 5 or not isprime(p):
                continue
            actual_m = n_order(2, p)
            if actual_m != m:
                continue
            all_primes_tested += 1
            if pow(3, m, p) == 1:  # CORRECT test
                regime = "B" if p >= m ** 4 else "A"
                found_3_in.append((m, p, regime))

    print(f"  Premiers testés : {all_primes_tested}")
    print(f"  3 ∈ ⟨2⟩ : {len(found_3_in)}")
    if found_3_in:
        for m, p, r in found_3_in:
            print(f"    m={m:3d}, p={p:15d}, p/m⁴={p / m**4:.4e}, regime {r}")
        regime_b = [x for x in found_3_in if x[2] == "B"]
        print(f"\n  En regime B (p ≥ m⁴) : {len(regime_b)}/{len(found_3_in)}")

    # Q2: For p | d(k), compute correct n₃
    print("\n\n2. n₃ CORRECT POUR p | d(k), k=69..150")
    print("-" * 55)

    all_cases = []
    for k in range(69, 151):
        S = math.ceil(k * theta)
        dk = pow(2, S) - pow(3, k)
        if dk <= 0:
            continue
        factors = factorint(dk, limit=10**6)
        for p, exp in factors.items():
            if p < 10 or not isprime(p):
                continue
            m = n_order(2, p)
            if m < 5:
                continue

            n3 = compute_n3_correct(p, m)
            q = (p - 1) // m
            regime = "B" if p >= m ** 4 else ("DI_B" if p >= m ** 2 else "W")
            is_generic = n3 == q
            in_gen2 = n3 == 1
            all_cases.append((k, p, m, n3, q, regime, is_generic, in_gen2))

    # Statistics
    total = len(all_cases)
    generic = sum(1 for c in all_cases if c[6])
    count_in = sum(1 for c in all_cases if c[7])
    divides = sum(1 for c in all_cases if (c[1] - 1) % (c[3] * c[2]) == 0)

    print(f"  Total : {total}")
    print(f"  n₃ = (p-1)/m (generique) : {generic}/{total} ({100*generic/total:.1f}%)")
    print(f"  3 ∈ ⟨2⟩ (n₃ = 1) : {count_in}/{total} ({100*count_in/total:.1f}%)")
    print(f"  n₃·m | p-1 : {divides}/{total} ({100*divides/total:.1f}%)")

    regime_b = [c for c in all_cases if c[5] == "B"]
    regime_dib = [c for c in all_cases if c[5] == "DI_B"]
    print(f"  Regime B : {len(regime_b)}/{total}")
    print(f"  Regime DI_B : {len(regime_dib)}/{total}")

    if regime_b:
        print("\n  CAS REGIME B :")
        for k, p, m, n3, q, r, g, i in regime_b:
            print(f"    k={k}, p={p}, m={m}, n₃={n3}")
    else:
        print("  ★★★ REGIME B EST VIDE EMPIRIQUEMENT ★★★")


if __name__ == "__main__":
    main()
