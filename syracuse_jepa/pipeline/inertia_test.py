#!/usr/bin/env python3
"""
INERTIA TEST — Is d inert in Z[α] where α^S = 3^k?
=====================================================

If X^S - 3^k is irreducible mod d (as polynomial in F_d[X]),
then d is INERT in Z[α], meaning (d) remains prime.

In that case: Z[α]/(d) ≅ F_{d^S} (field with d^S elements).
And P_σ(α) mod (d) has norm N(P_σ) ≡ P_σ(2)^S mod d.
So d | N(P_σ) ⟺ d | P_σ(2)^S ⟺ d | P_σ(2) (when d prime).

Equivalently: if d is prime AND inert, N(P_σ) ≡ 0 mod d ⟺ P_σ(2) ≡ 0 mod d.
So if N(P_σ) ≢ 0 mod d for all σ: P_σ(2) ≢ 0 mod d for all σ.
This is EXACTLY what we verified for k=3 (all norms coprime to d=5).

For d composite or d split: the argument is more complex.

TEST: For which k is X^S - 3^k irreducible mod d?
"""

import sys, os
from math import ceil, log2, gcd

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import compute_S, compute_d


def poly_mod_irreducible(S, three_k, d):
    """
    Test if X^S - three_k is irreducible in F_d[X] (when d is prime).

    X^S - a is irreducible over F_p iff:
    1. a is not a p^j-th power in F_p for any prime j | S, AND
    2. If 4 | S: a ∉ -4·(F_p*)^4 ... (Lidl-Niederreiter condition)

    Simplified: X^n - a is irreducible over F_p iff ord(a) in F_p* is
    divisible by every prime dividing n, and (if 4|n) a is not of the
    form -4b^4.

    Actually, the most practical test: compute gcd(X^{d^j} - X, X^S - a mod d)
    for j = 1, ..., S-1. If all gcds are trivial, X^S - a is irreducible.
    But this is expensive for large S.

    Simpler: X^S - a is irreducible over F_p iff the multiplicative order
    of a in F_p* doesn't divide p^j - 1 for any j < S with j | S... no.

    Actually: X^S - a ∈ F_p[X]. Its roots are a^{1/S} · ζ^j where ζ = primitive S-th root.
    The polynomial is irreducible iff the splitting field of X^S - a over F_p has degree S.
    The splitting field has degree lcm(ord_S, f) where f is the degree of a^{1/S} over F_p
    and ord_S is the multiplicative order of p mod S in (Z/SZ)*.

    This is complex. Let me just check: does X^S - a have a root in F_d?
    If not: it has no linear factor, which is necessary (but not sufficient) for irreducibility.
    """
    # Check: does X^S ≡ three_k mod d have a solution?
    # i.e., is three_k an S-th power residue mod d?
    # three_k = 3^k mod d = (3^k mod d)
    a = three_k % d
    if d <= 1:
        return None

    # For d prime: a is an S-th power iff a^{(d-1)/gcd(S, d-1)} ≡ 1 mod d
    g = gcd(S, d - 1)
    test = pow(a, (d - 1) // g, d)
    has_root = (test == 1)

    return not has_root  # Irreducible if NO root (necessary condition)


def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i+2) == 0: return False
        i += 6
    return True


def test_inertia(k_max=30):
    print("INERTIA TEST: X^S - 3^k irreducible mod d?")
    print("=" * 70)
    print(f"{'k':>3} {'S':>3} {'d':>12} {'d prime':>8} {'gcd(S,k)':>9} {'no root':>8} {'STATUS':>10}")
    print("-" * 60)

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue

        d_prime = is_prime(d)
        g = gcd(S, k)
        three_k = pow(3, k)

        if d_prime:
            no_root = poly_mod_irreducible(S, three_k, d)
            # If no root AND gcd(S,k)=1: good candidate for inertia
            if no_root and g == 1:
                status = "★ INERT?"
            elif no_root:
                status = "no root"
            else:
                status = "has root"
        else:
            no_root = None
            status = "composite"

        print(f"{k:3d} {S:3d} {d:12d} {str(d_prime):>8} {g:>9} "
              f"{str(no_root):>8} {status:>10}")


if __name__ == '__main__':
    test_inertia()
