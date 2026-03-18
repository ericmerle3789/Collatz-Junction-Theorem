#!/usr/bin/env python3
"""
2-DIFFERENCE POLYNOMIALS — Can Q_δ(2/3) = 0 mod d?
=====================================================

Q_δ(X) = Σ_{i=1}^{k-1} (2^{s_i} - 2^{δ_i}) · X^i
where s = sorted(δ) and δ has crossings.

Each coefficient c_i = 2^{s_i} - 2^{δ_i}.
If s_i = δ_i (position unchanged by sorting): c_i = 0.
If s_i > δ_i (value moved up): c_i > 0 in Z.
If s_i < δ_i (value moved down): c_i < 0 in Z.

KEY PROPERTY: Σ c_i = 0 (sorting preserves the sum of 2^{δ_i}).
So Q_δ(1) = 0 always. X = 1 IS a root.

This means Q_δ(X) = (X - 1) · R_δ(X) for some polynomial R_δ.
The correction F(sorted) - F(unsorted) = Q_δ(ρ) = (ρ - 1) · R_δ(ρ).

Since ρ - 1 = 2/3 - 1 = -1/3 mod d: ρ - 1 is a UNIT (since gcd(3,d)=1).
So Q_δ(ρ) = 0 iff R_δ(ρ) = 0.

R_δ has degree k-2 (one less than Q_δ).

FURTHERMORE: what other FIXED roots does Q_δ have?
If Σ c_i · j^i = 0 for some j independent of δ: that's another structural root.

Check: Q_δ(-1) = Σ c_i · (-1)^i. Is this always 0?
Σ c_i · (-1)^i = Σ (2^{s_i} - 2^{δ_i}) · (-1)^i.
Not obviously 0. Check numerically.

Check: Q_δ(ρ²) = 0? What about powers of ρ?

DEEPER: Since Q_δ(1) = 0 and we factor out (X-1):
R_δ(X) = Q_δ(X)/(X-1) = Σ_{i=1}^{k-1} c_i · (X^i - 1)/(X - 1)
        = Σ c_i · (1 + X + X² + ... + X^{i-1})

R_δ(ρ) = Σ c_i · (1 + ρ + ... + ρ^{i-1})
        = Σ c_i · (ρ^i - 1)/(ρ - 1)  (if ρ ≠ 1)

And the correction = (ρ-1) · R_δ(ρ) = Σ c_i · (ρ^i - 1).

So the correction is ALSO: Σ (2^{s_i} - 2^{δ_i}) · (ρ^i - 1).

Each term: (2^{s_i} - 2^{δ_i}) · (ρ^i - 1) is a product of two "differences".
The first factor is a 2-power difference.
The second is a ρ-power difference.

BOTH factors are nonzero (s_i ≠ δ_i implies first nonzero;
ρ^i ≠ 1 for i < ord(ρ) and ord(ρ) >> k).

The sum of products of nonzero terms: can it be 0?
This is the BILINEAR form: Σ a_i · b_i where a_i = 2^{s_i}-2^{δ_i}, b_i = ρ^i-1.

If {a_i} and {b_i} are "generic" (not specially aligned): the sum is nonzero.
The ALGEBRAIC CONSTRAINT is that a_i and b_i are both determined by
the same δ-sequence and the same algebraic number ρ.
"""

import sys, os
from math import ceil, log2, gcd
from itertools import product as cart_product

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import compute_S, compute_d


def analyze_Q_structure(k_max=8):
    """Analyze the structure of Q_δ polynomials."""
    print("2-DIFFERENCE POLYNOMIAL STRUCTURE")
    print("=" * 60)

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        max_delta = S - k

        inv3 = pow(3, -1, d)
        rho = (2 * inv3) % d
        rho_pow = [pow(rho, i, d) for i in range(k)]
        two_pow = [pow(2, j, d) for j in range(max_delta + 1)]

        total = (max_delta + 1)**(k-1)
        if total > 500000: continue

        print(f"\nk={k}, d={d}, ρ={rho}")

        # Verify: Q_δ(1) = 0 always (sum of coefficients = 0)
        q_at_1_always_zero = True

        for deltas in cart_product(range(max_delta + 1), repeat=k-1):
            f_val = (1 + sum(rho_pow[i+1] * two_pow[deltas[i]] % d for i in range(k-1))) % d
            if f_val != 0: continue

            sorted_d = tuple(sorted(deltas))
            if sorted_d == deltas: continue  # Already sorted

            # Coefficients c_i
            coeffs = [(two_pow[sorted_d[i]] - two_pow[deltas[i]]) % d for i in range(k-1)]

            # Q(1) = Σ c_i should be 0 mod d
            q_at_1 = sum(coeffs) % d
            if q_at_1 != 0:
                q_at_1_always_zero = False

            # Correction via bilinear form: Σ c_i · (ρ^{i+1} - 1)
            bilinear = sum(coeffs[i] * ((rho_pow[i+1] - 1) % d) % d for i in range(k-1)) % d

            # This should equal F(sorted) - F(unsorted)
            f_sorted = (1 + sum(rho_pow[i+1] * two_pow[sorted_d[i]] % d for i in range(k-1))) % d
            correction = (f_sorted - f_val) % d

            # Verify bilinear = correction (they should differ by factor (ρ-1))
            # Actually: correction = Σ c_i · ρ^{i+1} = Σ c_i · (ρ^{i+1}-1) + Σ c_i · 1
            #                      = bilinear + q_at_1 = bilinear (since q_at_1 = 0)

        print(f"  Q(1) = 0 always: {q_at_1_always_zero}")
        print(f"  → Q(X) = (X-1) · R(X), correction = (ρ-1)·R(ρ)")
        print(f"  ρ-1 = {(rho-1) % d} mod {d} = -1/3 mod d (unit)")

        # Now check: does R(ρ) = 0 for any free solution?
        # R(ρ) = Σ c_i · (ρ^{i+1}-1)/(ρ-1) = Σ c_i · (1+ρ+...+ρ^i)
        rho_minus_1_inv = pow((rho - 1) % d, -1, d)

        r_at_rho_zero = False
        for deltas in cart_product(range(max_delta + 1), repeat=k-1):
            f_val = (1 + sum(rho_pow[i+1] * two_pow[deltas[i]] % d for i in range(k-1))) % d
            if f_val != 0: continue
            sorted_d = tuple(sorted(deltas))
            if sorted_d == deltas: continue

            coeffs = [(two_pow[sorted_d[i]] - two_pow[deltas[i]]) % d for i in range(k-1)]
            correction = sum(coeffs[i] * rho_pow[i+1] % d for i in range(k-1)) % d
            r_rho = (correction * rho_minus_1_inv) % d

            if r_rho == 0:
                r_at_rho_zero = True
                print(f"  *** R(ρ)=0 for δ={deltas}! ***")

        if not r_at_rho_zero:
            print(f"  R(ρ) ≠ 0 for ALL free solutions ✓")
            print(f"  → All corrections = (ρ-1)·R(ρ) ≠ 0 (both factors nonzero)")


if __name__ == '__main__':
    analyze_Q_structure()
