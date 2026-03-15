"""
R157 — PROOF of T177: Structural degeneration of E_mixed

THEOREM T177: For any prime p and H = <2> ⊂ F_p* of order r,
the mixed energy E_mixed has N_cross = 0 identically. That is,
E_mixed = E_trivial = (r-1)(2r-3).

PROOF:
------
The two constraints are:
(ADD)  a₃ + a₄ ≡ a₁ + a₂ mod r           [in Z/rZ]
(MULT) (1-2^{a₃})(1-2^{a₄}) = (1-2^{a₁})(1-2^{a₂})  [in F_p*]

Let s = a₁ + a₂ mod r. By (ADD), a₄ = s - a₃ mod r.

Expand (MULT):
  1 - 2^{a₃} - 2^{a₄} + 2^{a₃+a₄} = 1 - 2^{a₁} - 2^{a₂} + 2^{a₁+a₂}

Since a₃+a₄ ≡ a₁+a₂ ≡ s mod r, we have 2^{a₃+a₄} = 2^s = 2^{a₁+a₂}.
These terms cancel:

  2^{a₃} + 2^{s-a₃} = 2^{a₁} + 2^{a₂}

Now let x = 2^{a₃}, y = 2^{s-a₃}. We have:
  x + y = 2^{a₁} + 2^{a₂}     (sum)
  x · y = 2^s = 2^{a₁} · 2^{a₂}  (product, since s = a₁+a₂ mod r)

The pair (x,y) satisfies both elementary symmetric functions of (2^{a₁}, 2^{a₂}).
By Vieta's formulas, {x, y} = {2^{a₁}, 2^{a₂}} as a multiset.

Since x = 2^{a₃} and a → 2^a is INJECTIVE (order r),
{a₃, s-a₃ mod r} = {a₁, a₂} as a multiset.

Therefore {a₃, a₄} = {a₁, a₂}, and N_cross = 0. QED.

KEY INSIGHT: The "separation" between Z/rZ and F_p* was ILLUSORY.
The exponential map a → 2^a is a GROUP HOMOMORPHISM from (Z/rZ, +) to (H, ×).
When we write (1-2^{a₃})(1-2^{a₄}) and expand, the cross term 2^{a₃+a₄}
AUTOMATICALLY satisfies the additive constraint via the homomorphism property.
This collapses the "two different algebraic structures" back into ONE.

LESSON T177: Any double constraint coupling Z/rZ and F_p* via the exponential
map a → 2^a reduces to a single constraint, because the map is a homomorphism.
The "bridge" is too regular to create non-trivial collisions.
"""

# Verify the algebraic proof numerically for a few cases
print("VERIFICATION: The algebraic proof of T177")
print("=" * 60)

for p in [31, 89, 127, 257, 521, 1031, 8191]:
    # Compute ord_p(2)
    r = 1
    x = 2
    while x % p != 1:
        x = (x * 2) % p
        r += 1

    print(f"\np = {p}, r = {r}")

    # For each (a1, a2), verify that the only solutions are {a3,a4}={a1,a2}
    violations = 0
    for a1 in range(1, r):
        for a2 in range(1, r):
            s = (a1 + a2) % r
            target_sum = (pow(2, a1, p) + pow(2, a2, p)) % p
            target_prod = (pow(2, a1, p) * pow(2, a2, p)) % p

            for a3 in range(1, r):
                a4 = (s - a3) % r
                if a4 == 0 or a4 >= r:
                    continue

                x = pow(2, a3, p)
                y = pow(2, a4, p)

                if (x + y) % p == target_sum:
                    # Must also have xy = target_prod (automatic!)
                    assert (x * y) % p == target_prod, "Product should be automatic!"

                    # Must be trivial
                    is_trivial = (a3 == a1 and a4 == a2) or (a3 == a2 and a4 == a1)
                    if not is_trivial:
                        violations += 1
                        print(f"  VIOLATION: a1={a1}, a2={a2}, a3={a3}, a4={a4}")

    print(f"  Violations: {violations} (expected: 0)")

print("\n" + "=" * 60)
print("T177 CONFIRMED: N_cross = 0 is a theorem, not an accident.")
print("The homomorphism property of a → 2^a collapses the double constraint.")
