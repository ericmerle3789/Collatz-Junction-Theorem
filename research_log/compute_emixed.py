"""
R157 — Numerical verification of E_mixed (mixed additive-multiplicative energy)

E_mixed = #{(a1,a2,a3,a4) in {1,...,r-1}^4 :
    a1+a2 ≡ a3+a4 mod r           [additive in Z/rZ]
    AND (1-2^a1)(1-2^a2) = (1-2^a3)(1-2^a4) mod p  [multiplicative in F_p*]}

We decompose: E_mixed = E_trivial + N_cross
where E_trivial counts quadruples with {a3,a4} = {a1,a2} (as multisets)
and N_cross counts genuinely non-trivial collisions.
"""

from itertools import product

def ord_mod(base, p):
    """Order of base in (Z/pZ)*"""
    r = 1
    x = base % p
    while x != 1:
        x = (x * base) % p
        r += 1
    return r

def compute_emixed(p):
    """Compute E_mixed, E_trivial, N_cross for prime p with base 2."""
    r = ord_mod(2, p)

    # Precompute h(a) = 1 - 2^a mod p for a = 1, ..., r-1
    # Note: we need h(a) != 0, i.e., 2^a != 1, i.e., a != 0 mod r
    # For a in {1,...,r-1}, 2^a mod p != 1, so h(a) != 0
    pow2 = [1] * r
    for a in range(1, r):
        pow2[a] = (pow2[a-1] * 2) % p

    h = {}
    for a in range(1, r):
        h[a] = (1 - pow2[a]) % p
        # Verify h(a) != 0
        assert h[a] != 0, f"h({a}) = 0 for p={p}"

    # Build index: for each value v in F_p*, which a's map to it?
    val_to_indices = {}
    for a in range(1, r):
        v = h[a]
        if v not in val_to_indices:
            val_to_indices[v] = []
        val_to_indices[v].append(a)

    # Count E_mixed by brute force for small r
    E_mixed = 0
    E_trivial = 0
    N_cross = 0

    indices = list(range(1, r))

    if r <= 200:
        # Brute force: iterate over (a1, a2) and check all (a3, a4)
        # For each pair (a1, a2):
        #   additive constraint: a3+a4 ≡ a1+a2 mod r
        #   multiplicative constraint: h(a3)*h(a4) = h(a1)*h(a2) mod p

        for a1 in indices:
            for a2 in indices:
                s_add = (a1 + a2) % r  # target sum mod r
                prod_mult = (h[a1] * h[a2]) % p  # target product mod p

                for a3 in indices:
                    a4_needed = (s_add - a3) % r
                    if a4_needed == 0:
                        continue  # a4 must be in {1,...,r-1}
                    if a4_needed < 1 or a4_needed >= r:
                        continue

                    a4 = a4_needed
                    # Check multiplicative constraint
                    if (h[a3] * h[a4]) % p == prod_mult:
                        E_mixed += 1

                        # Is it trivial? {a3,a4} = {a1,a2} as multisets
                        if (a3 == a1 and a4 == a2) or (a3 == a2 and a4 == a1):
                            E_trivial += 1
                        else:
                            N_cross += 1
    else:
        # For larger r, use dictionary approach
        # Group pairs by (sum mod r, product mod p)
        pair_groups = {}
        for a1 in indices:
            for a2 in indices:
                key = ((a1 + a2) % r, (h[a1] * h[a2]) % p)
                if key not in pair_groups:
                    pair_groups[key] = []
                pair_groups[key].append((a1, a2))

        for key, pairs in pair_groups.items():
            n = len(pairs)
            E_mixed += n * n  # each pair matches with every other pair in same group

            # Count trivial: pairs that are multiset-equal
            for i, (a1, a2) in enumerate(pairs):
                for j, (a3, a4) in enumerate(pairs):
                    if (a3 == a1 and a4 == a2) or (a3 == a2 and a4 == a1):
                        E_trivial += 1

        N_cross = E_mixed - E_trivial

    return r, E_mixed, E_trivial, N_cross

def compute_additive_energy(r):
    """E_add = #{(a1,a2,a3,a4) in {1,...,r-1}^4 : a1+a2 ≡ a3+a4 mod r}"""
    # For each target sum s, count how many pairs (a1,a2) have a1+a2 ≡ s mod r
    count = {}
    for a1 in range(1, r):
        for a2 in range(1, r):
            s = (a1 + a2) % r
            count[s] = count.get(s, 0) + 1
    return sum(c*c for c in count.values())

def compute_mult_energy(p, r, h_vals):
    """E_mult = #{(a1,a2,a3,a4) in {1,...,r-1}^4 : h(a1)h(a2) = h(a3)h(a4) mod p}"""
    count = {}
    for a1 in range(1, r):
        for a2 in range(1, r):
            prod = (h_vals[a1] * h_vals[a2]) % p
            count[prod] = count.get(prod, 0) + 1
    return sum(c*c for c in count.values())

# Test primes
test_primes = [31, 89, 127, 257, 521, 1031, 8191]

print("=" * 90)
print("R157 — NUMERICAL VERIFICATION OF E_mixed")
print("=" * 90)
print()

for p in test_primes:
    r, E_mixed, E_trivial, N_cross = compute_emixed(p)
    E_add = compute_additive_energy(r)

    # Compute h values for mult energy
    pow2 = [1] * r
    for a in range(1, r):
        pow2[a] = (pow2[a-1] * 2) % p
    h_vals = {a: (1 - pow2[a]) % p for a in range(1, r)}
    E_mult = compute_mult_energy(p, r, h_vals)

    # Ratios
    r_minus_1 = r - 1
    trivial_expected = 2 * r_minus_1**2 - r_minus_1  # (r-1)(2r-3)

    print(f"p = {p}, r = ord_p(2) = {r}")
    print(f"  (r-1) = {r_minus_1}")
    print(f"  E_mixed   = {E_mixed}")
    print(f"  E_trivial = {E_trivial} (expected: {trivial_expected})")
    print(f"  N_cross   = {N_cross}")
    print(f"  E_add (additive only)  = {E_add}")
    print(f"  E_mult (mult only)     = {E_mult}")
    print(f"  --- Ratios ---")
    print(f"  E_mixed / (r-1)^2      = {E_mixed / r_minus_1**2:.4f}")
    print(f"  E_mixed / (r-1)^3      = {E_mixed / r_minus_1**3:.6f}")
    print(f"  N_cross / (r-1)^2      = {N_cross / r_minus_1**2:.4f}")
    print(f"  N_cross / (r-1)^3      = {N_cross / r_minus_1**3:.6f}")
    print(f"  E_add / (r-1)^3        = {E_add / r_minus_1**3:.6f}")
    print(f"  E_mult / (r-1)^3       = {E_mult / r_minus_1**3:.6f}")
    if E_add > 0 and E_mult > 0:
        # If independent: E_mixed ≈ E_add * E_mult / (r-1)^4
        E_indep = E_add * E_mult / r_minus_1**4
        print(f"  E_mixed / E_independent = {E_mixed / E_indep:.4f}")
    print(f"  --- Key test: is N_cross << (r-1)^2? ---")
    if r_minus_1 > 0:
        print(f"  N_cross / E_trivial = {N_cross / max(E_trivial, 1):.4f}")
    print()

print("=" * 90)
print("INTERPRETATION")
print("=" * 90)
print("""
If N_cross = 0 or N_cross << E_trivial:
  → E_mixed ≈ E_trivial = O(r^2), which is SMALL (target was r^{3-δ})
  → But this would mean the mixed energy is TRIVIALLY small, not via arithmetic
  → Same kill as T175: the double constraint is too restrictive

If N_cross ~ C * (r-1)^2 for constant C:
  → E_mixed = O(r^2), still quadratic, possibly useful

If N_cross ~ (r-1)^3:
  → E_mixed = O(r^3), no gain from double constraint
""")
