#!/usr/bin/env python3
"""
R160ter — Numerical exploration: the role of "+1" in 3x+1.

Computes for primes p | d(k), k=22..41:
  - H = <2> mod p, r = ord_p(2)
  - |H ∩ (1-H)|
  - Σ(1-h)^k mod p for k=1,2,3,4
  - Product identity Π(1-2^a) mod p vs r mod p
  - Sum Σ(1-2^a) mod p vs r mod p
  - 3^{-1} mod p membership in H
"""

import math

def d_of_k(k):
    S = math.ceil(k * math.log2(3)) + 1
    return 2**S - 3**k

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    d = 5
    while d * d <= n:
        if n % d == 0 or n % (d + 2) == 0:
            return False
        d += 6
    return True

def prime_factors(n):
    n = abs(n)
    factors = set()
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.add(d)
            n //= d
        d += 1
    if n > 1:
        factors.add(n)
    return sorted(factors)

def compute_H(p):
    """H = <2> mod p."""
    H = set()
    x = 1
    for _ in range(p):
        H.add(x)
        x = (x * 2) % p
        if x == 1:
            break
    return H, len(H)

# ============================================================
print("=" * 80)
print("R160ter — NUMERICAL EXPLORATION: THE ROLE OF '+1' IN 3x+1")
print("=" * 80)

# ============================================================
# PART 1: Primes dividing d(k) for k=22..25 (small enough)
# ============================================================
print("\n" + "=" * 80)
print("PART 1: PRIMES p | d(k), k=22..25")
print("=" * 80)

for k in range(22, 26):
    dk = d_of_k(k)
    S = math.ceil(k * math.log2(3)) + 1
    pfs = prime_factors(dk)
    # Filter to manageable primes
    pfs = [p for p in pfs if p >= 5 and p <= 10**7]

    print(f"\nk = {k}, S = {S}, d(k) = {dk}")
    print(f"Usable prime factors: {pfs}")

    for p in pfs:
        H, r = compute_H(p)
        one_minus_H = set((1 - h) % p for h in H)
        intersection = H & one_minus_H

        # Pairs h + h' = 1
        pairs = sum(1 for h in H if (1 - h) % p in H)

        # Product and Sum
        product_val = 1
        sum_val = 0
        for a in range(1, r):
            val = (1 - pow(2, a, p)) % p
            product_val = (product_val * val) % p
            sum_val = (sum_val + val) % p

        # Power sums
        power_sums = {}
        for pw in range(1, 5):
            ps = 0
            for a in range(1, r):
                val = (1 - pow(2, a, p)) % p
                ps = (ps + pow(val, pw, p)) % p
            power_sums[pw] = ps

        # 3 in H?
        three_in_H = (3 % p) in H
        inv3 = pow(3, p - 2, p)
        inv3_in_H = inv3 in H

        r_mod = r % p

        print(f"\n  p = {p}, r = {r}, g = {(p-1)//r}")
        print(f"  |H ∩ (1-H)| = {len(intersection)}, #pairs(h+h'=1) = {pairs}")
        if len(intersection) <= 20 and len(intersection) > 0:
            print(f"    Elements: {sorted(intersection)[:20]}")
        print(f"  Π(1-2^a) = {product_val}, Σ(1-2^a) = {sum_val}, r mod p = {r_mod}")
        print(f"  Prod=r? {product_val == r_mod}, Sum=r? {sum_val == r_mod}, Sum=Prod? {sum_val == product_val}")
        print(f"  Power sums: p1={power_sums[1]}, p2={power_sums[2]}, p3={power_sums[3]}, p4={power_sums[4]}")
        print(f"  3∈H: {three_in_H}, 3^-1∈H: {inv3_in_H}")

# ============================================================
# PART 2: Systematic test Sum = Product = r on small primes
# ============================================================
print("\n" + "=" * 80)
print("PART 2: SUM vs PRODUCT vs r mod p (p < 200)")
print("=" * 80)

print(f"\n{'p':>5} {'r':>5} {'g':>5} {'Sum':>8} {'Prod':>8} {'r%p':>5} {'S=r':>4} {'P=r':>4}")
print("-" * 50)

sum_eq_r_count = 0
prod_eq_r_count = 0
total = 0

for p in range(5, 200):
    if not is_prime(p):
        continue
    H, r = compute_H(p)

    product_val = 1
    sum_val = 0
    for a in range(1, r):
        val = (1 - pow(2, a, p)) % p
        product_val = (product_val * val) % p
        sum_val = (sum_val + val) % p

    r_mod = r % p
    s_r = sum_val == r_mod
    p_r = product_val == r_mod

    total += 1
    if s_r: sum_eq_r_count += 1
    if p_r: prod_eq_r_count += 1

    print(f"{p:5d} {r:5d} {(p-1)//r:5d} {sum_val:8d} {product_val:8d} {r_mod:5d} {'Y' if s_r else 'N':>4} {'Y' if p_r else 'N':>4}")

print(f"\nSummary: Sum=r in {sum_eq_r_count}/{total}, Prod=r in {prod_eq_r_count}/{total}")

# ============================================================
# PART 3: |H ∩ (1-H)| statistics
# ============================================================
print("\n" + "=" * 80)
print("PART 3: |H ∩ (1-H)| / r STATISTICS (p < 200)")
print("=" * 80)

print(f"\n{'p':>5} {'r':>5} {'|H∩(1-H)|':>10} {'ratio':>8} {'pairs':>6} {'3∈H':>5}")
print("-" * 50)

for p in range(5, 200):
    if not is_prime(p):
        continue
    H, r = compute_H(p)
    one_minus_H = set((1 - h) % p for h in H)
    intersection = H & one_minus_H
    pairs = sum(1 for h in H if (1 - h) % p in H)
    three_in = (3 % p) in H if p > 3 else None
    ratio = len(intersection) / r if r > 0 else 0

    print(f"{p:5d} {r:5d} {len(intersection):10d} {ratio:8.3f} {pairs:6d} {str(three_in):>5}")

# ============================================================
# PART 4: corrSum_c = c * corrSum_1 — analytical proof
# ============================================================
print("\n" + "=" * 80)
print("PART 4: corrSum_c = c * corrSum_1 — PROOF")
print("=" * 80)
print("""
For the generalized Collatz map T_c: n → (3n+c)/2^{a} (c odd):

Step j: n_{j+1} = (3*n_j + c) / 2^{a_{j+1}}

Unrolling k steps of a hypothetical cycle n_0 → n_1 → ... → n_k = n_0:

  n_0 * (2^S - 3^k) = c * Σ_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}

where B_j = S - Σ_{i=0}^{j} a_i (remaining halving exponent).

The right side is c * corrSum_1, where corrSum_1 is the value for c=1.

THEREFORE: corrSum_c = c * corrSum_1.

CONSEQUENCE for divisibility:
  d | corrSum_c  ⟺  d | (c * corrSum_1)  ⟺  d | corrSum_1
  (since gcd(c, d) = 1 when c is odd and coprime to 3, and d = 2^S - 3^k is odd)

So N_0(d) is INDEPENDENT of c: the "+1" has no special role for counting
cycle-compatible vectors. Any odd c coprime to 3 gives the same count.

HOWEVER: n = c * corrSum_1 / d, so the VALUE of the cycle number depends on c.
For c=1, we get the smallest possible |n| for each compatible vector.
""")

# ============================================================
# PART 5: Newton's identities on small primes
# ============================================================
print("=" * 80)
print("PART 5: NEWTON'S IDENTITIES for {1-2^a} (selected primes)")
print("=" * 80)

for p in [7, 13, 31, 43, 89, 127]:
    if not is_prime(p):
        continue
    H, r = compute_H(p)
    elts = [(1 - pow(2, a, p)) % p for a in range(1, r)]
    n = len(elts)
    if n == 0:
        continue

    # Power sums
    ps = {}
    for kk in range(1, min(n + 1, 7)):
        ps[kk] = sum(pow(x, kk, p) for x in elts) % p

    # Elementary symmetric polys via polynomial expansion
    poly = [1]
    for x in elts:
        new_poly = [0] * (len(poly) + 1)
        for i, c in enumerate(poly):
            new_poly[i] = (new_poly[i] + c) % p
            new_poly[i + 1] = (new_poly[i + 1] - c * x) % p
        poly = new_poly

    e = {}
    for j in range(1, n + 1):
        e[j] = ((-1) ** j * poly[j]) % p

    prod_val = 1
    for x in elts:
        prod_val = (prod_val * x) % p

    print(f"\np = {p}, r = {r}, n = {n} elements: {elts[:10]}{'...' if n > 10 else ''}")
    print(f"  Π(x_i) = {prod_val}, r mod p = {r % p}")
    print(f"  e_1 (=Σx_i) = {e.get(1, '?')}, e_n (=Πx_i) = {e.get(n, '?')}")
    print(f"  Power sums: { {kk: ps[kk] for kk in sorted(ps)} }")
    print(f"  Elem sym:   { {kk: e[kk] for kk in sorted(e) if kk <= 6} }")

    # Newton check
    for kk in range(1, min(n + 1, 5)):
        lhs = ps[kk]
        rhs = 0
        for j in range(1, kk):
            rhs = (rhs + (-1) ** (j - 1) * e.get(j, 0) * ps.get(kk - j, 0)) % p
        rhs = (rhs + (-1) ** (kk - 1) * kk * e.get(kk, 0)) % p
        ok = "OK" if lhs == rhs % p else "FAIL"
        print(f"  Newton k={kk}: p_{kk}={lhs}, RHS={rhs % p} [{ok}]")

# ============================================================
# PART 6: Sum = r proof
# ============================================================
print("\n" + "=" * 80)
print("PART 6: PROOF THAT Σ(1-2^a) = r mod p")
print("=" * 80)
print("""
Σ_{a=1}^{r-1} (1 - 2^a) mod p
= (r-1) - Σ_{a=1}^{r-1} 2^a mod p
= (r-1) - (2^r - 2)/(2 - 1) mod p
= (r-1) - (2^r - 2) mod p

Since 2^r ≡ 1 mod p (by definition of r = ord_p(2)):
= (r-1) - (1 - 2) mod p
= (r-1) - (-1) mod p
= r mod p.  ∎

This is ELEMENTARY. The sum identity Σ(1-2^a) ≡ r mod p holds for ALL primes p ∤ 2.
""")

print("=" * 80)
print("COMPUTATION COMPLETE")
print("=" * 80)
