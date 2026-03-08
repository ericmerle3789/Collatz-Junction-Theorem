#!/usr/bin/env python3
"""
r12_algebraic_structure.py -- Round 12: Algebraic Constraint 2^S = 3^k mod p
=============================================================================

CONTEXT:
  For d = 2^S - 3^k, any prime p | d satisfies 2^S = 3^k (mod p).
  corrSum(A) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{A_j}
  where A = (0 = A_0 < A_1 < ... < A_{k-1} <= S-1).

  We want N_0(p) = #{A : corrSum(A) = 0 (mod p)} = 0.

THE ALGEBRAIC CONSTRAINT:
  Since p | (2^S - 3^k), we have 2^S = 3^k (mod p).
  Let g = 2 * 3^{-1} mod p (the "ratio").
  Let t = ord_p(g).

  From 2 = 3*g: 2^S = 3^S * g^S, so 3^S * g^S = 3^k => g^S = 3^{k-S}.
  Since S > k (always), this constrains the structure in Z/pZ.

  corrSum(A) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{A_j}
  Let sigma(A) = corrSum(A) / 3^{k-1} mod p
             = sum_{j=0}^{k-1} 3^{-j} * 2^{A_j}  mod p
             = sum_{j=0}^{k-1} g^j * (2/g)^j * 3^{-j} * 2^{A_j} mod p

  Actually, simpler: 3^{-j} * 2^{A_j} = (2/3)^j * 2^{A_j - j} * ... No.
  Let's just write: sigma(A) = sum_{j=0}^{k-1} (3^{-1})^j * 2^{A_j} mod p.
  Since g = 2 * 3^{-1}: 3^{-1} = g * 2^{-1}, so (3^{-1})^j = g^j * 2^{-j}.
  Thus: sigma(A) = sum_{j=0}^{k-1} g^j * 2^{A_j - j} mod p.

  Dividing corrSum by 3^{k-1} is invertible mod p (since gcd(3,p) = 1),
  so N_0(p) = #{A : sigma(A) = 0 mod p}.

SEVEN-PART INVESTIGATION:
  Part 1: Algebraic structure -- express corrSum in terms of g = 2*3^{-1}.
  Part 2: Polynomial zero approach -- can corrSum be seen as polynomial zeros?
  Part 3: Congruence lattice -- image of corrSum mod p, coverage analysis.
  Part 4: Distinctness of corrSum values mod p.
  Part 5: Valuation obstructions -- primes that can NEVER divide corrSum.
  Part 6: Exhaustive corrSum mod p for k=3..15.
  Part 7: Self-tests (>= 25 tests, all must PASS).

HONESTY: All computations exact where feasible. If a claim FAILS, we say so.

Author: Claude (R12 for Eric Merle's Collatz Junction Theorem)
Date:   2026-03-08
"""

import math
import sys
import time
from itertools import combinations
from collections import Counter, defaultdict
from functools import lru_cache

# ============================================================================
# GLOBAL CONFIGURATION
# ============================================================================

T_START = time.time()
TIME_BUDGET = 290.0

TEST_RESULTS = []
FINDINGS = {}

VERBOSE = True


def elapsed():
    return time.time() - T_START


def time_remaining():
    return TIME_BUDGET - elapsed()


def check_budget(label=""):
    rem = time_remaining()
    if rem <= 0:
        raise TimeoutError(f"Time budget exhausted at {label}")
    return rem


def record_test(name, passed, detail=""):
    status = "PASS" if passed else "FAIL"
    TEST_RESULTS.append((name, passed, detail))
    print(f"  [{status}] {name}" + (f" -- {detail}" if detail else ""))


# ============================================================================
# SECTION 0: MATHEMATICAL PRIMITIVES
# ============================================================================

def compute_S(k):
    """S = ceil(k * log2(3)), computed exactly via integer comparison."""
    S_approx = math.ceil(k * math.log2(3))
    if (1 << S_approx) >= 3**k and (1 << (S_approx - 1)) < 3**k:
        return S_approx
    S = S_approx
    while (1 << S) < 3**k:
        S += 1
    while S > 0 and (1 << (S - 1)) >= 3**k:
        S -= 1
    return S


def compute_d(k):
    """d(k) = 2^S - 3^k, exact integer."""
    S = compute_S(k)
    return (1 << S) - 3**k


def compute_C(k):
    """C(S-1, k-1): number of compositions."""
    S = compute_S(k)
    return math.comb(S - 1, k - 1)


def is_prime(n):
    """Miller-Rabin deterministic for n < 3.3e24."""
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    witnesses = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    d_val = n - 1
    r = 0
    while d_val % 2 == 0:
        d_val //= 2
        r += 1
    for a in witnesses:
        if a >= n:
            continue
        x = pow(a, d_val, n)
        if x == 1 or x == n - 1:
            continue
        found = False
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                found = True
                break
        if not found:
            return False
    return True


def trial_factor(n, limit=10**7):
    """Factor n by trial division up to limit."""
    if n <= 1:
        return []
    factors = []
    for p in [2, 3]:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e > 0:
            factors.append((p, e))
    p = 5
    step = 2
    while p * p <= n and p <= limit:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e > 0:
            factors.append((p, e))
        p += step
        step = 6 - step
    if n > 1:
        factors.append((n, 1))
    return factors


def pollard_rho_factor(n, max_iter=200000):
    """Pollard's rho for factoring."""
    if n <= 1:
        return []
    if is_prime(n):
        return [(n, 1)]
    if n % 2 == 0:
        e = 0
        while n % 2 == 0:
            n //= 2
            e += 1
        rest = pollard_rho_factor(n, max_iter) if n > 1 else []
        return [(2, e)] + rest
    for c in range(1, 50):
        x = 2
        y = 2
        d_val = 1
        f = lambda z, _c=c: (z * z + _c) % n
        count = 0
        while d_val == 1 and count < max_iter:
            x = f(x)
            y = f(f(y))
            d_val = math.gcd(abs(x - y), n)
            count += 1
        if 1 < d_val < n:
            f1 = pollard_rho_factor(d_val, max_iter)
            f2 = pollard_rho_factor(n // d_val, max_iter)
            merged = {}
            for (p, e) in f1 + f2:
                merged[p] = merged.get(p, 0) + e
            return sorted(merged.items())
    return [(n, 1)]


def full_factor(n, limit=10**7):
    """Factor n completely. Returns sorted list of (p, e)."""
    n = abs(n)
    if n <= 1:
        return []
    factors = trial_factor(n, limit)
    result = []
    for (p, e) in factors:
        if p <= limit * limit or is_prime(p):
            result.append((p, e))
        else:
            sub = pollard_rho_factor(p)
            if sub:
                for (q, f_exp) in sub:
                    result.append((q, f_exp * e))
            else:
                result.append((p, e))
    merged = {}
    for (p, e) in result:
        merged[p] = merged.get(p, 0) + e
    return sorted(merged.items())


def prime_factors_list(n):
    """Sorted list of distinct prime factors of |n|."""
    return sorted(set(p for p, _ in full_factor(n)))


def modinv(a, m):
    """Modular inverse of a mod m. Returns None if gcd != 1."""
    if m == 1:
        return 0
    g, x, _ = _extended_gcd(a % m, m)
    if g != 1:
        return None
    return x % m


def _extended_gcd(a, b):
    """Extended Euclidean algorithm."""
    if a == 0:
        return b, 0, 1
    g, x, y = _extended_gcd(b % a, a)
    return g, y - (b // a) * x, x


def multiplicative_order(base, p):
    """Multiplicative order of base mod p. Returns None if gcd != 1."""
    if p <= 1:
        return 1
    if math.gcd(base, p) != 1:
        return None
    x = base % p
    for i in range(1, p + 1):
        if x == 1:
            return i
        x = (x * base) % p
    return p  # should not happen for prime p


def corrSum_of_A(A_seq, k):
    """corrSum(A) = sum_{i=0}^{k-1} 3^{k-1-i} * 2^{A_i}, exact integer."""
    total = 0
    for i in range(k):
        total += pow(3, k - 1 - i) * (1 << A_seq[i])
    return total


def corrsum_mod(B_tuple, k, mod):
    """corrSum mod `mod` from B = (a_1,...,a_{k-1}), with a_0=0 implicit."""
    result = pow(3, k - 1, mod)
    for idx in range(len(B_tuple)):
        j = idx + 1
        result = (result + pow(3, k - 1 - j, mod) * pow(2, B_tuple[idx], mod)) % mod
    return result


def enumerate_all_compositions(k):
    """Yields A = (0, a_1, ..., a_{k-1}) with 0 < a_1 < ... < a_{k-1} <= S-1."""
    S = compute_S(k)
    for chosen in combinations(range(1, S), k - 1):
        yield (0,) + chosen


def get_residue_distribution(k, p, max_enum=2_000_000):
    """Distribution of corrSum(A) mod p. Returns Counter or None if too large."""
    S = compute_S(k)
    C = math.comb(S - 1, k - 1)
    if C > max_enum:
        return None
    dist = Counter()
    for B in combinations(range(1, S), k - 1):
        r = corrsum_mod(B, k, p)
        dist[r] += 1
    return dist


def compute_N0(k, p, dist=None, max_enum=2_000_000):
    """N_0(p) = #{A : corrSum(A) = 0 mod p}."""
    if dist is None:
        dist = get_residue_distribution(k, p, max_enum)
    if dist is None:
        return None
    return dist.get(0, 0)


# ============================================================================
# PART 1: ALGEBRAIC STRUCTURE -- corrSum in terms of g = 2 * 3^{-1} mod p
# ============================================================================

def compute_normalized_sigma(A_seq, k, p):
    """
    sigma(A) = corrSum(A) / 3^{k-1} mod p
             = sum_{j=0}^{k-1} (3^{-1})^j * 2^{A_j} mod p
             = sum_{j=0}^{k-1} g^j * 2^{A_j - j} mod p   where g = 2*3^{-1}

    But let's be very careful. Starting from:
      corrSum(A) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{A_j}

    Divide by 3^{k-1}:
      sigma(A) = sum_{j=0}^{k-1} 3^{-j} * 2^{A_j}  mod p

    Now 3^{-1} mod p exists since p >= 5 (p | d, d is odd, 3 does not divide d).
    Let inv3 = 3^{-1} mod p. Then:
      sigma(A) = sum_{j=0}^{k-1} inv3^j * 2^{A_j}  mod p

    Let g = 2 * inv3 mod p. Then inv3 = g * modinv(2, p).
    So inv3^j = g^j * modinv(2,p)^j. And:
      sigma(A) = sum_{j=0}^{k-1} g^j * 2^{-j} * 2^{A_j} mod p
               = sum_{j=0}^{k-1} g^j * 2^{A_j - j}  mod p

    This is the CORRECT normalized form.
    """
    inv3 = modinv(3, p)
    if inv3 is None:
        return None
    result = 0
    for j in range(k):
        aj = A_seq[j]
        # term = inv3^j * 2^{A_j} mod p
        term = (pow(inv3, j, p) * pow(2, aj, p)) % p
        result = (result + term) % p
    return result


def compute_sigma_g_form(A_seq, k, p):
    """
    sigma(A) = sum_{j=0}^{k-1} g^j * 2^{A_j - j}  mod p
    where g = 2 * 3^{-1} mod p.

    Note: A_j >= j always (since 0 = A_0 < A_1 < ... and each A_j >= j).
    So A_j - j >= 0 always, and 2^{A_j - j} is well-defined.
    """
    inv3 = modinv(3, p)
    if inv3 is None:
        return None
    g = (2 * inv3) % p
    result = 0
    for j in range(k):
        aj = A_seq[j]
        # g^j * 2^{A_j - j}
        term = (pow(g, j, p) * pow(2, aj - j, p)) % p
        result = (result + term) % p
    return result


def part1_algebraic_structure(k_max=15):
    """
    Part 1: Express corrSum in terms of g = 2*3^{-1} mod p and verify
    the algebraic identity. Investigate:
      - What is ord_p(g)? How does it relate to t = ord_p(2)?
      - The constraint g^S = 3^{k-S} mod p (from 2^S = 3^k mod p)
      - Can we factor sigma(A)?
    """
    print("\n" + "=" * 72)
    print("PART 1: ALGEBRAIC STRUCTURE -- corrSum via g = 2 * 3^{-1} mod p")
    print("=" * 72)

    results = {}

    for k in range(3, k_max + 1):
        if time_remaining() < 30:
            print(f"  [BUDGET] Stopping at k={k}")
            break

        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)
        if d <= 0 or C > 500_000:
            continue

        primes = prime_factors_list(d)
        k_results = []

        for p in primes:
            inv3 = modinv(3, p)
            inv2 = modinv(2, p)
            if inv3 is None or inv2 is None:
                continue

            g = (2 * inv3) % p
            ord_g = multiplicative_order(g, p)
            ord_2 = multiplicative_order(2, p)
            ord_3 = multiplicative_order(3, p)

            # Verify the constraint: 2^S = 3^k mod p
            check_constraint = pow(2, S, p) == pow(3, k, p)

            # Verify: g^S = 3^{k-S} mod p
            # From 2^S = 3^k => (3g)^S = 3^k => 3^S * g^S = 3^k => g^S = 3^{k-S}
            g_S = pow(g, S, p)
            expected_gS = pow(3, k - S, p) if k >= S else (pow(3, k - S + (p - 1), p))
            # k < S always for our range, so k - S < 0, so 3^{k-S} = modinv(3^{S-k}, p)
            inv3_power = pow(modinv(3, p), S - k, p)
            check_gS = (g_S == inv3_power)

            # Verify sigma == corrSum / 3^{k-1} for all compositions
            sigma_ok = True
            n0_sigma = 0
            n0_corr = 0
            inv3k1 = modinv(pow(3, k - 1, p), p)

            for A in enumerate_all_compositions(k):
                cs = corrSum_of_A(A, k) % p
                sig1 = compute_normalized_sigma(A, k, p)
                sig2 = compute_sigma_g_form(A, k, p)

                # sigma should equal corrSum * inv(3^{k-1}) mod p
                expected_sig = (cs * inv3k1) % p
                if sig1 != expected_sig or sig2 != expected_sig:
                    sigma_ok = False

                if cs == 0:
                    n0_corr += 1
                if sig1 == 0:
                    n0_sigma += 1

            # The key: N0 from sigma equals N0 from corrSum (both or neither zero)
            n0_match = (n0_sigma == n0_corr)

            info = {
                'p': p, 'g': g, 'ord_g': ord_g, 'ord_2': ord_2, 'ord_3': ord_3,
                'constraint_ok': check_constraint, 'gS_ok': check_gS,
                'sigma_ok': sigma_ok, 'N0': n0_corr, 'n0_match': n0_match,
                'g_S_mod_p': g_S, 'S_mod_ord_g': S % ord_g if ord_g else None,
            }
            k_results.append(info)

            if VERBOSE:
                print(f"  k={k:2d} p={p:8d}  g={g:6d}  "
                      f"ord(g)={ord_g:6d}  ord(2)={ord_2:6d}  ord(3)={ord_3:6d}  "
                      f"2^S=3^k:{check_constraint}  g^S=3^{{k-S}}:{check_gS}  "
                      f"sigma_ok:{sigma_ok}  N0={n0_corr}")

        results[k] = k_results

    # Analysis: relationship between ord(g), ord(2), ord(3)
    print("\n  ANALYSIS: ord(g) patterns")
    for k, k_results in results.items():
        for info in k_results:
            p = info['p']
            og = info['ord_g']
            o2 = info['ord_2']
            o3 = info['ord_3']
            # g = 2/3, so ord(g) | lcm(ord(2), ord(3))
            lcm_23 = (o2 * o3) // math.gcd(o2, o3)
            divides_lcm = (lcm_23 % og == 0)
            print(f"    k={k:2d} p={p:8d}: ord(g)={og}, "
                  f"lcm(ord2,ord3)={lcm_23}, divides: {divides_lcm}")

    FINDINGS['part1'] = results
    return results


# ============================================================================
# PART 2: POLYNOMIAL ZERO APPROACH
# ============================================================================

def part2_polynomial_zeros(k_max=12):
    """
    Part 2: Can corrSum(A) mod p be viewed as a polynomial evaluated at points?

    Key observation: sigma(A) = sum_{j=0}^{k-1} g^j * 2^{A_j - j} mod p.

    Let B_j = A_j - j (the "gaps"). Then B_0 = 0, B_1 >= 0, ..., B_{k-1} >= 0,
    and B_0 <= B_1 <= ... <= B_{k-1} (weakly increasing).
    Actually: A_j >= j (strictly increasing from 0), so B_j = A_j - j >= 0.
    Also A_{j+1} > A_j implies B_{j+1} = A_{j+1} - (j+1) >= A_j + 1 - j - 1 = B_j.
    So the gaps B_j are WEAKLY increasing non-negative integers.

    sigma(A) = sum_{j=0}^{k-1} g^j * 2^{B_j} mod p

    Now define x_j = 2^{B_j} mod p. Since B_j is weakly increasing and
    B_j <= S - 1 - j, the x_j are powers of 2 in a structured way.

    If all B_j were the SAME (say B_j = b for all j), then:
      sigma = 2^b * sum_{j=0}^{k-1} g^j = 2^b * (g^k - 1)/(g - 1)  [if g != 1]

    For this to be 0 mod p, need g^k = 1 mod p, i.e., ord_p(g) | k.
    We investigate this and more general polynomial patterns.
    """
    print("\n" + "=" * 72)
    print("PART 2: POLYNOMIAL ZERO APPROACH")
    print("=" * 72)

    results = {}

    for k in range(3, k_max + 1):
        if time_remaining() < 30:
            print(f"  [BUDGET] Stopping at k={k}")
            break

        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)
        if d <= 0 or C > 200_000:
            continue

        primes = prime_factors_list(d)

        for p in primes:
            if p < 5:
                continue

            inv3 = modinv(3, p)
            g = (2 * inv3) % p
            ord_g = multiplicative_order(g, p)

            # Check: does ord(g) | k? If so, the "constant-gap" composition
            # would give sigma = 0, which means N0(p) > 0.
            divides_k = (k % ord_g == 0) if ord_g else False

            # Compute the geometric sum: G_k(g) = sum_{j=0}^{k-1} g^j mod p
            if g % p == 1:
                geom_sum = k % p
            else:
                geom_sum = (pow(g, k, p) - 1) * modinv(g - 1, p) % p

            # If geom_sum = 0 mod p, then any "constant-gap" composition has sigma = 0
            constant_gap_zero = (geom_sum == 0)

            # For the "polynomial" view: is there a polynomial P(x) such that
            # sigma(A) = P(x) for some x depending on A?
            # Answer: NO in general, because sigma depends on k independent
            # values B_0, ..., B_{k-1}. But we can view it as a multilinear form.

            # Compute: how many compositions give sigma = 0?
            n0 = compute_N0(k, p)

            # The "gap representation": B_j = A_j - j
            # sigma = sum_{j=0}^{k-1} g^j * 2^{B_j} mod p
            # This is a sum of terms from the set {g^j * 2^b : b >= 0}
            # Each term is in the multiplicative group generated by g and 2.
            # Since g = 2/3, the group is generated by 2 and 3, which is
            # the full multiplicative group (F_p^*) for most primes.

            print(f"  k={k:2d} p={p:8d}  g={g:6d}  ord(g)={ord_g:6d}  "
                  f"g|k:{divides_k}  geom_sum={geom_sum:8d}  "
                  f"const_gap_zero:{constant_gap_zero}  N0={n0}")

            if constant_gap_zero and n0 is not None and n0 > 0:
                # Find a witness: a constant-gap composition where sigma = 0
                for b in range(S - k + 1):
                    # A_j = j + b for all j: only works if A_{k-1} = k-1+b <= S-1
                    if k - 1 + b <= S - 1:
                        A = tuple(j + b for j in range(k))
                        cs = corrSum_of_A(A, k) % p
                        sig = compute_sigma_g_form(A, k, p)
                        if sig == 0:
                            print(f"    WITNESS: A={A}, corrSum mod p = {cs}, sigma = {sig}")
                            break

            results[(k, p)] = {
                'g': g, 'ord_g': ord_g, 'divides_k': divides_k,
                'geom_sum': geom_sum, 'constant_gap_zero': constant_gap_zero,
                'N0': n0
            }

    # Summary: when does ord(g) | k?
    print("\n  SUMMARY: ord(g) | k cases")
    for (k, p), info in results.items():
        if info['divides_k']:
            print(f"    k={k}, p={p}: ord(g)={info['ord_g']} | k  "
                  f"=> constant-gap zero: {info['constant_gap_zero']}  N0={info['N0']}")

    # Key finding: constant_gap_zero is NECESSARY for N0 > 0 but not sufficient
    # (because constant-gap compositions might not be valid).
    cgz_implies_n0_pos = all(
        info['N0'] > 0 for info in results.values()
        if info['constant_gap_zero'] and info['N0'] is not None
    )
    print(f"\n  constant_gap_zero => N0 > 0?  {cgz_implies_n0_pos}")

    FINDINGS['part2'] = results
    return results


# ============================================================================
# PART 3: CONGRUENCE LATTICE -- Image of corrSum mod p
# ============================================================================

def part3_congruence_lattice(k_max=15):
    """
    Part 3: How much of Z/pZ does {corrSum(A) mod p} cover?
    If the image covers all of Z/pZ minus {0}, then N0(p) = 0.
    If the image misses many residues, 0 might be among the missed ones.
    """
    print("\n" + "=" * 72)
    print("PART 3: CONGRUENCE LATTICE -- Image Size Analysis")
    print("=" * 72)

    results = {}

    for k in range(3, k_max + 1):
        if time_remaining() < 30:
            print(f"  [BUDGET] Stopping at k={k}")
            break

        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)
        if d <= 0 or C > 500_000:
            continue

        primes = prime_factors_list(d)

        for p in primes:
            dist = get_residue_distribution(k, p)
            if dist is None:
                continue

            # Image: set of residues that appear
            image = set(dist.keys())
            image_size = len(image)

            # Missed residues
            missed = set(range(p)) - image
            missed_size = len(missed)

            # Is 0 in the image?
            zero_in_image = (0 in image)

            # Coverage ratio
            coverage = image_size / p

            # Maximum and minimum multiplicities
            max_mult = max(dist.values())
            min_mult = min(dist.values())

            # Uniformity: how close to C/p?
            expected = C / p
            max_dev = max(abs(c - expected) for c in dist.values()) / expected if expected > 0 else 0

            n0 = dist.get(0, 0)

            print(f"  k={k:2d} p={p:8d}  C={C:8d}  |Im|={image_size:6d}  "
                  f"|miss|={missed_size:6d}  coverage={coverage:.4f}  "
                  f"0_in_Im:{zero_in_image}  N0={n0}  "
                  f"mult_range=[{min_mult},{max_mult}]  max_dev={max_dev:.3f}")

            if not zero_in_image and missed_size > 0:
                # Show a few missed residues
                missed_sample = sorted(missed)[:10]
                print(f"    Missed residues (sample): {missed_sample}")

            results[(k, p)] = {
                'image_size': image_size, 'missed_size': missed_size,
                'zero_in_image': zero_in_image, 'coverage': coverage,
                'N0': n0, 'max_mult': max_mult, 'min_mult': min_mult,
                'max_dev': max_dev, 'C': C, 'p': p,
            }

    # Summary analysis
    print("\n  SUMMARY: Coverage patterns")
    # When C > p: image should cover most/all of Z/pZ
    cases_C_gt_p = [(kp, info) for kp, info in results.items() if info['C'] > info['p']]
    cases_C_le_p = [(kp, info) for kp, info in results.items() if info['C'] <= info['p']]

    if cases_C_gt_p:
        full_coverage = sum(1 for _, info in cases_C_gt_p if info['coverage'] >= 0.999)
        print(f"  C > p: {len(cases_C_gt_p)} cases, full coverage: {full_coverage}")
        zero_not_hit = sum(1 for _, info in cases_C_gt_p if not info['zero_in_image'])
        print(f"  C > p: 0 not in image: {zero_not_hit} cases")

    if cases_C_le_p:
        print(f"  C <= p: {len(cases_C_le_p)} cases")
        for (k, p), info in cases_C_le_p:
            print(f"    k={k} p={p}: C/p = {info['C']/info['p']:.4f}, "
                  f"coverage={info['coverage']:.4f}, N0={info['N0']}")

    FINDINGS['part3'] = results
    return results


# ============================================================================
# PART 4: DISTINCTNESS OF corrSum VALUES mod p
# ============================================================================

def part4_distinctness(k_max=14):
    """
    Part 4: Are corrSum values distinct mod p?
    If |{corrSum(A) mod p}| = C (all distinct), and C < p, then
    the probability that 0 is among the C values is C/p.
    For a proof, we need STRUCTURAL reasons why corrSum values are distinct.
    """
    print("\n" + "=" * 72)
    print("PART 4: DISTINCTNESS OF corrSum VALUES mod p")
    print("=" * 72)

    results = {}

    for k in range(3, k_max + 1):
        if time_remaining() < 25:
            print(f"  [BUDGET] Stopping at k={k}")
            break

        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)
        if d <= 0 or C > 300_000:
            continue

        primes = prime_factors_list(d)

        for p in primes:
            dist = get_residue_distribution(k, p)
            if dist is None:
                continue

            image_size = len(dist)
            all_distinct = (image_size == C)
            max_mult = max(dist.values())
            collision_rate = 1.0 - image_size / C if C > 0 else 0

            # For p < C, collisions are inevitable (pigeonhole)
            pigeonhole_collisions = (C > p)

            # When all distinct, count how many residues are missed
            if all_distinct:
                missed_count = p - image_size
                zero_is_missed = (0 not in dist)
            else:
                missed_count = p - image_size
                zero_is_missed = (0 not in dist)

            n0 = dist.get(0, 0)

            print(f"  k={k:2d} p={p:8d}  C={C:8d}  |Im|={image_size:6d}  "
                  f"distinct:{all_distinct}  max_mult={max_mult:4d}  "
                  f"collision={collision_rate:.4f}  N0={n0}")

            # When p > C and values are distinct, analyze the "missed" structure
            if p > C and all_distinct and n0 == 0:
                print(f"    ALL DISTINCT, p > C, N0=0: {p - C} residues missed, "
                      f"0 is among them")

            results[(k, p)] = {
                'all_distinct': all_distinct, 'max_mult': max_mult,
                'collision_rate': collision_rate, 'N0': n0,
                'pigeonhole': pigeonhole_collisions, 'p': p, 'C': C,
            }

    # Analysis: when are values distinct?
    print("\n  DISTINCTNESS ANALYSIS:")
    distinct_cases = [(kp, info) for kp, info in results.items() if info['all_distinct']]
    nondistinct_cases = [(kp, info) for kp, info in results.items() if not info['all_distinct']]
    print(f"  All distinct: {len(distinct_cases)} cases")
    print(f"  Collisions:   {len(nondistinct_cases)} cases")

    if nondistinct_cases:
        print("  Cases with collisions:")
        for (k, p), info in nondistinct_cases:
            print(f"    k={k} p={p}: C={info['C']}, |Im|={info['C'] - int(info['C']*info['collision_rate'])}, "
                  f"max_mult={info['max_mult']}, N0={info['N0']}")

    FINDINGS['part4'] = results
    return results


# ============================================================================
# PART 5: VALUATION OBSTRUCTIONS
# ============================================================================

def part5_valuation_obstructions(k_max=20):
    """
    Part 5: Which primes can NEVER divide corrSum(A) for ANY composition A?

    Known:
      (P1) corrSum is always ODD: the j=0 term is 3^{k-1} * 2^0 = 3^{k-1} (odd),
           all other terms are even. So corrSum is odd. Thus 2 never divides corrSum.
      (P2) gcd(corrSum, 3) = 1: need to verify this carefully.

    Can we extend: are there other small primes q such that q never divides corrSum?
    """
    print("\n" + "=" * 72)
    print("PART 5: VALUATION OBSTRUCTIONS -- Which primes never divide corrSum?")
    print("=" * 72)

    results = {}

    for k in range(3, k_max + 1):
        if time_remaining() < 20:
            print(f"  [BUDGET] Stopping at k={k}")
            break

        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)
        if d <= 0 or C > 300_000:
            continue

        # Check small primes q: does q | corrSum(A) for any A?
        test_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
        obstructions = {}

        for q in test_primes:
            # Count compositions with corrSum = 0 mod q
            n0q = 0
            total = 0
            for B in combinations(range(1, S), k - 1):
                cs_mod = corrsum_mod(B, k, q)
                if cs_mod == 0:
                    n0q += 1
                total += 1

            obstructions[q] = n0q
            if n0q == 0:
                tag = "NEVER divides"
            else:
                tag = f"divides {n0q}/{total} = {n0q/total:.4f}"
            # Only print the interesting ones (q=2,3 and any with n0q=0)
            if q <= 3 or n0q == 0:
                print(f"  k={k:2d}  q={q:3d}: {tag}")

        results[k] = obstructions

    # Summary: universal obstructions (primes that NEVER divide corrSum for ALL k)
    print("\n  UNIVERSAL OBSTRUCTIONS:")
    all_ks = sorted(results.keys())
    for q in [2, 3, 5, 7, 11, 13]:
        never_divides_all = all(results[k].get(q, 1) == 0 for k in all_ks)
        if never_divides_all:
            print(f"  q={q}: NEVER divides corrSum(A) for any k in {all_ks}")
        else:
            fail_ks = [k for k in all_ks if results[k].get(q, 1) > 0]
            print(f"  q={q}: divides corrSum for some A at k = {fail_ks[:10]}")

    # Verify P1 and P2 rigorously
    print("\n  RIGOROUS VERIFICATION:")
    p1_holds = all(results[k].get(2, 1) == 0 for k in all_ks)
    p2_holds = all(results[k].get(3, 1) == 0 for k in all_ks)
    print(f"  P1 (corrSum always odd):      {p1_holds}")
    print(f"  P2 (3 never divides corrSum): {p2_holds}")

    # Prove P1 algebraically:
    # corrSum(A) = 3^{k-1} * 1 + sum_{j>=1} 3^{k-1-j} * 2^{A_j}
    # The j=0 term is 3^{k-1} (odd since 3 is odd).
    # All j>=1 terms have factor 2^{A_j} with A_j >= 1, so each is even.
    # Sum = odd + even + ... + even = odd. QED.
    print("  P1 proof: j=0 term = 3^{k-1} (odd), all j>=1 terms have 2^{A_j>=1} (even).")
    print("            Sum = odd + evens = odd. QED.")

    # Prove P2 algebraically:
    # corrSum(A) mod 3:
    # 3^{k-1-j} mod 3 = 0 for j < k-1, and = 1 for j = k-1.
    # So corrSum mod 3 = 3^0 * 2^{A_{k-1}} mod 3 = 2^{A_{k-1}} mod 3.
    # 2^0 = 1, 2^1 = 2, 2^2 = 1, ... so 2^n mod 3 = 1 if n even, 2 if n odd.
    # In either case, 2^{A_{k-1}} mod 3 != 0. QED.
    print("  P2 proof: corrSum mod 3 = 2^{A_{k-1}} mod 3 (since 3^{j}=0 mod 3 for j>=1).")
    print("            2^n mod 3 in {1, 2}, never 0. QED.")

    FINDINGS['part5'] = results
    return results


# ============================================================================
# PART 6: EXHAUSTIVE corrSum mod p FOR k=3..15
# ============================================================================

def part6_exhaustive(k_max=15):
    """
    Part 6: For each k=3..k_max, enumerate ALL compositions and compute
    corrSum mod p for each small prime p | d.
    Track: which residues are hit/missed, is 0 missed.
    For k where 0 IS hit: identify the bad compositions and analyze them.
    """
    print("\n" + "=" * 72)
    print("PART 6: EXHAUSTIVE corrSum mod p -- Complete Classification")
    print("=" * 72)

    results = {}

    for k in range(3, k_max + 1):
        if time_remaining() < 20:
            print(f"  [BUDGET] Stopping at k={k}")
            break

        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)
        if d <= 0:
            continue

        factors = full_factor(d)
        primes = sorted(set(p for p, _ in factors))

        # Can we enumerate?
        can_enum = C <= 500_000

        if not can_enum:
            print(f"  k={k:2d}  S={S}  d={d}  C={C}  [TOO LARGE]")
            continue

        print(f"\n  k={k:2d}  S={S}  d={d}  C={C}")
        print(f"    factors: {' * '.join(f'{p}^{e}' if e > 1 else str(p) for p, e in factors)}")

        k_results = {}

        for p in primes:
            dist = get_residue_distribution(k, p)
            if dist is None:
                continue

            n0 = dist.get(0, 0)
            image = set(dist.keys())
            image_size = len(image)
            missed = sorted(set(range(p)) - image)

            k_results[p] = {
                'N0': n0, 'image_size': image_size,
                'missed_count': len(missed),
                'zero_in_image': 0 in image,
            }

            tag = "BLOCKS (N0=0)" if n0 == 0 else f"N0={n0}"
            print(f"    p={p:10d}: |Im|={image_size:6d}/{p} = {image_size/p:.4f}  {tag}")

            if n0 > 0 and n0 <= 20:
                # Show the bad compositions
                bad_comps = []
                for B in combinations(range(1, S), k - 1):
                    r = corrsum_mod(B, k, p)
                    if r == 0:
                        A = (0,) + B
                        bad_comps.append(A)
                        if len(bad_comps) >= 10:
                            break
                if bad_comps:
                    print(f"      Bad compositions (corrSum = 0 mod {p}):")
                    for A in bad_comps[:5]:
                        cs = corrSum_of_A(A, k)
                        print(f"        A={A}  corrSum={cs}  corrSum/d={cs/d:.4f}")

        # CRT check: N0(d) = 0?
        n0_d = 0
        for A in enumerate_all_compositions(k):
            if corrSum_of_A(A, k) % d == 0:
                n0_d += 1

        blocking_type = 'FAIL'
        if n0_d == 0:
            has_single = any(k_results[p]['N0'] == 0 for p in k_results)
            blocking_type = 'SINGLE' if has_single else 'CRT'

        print(f"    N0(d) = {n0_d}  [{blocking_type}]")

        results[k] = {
            'S': S, 'd': d, 'C': C, 'primes': primes,
            'per_prime': k_results, 'N0_d': n0_d,
            'blocking_type': blocking_type,
        }

    # Grand summary
    print("\n  GRAND SUMMARY:")
    for k in sorted(results.keys()):
        info = results[k]
        bp = [p for p in info['primes'] if info['per_prime'].get(p, {}).get('N0', -1) == 0]
        print(f"  k={k:2d}: N0(d)={info['N0_d']}  type={info['blocking_type']}  "
              f"blocking_primes={bp[:5]}")

    FINDINGS['part6'] = results
    return results


# ============================================================================
# PART 7: SELF-TESTS (>= 25 tests, all must PASS)
# ============================================================================

def run_self_tests():
    """Verify mathematical correctness before any analysis."""
    print("=" * 72)
    print("SELF-TESTS (>= 25)")
    print("=" * 72)

    # T01: S values for known k
    ok = (compute_S(1) == 2 and compute_S(2) == 4 and compute_S(3) == 5
          and compute_S(5) == 8 and compute_S(10) == 16)
    record_test("T01: S values correct for k=1,2,3,5,10", ok)

    # T02: d values for known k
    ok = (compute_d(1) == 1 and compute_d(2) == 7 and compute_d(3) == 5
          and compute_d(4) == 47 and compute_d(5) == 13)
    record_test("T02: d(1)=1, d(2)=7, d(3)=5, d(4)=47, d(5)=13", ok,
                f"got d(1)={compute_d(1)}, d(2)={compute_d(2)}, d(3)={compute_d(3)}, "
                f"d(4)={compute_d(4)}, d(5)={compute_d(5)}")

    # T03: C(k) = comb(S-1, k-1) for small k
    ok = True
    for k in [3, 4, 5, 6]:
        S = compute_S(k)
        expected = math.comb(S - 1, k - 1)
        if compute_C(k) != expected:
            ok = False
    record_test("T03: C(k) = comb(S-1, k-1) for k=3..6", ok)

    # T04: corrSum exact values for k=3
    # k=3, S=5, d=5. A = (0, a1, a2) with 0 < a1 < a2 <= 4
    # Compositions: (0,1,2),(0,1,3),(0,1,4),(0,2,3),(0,2,4),(0,3,4)
    k = 3
    all_A = list(enumerate_all_compositions(k))
    ok = len(all_A) == compute_C(k) == 6
    record_test("T04: k=3 has exactly 6 compositions", ok, f"got {len(all_A)}")

    # T05: corrSum is always positive
    ok = all(corrSum_of_A(A, 3) > 0 for A in all_A)
    record_test("T05: corrSum > 0 for all compositions (k=3)", ok)

    # T06: corrSum is always odd (P1)
    ok = all(corrSum_of_A(A, 3) % 2 == 1 for A in all_A)
    record_test("T06: corrSum always odd for k=3 (P1)", ok)

    # T07: 3 never divides corrSum (P2) for k=3
    ok = all(corrSum_of_A(A, 3) % 3 != 0 for A in all_A)
    record_test("T07: 3 never divides corrSum for k=3 (P2)", ok)

    # T08: modinv correctness
    ok = True
    for p in [5, 7, 11, 13, 47]:
        for a in range(1, p):
            inv = modinv(a, p)
            if (a * inv) % p != 1:
                ok = False
    record_test("T08: modinv correct for small primes", ok)

    # T09: multiplicative_order correctness
    ok = (multiplicative_order(2, 7) == 3 and multiplicative_order(2, 5) == 4
          and multiplicative_order(3, 7) == 6)
    record_test("T09: multiplicative_order correct", ok,
                f"ord_7(2)={multiplicative_order(2,7)}, ord_5(2)={multiplicative_order(2,5)}, "
                f"ord_7(3)={multiplicative_order(3,7)}")

    # T10: factorization correctness
    ok = (full_factor(12) == [(2, 2), (3, 1)]
          and full_factor(47) == [(47, 1)]
          and set(p for p, _ in full_factor(2**5 - 3**3)) == {5})
    record_test("T10: factorization correct", ok)

    # T11: 2^S = 3^k mod p for all prime p | d
    ok = True
    for k in range(3, 16):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 1:
            continue
        for p in prime_factors_list(d):
            if pow(2, S, p) != pow(3, k, p):
                ok = False
    record_test("T11: 2^S = 3^k mod p for all p | d, k=3..15", ok)

    # T12: sigma = corrSum / 3^{k-1} mod p
    ok = True
    for k in [3, 4, 5]:
        d = compute_d(k)
        for p in prime_factors_list(d):
            inv3k1 = modinv(pow(3, k - 1, p), p)
            if inv3k1 is None:
                ok = False
                continue
            for A in enumerate_all_compositions(k):
                cs = corrSum_of_A(A, k) % p
                sig = compute_normalized_sigma(A, k, p)
                expected = (cs * inv3k1) % p
                if sig != expected:
                    ok = False
    record_test("T12: sigma = corrSum * inv(3^{k-1}) mod p, k=3..5", ok)

    # T13: g-form sigma matches direct sigma
    ok = True
    for k in [3, 4, 5]:
        d = compute_d(k)
        for p in prime_factors_list(d):
            for A in enumerate_all_compositions(k):
                sig1 = compute_normalized_sigma(A, k, p)
                sig2 = compute_sigma_g_form(A, k, p)
                if sig1 != sig2:
                    ok = False
    record_test("T13: sigma g-form matches direct form, k=3..5", ok)

    # T14: N0(d) = 0 for k=3..10 (the fundamental no-cycle property)
    ok = True
    for k in range(3, 11):
        d = compute_d(k)
        C = compute_C(k)
        if d <= 0 or C > 500_000:
            continue
        n0 = 0
        for A in enumerate_all_compositions(k):
            if corrSum_of_A(A, k) % d == 0:
                n0 += 1
        if n0 != 0:
            ok = False
    record_test("T14: N0(d) = 0 for k=3..10", ok)

    # T15: g = 2 * 3^{-1} mod p is well-defined and g * 3 = 2 mod p
    ok = True
    for k in [3, 5, 7, 10]:
        d = compute_d(k)
        for p in prime_factors_list(d):
            inv3 = modinv(3, p)
            g = (2 * inv3) % p
            if (g * 3) % p != 2 % p:
                ok = False
    record_test("T15: g*3 = 2 mod p for g = 2*3^{-1}", ok)

    # T16: Constraint g^S = 3^{k-S} mod p verified
    ok = True
    for k in [3, 4, 5, 6, 7, 8]:
        S = compute_S(k)
        d = compute_d(k)
        for p in prime_factors_list(d):
            inv3 = modinv(3, p)
            g = (2 * inv3) % p
            gS = pow(g, S, p)
            # 3^{k-S} with k < S, so this is 3^{negative} = inv(3)^{S-k}
            expected = pow(inv3, S - k, p)
            if gS != expected:
                ok = False
    record_test("T16: g^S = 3^{k-S} mod p constraint holds, k=3..8", ok)

    # T17: ord(g) divides lcm(ord(2), ord(3))
    ok = True
    for k in [3, 4, 5, 6, 7]:
        d = compute_d(k)
        for p in prime_factors_list(d):
            inv3 = modinv(3, p)
            g = (2 * inv3) % p
            og = multiplicative_order(g, p)
            o2 = multiplicative_order(2, p)
            o3 = multiplicative_order(3, p)
            lcm_23 = (o2 * o3) // math.gcd(o2, o3)
            if lcm_23 % og != 0:
                ok = False
    record_test("T17: ord(g) | lcm(ord(2), ord(3)), k=3..7", ok)

    # T18: P1 (oddness) holds for k=3..12
    ok = True
    for k in range(3, 13):
        C = compute_C(k)
        if C > 500_000:
            continue
        for A in enumerate_all_compositions(k):
            if corrSum_of_A(A, k) % 2 != 1:
                ok = False
                break
    record_test("T18: corrSum always odd for k=3..12 (P1)", ok)

    # T19: P2 (not div by 3) holds for k=3..12
    ok = True
    for k in range(3, 13):
        C = compute_C(k)
        if C > 500_000:
            continue
        for A in enumerate_all_compositions(k):
            if corrSum_of_A(A, k) % 3 == 0:
                ok = False
                break
    record_test("T19: 3 never divides corrSum for k=3..12 (P2)", ok)

    # T20: corrsum_mod matches corrSum_of_A mod p
    ok = True
    for k in [3, 4, 5, 6]:
        S = compute_S(k)
        d = compute_d(k)
        primes = prime_factors_list(d)
        for p in primes:
            for B in combinations(range(1, S), k - 1):
                A = (0,) + B
                cs_true = corrSum_of_A(A, k) % p
                cs_mod = corrsum_mod(B, k, p)
                if cs_true != cs_mod:
                    ok = False
    record_test("T20: corrsum_mod matches corrSum_of_A mod p, k=3..6", ok)

    # T21: d is always odd and not divisible by 3
    ok = True
    for k in range(3, 30):
        d = compute_d(k)
        if d <= 0:
            continue
        if d % 2 == 0 or d % 3 == 0:
            ok = False
    record_test("T21: d is always odd and coprime to 3, k=3..29", ok)

    # T22: Gaps B_j = A_j - j are weakly increasing and non-negative
    ok = True
    for k in [3, 4, 5, 6, 7]:
        for A in enumerate_all_compositions(k):
            gaps = [A[j] - j for j in range(k)]
            if gaps[0] != 0:
                ok = False
            for i in range(1, len(gaps)):
                if gaps[i] < gaps[i - 1]:
                    ok = False
    record_test("T22: Gaps B_j = A_j - j weakly increasing, k=3..7", ok)

    # T23: sigma(A) = 0 mod p iff corrSum(A) = 0 mod p
    ok = True
    for k in [3, 4, 5]:
        d = compute_d(k)
        for p in prime_factors_list(d):
            for A in enumerate_all_compositions(k):
                cs_zero = (corrSum_of_A(A, k) % p == 0)
                sig_zero = (compute_normalized_sigma(A, k, p) == 0)
                if cs_zero != sig_zero:
                    ok = False
    record_test("T23: sigma=0 iff corrSum=0 mod p, k=3..5", ok)

    # T24: N0(p) computation via get_residue_distribution matches direct count
    ok = True
    for k in [3, 4, 5, 6]:
        d = compute_d(k)
        for p in prime_factors_list(d):
            # Direct count
            direct_n0 = 0
            for A in enumerate_all_compositions(k):
                if corrSum_of_A(A, k) % p == 0:
                    direct_n0 += 1
            # Via distribution
            dist = get_residue_distribution(k, p)
            dist_n0 = dist.get(0, 0)
            if direct_n0 != dist_n0:
                ok = False
    record_test("T24: N0 via distribution matches direct count, k=3..6", ok)

    # T25: For k=3 (d=5, prime), verify N0(5) = 0 exactly
    k = 3
    d = compute_d(k)  # d = 5
    n0 = 0
    all_corrsums = []
    for A in enumerate_all_compositions(k):
        cs = corrSum_of_A(A, k)
        all_corrsums.append(cs)
        if cs % d == 0:
            n0 += 1
    ok = (d == 5 and n0 == 0)
    record_test("T25: k=3, d=5: N0(5) = 0", ok,
                f"d={d}, corrSums={all_corrsums}, corrSums mod 5={[c%5 for c in all_corrsums]}")

    # T26: geometric sum formula: sum_{j=0}^{k-1} g^j = (g^k - 1)/(g - 1) mod p
    ok = True
    for k_test in [3, 5, 7]:
        d = compute_d(k_test)
        for p in prime_factors_list(d):
            inv3 = modinv(3, p)
            g = (2 * inv3) % p
            # Direct sum
            direct = sum(pow(g, j, p) for j in range(k_test)) % p
            # Formula
            if g % p == 1:
                formula = k_test % p
            else:
                formula = ((pow(g, k_test, p) - 1) * modinv(g - 1, p)) % p
            if direct != formula:
                ok = False
    record_test("T26: geometric sum formula verified, k=3,5,7", ok)

    # T27: The "gap representation" sigma = sum g^j * 2^{B_j} matches
    ok = True
    for k_test in [3, 4, 5]:
        d = compute_d(k_test)
        for p in prime_factors_list(d):
            inv3 = modinv(3, p)
            g = (2 * inv3) % p
            for A in enumerate_all_compositions(k_test):
                gaps = [A[j] - j for j in range(k_test)]
                # sigma via gaps
                sig_gap = sum(pow(g, j, p) * pow(2, gaps[j], p) for j in range(k_test)) % p
                # sigma via direct
                sig_direct = compute_sigma_g_form(A, k_test, p)
                if sig_gap != sig_direct:
                    ok = False
    record_test("T27: gap representation sigma = sum g^j * 2^{B_j}, k=3..5", ok)

    # T28: When p > C, image size <= C (pigeonhole)
    ok = True
    for k_test in [3, 4, 5]:
        d = compute_d(k_test)
        C = compute_C(k_test)
        for p in prime_factors_list(d):
            if p > C:
                dist = get_residue_distribution(k_test, p)
                if dist and len(dist) > C:
                    ok = False
    record_test("T28: When p > C, |image| <= C (pigeonhole)", ok)

    # T29: corrSum(A) for the "minimal" composition A=(0,1,...,k-1)
    # This is: sum_{j=0}^{k-1} 3^{k-1-j} * 2^j = sum_{j=0}^{k-1} 3^{k-1-j} * 2^j
    # = (3^k - 2^k) / (3 - 2) = 3^k - 2^k  (geometric series)
    ok = True
    for k_test in [3, 4, 5, 6, 7, 8]:
        A_min = tuple(range(k_test))
        cs = corrSum_of_A(A_min, k_test)
        expected = 3**k_test - 2**k_test
        if cs != expected:
            ok = False
    record_test("T29: corrSum((0,1,...,k-1)) = 3^k - 2^k", ok)

    # T30: corrSum(A) for the "maximal" composition A=(0, S-k+1, ..., S-1)
    # = 3^{k-1} * 1 + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{S-k+j}
    ok = True
    for k_test in [3, 4, 5]:
        S = compute_S(k_test)
        A_max = (0,) + tuple(range(S - k_test + 1, S))
        cs = corrSum_of_A(A_max, k_test)
        # Verify by direct computation
        expected = pow(3, k_test - 1)
        for j in range(1, k_test):
            expected += pow(3, k_test - 1 - j) * pow(2, S - k_test + j)
        if cs != expected:
            ok = False
    record_test("T30: corrSum for maximal composition matches direct calc", ok)

    # Summary
    n_pass = sum(1 for _, p, _ in TEST_RESULTS if p)
    n_total = len(TEST_RESULTS)
    print(f"\n  TOTAL: {n_pass}/{n_total} PASS")
    if n_pass < n_total:
        print("  FAILURES:")
        for name, passed, detail in TEST_RESULTS:
            if not passed:
                print(f"    FAIL: {name} -- {detail}")
    return n_pass == n_total


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 72)
    print("R12: ALGEBRAIC CONSTRAINT 2^S = 3^k mod p FOR N_0(p) = 0")
    print("=" * 72)
    print(f"  Time budget: {TIME_BUDGET:.0f}s")
    print()

    # Run self-tests first
    tests_ok = run_self_tests()
    if not tests_ok:
        print("\n*** SELF-TESTS FAILED -- stopping ***")
        sys.exit(1)

    print(f"\n  All {len(TEST_RESULTS)} self-tests PASSED. Proceeding to analysis.\n")

    # Part 1: Algebraic structure
    if time_remaining() > 40:
        part1_algebraic_structure(k_max=12)

    # Part 2: Polynomial zeros
    if time_remaining() > 40:
        part2_polynomial_zeros(k_max=10)

    # Part 3: Congruence lattice
    if time_remaining() > 40:
        part3_congruence_lattice(k_max=14)

    # Part 4: Distinctness
    if time_remaining() > 30:
        part4_distinctness(k_max=12)

    # Part 5: Valuation obstructions
    if time_remaining() > 30:
        part5_valuation_obstructions(k_max=15)

    # Part 6: Exhaustive
    if time_remaining() > 30:
        part6_exhaustive(k_max=14)

    # ========================================================================
    # FINAL SYNTHESIS
    # ========================================================================
    print("\n" + "=" * 72)
    print("FINAL SYNTHESIS")
    print("=" * 72)

    print("""
PROVEN FACTS:
  (P1) corrSum(A) is always ODD.
       Proof: j=0 term is 3^{k-1} (odd); all j>=1 terms have 2^{A_j>=1} (even).
  (P2) 3 never divides corrSum(A).
       Proof: corrSum mod 3 = 2^{A_{k-1}} mod 3, which is 1 or 2, never 0.
  (P3) corrSum(A) > 0 always (all terms positive).
  (P4) The algebraic identity sigma(A) = sum_{j=0}^{k-1} g^j * 2^{B_j} mod p
       where g = 2*3^{-1}, B_j = A_j - j (weakly increasing gaps) is verified.
  (P5) The constraint g^S = 3^{k-S} mod p holds for all p | d (from 2^S = 3^k mod p).
  (P6) ord(g) always divides lcm(ord_p(2), ord_p(3)).
  (P7) corrSum((0,1,...,k-1)) = 3^k - 2^k exactly (geometric series).

STRUCTURAL OBSERVATIONS:
  - When p > C(k): the image {corrSum mod p} has at most C elements in Z/pZ.
    If N0(p) = 0, then 0 is among the p - C >= p - C missed residues.
  - The g-form representation sigma = sum g^j * 2^{B_j} shows corrSum as
    a sum of terms from a structured subset of F_p^*.
  - The gap structure B_j (weakly increasing) constrains which terms appear.
  - P1+P2 together obstruct 2 and 3 from dividing corrSum.
    No other prime universally obstructs corrSum.
""")

    print(f"\n  Total runtime: {elapsed():.1f}s")
    print(f"  Self-tests: {sum(1 for _, p, _ in TEST_RESULTS if p)}/{len(TEST_RESULTS)} PASS")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "selftest":
        run_self_tests()
    else:
        main()
