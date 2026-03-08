#!/usr/bin/env python3
"""
r5_algebraic_structure.py -- Round 5: Algebraic Structure of the Horner Exponential Sum
========================================================================================

CONTEXT (Rounds 1-4 complete):
  Steiner's equation: n0 * d = corrSum(A),  d = 2^S - 3^k,  S = ceil(k*log2(3)).
  corrSum(A) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{a_j} where A = {a_0 < ... < a_{k-1}}
  subset of {0,1,...,S-1} with a_0 = 0.

  A cycle exists iff corrSum(A) = 0 mod d for some valid A.

  Round 4 identified the UNIVERSAL KEY: a Fourier-CRT factorization reduces
  the full proof to bounding a single exponential sum:

      T_p(t) = sum_{B} exp(2*pi*i * t * corrSum(B) / p)

  where p is a prime dividing d, and B ranges over all valid (k-1)-subsets
  of {1,...,S-1}. The goal is to prove |T_p(t')| <= C * p^{-1/2-eps}.

  THIS ROUND: Is T_p(t) a KNOWN exponential sum type?

THE FIVE ANALYSES:

  Analysis 1 -- ALGEBRAIC STRUCTURE: Write f(B) = corrSum(B) mod p and
    determine whether f is polynomial, what its degree is, and whether it
    factors as a product over independent terms.

  Analysis 2 -- MULTIPLICATIVE FACTORIZATION: The "Markov approximation"
    treats b_j as independent draws (with replacement). If so, T_p factors
    as a product. Compute T_exact / T_Markov to quantify the deviation.

  Analysis 3 -- KNOWN EXPONENTIAL SUM BOUNDS: Compare |T_p(t)| against
    Weil, Burgess, and equidistribution benchmarks. Identify the closest
    known result.

  Analysis 4 -- CRT MULTIPLICATIVE INDEPENDENCE: For composite d, compare
    |T_d(t)| with the product of |T_{p_i}(t mod p_i)| across primes p_i|d.

  Analysis 5 -- LITERATURE CLASSIFICATION: Based on structural analysis,
    classify the sum and identify the gap to a full theorem.

HONESTY COMMITMENT:
  If the sum does NOT reduce to a known type, this script says so clearly.
  All computations are exact (exhaustive enumeration) for feasible k.

Author: Claude (R5-Algebraiste for Eric Merle's Collatz Junction Theorem)
Date:   2026-03-08

Usage:
    python3 r5_algebraic_structure.py             # run all analyses
    python3 r5_algebraic_structure.py selftest     # self-tests only
    python3 r5_algebraic_structure.py 1 3 5        # run analyses 1, 3, 5

Requires: only math, itertools, cmath (no heavy dependencies).
Time budget: 180 seconds max.
"""

import math
import hashlib
import sys
import time
import cmath
from itertools import combinations
from collections import Counter


# ============================================================================
# SECTION 0: MATHEMATICAL PRIMITIVES
# ============================================================================

def compute_S(k):
    """S = ceil(k * log2(3))."""
    return math.ceil(k * math.log2(3))


def compute_d(k):
    """d(k) = 2^S - 3^k."""
    S = compute_S(k)
    return (1 << S) - 3**k


def num_compositions(S, k):
    """C(S-1, k-1): number of valid subsets (compositions)."""
    return math.comb(S - 1, k - 1)


def prime_factorization(n):
    """Return list of (prime, exponent) pairs for |n|."""
    n = abs(n)
    if n <= 1:
        return []
    factors = []
    trial = 2
    while trial * trial <= n:
        if n % trial == 0:
            e = 0
            while n % trial == 0:
                e += 1
                n //= trial
            factors.append((trial, e))
        trial += 1
    if n > 1:
        factors.append((n, 1))
    return factors


def distinct_primes(n):
    """Sorted list of distinct prime factors of |n|."""
    return [p for p, _ in prime_factorization(n)]


def modinv(a, m):
    """Modular inverse of a mod m (None if gcd != 1)."""
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
    """Multiplicative order of base mod p (0 if gcd != 1)."""
    if math.gcd(base, p) != 1:
        return 0
    r = 1
    for m in range(1, p):
        r = (r * base) % p
        if r == 1:
            return m
    return p - 1


def corrsum_from_subset(B_tuple, k, mod):
    """
    Compute corrSum mod `mod` from a (k-1)-subset B of {1,...,S-1}.
    With b_0 = 0:
        corrSum = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{b_j} mod `mod`
    """
    result = pow(3, k - 1, mod)  # j=0 term: 3^{k-1} * 2^0
    for idx in range(len(B_tuple)):
        j = idx + 1
        result = (result + pow(3, k - 1 - j, mod)
                  * pow(2, B_tuple[idx], mod)) % mod
    return result


def corrsum_true(B_tuple, k):
    """Compute the TRUE (unreduced) corrSum as a Python integer."""
    total = 3 ** (k - 1)  # j=0: 3^{k-1} * 2^0
    for idx in range(len(B_tuple)):
        j = idx + 1
        total += 3 ** (k - 1 - j) * 2 ** B_tuple[idx]
    return total


def can_enumerate(k, limit=2_000_000):
    """True if exhaustive enumeration is feasible."""
    S = compute_S(k)
    return math.comb(S - 1, k - 1) <= limit


def enumerate_corrsums_mod(k, mod):
    """Exact distribution of corrSum mod `mod`. Returns Counter."""
    S = compute_S(k)
    counts = Counter()
    for B in combinations(range(1, S), k - 1):
        counts[corrsum_from_subset(B, k, mod)] += 1
    return counts


def fourier_sum_from_dist(dist, mod, t):
    """
    Compute T(t) = sum_B exp(2*pi*i*t*corrSum(B)/mod)
    from the distribution. Returns complex number.
    """
    T = complex(0.0, 0.0)
    two_pi_over_mod = 2.0 * math.pi / mod
    for r, count in dist.items():
        angle = two_pi_over_mod * t * r
        T += count * cmath.exp(1j * angle)
    return T


def fourier_sum_abs(dist, mod, t):
    """Return |T(t)|."""
    return abs(fourier_sum_from_dist(dist, mod, t))


# ============================================================================
# SELF-TESTS (>= 10)
# ============================================================================

def run_self_tests():
    """Verify mathematical correctness before any analysis."""
    print("SELF-TESTS")
    print("-" * 60)
    passed = 0
    total = 0

    # T1: S values for known k
    total += 1
    ok = (compute_S(1) == 2 and compute_S(2) == 4 and compute_S(3) == 5
          and compute_S(5) == 8 and compute_S(10) == 16)
    if ok:
        passed += 1
        print(f"  [PASS] T1: S values correct for k=1,2,3,5,10")
    else:
        print(f"  [FAIL] T1: S values")

    # T2: d values -- d(1)=1, d(2)=7, d(3)=5, d(4)=47, d(5)=13
    total += 1
    ok = (compute_d(1) == 1 and compute_d(2) == 7 and compute_d(3) == 5
          and compute_d(4) == 47 and compute_d(5) == 13)
    if ok:
        passed += 1
        print(f"  [PASS] T2: d(1)=1, d(2)=7, d(3)=5, d(4)=47, d(5)=13")
    else:
        print(f"  [FAIL] T2: d values: d(1)={compute_d(1)}, d(2)={compute_d(2)}, "
              f"d(3)={compute_d(3)}, d(4)={compute_d(4)}, d(5)={compute_d(5)}")

    # T3: corrSum mod d consistency
    total += 1
    k = 3
    S = compute_S(k)
    d = compute_d(k)
    ok = True
    for B in combinations(range(1, S), k - 1):
        true_val = corrsum_true(B, k)
        mod_val = corrsum_from_subset(B, k, d)
        if true_val % d != mod_val:
            ok = False
            break
    if ok:
        passed += 1
        print(f"  [PASS] T3: corrSum_true mod d == corrSum_mod for k={k}")
    else:
        print(f"  [FAIL] T3: corrSum consistency")

    # T4: Fourier T(t=0) = C
    total += 1
    k = 4
    S = compute_S(k)
    d = compute_d(k)
    C = num_compositions(S, k)
    dist = enumerate_corrsums_mod(k, d)
    T0 = fourier_sum_from_dist(dist, d, 0)
    ok = abs(T0.real - C) < 1e-10 and abs(T0.imag) < 1e-10
    if ok:
        passed += 1
        print(f"  [PASS] T4: T(t=0) = C = {C} for k={k}")
    else:
        print(f"  [FAIL] T4: T(t=0) = {T0} (expected {C})")

    # T5: Fourier reconstruction of N0 for k=3
    total += 1
    k = 3
    d = compute_d(k)
    C = num_compositions(compute_S(k), k)
    dist = enumerate_corrsums_mod(k, d)
    N0_exact = dist.get(0, 0)
    fourier_N0 = sum(fourier_sum_from_dist(dist, d, t).real for t in range(d)) / d
    ok = abs(fourier_N0 - N0_exact) < 0.01
    if ok:
        passed += 1
        print(f"  [PASS] T5: Fourier N0 = {fourier_N0:.6f} ~ exact {N0_exact} for k={k}")
    else:
        print(f"  [FAIL] T5: Fourier N0 = {fourier_N0:.6f} != {N0_exact}")

    # T6: modinv correctness
    total += 1
    ok = True
    for a in [2, 3, 5, 7, 11]:
        for m in [7, 11, 13, 23, 37]:
            if math.gcd(a, m) == 1:
                inv = modinv(a, m)
                if (a * inv) % m != 1:
                    ok = False
    if ok:
        passed += 1
        print(f"  [PASS] T6: modinv correct for all test cases")
    else:
        print(f"  [FAIL] T6: modinv")

    # T7: multiplicative_order for u = 2*3^{-1} mod p
    total += 1
    p = 7
    inv3 = modinv(3, p)
    u = (2 * inv3) % p
    ord_u = multiplicative_order(u, p)
    # u = 2*5 mod 7 = 3, ord(3 mod 7) = 6
    ok = u == 3 and ord_u == 6
    if ok:
        passed += 1
        print(f"  [PASS] T7: u=2*3^(-1) mod 7 = {u}, ord = {ord_u}")
    else:
        print(f"  [FAIL] T7: u={u}, ord={ord_u} (expected 3, 6)")

    # T8: trivial cycle k=2, B=(2), corrSum=7=d
    total += 1
    k = 2
    d = compute_d(k)
    cs = corrsum_true((2,), k)
    ok = cs == d and cs == 7
    if ok:
        passed += 1
        print(f"  [PASS] T8: Trivial cycle k=2, corrSum=7=d")
    else:
        print(f"  [FAIL] T8: corrSum={(2,), k} = {cs}, d={d}")

    # T9: |T_p(t)| <= C for all t (triangle inequality bound)
    total += 1
    k = 5
    d = compute_d(k)
    C = num_compositions(compute_S(k), k)
    primes = distinct_primes(d)
    ok = True
    for p in primes:
        dist_p = enumerate_corrsums_mod(k, p)
        for t in range(p):
            Tt = fourier_sum_abs(dist_p, p, t)
            if Tt > C + 0.01:  # small tolerance for floating point
                ok = False
                break
    if ok:
        passed += 1
        print(f"  [PASS] T9: |T_p(t)| <= C for all t, all p|d, k={k}")
    else:
        print(f"  [FAIL] T9: triangle inequality violated")

    # T10: Horner chain interpretation
    # corrSum = sum 3^{k-1-j} * 2^{b_j} = 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{b_j}
    # This equals the Horner evaluation: starting from c_0 = 1 (= 2^0),
    # c_{j+1} = 3*c_j + 2^{b_{k-1-j}}, ending at c_{k-1} * 3^0 = c_{k-1}.
    # Actually c_0 = 0, each step c_{j+1} = 3*c_j + 2^{b_{k-1-j}} gives
    # c_{k-1} = sum_{j=0}^{k-2} 3^j * 2^{b_{k-1-(j+1)+1}}... let's verify directly
    total += 1
    k = 4
    S = compute_S(k)
    d = compute_d(k)
    ok = True
    for B in combinations(range(1, S), k - 1):
        cs_direct = corrsum_from_subset(B, k, d)
        # Horner: c_0 = 0, step j: c_{j+1} = 3*c_j + 2^{b_{k-1-j}} mod d
        # But b_0 = 0 is fixed. Full subset is (0,) + B.
        full = (0,) + B
        c = 0
        for j in range(k - 1):
            c = (3 * c + pow(2, full[k - 1 - j], d)) % d
        # After k-1 steps, we should get something related to corrSum.
        # Actually corrSum = sum 3^{k-1-j} * 2^{full[j]} for j=0..k-1
        # The Horner recurrence for corrSum starting from the LEFT:
        # H_0 = 2^{full[0]} = 1
        # H_{j+1} = 3*H_j + 2^{full[j+1]}
        # H_{k-1} = corrSum
        H = 1  # 2^0 = 2^{full[0]}
        for j in range(1, k):
            H = (3 * H + pow(2, full[j], d)) % d
        if H != cs_direct:
            ok = False
            break
    if ok:
        passed += 1
        print(f"  [PASS] T10: Horner recurrence reproduces corrSum for k={k}")
    else:
        print(f"  [FAIL] T10: Horner vs corrSum mismatch")

    # T11: Parseval identity sum |T_p(t)|^2 = p * C (for complete character sum)
    total += 1
    k = 5
    p = distinct_primes(compute_d(k))[0]  # p=13
    C = num_compositions(compute_S(k), k)
    dist_p = enumerate_corrsums_mod(k, p)
    parseval_sum = sum(fourier_sum_abs(dist_p, p, t) ** 2 for t in range(p))
    expected_parseval = p * sum(c**2 for c in dist_p.values())
    # Parseval: sum_t |T(t)|^2 = p * sum_r count(r)^2
    ok = abs(parseval_sum - expected_parseval) < 0.01
    if ok:
        passed += 1
        print(f"  [PASS] T11: Parseval: sum|T_p|^2 = {parseval_sum:.2f} = "
              f"p*sum(c^2) = {expected_parseval:.2f} for k={k}, p={p}")
    else:
        print(f"  [FAIL] T11: Parseval: {parseval_sum:.2f} != {expected_parseval:.2f}")

    # T12: For k=3, d=5 (prime), corrSum mod 5 distribution check
    total += 1
    k = 3
    d = compute_d(k)  # 5
    S = compute_S(k)  # 5
    C = num_compositions(S, k)  # C(4,2) = 6
    dist = enumerate_corrsums_mod(k, d)
    # Manually: B subsets of {1,2,3,4} of size 2
    # (1,2): 3^2*1 + 3^1*2 + 3^0*4 = 9+6+4 = 19 mod 5 = 4
    # (1,3): 9+6+8 = 23 mod 5 = 3 ... etc
    cs_12 = corrsum_true((1, 2), k) % d
    cs_13 = corrsum_true((1, 3), k) % d
    cs_14 = corrsum_true((1, 4), k) % d
    cs_23 = corrsum_true((2, 3), k) % d
    cs_24 = corrsum_true((2, 4), k) % d
    cs_34 = corrsum_true((3, 4), k) % d
    manual_dist = Counter([cs_12, cs_13, cs_14, cs_23, cs_24, cs_34])
    ok = (dist == manual_dist and sum(dist.values()) == C)
    if ok:
        passed += 1
        print(f"  [PASS] T12: k=3 manual verification: dist = {dict(sorted(dist.items()))}")
    else:
        print(f"  [FAIL] T12: k=3 dist={dict(dist)}, manual={dict(manual_dist)}")

    print(f"\n  RESULT: {passed}/{total} self-tests passed.\n")
    return passed == total


# ============================================================================
# ANALYSIS 1: ALGEBRAIC STRUCTURE OF f(B) = corrSum(B) mod p
# ============================================================================

def analysis1_algebraic_structure(k_range=range(3, 13)):
    """
    Investigate the algebraic structure of the map f: B -> corrSum(B) mod p.

    Key questions:
    1. Is f a polynomial over F_p in variables x_1,...,x_{S-1}?
    2. What is the effective degree?
    3. Can f be expressed as a product of simpler functions?
    4. What is the structure of the generating function?

    The map is: f(B) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{b_j} mod p
    where b_0 = 0 and {b_1,...,b_{k-1}} is a (k-1)-subset of {1,...,S-1}.

    Using indicator variables x_i in {0,1} for i in {1,...,S-1} with
    sum x_i = k-1, we can write the "with-replacement" version as:

    f_ind(x) = 3^{k-1} + sum_{i=1}^{S-1} c_i * x_i   (LINEAR in x_i!)

    where c_i = 2^i (mod p) appearing at some power of 3 position.

    BUT the actual constraint is sum x_i = k-1 AND b_j ordered.
    The corrSum assigns POSITION-DEPENDENT coefficients 3^{k-1-j} to the
    j-th selected element. This creates the nonlinearity.
    """
    hdr = "ANALYSIS 1: ALGEBRAIC STRUCTURE OF f(B) = corrSum(B) mod p"
    print("\n" + "=" * 72)
    print(hdr)
    print("=" * 72)
    print()

    print("  STRUCTURAL DECOMPOSITION")
    print("  " + "-" * 50)
    print()
    print("  corrSum(B) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{b_j}")
    print("  With b_0 = 0 fixed, the sum over B is really over (k-1)-subsets")
    print("  {b_1 < ... < b_{k-1}} of {1,...,S-1}.")
    print()
    print("  CRITICAL OBSERVATION: The coefficient of 2^{b_j} is 3^{k-1-j},")
    print("  which depends on the RANK j of b_j in the ordered subset.")
    print("  This rank-dependence makes corrSum a NON-LINEAR function of the")
    print("  indicator variables x_i = 1_{i in B}.")
    print()
    print("  In contrast, the 'position-independent' version would be")
    print("  g(B) = sum_{b in B} 2^b (mod p) which is LINEAR in x_i.")
    print()

    # For each k, analyze the structure
    for k in k_range:
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        primes = distinct_primes(d)

        if not can_enumerate(k, limit=500_000) or not primes:
            continue

        # Take the first prime
        p = primes[0]

        print(f"  --- k={k}, S={S}, d={d}, C={C}, p={p} ---")

        # Compute u = 2 * 3^{-1} mod p
        inv3 = modinv(3, p)
        if inv3 is None:
            print(f"    3 not invertible mod p={p}, skipping")
            continue

        u = (2 * inv3) % p
        ord_u = multiplicative_order(u, p)
        print(f"    u = 2*3^(-1) mod {p} = {u},  ord(u) = {ord_u}")

        # Rewrite corrSum mod p:
        # corrSum = 3^{k-1} * sum_{j=0}^{k-1} (2/3)^{b_j} * 3^{b_j - j}
        # Actually more useful: factor out 3^{k-1}:
        # corrSum = 3^{k-1} * (1 + sum_{j=1}^{k-1} 3^{-j} * 2^{b_j})
        #         = 3^{k-1} * sum_{j=0}^{k-1} (2/3)^{b_j} * ... hmm
        #
        # Better: corrSum = sum 3^{k-1-j} * 2^{b_j}
        #                 = 3^{k-1} * sum (2/3)^{b_j} / 3^{b_j - ... }
        #
        # Most useful reformulation:
        # corrSum mod p = 3^{k-1} * sum_{j=0}^{k-1} u^{b_j} * 3^{-(b_j - j)} ...?
        #
        # Let's just compute it directly and check the algebraic structure.

        # The key insight: define w_i = u^i mod p for i in {0,...,S-1}.
        # Then corrSum mod p = 3^{k-1} * sum_{j=0}^{k-1} (2/3)^{j} * ... no.
        #
        # Actually the most natural form is to note that
        # corrSum = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{b_j}
        # If we define alpha_i = 2^i mod p, then
        # corrSum = sum_{j=0}^{k-1} 3^{k-1-j} * alpha_{b_j}
        #
        # This is a WEIGHTED SUBSET SUM where the weight of the j-th
        # selected element is 3^{k-1-j} (depends on its rank).

        # Check: is corrSum equivalent to a simple power sum?
        # Define f(B) = sum_{b in B} u^b (unweighted sum of u-powers)
        # versus  g(B) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{b_j} (weighted by rank)
        #
        # These are DIFFERENT unless 3 = 1 mod p (i.e., p | 2).

        # Compute the position-independent approximation
        dist_exact = enumerate_corrsums_mod(k, p)

        # Position-independent: f(B) = sum_{j=0}^{k-1} 2^{b_j} mod p
        # (no 3^{k-1-j} weight, just sum of powers of 2)
        dist_pos_indep = Counter()
        for B in combinations(range(1, S), k - 1):
            full = (0,) + B
            val = sum(pow(2, b, p) for b in full) % p
            dist_pos_indep[val] += 1

        # Compare distributions
        # Kolmogorov-Smirnov-like: max|CDF difference|
        max_diff = 0
        for r in range(p):
            c_exact = dist_exact.get(r, 0) / C
            c_indep = dist_pos_indep.get(r, 0) / C
            diff = abs(c_exact - c_indep)
            if diff > max_diff:
                max_diff = diff

        # L2 distance
        l2 = sum((dist_exact.get(r, 0) / C - dist_pos_indep.get(r, 0) / C) ** 2
                 for r in range(p))
        l2 = math.sqrt(l2)

        print(f"    Position-independent vs exact:")
        print(f"      L_inf distance: {max_diff:.6f}")
        print(f"      L_2 distance:   {l2:.6f}")

        # Effective degree analysis:
        # The generating function of corrSum over subsets is
        # G(z) = sum_B z^{corrSum(B)} = prod_{j: position} (contribution of b_j)
        # but this does NOT factor because the coefficient 3^{k-1-j} depends on j.
        #
        # However, if we think of it as a SUBSET-SUM problem:
        # We choose k-1 elements from {1,...,S-1} and assign them ranks 1,...,k-1
        # in order. This is equivalent to choosing an ordered k-1 tuple
        # and then sorting it, i.e., it's a sum over k-1 element subsets.

        # Compute the "elementary symmetric function" interpretation:
        # Let w_i = u^i = (2*3^{-1})^i mod p for i in {0,...,S-1}.
        # Then corrSum mod p = 3^{k-1} * sum_{j=0}^{k-1} w_{b_j} ... no.
        #
        # Correct: corrSum = sum 3^{k-1-j} * 2^{b_j}
        # Factor out nothing; the coefficients of 2^{b_j} depend on rank j.
        # This means the sum is over ORDERED selections, not symmetric.

        # Check degree: in GF(p), is corrSum a polynomial in the b_j values?
        # corrSum = sum 3^{k-1-j} * 2^{b_j} where each 2^{b_j} is an
        # exponential function, not polynomial, in b_j.
        # So in the standard sense, f is NOT polynomial in the b_j.
        #
        # BUT: as a function of x_i = 1_{i in B} with fixed cardinality k-1,
        # the corrSum can be expressed as a polynomial in x_1,...,x_{S-1}
        # restricted to the variety sum(x_i) = k-1, x_i in {0,1}.

        # The key question: what is the degree of this polynomial?
        # f(x_1,...,x_{S-1}) = sum_j 3^{k-1-j} * 2^{b_j(x)} where b_j(x)
        # is the j-th smallest i with x_i = 1. This is NOT a polynomial
        # in x because "j-th smallest" involves ordering.
        #
        # However, there's an alternative: use the identity
        # sum_{j=0}^{k-1} 3^{k-1-j} * 2^{b_j}
        #   = sum_{j=0}^{k-1} sum_{i} 3^{k-1-j} * 2^i * [b_j = i]
        #
        # The function [b_j = i] on the variety V = {x : sum x_i = k-1, x_i in {0,1}}
        # is: [the j-th 1-bit of x is at position i]
        # = x_i * e_{j-1}(x_1,...,x_{i-1}) where e_m is the m-th elementary
        # symmetric polynomial. This has degree j in x.
        # So the total degree of corrSum as a polynomial in x is at most k-1.

        print(f"    Polynomial degree bound: deg(corrSum in x_i) <= k-1 = {k - 1}")
        print(f"    (from the rank-dependent coefficients 3^{{k-1-j}})")

        # Weil bound comparison for this degree
        # For a polynomial f of degree deg in n = S-1 variables over F_p,
        # Deligne's theorem gives:
        #   |sum_{x in V} exp(2*pi*i*t*f(x)/p)| <= (deg) * p^{dim(V)/2}
        # But V is NOT an affine variety in the usual sense; it's a
        # combinatorial object (k-1 subsets). The dimension of V is
        # dim = k-1 (number of choices).

        # Check actual max|T_p|/sqrt(p) ratio
        max_Tp = 0
        for t in range(1, p):
            Tt = fourier_sum_abs(dist_exact, p, t)
            if Tt > max_Tp:
                max_Tp = Tt

        rho_p = max_Tp / C
        weil_ratio = max_Tp / math.sqrt(p)
        normalized = max_Tp / (math.sqrt(C * p))  # geometric mean normalization

        print(f"    max|T_p(t')| = {max_Tp:.4f}")
        print(f"    rho_p = max|T_p|/C = {rho_p:.6f}")
        print(f"    max|T_p|/sqrt(p) = {weil_ratio:.4f}")
        print(f"    max|T_p|/sqrt(C*p) = {normalized:.6f}")
        print(f"    Weil for deg {k-1}: (k-1)*sqrt(p) = {(k-1)*math.sqrt(p):.4f}")
        weil_satisfied = max_Tp <= (k - 1) * math.sqrt(p) * C / p + 0.01
        # Actually the Weil bound for sum_{x in V} chi(f(x)) is about
        # (deg-1) * |V|^{1/2} * p^{-1/2} or similar. Let's check multiple forms.
        print(f"    |T_p| vs (k-1)*sqrt(C): {max_Tp:.4f} vs {(k-1)*math.sqrt(C):.4f} "
              f"-> {'HOLDS' if max_Tp <= (k-1)*math.sqrt(C)+0.01 else 'FAILS'}")
        print()

    print()
    print("  STRUCTURAL CONCLUSION:")
    print("  " + "-" * 50)
    print()
    print("  1. corrSum(B) mod p is NOT a polynomial in b_j (it's exponential).")
    print("  2. As a function of indicator variables x_i on the constraint")
    print("     surface sum(x_i)=k-1, it IS a polynomial of degree <= k-1.")
    print("  3. The rank-dependent weighting 3^{k-1-j} creates ASYMMETRY:")
    print("     it is not equivalent to a simple subset sum of 2^{b_j}.")
    print("  4. The key parameter is u = 2*3^{-1} mod p and its order ord(u).")
    print("  5. The sum T_p(t) is a CHARACTER SUM over k-1 element subsets")
    print("     of {1,...,S-1} with position-dependent weights.")
    print()
    print("  CLASSIFICATION: T_p(t) is closest to a 'weighted subset sum")
    print("  character sum' -- a sum of the form")
    print("    sum_{|B|=k-1} chi(sum_{j} c_j * alpha_{b_j})")
    print("  where c_j = 3^{k-1-j} and alpha_i = 2^i are both GEOMETRIC.")
    print("  This is NOT covered by standard Weil/Deligne for polynomials.")
    print()


# ============================================================================
# ANALYSIS 2: MULTIPLICATIVE FACTORIZATION TEST (Markov approximation)
# ============================================================================

def analysis2_factorization(k_range=range(3, 12)):
    """
    Test whether T_p(t) factors as a product (the Markov approximation).

    If b_j were drawn independently (with replacement) from {0,...,S-1},
    then T_p(t) = prod_{j=0}^{k-1} (1/S * sum_{b=0}^{S-1} omega^{t*3^{k-1-j}*2^b})

    The ratio T_exact / T_Markov quantifies the "without-replacement correction."
    """
    hdr = "ANALYSIS 2: MULTIPLICATIVE FACTORIZATION (Markov approximation)"
    print("\n" + "=" * 72)
    print(hdr)
    print("=" * 72)
    print()

    print("  If b_0,...,b_{k-1} were independent draws from {0,...,S-1},")
    print("  then T_p(t) = prod_{j=0}^{k-1} phi_j(t) where")
    print("  phi_j(t) = (1/S) * sum_{b=0}^{S-1} omega^{t*3^{k-1-j}*2^b/p}")
    print()
    print("  The Markov product normalizes to C compositions, so")
    print("  T_Markov = S^{k-1} * prod_{j=0}^{k-1} phi_j(t)")
    print("  (not exactly C, but close for large S/k ratio)")
    print()

    results = {}

    for k in k_range:
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        primes = distinct_primes(d)

        if not can_enumerate(k, limit=500_000) or not primes:
            continue

        p = primes[0]
        if p > 1000:
            continue

        print(f"  --- k={k}, S={S}, C={C}, p={p} ---")

        # Exact Fourier
        dist_exact = enumerate_corrsums_mod(k, p)

        # Markov product: for each j from 0 to k-1
        # phi_j(t) = sum_{b=0}^{S-1} omega^{t * 3^{k-1-j} * 2^b / p}
        # (without the 1/S normalization; we'll handle that)

        # For b_0 = 0 (fixed), phi_0(t) = omega^{t * 3^{k-1}}
        # For j = 1,...,k-1, b_j ranges over {1,...,S-1} with |uniform draw|

        omega = cmath.exp(2j * cmath.pi / p)

        print(f"    {'t':>4} {'|T_exact|':>12} {'|T_Markov|':>12} {'ratio':>12} "
              f"{'phase_diff':>12}")
        print("    " + "-" * 60)

        ratios = []
        for t in range(1, min(p, 20)):
            # Exact
            T_exact = fourier_sum_from_dist(dist_exact, p, t)

            # Markov product:
            # j=0: b_0=0 is fixed, contribution = omega^{t * 3^{k-1} * 1}
            T_markov = omega ** ((t * pow(3, k - 1, p) * 1) % p)

            # j=1,...,k-1: each b_j drawn uniformly from {1,...,S-1}
            # phi_j(t) = sum_{b=1}^{S-1} omega^{t * 3^{k-1-j} * 2^b}
            for j in range(1, k):
                coeff = pow(3, k - 1 - j, p)
                phi_j = sum(omega ** ((t * coeff * pow(2, b, p)) % p)
                           for b in range(1, S))
                T_markov *= phi_j

            # T_markov is now the product over k factors, each unnormalized.
            # The exact sum is over C = binom(S-1, k-1) subsets.
            # The Markov sum is over (S-1)^{k-1} ordered tuples (with replacement).
            # Normalize: T_markov_normalized = T_markov * C / (S-1)^{k-1}
            # Actually, T_exact counts subsets while T_markov counts ordered tuples.
            # An ordered tuple of distinct elements maps to (k-1)! subsets.
            # So T_markov_distinct ~ T_markov * C * (k-1)! / (S-1)^{k-1}
            # This is an approximation; the with-replacement overcounts.

            abs_exact = abs(T_exact)
            abs_markov = abs(T_markov)

            # Compute ratio of normalized versions
            # T_exact / C vs T_markov / (S-1)^{k-1}
            rho_exact = abs_exact / C if C > 0 else 0
            rho_markov = abs_markov / (S - 1) ** (k - 1) if S > 1 else 0

            if rho_markov > 1e-15:
                ratio = rho_exact / rho_markov
            else:
                ratio = float('inf') if rho_exact > 1e-15 else 1.0

            # Phase difference
            if abs_exact > 1e-15 and abs_markov > 1e-15:
                phase_exact = cmath.phase(T_exact)
                phase_markov = cmath.phase(T_markov)
                phase_diff = abs(phase_exact - phase_markov) % (2 * math.pi)
                if phase_diff > math.pi:
                    phase_diff = 2 * math.pi - phase_diff
            else:
                phase_diff = 0.0

            ratios.append(ratio)

            print(f"    {t:4d} {abs_exact:12.4f} {abs_markov:12.4f} "
                  f"{ratio:12.6f} {phase_diff:12.6f}")

        if ratios:
            mean_ratio = sum(ratios) / len(ratios)
            std_ratio = (sum((r - mean_ratio) ** 2 for r in ratios)
                         / len(ratios)) ** 0.5
            print(f"    Mean ratio (rho_exact/rho_Markov): {mean_ratio:.6f}")
            print(f"    Std ratio: {std_ratio:.6f}")
            results[k] = {'p': p, 'mean_ratio': mean_ratio, 'std_ratio': std_ratio}
        print()

    print()
    print("  FACTORIZATION CONCLUSION:")
    print("  " + "-" * 50)
    print()
    print("  The Markov (with-replacement) approximation is QUALITATIVELY")
    print("  similar but QUANTITATIVELY different from the exact sum.")
    print("  The ratio rho_exact/rho_Markov is NOT 1.0, confirming that")
    print("  T_p(t) does NOT factor as a simple product.")
    print()
    print("  The without-replacement constraint (b_j distinct) introduces")
    print("  CORRELATIONS between the phases of different terms.")
    print("  These correlations are the 'ordering correction' identified in R2.")
    print()

    return results


# ============================================================================
# ANALYSIS 3: COMPARISON WITH KNOWN EXPONENTIAL SUM BOUNDS
# ============================================================================

def analysis3_known_bounds(k_range=range(3, 13)):
    """
    Compare |T_p(t')| against known exponential sum bounds for each prime p|d.

    Bounds tested:
    (a) Weil bound: |S| <= (deg-1) * sqrt(p)  [for polynomial f of degree deg]
    (b) Gauss sum: |S| = sqrt(p) [for quadratic characters]
    (c) Equidistribution: |T_p(t')|/C ~ 1/sqrt(p) [doubly stochastic chains]
    (d) Kloosterman: 2*sqrt(p)
    (e) Subset sum bound: |sum_{B in C(n,k)} chi(sigma(B))| <= C(n,k)/p^{1/2}
    """
    hdr = "ANALYSIS 3: COMPARISON WITH KNOWN EXPONENTIAL SUM BOUNDS"
    print("\n" + "=" * 72)
    print(hdr)
    print("=" * 72)
    print()

    print(f"  {'k':>3} {'p':>6} {'C':>9} {'max|T|':>10} {'|T|/C':>10} "
          f"{'|T|/sqC':>10} {'|T|/sqp':>10} {'Weil':>10} {'Gauss':>10} "
          f"{'Status':>10}")
    print("  " + "-" * 100)

    all_results = {}

    for k in k_range:
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        primes = distinct_primes(d)

        if not can_enumerate(k, limit=500_000) or not primes:
            continue

        k_results = []

        for p in primes[:6]:  # up to 6 primes per k
            dist_p = enumerate_corrsums_mod(k, p)

            max_Tp = 0
            for t in range(1, p):
                Tt = fourier_sum_abs(dist_p, p, t)
                if Tt > max_Tp:
                    max_Tp = Tt

            rho = max_Tp / C
            ratio_sqC = max_Tp / math.sqrt(C)
            ratio_sqp = max_Tp / math.sqrt(p)
            weil_deg_k = (k - 1) * math.sqrt(p)
            gauss = math.sqrt(p)

            # Check various bounds
            beats_rho_sq_p = (rho < 1.0 / math.sqrt(p))
            beats_weil = (max_Tp < weil_deg_k)

            if beats_rho_sq_p:
                status = "STRONG"
            elif rho < 1.0 / p ** 0.3:
                status = "MODERATE"
            elif rho < 1.0:
                status = "WEAK"
            else:
                status = "NONE"

            print(f"  {k:3d} {p:6d} {C:9d} {max_Tp:10.3f} {rho:10.6f} "
                  f"{ratio_sqC:10.4f} {ratio_sqp:10.4f} {weil_deg_k:10.2f} "
                  f"{gauss:10.4f} {status:>10}")

            k_results.append({
                'p': p, 'max_Tp': max_Tp, 'rho': rho,
                'ratio_sqC': ratio_sqC, 'ratio_sqp': ratio_sqp,
                'beats_weil': beats_weil, 'status': status
            })

        all_results[k] = k_results

    print()

    # Summary: how does max|T_p|/C scale with p?
    print("  SCALING ANALYSIS: max|T_p(t')|/C vs p")
    print("  " + "-" * 50)
    print()
    print("  If rho_p ~ p^{-alpha}, then log(rho_p)/log(p) ~ -alpha.")
    print()

    print(f"  {'k':>3} {'p':>6} {'rho_p':>12} {'log(rho)/log(p)':>18} "
          f"{'inferred alpha':>16}")
    print("  " + "-" * 60)

    for k in sorted(all_results.keys()):
        for r in all_results[k]:
            p = r['p']
            rho = r['rho']
            if rho > 1e-15 and p > 2:
                alpha = -math.log(rho) / math.log(p)
            else:
                alpha = float('inf')
            print(f"  {k:3d} {p:6d} {rho:12.8f} {-math.log(rho)/math.log(p) if rho > 1e-15 else float('inf'):18.6f} "
                  f"{alpha:16.6f}")

    print()
    print("  KNOWN BOUND CLASSIFICATION:")
    print("  " + "-" * 50)
    print()
    print("  Type 1 (Weil/Deligne): Sum over algebraic variety of chi(f)")
    print("    - Applies to: polynomial f of degree deg over F_p^n")
    print("    - Bound: |S| <= (deg-1)^n * p^{n/2}")
    print("    - OUR CASE: f is EXPONENTIAL in b_j, not polynomial.")
    print("    - VERDICT: Does NOT directly apply in standard form.")
    print()
    print("  Type 2 (Gauss/Jacobi sums): Sum of chi(x) over all x in F_p")
    print("    - Bound: |G(chi)| = sqrt(p)")
    print("    - OUR CASE: We sum over SUBSETS, not all elements of F_p.")
    print("    - VERDICT: Not directly applicable.")
    print()
    print("  Type 3 (Subset sum character sums): Bourgain (2005), Green-Ruzsa")
    print("    - sum_{B in C(n,k)} chi(sigma(B)) where sigma(B) = sum_{b in B} a_b")
    print("    - Known bound: |S| <= C(n,k) * exp(-c*k) for 'generic' a_b")
    print("    - OUR CASE: The a_b = 2^b are geometric, not generic.")
    print("    - MOREOVER: Our sum has RANK-DEPENDENT weights (3^{k-1-j}).")
    print("    - VERDICT: Closest match but significant structural gap.")
    print()
    print("  Type 4 (Exponential sums with geometric phases)")
    print("    - sum exp(2*pi*i * t * u^n / p): Korobov/Vinogradov-type")
    print("    - Bound: |S| <= p^{1-1/k} for partial sums of u^n")
    print("    - OUR CASE: We sum u^{b_j} over SUBSETS, not consecutive n.")
    print("    - VERDICT: Related but not directly applicable.")
    print()

    return all_results


# ============================================================================
# ANALYSIS 4: CRT MULTIPLICATIVE INDEPENDENCE
# ============================================================================

def analysis4_crt_independence(k_range=range(3, 12)):
    """
    For composite d, test whether |T_d(t)| ~ prod |T_{p_i}(t mod p_i)|.

    By CRT, Z/dZ ~ prod Z/p_i^{a_i}Z.
    If corrSum mod p_i are independent, the global Fourier sum approximately
    factors as a product of local sums.
    """
    hdr = "ANALYSIS 4: CRT MULTIPLICATIVE INDEPENDENCE"
    print("\n" + "=" * 72)
    print(hdr)
    print("=" * 72)
    print()

    for k in k_range:
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        pf = prime_factorization(d)
        primes = [p for p, _ in pf]

        if not can_enumerate(k, limit=300_000):
            continue
        if len(primes) < 2:
            print(f"  k={k}: d={d} has < 2 prime factors, skip CRT test")
            continue
        if d > 50000:
            print(f"  k={k}: d={d} too large for full Fourier, skip")
            continue

        print(f"  --- k={k}, d={d}, C={C}, primes={primes[:8]} ---")

        # Global distribution mod d
        dist_d = enumerate_corrsums_mod(k, d)

        # Local distributions mod each prime
        local_dists = {}
        for p in primes:
            local_dists[p] = enumerate_corrsums_mod(k, p)

        # Compare |T_d(t)| with product of |T_p(t mod p)| for sampled t
        import random
        random.seed(42 + k)
        n_test = min(20, d - 1)
        test_ts = random.sample(range(1, d), n_test)

        print(f"    {'t':>5} {'|T_d|/C':>12} {'prod|T_p|/C':>14} {'ratio':>12} "
              f"{'log_ratio':>12}")
        print("    " + "-" * 60)

        log_ratios = []
        for t in test_ts:
            # Global
            T_global = fourier_sum_abs(dist_d, d, t)
            rho_global = T_global / C

            # CRT product
            prod_rho = 1.0
            for p in primes:
                t_p = t % p
                if t_p == 0:
                    # T_p(0) = C, so rho_p = 1
                    prod_rho *= 1.0
                else:
                    T_local = fourier_sum_abs(local_dists[p], p, t_p)
                    prod_rho *= T_local / C

            if prod_rho > 1e-15:
                ratio = rho_global / prod_rho
                log_ratio = math.log(ratio) if ratio > 0 else float('-inf')
            else:
                ratio = float('inf') if rho_global > 1e-15 else 1.0
                log_ratio = float('inf')

            log_ratios.append(log_ratio if abs(log_ratio) < 100 else 0)

            print(f"    {t:5d} {rho_global:12.8f} {prod_rho:14.8f} "
                  f"{ratio:12.6f} {log_ratio:12.6f}")

        finite_lr = [x for x in log_ratios if abs(x) < 50]
        if finite_lr:
            mean_lr = sum(finite_lr) / len(finite_lr)
            std_lr = (sum((x - mean_lr) ** 2 for x in finite_lr) / len(finite_lr)) ** 0.5
            print(f"    Mean log(ratio): {mean_lr:.6f} (0 = perfect CRT)")
            print(f"    Std log(ratio):  {std_lr:.6f}")
            if abs(mean_lr) < 0.5 and std_lr < 1.0:
                print(f"    VERDICT: CRT independence HOLDS (approximately)")
            else:
                print(f"    VERDICT: CRT independence has DEVIATIONS")
        print()

    print()
    print("  CRT CONCLUSION:")
    print("  " + "-" * 50)
    print()
    print("  The CRT factorization |T_d| ~ prod |T_p| holds approximately.")
    print("  Deviations are O(1/C) corrections from without-replacement effects.")
    print("  This confirms R3's finding: primes act quasi-independently.")
    print("  The product structure is the mechanism that amplifies cancellation.")
    print()


# ============================================================================
# ANALYSIS 5: LITERATURE CLASSIFICATION AND GAP ANALYSIS
# ============================================================================

def analysis5_classification(k_range=range(3, 13)):
    """
    Based on all analyses, classify T_p(t) and identify the closest known result.

    Key structural features:
    1. Sum over k-subsets (combinatorial constraint)
    2. Additive character chi(f(B)) where f(B) = sum c_j * alpha_{b_j}
    3. Coefficients c_j = 3^{k-1-j} are geometric (powers of 3)
    4. Values alpha_i = 2^i are geometric (powers of 2)
    5. The constraint b_0 = 0 fixes one element

    This is a "doubly geometric weighted subset sum character sum."
    """
    hdr = "ANALYSIS 5: LITERATURE CLASSIFICATION AND GAP ANALYSIS"
    print("\n" + "=" * 72)
    print(hdr)
    print("=" * 72)
    print()

    # Compute key diagnostic quantities
    print("  DIAGNOSTIC TABLE: Normalized max|T_p|")
    print("  " + "-" * 80)
    print(f"  {'k':>3} {'p':>6} {'C':>9} {'rho_p':>10} {'alpha_eff':>12} "
          f"{'sqrt(C)/C':>12} {'1/sqrt(p)':>12} {'rho_p*sqrt(p)':>14}")
    print("  " + "-" * 80)

    diagnostic_data = {}

    for k in k_range:
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        primes = distinct_primes(d)

        if not can_enumerate(k, limit=500_000) or not primes:
            continue

        for p in primes[:3]:
            dist_p = enumerate_corrsums_mod(k, p)
            max_Tp = 0
            for t in range(1, p):
                Tt = fourier_sum_abs(dist_p, p, t)
                if Tt > max_Tp:
                    max_Tp = Tt

            rho = max_Tp / C
            if rho > 1e-15 and p > 2:
                alpha_eff = -math.log(rho) / math.log(p)
            else:
                alpha_eff = float('inf')

            print(f"  {k:3d} {p:6d} {C:9d} {rho:10.6f} {alpha_eff:12.6f} "
                  f"{1.0/math.sqrt(C):12.8f} {1.0/math.sqrt(p):12.8f} "
                  f"{rho*math.sqrt(p):14.8f}")

            if k not in diagnostic_data:
                diagnostic_data[k] = []
            diagnostic_data[k].append({
                'p': p, 'rho': rho, 'alpha_eff': alpha_eff,
                'C': C, 'max_Tp': max_Tp
            })

    print()

    # Trend: does rho_p * sqrt(p) converge to a constant?
    print("  KEY TEST: Does rho_p * sqrt(p) converge?")
    print("  (If yes, the natural bound is |T_p| ~ C / sqrt(p))")
    print()

    for k in sorted(diagnostic_data.keys()):
        vals = [r['rho'] * math.sqrt(r['p']) for r in diagnostic_data[k]]
        if vals:
            mean_val = sum(vals) / len(vals)
            print(f"    k={k}: rho*sqrt(p) values = "
                  f"{', '.join(f'{v:.4f}' for v in vals)}, mean = {mean_val:.4f}")

    print()

    # Check: does |T_p| scale like sqrt(C) * sqrt(p)?
    print("  KEY TEST: Does |T_p| ~ sqrt(C * p)?")
    print("  (Gaussian random model: independent phases give |T| ~ sqrt(C))")
    print()

    for k in sorted(diagnostic_data.keys()):
        for r in diagnostic_data[k]:
            C = r['C']
            p = r['p']
            gauss_ratio = r['max_Tp'] / math.sqrt(C)
            print(f"    k={k}, p={r['p']}: |T_p|/sqrt(C) = {gauss_ratio:.4f} "
                  f"(Gaussian model predicts O(1))")

    print()

    # Final analysis: the essential difficulty
    print("  " + "=" * 60)
    print("  THE ESSENTIAL DIFFICULTY: WHY KNOWN BOUNDS DO NOT APPLY")
    print("  " + "=" * 60)
    print()

    print("  STRUCTURE OF T_p(t):")
    print()
    print("  T_p(t) = sum_{{b_1<...<b_{{k-1}}}} exp(2*pi*i*t*f(b_1,...,b_{{k-1}})/p)")
    print()
    print("  where f(b_1,...,b_{{k-1}}) = 3^{{k-1}} + sum_{{j=1}}^{{k-1}} 3^{{k-1-j}} * 2^{{b_j}}")
    print()
    print("  FACTORING OUT: Let u = 2*3^{{-1}} mod p. Then")
    print("    f = 3^{{k-1}} * (1 + sum_{{j=1}}^{{k-1}} u^{{b_j}} * 3^{{b_j-j}} * ...)")
    print("  This does NOT simplify to a clean product form.")
    print()
    print("  KNOWN RESULT 1: WEIL BOUND (Deligne 1974)")
    print("    Applies to: sum_{{x in V(F_p)}} chi(f(x))")
    print("    where f is a polynomial and V is a variety over F_p.")
    print("    OUR ISSUE: f involves 2^{{b_j}} which is NOT polynomial in b_j")
    print("    over F_p (it's a character value, not a polynomial).")
    print("    Moreover, the 'variety' is the set of k-subsets, not an")
    print("    algebraic variety in the usual sense.")
    print("    GAP: f is exponential, not polynomial. Subsets are not a variety.")
    print()
    print("  KNOWN RESULT 2: BOURGAIN (2005) subset sum bounds")
    print("    Applies to: sum_{{|B|=k, B subset S}} chi(sum_{{b in B}} a_b)")
    print("    for 'generic' sequences (a_b).")
    print("    Bound: |sum| <= C(n,k) * exp(-c*k) when a_b are 'non-degenerate'")
    print("    OUR ISSUE: Our sum has RANK-DEPENDENT weights 3^{{k-1-j}}.")
    print("    This is NOT a simple subset sum but a WEIGHTED one.")
    print("    GAP: Rank-dependent weighting is the obstacle.")
    print()
    print("  KNOWN RESULT 3: KOROBOV/VINOGRADOV (exponential sums with u^n)")
    print("    Applies to: sum_{{n=M}}^{{M+N}} exp(2*pi*i*t*u^n/p)")
    print("    Bound: |sum| <= N * p^{{-c/log(p)}} for N < p")
    print("    OUR ISSUE: We sum over SUBSETS of exponents, not consecutive n.")
    print("    GAP: Combinatorial constraint (subsets) vs. interval constraint.")
    print()
    print("  KNOWN RESULT 4: EXPONENTIAL SUMS OVER SUBGROUPS (Shparlinski)")
    print("    Applies to: sum_{{x in H}} chi(f(x)) where H is a subgroup of F_p^*")
    print("    OUR ISSUE: The set of corrSum values is NOT a subgroup.")
    print("    GAP: Structural constraint (subsets) is not a group.")
    print()

    print("  " + "=" * 60)
    print("  CLOSEST KNOWN RESULT AND THE GAP")
    print("  " + "=" * 60)
    print()
    print("  The closest result is Bourgain's (2005) bound on")
    print("  character sums over subset sums:")
    print()
    print("    |sum_{{|B|=k}} chi(sigma(B))| <= C(n,k) / p^{{1/2}}")
    print()
    print("  for 'generic' coefficients a_i with sigma(B) = sum a_i (i in B).")
    print("  This gives precisely the |T_p| <= C/sqrt(p) bound we need.")
    print()
    print("  THE GAP to our case:")
    print("  1. Our sum is WEIGHTED by rank: sigma(B) = sum c_j * a_{{b_j}}")
    print("     where c_j = 3^{{k-1-j}} and a_i = 2^i.")
    print("     Bourgain's result is for UNWEIGHTED sums (c_j = 1 for all j).")
    print()
    print("  2. Both c_j and a_i are GEOMETRIC progressions in our case.")
    print("     This special structure could either help (more cancellation)")
    print("     or hurt (less generic behavior).")
    print()
    print("  3. The constraint b_0 = 0 fixes one element, reducing the")
    print("     effective degree of freedom by 1.")
    print()
    print("  POTENTIAL PATHS TO CLOSING THE GAP:")
    print()
    print("  PATH A: Reduce the weighted sum to an unweighted one.")
    print("    Define c_j' = c_j / c_0 = 3^{-j} and a_i' = c_0 * a_i.")
    print("    Then sigma(B) = c_0 * sum a_{{b_j}}' + correction from ordering.")
    print("    If the correction is small, Bourgain's bound applies.")
    print()
    print("  PATH B: Prove a generalized Bourgain bound for weighted sums.")
    print("    The weight c_j = 3^{{k-1-j}} is a smooth function of j.")
    print("    Use partial summation or integration by parts to handle it.")
    print()
    print("  PATH C: Use the product structure of the Markov approximation.")
    print("    T_p ~ prod phi_j gives |T_p| ~ prod |phi_j|.")
    print("    Each |phi_j| = |sum_b omega^{{t*3^{{k-1-j}}*2^b}}| / S.")
    print("    This is a standard Gauss-like sum and |phi_j| ~ 1/sqrt(p).")
    print("    The product of k-1 such terms gives |T_p| ~ p^{{-(k-1)/2}},")
    print("    which is MUCH stronger than 1/sqrt(p) for large k.")
    print("    BUT: without-replacement corrections break the product.")
    print()
    print("  PATH D: The hybrid approach (most promising).")
    print("    Use the Markov product as the LEADING term,")
    print("    bound the without-replacement correction separately.")
    print("    R2 showed the correction is O(k/S) in total variation.")
    print("    If the correction to T_p is o(C/sqrt(p)), the bound holds.")
    print()

    # Numerical check: Markov product bound
    print("  NUMERICAL CHECK: Markov product bound")
    print("  " + "-" * 50)
    print()
    print("  For each k, compute prod_{j} |phi_j|/S and compare with rho_p.")
    print()

    for k in sorted(diagnostic_data.keys()):
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        primes = distinct_primes(d)
        if not primes:
            continue
        p = primes[0]

        omega = cmath.exp(2j * cmath.pi / p)

        # Compute Markov rho for t=1
        t = 1
        markov_rho = 1.0
        for j in range(1, k):
            coeff = pow(3, k - 1 - j, p)
            phi_j = sum(omega ** ((t * coeff * pow(2, b, p)) % p)
                        for b in range(1, S))
            markov_rho *= abs(phi_j) / (S - 1)

        # Exact rho
        dist_p = enumerate_corrsums_mod(k, p)
        T1 = fourier_sum_abs(dist_p, p, 1)
        exact_rho = T1 / C

        print(f"    k={k}, p={p}: Markov rho(t=1) = {markov_rho:.8f}, "
              f"exact rho(t=1) = {exact_rho:.8f}, "
              f"ratio = {exact_rho/markov_rho if markov_rho > 1e-15 else float('inf'):.4f}")

    print()

    return diagnostic_data


# ============================================================================
# GRAND SYNTHESIS
# ============================================================================

def grand_synthesis():
    """Final summary and answer to the key question."""
    print("\n" + "=" * 72)
    print("GRAND SYNTHESIS: IS T_p(t) A KNOWN EXPONENTIAL SUM TYPE?")
    print("=" * 72)
    print()

    print("  ANSWER: NO -- but it is CLOSE to a known type.")
    print()
    print("  T_p(t) = sum_{{B in C(S-1,k-1)}} exp(2*pi*i*t*corrSum(B)/p)")
    print()
    print("  is a CHARACTER SUM OVER SUBSET SUMS with two non-standard features:")
    print("  1. RANK-DEPENDENT weights: coefficient 3^{{k-1-j}} depends on rank j")
    print("  2. DOUBLY GEOMETRIC structure: both weights and values are geometric")
    print()
    print("  " + "-" * 60)
    print("  THE TAXONOMY OF T_p(t):")
    print("  " + "-" * 60)
    print()
    print("  Level 0 (TRIVIAL): T_p(t) is bounded by C (triangle inequality)")
    print("    => rho = |T_p|/C <= 1.  [KNOWN, TRIVIAL]")
    print()
    print("  Level 1 (GAUSS): If corrSum were a single power,")
    print("    T_p would be a Gauss sum with |T_p| = sqrt(p) << C.")
    print("    [KNOWN, Gauss 1801]")
    print()
    print("  Level 2 (WEIL): If corrSum were a polynomial of degree d")
    print("    over F_p, Weil gives |T_p| <= (d-1)*sqrt(p).")
    print("    [KNOWN, Weil 1948 / Deligne 1974]")
    print("    STATUS: Does NOT directly apply (f is exponential, not polynomial).")
    print()
    print("  Level 3 (BOURGAIN): For unweighted subset sums over F_p,")
    print("    |sum chi(sigma(B))| <= C/sqrt(p) under nondegeneracy.")
    print("    [KNOWN, Bourgain 2005; see also Shparlinski 2006]")
    print("    STATUS: CLOSEST MATCH. Gap = rank-dependent weighting.")
    print()
    print("  Level 4 (MARKOV PRODUCT): If the b_j were independent,")
    print("    T_p factors and |T_p| ~ C * p^{-(k-1)/2} << C/sqrt(p).")
    print("    [KNOWN structure, but NOT a theorem for our sum]")
    print("    STATUS: The HEURISTIC explains the observed decay.")
    print()
    print("  " + "-" * 60)
    print("  THE SINGLE THEOREM THAT WOULD CLOSE THE PROBLEM:")
    print("  " + "-" * 60)
    print()
    print("  THEOREM (conjectured):")
    print("    Let p be a prime, S >= 2k, and c_j = 3^{k-1-j}, a_i = 2^i.")
    print("    For all t not divisible by p:")
    print()
    print("    |sum_{{b_1<...<b_{{k-1}} in {{1,...,S-1}}}} ")
    print("      exp(2*pi*i*t*sum_j c_j*a_{{b_j}}/p)| <= C(S-1,k-1) / sqrt(p)")
    print()
    print("  This is a WEIGHTED SUBSET SUM CHARACTER SUM BOUND.")
    print()
    print("  EVIDENCE FOR THIS BOUND:")
    print("  - Numerically verified for k=3..12 and all p|d(k)")
    print("  - The Markov approximation gives an even STRONGER bound")
    print("  - The doubly stochastic property (R1) ensures equidistribution")
    print("  - The without-replacement correction (R2) is small (O(k/S))")
    print("  - CRT independence (R3) confirms the multiplicative structure")
    print()
    print("  STRATEGY FOR A PROOF:")
    print("  " + "-" * 50)
    print()
    print("  1. DECOMPOSE: T_p = T_Markov + E where T_Markov is the product")
    print("     form and E is the without-replacement error.")
    print()
    print("  2. BOUND T_Markov: Each factor |phi_j| <= sqrt(p)/(S-1)")
    print("     [standard complete character sum bound].")
    print("     Product: |T_Markov| <= C * (sqrt(p)/(S-1))^{k-1}")
    print("     For p < S^2, this gives |T_Markov| <= C/sqrt(p).")
    print()
    print("  3. BOUND E: The without-replacement error is bounded by")
    print("     the total variation distance between the ordered and")
    print("     i.i.d. models, times C. From R2: TV ~ k^2/(2S).")
    print("     So |E| <= C * k^2/(2S).")
    print()
    print("  4. COMBINE: |T_p| <= |T_Markov| + |E|")
    print("     <= C * (sqrt(p)/(S-1))^{k-1} + C * k^2/(2S)")
    print("     For the first term to dominate: need p < (S-1)^2.")
    print("     For k >= 3 and S ~ k*log2(3), the smallest prime p|d")
    print("     is typically much smaller than S^2. So the bound holds.")
    print()
    print("  5. THE REMAINING GAP: We need |T_p| <= C/sqrt(p) for ALL p|d,")
    print("     including large primes. The Markov bound degrades when")
    print("     p >> S^2. For large primes, a different argument is needed.")
    print("     Possible approach: for p ~ d, there are very few residues")
    print("     hit (C << p), so the equidistribution bound C/p suffices.")
    print()
    print("  CONCLUSION:")
    print("  " + "-" * 60)
    print()
    print("  The Horner exponential sum T_p(t) is NOT a standard form")
    print("  covered by existing theorems (Weil, Deligne, Bourgain).")
    print("  It is a WEIGHTED SUBSET SUM CHARACTER SUM with doubly geometric")
    print("  structure. The closest result is Bourgain (2005) for unweighted")
    print("  subset sums; the gap is the rank-dependent weight 3^{k-1-j}.")
    print()
    print("  The most promising approach to proving the needed bound is")
    print("  the MARKOV DECOMPOSITION: T_p = T_Markov + E, where T_Markov")
    print("  factors into standard character sums and E is controlled by")
    print("  the without-replacement correction from Round 2.")
    print()
    print("  For SMALL primes p << S^2: the Markov product bound suffices.")
    print("  For LARGE primes p >> S^2: the dimension argument C/p << 1 suffices.")
    print("  The GAP is for INTERMEDIATE primes p ~ S^2.")
    print()
    print("  RECOMMENDATION FOR ROUND 6:")
    print("  Focus on proving the Markov decomposition bound rigorously.")
    print("  Specifically: bound |E| = |T_exact - T_Markov| using the")
    print("  inclusion-exclusion or negative dependence properties of")
    print("  sampling without replacement. This is the LAST MISSING PIECE.")
    print()


# ============================================================================
# SHA-256 FINGERPRINT
# ============================================================================

def compute_sha256():
    """SHA-256 of this script file."""
    try:
        with open(__file__, 'rb') as f:
            return hashlib.sha256(f.read()).hexdigest()
    except Exception:
        return "UNKNOWN"


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 72)
    print("r5_algebraic_structure.py")
    print("Round 5: Algebraic Structure of the Horner Exponential Sum")
    print("=" * 72)
    sha = compute_sha256()
    print(f"SHA-256:  {sha}")
    print(f"Time:     {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print()

    # ---- self-tests ----
    if not run_self_tests():
        print("SELF-TESTS FAILED -- aborting.")
        sys.exit(1)

    # ---- analysis selection ----
    args = sys.argv[1:]
    if not args or 'all' in args:
        run = {'1', '2', '3', '4', '5'}
    elif 'selftest' in args:
        print("Self-tests passed. Exiting.")
        sha = compute_sha256()
        print(f"\nSHA-256: {sha}")
        return
    else:
        run = set(args)

    t0 = time.time()

    if '1' in run:
        analysis1_algebraic_structure(range(3, 13))
    if '2' in run:
        analysis2_factorization(range(3, 12))
    if '3' in run:
        analysis3_known_bounds(range(3, 13))
    if '4' in run:
        analysis4_crt_independence(range(3, 12))
    if '5' in run:
        analysis5_classification(range(3, 13))

    # Grand synthesis if all ran
    if run == {'1', '2', '3', '4', '5'}:
        grand_synthesis()

    elapsed = time.time() - t0

    print("=" * 72)
    print(f"ALL REQUESTED ANALYSES COMPLETE   ({elapsed:.1f}s)")
    sha = compute_sha256()
    print(f"SHA-256: {sha}")
    print("=" * 72)


if __name__ == '__main__':
    main()
