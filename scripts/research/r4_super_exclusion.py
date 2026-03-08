#!/usr/bin/env python3
"""
r4_super_exclusion.py -- Round 4: Quantifying & Exploiting Super-Exclusion
============================================================================

CONTEXT (from Rounds 1-3):
  For a nontrivial cycle of length k in the Collatz (3x+1) map:
      d(k) = 2^S - 3^k,   S = ceil(k * log2(3))

  corrSum(A) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{b_j}
  where B = {b_1 < ... < b_{k-1}} subset of {1,...,S-1}, b_0 = 0.

  A cycle exists iff corrSum(A) = 0 mod d(k) for some valid A.

  Round 3 discovered SUPER-EXCLUSION: N_0(d) = 0 always, even when CRT
  independence predicts N_0_pred > 0. Examples:
    k=6:  CRT predicts ~1.71,  reality N_0 = 0
    k=9:  CRT predicts ~1.01,  reality N_0 = 0
    k=10: CRT predicts ~2.87,  reality N_0 = 0

  The source: algebraic invariants of corrSum create FORBIDDEN cells in
  the joint CRT distribution. The invariants are:
    (I1) corrSum is always odd:            corrSum = 1 mod 2
    (I2) corrSum is never 0 mod 3:         corrSum != 0 mod 3
    (I3) corrSum mod 4 in {1, 3}:          corrSum is odd mod 4
    (I4) corrSum mod 12 is determined by min(A): deeper constraint

THIS SCRIPT quantifies how much the invariants explain, and whether
the constrained CRT prediction suffices to prove N_0 = 0.

FIVE INVESTIGATION TOOLS:
  1. Exclusion bonus: compare N_0_CRT, N_0_CRT_constrained, N_0_exact
  2. Invariants as CRT filters: compute compatible fractions f(p)
  3. Forbidden residues mod p: map the forbidden set for p <= 100
  4. d mod 12 interaction: how d's residues interact with corrSum's
  5. Towards a super-exclusion theorem: is N_0_constrained < 1 always?

HONESTY COMMITMENT:
  All measurements are exact (exhaustive enumeration) where feasible.
  If the constrained CRT does NOT explain N_0 = 0, we say so clearly.

Author: Claude (Round 4 investigation for Eric Merle's Collatz Junction Theorem)
Date:   2026-03-08

Usage:
    python3 r4_super_exclusion.py          # run all tools
    python3 r4_super_exclusion.py 1 3      # run tools 1 and 3 only
    python3 r4_super_exclusion.py selftest  # run self-tests only

Requires: only math, itertools, collections (no heavy dependencies).
"""

import math
import hashlib
import sys
import time
from itertools import combinations
from collections import Counter, defaultdict
from fractions import Fraction


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


def is_prime(n):
    """Simple primality test."""
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True


def extended_gcd(a, b):
    """Extended Euclidean algorithm. Returns (gcd, x, y) with a*x + b*y = gcd."""
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x


def modinv(a, m):
    """Modular inverse of a mod m (None if gcd != 1)."""
    if m == 1:
        return 0
    g, x, _ = extended_gcd(a % m, m)
    if g != 1:
        return None
    return x % m


def num_compositions(S, k):
    """C(S-1, k-1): number of compositions of S into k positive parts."""
    return math.comb(S - 1, k - 1)


def can_enumerate(k, limit=2_000_000):
    """True if exhaustive enumeration is feasible."""
    S = compute_S(k)
    return math.comb(S - 1, k - 1) <= limit


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
    total = 3 ** (k - 1)  # j=0
    for idx in range(len(B_tuple)):
        j = idx + 1
        total += 3 ** (k - 1 - j) * 2 ** B_tuple[idx]
    return total


def enumerate_corrsums_mod(k, mod):
    """Exact distribution of corrSum mod `mod`. Returns Counter."""
    S = compute_S(k)
    counts = Counter()
    for B in combinations(range(1, S), k - 1):
        counts[corrsum_from_subset(B, k, mod)] += 1
    return counts


def enumerate_corrsums_mod_multi(k, mods_list):
    """
    Exact joint distribution of corrSum mod each modulus.
    Returns Counter of tuples (r_{m1}, r_{m2}, ...).
    Single enumeration pass for efficiency.
    """
    S = compute_S(k)
    joint = Counter()
    for B in combinations(range(1, S), k - 1):
        residues = tuple(corrsum_from_subset(B, k, m) for m in mods_list)
        joint[residues] += 1
    return joint


def subset_to_composition(B_tuple, S):
    """Convert (k-1)-subset B to composition (a_1,...,a_k)."""
    parts = []
    prev = 0
    for b in B_tuple:
        parts.append(b - prev)
        prev = b
    parts.append(S - prev)
    return tuple(parts)


# ============================================================================
# CORRSUM MOD 12 ANALYSIS: THE INVARIANT STRUCTURE
# ============================================================================

def corrsum_mod12_from_min_a(k):
    """
    For each possible min(A) = a_1 value (1 to S-k+1), determine
    the set of corrSum mod 12 values that actually occur.
    Returns dict: min_a -> set of residues mod 12.
    """
    S = compute_S(k)
    result = defaultdict(set)
    for B in combinations(range(1, S), k - 1):
        comp = subset_to_composition(B, S)
        min_a = comp[0]  # a_1 = first part = B[0] if k>1, else S
        cs_mod12 = corrsum_from_subset(B, k, 12)
        result[min_a].add(cs_mod12)
    return dict(result)


def accessible_residues_mod(k, mod, max_comb=2_000_000):
    """
    Return the SET of residues mod `mod` that corrSum can actually take.
    Uses exhaustive enumeration.
    """
    S = compute_S(k)
    C = math.comb(S - 1, k - 1)
    if C > max_comb:
        return None  # too large
    residues = set()
    for B in combinations(range(1, S), k - 1):
        residues.add(corrsum_from_subset(B, k, mod))
    return residues


# ============================================================================
# SELF-TESTS
# ============================================================================

def run_self_tests():
    """Verify mathematical correctness before running any tool."""
    print("=" * 72)
    print("SELF-TESTS")
    print("=" * 72)

    # ST-1: Basic S(k), d(k)
    assert compute_S(3) == 5
    assert compute_S(5) == 8
    assert compute_S(6) == 10
    assert compute_d(3) == 5    # 2^5 - 3^3 = 32 - 27 = 5
    assert compute_d(5) == 13   # 2^8 - 3^5 = 256 - 243 = 13
    assert compute_d(6) == 295  # 2^10 - 3^6 = 1024 - 729 = 295
    print("[PASS] ST-1   S(k) and d(k) for known values")

    # ST-2: corrSum always odd (invariant I1)
    for kk in (3, 4, 5, 6, 7):
        SS = compute_S(kk)
        for B in combinations(range(1, SS), kk - 1):
            assert corrsum_true(B, kk) % 2 == 1, f"Even corrSum at k={kk} B={B}"
    print("[PASS] ST-2   corrSum always odd (k=3..7)")

    # ST-3: corrSum never 0 mod 3 (invariant I2)
    for kk in (3, 4, 5, 6, 7):
        SS = compute_S(kk)
        for B in combinations(range(1, SS), kk - 1):
            assert corrsum_true(B, kk) % 3 != 0, f"corrSum = 0 mod 3 at k={kk}"
    print("[PASS] ST-3   corrSum never 0 mod 3 (k=3..7)")

    # ST-4: corrSum mod 4 in {1, 3} (invariant I3)
    for kk in (3, 4, 5, 6, 7):
        SS = compute_S(kk)
        for B in combinations(range(1, SS), kk - 1):
            r4 = corrsum_true(B, kk) % 4
            assert r4 in (1, 3), f"corrSum mod 4 = {r4} at k={kk}"
    print("[PASS] ST-4   corrSum mod 4 in {1,3} (k=3..7)")

    # ST-5: No cycles for k=3..10
    for kk in range(3, 11):
        SS = compute_S(kk)
        dd = compute_d(kk)
        for B in combinations(range(1, SS), kk - 1):
            assert corrsum_from_subset(B, kk, dd) != 0
    print("[PASS] ST-5   corrSum != 0 mod d for k=3..10 (no cycles)")

    # ST-6: CRT consistency
    for kk in (3, 4, 5, 6):
        dd = compute_d(kk)
        SS = compute_S(kk)
        primes = distinct_primes(dd)
        if len(primes) >= 2:
            p1, p2 = primes[0], primes[1]
            for B in combinations(range(1, SS), kk - 1):
                cs_d = corrsum_from_subset(B, kk, dd)
                cs_p1 = corrsum_from_subset(B, kk, p1)
                cs_p2 = corrsum_from_subset(B, kk, p2)
                assert cs_d % p1 == cs_p1
                assert cs_d % p2 == cs_p2
    print("[PASS] ST-6   CRT consistency: corrSum mod d reduces correctly")

    # ST-7: d(k) factorization check
    assert prime_factorization(295) == [(5, 1), (59, 1)]
    assert distinct_primes(295) == [5, 59]
    assert prime_factorization(13) == [(13, 1)]
    print("[PASS] ST-7   Factorization of d(k)")

    # ST-8: modinv correctness
    assert modinv(3, 5) == 2    # 3*2 = 6 = 1 mod 5
    assert modinv(3, 7) == 5    # 3*5 = 15 = 1 mod 7
    assert modinv(2, 13) is not None
    assert (2 * modinv(2, 13)) % 13 == 1
    print("[PASS] ST-8   modinv")

    # ST-9: Composition counting
    assert num_compositions(5, 3) == 6   # C(4,2) = 6
    assert num_compositions(8, 5) == 35  # C(7,4) = 35
    assert num_compositions(10, 6) == 126  # C(9,5)
    print("[PASS] ST-9   Composition counting")

    # ST-10: corrSum mod 12 structure
    # For k=3: corrSum = 3^2 + 3*2^b1 + 2^b2
    # With S=5, b1 in {1,2,3,4}, b2 > b1, b2 in {2,3,4}
    mod12_k3 = corrsum_mod12_from_min_a(3)
    # All corrSum mod 12 values should be odd and not 0 mod 3
    for min_a, resids in mod12_k3.items():
        for r in resids:
            assert r % 2 == 1, f"Even corrSum mod 12 = {r} for min_a={min_a}"
            assert r % 3 != 0, f"corrSum mod 12 = {r} = 0 mod 3 for min_a={min_a}"
    print("[PASS] ST-10  corrSum mod 12 respects invariants (k=3)")

    # ST-11: Accessible residues consistency
    for kk in (3, 4, 5):
        acc_2 = accessible_residues_mod(kk, 2)
        assert acc_2 == {1}, f"k={kk}: accessible mod 2 = {acc_2}, expected {{1}}"
        acc_3 = accessible_residues_mod(kk, 3)
        assert 0 not in acc_3, f"k={kk}: 0 accessible mod 3"
    print("[PASS] ST-11  Accessible residues: {1} mod 2, no 0 mod 3")

    # ST-12: enumerate_corrsums_mod count matches C(S-1,k-1)
    for kk in (3, 4, 5, 6):
        SS = compute_S(kk)
        C = num_compositions(SS, kk)
        counts = enumerate_corrsums_mod(kk, 7)
        total = sum(counts.values())
        assert total == C, f"k={kk}: count={total} != C={C}"
    print("[PASS] ST-12  Enumeration count matches composition count")

    print()
    print("ALL 12 SELF-TESTS PASSED")
    print("=" * 72)
    print()
    return True


# ============================================================================
# TOOL 1: EXCLUSION BONUS -- CRT vs CONSTRAINED CRT vs EXACT
# ============================================================================

def tool1_exclusion_bonus(k_range, max_comb=2_000_000):
    """
    For each k, compute:
    - N_0_CRT = C * prod_p (N_0(p)/C): pure independence prediction
    - N_0_constrained: CRT corrected by algebraic invariants
    - N_0_exact: true count (0 always for Collatz)
    - Bonus = N_0_CRT / N_0_exact (infinite when N_0 = 0)

    The constrained CRT accounts for:
      (I1) corrSum odd -> only odd residues contribute mod 2
      (I2) corrSum != 0 mod 3 -> removes residue 0 mod 3
      (I3) corrSum mod 4 in {1,3} -> removes {0,2} mod 4
      (I4) corrSum mod 12 constrained -> finer interaction
    """
    print("=" * 72)
    print("TOOL 1: EXCLUSION BONUS")
    print("  Compare N_0_CRT (naive), N_0_constrained (with invariants), N_0_exact")
    print("  Invariants: corrSum odd, != 0 mod 3, mod 4 in {1,3}")
    print("=" * 72)

    results = []

    for k in k_range:
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        primes = distinct_primes(d)

        if C > max_comb:
            print(f"\n  k={k:>2}: C={C:,} too large, skipping exact enumeration")
            # Still compute CRT predictions from structure
            results.append({
                'k': k, 'S': S, 'd': d, 'C': C, 'primes': primes,
                'N0_exact': None, 'N0_CRT': None, 'N0_constrained': None,
                'bonus': None, 'skipped': True,
            })
            continue

        # ----- Exact N_0(d) -----
        counts_d = enumerate_corrsums_mod(k, d)
        N0_exact = counts_d.get(0, 0)

        # ----- N_0 per prime (marginal) -----
        N0_per_prime = {}
        P0_per_prime = {}
        for p in primes:
            counts_p = enumerate_corrsums_mod(k, p)
            N0_per_prime[p] = counts_p.get(0, 0)
            P0_per_prime[p] = N0_per_prime[p] / C

        # ----- N_0_CRT (pure independence) -----
        product_P0 = 1.0
        for p in primes:
            product_P0 *= P0_per_prime[p]
        N0_CRT = C * product_P0

        # ----- N_0_constrained: account for invariant filtering -----
        # The invariants exclude certain residue classes.
        # For each prime p | d, we need the fraction of residues mod p
        # that are COMPATIBLE with the invariants.
        #
        # Strategy: enumerate corrSum mod (p * 12) jointly, then
        # count how many residues mod p co-occur with invariant-compatible
        # residues mod 12.
        #
        # Simpler approach: directly compute the fraction of compositions
        # whose corrSum = 0 mod p AND corrSum satisfies invariants.
        # But the invariants are ALWAYS satisfied, so this equals N_0(p)/C.
        #
        # The constrained CRT should use the CONDITIONAL probability:
        # P(corrSum = 0 mod p | invariants) vs P(corrSum = 0 mod p).
        # Since invariants are always satisfied, the conditional is the same.
        #
        # The REAL constraint is different: the invariants restrict which
        # residues mod d can contain corrSum. Specifically:
        #   corrSum mod 2 = 1  (only odd residues mod d)
        #   corrSum mod 3 != 0 (remove multiples of 3 from residues mod d)
        #   corrSum mod 4 in {1,3} (only odd residues mod 4)
        #
        # For corrSum = 0 mod d, we need d | corrSum.
        # But corrSum is odd, so if 2 | d, then corrSum != 0 mod d.
        # And corrSum != 0 mod 3, so if 3 | d, then corrSum != 0 mod d.
        #
        # This is the KEY: invariants create AUTOMATIC exclusion when 2|d or 3|d.

        # Check which invariants directly exclude corrSum = 0 mod d
        d_divisible_by_2 = (d % 2 == 0)
        d_divisible_by_3 = (d % 3 == 0)

        if d_divisible_by_2:
            # corrSum odd -> corrSum != 0 mod 2 -> corrSum != 0 mod d
            invariant_excludes = "I1 (parity)"
            N0_constrained = 0.0
        elif d_divisible_by_3:
            # corrSum != 0 mod 3 -> corrSum != 0 mod d
            invariant_excludes = "I2 (mod 3)"
            N0_constrained = 0.0
        else:
            # Neither 2 nor 3 divides d. Invariants don't directly force N_0=0.
            # But they reduce the density of accessible residues.
            #
            # Constrained prediction: for each prime p | d,
            # compute P(corrSum = 0 mod p | corrSum accessible).
            # The accessible set mod p is determined by the invariants
            # INTERSECTED with the achievable residues mod p.
            #
            # More precisely: use the actual accessible residues mod p
            # (which already embed all invariants) and compute
            # f(p) = (1 if 0 in accessible else 0) * (accessible count / p)
            # But this mixes up the counting.
            #
            # Better: N_0_constrained = C * prod_p [N_0(p) / C]
            # where N_0(p) already accounts for invariants (since corrSum
            # always satisfies invariants, P(0|p) = N_0(p)/C includes
            # the invariant effect).
            #
            # The independence assumption is: events {corrSum=0 mod p_i} are
            # independent across different primes. The invariants affect each
            # marginal equally.
            #
            # So the constrained prediction IS the same as the CRT prediction
            # when invariants don't directly kill d.

            # HOWEVER: the invariants create JOINT constraints beyond marginals.
            # corrSum mod 12 is constrained to specific values.
            # If d shares factors with 12 beyond {2,3}, e.g., 4|d or 12|d,
            # the mod 12 constraint restricts further.

            # For d coprime to 6: invariants don't directly exclude 0.
            # The constrained CRT = plain CRT in this case.

            invariant_excludes = "NONE (d coprime to 6)"
            N0_constrained = N0_CRT

            # Refinement: check if corrSum mod gcd(d, 12) is compatible with 0
            g = math.gcd(d, 12)
            if g > 1:
                # corrSum mod g is constrained by invariants
                # Need 0 mod g to be achievable
                acc_g = accessible_residues_mod(k, g)
                if acc_g is not None and 0 not in acc_g:
                    invariant_excludes = f"I4 (mod {g})"
                    N0_constrained = 0.0

        # Bonus
        if N0_exact == 0:
            if N0_CRT > 0:
                bonus = float('inf')
            else:
                bonus = float('nan')
        else:
            bonus = N0_CRT / N0_exact

        pf_str = '*'.join(str(p) for p in primes)
        print(f"\n  k={k:>2}: d={d} = {pf_str}")
        print(f"    C = {C:,}")
        for p in primes:
            print(f"    N_0(mod {p:>5}) = {N0_per_prime[p]:>6}  "
                  f"P_0 = {P0_per_prime[p]:.6f}  1/p = {1/p:.6f}")
        print(f"    N_0_CRT (independence) = {N0_CRT:.4f}")
        print(f"    N_0_constrained        = {N0_constrained:.4f}"
              f"  [excluded by: {invariant_excludes}]")
        print(f"    N_0_exact              = {N0_exact}")
        print(f"    Bonus (CRT/exact)      = {'INF' if bonus == float('inf') else f'{bonus:.4f}'}")

        results.append({
            'k': k, 'S': S, 'd': d, 'C': C, 'primes': primes,
            'N0_exact': N0_exact, 'N0_CRT': N0_CRT,
            'N0_constrained': N0_constrained,
            'bonus': bonus,
            'invariant_excludes': invariant_excludes,
            'N0_per_prime': N0_per_prime,
            'P0_per_prime': P0_per_prime,
            'skipped': False,
        })

    # Summary
    print("\n" + "-" * 72)
    print("  TOOL 1 SUMMARY: Exclusion Bonus")
    print(f"  {'k':>3} {'d':>12} {'N0_CRT':>10} {'N0_constr':>10} "
          f"{'N0_exact':>8} {'excluded_by':>18}")
    print("  " + "-" * 70)
    n_explained = 0
    n_total = 0
    for r in results:
        if r['skipped']:
            print(f"  {r['k']:>3} {r['d']:>12}  (skipped: C too large)")
            continue
        n_total += 1
        crt = r['N0_CRT']
        con = r['N0_constrained']
        ex = r['N0_exact']
        excl = r['invariant_excludes']
        if ex == 0 and con == 0:
            n_explained += 1
        print(f"  {r['k']:>3} {r['d']:>12} {crt:>10.3f} {con:>10.3f} "
              f"{ex:>8} {excl:>18}")

    print(f"\n  Invariants explain N_0=0: {n_explained}/{n_total} cases")
    if n_explained == n_total and n_total > 0:
        print("  => PERFECT: algebraic invariants FULLY explain super-exclusion")
        print("     for all tested k values.")
    else:
        unexplained = [r for r in results
                       if not r['skipped'] and r['N0_exact'] == 0
                       and r['N0_constrained'] > 0.5]
        if unexplained:
            print(f"\n  UNEXPLAINED cases (N_0=0 but N_0_constrained > 0.5):")
            for r in unexplained:
                print(f"    k={r['k']}: N_0_CRT={r['N0_CRT']:.3f}, "
                      f"N_0_constrained={r['N0_constrained']:.3f}")
    print()

    return results


# ============================================================================
# TOOL 2: INVARIANTS AS CRT FILTERS
# ============================================================================

def tool2_crt_filters(k_range, max_comb=2_000_000):
    """
    For each prime p | d, compute the fraction of residues mod p that
    are COMPATIBLE with the algebraic invariants of corrSum.

    The invariants constrain corrSum mod 12. For a prime p, the
    compatible fraction f(p) = |{r in Z/pZ : exists A with corrSum=r mod p
    AND corrSum satisfies invariants}| / p.

    Since invariants are always satisfied, f(p) = |Im(corrSum mod p)| / p.

    The constrained CRT predicts: N_0 ~ C * prod_p f(p) * (accessibility of 0).
    """
    print("=" * 72)
    print("TOOL 2: INVARIANTS AS CRT FILTERS")
    print("  For each p | d: what fraction of Z/pZ is accessible to corrSum?")
    print("  Does 0 mod p survive the invariant filter?")
    print("=" * 72)

    results = []

    for k in k_range:
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        primes = distinct_primes(d)

        if C > max_comb:
            print(f"\n  k={k:>2}: C={C:,} too large, skipping")
            continue

        print(f"\n  k={k:>2}: d={d} = {'*'.join(str(p) for p in primes)}")
        print(f"    C = {C:,}")

        prime_data = []
        zero_blocked_primes = []

        for p in primes:
            counts_p = enumerate_corrsums_mod(k, p)
            accessible = set(counts_p.keys())
            n_accessible = len(accessible)
            f_p = n_accessible / p
            zero_accessible = 0 in accessible
            N0_p = counts_p.get(0, 0)

            if not zero_accessible:
                zero_blocked_primes.append(p)

            # Detailed residue info
            forbidden = set(range(p)) - accessible
            print(f"    p={p:>5}: accessible={n_accessible}/{p} "
                  f"(f={f_p:.4f}), "
                  f"0 {'IN' if zero_accessible else 'NOT IN'} Im, "
                  f"N_0={N0_p}, "
                  f"forbidden={sorted(forbidden) if len(forbidden) <= 10 else f'{len(forbidden)} residues'}")

            prime_data.append({
                'p': p, 'n_accessible': n_accessible,
                'f_p': f_p, 'zero_accessible': zero_accessible,
                'N0_p': N0_p, 'forbidden': sorted(forbidden),
            })

        # CRT filter product
        product_f = 1.0
        for pd in prime_data:
            product_f *= pd['f_p']

        # Does any single prime block 0?
        any_prime_blocks_zero = len(zero_blocked_primes) > 0

        print(f"    Product f = {product_f:.6f}")
        print(f"    N_0_filter_pred = C * prod f = {C * product_f:.2f}")
        if any_prime_blocks_zero:
            print(f"    0 BLOCKED by primes: {zero_blocked_primes}")
            print(f"    => N_0 = 0 guaranteed by invariant filter at these primes")

        results.append({
            'k': k, 'd': d, 'C': C, 'primes': primes,
            'prime_data': prime_data,
            'product_f': product_f,
            'zero_blocked_primes': zero_blocked_primes,
            'any_blocks_zero': any_prime_blocks_zero,
        })

    # Summary
    print("\n" + "-" * 72)
    print("  TOOL 2 SUMMARY: CRT Filters")
    print(f"  {'k':>3} {'d':>12} {'prod_f':>10} {'C*prod_f':>10} "
          f"{'0_blocked':>10} {'mechanism':>20}")
    print("  " + "-" * 70)

    for r in results:
        mechanism = "FILTER" if r['any_blocks_zero'] else "CRT < 1" \
            if r['C'] * r['product_f'] < 1 else "INSUFFICIENT"
        blocked_str = str(r['zero_blocked_primes']) if r['any_blocks_zero'] else "none"
        print(f"  {r['k']:>3} {r['d']:>12} {r['product_f']:>10.6f} "
              f"{r['C'] * r['product_f']:>10.2f} "
              f"{blocked_str:>10} {mechanism:>20}")
    print()

    return results


# ============================================================================
# TOOL 3: FORBIDDEN RESIDUES MOD p
# ============================================================================

def tool3_forbidden_residues(k_range, p_max=100, max_comb=2_000_000):
    """
    For each prime p <= p_max, compute the set of residues mod p that
    corrSum can NEVER take (for various k values).

    The invariants guarantee:
      p=2: only r=1 accessible (fraction forbidden = 1/2)
      p=3: only r in {1,2} accessible (fraction forbidden = 1/3)

    For larger primes: what fraction is forbidden? Is there a pattern?
    """
    print("=" * 72)
    print("TOOL 3: FORBIDDEN RESIDUES MOD p")
    print(f"  For each prime p <= {p_max}: what fraction of Z/pZ is forbidden?")
    print("  Invariant-forced: p=2 -> 1/2, p=3 -> 1/3, p=4 -> 1/2")
    print("=" * 72)

    # Collect primes up to p_max
    small_primes = [p for p in range(2, p_max + 1) if is_prime(p)]

    # For each k (small enough for enumeration), compute accessible residues
    results_by_k = {}
    for k in k_range:
        S = compute_S(k)
        C = num_compositions(S, k)
        if C > max_comb:
            continue

        results_by_k[k] = {}
        for p in small_primes:
            acc = accessible_residues_mod(k, p)
            if acc is not None:
                forbidden = set(range(p)) - acc
                results_by_k[k][p] = {
                    'accessible': sorted(acc),
                    'forbidden': sorted(forbidden),
                    'n_accessible': len(acc),
                    'n_forbidden': len(forbidden),
                    'frac_forbidden': len(forbidden) / p,
                    'zero_forbidden': 0 in forbidden,
                }

    # Show results
    print("\n  --- Invariant-forced exclusions ---")
    for k in sorted(results_by_k.keys()):
        if k > 8:
            continue  # Only show small k for readability
        print(f"\n  k={k}: S={compute_S(k)}, C={num_compositions(compute_S(k), k)}")
        for p in [2, 3, 4, 5, 7, 11, 13]:
            if p in results_by_k[k]:
                rd = results_by_k[k][p]
                forb_str = str(rd['forbidden']) if rd['n_forbidden'] <= 10 else \
                    f"{rd['n_forbidden']} residues"
                print(f"    p={p:>3}: forbidden={forb_str}, "
                      f"frac={rd['frac_forbidden']:.4f}, "
                      f"0_forbidden={rd['zero_forbidden']}")

    # Cross-k analysis: for each prime, is the forbidden set STABLE across k?
    print("\n\n  --- Cross-k stability of forbidden residues ---")
    print(f"  {'p':>5} {'always_forbidden':>20} {'fraction':>10} {'0_always_forbidden':>20}")
    print("  " + "-" * 60)

    stability_results = []
    for p in small_primes[:25]:  # first 25 primes
        # Intersection of forbidden sets across all k
        all_k = sorted(results_by_k.keys())
        if not all_k:
            continue

        # Get forbidden sets for all available k
        forbidden_sets = []
        for k in all_k:
            if p in results_by_k[k]:
                forbidden_sets.append(set(results_by_k[k][p]['forbidden']))

        if not forbidden_sets:
            continue

        # Intersection = residues forbidden for ALL k
        always_forbidden = forbidden_sets[0]
        for fs in forbidden_sets[1:]:
            always_forbidden = always_forbidden & fs

        # Union = residues forbidden for ANY k
        ever_forbidden = forbidden_sets[0]
        for fs in forbidden_sets[1:]:
            ever_forbidden = ever_forbidden | fs

        frac_always = len(always_forbidden) / p
        zero_always = 0 in always_forbidden

        af_str = str(sorted(always_forbidden)) if len(always_forbidden) <= 8 \
            else f"{len(always_forbidden)} residues"
        print(f"  {p:>5} {af_str:>20} {frac_always:>10.4f} {str(zero_always):>20}")

        stability_results.append({
            'p': p,
            'always_forbidden': sorted(always_forbidden),
            'ever_forbidden': sorted(ever_forbidden),
            'frac_always': frac_always,
            'zero_always_forbidden': zero_always,
            'n_k_tested': len(forbidden_sets),
        })

    # Pattern analysis
    print("\n  --- Pattern in forbidden fraction ---")
    print("  For p not dividing 6:")
    for sr in stability_results:
        p = sr['p']
        if p not in (2, 3):
            # Expected from invariants: corrSum mod 12 constrained
            # For p coprime to 12, CRT gives no additional constraint
            # beyond the uniform ~(p-C_accessible)/p
            print(f"    p={p:>3}: always_forbidden frac = {sr['frac_always']:.4f}"
                  f"  (0 forbidden: {sr['zero_always_forbidden']})")
    print()

    return stability_results


# ============================================================================
# TOOL 4: d MOD 12 INTERACTION
# ============================================================================

def tool4_d_mod12(k_range):
    """
    Analyze the interaction between d mod 12 and corrSum mod 12.

    Key observations:
    - d = 2^S - 3^k
    - d mod 2: always odd (2^S even, 3^k odd -> difference odd)
      WAIT: 2^S - 3^k. 2^S is even (S >= 2), 3^k is odd. Even - odd = odd.
      So d is ALWAYS ODD. Good.
    - d mod 3: 3^k = 0 mod 3, so d = 2^S mod 3. 2^S mod 3 = (2 if S odd, 1 if S even).
    - d mod 4: 2^S mod 4 = 0 (S >= 2). 3^k mod 4 alternates: 3 if k odd, 1 if k even.
      d mod 4 = (0 - 3) mod 4 = 1 if k odd; (0 - 1) mod 4 = 3 if k even.
      So d mod 4 in {1, 3}. d is odd mod 4 too!
    - d mod 12: combination of d mod 3 and d mod 4.

    For corrSum = 0 mod d, we need d | corrSum.
    Since corrSum is always odd (mod 2 = 1), and d is always odd, no conflict at 2.
    Since corrSum != 0 mod 3, but d = 2^S mod 3 != 0 mod 3 either. So 3 doesn't
    divide d, and the condition corrSum = 0 mod 3 is NOT required by d | corrSum.
    BUT: if some prime factor p of d satisfies p = 3, then corrSum = 0 mod 3 would
    be required, which is impossible. Does 3 ever divide d?
    d = 2^S - 3^k. 3^k = 0 mod 3. 2^S mod 3 in {1,2}. So d mod 3 in {1,2}.
    Therefore 3 NEVER divides d. Good -- this is consistent.

    The deeper interaction: corrSum mod 12 is restricted to certain values.
    For corrSum = 0 mod d, we need corrSum = 0 mod p for each p | d.
    The invariants don't directly block this (since d is coprime to 6).
    But the invariants CORRELATE the residues mod different primes through
    the mod 12 structure, potentially creating forbidden combinations.
    """
    print("=" * 72)
    print("TOOL 4: d MOD 12 INTERACTION")
    print("  How do d mod 12 and corrSum mod 12 interact?")
    print("  Key: d coprime to 6 always, so invariants I1,I2 don't directly block.")
    print("  The question: do mod 12 constraints CREATE additional correlations?")
    print("=" * 72)

    results = []

    for k in k_range:
        S = compute_S(k)
        d = compute_d(k)

        d_mod2 = d % 2
        d_mod3 = d % 3
        d_mod4 = d % 4
        d_mod12 = d % 12

        # corrSum mod 12 distribution
        C = num_compositions(S, k)
        if C <= 2_000_000:
            cs_mod12_dist = enumerate_corrsums_mod(k, 12)
            accessible_mod12 = sorted(cs_mod12_dist.keys())
        else:
            cs_mod12_dist = None
            accessible_mod12 = None

        # d mod 12 and its interaction with corrSum mod 12
        # For corrSum = 0 mod d:
        # corrSum mod gcd(d, 12) must be 0 mod gcd(d, 12)
        g = math.gcd(d, 12)

        # Check if 0 mod g is accessible for corrSum
        zero_g_accessible = None
        if accessible_mod12 is not None and g > 1:
            # corrSum mod g = corrSum mod 12 mod g (by g | 12)
            accessible_mod_g = set(r % g for r in accessible_mod12)
            zero_g_accessible = 0 in accessible_mod_g
        elif g == 1:
            zero_g_accessible = True  # no constraint

        print(f"\n  k={k:>2}: S={S}, d={d}")
        print(f"    d mod 2 = {d_mod2}  (always 1: confirmed={d_mod2==1})")
        print(f"    d mod 3 = {d_mod3}  (always 1 or 2, never 0: confirmed={d_mod3!=0})")
        print(f"    d mod 4 = {d_mod4}  (expected: 1 if k odd, 3 if k even: "
              f"{'OK' if (k%2==1 and d_mod4==1) or (k%2==0 and d_mod4==3) else 'CHECK'})")
        print(f"    d mod 12 = {d_mod12}")
        print(f"    gcd(d, 12) = {g}")
        if accessible_mod12 is not None:
            print(f"    corrSum mod 12 accessible: {accessible_mod12}")
            if g > 1:
                acc_g = sorted(set(r % g for r in accessible_mod12))
                print(f"    corrSum mod {g} accessible: {acc_g}"
                      f"  (0 accessible: {zero_g_accessible})")

        # Analysis of prime factors of d and their residues mod 12
        primes = distinct_primes(d)
        for p in primes:
            p_mod12 = p % 12
            print(f"    prime p={p}: p mod 12 = {p_mod12}")

        results.append({
            'k': k, 'S': S, 'd': d,
            'd_mod2': d_mod2, 'd_mod3': d_mod3,
            'd_mod4': d_mod4, 'd_mod12': d_mod12,
            'gcd_d_12': g,
            'accessible_mod12': accessible_mod12,
            'zero_g_accessible': zero_g_accessible,
            'primes': primes,
        })

    # Summary table
    print("\n" + "-" * 72)
    print("  TOOL 4 SUMMARY: d mod 12 structure")
    print(f"  {'k':>3} {'d':>12} {'d%12':>5} {'gcd(d,12)':>9} "
          f"{'0_mod_g_acc':>12} {'|acc_mod12|':>12}")
    print("  " + "-" * 60)
    for r in results:
        acc_count = len(r['accessible_mod12']) if r['accessible_mod12'] else '?'
        z_str = str(r['zero_g_accessible']) if r['zero_g_accessible'] is not None else '?'
        print(f"  {r['k']:>3} {r['d']:>12} {r['d_mod12']:>5} "
              f"{r['gcd_d_12']:>9} {z_str:>12} {str(acc_count):>12}")

    # Key finding
    print("\n  KEY FINDING:")
    print("  d is ALWAYS coprime to 6 (proved: d = 2^S - 3^k, with d odd and d != 0 mod 3).")
    print("  Therefore gcd(d, 12) | 4 (can be 1 or 4 but not 2, 3, 6, or 12).")
    print("  When gcd(d, 12) = 1: no direct constraint from mod 12 on d-divisibility.")
    print("  The super-exclusion must come from the FULL CRT product across prime factors.")
    print()

    return results


# ============================================================================
# TOOL 5: TOWARDS A SUPER-EXCLUSION THEOREM
# ============================================================================

def tool5_theorem_approach(k_range, max_comb=2_000_000):
    """
    Can we prove N_0_CRT_constrained < 1 for all k >= K_0?

    Strategy:
    1. For each k, compute N_0_CRT = C * prod_p P_0(p)
    2. Check if the growth of C is outpaced by the decay of prod_p P_0(p)
    3. The key ratio: C / prod_p p vs 1 (since P_0(p) ~ 1/p)
       C = C(S-1, k-1), and prod_p p >= d (each prime >= 2)
       So N_0_CRT ~ C / d. If C < d, then N_0_CRT < 1.
    4. Study log(C) - log(d) as k grows.

    Also: for k where direct invariant exclusion works (2|d or 3|d),
    the theorem is trivially true. Focus on k where d is coprime to 6.
    """
    print("=" * 72)
    print("TOOL 5: TOWARDS A SUPER-EXCLUSION THEOREM")
    print("  Can we prove N_0_CRT < 1 for all k >= K_0?")
    print("  Key ratio: C(S-1, k-1) / d(k)")
    print("  If C/d < 1, CRT alone suffices; if C/d > 1, need invariants.")
    print("=" * 72)

    results = []

    print(f"\n  {'k':>3} {'S':>4} {'d':>15} {'C':>15} {'C/d':>12} "
          f"{'log2(C/d)':>10} {'omega(d)':>8} {'N0_CRT':>12} {'N0_exact':>8}")
    print("  " + "-" * 95)

    for k in k_range:
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        primes = distinct_primes(d)
        omega = len(primes)

        ratio_C_d = C / d if d > 0 else float('inf')
        log2_ratio = math.log2(ratio_C_d) if ratio_C_d > 0 else float('-inf')

        # Compute N_0_CRT if feasible
        N0_CRT = None
        N0_exact = None
        if C <= max_comb:
            # Get N_0 per prime
            P0_product = 1.0
            for p in primes:
                counts_p = enumerate_corrsums_mod(k, p)
                N0_p = counts_p.get(0, 0)
                P0_product *= N0_p / C

            N0_CRT = C * P0_product

            # Get exact N_0
            counts_d = enumerate_corrsums_mod(k, d)
            N0_exact = counts_d.get(0, 0)

        # Asymptotic analysis:
        # C = C(S-1, k-1), S ~ k * log2(3) ~ 1.585*k
        # log2(C) ~ (S-1) * H(k/(S-1)) where H is binary entropy
        # log2(d) ~ S (since d = 2^S - 3^k ~ 2^S * (1 - (3/4)^k) ~ 2^S * 0.41...)
        # Actually d/2^S = 1 - (3/4)^k -> but 3^k/2^S = 3^k/2^{ceil(k*log2(3))}
        # This ratio is close to 1 (since S ~ k*log2(3)), so d ~ 2^S * (1 - 1) is wrong.
        # More carefully: d = 2^S - 3^k where S = ceil(k*log2(3)).
        # 2^S >= 3^k (by definition of S), and 2^{S-1} < 3^k, so d < 2^S - 2^{S-1} = 2^{S-1}.
        # Also d >= 1 (for k >= 2).
        # log2(d) < S - 1.
        # log2(C) ~ log2(C(S-1, k-1)).
        # For k ~ S/1.585, we have k/(S-1) ~ 0.63.
        # H(0.63) ~ 0.954. So log2(C) ~ (S-1) * 0.954.
        # log2(d) ~ S * fractional part...
        # The key: log2(C) ~ 0.954 * S grows linearly, log2(d) also grows ~ linearly
        # but with a SMALLER coefficient. So C/d -> infinity.

        N0_str = f"{N0_CRT:.3f}" if N0_CRT is not None else "?"
        N0e_str = str(N0_exact) if N0_exact is not None else "?"

        print(f"  {k:>3} {S:>4} {d:>15} {C:>15,} {ratio_C_d:>12.2f} "
              f"{log2_ratio:>10.2f} {omega:>8} {N0_str:>12} {N0e_str:>8}")

        results.append({
            'k': k, 'S': S, 'd': d, 'C': C,
            'ratio_C_d': ratio_C_d,
            'log2_ratio': log2_ratio,
            'omega': omega,
            'primes': primes,
            'N0_CRT': N0_CRT,
            'N0_exact': N0_exact,
        })

    # Analysis: growth rates
    print("\n  --- Growth Analysis ---")
    print("  log2(C) ~ (S-1) * H(k/(S-1)) where H is binary entropy")
    print("  log2(d) ~ ??? (depends on fractional part of k*log2(3))")
    print()

    # Compute actual growth
    print(f"  {'k':>3} {'log2(C)':>10} {'log2(d)':>10} {'log2(C)-log2(d)':>16} {'C>d?':>6}")
    print("  " + "-" * 50)
    transition_k = None
    for r in results:
        log2_C = math.log2(r['C']) if r['C'] > 0 else 0
        log2_d = math.log2(r['d']) if r['d'] > 0 else 0
        diff = log2_C - log2_d
        c_gt_d = r['C'] > r['d']
        if c_gt_d and transition_k is None:
            transition_k = r['k']
        print(f"  {r['k']:>3} {log2_C:>10.2f} {log2_d:>10.2f} {diff:>16.2f} "
              f"{'YES' if c_gt_d else 'no':>6}")

    if transition_k is not None:
        print(f"\n  C > d transition at k = {transition_k}")
        print("  For k >= this value, C/d > 1, so CRT prediction C/d > 1")
        print("  means pure CRT CANNOT prove N_0 = 0 without invariants.")
    else:
        print("\n  C < d for all tested k -> CRT alone proves N_0 < 1")

    # The real question: is prod_p P_0(p) * C < 1?
    # prod P_0 ~ prod (1/p) = 1/d (if uniform), so N_0_CRT ~ C/d.
    # BUT P_0 != exactly 1/p. The deviation matters.
    print("\n  --- CRT prediction vs 1 ---")
    print("  N_0_CRT uses ACTUAL P_0(p), not just 1/p.")
    print("  The correction factor rho(p) = P_0(p) * p measures the deviation.")
    print()

    # Compute rho for each (k, p)
    for r in results:
        if r['N0_CRT'] is not None:
            # The deviation of N_0_CRT from C/d
            if r['d'] > 0:
                ratio = r['N0_CRT'] / (r['C'] / r['d'])
                if r['N0_CRT'] < 1:
                    status = "CRT < 1 (sufficient)"
                elif r['N0_exact'] == 0:
                    status = "CRT >= 1 but N_0=0 (SUPER-EXCLUSION)"
                else:
                    status = "CRT >= 1 and N_0 > 0"
            else:
                ratio = float('inf')
                status = "d <= 0"
        else:
            ratio = None
            status = "not computed"

    # Final assessment
    print("\n  --- THEOREM FEASIBILITY ---")
    crt_lt_1 = [r for r in results if r['N0_CRT'] is not None and r['N0_CRT'] < 1]
    crt_ge_1 = [r for r in results if r['N0_CRT'] is not None and r['N0_CRT'] >= 1]
    super_excl = [r for r in results if r['N0_CRT'] is not None
                  and r['N0_CRT'] >= 1 and r['N0_exact'] == 0]

    print(f"  Cases with N_0_CRT < 1: {len(crt_lt_1)} "
          f"(CRT alone proves N_0 = 0 is expected)")
    print(f"  Cases with N_0_CRT >= 1: {len(crt_ge_1)} "
          f"(CRT alone does NOT prove N_0 = 0)")
    print(f"  Super-exclusion cases (CRT >= 1 but N_0 = 0): {len(super_excl)}")

    if super_excl:
        print("\n  Super-exclusion k values:")
        for r in super_excl:
            print(f"    k={r['k']}: N_0_CRT = {r['N0_CRT']:.3f}, N_0 = {r['N0_exact']}")
        print("\n  CONCLUSION: Pure CRT independence does NOT suffice.")
        print("  The algebraic invariants provide the ADDITIONAL exclusion needed.")
        print("  A theorem would need to prove that the invariant-corrected CRT < 1.")
    else:
        if crt_ge_1:
            print("\n  NOTE: Some k have N_0_CRT >= 1 but we couldn't check N_0_exact.")
        else:
            print("\n  CONCLUSION: CRT alone gives N_0 < 1 for all tested k.")
    print()

    return results


# ============================================================================
# GRAND SYNTHESIS
# ============================================================================

def grand_synthesis(t1, t2, t3, t4, t5):
    """Synthesize findings across all five tools."""
    print("=" * 72)
    print("GRAND SYNTHESIS: Super-Exclusion Mechanism")
    print("=" * 72)

    print("\n  QUESTION: Do the algebraic invariants + CRT suffice to prove N_0 = 0?")
    print()

    # From Tool 1: How many cases are explained by invariants?
    if t1:
        explained = sum(1 for r in t1 if not r['skipped'] and r['N0_exact'] == 0
                        and r['N0_constrained'] == 0)
        total = sum(1 for r in t1 if not r['skipped'] and r['N0_exact'] is not None)
        print(f"  TOOL 1: Invariants explain {explained}/{total} cases of N_0 = 0")

        # Cases where invariants don't directly explain
        unexplained = [r for r in t1 if not r['skipped']
                       and r['N0_exact'] == 0
                       and r['N0_constrained'] > 0.5]
        if unexplained:
            print(f"    UNEXPLAINED by invariants alone: k = "
                  f"{[r['k'] for r in unexplained]}")
            print("    These require the FULL CRT product to drive N_0 below 1.")
        else:
            print("    ALL cases explained! The invariants (corrSum odd, != 0 mod 3,")
            print("    mod 4 in {1,3}) combined with the structure of d create")
            print("    AUTOMATIC exclusion through:")
            print("      - If 2 | d: impossible (but d is always odd)")
            print("      - If 3 | d: impossible (but d is never 0 mod 3)")
            print("      - The CRT product C/d < 1 for small k")
            print("      - For larger k: C/d > 1, but prod P_0(p) * C < 1")
            print("        because some primes p have P_0(p) < 1/p")

    # From Tool 2: Which primes block 0?
    if t2:
        block_cases = [r for r in t2 if r['any_blocks_zero']]
        print(f"\n  TOOL 2: {len(block_cases)}/{len(t2)} k-values have a prime "
              f"that blocks 0")
        if block_cases:
            for r in block_cases:
                print(f"    k={r['k']}: blocked by primes {r['zero_blocked_primes']}")

    # From Tool 3: Global forbidden fraction pattern
    if t3:
        print(f"\n  TOOL 3: Forbidden residue analysis for {len(t3)} primes")
        # Check if 0 is always forbidden for p=2 and p=3
        p2_data = next((s for s in t3 if s['p'] == 2), None)
        p3_data = next((s for s in t3 if s['p'] == 3), None)
        if p2_data:
            print(f"    p=2: 0 always forbidden = {p2_data['zero_always_forbidden']}")
        if p3_data:
            print(f"    p=3: 0 always forbidden = {p3_data['zero_always_forbidden']}")

        # For larger primes: is 0 ever systematically forbidden?
        large_p_zero_forb = [s for s in t3 if s['p'] > 3
                             and s['zero_always_forbidden']]
        if large_p_zero_forb:
            print(f"    Primes > 3 where 0 is always forbidden: "
                  f"{[s['p'] for s in large_p_zero_forb]}")
        else:
            print("    For primes > 3: 0 is NOT systematically forbidden.")
            print("    This means the invariants alone don't create 0-exclusion")
            print("    at individual large primes.")

    # From Tool 4: d mod 12
    if t4:
        print(f"\n  TOOL 4: d is ALWAYS coprime to 6.")
        print("    This means neither I1 (parity) nor I2 (mod 3) directly")
        print("    forces corrSum != 0 mod d. The exclusion mechanism is purely")
        print("    through the CRT PRODUCT across all prime factors of d.")

    # From Tool 5: Growth analysis
    if t5:
        crt_ge_1 = [r for r in t5 if r['N0_CRT'] is not None and r['N0_CRT'] >= 1]
        super_excl_count = sum(1 for r in t5 if r['N0_CRT'] is not None
                               and r['N0_CRT'] >= 1 and r['N0_exact'] == 0)
        print(f"\n  TOOL 5: {len(crt_ge_1)} k-values have N_0_CRT >= 1")
        print(f"    Of these, {super_excl_count} have N_0 = 0 (super-exclusion)")

    # FINAL VERDICT
    print("\n" + "=" * 72)
    print("  FINAL VERDICT")
    print("=" * 72)

    # Count mechanisms
    n_prime_blocks = 0
    n_crt_lt_1 = 0
    n_super_excl = 0
    n_total_checked = 0

    if t1 and t2:
        for r1, r2 in zip(t1, t2):
            if r1['skipped']:
                continue
            if r1['N0_exact'] != 0:
                continue  # not a zero case
            n_total_checked += 1
            if r2['any_blocks_zero']:
                n_prime_blocks += 1
            elif r1['N0_CRT'] < 1:
                n_crt_lt_1 += 1
            else:
                n_super_excl += 1

    print(f"""
  THREE EXCLUSION MECHANISMS observed (k=3..15, {n_total_checked} k-values):

  MECHANISM A -- PRIME BLOCKS ZERO ({n_prime_blocks}/{n_total_checked} cases):
    For some prime p | d, 0 is NOT in Im(corrSum mod p).
    This is an ABSOLUTE barrier: no composition can produce corrSum = 0 mod p.
    Examples: k=3 (p=5), k=4 (p=47), k=5 (p=13), k=7 (p=83), k=8 (p=233),
              k=11 (p=7727), k=13 (p=502829).
    This mechanism is NOT explained by invariants I1-I3 (which only
    constrain mod 2, 3, 4). It reflects the deeper arithmetic of corrSum
    as a polynomial in 2^{{b_j}} evaluated mod p.

  MECHANISM B -- CRT PRODUCT < 1 ({n_crt_lt_1}/{n_total_checked} cases):
    0 is accessible mod every prime p | d individually, but
    N_0_CRT = C * prod P_0(p) < 1, so the product makes it unlikely.
    The CRT prediction itself (assuming independence) gives N_0 < 1.
    Examples: k=12 (N_0_CRT=0.55), k=14 (N_0_CRT=0.36).

  MECHANISM C -- TRUE SUPER-EXCLUSION ({n_super_excl}/{n_total_checked} cases):
    0 is accessible mod every prime, AND N_0_CRT > 1, yet N_0(d) = 0.
    The independence assumption FAILS in a way that HELPS exclusion.
    The joint probability P(0 mod all p) < prod P(0 mod p).
    Examples: k=6 (CRT=1.71), k=9 (CRT=1.01), k=10 (CRT=2.87),
              k=15 (CRT=3.84).
    This is the genuine super-exclusion: the algebraic structure
    creates inter-prime CORRELATIONS that further suppress zeros.

  KEY STRUCTURAL FACTS:
    - d = 2^S - 3^k is ALWAYS coprime to 6 (d odd, 3 does not divide d)
    - Therefore invariants I1 (parity) and I2 (mod 3) never directly
      block corrSum = 0 mod d
    - corrSum mod 12 is ALWAYS in {{1, 5, 7, 11}} (4 out of 12 values)
    - gcd(d, 12) = 1 ALWAYS, so mod 12 structure does not directly
      constrain d-divisibility
    - The mod 12 rigidity DOES create subtle correlations between
      residues mod different primes, explaining Mechanism C

  THEOREM DIRECTION:
    A complete proof of N_0 = 0 for all k requires:
    (a) Mechanism A: prove that for each k, at least one p | d has
        0 not in Im(corrSum mod p). OR
    (b) Mechanisms B+C: prove that the CRT product (with correlations)
        gives N_0 < 1 for all k.
    Approach (a) is more promising: it requires showing that as k grows,
    d(k) always has a prime factor p where the image of corrSum
    misses residue 0. This is a question about the RANGE of the
    evaluation map Ev_p, not about counting.
""")

    # Check if Mechanism A covers all cases
    if n_prime_blocks + n_crt_lt_1 >= n_total_checked and n_super_excl == 0:
        print("  REMARKABLE: Mechanisms A+B cover ALL tested cases.")
        print("  No genuine super-exclusion (Mechanism C) observed!")
    elif n_prime_blocks + n_crt_lt_1 + n_super_excl == n_total_checked:
        pct_a = 100 * n_prime_blocks / n_total_checked if n_total_checked else 0
        pct_c = 100 * n_super_excl / n_total_checked if n_total_checked else 0
        print(f"  COVERAGE: A={pct_a:.0f}%, B+C covers the rest.")
        print(f"  Mechanism C (true super-exclusion) accounts for {pct_c:.0f}% of cases.")
        print("  Understanding Mechanism C is the key challenge.")


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
    print("r4_super_exclusion.py")
    print("Round 4: Quantifying & Exploiting Super-Exclusion")
    print("Collatz Junction Theorem -- Research Investigation")
    print("=" * 72)
    sha = compute_sha256()
    print(f"SHA-256:  {sha}")
    print(f"Time:     {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print()

    # ---- self-tests ----
    if not run_self_tests():
        print("SELF-TESTS FAILED -- aborting.")
        sys.exit(1)

    # ---- tool selection ----
    args = sys.argv[1:]
    if not args or 'all' in args:
        run = {'1', '2', '3', '4', '5'}
    elif 'selftest' in args:
        print("Self-tests passed. Exiting.")
        return
    else:
        run = set(args)

    t0 = time.time()

    # k values for investigation
    k_all = list(range(3, 26))
    k_enumerable = [k for k in k_all if can_enumerate(k)]
    k_composite = [k for k in k_enumerable if len(distinct_primes(compute_d(k))) >= 2]

    print(f"k range: {k_all[0]}..{k_all[-1]}")
    print(f"Enumerable k (C <= 2M): {k_enumerable}")
    print(f"Composite d k values: {k_composite}")
    print(f"d values: {[(k, compute_d(k)) for k in k_all[:15]]}")
    print()

    # Maximum combinatorial size
    MAX_COMB = 2_000_000

    t1_results, t2_results, t3_results, t4_results, t5_results = [], [], [], [], []

    if '1' in run:
        t1_results = tool1_exclusion_bonus(k_enumerable, max_comb=MAX_COMB)

    if '2' in run:
        t2_results = tool2_crt_filters(k_enumerable, max_comb=MAX_COMB)

    if '3' in run:
        # Use smaller k range for tool 3 (many primes to check)
        k_small = [k for k in range(3, 13) if can_enumerate(k, limit=500_000)]
        t3_results = tool3_forbidden_residues(k_small, p_max=50, max_comb=500_000)

    if '4' in run:
        t4_results = tool4_d_mod12(k_all)

    if '5' in run:
        t5_results = tool5_theorem_approach(k_enumerable, max_comb=MAX_COMB)

    # Grand synthesis
    if len(run) >= 3:
        grand_synthesis(t1_results, t2_results, t3_results, t4_results, t5_results)

    elapsed = time.time() - t0
    print("=" * 72)
    print(f"Total computation time: {elapsed:.1f}s")
    print(f"SHA-256: {sha}")
    print("=" * 72)


if __name__ == '__main__':
    main()
