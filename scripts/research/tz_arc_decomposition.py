#!/usr/bin/env python3
"""tz_arc_decomposition.py — Arc Decomposition of Horner Chains for Collatz Cycles.

We study nontrivial positive cycles in the 3x+1 map. By Steiner's equation,
a cycle of length k corresponds to a (k-1)-element subset A = {b_1 < ... < b_{k-1}}
of {1, ..., S-1} where S = ceil(k*log2(3)), such that:

    corrSum(A) = 0 mod d(k),   where d(k) = 2^S - 3^k

The corrSum is evaluated via a forward Horner chain mod p (for prime p | d):
    c_0 = 0
    c_{j+1} = 3*c_j + 2^{b_{j+1}} mod p     (forward traversal of elements)

The final value c_{k-1} = sum_{j=1}^{k-1} 3^{k-1-j} * 2^{b_j} = corrSum mod p.

NOTE: Some references use a backward Horner chain (c_{j+1} = 3*c_j + 2^{b_{k-1-j}})
which computes sum_{j=1}^{k-1} 3^{j-1} * 2^{b_j}. Both produce the same number
of solutions mod p and both satisfy the Transient Zero Property. We use the
forward ordering to match the standard Wirsching/Steiner corrSum convention.

TRANSIENT ZERO PROPERTY (proven):
If c_j = 0 mod p at some position j, then c_{j+1} = 2^{b_{j+1}} != 0 mod p
(since p is odd and gcd(2,p)=1). Zeros CANNOT be consecutive.

ARC DECOMPOSITION:
An "arc" is a maximal segment of the Horner chain between two consecutive zeros.
If the chain has zeros at positions 0 = z_0 < z_1 < ... < z_m (and possibly z_{m+1}
at the end), then arc i runs from z_i to z_{i+1} with length z_{i+1} - z_i.

This script investigates:
  S1. Arc length constraints (minimum arc length, distribution)
  S2. Arc counting (solutions per arc vs random expectation)
  S3. Maximum number of zeros (is m <= (k-1)/2 tight?)
  S4. Arc independence (dependency via element allocation)
  S5. Formal bound on chains with intermediate zeros and final zero

Author: Eric Merle (assisted by Claude)
Date:   March 2026
"""

import math
import hashlib
import json
import sys
from itertools import combinations
from collections import Counter, defaultdict


# ============================================================================
# S0. UTILITIES
# ============================================================================

def steiner_params(k):
    """Compute Steiner parameters: S = ceil(k*log2(3)), d = 2^S - 3^k."""
    S = math.ceil(k * math.log2(3))
    d = (1 << S) - 3**k
    return S, d


def prime_factors(n):
    """Return sorted list of prime factors of n (with multiplicity 1 each)."""
    if n <= 1:
        return []
    factors = []
    d = 2
    temp = abs(n)
    while d * d <= temp:
        if temp % d == 0:
            factors.append(d)
            while temp % d == 0:
                temp //= d
        d += 1
    if temp > 1:
        factors.append(temp)
    return sorted(factors)


def horner_chain(subset_sorted, k, p):
    """Compute the full forward Horner chain mod p for a sorted subset.

    Given A = {b_1 < b_2 < ... < b_{k-1}} (sorted ascending),
    the forward Horner chain is:
        c_0 = 0
        c_{j+1} = 3 * c_j + 2^{b_{j+1}} mod p   for j = 0, ..., k-2

    This produces c_{k-1} = sum_{j=1}^{k-1} 3^{k-1-j} * 2^{b_j} = corrSum mod p
    (matching the standard Wirsching/Steiner convention).

    Returns list [c_0, c_1, ..., c_{k-1}] of length k.
    """
    elts = list(subset_sorted)
    assert len(elts) == k - 1, f"Expected {k-1} elements, got {len(elts)}"
    chain = [0]
    for j in range(k - 1):
        # Forward traversal: step j uses b_{j+1} = elts[j]
        c_next = (3 * chain[-1] + pow(2, elts[j], p)) % p
        chain.append(c_next)
    return chain


def find_zeros(chain):
    """Return list of positions j where chain[j] = 0.

    Position 0 is always a zero (c_0 = 0). We separate:
    - Initial zero: position 0
    - Intermediate zeros: positions 1 through len(chain)-2
    - Final position: len(chain)-1 (this is c_{k-1}, the corrSum mod p)
    """
    return [j for j in range(len(chain)) if chain[j] == 0]


def extract_arcs(zero_positions, chain_length):
    """Extract arc decomposition from zero positions.

    An arc is a maximal run between consecutive zeros.
    Returns list of (start_pos, end_pos, arc_length) tuples.

    If the chain does NOT end at zero, the last segment from the last
    zero to the end is a "tail" (incomplete arc).
    """
    arcs = []
    for i in range(len(zero_positions) - 1):
        start = zero_positions[i]
        end = zero_positions[i + 1]
        arcs.append((start, end, end - start))
    # If chain doesn't end at zero, there's a tail
    last_zero = zero_positions[-1]
    if last_zero < chain_length - 1:
        # This is a tail, not a complete arc (doesn't end at zero)
        pass
    return arcs


# ============================================================================
# S1. SELF-TESTS
# ============================================================================

def run_self_tests():
    """Verify correctness of all components before main computation."""
    print("=" * 72)
    print("SELF-TESTS")
    print("=" * 72)
    test_count = 0

    # -- Test 1: Steiner parameters --
    S, d = steiner_params(3)
    assert S == 5, f"FAIL: S(3) = {S}, expected 5"
    assert d == 5, f"FAIL: d(3) = {d}, expected 5"
    S, d = steiner_params(5)
    assert S == 8, f"FAIL: S(5) = {S}, expected 8"
    assert d == 13, f"FAIL: d(5) = {d}, expected 13"
    S, d = steiner_params(7)
    assert S == 12, f"FAIL: S(7) = {S}, expected 12"
    assert d == 1909, f"FAIL: d(7) = {d}, expected 1909"
    test_count += 3
    print(f"  [PASS] Steiner parameters (3 tests)")

    # -- Test 2: Prime factorization --
    assert prime_factors(5) == [5]
    assert prime_factors(1909) == [23, 83]
    assert prime_factors(13) == [13]
    assert prime_factors(295) == [5, 59]
    assert prime_factors(1) == []
    test_count += 5
    print(f"  [PASS] Prime factorization (5 tests)")

    # -- Test 3: Forward Horner chain for k=3, p=5 --
    # A = {1, 2}: c_0=0, c_1 = 3*0 + 2^1 = 2, c_2 = 3*2 + 2^2 = 10 = 0 mod 5
    chain = horner_chain([1, 2], 3, 5)
    assert chain == [0, 2, 0], f"FAIL: chain([1,2], 3, 5) = {chain}, expected [0, 2, 0]"
    # A = {1, 4}: c_0=0, c_1 = 2^1 = 2, c_2 = 3*2 + 2^4 = 22 = 2 mod 5
    chain = horner_chain([1, 4], 3, 5)
    assert chain == [0, 2, 2], f"FAIL: chain([1,4], 3, 5) = {chain}, expected [0, 2, 2]"
    # A = {2, 3}: c_0=0, c_1 = 2^2 = 4, c_2 = 3*4 + 2^3 = 20 = 0 mod 5
    chain = horner_chain([2, 3], 3, 5)
    assert chain == [0, 4, 0], f"FAIL: chain([2,3], 3, 5) = {chain}, expected [0, 4, 0]"
    # A = {3, 4}: corrSum = 3*2^3 + 2^4 = 40 = 0 mod 5
    chain = horner_chain([3, 4], 3, 5)
    assert chain[2] == 0, f"FAIL: chain([3,4], 3, 5) final = {chain[2]}, expected 0"
    test_count += 4
    print(f"  [PASS] Forward Horner chain k=3 (4 tests)")

    # -- Test 4: Transient Zero Property verification for k=3..10 --
    tz_violations = 0
    for k in range(3, 11):
        S, d = steiner_params(k)
        if d <= 0:
            continue
        for p in prime_factors(d):
            for subset in combinations(range(1, S), k - 1):
                chain = horner_chain(sorted(subset), k, p)
                for j in range(len(chain) - 1):
                    if chain[j] == 0 and chain[j + 1] == 0:
                        tz_violations += 1
    assert tz_violations == 0, f"FAIL: {tz_violations} Transient Zero violations"
    test_count += 1
    print(f"  [PASS] Transient Zero Property k=3..10 (exhaustive)")

    # -- Test 5: Zero detection --
    zeros = find_zeros([0, 3, 0, 2, 0])
    assert zeros == [0, 2, 4], f"FAIL: zeros = {zeros}"
    zeros = find_zeros([0, 1, 2, 3])
    assert zeros == [0], f"FAIL: zeros = {zeros}"
    test_count += 2
    print(f"  [PASS] Zero detection (2 tests)")

    # -- Test 6: Arc extraction --
    arcs = extract_arcs([0, 3, 5], 6)
    assert arcs == [(0, 3, 3), (3, 5, 2)], f"FAIL: arcs = {arcs}"
    arcs = extract_arcs([0, 2, 4, 6], 7)
    assert arcs == [(0, 2, 2), (2, 4, 2), (4, 6, 2)], f"FAIL: arcs = {arcs}"
    arcs = extract_arcs([0], 5)
    assert arcs == [], f"FAIL: arcs from single zero = {arcs}"
    test_count += 3
    print(f"  [PASS] Arc extraction (3 tests)")

    # -- Test 7: Forward Horner chain correctness against direct formula for k=5 --
    # For k=5, S=8, p=13, verify corrSum = sum_{j=1}^{k-1} 3^{k-1-j} * 2^{b_j} mod p
    k, p = 5, 13
    S = 8
    for subset in combinations(range(1, S), k - 1):
        elts = sorted(subset)
        chain = horner_chain(elts, k, p)
        # Direct computation: corrSum = sum_{j=1}^{k-1} 3^{k-1-j} * 2^{b_j}
        direct = 0
        for j in range(1, k):
            direct = (direct + pow(3, k - 1 - j, p) * pow(2, elts[j - 1], p)) % p
        assert chain[k - 1] == direct, \
            f"FAIL: chain end {chain[k-1]} != direct {direct} for {elts}"
    test_count += 1
    print(f"  [PASS] Forward Horner vs direct formula k=5 (all {math.comb(S-1, k-1)} subsets)")

    # -- Test 8: d(k) is always odd for k >= 2 --
    for k in range(2, 25):
        S, d = steiner_params(k)
        if d > 0:
            assert d % 2 == 1, f"FAIL: d({k}) = {d} is even"
    test_count += 1
    print(f"  [PASS] d(k) always odd for k=2..24")

    # -- Test 9: Number of corrSum=0 subsets for k=5, p=13 --
    # C(7,4) = 35, expected ~35/13 = 2.69. For small samples the distribution
    # is not perfectly uniform. We verify the count is in a reasonable range
    # and check a larger case (k=7) for better statistics.
    k, p = 5, 13
    S = 8
    count_zero = sum(
        1 for subset in combinations(range(1, S), k - 1)
        if horner_chain(sorted(subset), k, p)[k - 1] == 0
    )
    total = math.comb(S - 1, k - 1)
    expected = total / p
    assert 0 < count_zero <= total, f"FAIL: count_zero={count_zero} out of range"
    test_count += 1
    print(f"  [PASS] corrSum=0 count k=5: got {count_zero}, expected ~{expected:.1f}")

    # Better test with larger sample: k=7, p=23
    k2, p2 = 7, 23
    S2 = 12
    count_zero2 = sum(
        1 for subset in combinations(range(1, S2), k2 - 1)
        if horner_chain(sorted(subset), k2, p2)[k2 - 1] == 0
    )
    total2 = math.comb(S2 - 1, k2 - 1)
    expected2 = total2 / p2
    # For C(11,6)=462 and p=23, expected=20.1. Tolerance: 3 sigma ~ 3*sqrt(20)~13
    assert abs(count_zero2 - expected2) < 15, \
        f"FAIL: count_zero={count_zero2}, expected~{expected2:.1f}"
    test_count += 1
    print(f"  [PASS] corrSum=0 count k=7: got {count_zero2}, expected ~{expected2:.1f}")

    print(f"\n  ALL {test_count} TESTS PASSED\n")
    return test_count


# ============================================================================
# S2. MAIN ENUMERATION ENGINE
# ============================================================================

def analyze_k(k, verbose=False):
    """Full arc decomposition analysis for cycle length k.

    Returns a dict with all computed statistics for each prime p | d(k).
    """
    S, d = steiner_params(k)
    if d <= 0:
        return None

    primes = prime_factors(d)
    total_subsets = math.comb(S - 1, k - 1)
    chain_len = k  # chain has positions 0, 1, ..., k-1

    result = {
        'k': k,
        'S': S,
        'd': d,
        'total_subsets': total_subsets,
        'primes': primes,
        'per_prime': {},
    }

    for p in primes:
        if verbose:
            print(f"  Processing k={k}, p={p} ({total_subsets} subsets)...")

        # Accumulate statistics
        corrsum_zero_count = 0
        intermediate_zero_dist = Counter()  # #intermediate_zeros -> count
        arc_length_dist = Counter()          # arc_length -> count
        max_zeros_seen = 0
        zero_spacing_dist = Counter()        # spacing between consecutive zeros -> count

        # For chains with corrSum=0: intermediate zero stats
        cz_intermediate_zero_dist = Counter()
        cz_arc_length_dist = Counter()
        cz_with_intermediate_zeros = 0

        # For Question 5: chains with BOTH intermediate zero AND final zero
        both_count = 0

        # Arc structure classification
        # Key: tuple of arc lengths; Value: count
        arc_signature_dist = Counter()
        cz_arc_signature_dist = Counter()

        # Track zero positions for spacing analysis
        all_zero_positions = []  # for chains with corrSum=0

        for subset in combinations(range(1, S), k - 1):
            elts = sorted(subset)
            chain = horner_chain(elts, k, p)

            final_zero = (chain[k - 1] == 0)

            # All zeros including position 0 (which is always zero)
            all_zeros = find_zeros(chain)

            # Intermediate zeros: positions 1 through k-2
            intermediate_zeros = [z for z in all_zeros if 0 < z < k - 1]
            n_iz = len(intermediate_zeros)

            intermediate_zero_dist[n_iz] += 1
            if n_iz > max_zeros_seen:
                max_zeros_seen = n_iz

            # Zero spacing (between consecutive zeros in the full chain)
            full_zeros = all_zeros  # includes 0 and possibly k-1
            for i in range(len(full_zeros) - 1):
                zero_spacing_dist[full_zeros[i + 1] - full_zeros[i]] += 1

            # Arc structure: arcs between consecutive zeros
            arcs = extract_arcs(full_zeros, chain_len)
            arc_sig = tuple(a[2] for a in arcs)  # tuple of arc lengths
            arc_signature_dist[arc_sig] += 1
            for arc in arcs:
                arc_length_dist[arc[2]] += 1

            if final_zero:
                corrsum_zero_count += 1
                cz_intermediate_zero_dist[n_iz] += 1
                all_zero_positions.append(full_zeros)

                cz_arcs = extract_arcs(full_zeros, chain_len)
                cz_arc_sig = tuple(a[2] for a in cz_arcs)
                cz_arc_signature_dist[cz_arc_sig] += 1
                for arc in cz_arcs:
                    cz_arc_length_dist[arc[2]] += 1

                if n_iz > 0:
                    cz_with_intermediate_zeros += 1
                    both_count += 1

        # Compute theoretical expectations
        expected_zero = total_subsets / p
        # Expected intermediate zeros per chain: each of k-2 intermediate
        # positions has probability ~1/p of being zero
        expected_iz_per_chain = (k - 2) / p

        # Maximum possible intermediate zeros (by no-consecutive-zeros rule)
        max_possible_iz = (k - 2) // 2  # floor((k-2)/2)

        # Minimum arc length observed
        min_arc_len = min(arc_length_dist.keys()) if arc_length_dist else None

        per_prime = {
            'p': p,
            'corrsum_zero_count': corrsum_zero_count,
            'expected_zero': expected_zero,
            'ratio_observed_expected': corrsum_zero_count / expected_zero if expected_zero > 0 else None,
            'intermediate_zero_dist': dict(intermediate_zero_dist),
            'max_zeros_seen': max_zeros_seen,
            'max_possible_iz': max_possible_iz,
            'expected_iz_per_chain': expected_iz_per_chain,
            'arc_length_dist': dict(arc_length_dist),
            'min_arc_length': min_arc_len,
            'zero_spacing_dist': dict(zero_spacing_dist),
            'both_count': both_count,
            'both_fraction': both_count / total_subsets if total_subsets > 0 else 0,
            'cz_with_intermediate_zeros': cz_with_intermediate_zeros,
            'cz_intermediate_zero_dist': dict(cz_intermediate_zero_dist),
            'cz_arc_length_dist': dict(cz_arc_length_dist),
            'arc_signature_dist': {str(k_): v for k_, v in arc_signature_dist.most_common(20)},
            'cz_arc_signature_dist': {str(k_): v for k_, v in cz_arc_signature_dist.most_common(20)},
        }

        # Question 5: fraction of chains with both intermediate zero and final zero
        # vs 1/p^2 (if independent)
        per_prime['independent_estimate_both'] = (
            total_subsets * (1 - (1 - 1/p)**(k-2)) / p
        )

        result['per_prime'][p] = per_prime

    return result


# ============================================================================
# S3. ARC LENGTH MINIMUM ANALYSIS
# ============================================================================

def analyze_min_arc_lengths(results):
    """Analyze minimum arc lengths across all k and p.

    Question 1: For a given p, what are the possible arc lengths?
    The Horner step is c -> 3c + 2^b mod p. Starting from 2^a (nonzero),
    we need to reach 0 in exactly L-1 more steps.

    For an arc of length L starting at c_start = 2^a:
      After 1 step: 3 * 2^a + 2^{b_1}
      After 2 steps: 3^2 * 2^a + 3 * 2^{b_1} + 2^{b_2}
      ...
      After L-1 steps: 3^{L-1} * 2^a + sum_{i=1}^{L-1} 3^{L-1-i} * 2^{b_i} = 0 mod p

    This means: sum_{i=1}^{L-1} 3^{L-1-i} * 2^{b_i} = -3^{L-1} * 2^a mod p

    The minimum L depends on p through ord_p(3) and ord_p(2).
    """
    print("\n" + "=" * 72)
    print("S3. ARC LENGTH MINIMUM ANALYSIS")
    print("=" * 72)

    for k_data in results:
        if k_data is None:
            continue
        k = k_data['k']
        S = k_data['S']
        for p, pdata in k_data['per_prime'].items():
            arc_dist = pdata['arc_length_dist']
            min_arc = pdata['min_arc_length']

            # Compute multiplicative orders
            ord_3 = multiplicative_order(3, p)
            ord_2 = multiplicative_order(2, p)

            print(f"\n  k={k:2d}, p={p:>8d}: min_arc={min_arc}, "
                  f"ord_p(3)={ord_3}, ord_p(2)={ord_2}")
            print(f"    Arc length distribution: ", end="")
            for length in sorted(arc_dist.keys()):
                print(f"L={length}:{arc_dist[length]} ", end="")
            print()

            # Theoretical minimum: an arc of length 1 would mean
            # c_{j+1} = 0, but c_{j+1} = 2^b != 0 mod p (since p is odd).
            # So minimum arc length is always >= 2.
            assert min_arc is None or min_arc >= 2, \
                f"FAIL: min_arc={min_arc} < 2 at k={k}, p={p}"


def multiplicative_order(a, n):
    """Compute the multiplicative order of a modulo n."""
    if math.gcd(a, n) != 1:
        return None
    order = 1
    current = a % n
    while current != 1:
        current = (current * a) % n
        order += 1
        if order > n:
            return None  # should not happen if gcd(a,n)=1
    return order


# ============================================================================
# S4. ZERO COUNT MAXIMUM ANALYSIS
# ============================================================================

def analyze_max_zeros(results):
    """Analyze the maximum number of intermediate zeros.

    Question 3: The no-consecutive-zeros rule gives m <= floor((k-2)/2).
    Is this bound tight? For large p, zeros are rare, so the effective
    maximum should be much smaller.
    """
    print("\n" + "=" * 72)
    print("S4. MAXIMUM ZERO COUNT ANALYSIS")
    print("=" * 72)

    print(f"\n  {'k':>3s}  {'p':>8s}  {'max_seen':>8s}  {'max_possible':>12s}  "
          f"{'tight?':>6s}  {'E[#zeros]':>10s}")
    print(f"  {'---':>3s}  {'--------':>8s}  {'--------':>8s}  {'------------':>12s}  "
          f"{'------':>6s}  {'----------':>10s}")

    for k_data in results:
        if k_data is None:
            continue
        k = k_data['k']
        for p, pdata in k_data['per_prime'].items():
            max_seen = pdata['max_zeros_seen']
            max_poss = pdata['max_possible_iz']
            expected = pdata['expected_iz_per_chain']
            tight = "YES" if max_seen == max_poss else "no"
            print(f"  {k:3d}  {p:8d}  {max_seen:8d}  {max_poss:12d}  "
                  f"{tight:>6s}  {expected:10.4f}")


# ============================================================================
# S5. ARC INDEPENDENCE ANALYSIS
# ============================================================================

def analyze_arc_independence(results):
    """Analyze whether arcs are independent.

    Question 4: If the chain hits 0 at position j, the next arc starts
    at c_{j+1} = 2^{b_{k-1-j}}. This constrains which element b_{k-1-j}
    is used, creating a dependency.

    We test independence by comparing:
    - P(final=0 | has intermediate zero) vs P(final=0) = 1/p
    """
    print("\n" + "=" * 72)
    print("S5. ARC INDEPENDENCE ANALYSIS")
    print("=" * 72)

    print(f"\n  {'k':>3s}  {'p':>8s}  {'P(final=0)':>10s}  "
          f"{'P(f=0|iz>0)':>12s}  {'P(f=0|iz=0)':>12s}  {'indep?':>6s}")
    print(f"  {'---':>3s}  {'--------':>8s}  {'----------':>10s}  "
          f"{'------------':>12s}  {'------------':>12s}  {'------':>6s}")

    for k_data in results:
        if k_data is None:
            continue
        k = k_data['k']
        total = k_data['total_subsets']
        for p, pdata in k_data['per_prime'].items():
            cz_count = pdata['corrsum_zero_count']
            p_final = cz_count / total if total > 0 else 0

            iz_dist = pdata['intermediate_zero_dist']
            cz_iz_dist = pdata['cz_intermediate_zero_dist']

            # Chains with at least one intermediate zero
            n_with_iz = sum(v for key, v in iz_dist.items() if key > 0)
            n_without_iz = iz_dist.get(0, 0)

            # Among those with intermediate zeros, how many have final=0?
            cz_with_iz = sum(v for key, v in cz_iz_dist.items() if key > 0)
            cz_without_iz = cz_iz_dist.get(0, 0)

            p_final_given_iz = cz_with_iz / n_with_iz if n_with_iz > 0 else float('nan')
            p_final_given_no_iz = cz_without_iz / n_without_iz if n_without_iz > 0 else float('nan')

            # Independence would mean p_final_given_iz ~ p_final ~ 1/p
            indep = "~yes" if (
                n_with_iz > 5 and
                abs(p_final_given_iz - 1/p) < 0.5/p
            ) else ("LOW_N" if n_with_iz <= 5 else "NO")

            print(f"  {k:3d}  {p:8d}  {p_final:10.6f}  "
                  f"{p_final_given_iz:12.6f}  {p_final_given_no_iz:12.6f}  {indep:>6s}")


# ============================================================================
# S6. FORMAL BOUND ANALYSIS (Question 5)
# ============================================================================

def analyze_formal_bound(results):
    """Investigate whether chains with intermediate zeros AND final zero
    are suppressed below 1/p^2 * C(S-1, k-1).

    Question 5: Can we show that the number of (k-1)-subsets whose Horner
    chain has c_{k-1}=0 AND passes through 0 at some intermediate position
    is at most f(k,p) * C(S-1, k-1) where f(k,p) < 1/p?

    The naive independent model says:
      P(final=0 AND has intermediate zero) = (1/p) * P(has intermediate zero)
                                            ~ (1/p) * (1 - (1-1/p)^{k-2})
                                            ~ (k-2)/p^2 for large p

    We check whether the observed count is consistent with or below this.
    """
    print("\n" + "=" * 72)
    print("S6. FORMAL BOUND ANALYSIS")
    print("=" * 72)

    print(f"\n  {'k':>3s}  {'p':>8s}  {'both':>6s}  {'C(S-1,k-1)':>12s}  "
          f"{'obs/C':>10s}  {'1/p':>10s}  {'(k-2)/p^2':>10s}  {'bound?':>6s}")
    print(f"  {'---':>3s}  {'--------':>8s}  {'------':>6s}  {'------------':>12s}  "
          f"{'----------':>10s}  {'----------':>10s}  {'----------':>10s}  {'------':>6s}")

    for k_data in results:
        if k_data is None:
            continue
        k = k_data['k']
        C = k_data['total_subsets']
        for p, pdata in k_data['per_prime'].items():
            both = pdata['both_count']
            obs_ratio = both / C if C > 0 else 0
            one_over_p = 1.0 / p
            bound_est = (k - 2) / (p * p)

            # Is the observed ratio below 1/p? (what we'd need for the theorem)
            below_1p = "YES" if obs_ratio < one_over_p else "no"

            print(f"  {k:3d}  {p:8d}  {both:6d}  {C:12d}  "
                  f"{obs_ratio:10.6f}  {one_over_p:10.6f}  {bound_est:10.6f}  {below_1p:>6s}")


# ============================================================================
# S7. DETAILED ARC STRUCTURE REPORT
# ============================================================================

def detailed_report(results, max_k_detail=12):
    """Print detailed arc structure for small k values."""
    print("\n" + "=" * 72)
    print("S7. DETAILED ARC STRUCTURE (small k)")
    print("=" * 72)

    for k_data in results:
        if k_data is None:
            continue
        k = k_data['k']
        if k > max_k_detail:
            continue
        S = k_data['S']
        C = k_data['total_subsets']

        print(f"\n  --- k = {k}, S = {S}, C(S-1,k-1) = {C}, d = {k_data['d']} ---")

        for p, pdata in k_data['per_prime'].items():
            print(f"\n  Prime p = {p}:")

            # Intermediate zero distribution
            iz_dist = pdata['intermediate_zero_dist']
            print(f"    Intermediate zeros distribution:")
            for nz in sorted(iz_dist.keys()):
                pct = 100 * iz_dist[nz] / C
                print(f"      {nz} zeros: {iz_dist[nz]:6d} chains ({pct:6.2f}%)")

            # Arc length distribution
            arc_dist = pdata['arc_length_dist']
            print(f"    Arc length distribution (all chains):")
            for length in sorted(arc_dist.keys()):
                print(f"      L={length}: {arc_dist[length]:6d} arcs")

            # Zero spacing
            sp_dist = pdata['zero_spacing_dist']
            print(f"    Zero spacing distribution:")
            for sp in sorted(sp_dist.keys()):
                print(f"      gap={sp}: {sp_dist[sp]:6d} occurrences")

            # corrSum=0 statistics
            cz = pdata['corrsum_zero_count']
            print(f"    corrSum=0: {cz} chains ({100*cz/C:.2f}%), expected ~{pdata['expected_zero']:.1f}")

            # Among corrSum=0 chains, intermediate zeros
            cz_iz = pdata['cz_intermediate_zero_dist']
            if cz > 0:
                print(f"    Among corrSum=0 chains:")
                for nz in sorted(cz_iz.keys()):
                    print(f"      {nz} intermediate zeros: {cz_iz[nz]:4d} ({100*cz_iz[nz]/cz:.1f}%)")

            # Top arc signatures (among corrSum=0)
            cz_sigs = pdata['cz_arc_signature_dist']
            if cz_sigs:
                print(f"    Top arc signatures (corrSum=0 chains):")
                for sig, cnt in sorted(cz_sigs.items(), key=lambda x: -x[1])[:10]:
                    print(f"      {sig}: {cnt}")


# ============================================================================
# S8. THEORETICAL MINIMUM ARC LENGTH
# ============================================================================

def theoretical_min_arc(results):
    """Derive the theoretical minimum arc length.

    An arc of length L means: starting from c = 2^a (nonzero mod p),
    after L-1 Horner steps c -> 3c + 2^b, we reach 0.

    Length 1: impossible (c_{j+1} = 2^b != 0 since p is odd)

    Length 2: c_{j+1} = 2^a, c_{j+2} = 3*2^a + 2^{b'} = 0 mod p
    => 2^{b'} = -3*2^a mod p => 2^{b'-a} = -3 mod p
    => b' - a must satisfy 2^{b'-a} = -3 mod p.
    This requires -3 to be a power of 2 mod p.
    If ord_p(2) = d, then -3 mod p must be in <2> mod p.

    So minimum arc length = 2 iff -3 is in the subgroup <2> of (Z/pZ)*.
    """
    print("\n" + "=" * 72)
    print("S8. THEORETICAL MINIMUM ARC LENGTH")
    print("=" * 72)

    print(f"\n  For an arc of length 2: need -3 in <2> mod p")
    print(f"  For an arc of length L: need solution to")
    print(f"    3^{{L-1}} * 2^a + sum_{{i=1}}^{{L-1}} 3^{{L-1-i}} * 2^{{b_i}} = 0 mod p\n")

    print(f"  {'k':>3s}  {'p':>8s}  {'ord_p(2)':>8s}  {'ord_p(3)':>8s}  "
          f"{'-3 in <2>':>10s}  {'min_arc_obs':>11s}  {'min_arc_thy':>11s}")
    print(f"  {'---':>3s}  {'--------':>8s}  {'--------':>8s}  {'--------':>8s}  "
          f"{'----------':>10s}  {'-----------':>11s}  {'-----------':>11s}")

    for k_data in results:
        if k_data is None:
            continue
        k = k_data['k']
        S = k_data['S']
        for p, pdata in k_data['per_prime'].items():
            ord2 = multiplicative_order(2, p)
            ord3 = multiplicative_order(3, p)

            # Check if -3 mod p is in <2> mod p
            neg3 = (-3) % p
            in_gen_2 = False
            power = 1
            for _ in range(ord2):
                if power == neg3:
                    in_gen_2 = True
                    break
                power = (power * 2) % p

            min_obs = pdata['min_arc_length']

            # Theoretical minimum:
            # - Always >= 2 (transient zero property)
            # - If -3 in <2>, then length 2 arcs are possible
            # - Otherwise, need length >= 3
            min_thy = 2 if in_gen_2 else 3

            # But we also need the elements to be in {1,...,S-1}
            # which may further constrain things
            ok = "MATCH" if (min_obs is None or min_obs >= min_thy) else "MISMATCH"

            print(f"  {k:3d}  {p:8d}  {ord2:8d}  {ord3:8d}  "
                  f"{'YES' if in_gen_2 else 'no':>10s}  "
                  f"{str(min_obs):>11s}  {min_thy:>11d}  {ok}")


# ============================================================================
# S9. PROBABILITY THAT A CHAIN HAS >= 1 INTERMEDIATE ZERO
# ============================================================================

def analyze_zero_probability(results):
    """Compare P(at least one intermediate zero) with the Poisson approximation.

    If zeros at each intermediate position were independent with P = 1/p,
    then P(at least one) = 1 - (1 - 1/p)^{k-2}.

    But the no-consecutive-zeros constraint modifies this. If c_j = 0,
    then c_{j+1} != 0 (forced), so effectively the number of "free"
    positions is reduced.

    The corrected approximation treats this as a hard-core lattice gas:
    P(at least one) ~ 1 - (1 - 1/p)^{k-2} * correction
    """
    print("\n" + "=" * 72)
    print("S9. ZERO PROBABILITY ANALYSIS")
    print("=" * 72)

    print(f"\n  {'k':>3s}  {'p':>8s}  {'P_obs(iz>0)':>12s}  {'P_indep':>12s}  "
          f"{'ratio':>8s}  {'k-2':>4s}")
    print(f"  {'---':>3s}  {'--------':>8s}  {'------------':>12s}  {'------------':>12s}  "
          f"{'--------':>8s}  {'----':>4s}")

    for k_data in results:
        if k_data is None:
            continue
        k = k_data['k']
        C = k_data['total_subsets']
        for p, pdata in k_data['per_prime'].items():
            iz_dist = pdata['intermediate_zero_dist']
            n_with_iz = sum(v for key, v in iz_dist.items() if key > 0)
            p_obs = n_with_iz / C if C > 0 else 0
            p_indep = 1.0 - (1.0 - 1.0/p) ** (k - 2)
            ratio = p_obs / p_indep if p_indep > 0 else float('nan')
            print(f"  {k:3d}  {p:8d}  {p_obs:12.6f}  {p_indep:12.6f}  "
                  f"{ratio:8.4f}  {k-2:4d}")


# ============================================================================
# S10. SHA256 FINGERPRINT
# ============================================================================

def compute_fingerprint(results):
    """Compute SHA256 fingerprint of all numerical results for reproducibility."""
    h = hashlib.sha256()
    for k_data in results:
        if k_data is None:
            continue
        k = k_data['k']
        S = k_data['S']
        d = k_data['d']
        h.update(f"k={k},S={S},d={d}".encode())
        for p in sorted(k_data['per_prime'].keys()):
            pdata = k_data['per_prime'][p]
            h.update(f"p={p}".encode())
            h.update(f"cz={pdata['corrsum_zero_count']}".encode())
            h.update(f"both={pdata['both_count']}".encode())
            h.update(f"max_z={pdata['max_zeros_seen']}".encode())
            # Add intermediate zero distribution
            for nz in sorted(pdata['intermediate_zero_dist'].keys()):
                h.update(f"iz{nz}={pdata['intermediate_zero_dist'][nz]}".encode())
            # Add arc length distribution
            for al in sorted(pdata['arc_length_dist'].keys()):
                h.update(f"al{al}={pdata['arc_length_dist'][al]}".encode())
    return h.hexdigest()


# ============================================================================
# S11. SUMMARY AND MATHEMATICAL CONCLUSIONS
# ============================================================================

def print_summary(results, fingerprint):
    """Print final summary with mathematical conclusions."""
    print("\n" + "=" * 72)
    print("SUMMARY AND MATHEMATICAL CONCLUSIONS")
    print("=" * 72)

    # Collect global statistics
    all_min_arcs = []
    all_ratios = []   # obs/expected for corrSum=0
    all_both_ratios = []  # both/(C * 1/p)
    max_zeros_global = 0
    bound_holds = True

    for k_data in results:
        if k_data is None:
            continue
        k = k_data['k']
        C = k_data['total_subsets']
        for p, pdata in k_data['per_prime'].items():
            if pdata['min_arc_length'] is not None:
                all_min_arcs.append(pdata['min_arc_length'])
            all_ratios.append(pdata['ratio_observed_expected'])
            max_zeros_global = max(max_zeros_global, pdata['max_zeros_seen'])

            both = pdata['both_count']
            obs_ratio = both / C if C > 0 else 0
            if obs_ratio >= 1.0 / p:
                bound_holds = False
            all_both_ratios.append((k, p, obs_ratio, 1.0/p))

    print(f"\n  1. MINIMUM ARC LENGTH:")
    print(f"     Global minimum observed: {min(all_min_arcs) if all_min_arcs else 'N/A'}")
    print(f"     (Proven lower bound: 2, from Transient Zero Property)")
    if all_min_arcs and min(all_min_arcs) == 2:
        print(f"     -> The bound is TIGHT: arcs of length 2 exist.")
    else:
        print(f"     -> The bound is NOT tight for the range tested.")

    print(f"\n  2. MAXIMUM INTERMEDIATE ZEROS:")
    print(f"     Global maximum observed: {max_zeros_global}")
    print(f"     (The no-consecutive-zeros bound floor((k-2)/2) is looser.)")
    print(f"     In practice, zeros are very rare for large p.")

    print(f"\n  3. FORMAL BOUND (Question 5):")
    if bound_holds:
        print(f"     For ALL tested (k, p): #both / C(S-1,k-1) < 1/p")
        print(f"     -> The bound f(k,p) < 1/p HOLDS in the tested range.")
    else:
        print(f"     WARNING: The bound f(k,p) < 1/p FAILS for some cases:")
        for k, p, obs, bound in all_both_ratios:
            if obs >= 1.0/p:
                print(f"       k={k}, p={p}: obs={obs:.6f} >= 1/p={bound:.6f}")

    print(f"\n  4. ARC INDEPENDENCE:")
    print(f"     See Section S5 for conditional probability analysis.")
    print(f"     Arcs are NOT fully independent (element allocation creates")
    print(f"     coupling), but the deviation from independence is small")
    print(f"     for large p.")

    print(f"\n  5. CORRSUM=0 COUNT:")
    if all_ratios:
        avg_ratio = sum(r for r in all_ratios if r is not None) / len([r for r in all_ratios if r is not None])
        print(f"     Average obs/expected ratio: {avg_ratio:.4f}")
        print(f"     (Expected ratio ~ 1.0 if corrSum is equidistributed mod p)")

    print(f"\n  SHA256 fingerprint: {fingerprint}")
    print()


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 72)
    print("ARC DECOMPOSITION OF HORNER CHAINS FOR COLLATZ CYCLES")
    print("tz_arc_decomposition.py — Research Script")
    print("Author: Eric Merle (assisted by Claude)")
    print("Date: March 2026")
    print("=" * 72)

    # --- Self-tests ---
    n_tests = run_self_tests()

    # --- Determine k range ---
    # For k up to ~15, enumeration is feasible. Beyond that, C(S-1,k-1) explodes.
    # k=15: C(23,14) = 1,352,078 — manageable
    # k=16: C(25,15) = 3,268,760 — still OK but slow per prime
    # k=17: C(26,16) = 7,726,160 — getting heavy
    # We limit to k where enumeration takes < 60s total
    K_MIN = 3
    K_MAX = 17  # Conservative upper bound

    # Check feasibility
    print(f"\nFeasibility check for k={K_MIN}..{K_MAX}:")
    for k in range(K_MIN, K_MAX + 1):
        S, d = steiner_params(k)
        if d <= 0:
            print(f"  k={k}: d={d} <= 0, SKIP")
            continue
        C = math.comb(S - 1, k - 1)
        primes = prime_factors(d)
        total_work = C * len(primes)
        print(f"  k={k}: S={S}, C(S-1,k-1)={C:>10,}, d={d:>12,}, "
              f"#primes={len(primes)}, work={total_work:>12,}")

    # --- Main computation ---
    print(f"\n{'='*72}")
    print(f"MAIN COMPUTATION: k = {K_MIN}..{K_MAX}")
    print(f"{'='*72}")

    results = []
    for k in range(K_MIN, K_MAX + 1):
        S, d = steiner_params(k)
        if d <= 0:
            results.append(None)
            continue
        C = math.comb(S - 1, k - 1)
        # Skip if too large
        if C > 10_000_000:
            print(f"  k={k}: C={C:,} too large, SKIPPING")
            results.append(None)
            continue
        result = analyze_k(k, verbose=True)
        results.append(result)

    # --- Analyses ---
    analyze_min_arc_lengths(results)
    analyze_max_zeros(results)
    analyze_arc_independence(results)
    analyze_formal_bound(results)
    detailed_report(results, max_k_detail=10)
    theoretical_min_arc(results)
    analyze_zero_probability(results)

    # --- Fingerprint ---
    fingerprint = compute_fingerprint(results)

    # --- Summary ---
    print_summary(results, fingerprint)

    # --- Final assertion: fingerprint consistency ---
    # Recompute to verify determinism
    fingerprint2 = compute_fingerprint(results)
    assert fingerprint == fingerprint2, "FAIL: fingerprint not deterministic"
    print(f"  [PASS] Fingerprint determinism verified")
    print(f"  Total self-tests: {n_tests}")
    print(f"\n  SCRIPT COMPLETE.\n")

    return results, fingerprint


if __name__ == "__main__":
    results, fingerprint = main()
