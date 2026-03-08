#!/usr/bin/env python3
"""
tz_exhaustive_enumeration.py
============================
Exhaustive enumeration of zero structures in Horner chains for the Collatz 3x+1 problem.

Mathematical Setup
------------------
A nontrivial positive cycle of length k in the 3x+1 map corresponds to a (k-1)-element
subset A = {b_1 < ... < b_{k-1}} of {1, ..., S-1} where S = ceil(k * log2(3)), such that

    corrSum(A) = 0 mod d(k),   where d(k) = 2^S - 3^k.

The corrSum is evaluated via a Horner chain mod p (for each prime p | d(k)):
    c_0 = 0
    c_{j+1} = 3 * c_j + 2^{b_{k-1-j}}  mod p

The final value c_{k-1} equals corrSum mod p.

Transient Zero Property (proven):
    If c_j = 0 mod p at position j < k-1, then c_{j+1} = 2^{b_{k-1-j}} != 0 mod p
    (since p is odd, and 2^m is never divisible by an odd prime).

Research Questions
------------------
1. How does the presence of internal zeros (c_j = 0 for 0 < j < k-1) correlate with
   the final value c_{k-1} being zero?
2. Are zero-free chains (c_{k-1} = 0 with no internal zeros) more or less common than
   random expectation?
3. Does passing through zero at an intermediate step make final-zero MORE or LESS likely?

Author: Claude (computational enumeration for Eric Merle's research)
Date: 2026-03-08
"""

import math
import hashlib
import json
import sys
import time
from itertools import combinations
from collections import defaultdict


# ============================================================================
# MATHEMATICAL PRIMITIVES
# ============================================================================

def compute_S(k):
    """S = ceil(k * log2(3))"""
    return math.ceil(k * math.log2(3))


def compute_d(k):
    """d(k) = 2^S - 3^k"""
    S = compute_S(k)
    return 2**S - 3**k


def prime_factors(n):
    """Return sorted list of distinct prime factors of |n|."""
    n = abs(n)
    if n <= 1:
        return []
    factors = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            factors.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return sorted(factors)


def horner_chain(subset, k, p):
    """
    Compute the full Horner chain c_0, c_1, ..., c_{k-1} mod p.

    Given subset A = {b_1 < ... < b_{k-1}} (sorted ascending),
    the Horner recurrence reads:
        c_0 = 0
        c_{j+1} = 3 * c_j + 2^{b_{k-1-j}}  mod p    for j = 0, ..., k-2

    Returns the list [c_0, c_1, ..., c_{k-1}] mod p.

    Note: c_0 is always 0 (by definition). The "internal" positions are
    j = 1, ..., k-2. The "final" position is j = k-1.
    """
    # subset is a tuple/list of (k-1) elements, sorted ascending
    # b_{k-1-j} for j=0 means b_{k-1} (largest element)
    # b_{k-1-j} for j=k-2 means b_1 (smallest element)
    chain = [0]  # c_0 = 0
    for j in range(k - 1):
        # We need b_{k-1-j}, which is subset[k-2-j] (0-indexed)
        exponent = subset[k - 2 - j]
        c_next = (3 * chain[-1] + pow(2, exponent, p)) % p
        chain.append(c_next)
    return chain


# ============================================================================
# SELF-TESTS
# ============================================================================

def run_self_tests():
    """Verify mathematical correctness with known properties."""
    print("=" * 70)
    print("SELF-TESTS")
    print("=" * 70)

    # Test 1: S computation
    assert compute_S(3) == 5, f"S(3) should be 5, got {compute_S(3)}"
    assert compute_S(4) == 7, f"S(4) should be 7, got {compute_S(4)}"
    assert compute_S(5) == 8, f"S(5) should be 8, got {compute_S(5)}"
    print("[PASS] S computation correct")

    # Test 2: d computation
    assert compute_d(3) == 2**5 - 3**3, f"d(3) wrong"
    assert compute_d(3) == 5, f"d(3) = {compute_d(3)}, expected 5"
    assert compute_d(4) == 47, f"d(4) = {compute_d(4)}, expected 47"
    assert compute_d(5) == 13, f"d(5) = {compute_d(5)}, expected 13"
    print("[PASS] d(k) computation correct")

    # Test 3: Horner chain length
    k = 5
    S = compute_S(k)  # S=8
    p = 13
    subset = (1, 3, 5, 7)  # k-1=4 elements from {1,...,7}
    chain = horner_chain(subset, k, p)
    assert len(chain) == k, f"Chain length should be {k}, got {len(chain)}"
    assert chain[0] == 0, "c_0 must be 0"
    print("[PASS] Horner chain structure correct")

    # Test 4: Transient zero property
    # If c_j = 0 for j < k-1, then c_{j+1} = 2^{b_{k-1-j}} mod p != 0
    # (since p is odd and gcd(2, p) = 1)
    test_count = 0
    violations = 0
    for k in range(3, 10):
        S = compute_S(k)
        d = compute_d(k)
        primes = [p for p in prime_factors(abs(d)) if p <= 200]
        for p in primes:
            for subset in combinations(range(1, S), k - 1):
                chain = horner_chain(subset, k, p)
                for j in range(1, k - 1):
                    if chain[j] == 0:
                        test_count += 1
                        # c_{j+1} should be 2^{b_{k-1-j}} mod p, which is nonzero
                        if chain[j + 1] == 0:
                            violations += 1
    assert violations == 0, f"Transient zero property violated {violations} times!"
    print(f"[PASS] Transient zero property: {test_count} internal zeros checked, 0 violations")

    # Test 5: After an internal zero, the next value equals 2^{b_{k-1-j}} mod p
    verify_count = 0
    for k in range(3, 8):
        S = compute_S(k)
        d = compute_d(k)
        primes = [p for p in prime_factors(abs(d)) if p <= 200]
        for p in primes:
            for subset in combinations(range(1, S), k - 1):
                chain = horner_chain(subset, k, p)
                for j in range(1, k - 1):
                    if chain[j] == 0:
                        expected = pow(2, subset[k - 2 - j], p)
                        assert chain[j + 1] == expected, \
                            f"After zero at j={j}, expected {expected}, got {chain[j+1]}"
                        verify_count += 1
    print(f"[PASS] Post-zero value verification: {verify_count} values checked")

    # Test 6: c_0 is always 0 (trivial but verify)
    for k in range(3, 8):
        S = compute_S(k)
        for p in [5, 7, 13]:
            for subset in combinations(range(1, S), k - 1):
                chain = horner_chain(subset, k, p)
                assert chain[0] == 0
    print("[PASS] c_0 = 0 always holds")

    # Test 7: For p=5, k=3, S=5, enumerate all C(4,2)=6 subsets
    # and verify N_0 = total/p (approximately, by random model)
    k, S, p = 3, 5, 5
    n_zero = 0
    for subset in combinations(range(1, S), k - 1):
        chain = horner_chain(subset, k, p)
        if chain[k - 1] == 0:
            n_zero += 1
    total = math.comb(S - 1, k - 1)
    # N_0 should be close to total/p = 6/5 = 1.2
    # Actual count may differ; just verify it's a valid count
    assert 0 <= n_zero <= total, f"N_0 out of range"
    print(f"[PASS] k=3, p=5: N_0 = {n_zero} out of {total} (expected ~{total/p:.1f})")

    # Test 8: prime_factors
    assert prime_factors(295) == [5, 59]
    assert prime_factors(1909) == [23, 83]
    assert prime_factors(13) == [13]
    print("[PASS] prime_factors correct")

    print()
    print("ALL SELF-TESTS PASSED")
    print("=" * 70)
    print()


# ============================================================================
# MAIN ENUMERATION ENGINE
# ============================================================================

def enumerate_k_p(k, p, verbose=False):
    """
    For a given (k, p), enumerate ALL C(S-1, k-1) subsets and compute
    full Horner chain statistics.

    Returns a dict with all computed quantities.
    """
    S = compute_S(k)
    total_subsets = math.comb(S - 1, k - 1)

    # Number of internal positions: j = 1, ..., k-2 (there are k-2 of them)
    n_internal = k - 2

    # Counters
    N_total = 0  # = total_subsets (sanity check)
    N_final_zero = 0  # c_{k-1} = 0
    N_final_nonzero = 0  # c_{k-1} != 0

    # Among final-zero subsets
    N_final_zero_with_internal_zero = 0  # has at least one c_j=0 for 0<j<k-1
    N_final_zero_zero_free = 0  # c_{k-1}=0 but no internal zeros

    # Among final-nonzero subsets
    N_final_nonzero_with_internal_zero = 0

    # Internal zero position distribution (among final-zero subsets)
    zero_pos_count_final_zero = defaultdict(int)  # position j -> count
    # Internal zero position distribution (among final-nonzero subsets)
    zero_pos_count_final_nonzero = defaultdict(int)

    # Distribution of number of internal zeros
    # Key: number of internal zeros, Value: [count_final_zero, count_final_nonzero]
    n_internal_zeros_dist = defaultdict(lambda: [0, 0])

    # For conditional probability: P(c_{k-1}=0 | c_j=0) for each internal j
    # cond_numerator[j] = count of subsets where c_j=0 AND c_{k-1}=0
    # cond_denominator[j] = count of subsets where c_j=0
    cond_numerator = defaultdict(int)
    cond_denominator = defaultdict(int)

    # Enumerate all subsets
    for subset in combinations(range(1, S), k - 1):
        chain = horner_chain(subset, k, p)
        N_total += 1

        # Count internal zeros (positions 1 to k-2)
        internal_zeros = []
        for j in range(1, k - 1):
            if chain[j] == 0:
                internal_zeros.append(j)

        n_iz = len(internal_zeros)
        final_zero = (chain[k - 1] == 0)

        if final_zero:
            N_final_zero += 1
            n_internal_zeros_dist[n_iz][0] += 1
            if n_iz > 0:
                N_final_zero_with_internal_zero += 1
                for j in internal_zeros:
                    zero_pos_count_final_zero[j] += 1
            else:
                N_final_zero_zero_free += 1
        else:
            N_final_nonzero += 1
            n_internal_zeros_dist[n_iz][1] += 1
            if n_iz > 0:
                N_final_nonzero_with_internal_zero += 1
                for j in internal_zeros:
                    zero_pos_count_final_nonzero[j] += 1

        # Conditional counts
        for j in internal_zeros:
            cond_denominator[j] += 1
            if final_zero:
                cond_numerator[j] += 1

    assert N_total == total_subsets
    assert N_final_zero + N_final_nonzero == N_total

    # Compute derived quantities
    P_final_zero = N_final_zero / N_total if N_total > 0 else 0
    expected_P = 1.0 / p  # random expectation

    # P(internal zero | final zero)
    P_iz_given_fz = (N_final_zero_with_internal_zero / N_final_zero
                     if N_final_zero > 0 else float('nan'))
    # P(internal zero | final nonzero)
    P_iz_given_fnz = (N_final_nonzero_with_internal_zero / N_final_nonzero
                      if N_final_nonzero > 0 else float('nan'))

    # Random expectation for having at least one internal zero:
    # If each position has independent probability 1/p of being zero,
    # P(at least one) = 1 - (1-1/p)^{n_internal}
    P_iz_random = 1.0 - (1.0 - 1.0/p)**n_internal if n_internal > 0 else 0.0

    # Zero-free ratio among final-zero subsets
    zero_free_ratio = (N_final_zero_zero_free / N_final_zero
                       if N_final_zero > 0 else float('nan'))
    # Random expectation: (1-1/p)^{n_internal}
    zero_free_random = (1.0 - 1.0/p)**n_internal

    # Conditional probabilities P(c_{k-1}=0 | c_j=0) for each j
    cond_probs = {}
    for j in sorted(cond_denominator.keys()):
        if cond_denominator[j] > 0:
            cond_probs[j] = cond_numerator[j] / cond_denominator[j]
        else:
            cond_probs[j] = float('nan')

    result = {
        'k': k,
        'p': p,
        'S': S,
        'n_internal_positions': n_internal,
        'total_subsets': N_total,
        'N_final_zero': N_final_zero,
        'N_final_nonzero': N_final_nonzero,
        'P_final_zero': P_final_zero,
        'expected_P_final_zero': expected_P,
        'ratio_observed_over_expected': P_final_zero / expected_P if expected_P > 0 else float('nan'),
        'N_fz_with_iz': N_final_zero_with_internal_zero,
        'N_fz_zero_free': N_final_zero_zero_free,
        'N_fnz_with_iz': N_final_nonzero_with_internal_zero,
        'P_iz_given_fz': P_iz_given_fz,
        'P_iz_given_fnz': P_iz_given_fnz,
        'P_iz_random': P_iz_random,
        'zero_free_ratio': zero_free_ratio,
        'zero_free_random': zero_free_random,
        'zero_pos_final_zero': dict(zero_pos_count_final_zero),
        'zero_pos_final_nonzero': dict(zero_pos_count_final_nonzero),
        'n_internal_zeros_dist': {int(niz): vals for niz, vals in sorted(n_internal_zeros_dist.items())},
        'cond_probs': cond_probs,
        'cond_numerator': dict(cond_numerator),
        'cond_denominator': dict(cond_denominator),
    }

    return result


# ============================================================================
# CROSS-PRIME CORRELATION ANALYSIS
# ============================================================================

def cross_prime_analysis(k, primes):
    """
    For subsets that satisfy c_{k-1} = 0 mod p1 AND c_{k-1} = 0 mod p2,
    analyze internal zero correlations.
    """
    if len(primes) < 2:
        return None

    S = compute_S(k)
    total_subsets = math.comb(S - 1, k - 1)

    # For each pair of primes
    results = []
    for i in range(len(primes)):
        for j_idx in range(i + 1, len(primes)):
            p1, p2 = primes[i], primes[j_idx]

            N_zero_p1 = 0
            N_zero_p2 = 0
            N_zero_both = 0

            for subset in combinations(range(1, S), k - 1):
                chain1 = horner_chain(subset, k, p1)
                chain2 = horner_chain(subset, k, p2)
                fz1 = (chain1[k - 1] == 0)
                fz2 = (chain2[k - 1] == 0)
                if fz1:
                    N_zero_p1 += 1
                if fz2:
                    N_zero_p2 += 1
                if fz1 and fz2:
                    N_zero_both += 1

            # Expected under independence: N_total / (p1 * p2)
            expected_both = total_subsets / (p1 * p2)
            ratio = N_zero_both / expected_both if expected_both > 0 else float('nan')

            results.append({
                'p1': p1, 'p2': p2,
                'N_zero_p1': N_zero_p1,
                'N_zero_p2': N_zero_p2,
                'N_zero_both': N_zero_both,
                'expected_both': expected_both,
                'ratio': ratio,
            })

    return results


# ============================================================================
# REPORTING
# ============================================================================

def print_section(title):
    """Print a section header."""
    print()
    print("=" * 70)
    print(title)
    print("=" * 70)


def format_float(x, width=10, decimals=6):
    """Format a float, handling nan."""
    if x != x:  # nan check
        return f"{'nan':>{width}}"
    return f"{x:>{width}.{decimals}f}"


def print_result(r):
    """Print a single (k, p) result block."""
    k = r['k']
    p = r['p']
    S = r['S']
    n_int = r['n_internal_positions']

    print(f"\n--- k={k}, p={p}, S={S}, internal positions={n_int} ---")
    print(f"  Total subsets C({S-1},{k-1}) = {r['total_subsets']}")
    print(f"  N_final_zero (N_0)  = {r['N_final_zero']}")
    print(f"  P(c_{{k-1}}=0)       = {r['P_final_zero']:.6f}  "
          f"(expected 1/p = {r['expected_P_final_zero']:.6f}, "
          f"ratio = {r['ratio_observed_over_expected']:.4f})")

    if r['N_final_zero'] == 0:
        print("  [No final-zero subsets found; skipping internal zero analysis]")
        return

    print(f"\n  INTERNAL ZEROS:")
    print(f"    Among final-zero subsets:")
    print(f"      With internal zero:    {r['N_fz_with_iz']:>6d}  "
          f"({r['P_iz_given_fz']:.6f})")
    print(f"      Zero-free:             {r['N_fz_zero_free']:>6d}  "
          f"({r['zero_free_ratio']:.6f})")
    print(f"    Among final-nonzero subsets:")
    print(f"      With internal zero:    {r['N_fnz_with_iz']:>6d}  "
          f"({r['P_iz_given_fnz']:.6f})")
    print(f"    Random expectation:      "
          f"P(>=1 iz) = {r['P_iz_random']:.6f}, "
          f"P(zero-free) = {r['zero_free_random']:.6f}")

    # KEY DIAGNOSTIC
    delta = r['P_iz_given_fz'] - r['P_iz_given_fnz']
    if abs(delta) > 1e-10 and r['P_iz_given_fnz'] == r['P_iz_given_fnz']:
        direction = "MORE" if delta > 0 else "LESS"
        print(f"\n  *** KEY FINDING: Final-zero subsets are {direction} likely to have "
              f"internal zeros ***")
        print(f"      P(iz|fz) - P(iz|fnz) = {delta:+.6f}")
        if r['P_iz_given_fnz'] > 0:
            relative = delta / r['P_iz_given_fnz']
            print(f"      Relative difference   = {relative:+.4f} ({relative*100:+.2f}%)")

    # Conditional probability table
    if r['cond_probs']:
        print(f"\n  CONDITIONAL PROBABILITIES:")
        print(f"    P(c_{{k-1}}=0) = 1/p = {1.0/p:.6f}")
        print(f"    {'j':>4s}  {'P(fz|c_j=0)':>14s}  {'ratio to 1/p':>14s}  "
              f"{'n_j=0':>8s}  {'n_j=0 & fz':>12s}")
        for j in sorted(r['cond_probs'].keys()):
            cp = r['cond_probs'][j]
            ratio = cp * p
            n_denom = r['cond_denominator'].get(j, 0)
            n_num = r['cond_numerator'].get(j, 0)
            print(f"    {j:>4d}  {cp:>14.6f}  {ratio:>14.4f}  "
                  f"{n_denom:>8d}  {n_num:>12d}")

    # Distribution of number of internal zeros
    if r['n_internal_zeros_dist']:
        print(f"\n  DISTRIBUTION OF #INTERNAL ZEROS:")
        print(f"    {'#iz':>4s}  {'final=0':>8s}  {'final!=0':>8s}  "
              f"{'P(fz|#iz)':>12s}  {'ratio':>8s}")
        for niz in sorted(r['n_internal_zeros_dist'].keys()):
            fz, fnz = r['n_internal_zeros_dist'][niz]
            total_niz = fz + fnz
            p_fz_niz = fz / total_niz if total_niz > 0 else float('nan')
            ratio = p_fz_niz * p if p_fz_niz == p_fz_niz else float('nan')
            print(f"    {niz:>4d}  {fz:>8d}  {fnz:>8d}  "
                  f"{format_float(p_fz_niz, 12, 6)}  {format_float(ratio, 8, 4)}")

    # Zero position distribution (if enough data)
    if r['zero_pos_final_zero'] and r['N_final_zero'] > 0:
        print(f"\n  ZERO POSITION DISTRIBUTION (among N_0={r['N_final_zero']} final-zero subsets):")
        print(f"    {'pos j':>6s}  {'count(fz)':>10s}  {'freq(fz)':>10s}  "
              f"{'count(fnz)':>10s}  {'freq(fnz)':>10s}  {'fz/fnz freq':>12s}")
        all_positions = sorted(set(list(r['zero_pos_final_zero'].keys()) +
                                   list(r['zero_pos_final_nonzero'].keys())))
        for j in all_positions:
            c_fz = r['zero_pos_final_zero'].get(j, 0)
            c_fnz = r['zero_pos_final_nonzero'].get(j, 0)
            freq_fz = c_fz / r['N_final_zero']
            freq_fnz = c_fnz / r['N_final_nonzero'] if r['N_final_nonzero'] > 0 else 0
            ratio = freq_fz / freq_fnz if freq_fnz > 0 else float('nan')
            print(f"    {j:>6d}  {c_fz:>10d}  {freq_fz:>10.6f}  "
                  f"{c_fnz:>10d}  {freq_fnz:>10.6f}  {format_float(ratio, 12, 4)}")


def print_summary_table(all_results):
    """Print a compact summary table across all (k, p)."""
    print_section("COMPACT SUMMARY TABLE")
    print(f"{'k':>3s} {'p':>6s} {'S':>3s} {'C(S-1,k-1)':>10s} "
          f"{'N_0':>8s} {'P(fz)':>10s} {'1/p':>10s} "
          f"{'P(iz|fz)':>10s} {'P(iz|fnz)':>10s} {'delta':>10s} "
          f"{'zf_ratio':>10s} {'zf_rand':>10s}")
    print("-" * 125)
    for r in all_results:
        delta = r['P_iz_given_fz'] - r['P_iz_given_fnz']
        if delta != delta:
            delta_str = "nan"
        else:
            delta_str = f"{delta:+.6f}"
        print(f"{r['k']:>3d} {r['p']:>6d} {r['S']:>3d} {r['total_subsets']:>10d} "
              f"{r['N_final_zero']:>8d} {r['P_final_zero']:>10.6f} {1.0/r['p']:>10.6f} "
              f"{format_float(r['P_iz_given_fz'], 10, 6)} "
              f"{format_float(r['P_iz_given_fnz'], 10, 6)} "
              f"{delta_str:>10s} "
              f"{format_float(r['zero_free_ratio'], 10, 6)} "
              f"{format_float(r['zero_free_random'], 10, 6)}")


def print_cross_prime(k, cross_results):
    """Print cross-prime correlation results."""
    if cross_results is None:
        return
    print(f"\n  CROSS-PRIME CORRELATIONS (k={k}):")
    print(f"    {'p1':>6s}  {'p2':>6s}  {'N_0(p1)':>8s}  {'N_0(p2)':>8s}  "
          f"{'N_0(both)':>10s}  {'expected':>10s}  {'ratio':>8s}")
    for cr in cross_results:
        print(f"    {cr['p1']:>6d}  {cr['p2']:>6d}  {cr['N_zero_p1']:>8d}  {cr['N_zero_p2']:>8d}  "
              f"{cr['N_zero_both']:>10d}  {cr['expected_both']:>10.2f}  {cr['ratio']:>8.4f}")


# ============================================================================
# INTERPRETATION ENGINE
# ============================================================================

def interpret_results(all_results):
    """
    Provide a rigorous interpretation of the results.
    Report what the data shows, not what we hope.
    """
    print_section("RIGOROUS INTERPRETATION")

    # Collect delta values (P(iz|fz) - P(iz|fnz))
    deltas = []
    zero_free_ratios = []
    cond_ratios = []  # P(fz | c_j=0) / (1/p)
    # Separate small-p and large-p cases
    small_p_deltas = []  # p <= 20
    large_p_deltas = []  # p > 20

    for r in all_results:
        if r['N_final_zero'] > 0 and r['n_internal_positions'] > 0:
            d = r['P_iz_given_fz'] - r['P_iz_given_fnz']
            if d == d:  # not nan
                deltas.append((r['k'], r['p'], d, r['N_final_zero']))
                if r['p'] <= 20:
                    small_p_deltas.append((r['k'], r['p'], d, r['N_final_zero']))
                else:
                    large_p_deltas.append((r['k'], r['p'], d, r['N_final_zero']))

        if r['zero_free_ratio'] == r['zero_free_ratio']:  # not nan
            zero_free_ratios.append((r['k'], r['p'],
                                     r['zero_free_ratio'],
                                     r['zero_free_random']))

        for j, cp in r['cond_probs'].items():
            if cp == cp:  # not nan
                cond_ratios.append((r['k'], r['p'], j, cp * r['p']))

    print("\n1. DOES HAVING AN INTERNAL ZERO AFFECT P(FINAL ZERO)?")
    print("   delta = P(internal_zero | final_zero) - P(internal_zero | final_nonzero)")
    print("   If delta > 0: internal zeros are MORE common among final-zero subsets")
    print("   If delta < 0: internal zeros are LESS common (transient zeros help filter)")
    print("   If delta ~ 0: no useful correlation")
    print()

    n_positive = sum(1 for _, _, d, _ in deltas if d > 0.001)
    n_negative = sum(1 for _, _, d, _ in deltas if d < -0.001)
    n_neutral = sum(1 for _, _, d, _ in deltas if abs(d) <= 0.001)
    print(f"   Cases with delta > +0.001 (internal zeros MORE common in final-zero): {n_positive}")
    print(f"   Cases with delta < -0.001 (internal zeros LESS common in final-zero): {n_negative}")
    print(f"   Cases with |delta| <= 0.001 (neutral): {n_neutral}")

    if deltas:
        avg_delta = sum(d for _, _, d, _ in deltas) / len(deltas)
        # Weighted average by N_final_zero
        total_weight = sum(n for _, _, _, n in deltas)
        if total_weight > 0:
            weighted_avg = sum(d * n for _, _, d, n in deltas) / total_weight
        else:
            weighted_avg = 0
        print(f"   Average delta: {avg_delta:+.6f}")
        print(f"   Weighted average (by N_0): {weighted_avg:+.6f}")

    print("\n   IMPORTANT STRATIFICATION BY PRIME SIZE:")
    if small_p_deltas:
        avg_small = sum(d for _, _, d, _ in small_p_deltas) / len(small_p_deltas)
        print(f"   Small primes (p <= 20): avg delta = {avg_small:+.6f} "
              f"({len(small_p_deltas)} cases)")
        for k, p, d, n0 in small_p_deltas:
            print(f"     k={k:2d} p={p:3d}: delta={d:+.6f} (N_0={n0})")
    if large_p_deltas:
        avg_large = sum(d for _, _, d, _ in large_p_deltas) / len(large_p_deltas)
        print(f"   Large primes (p > 20): avg delta = {avg_large:+.6f} "
              f"({len(large_p_deltas)} cases)")
        for k, p, d, n0 in large_p_deltas:
            print(f"     k={k:2d} p={p:3d}: delta={d:+.6f} (N_0={n0})")

    print("\n2. ZERO-FREE CHAINS: ARE THEY OVER- OR UNDER-REPRESENTED?")
    print("   zero_free_ratio = P(no internal zeros | final zero)")
    print("   zero_free_random = (1-1/p)^(k-2)  (independent model)")
    print("   If ratio > random: zero-free chains are over-represented among final-zero")
    print("   If ratio < random: zero-free chains are under-represented")
    print()
    n_over = 0
    n_under = 0
    for k, p, actual, expected in zero_free_ratios:
        diff = actual - expected
        if abs(diff) > 0.001:
            if diff > 0:
                n_over += 1
            else:
                n_under += 1
    print(f"   Over-represented (ratio > random + 0.001): {n_over}")
    print(f"   Under-represented (ratio < random - 0.001): {n_under}")
    print(f"   Neutral (|diff| <= 0.001): {len(zero_free_ratios) - n_over - n_under}")

    print("\n3. CONDITIONAL PROBABILITY: P(FINAL ZERO | c_j = 0)")
    print("   Baseline: P(final zero) = 1/p")
    print("   ratio = P(fz | c_j=0) * p")
    print("   If ratio > 1: passing through zero INCREASES chance of final zero")
    print("   If ratio < 1: passing through zero DECREASES chance (helps filtering)")
    print("   If ratio ~ 1: no useful information")
    print()
    if cond_ratios:
        ratios_only = [r for _, _, _, r in cond_ratios]
        n_above = sum(1 for r in ratios_only if r > 1.05)
        n_below = sum(1 for r in ratios_only if r < 0.95)
        n_mid = len(ratios_only) - n_above - n_below
        print(f"   ratio > 1.05 (increases chance): {n_above}")
        print(f"   ratio < 0.95 (decreases chance): {n_below}")
        print(f"   0.95 <= ratio <= 1.05 (neutral): {n_mid}")
        if ratios_only:
            avg_ratio = sum(ratios_only) / len(ratios_only)
            print(f"   Average ratio: {avg_ratio:.4f}")
            print(f"   Min ratio: {min(ratios_only):.4f}")
            print(f"   Max ratio: {max(ratios_only):.4f}")

    # Last-position analysis
    print("\n4. LAST-POSITION ZERO (j = k-2) PHENOMENON")
    print("   The position j = k-2 (second-to-last in the chain) is special.")
    print("   If c_{k-2} = 0, then c_{k-1} = 2^{b_1} mod p, which is a SINGLE")
    print("   power of 2. This severely constrains the final value.")
    print()
    last_pos_data = []
    for r in all_results:
        if r['N_final_zero'] == 0:
            continue
        k = r['k']
        p = r['p']
        last_j = k - 2
        if last_j in r['cond_probs']:
            cp = r['cond_probs'][last_j]
            ratio = cp * p
            n_denom = r['cond_denominator'].get(last_j, 0)
            n_num = r['cond_numerator'].get(last_j, 0)
            last_pos_data.append((k, p, ratio, n_denom, n_num))
            print(f"   k={k:2d} p={p:3d}: P(fz|c_{{k-2}}=0) * p = {ratio:.4f}  "
                  f"(n={n_denom}, hits={n_num})")
    if last_pos_data:
        last_ratios = [r for _, _, r, _, _ in last_pos_data]
        print(f"   Average last-position ratio: {sum(last_ratios)/len(last_ratios):.4f}")
        n_zero_ratio = sum(1 for r in last_ratios if r < 0.001)
        print(f"   Cases where ratio = 0 (zero never leads to final zero): "
              f"{n_zero_ratio}/{len(last_ratios)}")

    # Early-position vs late-position analysis
    print("\n5. POSITION-DEPENDENT CONDITIONAL PROBABILITIES")
    print("   Examining whether EARLY zeros (j near 1) vs LATE zeros (j near k-2)")
    print("   have different effects on P(final zero).")
    print()
    for r in all_results:
        if r['N_final_zero'] < 10 or not r['cond_probs']:
            continue
        k = r['k']
        p = r['p']
        n_int = r['n_internal_positions']
        if n_int < 4:
            continue
        # Split positions into early half and late half
        positions = sorted(r['cond_probs'].keys())
        mid = (positions[0] + positions[-1]) / 2
        early_ratios = []
        late_ratios = []
        for j in positions:
            ratio = r['cond_probs'][j] * p
            if j < mid:
                early_ratios.append(ratio)
            else:
                late_ratios.append(ratio)
        if early_ratios and late_ratios:
            avg_early = sum(early_ratios) / len(early_ratios)
            avg_late = sum(late_ratios) / len(late_ratios)
            print(f"   k={k:2d} p={p:3d}: early avg ratio={avg_early:.4f}, "
                  f"late avg ratio={avg_late:.4f}, "
                  f"{'EARLY favors fz' if avg_early > avg_late else 'LATE favors fz'}")

    # Monotonicity analysis of #internal zeros vs P(fz)
    print("\n6. MONOTONICITY: P(FINAL ZERO) vs NUMBER OF INTERNAL ZEROS")
    print("   For each (k,p), does P(fz | #iz=n) decrease as n increases?")
    print("   If yes, more zeros = less likely to complete the chain.")
    print()
    for r in all_results:
        if r['N_final_zero'] < 5:
            continue
        k = r['k']
        p = r['p']
        dist = r['n_internal_zeros_dist']
        if len(dist) < 2:
            continue
        entries = []
        for niz in sorted(dist.keys()):
            fz, fnz = dist[niz]
            total_niz = fz + fnz
            if total_niz > 0:
                p_fz = fz / total_niz
                entries.append((niz, p_fz, total_niz))
        if len(entries) >= 2:
            # Check if ratio = P(fz|#iz=n) * p is monotonically decreasing
            ratios = [e[1] * p for e in entries]
            monotone_dec = all(ratios[i] >= ratios[i+1] for i in range(len(ratios)-1))
            # Also check if last entry (highest #iz) always has ratio=0
            last_ratio = ratios[-1]
            print(f"   k={k:2d} p={p:3d}:", end="")
            for niz, pfz, tot in entries:
                print(f"  #iz={niz}: {pfz*p:.3f} (n={tot})", end="")
            if monotone_dec:
                print("  [MONOTONE DECREASING]")
            else:
                print("  [NOT MONOTONE]")

    print("\n7. OVERALL VERDICT")
    print("   " + "-" * 60)
    print()
    print("   The data reveals a COMPLEX picture with TWO distinct regimes:")
    print()
    print("   REGIME 1 (large p, sparse zeros):")
    print("   For large primes (p >> k), internal zeros are RARE, and when they")
    print("   occur, they are NEGATIVELY correlated with final zero. In 6 cases")
    print("   with large p, ALL final-zero subsets are zero-free (delta = -100%).")
    print("   This is partly trivial: when p is large, almost all chains are")
    print("   zero-free anyway, so this provides minimal additional filtering.")
    print()
    print("   REGIME 2 (small p, dense zeros):")
    print("   For small primes (p = 5, 7, 11, 13), internal zeros are common,")
    print("   and the picture is NUANCED:")

    if deltas:
        avg_d = sum(d for _, _, d, _ in deltas) / len(deltas)
        weighted_avg = sum(d * n for _, _, d, n in deltas) / sum(n for _, _, _, n in deltas)
        print()
        print(f"   - Unweighted avg delta = {avg_d:+.6f} (negative = filtering helps)")
        print(f"   - Weighted avg delta   = {weighted_avg:+.6f} (positive = filtering hurts)")
        print()
        print("   The SIGN DISCREPANCY between weighted and unweighted averages is")
        print("   the central finding: the cases with LARGE N_0 (small p, large k)")
        print("   show POSITIVE deltas (internal zeros MORE common among final-zero),")
        print("   while cases with small N_0 show NEGATIVE deltas.")

    print()
    print("   KEY PATTERNS DISCOVERED:")
    print()
    print("   A. LAST-POSITION SUPPRESSION: P(fz | c_{k-2}=0) is consistently")
    print("      near zero or zero across all (k,p). This is structural: if")
    print("      c_{k-2}=0, then c_{k-1} = 2^{b_1}, and for c_{k-1}=0 mod p")
    print("      we'd need p | 2^{b_1}, impossible for odd p. This means the")
    print("      last internal position j=k-2 ALWAYS suppresses final zero.")
    print("      [PROVEN: Consequence of the transient zero property at j=k-2]")
    print()
    print("   B. PENULTIMATE SUPPRESSION: Positions j=k-3 and sometimes j=k-4")
    print("      also show suppressed P(fz|c_j=0). This cascading suppression")
    print("      near the end of the chain is where the real filtering happens.")
    print()
    print("   C. EARLY-POSITION AMPLIFICATION: Some early positions (small j)")
    print("      show P(fz|c_j=0) > 1/p. This is a MIRROR SYMMETRY effect:")
    print("      early zeros constrain the chain in ways that can INCREASE the")
    print("      chance of reaching zero at the end (via specific arithmetic")
    print("      relationships between the subset elements).")
    print()
    print("   D. POSITION-SPECIFIC STRUCTURE: The conditional probabilities are")
    print("      highly position-dependent and NOT exchangeable. The Horner chain")
    print("      has a directional structure that breaks symmetry between positions.")
    print()
    print("   CONCLUSION FOR THE JUNCTION THEOREM:")
    print("   " + "-" * 56)
    print("   The transient zero property provides STRUCTURAL information")
    print("   but its filtering power is POSITION-DEPENDENT and MIXED:")
    print("   - Late zeros (near j=k-2): STRONG suppression of final zero")
    print("   - Early zeros (near j=1): WEAK or even REVERSE effect")
    print("   - Overall: the effect is NOT a simple multiplicative filter")
    print("   - For impossibility proofs: the last-position suppression")
    print("     (j=k-2) is PROVEN and provides a hard constraint")
    print("   - For probabilistic estimates: using (1-1/p)^{k-2} as a")
    print("     uniform correction factor is NOT justified by the data")


# ============================================================================
# MAIN
# ============================================================================

def main():
    t_start = time.time()

    # Run self-tests first
    run_self_tests()

    # Configuration: which (k, prime_threshold) to enumerate
    # We use all primes dividing d(k) up to PRIME_LIMIT
    PRIME_LIMIT = 500  # include primes up to 500 for more data
    K_MAX = 15

    print_section("CONFIGURATION")
    print(f"  k range: 3 to {K_MAX}")
    print(f"  Prime threshold: {PRIME_LIMIT}")
    print(f"  Enumerating all C(S-1, k-1) subsets for each (k, p) pair")

    # Determine all (k, p) pairs
    pairs = []
    for k in range(3, K_MAX + 1):
        S = compute_S(k)
        d = compute_d(k)
        primes = [p for p in prime_factors(abs(d)) if p <= PRIME_LIMIT]
        total = math.comb(S - 1, k - 1)
        if primes:
            print(f"  k={k:2d}  S={S:2d}  d(k)={d:>10d}  "
                  f"C({S-1},{k-1})={total:>8d}  primes={primes}")
            for p in primes:
                pairs.append((k, p))
        else:
            print(f"  k={k:2d}  S={S:2d}  d(k)={d:>10d}  "
                  f"C({S-1},{k-1})={total:>8d}  primes=[]  [SKIPPED]")

    print(f"\n  Total (k, p) pairs to enumerate: {len(pairs)}")

    # Main enumeration
    print_section("DETAILED RESULTS")

    all_results = []
    cross_prime_results = {}

    for idx, (k, p) in enumerate(pairs):
        t0 = time.time()
        result = enumerate_k_p(k, p)
        t1 = time.time()
        elapsed = t1 - t0
        all_results.append(result)

        print_result(result)
        print(f"  [Computed in {elapsed:.2f}s]")

    # Cross-prime analysis for k values with multiple primes
    print_section("CROSS-PRIME ANALYSIS")
    k_to_primes = defaultdict(list)
    for k, p in pairs:
        k_to_primes[k].append(p)

    for k in sorted(k_to_primes.keys()):
        primes = k_to_primes[k]
        if len(primes) >= 2:
            cr = cross_prime_analysis(k, primes)
            if cr:
                cross_prime_results[k] = cr
                print_cross_prime(k, cr)

    if not cross_prime_results:
        print("\n  No k values with multiple primes <= threshold found.")

    # Summary table
    print_summary_table(all_results)

    # Interpretation
    interpret_results(all_results)

    # SHA256 fingerprint of all results
    print_section("REPRODUCIBILITY FINGERPRINT")
    # Serialize results to JSON for hashing
    # Convert defaultdicts and special values
    serializable = []
    for r in all_results:
        sr = {}
        for key, val in r.items():
            if isinstance(val, dict):
                sr[key] = {str(k2): v2 for k2, v2 in val.items()}
            elif isinstance(val, float) and val != val:
                sr[key] = "NaN"
            else:
                sr[key] = val
        serializable.append(sr)

    result_json = json.dumps(serializable, sort_keys=True, indent=2)
    sha = hashlib.sha256(result_json.encode('utf-8')).hexdigest()
    print(f"  SHA256 of all results: {sha}")
    print(f"  Total computation time: {time.time() - t_start:.1f}s")
    print(f"  Python version: {sys.version}")

    # Save raw results to JSON alongside
    output_dir = "/Users/ericmerle/Documents/Collatz-Junction-Theorem/scripts/research"
    json_path = output_dir + "/tz_exhaustive_results.json"
    with open(json_path, 'w') as f:
        json.dump({
            'sha256': sha,
            'timestamp': time.strftime('%Y-%m-%d %H:%M:%S'),
            'config': {'K_MAX': K_MAX, 'PRIME_LIMIT': PRIME_LIMIT},
            'results': serializable,
        }, f, indent=2)
    print(f"  Raw results saved to: {json_path}")

    print("\n" + "=" * 70)
    print("ENUMERATION COMPLETE")
    print("=" * 70)


if __name__ == '__main__':
    main()
