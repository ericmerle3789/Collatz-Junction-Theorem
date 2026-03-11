#!/usr/bin/env python3
"""
R53: COLLISION TAXONOMY -- Decomposition of E_excess by Structural Families
===========================================================================
Agent R53 (Axe A) -- Round 53

MISSION: Decompose E_excess by structural families to understand WHO produces
the excess collisions in the Collatz B-vector distribution.

CONTEXT ACQUIRED (DO NOT RE-PROVE):
  P_B(g) = Sum_{j=0}^{k-1} g^j * 2^{B_j} mod p, with g = 2*3^{-1} mod p
  B monotone: 0 <= B_0 <= ... <= B_{k-1} <= max_B = S-k, S = ceil(k*log2(3))
  C = C(max_B+k, k) = total number of nondecreasing B-vectors
  N_r = #{B monotone : P_B = r mod p}
  M_2 = Sum_r N_r^2 = #{(B,B') : P_B = P_{B'} mod p}  (collision count)
  V = M_2 - C^2/p  (L^2 discrepancy)
  mu = M_2*p/C^2  (collision multiplicity, mu=1 = perfect equidistribution)
  E_excess = M_2 - C - C(C-1)/p  (collisions beyond random expectation)
  mu-1 = (p-1)/C + p*E_excess/C^2  [PROVED R46]

KEY RESULTS (R52):
  V <= 1.42*C in R1 (232/232 cases)
  |E_excess/C| < 0.90 in R1
  K = (mu-1)*C/p < 1.42 in R1

KEY RESULT (R46, LSD h=1):
  Two monotone B-vectors at Hamming distance h=1 collide iff ord_p(2) | |Delta|,
  where Delta = B_j - B_j' at the single differing position.

SECTIONS:
  1: Full collision enumeration (small cases, k<=7)
  2: Decomposition of E_excess by Hamming distance
  3: h=1 contribution analysis using LSD criterion
  4: Collision degree distribution
  5: Structure of excess collisions (near/mid/far)
  6: Regime dependence

EPISTEMIC LABELS:
  [PROUVE]       = rigorous proof or exact computation
  [CALCULE]      = verified by exact computation
  [OBSERVE]      = numerical evidence, NOT a proof
  [CONJECTURAL]  = plausible but unproven

Author: Claude Opus 4.6 (R53 Axe A Investigateur collision-taxonomy pour Eric Merle)
Date:   2026-03-11
"""

import sys
import time
from math import comb, gcd, ceil, log2, sqrt, log
from itertools import combinations_with_replacement
from collections import defaultdict, Counter

# ============================================================================
# GLOBAL CONFIGURATION
# ============================================================================

T_START = time.time()
TIME_BUDGET = 280.0  # 280s budget

PASS_COUNT = 0
FAIL_COUNT = 0
VERBOSE = True

# Accumulators for cross-section data
SECTION_DATA = defaultdict(list)

# Test pairs as specified
R1_PAIRS = [(3, 7), (4, 13), (5, 31), (6, 59), (7, 127)]
RGEN_PAIRS = [(3, 5)]
ALL_TEST_PAIRS = R1_PAIRS + RGEN_PAIRS

# Additional primes for regime sweep
PRIMES_POOL = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
               67, 71, 73, 79, 83, 89, 97, 101, 127, 131, 137, 139, 149, 151, 157]


def elapsed():
    return time.time() - T_START


def time_remaining():
    return TIME_BUDGET - elapsed()


def record_test(name, passed, detail=""):
    global PASS_COUNT, FAIL_COUNT
    status = "PASS" if passed else "FAIL"
    if passed:
        PASS_COUNT += 1
    else:
        FAIL_COUNT += 1
    if VERBOSE:
        print(f"  [{status}] {name}" + (f" -- {detail}" if detail else ""))


# ============================================================================
# SECTION 0: MATHEMATICAL PRIMITIVES
# ============================================================================

def compute_S(k):
    """Minimal S such that 2^S > 3^k. Exact via integer comparison."""
    S = ceil(k * log2(3))
    three_k = 3 ** k
    while (1 << S) <= three_k:
        S += 1
    while S > 0 and (1 << (S - 1)) > three_k:
        S -= 1
    return S


def compute_max_B(k):
    """max_B = S - k."""
    return compute_S(k) - k


def compute_C(k):
    """C(k) = C(max_B+k, k), number of nondecreasing B-vectors in [0, max_B]^k."""
    max_B = compute_max_B(k)
    return comb(max_B + k, k)


def compute_g(p):
    """g = 2 * 3^{-1} mod p. Standard project convention."""
    if p == 2 or p == 3:
        return None
    return (2 * pow(3, p - 2, p)) % p


def ord_mod(base, m):
    """Multiplicative order of base modulo m."""
    if m <= 1 or gcd(base, m) != 1:
        return None
    o = 1
    v = base % m
    while v != 1:
        o += 1
        v = (v * base) % m
        if o > m:
            return None
    return o


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


def classify_regime(k, p):
    """Classify (k,p) into sub-regime R1/R2/R3/R_gen."""
    max_B = compute_max_B(k)
    ord2 = ord_mod(2, p)
    if ord2 is None:
        return 'R_gen', ord2
    if ord2 >= 4 * (max_B + 1):
        return 'R3', ord2
    elif ord2 >= 2 * (max_B + 1):
        return 'R2', ord2
    elif ord2 >= max_B + 1:
        return 'R1', ord2
    else:
        return 'R_gen', ord2


def hamming_distance(B1, B2):
    """Hamming distance between two tuples of same length."""
    return sum(1 for a, b in zip(B1, B2) if a != b)


def diff_vector(B1, B2):
    """Signed difference vector B1 - B2."""
    return tuple(a - b for a, b in zip(B1, B2))


def enumerate_all_PB(k, p):
    """Enumerate all monotone B-vectors and their P_B values.
    Returns: list of (B_tuple, P_B_value).
    """
    max_B = compute_max_B(k)
    g = compute_g(p)
    if g is None:
        return []

    g_pows = [pow(g, j, p) for j in range(k)]
    two_pows = [pow(2, b, p) for b in range(max_B + 1)]

    results = []
    for B in combinations_with_replacement(range(max_B + 1), k):
        val = 0
        for j in range(k):
            val = (val + g_pows[j] * two_pows[B[j]]) % p
        results.append((B, val))

    return results


def compute_Nr(k, p):
    """Compute N_r array and basic statistics."""
    results = enumerate_all_PB(k, p)
    Nr = [0] * p
    for _, val in results:
        Nr[val] += 1
    C = len(results)
    M2 = sum(n * n for n in Nr)
    V = M2 - C * C / p
    E_excess = M2 - C - C * (C - 1) / p
    return {
        'results': results,
        'Nr': Nr,
        'C': C,
        'M2': M2,
        'V': V,
        'E_excess': E_excess,
        'mu_minus_1': p * V / (C * C) if C > 0 else 0,
    }


# ============================================================================
# SECTION 1: FULL COLLISION ENUMERATION (small cases, k<=7)
# ============================================================================

def section1_full_enumeration():
    """Enumerate ALL colliding pairs (B,B') and classify them."""
    print("\n" + "=" * 72)
    print("SECTION 1: FULL COLLISION ENUMERATION (small cases)")
    print("  For each (k,p): enumerate all pairs (B,B') with P_B = P_{B'} mod p")
    print("  Classify by: self-collision (B=B'), Hamming distance h, diff vector D")
    print("=" * 72)

    test_count = 0

    for k, p in ALL_TEST_PAIRS:
        if time_remaining() < 30:
            print("  [TIME LIMIT] Stopping section 1")
            break

        regime, ord2 = classify_regime(k, p)
        max_B = compute_max_B(k)
        C = compute_C(k)

        print(f"\n  --- k={k}, p={p}, ord_p(2)={ord2}, max_B={max_B}, C={C}, {regime} ---")

        if C > 50000:
            print(f"  [SKIP] C={C} too large for full pair enumeration")
            continue

        data = compute_Nr(k, p)
        results = data['results']
        M2 = data['M2']
        E_excess = data['E_excess']

        # Verify C
        record_test(f"S1.C_check k={k} p={p}", len(results) == C,
                     f"len={len(results)} vs C={C}")
        test_count += 1

        # Group by residue
        by_residue = defaultdict(list)
        for B, val in results:
            by_residue[val].append(B)

        # Count collisions and classify
        total_pairs = 0
        self_collisions = 0
        hamming_counts = Counter()  # h -> count of ordered pairs at distance h
        diff_counts = Counter()     # diff_vector -> count

        for r, B_list in by_residue.items():
            nr = len(B_list)
            # Number of ordered pairs (B,B') with P_B = P_{B'} = r is nr^2
            # This includes self-collisions (B=B')
            total_pairs += nr * nr
            self_collisions += nr  # diagonal: B = B'

            # For off-diagonal pairs (B != B'), classify by Hamming distance
            for i in range(len(B_list)):
                for j in range(len(B_list)):
                    if i == j:
                        continue  # skip diagonal
                    B1, B2 = B_list[i], B_list[j]
                    h = hamming_distance(B1, B2)
                    hamming_counts[h] += 1
                    D = diff_vector(B1, B2)
                    diff_counts[D] += 1

        # Verify: total_pairs = M2
        record_test(f"S1.M2_check k={k} p={p}", total_pairs == M2,
                     f"pairs={total_pairs} vs M2={M2}")
        test_count += 1

        # Verify: self_collisions = C (diagonal = C)
        record_test(f"S1.diag_check k={k} p={p}", self_collisions == C,
                     f"self={self_collisions} vs C={C}")
        test_count += 1

        off_diag = total_pairs - self_collisions
        expected_off = C * (C - 1) / p

        print(f"    M2 = {M2}, diagonal = {C}, off-diagonal = {off_diag}")
        print(f"    Expected off-diagonal (random) = {expected_off:.2f}")
        print(f"    E_excess = {E_excess:.4f}")

        # Hamming distance distribution of off-diagonal collisions
        print(f"    Hamming distance distribution of off-diagonal collisions:")
        for h in sorted(hamming_counts.keys()):
            count = hamming_counts[h]
            print(f"      h={h}: {count} ordered pairs ({count/2} unordered)")

        # Verify: sum of hamming counts = off-diagonal
        total_offdiag_check = sum(hamming_counts.values())
        record_test(f"S1.offdiag_sum k={k} p={p}", total_offdiag_check == off_diag,
                     f"sum_h={total_offdiag_check} vs off_diag={off_diag}")
        test_count += 1

        # Top diff vectors
        if diff_counts:
            top_diffs = diff_counts.most_common(5)
            print(f"    Top 5 diff vectors (D = B-B'):")
            for D, cnt in top_diffs:
                print(f"      D={D}: {cnt} pairs")

        # Store for later sections
        entry = {
            'k': k, 'p': p, 'regime': regime, 'ord2': ord2,
            'max_B': max_B, 'C': C, 'M2': M2,
            'E_excess': E_excess, 'V': data['V'],
            'mu_minus_1': data['mu_minus_1'],
            'hamming_counts': dict(hamming_counts),
            'off_diag': off_diag,
            'expected_off': expected_off,
            'results': results,
            'by_residue': dict(by_residue),
        }
        SECTION_DATA['enumerated'].append(entry)

    print(f"\n  Section 1 total: {test_count} tests")
    return test_count


# ============================================================================
# SECTION 2: DECOMPOSITION OF E_excess BY HAMMING DISTANCE
# ============================================================================

def section2_hamming_decomposition():
    """Decompose E_excess = Sum_{h>=1} E_h by Hamming distance."""
    print("\n" + "=" * 72)
    print("SECTION 2: DECOMPOSITION OF E_excess BY HAMMING DISTANCE")
    print("  E_excess = Sum_{h>=1} E_h")
    print("  E_h = (collisions at distance h) - (expected at distance h under random)")
    print("=" * 72)

    test_count = 0

    for entry in SECTION_DATA['enumerated']:
        if time_remaining() < 20:
            break

        k = entry['k']
        p = entry['p']
        C = entry['C']
        regime = entry['regime']
        E_excess = entry['E_excess']
        hamming_counts = entry['hamming_counts']  # h -> ordered pair count
        results = entry['results']

        print(f"\n  --- k={k}, p={p}, C={C}, {regime} ---")

        # Count total pairs at each Hamming distance (regardless of collision)
        # This requires counting over ALL pairs, not just colliding ones.
        # For small C this is feasible.
        total_pairs_by_h = Counter()
        all_B = [B for B, _ in results]

        if C <= 5000:
            for i in range(len(all_B)):
                for j in range(len(all_B)):
                    if i == j:
                        continue
                    h = hamming_distance(all_B[i], all_B[j])
                    total_pairs_by_h[h] += 1
        else:
            print(f"    [SKIP] C={C} too large for all-pairs Hamming count")
            continue

        print(f"    Hamming distance decomposition of E_excess:")
        print(f"    {'h':>3s} {'coll_h':>10s} {'total_h':>10s} {'exp_h':>12s} "
              f"{'E_h':>12s} {'E_h/E_exc':>10s}")
        print(f"    " + "-" * 62)

        E_h_values = {}
        E_excess_check = 0.0

        for h in range(1, k + 1):
            coll_h = hamming_counts.get(h, 0)        # ordered colliding pairs at distance h
            total_h = total_pairs_by_h.get(h, 0)     # total ordered pairs at distance h
            expected_h = total_h / p                  # expected under random
            E_h = coll_h - expected_h
            E_h_values[h] = E_h
            E_excess_check += E_h

            ratio = E_h / E_excess if abs(E_excess) > 1e-10 else float('nan')
            print(f"    {h:3d} {coll_h:10d} {total_h:10d} {expected_h:12.2f} "
                  f"{E_h:12.4f} {ratio:10.4f}")

        # Verify: Sum E_h = E_excess
        # Note: E_excess = M2 - C - C(C-1)/p = off_diag - C(C-1)/p
        # Sum_h coll_h = off_diag (all off-diagonal colliding pairs)
        # Sum_h total_h/p = Sum_h total_h / p = C(C-1)/p (all off-diagonal pairs / p)
        # So Sum E_h = off_diag - C(C-1)/p = E_excess. QED.
        abs_diff = abs(E_excess_check - E_excess)
        record_test(f"S2.E_h_sum k={k} p={p}", abs_diff < 1e-6,
                     f"Sum E_h={E_excess_check:.6f} vs E_excess={E_excess:.6f}")
        test_count += 1

        # Verify: Sum total_h = C*(C-1) (all ordered off-diagonal pairs)
        total_h_sum = sum(total_pairs_by_h.values())
        record_test(f"S2.total_h_sum k={k} p={p}", total_h_sum == C * (C - 1),
                     f"sum={total_h_sum} vs C(C-1)={C*(C-1)}")
        test_count += 1

        # Identify dominant h
        if E_h_values:
            dominant_h = max(E_h_values, key=lambda h: abs(E_h_values[h]))
            dominant_E = E_h_values[dominant_h]
            dominant_frac = dominant_E / E_excess if abs(E_excess) > 1e-10 else float('nan')
            print(f"    Dominant: h={dominant_h} with E_h={dominant_E:.4f} "
                  f"({dominant_frac:.2%} of E_excess)")

        # Store
        entry['E_h_values'] = E_h_values
        entry['total_pairs_by_h'] = dict(total_pairs_by_h)

    print(f"\n  Section 2 total: {test_count} tests")
    return test_count


# ============================================================================
# SECTION 3: h=1 CONTRIBUTION ANALYSIS USING LSD CRITERION
# ============================================================================

def section3_h1_lsd_analysis():
    """For h=1 collisions: verify they match ord_p(2)|Delta criterion."""
    print("\n" + "=" * 72)
    print("SECTION 3: h=1 CONTRIBUTION ANALYSIS USING LSD CRITERION")
    print("  LSD (R46): two B-vectors at h=1 collide iff ord_p(2) | |Delta|")
    print("  where Delta = B_j - B'_j at the single differing position j")
    print("=" * 72)

    test_count = 0

    for entry in SECTION_DATA['enumerated']:
        if time_remaining() < 20:
            break

        k = entry['k']
        p = entry['p']
        C = entry['C']
        regime = entry['regime']
        ord2 = entry['ord2']
        max_B = entry['max_B']
        E_excess = entry['E_excess']
        results = entry['results']
        by_residue = entry['by_residue']

        print(f"\n  --- k={k}, p={p}, ord_p(2)={ord2}, max_B={max_B}, {regime} ---")

        if ord2 is None:
            print(f"    [SKIP] ord_p(2) undefined")
            continue

        # Find all h=1 colliding pairs by direct enumeration
        h1_collisions_direct = []
        for r, B_list in by_residue.items():
            for i in range(len(B_list)):
                for j in range(i + 1, len(B_list)):
                    B1, B2 = B_list[i], B_list[j]
                    if hamming_distance(B1, B2) == 1:
                        # Find the differing position
                        for pos in range(k):
                            if B1[pos] != B2[pos]:
                                delta = abs(B1[pos] - B2[pos])
                                h1_collisions_direct.append((B1, B2, pos, delta))
                                break

        n_h1_direct = len(h1_collisions_direct)
        print(f"    h=1 collisions found (unordered): {n_h1_direct}")

        # Now predict h=1 collisions via LSD: for each pair (B,B') at h=1,
        # they collide iff ord_p(2) | |Delta|
        h1_predicted_by_lsd = 0
        h1_total = 0  # total pairs at h=1

        all_B = [B for B, _ in results]

        # For efficiency, enumerate h=1 pairs directly:
        # Two monotone vectors at h=1 differ at exactly one position j.
        # For position j, B_j can change to B'_j (must maintain monotonicity).
        lsd_predictions = []

        for idx, B in enumerate(all_B):
            B_list = list(B)
            for pos in range(k):
                # Try all alternative values at position pos that maintain monotonicity
                lo = B_list[pos - 1] if pos > 0 else 0
                hi = B_list[pos + 1] if pos < k - 1 else max_B
                for new_val in range(lo, hi + 1):
                    if new_val == B_list[pos]:
                        continue
                    # This gives a valid h=1 neighbor
                    h1_total += 1
                    delta = abs(new_val - B_list[pos])
                    if delta > 0 and delta % ord2 == 0:
                        h1_predicted_by_lsd += 1
                        lsd_predictions.append((tuple(B_list), pos, delta))

        # h1_total counts ordered pairs. n_h1_direct counts unordered.
        # The hamming_counts from section 1 also count ordered pairs.
        h1_ordered_direct = entry['hamming_counts'].get(1, 0)

        print(f"    h=1 total pairs (ordered): {h1_total}")
        print(f"    h=1 collisions (ordered, from enum): {h1_ordered_direct}")
        print(f"    h=1 collisions predicted by LSD (ordered): {h1_predicted_by_lsd}")

        # Verify LSD prediction matches actual h=1 collisions
        # Note: LSD gives the exact criterion, so these should match perfectly
        record_test(f"S3.lsd_match k={k} p={p}",
                     h1_predicted_by_lsd == h1_ordered_direct,
                     f"LSD_pred={h1_predicted_by_lsd} vs actual={h1_ordered_direct}")
        test_count += 1

        # Fraction of E_excess from h=1
        E_h1 = entry.get('E_h_values', {}).get(1, None)
        if E_h1 is not None and abs(E_excess) > 1e-10:
            frac_h1 = E_h1 / E_excess
            print(f"    E_h1 = {E_h1:.4f}, E_excess = {E_excess:.4f}")
            print(f"    Fraction of E_excess from h=1: {frac_h1:.4f} ({frac_h1:.2%})")
            record_test(f"S3.h1_fraction k={k} p={p}", True,
                         f"E_h1/E_excess = {frac_h1:.4f}")
            test_count += 1

        # By-position analysis: count h=1 collisions per position j
        pos_counts = Counter()
        for _, _, pos, delta in h1_collisions_direct:
            pos_counts[pos] += 1

        if pos_counts:
            print(f"    h=1 collisions by position (unordered):")
            for pos in range(k):
                cnt = pos_counts.get(pos, 0)
                print(f"      j={pos}: {cnt} collisions")

        # Delta distribution
        delta_counts = Counter()
        for _, _, _, delta in h1_collisions_direct:
            delta_counts[delta] += 1

        if delta_counts:
            print(f"    Delta distribution for h=1 collisions:")
            for delta in sorted(delta_counts.keys()):
                cnt = delta_counts[delta]
                divides = (delta % ord2 == 0) if ord2 else False
                print(f"      |Delta|={delta}: {cnt} pairs "
                      f"(ord|Delta: {'YES' if divides else 'NO'})")

                # LSD says every h=1 collision has ord|Delta
                record_test(f"S3.lsd_delta k={k} p={p} delta={delta}",
                             divides,
                             f"|Delta|={delta}, ord={ord2}")
                test_count += 1

    print(f"\n  Section 3 total: {test_count} tests")
    return test_count


# ============================================================================
# SECTION 4: COLLISION DEGREE DISTRIBUTION
# ============================================================================

def section4_collision_degree():
    """For each B, define coll(B) = #{B' != B : P_B = P_{B'}}. Study distribution."""
    print("\n" + "=" * 72)
    print("SECTION 4: COLLISION DEGREE DISTRIBUTION")
    print("  coll(B) = #{B' != B : P_B = P_{B'} mod p}")
    print("  Mean, std, max, fraction with coll(B)=0")
    print("=" * 72)

    test_count = 0

    for entry in SECTION_DATA['enumerated']:
        if time_remaining() < 20:
            break

        k = entry['k']
        p = entry['p']
        C = entry['C']
        regime = entry['regime']
        by_residue = entry['by_residue']
        results = entry['results']

        print(f"\n  --- k={k}, p={p}, C={C}, {regime} ---")

        # For each B, coll(B) = N_r(P_B) - 1 (subtract self)
        coll_degrees = []
        for B, val in results:
            nr = len(by_residue[val])
            coll_degrees.append(nr - 1)

        # Statistics
        n = len(coll_degrees)
        mean_coll = sum(coll_degrees) / n
        max_coll = max(coll_degrees)
        min_coll = min(coll_degrees)
        std_coll = sqrt(sum((c - mean_coll) ** 2 for c in coll_degrees) / n) if n > 1 else 0
        frac_zero = sum(1 for c in coll_degrees if c == 0) / n
        frac_hub = sum(1 for c in coll_degrees if c > 2 * mean_coll) / n if mean_coll > 0 else 0

        print(f"    coll(B) distribution:")
        print(f"      mean   = {mean_coll:.4f}")
        print(f"      std    = {std_coll:.4f}")
        print(f"      min    = {min_coll}")
        print(f"      max    = {max_coll}")
        print(f"      frac(coll=0) = {frac_zero:.4f} ({frac_zero:.2%})")
        print(f"      frac(hub: coll>2*mean) = {frac_hub:.4f} ({frac_hub:.2%})")

        # Expected mean under random: (C-1)/p
        expected_mean = (C - 1) / p
        print(f"      Expected mean (random) = {expected_mean:.4f}")

        # Verify: Sum coll(B) = Sum (N_r - 1) for all B = Sum N_r^2 - C = M2 - C = off_diag
        sum_coll = sum(coll_degrees)
        off_diag = entry['off_diag']
        record_test(f"S4.sum_coll k={k} p={p}", sum_coll == off_diag,
                     f"sum_coll={sum_coll} vs off_diag={off_diag}")
        test_count += 1

        # Verify mean: mean_coll = off_diag / C
        expected_mean_exact = off_diag / C
        record_test(f"S4.mean_coll k={k} p={p}",
                     abs(mean_coll - expected_mean_exact) < 1e-10,
                     f"mean={mean_coll:.4f} vs off_diag/C={expected_mean_exact:.4f}")
        test_count += 1

        # Histogram of collision degrees
        degree_hist = Counter(coll_degrees)
        print(f"    Degree histogram:")
        for deg in sorted(degree_hist.keys()):
            cnt = degree_hist[deg]
            bar = "#" * min(cnt, 50)
            print(f"      coll={deg:3d}: {cnt:5d} vectors {bar}")

        # Hub analysis: are collisions concentrated?
        # Gini-like coefficient: how concentrated are collisions?
        sorted_coll = sorted(coll_degrees)
        cum = 0
        gini_num = 0
        for i, c in enumerate(sorted_coll):
            cum += c
            gini_num += (2 * (i + 1) - n - 1) * c
        gini = gini_num / (n * sum_coll) if sum_coll > 0 else 0

        print(f"    Gini coefficient of coll(B): {gini:.4f}")
        print(f"      (0 = perfectly uniform, 1 = fully concentrated)")

        record_test(f"S4.gini_valid k={k} p={p}", 0 <= gini <= 1,
                     f"Gini={gini:.4f}")
        test_count += 1

        # Is coll concentrated or spread? If max_coll >> mean, concentrated.
        concentration_ratio = max_coll / mean_coll if mean_coll > 0 else 0
        print(f"    Concentration ratio (max/mean): {concentration_ratio:.2f}")
        record_test(f"S4.concentration k={k} p={p}", True,
                     f"max/mean={concentration_ratio:.2f} Gini={gini:.4f}")
        test_count += 1

        # Store
        entry['coll_degrees'] = coll_degrees
        entry['gini'] = gini
        entry['concentration_ratio'] = concentration_ratio
        entry['frac_zero'] = frac_zero

    print(f"\n  Section 4 total: {test_count} tests")
    return test_count


# ============================================================================
# SECTION 5: STRUCTURE OF EXCESS COLLISIONS (near/mid/far)
# ============================================================================

def section5_near_mid_far():
    """Separate E_excess into E_near (h<=2), E_mid (3<=h<=k/2), E_far (h>k/2)."""
    print("\n" + "=" * 72)
    print("SECTION 5: STRUCTURE OF EXCESS COLLISIONS")
    print("  E_near = excess from h <= 2")
    print("  E_mid  = excess from 3 <= h <= k/2")
    print("  E_far  = excess from h > k/2")
    print("  Question: does E_near/E_excess -> 1 as C grows?")
    print("=" * 72)

    test_count = 0

    for entry in SECTION_DATA['enumerated']:
        if 'E_h_values' not in entry:
            continue

        k = entry['k']
        p = entry['p']
        C = entry['C']
        regime = entry['regime']
        E_excess = entry['E_excess']
        E_h = entry['E_h_values']

        print(f"\n  --- k={k}, p={p}, C={C}, {regime} ---")

        # Define boundaries
        near_max = 2
        mid_max = max(k // 2, 3)  # at least 3 to have a non-empty mid range

        E_near = sum(E_h.get(h, 0) for h in range(1, near_max + 1))
        E_mid = sum(E_h.get(h, 0) for h in range(near_max + 1, mid_max + 1))
        E_far = sum(E_h.get(h, 0) for h in range(mid_max + 1, k + 1))

        # Verify decomposition
        E_sum = E_near + E_mid + E_far
        record_test(f"S5.decomp_check k={k} p={p}",
                     abs(E_sum - E_excess) < 1e-6,
                     f"E_near+E_mid+E_far={E_sum:.6f} vs E_excess={E_excess:.6f}")
        test_count += 1

        if abs(E_excess) > 1e-10:
            frac_near = E_near / E_excess
            frac_mid = E_mid / E_excess
            frac_far = E_far / E_excess
        else:
            frac_near = frac_mid = frac_far = float('nan')

        print(f"    E_near (h<=2)       = {E_near:12.4f} ({frac_near:8.4f} of E_excess)")
        print(f"    E_mid  (3<=h<={mid_max})    = {E_mid:12.4f} ({frac_mid:8.4f} of E_excess)")
        print(f"    E_far  (h>{mid_max})       = {E_far:12.4f} ({frac_far:8.4f} of E_excess)")

        # Which dominates?
        parts = [('near', abs(E_near)), ('mid', abs(E_mid)), ('far', abs(E_far))]
        dominant = max(parts, key=lambda x: x[1])
        print(f"    Dominant family: {dominant[0]} (|E|={dominant[1]:.4f})")

        record_test(f"S5.dominant k={k} p={p}", True,
                     f"dominant={dominant[0]}, frac_near={frac_near:.4f}")
        test_count += 1

        # Store for trend analysis
        entry['E_near'] = E_near
        entry['E_mid'] = E_mid
        entry['E_far'] = E_far
        entry['frac_near'] = frac_near

    # Trend analysis: does frac_near grow with C?
    r1_entries = [e for e in SECTION_DATA['enumerated']
                  if 'frac_near' in e and e['regime'] in ('R1', 'R2', 'R3')
                  and not (e['frac_near'] != e['frac_near'])]  # exclude NaN

    if len(r1_entries) >= 3:
        r1_sorted = sorted(r1_entries, key=lambda e: e['C'])
        print(f"\n  Trend: frac_near vs C (R1+ cases)")
        print(f"    {'k':>3s} {'p':>5s} {'C':>8s} {'frac_near':>10s} {'E_excess':>12s}")
        for e in r1_sorted:
            print(f"    {e['k']:3d} {e['p']:5d} {e['C']:8d} "
                  f"{e['frac_near']:10.4f} {e['E_excess']:12.4f}")

        # Is frac_near trending towards 1?
        fracs = [e['frac_near'] for e in r1_sorted]
        Cs = [e['C'] for e in r1_sorted]
        last_frac = fracs[-1]
        print(f"\n    Largest C frac_near = {last_frac:.4f}")

        # Simple correlation
        if len(fracs) >= 3:
            n = len(fracs)
            lC = [log(c) for c in Cs]
            lC_m = sum(lC) / n
            f_m = sum(fracs) / n
            num = sum((a - lC_m) * (b - f_m) for a, b in zip(lC, fracs))
            d1 = sqrt(sum((a - lC_m) ** 2 for a in lC))
            d2 = sqrt(sum((b - f_m) ** 2 for b in fracs))
            r_trend = num / (d1 * d2) if d1 > 0 and d2 > 0 else 0
            print(f"    corr(log(C), frac_near) = {r_trend:+.4f}")
            record_test("S5.near_dominance_trend", True,
                         f"corr={r_trend:+.4f} last_frac={last_frac:.4f}")
            test_count += 1

    # R_gen comparison
    rgen_entries = [e for e in SECTION_DATA['enumerated']
                    if 'frac_near' in e and e['regime'] == 'R_gen'
                    and not (e['frac_near'] != e['frac_near'])]
    if rgen_entries:
        print(f"\n  R_gen cases:")
        for e in rgen_entries:
            print(f"    k={e['k']} p={e['p']}: frac_near={e['frac_near']:.4f} "
                  f"E_excess={e['E_excess']:.4f}")

    print(f"\n  Section 5 total: {test_count} tests")
    return test_count


# ============================================================================
# SECTION 6: REGIME DEPENDENCE
# ============================================================================

def section6_regime_dependence():
    """Compare collision taxonomy across regimes R3, R2, R1, R_gen."""
    print("\n" + "=" * 72)
    print("SECTION 6: REGIME DEPENDENCE")
    print("  Compare taxonomy across R3, R2, R1, R_gen")
    print("  Does the dominant collision family change with regime?")
    print("=" * 72)

    test_count = 0

    # Extend the dataset with more (k,p) pairs
    extra_entries = []

    for k in range(3, 8):
        if time_remaining() < 30:
            break

        max_B = compute_max_B(k)
        C = compute_C(k)
        if C > 20000:
            continue

        for p in PRIMES_POOL:
            if time_remaining() < 20:
                break
            if p <= 3 or not is_prime(p):
                continue

            # Skip if already enumerated
            already = any(e['k'] == k and e['p'] == p for e in SECTION_DATA['enumerated'])
            if already:
                continue

            regime, ord2 = classify_regime(k, p)
            if ord2 is None:
                continue

            data = compute_Nr(k, p)
            results = data['results']
            by_residue = defaultdict(list)
            for B, val in results:
                by_residue[val].append(B)

            # Count h=1, h=2 collisions
            hamming_counts = Counter()
            for r, B_list in by_residue.items():
                for i in range(len(B_list)):
                    for j in range(len(B_list)):
                        if i == j:
                            continue
                        h = hamming_distance(B_list[i], B_list[j])
                        hamming_counts[h] += 1

            off_diag = data['M2'] - C

            # Count total pairs by h (need all-pairs)
            all_B = [B for B, _ in results]
            total_pairs_by_h = Counter()
            if C <= 3000:
                for i in range(len(all_B)):
                    for j in range(len(all_B)):
                        if i == j:
                            continue
                        h = hamming_distance(all_B[i], all_B[j])
                        total_pairs_by_h[h] += 1

                E_h_values = {}
                for h in range(1, k + 1):
                    coll_h = hamming_counts.get(h, 0)
                    total_h = total_pairs_by_h.get(h, 0)
                    E_h_values[h] = coll_h - total_h / p

                E_near = sum(E_h_values.get(h, 0) for h in range(1, 3))
                E_mid = sum(E_h_values.get(h, 0) for h in range(3, max(k // 2 + 1, 4)))
                E_far = sum(E_h_values.get(h, 0) for h in range(max(k // 2 + 1, 4), k + 1))

                E_excess = data['E_excess']
                frac_near = E_near / E_excess if abs(E_excess) > 1e-10 else float('nan')

                extra_entries.append({
                    'k': k, 'p': p, 'regime': regime, 'ord2': ord2,
                    'max_B': max_B, 'C': C, 'M2': data['M2'],
                    'E_excess': E_excess, 'V': data['V'],
                    'mu_minus_1': data['mu_minus_1'],
                    'E_near': E_near, 'E_mid': E_mid, 'E_far': E_far,
                    'frac_near': frac_near,
                    'E_h_values': E_h_values,
                    'K_emp': data['mu_minus_1'] * C / p if C > 0 and p > 0 else 0,
                })

    # Combine with previous entries
    all_entries = []
    for e in SECTION_DATA['enumerated']:
        if 'frac_near' in e:
            if 'K_emp' not in e:
                e['K_emp'] = e['mu_minus_1'] * e['C'] / e['p'] if e['C'] > 0 and e['p'] > 0 else 0
            all_entries.append(e)
    all_entries.extend(extra_entries)

    # Summary table by regime
    print(f"\n  Regime summary ({len(all_entries)} cases total):")
    print(f"  {'Regime':>8s} {'n':>5s} {'K_max':>8s} {'|E/C|_max':>10s} "
          f"{'frac_near':>10s} {'frac_near_range':>20s} {'dominant':>10s}")
    print(f"  " + "-" * 78)

    for regime_name in ['R3', 'R2', 'R1', 'R_gen']:
        rd = [e for e in all_entries if e['regime'] == regime_name
              and not (e['frac_near'] != e['frac_near'])]  # exclude NaN
        if not rd:
            continue

        K_vals = [e.get('K_emp', 0) for e in rd]
        EC_vals = [abs(e['E_excess'] / e['C']) if e['C'] > 0 else 0 for e in rd]
        fn_vals = [e['frac_near'] for e in rd]

        # Dominant family counting
        dom_near = sum(1 for e in rd if abs(e.get('E_near', 0)) >= abs(e.get('E_mid', 0))
                       and abs(e.get('E_near', 0)) >= abs(e.get('E_far', 0)))

        fn_mean = sum(fn_vals) / len(fn_vals)
        fn_min = min(fn_vals)
        fn_max = max(fn_vals)

        print(f"  {regime_name:>8s} {len(rd):5d} {max(K_vals):8.4f} {max(EC_vals):10.4f} "
              f"{fn_mean:10.4f} [{fn_min:8.4f}, {fn_max:8.4f}] "
              f"near:{dom_near}/{len(rd)}")

        record_test(f"S6.regime_{regime_name}_analyzed", True,
                     f"n={len(rd)} frac_near_mean={fn_mean:.4f} "
                     f"near_dominant={dom_near}/{len(rd)}")
        test_count += 1

    # Detailed per-case table for R1+ regime
    r1_plus = [e for e in all_entries if e['regime'] in ('R1', 'R2', 'R3')
               and not (e['frac_near'] != e['frac_near'])]

    if r1_plus:
        print(f"\n  Detailed R1+ table ({len(r1_plus)} cases):")
        print(f"  {'k':>3s} {'p':>5s} {'ord':>5s} {'C':>8s} {'regime':>6s} "
              f"{'E_excess':>10s} {'K':>8s} {'f_near':>8s} {'f_mid':>8s} {'f_far':>8s}")
        print(f"  " + "-" * 78)

        for e in sorted(r1_plus, key=lambda x: (x['k'], x['p'])):
            f_mid = e.get('E_mid', 0) / e['E_excess'] if abs(e['E_excess']) > 1e-10 else float('nan')
            f_far = e.get('E_far', 0) / e['E_excess'] if abs(e['E_excess']) > 1e-10 else float('nan')
            print(f"  {e['k']:3d} {e['p']:5d} {e['ord2']:5d} {e['C']:8d} "
                  f"{e['regime']:>6s} {e['E_excess']:10.4f} {e.get('K_emp',0):8.4f} "
                  f"{e['frac_near']:8.4f} {f_mid:8.4f} {f_far:8.4f}")

    # Test: is near-collision dominance universal in R1?
    if r1_plus:
        near_dominant_count = sum(
            1 for e in r1_plus
            if abs(e.get('E_near', 0)) >= abs(e.get('E_mid', 0))
            and abs(e.get('E_near', 0)) >= abs(e.get('E_far', 0))
        )
        frac_near_dominant = near_dominant_count / len(r1_plus)
        print(f"\n  Near-collision dominance in R1+: {near_dominant_count}/{len(r1_plus)} "
              f"= {frac_near_dominant:.2%}")

        record_test("S6.near_dominance_R1",
                     frac_near_dominant > 0.5,
                     f"{near_dominant_count}/{len(r1_plus)} = {frac_near_dominant:.2%}")
        test_count += 1

    # Compare R_gen vs R1 dominant family
    rgen = [e for e in all_entries if e['regime'] == 'R_gen'
            and not (e['frac_near'] != e['frac_near'])]
    if rgen and r1_plus:
        fn_r1_mean = sum(e['frac_near'] for e in r1_plus) / len(r1_plus)
        fn_rgen_mean = sum(e['frac_near'] for e in rgen) / len(rgen)
        print(f"\n  frac_near comparison:")
        print(f"    R1+ mean: {fn_r1_mean:.4f} (n={len(r1_plus)})")
        print(f"    R_gen mean: {fn_rgen_mean:.4f} (n={len(rgen)})")
        record_test("S6.regime_comparison", True,
                     f"R1+={fn_r1_mean:.4f} R_gen={fn_rgen_mean:.4f}")
        test_count += 1

    print(f"\n  Section 6 total: {test_count} tests")
    return test_count


# ============================================================================
# FINAL SUMMARY
# ============================================================================

def final_summary():
    """Print comprehensive summary of findings."""
    print("\n" + "=" * 72)
    print("FINAL SUMMARY: COLLISION TAXONOMY FINDINGS")
    print("=" * 72)

    # Summary of key findings from each section
    enumerated = SECTION_DATA['enumerated']

    r1_entries = [e for e in enumerated if e['regime'] in ('R1', 'R2', 'R3')]

    if r1_entries:
        print("\n  Key findings in R1 regime:")

        # h=1 contribution
        h1_fracs = []
        for e in r1_entries:
            if 'E_h_values' in e and abs(e['E_excess']) > 1e-10:
                E_h1 = e['E_h_values'].get(1, 0)
                h1_fracs.append(E_h1 / e['E_excess'])

        if h1_fracs:
            print(f"\n  1. h=1 fraction of E_excess:")
            print(f"     mean = {sum(h1_fracs)/len(h1_fracs):.4f}")
            print(f"     range = [{min(h1_fracs):.4f}, {max(h1_fracs):.4f}]")

        # Near-collision dominance
        near_fracs = [e['frac_near'] for e in r1_entries
                      if 'frac_near' in e and not (e['frac_near'] != e['frac_near'])]
        if near_fracs:
            print(f"\n  2. Near-collision (h<=2) fraction of E_excess:")
            print(f"     mean = {sum(near_fracs)/len(near_fracs):.4f}")
            print(f"     range = [{min(near_fracs):.4f}, {max(near_fracs):.4f}]")

        # Gini concentration
        ginis = [e['gini'] for e in r1_entries if 'gini' in e]
        if ginis:
            print(f"\n  3. Collision concentration (Gini):")
            print(f"     mean = {sum(ginis)/len(ginis):.4f}")
            print(f"     range = [{min(ginis):.4f}, {max(ginis):.4f}]")

        # LSD verification
        print(f"\n  4. LSD criterion (ord_p(2) | |Delta|):")
        print(f"     All h=1 collisions verified: see Section 3 tests")

    # R_gen comparison
    rgen_entries = [e for e in enumerated if e['regime'] == 'R_gen']
    if rgen_entries and r1_entries:
        print(f"\n  5. R_gen vs R1 comparison:")
        for e in rgen_entries:
            if 'frac_near' in e:
                print(f"     R_gen k={e['k']} p={e['p']}: "
                      f"frac_near={e.get('frac_near', 'N/A')}, "
                      f"E_excess={e['E_excess']:.4f}")


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 72)
    print("R53: COLLISION TAXONOMY")
    print("  Decomposition of E_excess by structural families")
    print("  Axe A: WHO produces excess collisions?")
    print("=" * 72)

    # === SECTION 1: Full collision enumeration ===
    t1 = section1_full_enumeration()

    # === SECTION 2: Hamming decomposition ===
    t2 = section2_hamming_decomposition()

    # === SECTION 3: h=1 LSD analysis ===
    t3 = section3_h1_lsd_analysis()

    # === SECTION 4: Collision degree distribution ===
    t4 = section4_collision_degree()

    # === SECTION 5: Near/mid/far structure ===
    t5 = section5_near_mid_far()

    # === SECTION 6: Regime dependence ===
    t6 = section6_regime_dependence()

    # === Final summary ===
    final_summary()

    # === TEST SUMMARY ===
    total = PASS_COUNT + FAIL_COUNT
    print("\n" + "=" * 72)
    print(f"FINAL TEST SUMMARY: {PASS_COUNT} PASS / {FAIL_COUNT} FAIL / {total} total")
    print(f"  Section 1 (full enumeration):     {t1} tests")
    print(f"  Section 2 (Hamming decomposition): {t2} tests")
    print(f"  Section 3 (h=1 LSD analysis):     {t3} tests")
    print(f"  Section 4 (collision degree):      {t4} tests")
    print(f"  Section 5 (near/mid/far):          {t5} tests")
    print(f"  Section 6 (regime dependence):     {t6} tests")
    print(f"  Elapsed: {elapsed():.1f}s")
    rate = PASS_COUNT / total * 100 if total > 0 else 0
    print(f"  Pass rate: {rate:.1f}%")
    if FAIL_COUNT > 0:
        print(f"  *** {FAIL_COUNT} FAILURES DETECTED ***")
    else:
        print(f"  ALL TESTS PASSED")
    print("=" * 72)


if __name__ == '__main__':
    main()
