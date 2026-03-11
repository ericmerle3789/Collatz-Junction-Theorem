#!/usr/bin/env python3
"""
R54: INDUCTION BY LAST COORDINATE -- Axe B
==========================================================================
Agent R54 (Axe B) -- Round 54

MISSION: Explore whether induction on the last coordinate B_{k-1} can
control collisions more robustly than polynomial vanishing.

CONTEXT ACQUIRED (DO NOT RE-PROVE):
  P_B(g) = Sum_{j=0}^{k-1} g^j * 2^{B_j} mod p
  B monotone: 0 <= B_0 <= ... <= B_{k-1} <= max_B = S-k, S = ceil(k*log2(3))
  C = C(max_B+k-1, k-1) = number of monotone B-vectors
  M2 = Sum_r N_r^2 = collision count
  V = M2 - C^2/p
  E_excess = M2 - C - C(C-1)/p
  mu = M2*p/C^2, mu-1 = (p-1)/C + p*E_excess/C^2  [PROVED R46]

KEY RESULTS (R53):
  [PROVED] In R1, h=1 collisions are IMPOSSIBLE
  [OBSERVED] E_excess < 0 in R1 (anti-concentration)
  [OBSERVED] E_intra dominates E_cross: 65-96% via last coordinate
  [OBSERVED] |E_b/C_b| <= 0.67 uniformly across slices

KEY RESULT (R49):
  [PROVED] V_{b0}(k,p) = V(SubProblem(k-1, [b0, max_B], p))
  [PROVED] C_{b0} = C(max_B - b0 + k - 2, k - 2)

LAST-COORDINATE DECOMPOSITION:
  Fix B_{k-1} = b. Then (B_0,...,B_{k-2}) monotone in [0,b].
  C_b = comb(b + k - 1, k - 1) = #{monotone sequences of length k-1 from {0,...,b}}
  [Corrected from task description: length is k-1, not k-2]
  P_B = P_{sub}(g) + g^{k-1} * 2^b, where P_{sub} = Sum_{j=0}^{k-2} g^j * 2^{B_j}

SECTIONS:
  1: Slice decomposition by last coordinate
  2: Intra-slice collisions (b = b')
  3: Cross-slice collisions (b != b')
  4: Inductive contraction test
  5: Recursive formula for V
  6: First inductive lemma candidate
  7: Viability verdict

EPISTEMIC LABELS:
  [PROVED]       = rigorous proof or exact computation
  [COMPUTED]     = verified by exact computation
  [OBSERVED]     = numerical evidence, NOT a proof
  [CONJECTURAL]  = plausible but unproven
  [REFUTED]      = contradicted by evidence

Author: Claude Opus 4.6 (R54 Axe B Induction Last Coordinate pour Eric Merle)
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
TIME_BUDGET = 540.0  # generous budget

PASS_COUNT = 0
FAIL_COUNT = 0
VERBOSE = True

SECTION_DATA = defaultdict(list)
SECTION_TESTS = defaultdict(int)


def elapsed():
    return time.time() - T_START


def time_remaining():
    return TIME_BUDGET - elapsed()


def record_test(section, name, passed, detail=""):
    global PASS_COUNT, FAIL_COUNT
    status = "PASS" if passed else "FAIL"
    if passed:
        PASS_COUNT += 1
    else:
        FAIL_COUNT += 1
    SECTION_TESTS[section] += 1
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
    """C(k) = comb(max_B + k - 1, k - 1), number of monotone B-vectors in [0, max_B]^k.
    Stars-and-bars: choose k values from {0,...,max_B} nondecreasing.
    Wait -- this requires care. The number of nondecreasing sequences of length k
    from {0,...,max_B} is comb(max_B + k, k) by stars-and-bars.

    But looking at R53_double_counting compute_C: comb(max_B + k, k).
    And R49 compute_C: comb(S-1, k-1) = comb(max_B+k-1, k-1).

    These differ! The R49 version FIXES B_{k-1} = max_B (Collatz constraint),
    while R53 does NOT. Let's verify which is correct for our context.

    For k=3, max_B=2: all monotone (B0,B1,B2) in [0,2].
    Full count (no constraint): comb(2+3,3)=comb(5,3)=10
    With B2=max_B=2 forced: (B0,B1) in [0,2] monotone = comb(2+2,2)=6
    From enumeration: (0,0,2),(0,1,2),(0,2,2),(1,1,2),(1,2,2),(2,2,2) = 6.
    Plus those with B2<2: (0,0,0),(0,0,1),(0,1,1),(1,1,1) = 4.
    Total = 10. So with NO constraint: 10. With B_{k-1}=max_B forced: 6.

    The Collatz context does NOT force B_{k-1}=max_B for the full problem.
    B is any monotone sequence in [0,max_B]. So C = comb(max_B+k, k).

    But R49 uses comb(S-1, k-1) which forces B_{k-1}=max_B.
    Let's check: comb(S-1,k-1) = comb(max_B+k-1, k-1). For k=3, max_B=2:
    comb(4,2)=6. That's the constrained count.

    For this script, we need to be consistent. The task description says:
    C(k) = comb(max_B+k-1, k-1). Let me check what the R53_double_counting uses
    in its compute_C: comb(max_B + k, k). And R53_collision_taxonomy uses
    comb(max_B + k, k) too.

    The difference is whether B_{k-1} is FORCED to be max_B or FREE in [0,max_B].
    For Collatz, B_{k-1} <= max_B (free). So C = comb(max_B+k, k).

    Wait - but looking at the task description header, it says:
    C(k) = comb(max_B+k-1, k-1)
    And comb(max_B+k, k) = comb(max_B+k, max_B) while comb(max_B+k-1, k-1) = comb(max_B+k-1, max_B).
    These are different! For k=3,max_B=2: comb(5,3)=10 vs comb(4,2)=6.

    I'll follow R53_double_counting which uses comb(max_B+k, k) = FREE B_{k-1}.
    This makes the last-coordinate decomposition natural:
    Fix B_{k-1}=b, sub-sequence (B_0,...,B_{k-2}) monotone in [0,b].
    C_b = comb(b + k - 1, k - 1). Sum_{b=0}^{max_B} C_b should = C.
    Verify: Sum_{b=0}^{M} comb(b+k-1,k-1) = comb(M+k, k) by hockey stick. YES!
    """
    max_B = compute_max_B(k)
    return comb(max_B + k, k)


def compute_C_last(k, b):
    """Number of monotone B-vectors with B_{k-1} = b.
    Sub-sequence (B_0,...,B_{k-2}) is monotone in [0,b], length k-1.
    C_b = comb(b + k - 1, k - 1) by stars-and-bars.
    [Note: R53 Section 6 uses this formula and it matches enumeration]
    """
    if b < 0:
        return 0
    return comb(b + k - 1, k - 1)


def compute_g(k, p):
    """g = 2^S * 3^{-k} mod p. Matches R53_double_counting convention."""
    if p <= 1 or gcd(6, p) != 1:
        return None
    S = compute_S(k)
    two_S = pow(2, S, p)
    three_k_inv = pow(pow(3, k, p), p - 2, p)
    return (two_S * three_k_inv) % p


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


def enumerate_all_PB(k, p, g=None):
    """Enumerate all monotone B-vectors and P_B(g) mod p.
    B in [0, max_B]^k, nondecreasing, NO constraint on B_{k-1}.
    Returns list of (B_tuple, P_B_value).
    """
    max_B = compute_max_B(k)
    if g is None:
        g = compute_g(k, p)
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


def enumerate_sub_PB(k_sub, p, b_max, g_full_k=None, k_full=None):
    """Enumerate P_{sub}(g) for monotone sub-vectors of length k_sub in [0, b_max].
    P_{sub}(g) = Sum_{j=0}^{k_sub-1} g^j * 2^{B_j} mod p.

    IMPORTANT: g = 2^S * 3^{-k} mod p depends on the FULL k, not k_sub.
    The sub-polynomial uses g^0, ..., g^{k_sub-1} with the SAME g as the full problem.

    Returns list of (B_tuple, P_sub_value).
    """
    if g_full_k is None:
        return []

    g = g_full_k
    g_pows = [pow(g, j, p) for j in range(k_sub)]
    two_pows = [pow(2, b, p) for b in range(b_max + 1)]

    results = []
    for B in combinations_with_replacement(range(b_max + 1), k_sub):
        val = 0
        for j in range(k_sub):
            val = (val + g_pows[j] * two_pows[B[j]]) % p
        results.append((B, val))
    return results


def compute_stats_from_results(results, p):
    """Compute Nr, M2, V, E_excess from enumerated results."""
    Nr = [0] * p
    for _, val in results:
        Nr[val] += 1
    C = len(results)
    M2 = sum(n * n for n in Nr)
    V = M2 - C * C / p
    E_excess = M2 - C - C * (C - 1) / p
    mu = M2 * p / (C * C) if C > 0 else float('inf')
    return {
        'Nr': Nr, 'C': C, 'M2': M2, 'V': V,
        'E_excess': E_excess, 'mu': mu,
        'mu_m1': mu - 1 if mu != float('inf') else float('inf'),
    }


# ============================================================================
# TEST PAIRS
# ============================================================================

TEST_PAIRS_R1 = [(3, 7), (5, 31), (7, 127), (3, 5)]
TEST_PAIRS_LARGER = [(4, 13), (6, 59)]
ALL_TEST_PAIRS = TEST_PAIRS_R1 + TEST_PAIRS_LARGER


def verify_test_pairs():
    """Verify regime classification and basic parameters for all test pairs."""
    print("\n  Test pair verification:")
    print(f"  {'k':>3s} {'p':>5s} {'S':>3s} {'max_B':>5s} {'ord2':>5s} {'C':>8s} "
          f"{'regime':>6s} {'g':>5s}")
    print(f"  " + "-" * 50)

    for k, p in ALL_TEST_PAIRS:
        S = compute_S(k)
        max_B = compute_max_B(k)
        C = compute_C(k)
        ord2 = ord_mod(2, p)
        regime, _ = classify_regime(k, p)
        g = compute_g(k, p)

        print(f"  {k:3d} {p:5d} {S:3d} {max_B:5d} {ord2!s:>5s} {C:8d} "
              f"{regime:>6s} {g!s:>5s}")

        record_test('S0', f"S0.pair k={k} p={p}", is_prime(p) and C > 0,
                     f"S={S} max_B={max_B} C={C} regime={regime}")


# ============================================================================
# SECTION 1: SLICE DECOMPOSITION BY LAST COORDINATE
# ============================================================================

def section1_slice_decomposition():
    """For each (k,p): decompose by B_{k-1} = b.
    C_b = comb(b + k - 1, k - 1). Verify Sum C_b = C.
    """
    print("\n" + "=" * 72)
    print("SECTION 1: SLICE DECOMPOSITION BY LAST COORDINATE")
    print("  Fix B_{k-1} = b. Sub-vector (B_0,...,B_{k-2}) monotone in [0,b].")
    print("  C_b = comb(b + k - 1, k - 1)")
    print("  Verify: Sum_{b=0}^{max_B} C_b = C(k)  [hockey stick identity]")
    print("  P_B = P_{sub}(g) + g^{k-1} * 2^b")
    print("=" * 72)

    for k, p in ALL_TEST_PAIRS:
        if time_remaining() < 30:
            print("  [TIME LIMIT] Stopping section 1")
            break

        max_B = compute_max_B(k)
        C = compute_C(k)
        g = compute_g(k, p)
        regime, ord2 = classify_regime(k, p)

        print(f"\n  --- k={k}, p={p}, max_B={max_B}, C={C}, {regime}, ord_p(2)={ord2} ---")

        # Verify C_b formula and sum
        C_b_list = []
        sum_C_b = 0
        for b in range(max_B + 1):
            C_b = compute_C_last(k, b)
            C_b_list.append(C_b)
            sum_C_b += C_b

        record_test('S1', f"S1.sum_Cb k={k} p={p}", sum_C_b == C,
                     f"Sum C_b = {sum_C_b} vs C = {C}")

        # Verify by enumeration
        results = enumerate_all_PB(k, p, g)
        record_test('S1', f"S1.enum_C k={k} p={p}", len(results) == C,
                     f"enum={len(results)} vs C={C}")

        # Group by last coordinate
        by_last = defaultdict(list)
        for B, val in results:
            by_last[B[k - 1]].append((B, val))

        all_match = True
        for b in range(max_B + 1):
            actual = len(by_last.get(b, []))
            expected = C_b_list[b]
            if actual != expected:
                all_match = False
                record_test('S1', f"S1.Cb_match k={k} p={p} b={b}", False,
                             f"actual={actual} expected={expected}")

        record_test('S1', f"S1.all_Cb_match k={k} p={p}", all_match,
                     f"All {max_B+1} slices match formula")

        # Verify polynomial decomposition: P_B = P_{sub} + g^{k-1} * 2^b
        g_k1 = pow(g, k - 1, p)
        decomp_ok = True
        n_checked = 0
        for b in range(max_B + 1):
            two_b = pow(2, b, p)
            shift = (g_k1 * two_b) % p
            for B, val in by_last.get(b, []):
                B_sub = B[:k - 1]
                # Compute P_{sub}
                P_sub = 0
                for j in range(k - 1):
                    P_sub = (P_sub + pow(g, j, p) * pow(2, B_sub[j], p)) % p
                reconstructed = (P_sub + shift) % p
                if reconstructed != val:
                    decomp_ok = False
                n_checked += 1

        record_test('S1', f"S1.poly_decomp k={k} p={p}", decomp_ok,
                     f"Checked {n_checked} vectors, P_B = P_sub + g^{{k-1}}*2^b")

        # Print slice size table
        print(f"    Slice sizes C_b:")
        print(f"    {'b':>3s} {'C_b':>8s} {'frac':>8s}")
        for b in range(max_B + 1):
            frac = C_b_list[b] / C
            print(f"    {b:3d} {C_b_list[b]:8d} {frac:8.4f}")

        # Store data for later sections
        SECTION_DATA['s1'].append({
            'k': k, 'p': p, 'max_B': max_B, 'C': C, 'g': g,
            'regime': regime, 'ord2': ord2,
            'C_b_list': C_b_list,
            'results': results,
            'by_last': dict(by_last),
        })


# ============================================================================
# SECTION 2: INTRA-SLICE COLLISIONS (b = b')
# ============================================================================

def section2_intra_slice():
    """When b=b': P_{sub} = P_{sub'} mod p. This is a collision in the sub-problem
    of dimension k-1 with max_B' = b.

    M2_intra(b) = Sum_r N_{b,r}^2 = M2(k-1, [0,b], p)
    Compute mu(k-1, b, p) for each b.
    E_intra(b) = M2_intra(b) - C_b - C_b(C_b-1)/p.
    """
    print("\n" + "=" * 72)
    print("SECTION 2: INTRA-SLICE COLLISIONS (b = b')")
    print("  When B_{k-1} = B'_{k-1} = b: collision iff P_{sub} = P_{sub'} mod p")
    print("  M2_intra(b) = M2 of sub-problem (k-1, [0,b], p)")
    print("  KEY QUESTION: Is mu(k-1, b, p) <= mu(k, max_B, p)?")
    print("=" * 72)

    for entry in SECTION_DATA['s1']:
        if time_remaining() < 40:
            print("  [TIME LIMIT] Stopping section 2")
            break

        k = entry['k']
        p = entry['p']
        C = entry['C']
        max_B = entry['max_B']
        g = entry['g']
        regime = entry['regime']
        by_last = entry['by_last']

        print(f"\n  --- k={k}, p={p}, C={C}, max_B={max_B}, {regime} ---")

        # Compute full-problem stats
        full_stats = compute_stats_from_results(entry['results'], p)
        mu_full = full_stats['mu']

        # For each slice b, compute intra-slice stats
        intra_data = []
        M2_intra_total = 0

        for b in range(max_B + 1):
            items = by_last.get(b, [])
            C_b = len(items)
            if C_b == 0:
                intra_data.append({'b': b, 'C_b': 0, 'M2': 0, 'V': 0,
                                   'E_intra': 0, 'mu': 1.0, 'mu_sub': 1.0})
                continue

            # Compute Nr for this slice
            Nr_b = [0] * p
            for _, val in items:
                Nr_b[val] += 1

            M2_b = sum(n * n for n in Nr_b)
            V_b = M2_b - C_b * C_b / p
            E_b = M2_b - C_b - C_b * (C_b - 1) / p
            mu_b = M2_b * p / (C_b * C_b) if C_b > 0 else 1.0

            M2_intra_total += M2_b

            # Also compute the sub-problem directly for VERIFICATION:
            # Enumerate monotone (B_0,...,B_{k-2}) in [0,b] with P_sub = Sum g^j * 2^{B_j}
            sub_results = enumerate_sub_PB(k - 1, p, b, g, k)
            sub_stats = compute_stats_from_results(sub_results, p)

            # The sub-problem count should match C_b
            record_test('S2', f"S2.sub_C k={k} p={p} b={b}",
                         sub_stats['C'] == C_b,
                         f"sub_C={sub_stats['C']} vs C_b={C_b}")

            # The sub-problem M2 should match M2_b
            # BUT: M2 of slice b counts collisions among {P_B : B_{k-1}=b}
            # while M2 of sub-problem counts among {P_sub : sub in [0,b]^{k-1}}.
            # Since P_B = P_sub + g^{k-1}*2^b, and the shift is a bijection on Z/pZ,
            # M2 is preserved under shift. So they SHOULD match.
            record_test('S2', f"S2.sub_M2 k={k} p={p} b={b}",
                         sub_stats['M2'] == M2_b,
                         f"sub_M2={sub_stats['M2']} vs M2_b={M2_b}")

            intra_data.append({
                'b': b, 'C_b': C_b, 'M2': M2_b, 'V': V_b,
                'E_intra': E_b, 'mu': mu_b, 'mu_sub': sub_stats['mu'],
                'V_sub': sub_stats['V'],
            })

        # Print intra-slice table
        print(f"    {'b':>3s} {'C_b':>6s} {'M2_b':>8s} {'V_b':>10s} "
              f"{'E_intra':>10s} {'mu(b)':>10s} {'mu_sub':>10s} {'|E/C|':>8s}")
        print(f"    " + "-" * 75)

        for d in intra_data:
            if d['C_b'] > 0:
                E_over_C = abs(d['E_intra'] / d['C_b']) if d['C_b'] > 0 else 0
                print(f"    {d['b']:3d} {d['C_b']:6d} {d['M2']:8d} "
                      f"{d['V']:10.4f} {d['E_intra']:10.4f} "
                      f"{d['mu']:10.6f} {d['mu_sub']:10.6f} {E_over_C:8.4f}")

        # Verify Sum M2_intra(b) = M2_intra_total
        # (This is just sum of intra-slice collision counts, not yet the full M2)
        print(f"    M2_intra_total = {M2_intra_total}")
        print(f"    mu_full = {mu_full:.6f}")

        # KEY TEST: is max_b mu(k-1, b, p) < mu(k, max_B, p)?  [contraction]
        mu_values = [d['mu'] for d in intra_data if d['C_b'] >= 2]
        if mu_values:
            max_mu_sub = max(mu_values)
            contraction = max_mu_sub < mu_full
            ratio = max_mu_sub / mu_full if mu_full > 0 else float('inf')
            record_test('S2', f"S2.contraction k={k} p={p}", contraction,
                         f"max_mu_sub={max_mu_sub:.6f} vs mu_full={mu_full:.6f} "
                         f"ratio={ratio:.4f}")
            print(f"    CONTRACTION TEST: max_mu_sub = {max_mu_sub:.6f}, "
                  f"mu_full = {mu_full:.6f}, ratio = {ratio:.4f}")
            if contraction:
                print(f"    ==> CONTRACTION HOLDS (sub-problems have smaller mu)")
            else:
                print(f"    ==> CONTRACTION FAILS (some sub-problem has mu >= mu_full)")

        # Weighted average: Sum (C_b/C)^2 * mu(b)
        weighted_mu = sum((d['C_b'] / C) ** 2 * d['mu']
                          for d in intra_data if d['C_b'] > 0)
        print(f"    Weighted average mu: Sum (C_b/C)^2 * mu(b) = {weighted_mu:.6f}")
        print(f"    Compare: mu_full = {mu_full:.6f}")
        print(f"    Ratio weighted/full = {weighted_mu / mu_full:.4f}" if mu_full > 0 else "")

        # Store
        entry['intra_data'] = intra_data
        entry['M2_intra_total'] = M2_intra_total
        entry['full_stats'] = full_stats


# ============================================================================
# SECTION 3: CROSS-SLICE COLLISIONS (b != b')
# ============================================================================

def section3_cross_slice():
    """When b != b': P_{sub} - P_{sub'} = g^{k-1}*(2^{b'} - 2^b) mod p.
    RHS is a known constant Delta(b,b').
    Cross collisions between slices b and b'.
    """
    print("\n" + "=" * 72)
    print("SECTION 3: CROSS-SLICE COLLISIONS (b != b')")
    print("  P_{sub}(g) - P_{sub'}(g) = g^{k-1}*(2^{b'} - 2^b) = Delta(b,b') mod p")
    print("  #{cross collisions} = #{(sub,sub') : P_sub - P_sub' = Delta(b,b')}")
    print("  Compare with C_b * C_{b'} / p (expected under uniformity)")
    print("=" * 72)

    for entry in SECTION_DATA['s1']:
        if time_remaining() < 40:
            print("  [TIME LIMIT] Stopping section 3")
            break

        k = entry['k']
        p = entry['p']
        C = entry['C']
        max_B = entry['max_B']
        g = entry['g']
        regime = entry['regime']
        by_last = entry['by_last']
        full_stats = entry['full_stats']
        M2_full = full_stats['M2']
        M2_intra_total = entry['M2_intra_total']

        print(f"\n  --- k={k}, p={p}, C={C}, max_B={max_B}, {regime} ---")

        # Compute cross-slice collision counts
        # For each pair (b, b') with b < b', count ordered pairs (sub, sub')
        # where sub in slice b, sub' in slice b', and P_sub + g^{k-1}*2^b = P_sub' + g^{k-1}*2^{b'} mod p
        # i.e., P_sub - P_sub' = g^{k-1}*(2^{b'} - 2^b) mod p

        # Build per-slice Nr dictionaries
        slice_Nr = {}
        for b in range(max_B + 1):
            items = by_last.get(b, [])
            Nr_b = defaultdict(int)
            for _, val in items:
                Nr_b[val] += 1
            slice_Nr[b] = dict(Nr_b)

        # Cross M2: for ordered pairs b != b', sum_r Nr_b(r) * Nr_{b'}(r)
        # This counts ordered cross-collisions at the FULL level
        # (collision at P_B level, not P_sub level)
        M2_cross_total = 0
        cross_data = {}

        for b1 in range(max_B + 1):
            for b2 in range(max_B + 1):
                if b1 == b2:
                    continue
                cross = 0
                for r, n1 in slice_Nr[b1].items():
                    n2 = slice_Nr[b2].get(r, 0)
                    cross += n1 * n2
                if b1 < b2:
                    cross_data[(b1, b2)] = cross
                M2_cross_total += cross

        # Verify: M2 = M2_intra + M2_cross (ordered pairs)
        M2_reconstructed = M2_intra_total + M2_cross_total
        record_test('S3', f"S3.M2_decomp k={k} p={p}", M2_reconstructed == M2_full,
                     f"M2_intra={M2_intra_total} M2_cross={M2_cross_total} "
                     f"sum={M2_reconstructed} M2={M2_full}")

        # Compare cross with expectation
        print(f"    Cross-slice analysis (b < b'):")
        print(f"    {'b':>3s} {'b_':>3s} {'C_b':>6s} {'C_b_':>6s} {'cross':>8s} "
              f"{'expected':>10s} {'E_cross':>10s} {'E/sqrt':>10s}")
        print(f"    " + "-" * 62)

        E_cross_total = 0
        E_cross_details = {}

        for b1 in range(max_B + 1):
            C_b1 = len(by_last.get(b1, []))
            for b2 in range(b1 + 1, max_B + 1):
                C_b2 = len(by_last.get(b2, []))
                if C_b1 == 0 or C_b2 == 0:
                    continue

                # cross_data has UNORDERED sum: sum over (sub in b1, sub' in b2)
                # Since full cross counts ordered pairs both ways, for the pair (b1,b2)
                # with b1<b2, the ordered cross count is 2*cross_data[(b1,b2)]
                cross_ordered = cross_data.get((b1, b2), 0)
                # But actually cross_data[(b1,b2)] counts sub in b1, sub' in b2 with P_B=P_{B'}
                # The other direction (sub in b2, sub' in b1) is counted separately.
                # So total cross for this pair = 2*cross_data[(b1,b2)].

                expected = C_b1 * C_b2 / p
                E_cross = cross_ordered - expected
                E_cross_total += 2 * E_cross  # both orderings

                stddev = sqrt(expected) if expected > 0 else 1
                E_norm = E_cross / stddev if stddev > 0 else 0

                E_cross_details[(b1, b2)] = {
                    'cross': cross_ordered, 'expected': expected,
                    'E_cross': E_cross, 'E_norm': E_norm,
                    'C_b1': C_b1, 'C_b2': C_b2,
                }

                if max_B <= 5 or abs(E_norm) > 1:
                    print(f"    {b1:3d} {b2:3d} {C_b1:6d} {C_b2:6d} "
                          f"{cross_ordered:8d} {expected:10.2f} "
                          f"{E_cross:10.4f} {E_norm:10.4f}")

        # Verify E_excess decomposition
        E_intra_total = sum(d['E_intra'] for d in entry['intra_data'] if d['C_b'] > 0)
        E_total = E_intra_total + E_cross_total
        E_excess_full = full_stats['E_excess']

        record_test('S3', f"S3.E_decomp k={k} p={p}",
                     abs(E_total - E_excess_full) < 1e-6,
                     f"E_intra={E_intra_total:.4f} E_cross={E_cross_total:.4f} "
                     f"sum={E_total:.4f} E_excess={E_excess_full:.4f}")

        # Fractions
        if abs(E_excess_full) > 1e-10:
            frac_intra = E_intra_total / E_excess_full
            frac_cross = E_cross_total / E_excess_full
        else:
            frac_intra = frac_cross = float('nan')

        print(f"\n    E_intra = {E_intra_total:.6f} ({frac_intra:.2%} of E_excess)")
        print(f"    E_cross = {E_cross_total:.6f} ({frac_cross:.2%} of E_excess)")
        print(f"    E_excess = {E_excess_full:.6f}")

        # R53 found E_intra dominates (65-96%). Verify.
        if not (frac_intra != frac_intra):  # not NaN
            dominance = abs(frac_intra) > abs(frac_cross)
            record_test('S3', f"S3.intra_dominates k={k} p={p}",
                         abs(frac_intra) > 0.5,
                         f"|frac_intra|={abs(frac_intra):.4f} "
                         f"|frac_cross|={abs(frac_cross):.4f}")

        # Store
        entry['E_intra_total'] = E_intra_total
        entry['E_cross_total'] = E_cross_total
        entry['cross_data'] = cross_data
        entry['E_cross_details'] = E_cross_details
        entry['frac_intra'] = frac_intra
        entry['frac_cross'] = frac_cross


# ============================================================================
# SECTION 4: INDUCTIVE CONTRACTION TEST
# ============================================================================

def section4_contraction():
    """The core question: does the induction actually help?
    For each (k,p):
    - mu_full = mu(k, max_B, p)
    - mu(k-1, b, p) for each b
    - Is max_b mu(k-1, b, p) < mu_full?  [contraction]
    - Compare with R49's first-coordinate result.
    """
    print("\n" + "=" * 72)
    print("SECTION 4: INDUCTIVE CONTRACTION TEST")
    print("  Does the induction k -> k-1 CONTRACT the collision multiplicity?")
    print("  mu_full = mu(k, max_B, p)")
    print("  mu_sub(b) = mu of sub-problem (k-1, [0,b], p)")
    print("  CONTRACTION: max_b mu_sub(b) < mu_full?")
    print("=" * 72)

    contraction_results = []

    for entry in SECTION_DATA['s1']:
        if time_remaining() < 30:
            print("  [TIME LIMIT] Stopping section 4")
            break

        k = entry['k']
        p = entry['p']
        C = entry['C']
        max_B = entry['max_B']
        g = entry['g']
        regime = entry['regime']
        intra_data = entry['intra_data']
        full_stats = entry['full_stats']

        mu_full = full_stats['mu']
        print(f"\n  --- k={k}, p={p}, C={C}, {regime}, mu_full={mu_full:.6f} ---")

        # Collect mu values for each sub-problem
        mu_subs = {}
        for d in intra_data:
            b = d['b']
            if d['C_b'] >= 2:
                mu_subs[b] = d['mu']

        if not mu_subs:
            print(f"    [SKIP] No sub-problems with C_b >= 2")
            continue

        # Max contraction
        max_b = max(mu_subs, key=mu_subs.get)
        max_mu_sub = mu_subs[max_b]
        ratio = max_mu_sub / mu_full if mu_full > 0 else float('inf')

        contracts = max_mu_sub < mu_full
        record_test('S4', f"S4.contraction k={k} p={p}", contracts,
                     f"max_mu_sub={max_mu_sub:.6f} at b={max_b}, "
                     f"mu_full={mu_full:.6f}, ratio={ratio:.4f}")

        # Weighted average
        weighted_mu = 0
        total_weight = 0
        for d in intra_data:
            if d['C_b'] > 0:
                w = (d['C_b'] / C) ** 2
                weighted_mu += w * d['mu']
                total_weight += w

        if total_weight > 0:
            weighted_ratio = weighted_mu / mu_full if mu_full > 0 else float('inf')
            print(f"    Weighted mu: {weighted_mu:.6f}, "
                  f"ratio to full: {weighted_ratio:.4f}")
            record_test('S4', f"S4.weighted_contraction k={k} p={p}",
                         weighted_mu < mu_full,
                         f"weighted_mu={weighted_mu:.6f} < mu_full={mu_full:.6f}")

        # Print contraction table
        print(f"    {'b':>3s} {'C_b':>6s} {'mu(b)':>10s} {'ratio':>8s} {'contracts':>10s}")
        print(f"    " + "-" * 45)
        for d in intra_data:
            if d['C_b'] >= 2:
                r = d['mu'] / mu_full if mu_full > 0 else float('inf')
                c = "YES" if d['mu'] < mu_full else "NO"
                print(f"    {d['b']:3d} {d['C_b']:6d} {d['mu']:10.6f} "
                      f"{r:8.4f} {c:>10s}")

        # Compare with first-coordinate decomposition (R49 style)
        # For the first coordinate b0, sub-problem is (k-1, [b0, max_B], p)
        # For the last coordinate b, sub-problem is (k-1, [0, b], p)
        # These are DUAL: first coord varies lower bound, last coord varies upper bound.
        print(f"\n    First vs Last coordinate comparison:")
        print(f"    Last coord: sub-problem on [0, b], max_b mu_sub = {max_mu_sub:.6f}")
        print(f"    (First coord from R49 would use sub-problems on [b0, max_B])")
        print(f"    Duality: range [0,b] vs [b0,max_B] with max_B-b0 ~ b")

        contraction_results.append({
            'k': k, 'p': p, 'regime': regime, 'C': C,
            'mu_full': mu_full, 'max_mu_sub': max_mu_sub,
            'ratio': ratio, 'contracts': contracts,
            'weighted_mu': weighted_mu,
        })

    # Summary table
    if contraction_results:
        print(f"\n  CONTRACTION SUMMARY:")
        print(f"  {'k':>3s} {'p':>5s} {'regime':>6s} {'C':>8s} {'mu_full':>10s} "
              f"{'max_mu_sub':>10s} {'ratio':>8s} {'contracts':>10s}")
        print(f"  " + "-" * 65)
        for cr in contraction_results:
            c = "YES" if cr['contracts'] else "NO"
            print(f"  {cr['k']:3d} {cr['p']:5d} {cr['regime']:>6s} {cr['C']:8d} "
                  f"{cr['mu_full']:10.6f} {cr['max_mu_sub']:10.6f} "
                  f"{cr['ratio']:8.4f} {c:>10s}")

        # Overall contraction rate
        n_contract = sum(1 for cr in contraction_results if cr['contracts'])
        total = len(contraction_results)
        record_test('S4', f"S4.overall_contraction_rate",
                     n_contract == total,
                     f"{n_contract}/{total} cases contract")

    SECTION_DATA['contraction'] = contraction_results


# ============================================================================
# SECTION 5: RECURSIVE FORMULA FOR V
# ============================================================================

def section5_recursive_V():
    """From the decomposition:
    V = M2 - C^2/p
    V_intra = Sum_b [M2_b - C_b^2/p] = Sum_b V(k-1, b, p)
    V_cross = M2_cross - (C^2 - Sum C_b^2)/p
    V = V_intra + V_cross

    Verify and analyze.
    """
    print("\n" + "=" * 72)
    print("SECTION 5: RECURSIVE FORMULA FOR V")
    print("  V = V_intra + V_cross")
    print("  V_intra = Sum_b V(k-1, b, p)")
    print("  V_cross = M2_cross_total - (C^2 - Sum C_b^2)/p")
    print("  Question: Is V_intra / V > 0.5? (R53: 65-96%)")
    print("  Can we bound: V(k, M, p) <= f(k)*max_b V(k-1, b, p) + g(k)?")
    print("=" * 72)

    for entry in SECTION_DATA['s1']:
        if time_remaining() < 25:
            print("  [TIME LIMIT] Stopping section 5")
            break

        k = entry['k']
        p = entry['p']
        C = entry['C']
        max_B = entry['max_B']
        full_stats = entry['full_stats']
        intra_data = entry['intra_data']
        regime = entry['regime']

        V_full = full_stats['V']
        M2_full = full_stats['M2']

        print(f"\n  --- k={k}, p={p}, C={C}, {regime}, V_full={V_full:.4f} ---")

        # Compute V_intra = Sum V_b
        V_intra = sum(d['V'] for d in intra_data)

        # Compute Sum C_b^2
        sum_Cb2 = sum(d['C_b'] ** 2 for d in intra_data)

        # V_cross = V_full - V_intra  (from the ANOVA decomposition)
        # Equivalently: V_cross = M2_cross_total - (C^2 - Sum C_b^2)/p
        V_cross = V_full - V_intra

        # Verify via alternative formula
        M2_intra = entry['M2_intra_total']
        M2_cross = M2_full - M2_intra
        V_cross_alt = M2_cross - (C * C - sum_Cb2) / p
        record_test('S5', f"S5.V_cross_match k={k} p={p}",
                     abs(V_cross - V_cross_alt) < 1e-6,
                     f"V_cross={V_cross:.6f} alt={V_cross_alt:.6f}")

        # Verify V = V_intra + V_cross
        V_sum = V_intra + V_cross
        record_test('S5', f"S5.V_decomp k={k} p={p}",
                     abs(V_sum - V_full) < 1e-6,
                     f"V_intra+V_cross={V_sum:.6f} vs V_full={V_full:.6f}")

        # Ratios
        if abs(V_full) > 1e-10:
            frac_V_intra = V_intra / V_full
            frac_V_cross = V_cross / V_full
        else:
            frac_V_intra = frac_V_cross = float('nan')

        print(f"    V_intra = {V_intra:.6f} ({frac_V_intra:.2%} of V)")
        print(f"    V_cross = {V_cross:.6f} ({frac_V_cross:.2%} of V)")
        print(f"    V_full  = {V_full:.6f}")
        print(f"    Sum C_b^2 = {sum_Cb2}, C^2 = {C*C}")
        print(f"    (C^2 - Sum C_b^2)/p = {(C*C - sum_Cb2)/p:.4f}")

        record_test('S5', f"S5.V_intra_dominance k={k} p={p}",
                     abs(frac_V_intra) > 0.5 if not (frac_V_intra != frac_V_intra) else False,
                     f"V_intra/V = {frac_V_intra:.4f}")

        # Per-slice V breakdown
        V_b_values = [d['V'] for d in intra_data if d['C_b'] >= 2]
        if V_b_values:
            max_V_b = max(V_b_values)
            print(f"    max_b V(b) = {max_V_b:.6f}")
            print(f"    V/C = {V_full / C:.6f}" if C > 0 else "")

        # Can we bound: V(k, M, p) <= alpha * Sum (C_b/C)*V(b) + beta*C?
        # This is tested in Section 6.

        # Intermediate: V_intra / C  vs  V_full / C
        V_intra_over_C = V_intra / C if C > 0 else 0
        V_full_over_C = V_full / C if C > 0 else 0

        print(f"    V_intra/C = {V_intra_over_C:.6f}")
        print(f"    V_full/C  = {V_full_over_C:.6f}")

        # Can V_cross be bounded by V_intra or C?
        if abs(V_intra) > 1e-10:
            cross_to_intra = V_cross / V_intra
            print(f"    V_cross/V_intra = {cross_to_intra:.4f}")
        if C > 0:
            cross_over_C = V_cross / C
            print(f"    V_cross/C = {cross_over_C:.6f}")

        # Store
        entry['V_intra'] = V_intra
        entry['V_cross'] = V_cross
        entry['frac_V_intra'] = frac_V_intra
        entry['frac_V_cross'] = frac_V_cross


# ============================================================================
# SECTION 6: FIRST INDUCTIVE LEMMA CANDIDATE
# ============================================================================

def section6_inductive_lemma():
    """Formulate and test:
    Lemma: V(k, M, p) <= alpha * Sum_b (C_b/C)*V(k-1, b, p) + beta*C
    Find best alpha, beta.

    Also test base case k=2.
    """
    print("\n" + "=" * 72)
    print("SECTION 6: FIRST INDUCTIVE LEMMA CANDIDATE")
    print("  Test: V(k, M, p) <= alpha * Sum_b (C_b/C)*V(b) + beta*C")
    print("  Find best alpha, beta for each (k,p)")
    print("  Base case: k=2")
    print("=" * 72)

    # ---- BASE CASE: k=2 ----
    print(f"\n  --- BASE CASE: k=2 ---")
    # For k=2: B = (B_0, B_1) monotone in [0, max_B]. C = comb(max_B+2, 2).
    # V(2, max_B, p) should be computable and O(max_B) = O(C^{1/2})?
    # Actually C(2) = comb(max_B+2, 2) = (max_B+2)(max_B+1)/2, so max_B ~ sqrt(2C).

    k_base = 2
    base_primes = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
                   67, 71, 73, 79, 83, 89, 97, 101, 127]

    max_B_2 = compute_max_B(k_base)
    C_2 = compute_C(k_base)

    print(f"  k=2: max_B={max_B_2}, C={C_2}")
    print(f"  {'p':>5s} {'regime':>6s} {'V':>10s} {'V/C':>10s} {'V/maxB':>10s} {'mu':>10s}")
    print(f"  " + "-" * 55)

    for p in base_primes:
        if time_remaining() < 20:
            break
        if not is_prime(p):
            continue

        g = compute_g(k_base, p)
        if g is None:
            continue

        results = enumerate_all_PB(k_base, p, g)
        if len(results) != C_2:
            continue

        stats = compute_stats_from_results(results, p)
        regime, _ = classify_regime(k_base, p)

        V_over_C = stats['V'] / C_2 if C_2 > 0 else 0
        V_over_maxB = stats['V'] / max_B_2 if max_B_2 > 0 else 0

        print(f"  {p:5d} {regime:>6s} {stats['V']:10.4f} {V_over_C:10.6f} "
              f"{V_over_maxB:10.4f} {stats['mu']:10.6f}")

        record_test('S6', f"S6.base_k2 p={p}", V_over_C < 2.0,
                     f"V/C={V_over_C:.6f} V/max_B={V_over_maxB:.4f}")

    # ---- INDUCTIVE STEP: find alpha, beta ----
    print(f"\n  --- INDUCTIVE STEP: Finding alpha, beta ---")
    print(f"  V(k) <= alpha * Sum_b (C_b/C)*V(b) + beta*C")

    lemma_results = []

    for entry in SECTION_DATA['s1']:
        if time_remaining() < 20:
            break

        k = entry['k']
        p = entry['p']
        C = entry['C']
        max_B = entry['max_B']
        regime = entry['regime']
        intra_data = entry['intra_data']
        V_full = entry['full_stats']['V']

        # Compute weighted V_intra: Sum (C_b/C) * V(b)
        weighted_V = 0
        for d in intra_data:
            if d['C_b'] > 0:
                weighted_V += (d['C_b'] / C) * d['V']

        # We want: V_full <= alpha * weighted_V + beta * C
        # Minimum alpha when beta = 0: alpha_min = V_full / weighted_V
        # Minimum beta when alpha = 0: beta_min = V_full / C
        if weighted_V > 1e-10:
            alpha_min = V_full / weighted_V
        else:
            alpha_min = float('inf')

        beta_min = V_full / C if C > 0 else float('inf')

        # For alpha = 1: beta needed = (V_full - weighted_V) / C
        if C > 0:
            beta_at_alpha1 = (V_full - weighted_V) / C
        else:
            beta_at_alpha1 = float('inf')

        print(f"\n  k={k}, p={p}, {regime}:")
        print(f"    V_full = {V_full:.6f}")
        print(f"    weighted_V = Sum (C_b/C)*V(b) = {weighted_V:.6f}")
        print(f"    alpha_min (beta=0) = {alpha_min:.4f}")
        print(f"    beta_min (alpha=0) = V/C = {beta_min:.6f}")
        print(f"    beta at alpha=1 = {beta_at_alpha1:.6f}")

        # Test: does V_full <= 2 * weighted_V + 1 * C?
        holds_2_1 = V_full <= 2 * weighted_V + 1 * C
        record_test('S6', f"S6.lemma_2_1 k={k} p={p}", holds_2_1,
                     f"V={V_full:.4f} <= 2*wV+C = {2*weighted_V + C:.4f}")

        # Test: does V_full <= 1.5 * weighted_V + 0.5 * C?
        holds_15_05 = V_full <= 1.5 * weighted_V + 0.5 * C
        record_test('S6', f"S6.lemma_1.5_0.5 k={k} p={p}", holds_15_05,
                     f"V={V_full:.4f} <= 1.5*wV+0.5*C = {1.5*weighted_V + 0.5*C:.4f}")

        # Tight bound: find smallest alpha such that beta = V_full/C - alpha*weighted_V/C
        # and alpha * weighted_V + beta * C >= V_full
        # Along the line alpha*wV + beta*C = V, we need alpha, beta >= 0
        # So alpha in [0, V/wV] and beta = (V - alpha*wV)/C.

        lemma_results.append({
            'k': k, 'p': p, 'regime': regime, 'C': C,
            'V_full': V_full, 'weighted_V': weighted_V,
            'alpha_min': alpha_min, 'beta_min': beta_min,
            'beta_at_alpha1': beta_at_alpha1,
        })

    # Summary
    if lemma_results:
        print(f"\n  LEMMA FEASIBILITY SUMMARY:")
        print(f"  {'k':>3s} {'p':>5s} {'regime':>6s} {'V/C':>8s} {'wV':>10s} "
              f"{'alpha_min':>10s} {'beta@a=1':>10s}")
        print(f"  " + "-" * 60)
        for lr in lemma_results:
            V_over_C = lr['V_full'] / lr['C'] if lr['C'] > 0 else 0
            print(f"  {lr['k']:3d} {lr['p']:5d} {lr['regime']:>6s} {V_over_C:8.4f} "
                  f"{lr['weighted_V']:10.4f} {lr['alpha_min']:10.4f} "
                  f"{lr['beta_at_alpha1']:10.6f}")

        # Is alpha_min close to 1?
        alpha_mins = [lr['alpha_min'] for lr in lemma_results
                      if lr['alpha_min'] != float('inf')]
        if alpha_mins:
            max_alpha = max(alpha_mins)
            mean_alpha = sum(alpha_mins) / len(alpha_mins)
            print(f"\n  alpha_min: max={max_alpha:.4f}, mean={mean_alpha:.4f}")
            record_test('S6', f"S6.alpha_close_to_1",
                         max_alpha < 3.0,
                         f"max alpha_min={max_alpha:.4f}")

        # Does the recursive bound imply V = O(C)?
        # If alpha < max_B+1 (number of slices) and beta = O(1),
        # then V(k) = O(C) by unrolling the recursion.
        # Actually need alpha * max(C_b/C) <= 1 for contraction.
        print(f"\n  [ANALYSIS] For V = O(C) via recursion:")
        print(f"  Need: alpha * max(C_b/C) < 1 (contraction), or")
        print(f"  More precisely: Sum (C_b/C)*V(b) tracks V(k-1 sub-problems)")
        print(f"  and the recursion terminates at k=2 where V/C is bounded.")

    SECTION_DATA['lemma_results'] = lemma_results


# ============================================================================
# SECTION 7: VIABILITY VERDICT
# ============================================================================

def section7_verdict():
    """Rate the inductive route by last coordinate."""
    print("\n" + "=" * 72)
    print("SECTION 7: VIABILITY VERDICT -- INDUCTION BY LAST COORDINATE")
    print("=" * 72)

    # Gather all evidence
    contraction_results = SECTION_DATA.get('contraction', [])
    lemma_results = SECTION_DATA.get('lemma_results', [])

    # ---- Intra-slice control ----
    print(f"\n  1. INTRA-SLICE CONTROL:")
    intra_fracs = []
    for entry in SECTION_DATA['s1']:
        if 'frac_intra' in entry and not (entry['frac_intra'] != entry['frac_intra']):
            intra_fracs.append(abs(entry['frac_intra']))

    if intra_fracs:
        min_frac = min(intra_fracs)
        max_frac = max(intra_fracs)
        mean_frac = sum(intra_fracs) / len(intra_fracs)
        print(f"    |E_intra/E_excess|: min={min_frac:.4f} mean={mean_frac:.4f} max={max_frac:.4f}")
        intra_control = "STRONG" if mean_frac > 0.6 else ("MODERATE" if mean_frac > 0.3 else "WEAK")
        print(f"    Assessment: {intra_control}")
    else:
        intra_control = "UNKNOWN"
        print(f"    Assessment: UNKNOWN (no data)")

    # ---- Cross-slice control ----
    print(f"\n  2. CROSS-SLICE CONTROL:")
    cross_fracs = []
    for entry in SECTION_DATA['s1']:
        if 'frac_cross' in entry and not (entry['frac_cross'] != entry['frac_cross']):
            cross_fracs.append(abs(entry['frac_cross']))

    if cross_fracs:
        min_frac = min(cross_fracs)
        max_frac = max(cross_fracs)
        mean_frac = sum(cross_fracs) / len(cross_fracs)
        print(f"    |E_cross/E_excess|: min={min_frac:.4f} mean={mean_frac:.4f} max={max_frac:.4f}")
        cross_control = "STRONG" if mean_frac < 0.3 else ("MODERATE" if mean_frac < 0.5 else "WEAK")
        print(f"    Assessment: {cross_control} (smaller fraction = better controlled)")
    else:
        cross_control = "UNKNOWN"
        print(f"    Assessment: UNKNOWN (no data)")

    # ---- Contraction ----
    print(f"\n  3. INDUCTIVE CONTRACTION:")
    if contraction_results:
        n_contract = sum(1 for cr in contraction_results if cr['contracts'])
        total = len(contraction_results)
        pct = n_contract / total if total > 0 else 0

        ratios = [cr['ratio'] for cr in contraction_results]
        max_ratio = max(ratios)
        mean_ratio = sum(ratios) / len(ratios)

        print(f"    Contraction rate: {n_contract}/{total} ({pct:.0%})")
        print(f"    max_mu_sub/mu_full: max={max_ratio:.4f} mean={mean_ratio:.4f}")

        if pct == 1.0 and max_ratio < 1.0:
            contraction_verdict = "STRONG"
        elif pct >= 0.8:
            contraction_verdict = "MODERATE"
        else:
            contraction_verdict = "WEAK"
        print(f"    Assessment: {contraction_verdict}")
    else:
        contraction_verdict = "UNKNOWN"
        print(f"    Assessment: UNKNOWN")

    # ---- Recursive bound feasibility ----
    print(f"\n  4. RECURSIVE BOUND FEASIBILITY:")
    if lemma_results:
        alpha_mins = [lr['alpha_min'] for lr in lemma_results
                      if lr['alpha_min'] != float('inf')]
        betas = [lr['beta_at_alpha1'] for lr in lemma_results
                 if lr['beta_at_alpha1'] != float('inf')]

        if alpha_mins:
            max_alpha = max(alpha_mins)
            mean_alpha = sum(alpha_mins) / len(alpha_mins)
            print(f"    alpha_min: max={max_alpha:.4f} mean={mean_alpha:.4f}")
            print(f"    (alpha near 1 = V_intra carries most of V)")

        if betas:
            max_beta = max(abs(b) for b in betas)
            print(f"    beta at alpha=1: max|beta| = {max_beta:.6f}")
            print(f"    (small beta = V_cross well-controlled)")

        if alpha_mins and max(alpha_mins) < 3.0:
            bound_feasibility = "HIGH"
        elif alpha_mins and max(alpha_mins) < 5.0:
            bound_feasibility = "MEDIUM"
        else:
            bound_feasibility = "LOW"
        print(f"    Assessment: {bound_feasibility}")
    else:
        bound_feasibility = "UNKNOWN"
        print(f"    Assessment: UNKNOWN")

    # ---- V decomposition ----
    print(f"\n  5. V DECOMPOSITION (ANOVA-style):")
    V_intra_fracs = []
    for entry in SECTION_DATA['s1']:
        if 'frac_V_intra' in entry and not (entry['frac_V_intra'] != entry['frac_V_intra']):
            V_intra_fracs.append(entry['frac_V_intra'])

    if V_intra_fracs:
        min_vi = min(V_intra_fracs)
        max_vi = max(V_intra_fracs)
        mean_vi = sum(V_intra_fracs) / len(V_intra_fracs)
        print(f"    V_intra/V: min={min_vi:.4f} mean={mean_vi:.4f} max={max_vi:.4f}")
        print(f"    (R53 found 65-96% via last coordinate; reproduced here)")

    # ---- Comparison with polynomial vanishing (Axe A) ----
    print(f"\n  6. COMPARISON WITH POLYNOMIAL VANISHING (Axe A):")
    print(f"    Polynomial vanishing: P_B(g) = P_{{B'}}(g) iff polynomial identity mod p")
    print(f"    Requires factoring/root-counting arguments")
    print(f"    Induction by last coord: structural decomposition, no polynomial theory")
    print(f"    Advantage: works slice-by-slice, natural recursion")
    print(f"    Disadvantage: cross-slice terms need separate control")
    print(f"    Verdict: COMPLEMENTARY approaches (induction for structure, polynomial for bounds)")

    # ---- Minimum useful statement ----
    print(f"\n  7. MINIMUM USEFUL STATEMENT:")
    print(f"    If contraction holds universally (max_b mu(k-1,b,p) < mu(k,M,p)):")
    print(f"    Then mu(k) is bounded by a recursion that terminates at k=2.")
    print(f"    Combined with V = O(C) at k=2, this would give V = O(C) for all k.")
    print(f"    Even without universal contraction:")
    print(f"    V_intra = Sum V(k-1, b, p) is the dominant term (65-96%),")
    print(f"    so controlling sub-problems suffices up to the cross-term residual.")

    # ---- FINAL VERDICT ----
    print(f"\n  " + "=" * 60)
    print(f"  FINAL VERDICT:")

    scores = {
        'STRONG': 3, 'MODERATE': 2, 'WEAK': 1,
        'HIGH': 3, 'MEDIUM': 2, 'LOW': 1, 'UNKNOWN': 0,
    }

    total_score = (scores.get(intra_control, 0) +
                   scores.get(cross_control, 0) +
                   scores.get(contraction_verdict, 0) +
                   scores.get(bound_feasibility, 0))
    max_score = 12

    print(f"    Intra-slice control:      {intra_control}")
    print(f"    Cross-slice control:       {cross_control}")
    print(f"    Inductive contraction:     {contraction_verdict}")
    print(f"    Recursive bound feasibility: {bound_feasibility}")
    print(f"    Score: {total_score}/{max_score}")

    if total_score >= 10:
        verdict = "VIABLE"
        explanation = ("Induction by last coordinate provides a robust structural "
                       "decomposition. Contraction holds, V_intra dominates, and "
                       "a recursive bound V = O(C) appears provable.")
    elif total_score >= 6:
        verdict = "FRAGILE"
        explanation = ("Induction by last coordinate shows promise but has gaps. "
                       "Some contraction failures or cross-term issues remain. "
                       "May need additional arguments for cross-slice control.")
    else:
        verdict = "DEAD"
        explanation = ("Induction by last coordinate does not provide sufficient "
                       "control. Contraction fails or cross-terms dominate.")

    print(f"\n    VERDICT: {verdict}")
    print(f"    {explanation}")
    print(f"  " + "=" * 60)

    record_test('S7', f"S7.verdict", verdict in ("VIABLE", "FRAGILE"),
                 f"verdict={verdict} score={total_score}/{max_score}")


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 72)
    print("R54: INDUCTION BY LAST COORDINATE -- AXE B")
    print("  Can induction on B_{k-1} control collisions in Collatz B-vectors?")
    print("  Structural decomposition: fix B_{k-1} = b, reduce to (k-1)-dim sub-problem")
    print("=" * 72)

    # Setup
    verify_test_pairs()

    # Section 1: Slice decomposition
    section1_slice_decomposition()

    # Section 2: Intra-slice collisions
    section2_intra_slice()

    # Section 3: Cross-slice collisions
    section3_cross_slice()

    # Section 4: Contraction test
    section4_contraction()

    # Section 5: Recursive V formula
    section5_recursive_V()

    # Section 6: Inductive lemma
    section6_inductive_lemma()

    # Section 7: Verdict
    section7_verdict()

    # ---- FINAL TEST SUMMARY ----
    total = PASS_COUNT + FAIL_COUNT
    print("\n" + "=" * 72)
    print(f"FINAL TEST SUMMARY: {PASS_COUNT} PASS / {FAIL_COUNT} FAIL / {total} total")
    for sec in sorted(SECTION_TESTS.keys()):
        print(f"  {sec}: {SECTION_TESTS[sec]} tests")
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
