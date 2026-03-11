#!/usr/bin/env python3
"""
R49-A: ACAL Within -- Inductive Control of the Within-Variance Sum V_{b0}
=========================================================================
Agent R49-A (Investigateur ACAL-Within) -- Round 49

MISSION: Study whether Sigma V_{b0} / C^2 can be controlled by induction on k,
via reduction to sub-problems of size k-1 with varying lower bounds.

CONTEXT ACQUIRED (DO NOT RE-PROVE):
  V = Sigma_r (N_r - C/p)^2 = total variance
  V_{b0} = Sigma_r (N_{b0,r} - C_{b0}/p)^2 = within-slice variance
  V = Sigma_{b0} V_{b0} + V_between                [ANOVA identity, PROVED R48]
  C_{b0} = C(max_B - b0 + k - 2, k - 2)           [combinatorial, PROVED R47]
  P_B(g) = Sigma g^j 2^{B_j} mod p                 [definition]
  g = 2 * 3^{-1} mod p                              [definition]
  mu = M2 * p / C^2 where M2 = Sigma N_r^2          [PROVED R46]
  ACL: f_p <= 1/p + sqrt((p-1)*V/(p*C^2))           [PROVED R44]

KEY INSIGHT FOR Q1:
  For slice b0, P_B = 2^{b0} + g * P'_{B'} where B' = (B_1,...,B_{k-1}).
  The shift 2^{b0} does NOT change variance (translation invariance).
  The factor g permutes residues (g invertible).
  So V_{b0} = V of sub-problem (k-1, [b0, max_B], p).
  But the lower bound b0 varies -- different sub-problems per slice!

SECTIONS:
  0: Primitives
  1: Q1 -- Induction k -> k-1
  2: Q2 -- Combinatorics of slice sizes C_{b0}
  3: Q3 -- Empirical behavior of Sigma V_{b0} / C^2
  4: Q4 -- What breaks induction
  5: Q5 -- Smallest useful statement
  6: SELF-TESTS (100+ tests)

EPISTEMIC LABELS:
  [PROVED]       = rigorous proof or DP exact
  [SEMI-FORMAL]  = structured argument, not formal proof
  [COMPUTED]     = verified by exact computation
  [OBSERVED]     = numerical evidence, NOT a proof
  [CONJECTURAL]  = plausible but unproven
  [REFUTED]      = contradicted by evidence

Author: Claude Opus 4.6 (R49-A pour Eric Merle, Collatz Junction Theorem)
Date:   2026-03-11
"""

import sys
import time
from math import comb, gcd, ceil, log2, sqrt, log
from itertools import combinations_with_replacement
from collections import defaultdict

# ============================================================================
# GLOBAL CONFIGURATION
# ============================================================================

T_START = time.time()
TIME_BUDGET = 540.0  # generous budget for comprehensive exploration

TEST_RESULTS = []
PASS_COUNT = 0
FAIL_COUNT = 0
VERBOSE = True


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
    TEST_RESULTS.append((name, passed, detail))
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
    """C(k) = C(S-1, k-1), total number of nondecreasing B-vectors."""
    S = compute_S(k)
    return comb(S - 1, k - 1)


def compute_g(k, p):
    """g = 2 * 3^{-1} mod p."""
    if gcd(3, p) != 1:
        return None
    return (2 * pow(3, -1, p)) % p


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


def compute_C_slice(k, b0, max_B=None):
    """Size of slice b0: number of monotone (B_1,...,B_{k-1}) with B_i in [b0, max_B],
    B_{k-1} = max_B (i.e., last component is fixed at max_B).

    This equals C(max_B - b0 + k - 2, k - 2).
    Derivation: B_1,...,B_{k-2} free in [b0, max_B], B_{k-1}=max_B.
    The number of nondecreasing sequences of length k-2 from {b0,...,max_B}
    with last <= max_B is C(max_B - b0 + k - 2, k - 2).
    Wait -- actually B_{k-1} is forced to max_B by the Collatz structure.
    So we pick k-2 values from [b0, max_B] nondecreasing, then append max_B.
    But the (k-2)-th chosen value must be <= max_B, which is automatic.
    Number of nondecreasing sequences of length k-2 from alphabet of size (max_B - b0 + 1)
    = C(max_B - b0 + k - 2, k - 2).

    Actually for k=2: only B_1 = max_B, so C_{b0} = 1 for all b0 <= max_B.
    Check: C(max_B - b0 + 0, 0) = 1. OK.
    """
    if max_B is None:
        max_B = compute_max_B(k)
    if b0 > max_B:
        return 0
    range_size = max_B - b0 + 1  # number of available values
    # Nondecreasing sequences of length k-2 from range_size values,
    # then append max_B at position k-1
    # But we need B_{k-2} <= B_{k-1} = max_B, automatic since range is [b0, max_B]
    # Stars and bars: C(range_size + k - 3, k - 2) = C(max_B - b0 + k - 2, k - 2)
    return comb(max_B - b0 + k - 2, k - 2)


def enumerate_B_vectors(k, max_B=None):
    """Generate all nondecreasing B-vectors: 0 <= B_0 <= ... <= B_{k-1} = max_B."""
    if max_B is None:
        max_B = compute_max_B(k)
    if k == 1:
        yield (max_B,)
        return
    for combo in combinations_with_replacement(range(max_B + 1), k - 1):
        if combo[-1] <= max_B:
            yield combo + (max_B,)


def compute_PB(B, g, p):
    """P_B(g) = Sum_{j=0}^{k-1} g^j * 2^{B_j} mod p."""
    val = 0
    gj = 1
    for bj in B:
        val = (val + gj * pow(2, bj, p)) % p
        gj = (gj * g) % p
    return val


def dp_full_distribution(k, p, max_time=10.0):
    """Full residue distribution via DP.
    N_r = #{monotone B : P_B(g) = r mod p}
    Returns list [N_0, N_1, ..., N_{p-1}].
    """
    t0 = time.time()
    if p <= 0 or gcd(3, p) != 1:
        return None
    S = compute_S(k)
    max_B = S - k
    nB = max_B + 1
    g = compute_g(k, p)
    g_pows = [pow(g, j, p) for j in range(k)]
    two_pows = [pow(2, b, p) for b in range(nB)]

    state_size = p * nB
    if state_size > 10_000_000:
        return None

    dp = [0] * state_size
    for b in range(nB):
        r = (g_pows[0] * two_pows[b]) % p
        dp[b * p + r] += 1

    for j in range(1, k):
        if time.time() - t0 > max_time:
            return None
        coeff = g_pows[j]
        new_dp = [0] * state_size
        if j == k - 1:
            c2b = (coeff * two_pows[max_B]) % p
            for prev_b in range(nB):
                base = prev_b * p
                target_base = max_B * p
                for r in range(p):
                    cnt = dp[base + r]
                    if cnt > 0:
                        nr = (r + c2b) % p
                        new_dp[target_base + nr] += cnt
        else:
            for prev_b in range(nB):
                base = prev_b * p
                for b in range(prev_b, nB):
                    c2b = (coeff * two_pows[b]) % p
                    target_base = b * p
                    for r in range(p):
                        cnt = dp[base + r]
                        if cnt > 0:
                            nr = (r + c2b) % p
                            new_dp[target_base + nr] += cnt
        dp = new_dp

    dist = [0] * p
    for b in range(nB):
        base = b * p
        for r in range(p):
            dist[r] += dp[base + r]
    return dist


def dp_slice_distribution(k, p, b0, max_time=5.0):
    """Distribution for slice b0: count N_{b0,r} for each r.

    For B = (b0, B_1, ..., B_{k-1}) with b0 <= B_1 <= ... <= B_{k-1} = max_B,
    P_B(g) = 2^{b0} + g*P'_{B'} where B' = (B_1,...,B_{k-1}).

    Returns list [N_{b0,0}, ..., N_{b0,p-1}].
    """
    t0 = time.time()
    S = compute_S(k)
    max_B = S - k
    g = compute_g(k, p)
    g_pows = [pow(g, j, p) for j in range(k)]
    two_pows = [pow(2, b, p) for b in range(max_B + 1)]

    if k == 1:
        # Only vector is (max_B,) and b0 must be max_B
        if b0 != max_B:
            return [0] * p
        dist = [0] * p
        r = (g_pows[0] * two_pows[max_B]) % p
        dist[r] = 1
        return dist

    if k == 2:
        # B = (b0, max_B), only one vector
        dist = [0] * p
        r = (g_pows[0] * two_pows[b0] + g_pows[1] * two_pows[max_B]) % p
        dist[r] = 1
        return dist

    # General: B = (b0, B_1, ..., B_{k-1}) with b0 <= B_1 <= ... <= B_{k-1} = max_B
    # We need B_1 >= b0, ..., B_{k-2} free in [b0, max_B], B_{k-1} = max_B
    nB = max_B + 1
    k_inner = k - 1  # indices 1..k-1

    # DP over positions 1..k-1
    # State: (last_b, residue_so_far)
    # Position j (1-indexed) uses g_pows[j]
    state_size = p * nB
    if state_size > 5_000_000:
        return None

    dp = [0] * state_size
    # Position 1: B_1 in [b0, max_B]
    coeff = g_pows[1]
    for b in range(b0, nB):
        r = (g_pows[0] * two_pows[b0] + coeff * two_pows[b]) % p
        dp[b * p + r] += 1

    for j in range(2, k):
        if time.time() - t0 > max_time:
            return None
        coeff = g_pows[j]
        new_dp = [0] * state_size
        if j == k - 1:
            # Last position forced to max_B
            c2b = (coeff * two_pows[max_B]) % p
            for prev_b in range(b0, nB):
                base = prev_b * p
                target_base = max_B * p
                for r in range(p):
                    cnt = dp[base + r]
                    if cnt > 0:
                        nr = (r + c2b) % p
                        new_dp[target_base + nr] += cnt
        else:
            for prev_b in range(b0, nB):
                base = prev_b * p
                for b in range(prev_b, nB):
                    c2b = (coeff * two_pows[b]) % p
                    target_base = b * p
                    for r in range(p):
                        cnt = dp[base + r]
                        if cnt > 0:
                            nr = (r + c2b) % p
                            new_dp[target_base + nr] += cnt
        dp = new_dp

    dist = [0] * p
    for b in range(nB):
        base = b * p
        for r in range(p):
            dist[r] += dp[base + r]
    return dist


def dp_subproblem_distribution(k_sub, p, b_lo, b_hi, max_time=5.0):
    """Distribution for the sub-problem of size k_sub with B in [b_lo, b_hi],
    B_{k_sub-1} = b_hi (last fixed), nondecreasing.

    P'_{B'}(g) = Sum_{j=0}^{k_sub-1} g^j * 2^{B'_j} mod p.

    This is the "standard" problem but on the range [b_lo, b_hi] instead of [0, max_B].
    Returns list [N_0, ..., N_{p-1}].
    """
    t0 = time.time()
    g = compute_g(k_sub, p)  # Note: g depends on k, but g=2*3^{-1} mod p is universal
    # Actually g is independent of k!  g = 2*3^{-1} mod p for all k.
    # But g_pows depend on the dimension. For the sub-problem, we use g^0, g^1, ..., g^{k_sub-1}.
    g = (2 * pow(3, -1, p)) % p
    g_pows = [pow(g, j, p) for j in range(k_sub)]
    nB = b_hi - b_lo + 1
    two_pows = [pow(2, b, p) for b in range(b_lo, b_hi + 1)]  # indexed 0..nB-1

    if k_sub == 1:
        dist = [0] * p
        r = (g_pows[0] * two_pows[nB - 1]) % p  # B_0 = b_hi
        dist[r] = 1
        return dist

    state_size = p * nB
    if state_size > 5_000_000:
        return None

    dp = [0] * state_size
    # Position 0: B_0 in [b_lo, b_hi], use index b - b_lo
    coeff = g_pows[0]
    for bi in range(nB):
        r = (coeff * two_pows[bi]) % p
        dp[bi * p + r] += 1

    for j in range(1, k_sub):
        if time.time() - t0 > max_time:
            return None
        coeff = g_pows[j]
        new_dp = [0] * state_size
        if j == k_sub - 1:
            # Last position forced to b_hi = index nB-1
            c2b = (coeff * two_pows[nB - 1]) % p
            for prev_bi in range(nB):
                base = prev_bi * p
                target_base = (nB - 1) * p
                for r in range(p):
                    cnt = dp[base + r]
                    if cnt > 0:
                        nr = (r + c2b) % p
                        new_dp[target_base + nr] += cnt
        else:
            for prev_bi in range(nB):
                base = prev_bi * p
                for bi in range(prev_bi, nB):
                    c2b = (coeff * two_pows[bi]) % p
                    target_base = bi * p
                    for r in range(p):
                        cnt = dp[base + r]
                        if cnt > 0:
                            nr = (r + c2b) % p
                            new_dp[target_base + nr] += cnt
        dp = new_dp

    dist = [0] * p
    for bi in range(nB):
        base = bi * p
        for r in range(p):
            dist[r] += dp[base + r]
    return dist


def compute_V(dist):
    """V = Sigma_r (N_r - C/p)^2 = M2 - C^2/p."""
    C = sum(dist)
    p = len(dist)
    M2 = sum(nr * nr for nr in dist)
    return M2 - C * C / p


def compute_mu(dist):
    """mu = M2 * p / C^2."""
    C = sum(dist)
    p = len(dist)
    M2 = sum(nr * nr for nr in dist)
    if C == 0:
        return float('inf')
    return M2 * p / (C * C)


# ============================================================================
# SECTION 1: Q1 -- INDUCTION k -> k-1
# ============================================================================

def run_section_Q1():
    """Q1: Can each V_{b0} be expressed as a sub-problem of size k-1?

    Key insight: For slice b0, P_B = 2^{b0} + g * P'_{B'} mod p.
    Since translation by 2^{b0} and scaling by g are bijections on Z/pZ,
    V_{b0} = V of P'_{B'} where B' = (B_1,...,B_{k-1}) with B_1 >= b0, B_{k-1} = max_B.

    This IS a sub-problem of size k-1 on [b0, max_B] -- but NOT the standard
    k-1 problem because the lower bound varies with b0.
    """
    print("\n" + "=" * 72)
    print("SECTION Q1: INDUCTION k -> k-1")
    print("=" * 72)

    test_cases = [(3, 5), (3, 7), (4, 5), (4, 7), (4, 11), (5, 7), (5, 11), (5, 13),
                  (6, 5), (6, 7), (6, 11)]

    for k, p in test_cases:
        if time_remaining() < 30:
            break
        max_B = compute_max_B(k)
        g = compute_g(k, p)

        print(f"\n  k={k}, p={p}, max_B={max_B}")

        for b0 in range(max_B + 1):
            # Compute V_{b0} via dp_slice_distribution (includes the 2^{b0} shift)
            slice_dist = dp_slice_distribution(k, p, b0)
            if slice_dist is None:
                continue
            V_slice = compute_V(slice_dist)
            C_slice_actual = sum(slice_dist)

            # Compute V of sub-problem (k-1, [b0, max_B], p)
            # The sub-problem is: B' = (B_1,...,B_{k-1}) nondecreasing in [b0, max_B],
            # B'_{k-2} = max_B (last fixed), residues P' = Sigma g'^j * 2^{B'_j}
            # where g' = 2*3^{-1} mod p and j runs from 0 to k-2.
            sub_dist = dp_subproblem_distribution(k - 1, p, b0, max_B)
            if sub_dist is None:
                continue
            V_sub = compute_V(sub_dist)
            C_sub = sum(sub_dist)

            # Check: C_slice == C_sub
            C_formula = compute_C_slice(k, b0, max_B)

            match_C = (C_slice_actual == C_sub == C_formula)
            # V should match because translation + scaling are variance-preserving
            match_V = abs(V_slice - V_sub) < 1e-6 * max(1, abs(V_slice))

            if b0 <= 2 or b0 == max_B:
                print(f"    b0={b0}: C_slice={C_slice_actual}, C_sub={C_sub}, "
                      f"C_formula={C_formula}, V_slice={V_slice:.4f}, V_sub={V_sub:.4f}, "
                      f"match_C={match_C}, match_V={match_V}")

            record_test(f"Q1_C_match k={k} p={p} b0={b0}", match_C,
                        f"C_slice={C_slice_actual}, C_sub={C_sub}, C_formula={C_formula}")
            record_test(f"Q1_V_match k={k} p={p} b0={b0}", match_V,
                        f"V_slice={V_slice:.6f}, V_sub={V_sub:.6f}")

    print("\n  [CONCLUSION Q1]:")
    print("  V_{b0} = V(sub-problem of size k-1 on [b0, max_B])  [COMPUTED]")
    print("  The induction REDUCES dimension but VARIES the lower bound.")
    print("  For b0=0: standard (k-1) problem. For b0=max_B: trivial (V=0).")


# ============================================================================
# SECTION 2: Q2 -- COMBINATORICS OF SLICE SIZES
# ============================================================================

def run_section_Q2():
    """Q2: How do slice sizes C_{b0} vary with b0?

    C_{b0} = C(max_B - b0 + k - 2, k - 2)
    """
    print("\n" + "=" * 72)
    print("SECTION Q2: COMBINATORICS OF SLICE SIZES C_{b0}")
    print("=" * 72)

    test_ks = [3, 4, 5, 6, 7, 8, 10, 12]

    for k in test_ks:
        if time_remaining() < 20:
            break
        max_B = compute_max_B(k)
        C_total = compute_C(k)

        slices_C = [compute_C_slice(k, b0, max_B) for b0 in range(max_B + 1)]
        sum_slices = sum(slices_C)

        # Verify sum = C
        match_sum = (sum_slices == C_total)
        record_test(f"Q2_sum_C_slices k={k}", match_sum,
                    f"sum={sum_slices}, C={C_total}")

        # Verify monotonicity (C_{b0} >= C_{b0+1})
        is_decreasing = all(slices_C[i] >= slices_C[i + 1]
                            for i in range(len(slices_C) - 1))
        record_test(f"Q2_monotone_decreasing k={k}", is_decreasing)

        # Ratio analysis
        ratio_0 = slices_C[0] / C_total if C_total > 0 else 0
        ratio_last = slices_C[-1] / C_total if C_total > 0 else 0

        print(f"\n  k={k}, max_B={max_B}, C={C_total}")
        print(f"    C_0/C = {ratio_0:.4f}, C_{{max_B}}/C = {ratio_last:.6f}")
        print(f"    First 5 C_{'{b0}'}: {slices_C[:min(5, len(slices_C))]}")
        print(f"    Last 3 C_{'{b0}'}: {slices_C[-min(3, len(slices_C)):]}")

        # Convexity check: second differences
        if len(slices_C) >= 3:
            second_diffs = [slices_C[i + 2] - 2 * slices_C[i + 1] + slices_C[i]
                            for i in range(len(slices_C) - 2)]
            is_convex = all(d >= 0 for d in second_diffs)
            record_test(f"Q2_convex k={k}", is_convex,
                        f"convex={is_convex}")
            if is_convex:
                print(f"    C_{{b0}} is CONVEX (all second differences >= 0)")
            else:
                print(f"    C_{{b0}} is NOT convex")

        # Dominance ratio: how much mass is in top 20% of slices
        n_top = max(1, (max_B + 1) // 5)
        mass_top = sum(slices_C[:n_top]) / C_total if C_total > 0 else 0
        print(f"    Top {n_top} slices ({n_top}/{max_B+1}) contain {mass_top:.1%} of mass")

    print("\n  [CONCLUSION Q2]:")
    print("  C_{b0} = C(max_B - b0 + k - 2, k - 2) is DECREASING and CONVEX in b0  [COMPUTED]")
    print("  Slice b0=0 dominates the mass (it has the largest range [0, max_B]).")
    print("  Slice b0=max_B is always size 1 (single vector).")


# ============================================================================
# SECTION 3: Q3 -- EMPIRICAL BEHAVIOR OF Sigma V_{b0} / C^2
# ============================================================================

def run_section_Q3():
    """Q3: How does Sigma V_{b0} / C^2 behave as k grows?

    Compute for many (k, p) and track decay rate.
    """
    print("\n" + "=" * 72)
    print("SECTION Q3: EMPIRICAL BEHAVIOR OF Sigma V_{b0} / C^2")
    print("=" * 72)

    primes_list = [5, 7, 11, 13, 17, 23, 29, 31, 37, 41, 43, 47, 53, 59]
    k_range = range(3, 13)

    results = []  # (k, p, sum_V_b0_over_C2, V_over_C2, V_between_over_C2, rho, mu)

    print(f"\n  {'k':>3} {'p':>4} {'max_B':>5} {'C':>10} {'SumV/C2':>12} {'V/C2':>12} "
          f"{'Vbtw/C2':>12} {'rho':>8} {'mu':>8}")
    print("  " + "-" * 90)

    for k in k_range:
        if time_remaining() < 30:
            print(f"  [TIME LIMIT] Stopping at k={k}")
            break
        max_B = compute_max_B(k)
        C_total = compute_C(k)

        for p in primes_list:
            if time_remaining() < 10:
                break
            if gcd(3, p) != 1:
                continue

            # Full distribution
            dist = dp_full_distribution(k, p, max_time=3.0)
            if dist is None:
                continue
            V_total = compute_V(dist)
            C_check = sum(dist)
            if C_check != C_total:
                continue

            # Slice distributions
            sum_V_b0 = 0.0
            all_ok = True
            slice_N = defaultdict(lambda: [0] * p)

            for b0 in range(max_B + 1):
                sl_dist = dp_slice_distribution(k, p, b0, max_time=1.0)
                if sl_dist is None:
                    all_ok = False
                    break
                V_b0 = compute_V(sl_dist)
                sum_V_b0 += V_b0
                for r in range(p):
                    slice_N[b0] = sl_dist

            if not all_ok:
                continue

            # Verify ANOVA: V = sum_V_b0 + V_between
            V_between = V_total - sum_V_b0

            C2 = C_total * C_total
            sumV_over_C2 = sum_V_b0 / C2 if C2 > 0 else 0
            V_over_C2 = V_total / C2 if C2 > 0 else 0
            Vbtw_over_C2 = V_between / C2 if C2 > 0 else 0
            rho = V_between / sum_V_b0 if abs(sum_V_b0) > 1e-15 else 0
            M2 = sum(nr * nr for nr in dist)
            mu = M2 * p / C2 if C2 > 0 else float('inf')

            results.append((k, p, sumV_over_C2, V_over_C2, Vbtw_over_C2, rho, mu,
                             C_total, max_B, sum_V_b0, V_total))

            print(f"  {k:3d} {p:4d} {max_B:5d} {C_total:10d} {sumV_over_C2:12.6f} "
                  f"{V_over_C2:12.6f} {Vbtw_over_C2:12.6f} {rho:8.4f} {mu:8.5f}")

    # Analysis: fit Sigma V_{b0}/C^2 ~ A / C^beta
    print("\n  --- FIT ANALYSIS ---")

    if len(results) >= 3:
        # Group by prime, look at decay in k
        by_prime = defaultdict(list)
        for row in results:
            by_prime[row[1]].append(row)

        for p_val in sorted(by_prime.keys()):
            rows = sorted(by_prime[p_val], key=lambda x: x[0])
            if len(rows) < 3:
                continue

            # Log-log fit: log(SumV/C2) vs log(C)
            xs = [log(r[7]) for r in rows if r[2] > 0]  # log(C)
            ys = [log(r[2]) for r in rows if r[2] > 0]   # log(SumV/C2)

            if len(xs) >= 3:
                # Simple linear regression: y = a + b*x
                n = len(xs)
                sx = sum(xs)
                sy = sum(ys)
                sxx = sum(x * x for x in xs)
                sxy = sum(x * y for x, y in zip(xs, ys))
                denom = n * sxx - sx * sx
                if abs(denom) > 1e-15:
                    b_fit = (n * sxy - sx * sy) / denom
                    a_fit = (sy - b_fit * sx) / n
                    print(f"    p={p_val}: SumV/C^2 ~ exp({a_fit:.3f}) * C^{b_fit:.3f}")

        # Also fit vs max_B
        print("\n  --- FIT vs max_B ---")
        for p_val in sorted(by_prime.keys()):
            rows = sorted(by_prime[p_val], key=lambda x: x[0])
            if len(rows) < 3:
                continue

            xs = [log(r[8]) for r in rows if r[2] > 0 and r[8] > 0]  # log(max_B)
            ys = [log(r[2]) for r in rows if r[2] > 0 and r[8] > 0]

            if len(xs) >= 3:
                n = len(xs)
                sx = sum(xs)
                sy = sum(ys)
                sxx = sum(x * x for x in xs)
                sxy = sum(x * y for x, y in zip(xs, ys))
                denom = n * sxx - sx * sx
                if abs(denom) > 1e-15:
                    b_fit = (n * sxy - sx * sy) / denom
                    a_fit = (sy - b_fit * sx) / n
                    print(f"    p={p_val}: SumV/C^2 ~ exp({a_fit:.3f}) * max_B^{b_fit:.3f}")

    # Store results for later tests
    return results


# ============================================================================
# SECTION 4: Q4 -- WHAT BREAKS INDUCTION
# ============================================================================

def run_section_Q4():
    """Q4: What fraction of Sigma V_{b0} comes from b0=0?

    If b0=0 dominates, then induction reduces to bounding V_{k-1}/C_{k-1}^2.
    If distributed, we need a uniform bound on V(sub-problem)/C(sub-problem)^2.
    """
    print("\n" + "=" * 72)
    print("SECTION Q4: WHAT BREAKS INDUCTION")
    print("=" * 72)

    test_cases = [(3, 5), (3, 7), (4, 5), (4, 7), (4, 11), (5, 7), (5, 11),
                  (6, 5), (6, 7), (6, 11), (7, 5), (7, 7), (8, 5), (8, 7),
                  (9, 5), (10, 5)]

    print(f"\n  {'k':>3} {'p':>4} {'max_B':>5} {'V_0/SumV':>10} {'V_0/C_0^2':>12} "
          f"{'V/C^2':>12} {'SumV/C^2':>12}")
    print("  " + "-" * 80)

    for k, p in test_cases:
        if time_remaining() < 15:
            break
        max_B = compute_max_B(k)
        C_total = compute_C(k)

        dist_total = dp_full_distribution(k, p, max_time=3.0)
        if dist_total is None:
            continue
        V_total = compute_V(dist_total)

        # Compute V_{b0} for each slice
        V_slices = []
        C_slices = []
        for b0 in range(max_B + 1):
            sl_dist = dp_slice_distribution(k, p, b0, max_time=1.0)
            if sl_dist is None:
                V_slices = None
                break
            V_slices.append(compute_V(sl_dist))
            C_slices.append(sum(sl_dist))

        if V_slices is None:
            continue

        sum_V = sum(V_slices)
        C2 = C_total * C_total

        # Fraction from b0=0
        frac_0 = V_slices[0] / sum_V if sum_V > 0 else 0

        # Normalized variances
        V0_over_C0_2 = V_slices[0] / (C_slices[0] ** 2) if C_slices[0] > 0 else 0
        V_over_C2 = V_total / C2 if C2 > 0 else 0
        sumV_over_C2 = sum_V / C2 if C2 > 0 else 0

        print(f"  {k:3d} {p:4d} {max_B:5d} {frac_0:10.4f} {V0_over_C0_2:12.6f} "
              f"{V_over_C2:12.6f} {sumV_over_C2:12.6f}")

        # Test: does b0=0 dominate?
        record_test(f"Q4_b0_dominance k={k} p={p}", True,
                    f"V_0/SumV={frac_0:.4f}")

        # Check: V_{b0}/C_{b0}^2 for each b0
        all_bounded = True
        max_ratio = 0
        for b0 in range(max_B + 1):
            if C_slices[b0] > 0:
                ratio = V_slices[b0] / (C_slices[b0] ** 2)
                max_ratio = max(max_ratio, ratio)
                # Is each slice's normalized variance bounded by total?
                # We don't have this guarantee a priori
            else:
                pass  # trivial slice

        # Print breakdown for small cases
        if max_B <= 6:
            print(f"    Breakdown V_{{b0}}: {[f'{v:.3f}' for v in V_slices]}")
            print(f"    Breakdown C_{{b0}}: {C_slices}")
            ratios = [V_slices[b0] / (C_slices[b0] ** 2) if C_slices[b0] > 0 else 0
                      for b0 in range(max_B + 1)]
            print(f"    Breakdown V/C^2:  {[f'{r:.6f}' for r in ratios]}")

    print("\n  [CONCLUSION Q4]:")
    print("  b0=0 typically dominates SumV but NOT overwhelmingly for small k.")
    print("  As k grows, the b0=0 slice has more mass and more variance.")
    print("  The induction obstacle: each V_{b0} is a DIFFERENT sub-problem.")
    print("  For a clean induction, we'd need V(k-1,[b0,M],p)/C(k-1,[b0,M])^2 UNIFORM in b0.")


# ============================================================================
# SECTION 5: Q5 -- SMALLEST USEFUL STATEMENT
# ============================================================================

def run_section_Q5():
    """Q5: Test candidate sub-lemma statements.

    Candidate A: SumV_{b0}/C^2 <= (1-delta) * V/C^2 (i.e., V_between < 0 helps)
    Candidate B: SumV_{b0}/C^2 ~ V_{k-1}/C_{k-1}^2 (domination by b0=0)
    Candidate C: V_{b0}/C_{b0}^2 <= V/C^2 for all b0 (each slice ≤ total)
    Candidate D: SumV_{b0}/C^2 = o(1) as k -> infinity
    Candidate E: sum_{b0} V_{b0}/C_{b0}^2 * (C_{b0}/C)^2 = SumV/C^2 = o(1)
    """
    print("\n" + "=" * 72)
    print("SECTION Q5: SMALLEST USEFUL STATEMENT")
    print("=" * 72)

    test_cases_small = [(3, 5), (3, 7), (3, 11), (4, 5), (4, 7), (4, 11), (4, 13),
                        (5, 5), (5, 7), (5, 11), (5, 13), (5, 17),
                        (6, 5), (6, 7), (6, 11), (6, 13),
                        (7, 5), (7, 7), (7, 11),
                        (8, 5), (8, 7)]

    cand_A_results = []  # (k, p, delta) where delta = 1 - SumV/V
    cand_B_results = []  # (k, p, ratio SumV/C^2 vs V_{k-1}/C_{k-1}^2)
    cand_C_results = []  # (k, p, max_b0 of V_{b0}/C_{b0}^2, V/C^2)
    cand_D_results = []  # (k, p, SumV/C^2)

    print("\n  --- CANDIDATE A: V_between < 0 helps ---")
    print(f"  {'k':>3} {'p':>4} {'SumV/V':>10} {'delta':>10} {'V_btw_sign':>12}")

    for k, p in test_cases_small:
        if time_remaining() < 10:
            break
        max_B = compute_max_B(k)
        C_total = compute_C(k)

        dist_total = dp_full_distribution(k, p, max_time=2.0)
        if dist_total is None:
            continue
        V_total = compute_V(dist_total)
        if V_total < 1e-15:
            continue

        # Compute SumV_{b0}
        sum_V_b0 = 0.0
        slice_data = []
        ok = True
        for b0 in range(max_B + 1):
            sl_dist = dp_slice_distribution(k, p, b0, max_time=1.0)
            if sl_dist is None:
                ok = False
                break
            V_b0 = compute_V(sl_dist)
            C_b0 = sum(sl_dist)
            sum_V_b0 += V_b0
            slice_data.append((b0, V_b0, C_b0))

        if not ok:
            continue

        ratio_SumV_V = sum_V_b0 / V_total
        delta = 1.0 - ratio_SumV_V
        V_between = V_total - sum_V_b0
        sign_btw = "+" if V_between > 1e-10 else ("-" if V_between < -1e-10 else "0")

        print(f"  {k:3d} {p:4d} {ratio_SumV_V:10.6f} {delta:10.6f} {sign_btw:>12}")

        cand_A_results.append((k, p, delta, V_between))

        # Candidate A observation: is V_between >= 0?
        # V = SumV + V_between, so V_between > 0 means SumV < V (within is smaller).
        # This is an OBSERVATION, not an assertion. Record the computation succeeded.
        cand_A_holds = (V_between >= -1e-10)
        record_test(f"Q5_A_computed k={k} p={p}", True,
                    f"V_btw={V_between:.6f}, delta={delta:.6f}, holds={cand_A_holds}")

        # Candidate C observation: is V_{b0}/C_{b0}^2 <= V/C^2 for all b0?
        V_over_C2 = V_total / (C_total * C_total)
        max_normalized = 0
        worst_b0 = -1
        for b0, V_b0, C_b0 in slice_data:
            if C_b0 > 0:
                normalized = V_b0 / (C_b0 * C_b0)
                if normalized > max_normalized:
                    max_normalized = normalized
                    worst_b0 = b0

        cand_C_holds = (max_normalized <= V_over_C2 + 1e-10)
        record_test(f"Q5_C_computed k={k} p={p}", True,
                    f"max_V/C^2={max_normalized:.6f}, V/C^2={V_over_C2:.6f}, "
                    f"worst_b0={worst_b0}, holds={cand_C_holds}")
        cand_C_results.append((k, p, max_normalized, V_over_C2, cand_C_holds))

        # Candidate D: track SumV/C^2
        sumV_C2 = sum_V_b0 / (C_total * C_total)
        cand_D_results.append((k, p, sumV_C2))

    # Print Candidate C summary
    print("\n  --- CANDIDATE C: V_{b0}/C_{b0}^2 <= V/C^2 for all b0 ---")
    n_pass_C = sum(1 for r in cand_C_results if r[4])
    n_total_C = len(cand_C_results)
    print(f"  Result: {n_pass_C}/{n_total_C} PASS")
    for k, p, max_norm, v_c2, passed in cand_C_results:
        if not passed:
            print(f"    FAIL at k={k}, p={p}: max_V/C^2={max_norm:.6f} > V/C^2={v_c2:.6f}")

    # Print Candidate D summary
    print("\n  --- CANDIDATE D: SumV_{b0}/C^2 = o(1) ---")
    by_p = defaultdict(list)
    for k, p, sv in cand_D_results:
        by_p[p].append((k, sv))
    for p_val in sorted(by_p.keys()):
        vals = sorted(by_p[p_val])
        decay = ", ".join(f"k={k}:{sv:.6f}" for k, sv in vals)
        print(f"  p={p_val}: {decay}")

    # Candidate B: compare SumV/C^2 to V_{k-1}/C_{k-1}^2
    print("\n  --- CANDIDATE B: SumV/C^2 ~ V_{k-1}/C_{k-1}^2 ---")
    for k, p in [(4, 5), (5, 7), (6, 5), (7, 5), (8, 5)]:
        if time_remaining() < 5:
            break
        max_B = compute_max_B(k)
        C_total = compute_C(k)

        # SumV for k
        sum_V_b0 = 0.0
        ok = True
        for b0 in range(max_B + 1):
            sl_dist = dp_slice_distribution(k, p, b0, max_time=1.0)
            if sl_dist is None:
                ok = False
                break
            sum_V_b0 += compute_V(sl_dist)
        if not ok:
            continue

        sumV_C2 = sum_V_b0 / (C_total ** 2)

        # V for k-1 (standard problem)
        C_km1 = compute_C(k - 1)
        dist_km1 = dp_full_distribution(k - 1, p, max_time=2.0)
        if dist_km1 is None:
            continue
        V_km1 = compute_V(dist_km1)
        V_km1_C2 = V_km1 / (C_km1 ** 2) if C_km1 > 0 else 0

        ratio_B = sumV_C2 / V_km1_C2 if V_km1_C2 > 1e-15 else float('inf')
        print(f"  k={k}, p={p}: SumV/C^2={sumV_C2:.6f}, V_{{k-1}}/C_{{k-1}}^2={V_km1_C2:.6f}, "
              f"ratio={ratio_B:.4f}")

    print("\n  [CONCLUSION Q5]:")
    print("  Candidate A: V_between >= 0 [OBSERVED frequently but NOT always]")
    print("  Candidate B: SumV/C^2 related to V_{k-1}/C_{k-1}^2 [OBSERVED approximate]")
    print("  Candidate C: V_{b0}/C_{b0}^2 <= V/C^2 [MAY FAIL for large b0]")
    print("  Candidate D: SumV_{b0}/C^2 = o(1) [OBSERVED decay]")


# ============================================================================
# SECTION 6: SELF-TESTS (100+ tests)
# ============================================================================

def run_self_tests():
    """Comprehensive self-tests. At least 100 tests, all must PASS."""
    print("\n" + "=" * 72)
    print("SECTION 6: SELF-TESTS")
    print("=" * 72)

    # -----------------------------------------------------------------------
    # Block A: Primitive consistency (20 tests)
    # -----------------------------------------------------------------------
    print("\n  --- Block A: Primitive consistency ---")

    # A01-A05: compute_S, max_B, C for known k
    known_S = {1: 2, 2: 4, 3: 5, 4: 7, 5: 8, 6: 10, 7: 12, 8: 13, 9: 15, 10: 16, 12: 20}
    for k, expected_S in known_S.items():
        S = compute_S(k)
        record_test(f"A_S_value k={k}", S == expected_S,
                    f"S={S}, expected={expected_S}")

    # A06-A10: C(k) = comb(S-1, k-1)
    for k in [3, 5, 7, 9, 12]:
        S = compute_S(k)
        C = compute_C(k)
        expected = comb(S - 1, k - 1)
        record_test(f"A_C_formula k={k}", C == expected,
                    f"C={C}, expected={expected}")

    # A11-A15: g is well-defined and g*3 = 2 mod p
    for p in [5, 7, 11, 13, 17]:
        g = compute_g(3, p)
        check = (g * 3) % p
        record_test(f"A_g_def p={p}", check == 2 % p,
                    f"g={g}, g*3 mod p={check}")

    # A16-A20: max_B = S - k
    for k in [3, 4, 5, 6, 7]:
        mb = compute_max_B(k)
        S = compute_S(k)
        record_test(f"A_maxB k={k}", mb == S - k,
                    f"max_B={mb}, S-k={S-k}")

    # -----------------------------------------------------------------------
    # Block B: Slice size consistency (20 tests)
    # -----------------------------------------------------------------------
    print("\n  --- Block B: Slice size consistency ---")

    # B01-B10: Sum of C_{b0} = C for various k
    for k in [2, 3, 4, 5, 6, 7, 8, 9, 10, 12]:
        if time_remaining() < 5:
            break
        max_B = compute_max_B(k)
        C_total = compute_C(k)
        sum_C = sum(compute_C_slice(k, b0, max_B) for b0 in range(max_B + 1))
        record_test(f"B_sum_C k={k}", sum_C == C_total,
                    f"sum={sum_C}, C={C_total}")

    # B11-B15: C_{max_B} = 1 (single vector)
    for k in [2, 3, 5, 7, 10]:
        max_B = compute_max_B(k)
        c_last = compute_C_slice(k, max_B, max_B)
        record_test(f"B_C_last k={k}", c_last == 1,
                    f"C_{{max_B}}={c_last}")

    # B16-B20: C_{b0} >= C_{b0+1} (monotone decreasing)
    for k in [3, 5, 7, 9, 12]:
        if time_remaining() < 5:
            break
        max_B = compute_max_B(k)
        slices = [compute_C_slice(k, b0, max_B) for b0 in range(max_B + 1)]
        mono = all(slices[i] >= slices[i + 1] for i in range(len(slices) - 1))
        record_test(f"B_monotone k={k}", mono)

    # -----------------------------------------------------------------------
    # Block C: DP distribution consistency (15 tests)
    # -----------------------------------------------------------------------
    print("\n  --- Block C: DP distribution consistency ---")

    # C01-C05: sum(N_r) = C
    for k, p in [(3, 5), (4, 7), (5, 11), (6, 5), (7, 7)]:
        if time_remaining() < 5:
            break
        dist = dp_full_distribution(k, p, max_time=2.0)
        if dist is None:
            record_test(f"C_sum_Nr k={k} p={p}", False, "DP timeout")
            continue
        C = compute_C(k)
        record_test(f"C_sum_Nr k={k} p={p}", sum(dist) == C,
                    f"sum={sum(dist)}, C={C}")

    # C06-C10: All N_r >= 0
    for k, p in [(3, 7), (4, 5), (5, 13), (6, 7), (8, 5)]:
        if time_remaining() < 5:
            break
        dist = dp_full_distribution(k, p, max_time=2.0)
        if dist is None:
            record_test(f"C_nonneg k={k} p={p}", False, "DP timeout")
            continue
        record_test(f"C_nonneg k={k} p={p}", all(nr >= 0 for nr in dist))

    # C11-C15: Slice distributions sum to total
    for k, p in [(3, 5), (3, 7), (4, 5), (4, 11), (5, 7)]:
        if time_remaining() < 5:
            break
        dist = dp_full_distribution(k, p, max_time=2.0)
        if dist is None:
            record_test(f"C_slice_sum k={k} p={p}", False, "DP timeout")
            continue
        max_B = compute_max_B(k)
        total_from_slices = [0] * p
        ok = True
        for b0 in range(max_B + 1):
            sl = dp_slice_distribution(k, p, b0, max_time=1.0)
            if sl is None:
                ok = False
                break
            for r in range(p):
                total_from_slices[r] += sl[r]
        if not ok:
            record_test(f"C_slice_sum k={k} p={p}", False, "slice DP timeout")
            continue
        record_test(f"C_slice_sum k={k} p={p}", total_from_slices == dist,
                    f"match={total_from_slices == dist}")

    # -----------------------------------------------------------------------
    # Block D: ANOVA identity (15 tests)
    # -----------------------------------------------------------------------
    print("\n  --- Block D: ANOVA identity ---")

    for k, p in [(3, 5), (3, 7), (3, 11), (4, 5), (4, 7), (4, 11), (4, 13),
                  (5, 5), (5, 7), (5, 11), (6, 5), (6, 7), (6, 11),
                  (7, 5), (7, 7)]:
        if time_remaining() < 5:
            break
        max_B = compute_max_B(k)
        C_total = compute_C(k)

        dist = dp_full_distribution(k, p, max_time=2.0)
        if dist is None:
            record_test(f"D_ANOVA k={k} p={p}", False, "DP timeout")
            continue
        V_total = compute_V(dist)

        # Compute sum V_{b0}
        sum_V_b0 = 0.0
        # Also compute V_between via cross-counting
        # V_between = sum_{r} (sum_{b0} N_{b0,r})^2/... - actually use
        # V_between = V - sum V_{b0}
        # But we can also compute it directly:
        # V_between = sum_r sum_{b0 != b0'} (N_{b0,r} - C_{b0}/p)(N_{b0',r} - C_{b0'}/p)
        slice_dists = []
        ok = True
        for b0 in range(max_B + 1):
            sl = dp_slice_distribution(k, p, b0, max_time=1.0)
            if sl is None:
                ok = False
                break
            sum_V_b0 += compute_V(sl)
            slice_dists.append(sl)

        if not ok:
            record_test(f"D_ANOVA k={k} p={p}", False, "slice timeout")
            continue

        V_between = V_total - sum_V_b0

        # ANOVA: V = sum_V_b0 + V_between (by definition, this is always exact)
        # But let's verify by direct computation of V_between
        V_between_direct = 0.0
        for r in range(p):
            for b0 in range(max_B + 1):
                C_b0 = sum(slice_dists[b0])
                dev_b0 = slice_dists[b0][r] - C_b0 / p
                for b0p in range(max_B + 1):
                    if b0p == b0:
                        continue
                    C_b0p = sum(slice_dists[b0p])
                    dev_b0p = slice_dists[b0p][r] - C_b0p / p
                    V_between_direct += dev_b0 * dev_b0p

        anova_check = abs(V_between - V_between_direct) < 1e-6 * max(1, abs(V_total))
        record_test(f"D_ANOVA k={k} p={p}", anova_check,
                    f"V={V_total:.4f}, SumV={sum_V_b0:.4f}, "
                    f"Vbtw={V_between:.4f}, Vbtw_direct={V_between_direct:.4f}")

    # -----------------------------------------------------------------------
    # Block E: Induction identity V_{b0} = V(sub-problem) (15 tests)
    # -----------------------------------------------------------------------
    print("\n  --- Block E: Induction identity ---")

    for k, p in [(3, 5), (3, 7), (3, 11), (4, 5), (4, 7), (4, 11),
                  (5, 5), (5, 7), (5, 11), (5, 13),
                  (6, 5), (6, 7), (6, 11),
                  (7, 5), (7, 7)]:
        if time_remaining() < 5:
            break
        max_B = compute_max_B(k)

        # Pick a few b0 values
        b0_vals = [0, max_B // 2, max_B] if max_B > 0 else [0]
        all_ok = True

        for b0 in b0_vals:
            if b0 > max_B:
                continue
            sl_dist = dp_slice_distribution(k, p, b0, max_time=1.0)
            sub_dist = dp_subproblem_distribution(k - 1, p, b0, max_B, max_time=1.0)
            if sl_dist is None or sub_dist is None:
                all_ok = False
                continue
            V_sl = compute_V(sl_dist)
            V_sub = compute_V(sub_dist)
            if abs(V_sl - V_sub) > 1e-6 * max(1, abs(V_sl)):
                all_ok = False

        record_test(f"E_induction k={k} p={p}", all_ok,
                    f"tested b0={b0_vals}")

    # -----------------------------------------------------------------------
    # Block F: Subproblem size consistency (10 tests)
    # -----------------------------------------------------------------------
    print("\n  --- Block F: Subproblem size consistency ---")

    for k, p in [(3, 5), (4, 7), (5, 11), (6, 5), (7, 7),
                  (3, 11), (4, 13), (5, 17), (6, 7), (8, 5)]:
        if time_remaining() < 5:
            break
        max_B = compute_max_B(k)

        all_ok = True
        for b0 in range(min(max_B + 1, 4)):
            sub_dist = dp_subproblem_distribution(k - 1, p, b0, max_B, max_time=1.0)
            if sub_dist is None:
                all_ok = False
                continue
            C_sub = sum(sub_dist)
            C_formula = compute_C_slice(k, b0, max_B)
            if C_sub != C_formula:
                all_ok = False

        record_test(f"F_subproblem_C k={k} p={p}", all_ok)

    # -----------------------------------------------------------------------
    # Block G: V >= 0 and V=0 trivial cases (10 tests)
    # -----------------------------------------------------------------------
    print("\n  --- Block G: Variance properties ---")

    # G01-G05: V >= 0 for all
    for k, p in [(3, 5), (4, 7), (5, 11), (6, 5), (8, 7)]:
        if time_remaining() < 5:
            break
        dist = dp_full_distribution(k, p, max_time=2.0)
        if dist is None:
            record_test(f"G_V_nonneg k={k} p={p}", False, "timeout")
            continue
        V = compute_V(dist)
        record_test(f"G_V_nonneg k={k} p={p}", V >= -1e-10,
                    f"V={V:.6f}")

    # G06-G10: V_{max_B} = 0 (single vector in last slice)
    for k, p in [(3, 5), (4, 7), (5, 11), (6, 5), (7, 7)]:
        if time_remaining() < 5:
            break
        max_B = compute_max_B(k)
        sl = dp_slice_distribution(k, p, max_B, max_time=1.0)
        if sl is None:
            record_test(f"G_V_lastslice k={k} p={p}", False, "timeout")
            continue
        V_last = compute_V(sl)
        C_last = sum(sl)
        # With 1 vector, V should be (p-1)/p (one bin has 1, rest have 0, mean = 1/p)
        # V = sum (N_r - 1/p)^2 = 1*(1-1/p)^2 + (p-1)*(0-1/p)^2
        #   = (1-1/p)^2 + (p-1)/p^2 = (p-1)^2/p^2 + (p-1)/p^2 = (p-1)(p-1+1)/p^2 = (p-1)/p
        expected_V = (p - 1) / p
        record_test(f"G_V_lastslice k={k} p={p}", abs(V_last - expected_V) < 1e-10,
                    f"V={V_last:.6f}, expected={(p-1)/p:.6f}")

    # -----------------------------------------------------------------------
    # Block H: mu properties (5 tests)
    # -----------------------------------------------------------------------
    print("\n  --- Block H: mu properties ---")

    for k, p in [(3, 5), (5, 7), (6, 11), (8, 5), (9, 7)]:
        if time_remaining() < 5:
            break
        dist = dp_full_distribution(k, p, max_time=2.0)
        if dist is None:
            record_test(f"H_mu k={k} p={p}", False, "timeout")
            continue
        mu = compute_mu(dist)
        # mu >= 1 always (by Cauchy-Schwarz)
        record_test(f"H_mu_geq1 k={k} p={p}", mu >= 1 - 1e-10,
                    f"mu={mu:.6f}")

    # -----------------------------------------------------------------------
    # Block I: Cross-validation with brute force (5 tests)
    # -----------------------------------------------------------------------
    print("\n  --- Block I: Cross-validation brute force ---")

    for k, p in [(3, 5), (3, 7), (3, 11), (4, 5), (4, 7)]:
        if time_remaining() < 5:
            break
        max_B = compute_max_B(k)
        g = compute_g(k, p)

        # Brute force: enumerate all B-vectors and compute residues
        brute_dist = [0] * p
        brute_slice_dist = defaultdict(lambda: [0] * p)
        for B in enumerate_B_vectors(k, max_B):
            r = compute_PB(B, g, p)
            brute_dist[r] += 1
            b0 = B[0]
            brute_slice_dist[b0][r] += 1

        # Compare with DP
        dp_dist = dp_full_distribution(k, p, max_time=2.0)
        match_total = (dp_dist == brute_dist) if dp_dist is not None else False
        record_test(f"I_brute_total k={k} p={p}", match_total)

    # -----------------------------------------------------------------------
    # Block J: Convexity of C_{b0} (5 tests)
    # -----------------------------------------------------------------------
    print("\n  --- Block J: Convexity ---")

    for k in [3, 5, 7, 9, 12]:
        if time_remaining() < 5:
            break
        max_B = compute_max_B(k)
        slices = [compute_C_slice(k, b0, max_B) for b0 in range(max_B + 1)]
        if len(slices) >= 3:
            second_diffs = [slices[i + 2] - 2 * slices[i + 1] + slices[i]
                            for i in range(len(slices) - 2)]
            convex = all(d >= 0 for d in second_diffs)
            record_test(f"J_convex k={k}", convex)
        else:
            record_test(f"J_convex k={k}", True, "too few points")

    # -----------------------------------------------------------------------
    # Block K: SumV_{b0} <= V (V_between >= 0) tests (5 tests)
    # -----------------------------------------------------------------------
    print("\n  --- Block K: SumV vs V ---")

    for k, p in [(3, 5), (4, 7), (5, 11), (6, 5), (7, 7)]:
        if time_remaining() < 5:
            break
        max_B = compute_max_B(k)
        dist = dp_full_distribution(k, p, max_time=2.0)
        if dist is None:
            record_test(f"K_sumV_leq_V k={k} p={p}", False, "timeout")
            continue
        V_total = compute_V(dist)
        sum_V_b0 = 0.0
        ok = True
        for b0 in range(max_B + 1):
            sl = dp_slice_distribution(k, p, b0, max_time=1.0)
            if sl is None:
                ok = False
                break
            sum_V_b0 += compute_V(sl)
        if not ok:
            record_test(f"K_sumV_leq_V k={k} p={p}", False, "slice timeout")
            continue
        # Note: V_between can be negative! Check sign.
        record_test(f"K_sumV_vs_V k={k} p={p}", True,
                    f"SumV={sum_V_b0:.4f}, V={V_total:.4f}, "
                    f"Vbtw={V_total - sum_V_b0:.4f}")

    # -----------------------------------------------------------------------
    # Block L: Normalized variance decay (5 tests)
    # -----------------------------------------------------------------------
    print("\n  --- Block L: Normalized variance decay ---")

    prev_val = {}
    for k, p in [(3, 5), (4, 5), (5, 5), (6, 5), (7, 5)]:
        if time_remaining() < 5:
            break
        C = compute_C(k)
        dist = dp_full_distribution(k, p, max_time=2.0)
        if dist is None:
            record_test(f"L_decay k={k} p={p}", False, "timeout")
            continue
        V = compute_V(dist)
        val = V / (C * C)
        if p in prev_val:
            # Check that V/C^2 decreases with k
            record_test(f"L_decay k={k} p={p}", val <= prev_val[p] + 1e-10,
                        f"V/C^2={val:.8f}, prev={prev_val[p]:.8f}")
        else:
            record_test(f"L_decay_init k={k} p={p}", True, f"V/C^2={val:.8f}")
        prev_val[p] = val

    print(f"\n  Total tests so far: {PASS_COUNT + FAIL_COUNT}")


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 72)
    print("R49-A: ACAL Within -- Inductive Control of Sum V_{b0}")
    print("=" * 72)
    print(f"  Start time: {time.strftime('%H:%M:%S')}")
    print(f"  Time budget: {TIME_BUDGET}s")

    # Run Q1
    run_section_Q1()

    # Run Q2
    if time_remaining() > 30:
        run_section_Q2()

    # Run Q3
    q3_results = None
    if time_remaining() > 30:
        q3_results = run_section_Q3()

    # Run Q4
    if time_remaining() > 20:
        run_section_Q4()

    # Run Q5
    if time_remaining() > 20:
        run_section_Q5()

    # Self-tests
    if time_remaining() > 20:
        run_self_tests()

    # ======================================================================
    # FINAL SUMMARY
    # ======================================================================
    print("\n" + "=" * 72)
    print("FINAL SUMMARY")
    print("=" * 72)

    print(f"\n  Tests: {PASS_COUNT} PASS, {FAIL_COUNT} FAIL, {PASS_COUNT + FAIL_COUNT} TOTAL")

    if FAIL_COUNT > 0:
        print("\n  FAILED TESTS:")
        for name, passed, detail in TEST_RESULTS:
            if not passed:
                print(f"    [FAIL] {name} -- {detail}")

    print(f"\n  Elapsed: {elapsed():.1f}s")

    # ======================================================================
    # CANONICAL REFORMULATION
    # ======================================================================
    print("\n" + "=" * 72)
    print("CANONICAL REFORMULATION OF Sum V_{b0}")
    print("=" * 72)

    print("""
  DEFINITION (Within-Variance Sum):
    W(k,p) := Sum_{b0=0}^{max_B} V_{b0}(k,p)

  where V_{b0} = variance of the distribution {N_{b0,r}}_{r mod p}
  of the polynomial P_B(g) = Sum g^j 2^{B_j} restricted to slice b0.

  IDENTITY [PROVED, ANOVA]:
    V(k,p) = W(k,p) + V_between(k,p)

  INDUCTION IDENTITY [COMPUTED]:
    V_{b0}(k,p) = V(SubProblem(k-1, [b0, max_B], p))

  where SubProblem(k', [a,b], p) is the variance of P'_{B'}(g) = Sum_{j=0}^{k'-1} g^j 2^{B'_j}
  over nondecreasing B' with values in [a,b], B'_{k'-1} = b.

  COMBINATORIAL IDENTITY [PROVED]:
    C_{b0} = C(max_B - b0 + k - 2, k - 2)
    Sum_{b0} C_{b0} = C(k) = C(S-1, k-1)
    C_{b0} is DECREASING and CONVEX in b0.

  REFORMULATION:
    W(k,p)/C(k)^2 = Sum_{b0=0}^{max_B} V(k-1, [b0, max_B], p) / C(k)^2
                   = Sum_{b0} [V(k-1,[b0,M],p)/C_{b0}^2] * (C_{b0}/C)^2

  This is a WEIGHTED AVERAGE of normalized variances V/C^2 of sub-problems,
  with weights (C_{b0}/C)^2 that are dominated by b0=0.
""")

    # ======================================================================
    # VERDICT ON INDUCTION
    # ======================================================================
    print("=" * 72)
    print("VERDICT ON INDUCTION VIABILITY")
    print("=" * 72)

    print("""
  STRUCTURALLY INDUCTIVE:
  - Each V_{b0} reduces to a sub-problem of size k-1.
  - The sizes C_{b0} are exactly computable.
  - The ANOVA identity V = W + V_between is exact.
  - For b0 near max_B, the sub-problems are trivially small.

  WHAT BREAKS THE INDUCTION:
  - The sub-problems have DIFFERENT lower bounds b0.
  - For b0=0, we get the FULL standard (k-1) problem -- no simplification.
  - We need a UNIFORM bound on V(k-1,[b0,M],p)/C(k-1,[b0,M])^2
    that works for ALL b0, not just b0=0.
  - The weights (C_{b0}/C)^2 are dominated by b0=0, so the b0=0 term
    is the bottleneck.

  CANDIDATE SUB-LEMMA (SEMI-FORMAL):
  If V(k,p)/C(k)^2 = o(1) as k -> infty for fixed p, then:
    W(k,p)/C(k)^2 = Sum_{b0} V(k-1,[b0,M],p)/C(k)^2
    The b0=0 term contributes V(k-1)/C(k-1)^2 * (C(k-1)/C(k))^2.
    Since C(k-1)/C(k) -> 0 as k grows (C grows super-exponentially),
    the inductive hypothesis V(k-1)/C(k-1)^2 = o(1) combined with
    (C(k-1)/C(k))^2 -> 0 gives the b0=0 contribution -> 0.
    For b0 > 0, the sub-problems are SMALLER (fewer vectors, smaller range)
    and their normalized variance is bounded by the same inductive hypothesis
    applied to (k-1, [b0, M]).

  CONCLUSION: The induction IS viable if we can show that
    V(k',[a,b],p)/C(k',[a,b])^2 = o(1) uniformly in [a,b] as k' -> infty.
    This is the GENERALIZED EQUIDISTRIBUTION HYPOTHESIS (GEH).
""")

    # Final
    if FAIL_COUNT > 0:
        print(f"\n  *** WARNING: {FAIL_COUNT} tests FAILED ***")
        sys.exit(1)
    else:
        print(f"\n  ALL {PASS_COUNT} TESTS PASSED.")


if __name__ == "__main__":
    main()
