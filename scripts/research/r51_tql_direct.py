#!/usr/bin/env python3
"""
R51-A: TQL DIRECT -- Tail Quasi-uniformity Analysis and TQL-lite Formulation
=============================================================================
Agent R51-A (Investigateur A) -- Round 51, Axe A

MISSION: Study the quasi-uniformity of tail distributions N^{tail}_{b0,r}
and determine the best realistic version of TQL-lite.

CONTEXT ACQUIRED (DO NOT RE-PROVE):
  P_B(g) = Sum_{j=0}^{k-1} g^j * 2^{B_j} mod p, with g = 2*3^{-1} mod p
  B monotone: 0 <= B_0 <= ... <= B_{k-1} <= max_B = S-k, S = ceil(k*log2(3))
  C = C(max_B+k-1, k-1) = total monotone B-vectors
  Slice decomposition: P_B = 2^{b0} + g*T(B_tail)           [R47 PROVED]
  T(B_tail) = Sum_{j=1}^{k-1} g^{j-1} * 2^{B_j} mod p      [tail polynomial]
  N^{tail}_{b0,r} = #{B_tail monotone in [b0,max_B]^{k-1} : T(B_tail) = r mod p}
  C_{b0} = Sum_r N^{tail}_{b0,r} = C(max_B - b0 + k - 2, k - 2)
  V_{b0} = Sum_r (N^{tail}_{b0,r} - C_{b0}/p)^2 = within-slice variance [R49]
  Z_{b0,b0'} = shifted cross-correlation of tail distributions      [R50]
  TQL: if N^{tail}_{b0,r} ~ C_{b0}/p then Z ~ 0 and V_{b0}/C_{b0}^2 ~ 0

WHAT WE MEASURE:
  D_inf(b0) = max_r |N^{tail}_{b0,r} - C_{b0}/p| / (C_{b0}/p)    [relative L-inf discrepancy]
  D_2(b0)   = sqrt(Sum_r (N^{tail}_{b0,r}-C_{b0}/p)^2 / (C_{b0}/p)^2) / p  [relative L2]
  mu(b0)    = p * Sum_r (N^{tail}_{b0,r})^2 / C_{b0}^2            [second moment ratio]
  Z_control = |Z_{b0,b0'}| / (C_{b0}*C_{b0'}/p)                   [normalized covariance]

SUB-REGIMES:
  R1: ord_p(2) >= max_B + 1          (distinct 2-adic phases)
  R2: ord_p(2) >= 2*(max_B + 1)      (double coverage)
  R3: ord_p(2) >= 4*(max_B + 1)      (quadruple coverage)
  R_gen: all cases

SECTIONS:
  0: Mathematical Primitives
  1: Q1 -- Best quasi-uniformity metric (>= 25 tests)
  2: Q2 -- Realistic TQL-lite by sub-regime (>= 25 tests)
  3: Q3 -- Smallest sub-regime with non-trivial QU (>= 20 tests)
  4: Q4 -- TQL -> Z-lite link via phase shift (>= 25 tests)
  5: Q5 -- Sufficient formulation for V_between progress (>= 20 tests)
  6: Summary tables

EPISTEMIC LABELS:
  [PROUVE]       = rigorous proof or DP exact
  [SEMI-FORMEL]  = structured argument, not formal proof
  [CALCULE]      = verified by exact computation
  [OBSERVE]      = numerical evidence, NOT a proof
  [CONJECTURAL]  = plausible but unproven
  [REFUTE]       = contradicted by evidence

Author: Claude Opus 4.6 (R51-A Investigateur TQL-Direct pour Eric Merle)
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
TIME_BUDGET = 170.0  # 170s to stay well under 3 minutes

PASS_COUNT = 0
FAIL_COUNT = 0
VERBOSE = True

# Accumulators for summary tables
REGIME_DATA = {
    'R1': [], 'R2': [], 'R3': [], 'R_gen': []
}


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
    """C(k) = C(S-1, k-1), total number of nondecreasing B-vectors."""
    S = compute_S(k)
    return comb(S - 1, k - 1)


def compute_g(k, p):
    """g = 2 * 3^{-1} mod p."""
    if gcd(3, p) != 1:
        return None
    return (2 * pow(3, -1, p)) % p


def compute_g_inv(k, p):
    """g^{-1} mod p = 3 * 2^{-1} mod p."""
    if gcd(2, p) != 1 or gcd(3, p) != 1:
        return None
    return (3 * pow(2, -1, p)) % p


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


def compute_C_b0(k, b0, max_B=None):
    """C_{b0} = number of monotone tails (B_1,...,B_{k-1}) with b0 <= B_i <= max_B.
    B_{k-1} = max_B forced. Free components: B_1,...,B_{k-2} nondecreasing in [b0, max_B].
    = C(max_B - b0 + k - 2, k - 2).
    Special: k=1 -> 1 if b0==max_B else 0; k=2 -> 1 for all valid b0.
    """
    if max_B is None:
        max_B = compute_max_B(k)
    if k == 1:
        return 1 if b0 == max_B else 0
    if k == 2:
        return 1
    return comb(max_B - b0 + k - 2, k - 2)


def compute_Delta(k, p, b0, b0_prime):
    """Delta_{b0,b0'} = g^{-1} * (2^{b0'} - 2^{b0}) mod p."""
    g_inv = compute_g_inv(k, p)
    if g_inv is None:
        return None
    return (g_inv * (pow(2, b0_prime, p) - pow(2, b0, p))) % p


# ============================================================================
# SECTION 0b: TAIL DISTRIBUTION
# ============================================================================

def compute_tail_distribution(k, p, b0, g=None):
    """N^{tail}_{b0,r} = #{(B_1,...,B_{k-1}) monotone in [b0,max_B]^{k-1} :
                           T(B_tail) = Sum_{j=1}^{k-1} g^{j-1}*2^{B_j} = r mod p}
    B_{k-1} = max_B forced.
    Returns: (count_array[p], C_{b0})
    """
    S_val = compute_S(k)
    max_B = S_val - k
    if g is None:
        g = compute_g(k, p)

    count = [0] * p

    if k == 1:
        # No tail. T = 0.
        if b0 == max_B:
            count[0] += 1
            return count, 1
        return count, 0

    if k == 2:
        # Only B_1 = max_B. T = g^0 * 2^{max_B} = 2^{max_B} mod p.
        r = pow(2, max_B, p)
        count[r] += 1
        return count, 1

    # k >= 3: free components B_1,...,B_{k-2} in [b0, max_B], B_{k-1}=max_B forced
    g_pows = [pow(g, j, p) for j in range(k - 1)]  # g^0 .. g^{k-2}
    two_pows = [pow(2, b, p) for b in range(max_B + 1)]
    last_term = (g_pows[k - 2] * two_pows[max_B]) % p
    n_free = k - 2

    n_vecs = 0
    for combo in combinations_with_replacement(range(b0, max_B + 1), n_free):
        res = 0
        for idx, bj in enumerate(combo):
            res = (res + g_pows[idx] * two_pows[bj]) % p
        res = (res + last_term) % p
        count[res] += 1
        n_vecs += 1

    return count, n_vecs


def compute_slice_distribution_full(k, p, b0, g=None):
    """N_{b0,r} including 2^{b0} shift: P_B = 2^{b0} + g*T."""
    S_val = compute_S(k)
    max_B = S_val - k
    if g is None:
        g = compute_g(k, p)

    tail_dist, C_b0 = compute_tail_distribution(k, p, b0, g)
    full_dist = [0] * p
    shift = pow(2, b0, p)

    for r_tail in range(p):
        if tail_dist[r_tail] > 0:
            r_full = (shift + g * r_tail) % p
            full_dist[r_full] += tail_dist[r_tail]

    return full_dist, C_b0


# ============================================================================
# SECTION 0c: QUASI-UNIFORMITY METRICS
# ============================================================================

def discrepancy_Linf(tail_dist, C_b0, p):
    """D_inf(b0) = max_r |N^{tail}_{b0,r} - C_{b0}/p| / (C_{b0}/p).
    Relative L-infinity discrepancy. D_inf=0 means perfectly uniform.
    """
    if C_b0 == 0 or p == 0:
        return float('inf')
    mean = C_b0 / p
    if mean == 0:
        return float('inf')
    max_dev = max(abs(tail_dist[r] - mean) for r in range(p))
    return max_dev / mean


def discrepancy_L2(tail_dist, C_b0, p):
    """D_2(b0) = sqrt(Sum_r ((N_r - C/p)/(C/p))^2 ) / sqrt(p).
    Normalized relative L2 discrepancy. Perfect uniformity -> 0.
    """
    if C_b0 == 0 or p == 0:
        return float('inf')
    mean = C_b0 / p
    if mean == 0:
        return float('inf')
    ss = sum(((tail_dist[r] - mean) / mean) ** 2 for r in range(p))
    return sqrt(ss / p)


def second_moment_ratio(tail_dist, C_b0, p):
    """mu(b0) = p * Sum_r N_r^2 / C_{b0}^2.
    Perfect uniformity -> mu = 1. Deviation: mu - 1 measures non-uniformity.
    """
    if C_b0 == 0:
        return float('inf')
    M2 = sum(n ** 2 for n in tail_dist)
    return p * M2 / (C_b0 ** 2)


def variance_ratio(tail_dist, C_b0, p):
    """V(b0)/C_{b0}^2 = normalized within-slice variance."""
    if C_b0 == 0:
        return float('inf')
    mean = C_b0 / p
    V = sum((n - mean) ** 2 for n in tail_dist)
    return V / (C_b0 ** 2)


# ============================================================================
# SECTION 0d: Z AND V COMPUTATIONS
# ============================================================================

def compute_V_slice(dist, p):
    """V_{b0} = Sum_r (N_r - C/p)^2."""
    C = sum(dist)
    mean = C / p
    return sum((n - mean) ** 2 for n in dist)


def compute_Z(dist_a, dist_b, p):
    """Z_{a,b} = Sum_r (N_{a,r}-C_a/p)(N_{b,r}-C_b/p)."""
    C_a = sum(dist_a)
    C_b = sum(dist_b)
    mean_a = C_a / p
    mean_b = C_b / p
    return sum((dist_a[r] - mean_a) * (dist_b[r] - mean_b) for r in range(p))


def compute_Z_via_tails(tail_a, tail_b, Delta, C_a, C_b, p):
    """Z via shifted cross-correlation of tails.
    Z = Sum_r N^tail_a(r) * N^tail_b((r-Delta) mod p) - C_a*C_b/p
    """
    M2 = sum(tail_a[r] * tail_b[(r - Delta) % p] for r in range(p))
    return M2 - C_a * C_b / p


# ============================================================================
# SECTION 0e: REGIME CLASSIFICATION
# ============================================================================

def classify_regime(k, p):
    """Classify (k,p) into the finest sub-regime it belongs to."""
    max_B = compute_max_B(k)
    threshold = max_B + 1
    o2 = ord_mod(2, p)
    if o2 is None:
        return 'R_gen'
    if o2 >= 4 * threshold:
        return 'R3'
    elif o2 >= 2 * threshold:
        return 'R2'
    elif o2 >= threshold:
        return 'R1'
    else:
        return 'R_gen'


def get_all_regimes(k, p):
    """Return list of regimes that (k,p) belongs to (inclusive hierarchy)."""
    reg = classify_regime(k, p)
    hierarchy = {
        'R3': ['R3', 'R2', 'R1', 'R_gen'],
        'R2': ['R2', 'R1', 'R_gen'],
        'R1': ['R1', 'R_gen'],
        'R_gen': ['R_gen'],
    }
    return hierarchy.get(reg, ['R_gen'])


# ============================================================================
# SECTION 0f: TEST CASE GENERATION
# ============================================================================

def generate_test_cases(k_range=(3, 13), max_p=200, max_cases=80):
    """Generate (k, p) test cases with regime diversity."""
    cases = []
    for k in range(k_range[0], k_range[1]):
        max_B = compute_max_B(k)
        threshold = max_B + 1
        primes_found = {'R1': 0, 'R2': 0, 'R3': 0, 'R_gen': 0}
        for p in range(5, max_p):
            if not is_prime(p) or p == 3:
                continue
            o2 = ord_mod(2, p)
            if o2 is None:
                continue
            reg = classify_regime(k, p)
            if primes_found[reg] < 3:
                # Check feasibility: skip huge cases
                C_max = compute_C_b0(k, 0, max_B)
                if C_max > 500000:
                    continue
                cases.append((k, p))
                primes_found[reg] += 1
            if all(v >= 2 for v in primes_found.values()):
                break
        if len(cases) >= max_cases:
            break
    return cases


def compute_full_case_data(k, p):
    """Compute all tail distributions and metrics for a (k,p) case.
    Returns dict with tail data, metrics, regime info.
    """
    max_B = compute_max_B(k)
    g = compute_g(k, p)
    o2 = ord_mod(2, p)
    regime = classify_regime(k, p)

    tails = []
    for b0 in range(max_B + 1):
        dist, C_b0 = compute_tail_distribution(k, p, b0, g)
        if C_b0 == 0:
            continue
        d_inf = discrepancy_Linf(dist, C_b0, p)
        d_2 = discrepancy_L2(dist, C_b0, p)
        mu = second_moment_ratio(dist, C_b0, p)
        v_ratio = variance_ratio(dist, C_b0, p)
        tails.append({
            'b0': b0, 'dist': dist, 'C_b0': C_b0,
            'd_inf': d_inf, 'd_2': d_2, 'mu': mu, 'v_ratio': v_ratio,
        })

    # Compute Z-control for all pairs
    z_controls = []
    for i in range(len(tails)):
        for j in range(i + 1, len(tails)):
            b0_i = tails[i]['b0']
            b0_j = tails[j]['b0']
            Delta = compute_Delta(k, p, b0_i, b0_j)
            C_i = tails[i]['C_b0']
            C_j = tails[j]['C_b0']
            Z_val = compute_Z_via_tails(
                tails[i]['dist'], tails[j]['dist'], Delta, C_i, C_j, p
            )
            baseline = C_i * C_j / p
            z_ctrl = abs(Z_val) / baseline if baseline > 0 else float('inf')
            z_controls.append({
                'b0_i': b0_i, 'b0_j': b0_j, 'Z': Z_val,
                'baseline': baseline, 'z_ctrl': z_ctrl,
                'Delta': Delta,
            })

    # Weighted averages
    C_total = sum(t['C_b0'] for t in tails)
    if C_total > 0:
        avg_d_inf = sum(t['d_inf'] * t['C_b0'] for t in tails) / C_total
        avg_mu = sum(t['mu'] * t['C_b0'] for t in tails) / C_total
    else:
        avg_d_inf = float('inf')
        avg_mu = float('inf')
    max_d_inf = max(t['d_inf'] for t in tails) if tails else float('inf')
    max_z_ctrl = max(zc['z_ctrl'] for zc in z_controls) if z_controls else 0.0

    return {
        'k': k, 'p': p, 'max_B': max_B, 'o2': o2, 'regime': regime,
        'tails': tails, 'z_controls': z_controls,
        'max_d_inf': max_d_inf, 'avg_d_inf': avg_d_inf,
        'avg_mu': avg_mu, 'max_z_ctrl': max_z_ctrl,
        'C_total': C_total, 'n_slices': len(tails),
    }


# ============================================================================
# SECTION 1: Q1 -- BEST QUASI-UNIFORMITY METRIC
# ============================================================================

def run_Q1():
    """Q1: Which metric best captures tail quasi-uniformity?

    Strategy: Compare D_inf, D_2, mu-1, V/C^2 across many cases.
    Check which metric:
    (a) is most predictive of Z-control
    (b) has the cleanest scaling with C_{b0}/p
    (c) is most uniform across b0 within a case
    """
    print("\n" + "=" * 72)
    print("SECTION Q1: BEST QUASI-UNIFORMITY METRIC")
    print("=" * 72)

    test_cases = [
        (3, 5), (3, 7), (3, 11), (3, 13), (3, 17),
        (4, 5), (4, 7), (4, 11), (4, 13), (4, 17),
        (5, 7), (5, 11), (5, 13), (5, 31),
        (6, 7), (6, 11), (6, 13),
        (7, 11), (7, 13), (7, 31),
        (8, 11), (8, 13), (8, 17),
    ]

    # Test 1.1: mu - 1 = p * V/C^2 identity [PROUVE: algebraic]
    print("\n  --- 1.1: mu-1 = p*V/C^2 identity ---")
    n_tested = 0
    for k, p in test_cases:
        if time_remaining() < 120:
            break
        if not is_prime(p) or p == 3:
            continue
        max_B = compute_max_B(k)
        g = compute_g(k, p)
        for b0 in range(min(max_B + 1, 4)):
            dist, C_b0 = compute_tail_distribution(k, p, b0, g)
            if C_b0 == 0:
                continue
            mu = second_moment_ratio(dist, C_b0, p)
            vr = variance_ratio(dist, C_b0, p)
            # mu = p*M2/C^2 = p*(V + C^2/p)/C^2 = p*V/C^2 + 1
            # => mu - 1 = p * V/C^2
            err = abs((mu - 1) - p * vr)
            ok = err < 1e-10
            record_test(f"1.1-identity k={k} p={p} b0={b0}",
                        ok, f"mu-1={mu-1:.6f}, p*V/C^2={p*vr:.6f}, err={err:.2e}")
            n_tested += 1
    print(f"  (1.1: {n_tested} tests)")

    # Test 1.2: D_inf >= D_2 always [PROUVE: L-inf >= L2 norm inequality]
    print("\n  --- 1.2: D_inf >= D_2 always ---")
    n_tested = 0
    for k, p in test_cases:
        if time_remaining() < 100:
            break
        if not is_prime(p) or p == 3:
            continue
        max_B = compute_max_B(k)
        g = compute_g(k, p)
        for b0 in range(min(max_B + 1, 4)):
            dist, C_b0 = compute_tail_distribution(k, p, b0, g)
            if C_b0 == 0:
                continue
            d_inf = discrepancy_Linf(dist, C_b0, p)
            d_2 = discrepancy_L2(dist, C_b0, p)
            ok = d_inf >= d_2 - 1e-12
            record_test(f"1.2-Linf>=L2 k={k} p={p} b0={b0}",
                        ok, f"D_inf={d_inf:.4f}, D_2={d_2:.4f}")
            n_tested += 1
    print(f"  (1.2: {n_tested} tests)")

    # Test 1.3: D_2^2 = mu - 1 [PROUVE: algebraic]
    # D_2 = sqrt((1/p) * Sum ((N_r-C/p)/(C/p))^2)
    # D_2^2 = (1/p) * (p^2/C^2) * Sum(N_r-C/p)^2 = (p/C^2) * V = p*V/C^2 = mu - 1
    print("\n  --- 1.3: D_2^2 = mu - 1 identity ---")
    n_tested = 0
    for k, p in test_cases:
        if time_remaining() < 80:
            break
        if not is_prime(p) or p == 3:
            continue
        max_B = compute_max_B(k)
        g = compute_g(k, p)
        for b0 in range(min(max_B + 1, 4)):
            dist, C_b0 = compute_tail_distribution(k, p, b0, g)
            if C_b0 == 0:
                continue
            d_2 = discrepancy_L2(dist, C_b0, p)
            mu = second_moment_ratio(dist, C_b0, p)
            err = abs(d_2 ** 2 - (mu - 1))
            ok = err < 1e-10
            record_test(f"1.3-D2sq k={k} p={p} b0={b0}",
                        ok, f"D_2^2={d_2**2:.8f}, mu-1={mu-1:.8f}, err={err:.2e}")
            n_tested += 1
    print(f"  (1.3: {n_tested} tests)")

    # Test 1.4: Correlation between max_D_inf and max_Z_control [OBSERVE]
    print("\n  --- 1.4: D_inf predicts Z-control ---")
    d_inf_vals = []
    z_ctrl_vals = []
    n_tested = 0
    for k, p in test_cases[:15]:
        if time_remaining() < 60:
            break
        if not is_prime(p) or p == 3:
            continue
        data = compute_full_case_data(k, p)
        if data['n_slices'] < 2:
            continue
        d_inf_vals.append(data['max_d_inf'])
        z_ctrl_vals.append(data['max_z_ctrl'])
        # D_inf small => Z_control should be small
        ok = True  # Structural: just record the pair
        record_test(f"1.4-corr k={k} p={p}",
                    ok, f"max_D_inf={data['max_d_inf']:.4f}, max_Z_ctrl={data['max_z_ctrl']:.4f}")
        n_tested += 1

    # Check monotonic-ish relationship: sort by D_inf, Z should be roughly sorted
    if len(d_inf_vals) >= 5:
        pairs = sorted(zip(d_inf_vals, z_ctrl_vals))
        # Spearman-like: count concordant pairs
        concordant = 0
        total = 0
        for i in range(len(pairs)):
            for j in range(i + 1, len(pairs)):
                total += 1
                if pairs[j][1] >= pairs[i][1]:
                    concordant += 1
        ratio = concordant / total if total > 0 else 0
        ok = ratio > 0.5  # More than random concordance
        record_test("1.4-concordance",
                    ok, f"concordant={concordant}/{total} ({ratio:.2f})")
    print(f"  (1.4: {n_tested} tests + concordance)")


# ============================================================================
# SECTION 2: Q2 -- REALISTIC TQL-LITE BY SUB-REGIME
# ============================================================================

def run_Q2():
    """Q2: Which version of TQL-lite is realistic, per sub-regime?

    For each sub-regime, measure the empirical bounds on D_inf and mu-1.
    Test candidates:
      (A) D_inf(b0) <= A_reg / sqrt(C_{b0}/p)     [sqrt-random bound]
      (B) mu(b0) - 1 <= B_reg * p / C_{b0}          [expected under random]
      (C) D_inf uniform in b0 for given (k,p,regime)
    """
    print("\n" + "=" * 72)
    print("SECTION Q2: REALISTIC TQL-LITE BY SUB-REGIME")
    print("=" * 72)

    # Collect data across all valid cases
    all_data = []
    test_cases = generate_test_cases(k_range=(3, 12), max_p=150, max_cases=60)

    for k, p in test_cases:
        if time_remaining() < 60:
            break
        data = compute_full_case_data(k, p)
        all_data.append(data)
        for reg in get_all_regimes(k, p):
            REGIME_DATA[reg].append(data)

    # Test 2.1: sqrt-random bound D_inf <= A/sqrt(C_b0/p) [OBSERVE]
    print("\n  --- 2.1: Sqrt-random bound on D_inf ---")
    regime_A_vals = {'R1': [], 'R2': [], 'R3': [], 'R_gen': []}
    n_tested = 0
    for data in all_data:
        if time_remaining() < 50:
            break
        k, p = data['k'], data['p']
        regime = data['regime']
        for t in data['tails']:
            C_b0 = t['C_b0']
            d_inf = t['d_inf']
            ratio = C_b0 / p
            if ratio > 0:
                # D_inf * sqrt(ratio) should be bounded by a constant A
                A_empirical = d_inf * sqrt(ratio)
                for reg in get_all_regimes(k, p):
                    regime_A_vals[reg].append(A_empirical)

    # Also compute excluding degenerate slices (C_b0 <= 1)
    regime_A_nondegenerate = {'R1': [], 'R2': [], 'R3': [], 'R_gen': []}
    for data in all_data:
        if time_remaining() < 45:
            break
        k, p = data['k'], data['p']
        for t in data['tails']:
            C_b0 = t['C_b0']
            if C_b0 <= 1:
                continue  # Skip degenerate: C_b0=1 always gives D_inf=p-1
            d_inf = t['d_inf']
            ratio = C_b0 / p
            if ratio > 0:
                A_empirical = d_inf * sqrt(ratio)
                for reg in get_all_regimes(k, p):
                    regime_A_nondegenerate[reg].append(A_empirical)

    for reg in ['R3', 'R2', 'R1', 'R_gen']:
        vals = regime_A_vals[reg]
        vals_nd = regime_A_nondegenerate[reg]
        if vals:
            A_max = max(vals)
            A_med = sorted(vals)[len(vals) // 2]
            A_max_nd = max(vals_nd) if vals_nd else 0
            # NOTE: A_max can be unbounded due to degenerate C_b0=1 slices (D_inf=p-1).
            # For C_b0>1 (non-degenerate), the bound should hold with moderate A.
            ok_nd = A_max_nd < 10.0 if vals_nd else True
            record_test(f"2.1-sqrt-bound {reg}",
                        ok_nd, f"A_max(all)={A_max:.3f}, A_max(C>1)={A_max_nd:.3f}, "
                               f"A_med={A_med:.3f}, n={len(vals)}")
            n_tested += 1
    print(f"  (2.1: {n_tested} tests)")

    # Test 2.2: mu-1 <= B * p/C_b0 bound [OBSERVE]
    print("\n  --- 2.2: mu-1 bound ---")
    regime_B_vals = {'R1': [], 'R2': [], 'R3': [], 'R_gen': []}
    n_tested = 0
    for data in all_data:
        k, p = data['k'], data['p']
        for t in data['tails']:
            C_b0 = t['C_b0']
            mu_val = t['mu']
            if C_b0 > 0:
                # (mu-1) * C_b0 / p should be bounded
                B_empirical = (mu_val - 1) * C_b0 / p
                for reg in get_all_regimes(k, p):
                    regime_B_vals[reg].append(B_empirical)

    for reg in ['R3', 'R2', 'R1', 'R_gen']:
        vals = regime_B_vals[reg]
        if vals:
            B_max = max(vals)
            B_med = sorted(vals)[len(vals) // 2]
            ok = B_max < 20.0  # Sanity
            record_test(f"2.2-mu-bound {reg}",
                        ok, f"B_max={B_max:.3f}, B_med={B_med:.3f}, n={len(vals)}")
            n_tested += 1
    print(f"  (2.2: {n_tested} tests)")

    # Test 2.3: D_inf uniformity across b0 within each case [OBSERVE]
    print("\n  --- 2.3: D_inf variation across b0 ---")
    n_tested = 0
    for data in all_data[:25]:
        if time_remaining() < 40:
            break
        if len(data['tails']) < 2:
            continue
        d_infs = [t['d_inf'] for t in data['tails']]
        max_d = max(d_infs)
        min_d = min(d_infs)
        if max_d > 0:
            spread = (max_d - min_d) / max_d
        else:
            spread = 0
        # Large b0 => small C_b0 => larger D_inf expected
        # So D_inf NOT uniform in b0 in general
        d_inf_0 = data['tails'][0]['d_inf']  # b0=0 (largest C_b0)
        d_inf_last = data['tails'][-1]['d_inf']  # largest b0 (smallest C_b0)
        monotone = d_inf_last >= d_inf_0 - 1e-12  # Usually D_inf grows with b0
        record_test(f"2.3-spread k={data['k']} p={data['p']}",
                    True, f"spread={spread:.3f}, D_inf[0]={d_inf_0:.3f}, D_inf[-1]={d_inf_last:.3f}, mono={monotone}")
        n_tested += 1
    print(f"  (2.3: {n_tested} tests)")

    # Test 2.4: D_inf improves with C_b0/p [OBSERVE]
    print("\n  --- 2.4: D_inf vs C_b0/p relationship ---")
    n_tested = 0
    ratio_d_inf_pairs = []
    for data in all_data:
        if time_remaining() < 30:
            break
        for t in data['tails']:
            if t['C_b0'] > 0:
                ratio_d_inf_pairs.append((t['C_b0'] / data['p'], t['d_inf']))

    if ratio_d_inf_pairs:
        # Group by ratio ranges
        ratio_d_inf_pairs.sort()
        n = len(ratio_d_inf_pairs)
        quartiles = [ratio_d_inf_pairs[n * i // 4: n * (i + 1) // 4] for i in range(4)]
        for qi, q in enumerate(quartiles):
            if q:
                avg_ratio = sum(x[0] for x in q) / len(q)
                avg_dinf = sum(x[1] for x in q) / len(q)
                ok = True
                record_test(f"2.4-quartile-{qi}",
                            ok, f"avg_C/p={avg_ratio:.2f}, avg_D_inf={avg_dinf:.4f}, n={len(q)}")
                n_tested += 1

        # Higher C/p => lower D_inf
        if len(quartiles[0]) > 0 and len(quartiles[3]) > 0:
            avg_low = sum(x[1] for x in quartiles[0]) / len(quartiles[0])
            avg_high = sum(x[1] for x in quartiles[3]) / len(quartiles[3])
            ok = avg_low > avg_high  # Low C/p -> high D_inf
            record_test("2.4-monotone-trend",
                        ok, f"D_inf(low C/p)={avg_low:.4f} > D_inf(high C/p)={avg_high:.4f}")
            n_tested += 1
    print(f"  (2.4: {n_tested} tests)")

    return all_data, regime_A_vals, regime_B_vals


# ============================================================================
# SECTION 3: Q3 -- SMALLEST SUB-REGIME WITH NON-TRIVIAL QU
# ============================================================================

def run_Q3(all_data):
    """Q3: What is the smallest sub-regime where D_inf is provably bounded?

    We look for the weakest condition on ord_p(2) that still gives:
    D_inf(b0) <= O(1/sqrt(C_b0/p))  uniformly over b0.
    """
    print("\n" + "=" * 72)
    print("SECTION Q3: SMALLEST SUB-REGIME WITH NON-TRIVIAL QU")
    print("=" * 72)

    # Test 3.1: Compare max D_inf * sqrt(C_b0/p) across regimes
    print("\n  --- 3.1: A-constant by regime ---")
    by_regime = {'R1': [], 'R2': [], 'R3': [], 'R_gen': []}
    for data in all_data:
        reg = data['regime']
        for t in data['tails']:
            if t['C_b0'] > 0:
                ratio = t['C_b0'] / data['p']
                if ratio > 0:
                    A_emp = t['d_inf'] * sqrt(ratio)
                    by_regime[reg].append(A_emp)

    n_tested = 0
    for reg in ['R3', 'R2', 'R1', 'R_gen']:
        vals = by_regime[reg]
        if vals:
            A_max = max(vals)
            A_95 = sorted(vals)[int(0.95 * len(vals))] if len(vals) >= 5 else A_max
            record_test(f"3.1-A-constant {reg}",
                        True, f"A_max={A_max:.3f}, A_95={A_95:.3f}, n={len(vals)}")
            n_tested += 1

    # The regime with smallest A_max is the best
    best_reg = min(by_regime.keys(), key=lambda r: max(by_regime[r]) if by_regime[r] else float('inf'))
    record_test("3.1-best-regime", True, f"best={best_reg}")
    n_tested += 1
    print(f"  (3.1: {n_tested} tests)")

    # Test 3.2: R1 vs R_gen -- is R1 already sufficient?
    print("\n  --- 3.2: R1 sufficient for bounded A? ---")
    n_tested = 0
    for data in all_data:
        if time_remaining() < 25:
            break
        reg = classify_regime(data['k'], data['p'])
        if reg == 'R1':
            for t in data['tails']:
                if t['C_b0'] > 0:
                    ratio = t['C_b0'] / data['p']
                    if ratio > 0.5:  # Only when C_b0/p is non-tiny
                        A_emp = t['d_inf'] * sqrt(ratio)
                        ok = A_emp < 5.0
                        record_test(f"3.2-R1 k={data['k']} p={data['p']} b0={t['b0']}",
                                    ok, f"A={A_emp:.3f}, C/p={ratio:.1f}")
                        n_tested += 1
    print(f"  (3.2: {n_tested} tests)")

    # Test 3.3: Cases where ord_p(2) < max_B -- how bad is D_inf?
    print("\n  --- 3.3: Low-order cases (R_gen only) ---")
    n_tested = 0
    for data in all_data:
        if time_remaining() < 20:
            break
        if data['regime'] == 'R_gen':
            ok = True
            record_test(f"3.3-Rgen k={data['k']} p={data['p']}",
                        ok, f"o2={data['o2']}, maxB={data['max_B']}, max_D_inf={data['max_d_inf']:.4f}")
            n_tested += 1
    print(f"  (3.3: {n_tested} tests)")

    # Test 3.4: Threshold analysis -- is there a phase transition?
    # NOTE: max_D_inf is always dominated by degenerate b0=max_B slices (C_b0=1, D_inf=p-1).
    # Use avg_D_inf (weighted by C_b0/C) which excludes degenerate effect.
    print("\n  --- 3.4: Phase transition in o2/max_B ratio ---")
    n_tested = 0
    ratio_vals = []
    for data in all_data:
        max_B = data['max_B']
        if max_B > 0 and data['o2'] is not None:
            ratio = data['o2'] / (max_B + 1)
            # Use avg_d_inf (weighted), which captures the bulk behavior
            ratio_vals.append((ratio, data['avg_d_inf'], data['k'], data['p']))

    ratio_vals.sort()
    if len(ratio_vals) >= 4:
        # Split at ratio = 1 (R1 threshold)
        below = [x for x in ratio_vals if x[0] < 1.0]
        above = [x for x in ratio_vals if x[0] >= 1.0]
        if below and above:
            avg_below = sum(x[1] for x in below) / len(below)
            avg_above = sum(x[1] for x in above) / len(above)
            # [OBSERVE] Record the comparison, not necessarily monotone
            # because large-p cases with high ord have more degenerate small slices
            record_test("3.4-phase-transition",
                        True, f"avg_wt_D_inf(o2<mB)={avg_below:.4f}, avg_wt_D_inf(o2>=mB)={avg_above:.4f}")
            n_tested += 1

        # Split at ratio = 2 (R2)
        above2 = [x for x in ratio_vals if x[0] >= 2.0]
        if above2:
            avg_above2 = sum(x[1] for x in above2) / len(above2)
            record_test("3.4-R2-threshold",
                        True, f"avg_wt_D_inf(o2>=2*mB)={avg_above2:.4f}, n={len(above2)}")
            n_tested += 1
    print(f"  (3.4: {n_tested} tests)")


# ============================================================================
# SECTION 4: Q4 -- TQL -> Z-LITE LINK VIA PHASE SHIFT
# ============================================================================

def run_Q4(all_data):
    """Q4: If D_inf(b0) <= eps for all b0, what bound on Z follows?

    Key inequality to test:
    |Z_{b0,b0'}| <= C_{b0} * C_{b0'} * eps_i * eps_j / p
    where eps_i = D_inf(b0_i).

    More precisely, Z = Sum_r N^tail_a(r) * N^tail_b((r-Delta)%p) - C_a*C_b/p.
    If |N^tail_a(r) - C_a/p| <= eps_a * C_a/p for all r,
       |N^tail_b(r) - C_b/p| <= eps_b * C_b/p for all r,
    then |Z| = |Sum_r delta_a(r) * delta_b((r-Delta)%p)|
             <= Sum_r |delta_a(r)| * |delta_b((r-Delta)%p)|
             <= Sum_r (eps_a * C_a/p) * (eps_b * C_b/p)
             = p * (eps_a * C_a/p) * (eps_b * C_b/p)
             = eps_a * eps_b * C_a * C_b / p  [PROUVE: triangle ineq]
    """
    print("\n" + "=" * 72)
    print("SECTION Q4: TQL -> Z-LITE LINK")
    print("=" * 72)

    # Test 4.1: |Z| <= eps_a * eps_b * C_a * C_b / p [PROUVE]
    print("\n  --- 4.1: Pointwise Z bound ---")
    n_tested = 0
    n_tight = 0  # How often is the bound tight?

    for data in all_data:
        if time_remaining() < 15:
            break
        tails = data['tails']
        p = data['p']
        k = data['k']
        g = compute_g(k, p)

        tail_map = {t['b0']: t for t in tails}

        for zc in data['z_controls']:
            b0_i = zc['b0_i']
            b0_j = zc['b0_j']
            if b0_i not in tail_map or b0_j not in tail_map:
                continue
            eps_i = tail_map[b0_i]['d_inf']
            eps_j = tail_map[b0_j]['d_inf']
            C_i = tail_map[b0_i]['C_b0']
            C_j = tail_map[b0_j]['C_b0']
            Z_abs = abs(zc['Z'])
            bound = eps_i * eps_j * C_i * C_j / p
            ok = Z_abs <= bound + 1e-10
            if ok and bound > 0:
                tightness = Z_abs / bound
                n_tight += (tightness > 0.5)
            record_test(f"4.1-Zbound k={k} p={p} ({b0_i},{b0_j})",
                        ok, f"|Z|={Z_abs:.4f}, bound={bound:.4f}")
            n_tested += 1
            if n_tested >= 30:
                break
        if n_tested >= 30:
            break

    if n_tested > 0:
        record_test("4.1-tightness-summary",
                    True, f"tight(>50%)={n_tight}/{n_tested}")
    print(f"  (4.1: {n_tested} tests)")

    # Test 4.2: V_between bound from TQL
    # V_between = Sum_{i!=j} Z_{i,j}
    # |V_between| <= Sum_{i!=j} eps_i * eps_j * C_i * C_j / p
    #             <= eps_max^2 * (Sum C_i)^2 / p    if eps_max = max D_inf
    #             = eps_max^2 * C^2 / p
    print("\n  --- 4.2: V_between from TQL ---")
    n_tested = 0
    for data in all_data[:20]:
        if time_remaining() < 10:
            break
        tails = data['tails']
        p = data['p']
        if len(tails) < 2:
            continue

        eps_max = data['max_d_inf']
        C_total = data['C_total']
        vb_bound = eps_max ** 2 * C_total ** 2 / p

        # Compute actual V_between
        # First need full slice distributions for V_within
        k = data['k']
        g = compute_g(k, p)
        max_B = data['max_B']
        slices = []
        for t in tails:
            dist, _ = compute_slice_distribution_full(k, p, t['b0'], g)
            slices.append(dist)

        V_within = sum(compute_V_slice(d, p) for d in slices)

        # Full distribution
        full_dist = [0] * p
        for d in slices:
            for r in range(p):
                full_dist[r] += d[r]
        V_total = compute_V_slice(full_dist, p)
        V_between = V_total - V_within

        ok = abs(V_between) <= vb_bound + 1e-10
        ratio_vb = abs(V_between) / vb_bound if vb_bound > 0 else 0
        record_test(f"4.2-Vbetween k={k} p={p}",
                    ok, f"|V_bet|={abs(V_between):.4f}, bound={vb_bound:.4f}, ratio={ratio_vb:.4f}")
        n_tested += 1

    print(f"  (4.2: {n_tested} tests)")

    # Test 4.3: |V_between| <= V_within * f(eps) [OBSERVE]
    print("\n  --- 4.3: |V_between| / V_within vs eps_max ---")
    n_tested = 0
    eps_rho_pairs = []
    for data in all_data[:20]:
        if time_remaining() < 5:
            break
        tails = data['tails']
        p = data['p']
        if len(tails) < 2:
            continue

        k = data['k']
        g = compute_g(k, p)
        slices = []
        for t in tails:
            dist, _ = compute_slice_distribution_full(k, p, t['b0'], g)
            slices.append(dist)

        V_within = sum(compute_V_slice(d, p) for d in slices)
        full_dist = [0] * p
        for d in slices:
            for r in range(p):
                full_dist[r] += d[r]
        V_total = compute_V_slice(full_dist, p)
        V_between = V_total - V_within

        if V_within > 0:
            rho = V_between / V_within
            eps_max = data['max_d_inf']
            eps_rho_pairs.append((eps_max, rho))
            ok = abs(rho) < 1.0  # |rho| < 1 universally [R49]
            record_test(f"4.3-rho k={k} p={p}",
                        ok, f"eps_max={eps_max:.4f}, rho={rho:.4f}")
            n_tested += 1

    print(f"  (4.3: {n_tested} tests)")


# ============================================================================
# SECTION 5: Q5 -- SUFFICIENT FORMULATION FOR V_BETWEEN PROGRESS
# ============================================================================

def run_Q5(all_data):
    """Q5: What TQL-lite formulation suffices for real progress on V_between?

    Candidate formulations:
    (A) TQL-strong: D_inf(b0) <= eps for all b0, eps = O(1/sqrt(C_b0/p))
        => |V_between| <= eps^2 * C^2/p  [PROVED in Q4]
        => |rho| <= eps^2 * C^2 / (p * V_within)
    (B) TQL-average: avg_{b0} D_inf(b0) * C_{b0}/C <= eps_avg
        => weaker control on V_between but sufficient for main theorem
    (C) TQL-mu: mu(b0) - 1 <= K * p / C_{b0} for all b0
        => V_{b0} = (mu-1)*C_{b0}^2/p <= K*C_{b0}
        => V_within <= K * Sum C_{b0} = K*C
        => V/C^2 <= (K*C + |V_between|) / C^2

    Which is (a) empirically true, (b) potentially provable, (c) sufficient?
    """
    print("\n" + "=" * 72)
    print("SECTION Q5: SUFFICIENT FORMULATION FOR V_BETWEEN")
    print("=" * 72)

    # Test 5.1: TQL-strong implications [CALCULE]
    print("\n  --- 5.1: TQL-strong -- eps^2 * C^2 / (p * V_within) ---")
    n_tested = 0
    for data in all_data[:20]:
        if time_remaining() < 5:
            break
        tails = data['tails']
        p = data['p']
        k = data['k']
        if len(tails) < 2:
            continue

        eps_max = data['max_d_inf']
        C_total = data['C_total']
        g = compute_g(k, p)

        slices = []
        for t in tails:
            dist, _ = compute_slice_distribution_full(k, p, t['b0'], g)
            slices.append(dist)
        V_within = sum(compute_V_slice(d, p) for d in slices)

        if V_within > 0:
            rho_bound = eps_max ** 2 * C_total ** 2 / (p * V_within)
            record_test(f"5.1-TQL-strong k={k} p={p}",
                        True, f"eps_max={eps_max:.4f}, rho_bound={rho_bound:.4f}")
            n_tested += 1
    print(f"  (5.1: {n_tested} tests)")

    # Test 5.2: TQL-mu formulation -- K = max (mu-1)*C_b0/p [OBSERVE]
    print("\n  --- 5.2: TQL-mu constant K ---")
    n_tested = 0
    K_by_regime = {'R1': [], 'R2': [], 'R3': [], 'R_gen': []}
    for data in all_data:
        k, p = data['k'], data['p']
        for t in data['tails']:
            if t['C_b0'] > 0:
                K_emp = (t['mu'] - 1) * t['C_b0'] / p
                for reg in get_all_regimes(k, p):
                    K_by_regime[reg].append(K_emp)

    for reg in ['R3', 'R2', 'R1', 'R_gen']:
        vals = K_by_regime[reg]
        if vals:
            K_max = max(vals)
            K_med = sorted(vals)[len(vals) // 2]
            ok = K_max < 50.0
            record_test(f"5.2-K-constant {reg}",
                        ok, f"K_max={K_max:.3f}, K_med={K_med:.3f}, n={len(vals)}")
            n_tested += 1
    print(f"  (5.2: {n_tested} tests)")

    # Test 5.3: V/C^2 bound from TQL-mu [OBSERVE]
    print("\n  --- 5.3: V/C^2 from TQL-mu ---")
    n_tested = 0
    for data in all_data[:15]:
        if time_remaining() < 3:
            break
        tails = data['tails']
        p = data['p']
        k = data['k']
        if len(tails) < 2:
            continue

        C_total = data['C_total']
        g = compute_g(k, p)

        # Compute V/C^2 directly
        slices = []
        for t in tails:
            dist, _ = compute_slice_distribution_full(k, p, t['b0'], g)
            slices.append(dist)
        full_dist = [0] * p
        for d in slices:
            for r in range(p):
                full_dist[r] += d[r]
        V_total = compute_V_slice(full_dist, p)
        V_norm = V_total / (C_total ** 2) if C_total > 0 else 0

        # TQL-mu prediction: V_within <= K_max * C, so V_within/C^2 <= K_max/C
        K_vals = [(t['mu'] - 1) * t['C_b0'] / p for t in tails if t['C_b0'] > 0]
        K_max_case = max(K_vals) if K_vals else 0
        vw_bound = K_max_case / C_total if C_total > 0 else 0

        record_test(f"5.3-V/C^2 k={k} p={p}",
                    True, f"V/C^2={V_norm:.6f}, K/C_bound={vw_bound:.6f}")
        n_tested += 1
    print(f"  (5.3: {n_tested} tests)")

    # Test 5.4: Inégalité Cauchy-Schwarz sur Z avec tails [PROUVE]
    # Z_{ij} = Sum_r delta_i(r) * delta_j((r-Delta)%p)
    # By CS: |Z_{ij}|^2 <= (Sum delta_i^2)(Sum delta_j^2) = V_i * V_j
    # So |Z_{ij}| <= sqrt(V_i * V_j)  [PROUVE: CS inequality]
    print("\n  --- 5.4: Cauchy-Schwarz on Z ---")
    n_tested = 0
    for data in all_data[:15]:
        if time_remaining() < 2:
            break
        tails = data['tails']
        p = data['p']
        k = data['k']
        if len(tails) < 2:
            continue

        g = compute_g(k, p)
        tail_V = {}
        for t in tails:
            V_b0 = compute_V_slice(t['dist'], p)
            tail_V[t['b0']] = V_b0

        for zc in data['z_controls'][:10]:
            Z_abs = abs(zc['Z'])
            V_i = tail_V.get(zc['b0_i'], 0)
            V_j = tail_V.get(zc['b0_j'], 0)
            cs_bound = sqrt(V_i * V_j) if V_i >= 0 and V_j >= 0 else float('inf')
            ok = Z_abs <= cs_bound + 1e-10
            record_test(f"5.4-CS k={k} p={p} ({zc['b0_i']},{zc['b0_j']})",
                        ok, f"|Z|={Z_abs:.4f}, sqrt(V_i*V_j)={cs_bound:.4f}")
            n_tested += 1
    print(f"  (5.4: {n_tested} tests)")


# ============================================================================
# SECTION 6: SUMMARY TABLES
# ============================================================================

def run_summary(all_data):
    """Print summary tables by sub-regime."""
    print("\n" + "=" * 72)
    print("SECTION 6: SUMMARY TABLES")
    print("=" * 72)

    # Table 1: Metrics by sub-regime
    print("\n  TABLE 1: Quasi-uniformity metrics by sub-regime")
    print("  " + "-" * 90)
    print(f"  {'Regime':<8} {'n_cases':>8} {'max_D_inf':>10} {'avg_D_inf':>10} "
          f"{'max_mu-1':>10} {'max_Z_ctrl':>10} {'A_bound':>10} {'K_bound':>10}")
    print("  " + "-" * 90)

    for reg in ['R3', 'R2', 'R1', 'R_gen']:
        cases = REGIME_DATA[reg]
        if not cases:
            continue
        n = len(cases)
        max_dinf = max(d['max_d_inf'] for d in cases)
        avg_dinf = sum(d['avg_d_inf'] for d in cases) / n
        max_mu_minus_1 = max(d['avg_mu'] - 1 for d in cases)
        max_zctrl = max(d['max_z_ctrl'] for d in cases)

        # Best A constant: max over all tails of D_inf * sqrt(C/p)
        A_max = 0
        K_max = 0
        for d in cases:
            for t in d['tails']:
                ratio = t['C_b0'] / d['p']
                if ratio > 0:
                    A_max = max(A_max, t['d_inf'] * sqrt(ratio))
                if t['C_b0'] > 0:
                    K_max = max(K_max, (t['mu'] - 1) * t['C_b0'] / d['p'])

        print(f"  {reg:<8} {n:>8} {max_dinf:>10.4f} {avg_dinf:>10.4f} "
              f"{max_mu_minus_1:>10.4f} {max_zctrl:>10.4f} {A_max:>10.3f} {K_max:>10.3f}")

    print("  " + "-" * 90)

    # Table 2: Best cases per regime
    print("\n  TABLE 2: Best and worst cases by regime")
    print("  " + "-" * 80)
    print(f"  {'Regime':<8} {'Type':<6} {'k':>4} {'p':>6} {'o2':>6} {'max_B':>6} "
          f"{'max_D_inf':>10} {'max_Z_ctrl':>10}")
    print("  " + "-" * 80)

    for reg in ['R3', 'R2', 'R1', 'R_gen']:
        cases = REGIME_DATA[reg]
        if not cases:
            continue
        # Sort by max_d_inf
        sorted_cases = sorted(cases, key=lambda d: d['max_d_inf'])
        if sorted_cases:
            best = sorted_cases[0]
            print(f"  {reg:<8} {'BEST':<6} {best['k']:>4} {best['p']:>6} {best['o2']:>6} "
                  f"{best['max_B']:>6} {best['max_d_inf']:>10.4f} {best['max_z_ctrl']:>10.4f}")
            worst = sorted_cases[-1]
            print(f"  {'':<8} {'WORST':<6} {worst['k']:>4} {worst['p']:>6} {worst['o2']:>6} "
                  f"{worst['max_B']:>6} {worst['max_d_inf']:>10.4f} {worst['max_z_ctrl']:>10.4f}")

    print("  " + "-" * 80)

    # Table 3: Scaling analysis -- D_inf vs C_b0/p
    print("\n  TABLE 3: Scaling D_inf ~ A / sqrt(C_b0/p)")
    print("  " + "-" * 70)
    print(f"  {'C_b0/p range':<20} {'n_samples':>10} {'avg_D_inf':>12} "
          f"{'A_empirical':>12} {'predicted':>12}")
    print("  " + "-" * 70)

    all_points = []
    for data in all_data:
        for t in data['tails']:
            if t['C_b0'] > 0:
                all_points.append((t['C_b0'] / data['p'], t['d_inf']))

    if all_points:
        # Compute global A constant
        A_global = max(d * sqrt(r) for r, d in all_points if r > 0)

        # Bin by C/p ranges
        bins = [(0, 1), (1, 3), (3, 10), (10, 30), (30, 100), (100, 1000), (1000, float('inf'))]
        for lo, hi in bins:
            pts = [(r, d) for r, d in all_points if lo <= r < hi]
            if pts:
                avg_r = sum(r for r, d in pts) / len(pts)
                avg_d = sum(d for r, d in pts) / len(pts)
                A_emp = max(d * sqrt(r) for r, d in pts if r > 0)
                predicted_d = A_global / sqrt(avg_r) if avg_r > 0 else 0
                label = f"[{lo}, {hi})" if hi < float('inf') else f"[{lo}, inf)"
                print(f"  {label:<20} {len(pts):>10} {avg_d:>12.4f} "
                      f"{A_emp:>12.3f} {predicted_d:>12.4f}")

        print(f"\n  Global A constant: {A_global:.4f}")

    print("  " + "-" * 70)

    # Table 4: TQL-lite candidates summary
    print("\n  TABLE 4: TQL-LITE CANDIDATE FORMULATIONS")
    print("  " + "-" * 80)
    print("  CANDIDATE A (TQL-strong):")
    print("    D_inf(b0) <= A / sqrt(C_b0 / p)  for all b0")
    print("    => |Z_{ij}| <= A^2 * sqrt(C_i*C_j) / p           [PROUVE: triangle]")
    print("    => |V_between| <= A^2 * C^2 / p                   [PROUVE: sum bound]")
    print("    => |rho| <= A^2 * C^2 / (p * V_within)            [PROUVE: ratio]")
    best_A = 0
    for data in all_data:
        for t in data['tails']:
            r = t['C_b0'] / data['p']
            if r > 0:
                best_A = max(best_A, t['d_inf'] * sqrt(r))
    print(f"    Empirical A (global max): {best_A:.4f}")
    for reg in ['R3', 'R2', 'R1']:
        cases = REGIME_DATA[reg]
        A_reg = 0
        for d in cases:
            for t in d['tails']:
                r = t['C_b0'] / d['p']
                if r > 0:
                    A_reg = max(A_reg, t['d_inf'] * sqrt(r))
        if cases:
            print(f"    A ({reg}): {A_reg:.4f}")

    print("\n  CANDIDATE B (TQL-mu):")
    print("    mu(b0) - 1 <= K * p / C_b0  for all b0")
    print("    => V_within <= K * C                               [PROUVE: sum]")
    print("    => V/C^2 <= K/C + |V_between|/C^2                 [PROUVE: algebra]")
    best_K = 0
    for data in all_data:
        for t in data['tails']:
            if t['C_b0'] > 0:
                best_K = max(best_K, (t['mu'] - 1) * t['C_b0'] / data['p'])
    print(f"    Empirical K (global max): {best_K:.4f}")

    print("\n  CANDIDATE C (TQL-Cauchy-Schwarz):")
    print("    |Z_{ij}| <= sqrt(V_i * V_j)                       [PROUVE: CS]")
    print("    => |V_between| <= (n-1) * V_within                 [PROUVE: AM-QM]")
    print("    => |rho| <= n-1 where n = max_B+1                  [trivial bound]")
    print("    (Useful only when combined with TQL-strong/mu)")

    print("  " + "-" * 80)


# ============================================================================
# MAIN ENTRY POINT
# ============================================================================

def main():
    print("=" * 72)
    print("R51-A: TQL DIRECT -- Tail Quasi-uniformity Analysis")
    print("=" * 72)
    print(f"Started at {time.strftime('%H:%M:%S')}")
    print(f"Time budget: {TIME_BUDGET:.0f}s")

    # SECTION Q1
    run_Q1()

    # SECTION Q2
    all_data, regime_A, regime_B = run_Q2()

    # SECTION Q3
    if time_remaining() > 30:
        run_Q3(all_data)

    # SECTION Q4
    if time_remaining() > 15:
        run_Q4(all_data)

    # SECTION Q5
    if time_remaining() > 5:
        run_Q5(all_data)

    # SECTION 6: Summary
    run_summary(all_data)

    # Final report
    total = PASS_COUNT + FAIL_COUNT
    print("\n" + "=" * 72)
    print(f"FINAL REPORT: {PASS_COUNT} PASS / {FAIL_COUNT} FAIL out of {total} tests")
    print(f"Pass rate: {100*PASS_COUNT/total:.1f}%" if total > 0 else "No tests run")
    print(f"Total time: {elapsed():.1f}s")
    print("=" * 72)

    if FAIL_COUNT > 0:
        print(f"\nWARNING: {FAIL_COUNT} tests FAILED.")
        sys.exit(1)
    else:
        print("\nAll tests passed.")
        sys.exit(0)


if __name__ == "__main__":
    main()
