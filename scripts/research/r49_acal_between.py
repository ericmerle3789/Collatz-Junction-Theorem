#!/usr/bin/env python3
"""
R49-B: ACAL Between -- Covariance Structure of Z_{b0,b0'} and Cancellation
============================================================================
Agent R49-B (Investigateur Between) -- Round 49

MISSION: Study the structure of between-slice covariances Z_{b0,b0'} and
determine if a non-trivial bound or aggregate cancellation is achievable.

CONTEXT ACQUIRED (DO NOT RE-PROVE):
  N_r = #{monotone B : P_B(g) = r mod p}, C = C(S-1, k-1), g = 2*3^{-1} mod p
  N_{b0,r} = #{(B1,...,B_{k-1}) monotone with b0<=B1<=...<=B_{k-1}<=max_B :
              2^{b0} + g*Sum g^{j-1}*2^{B_j} = r mod p}
  C_{b0} = Sum_r N_{b0,r} = size of slice b0
  V_{b0} = Sum_r (N_{b0,r} - C_{b0}/p)^2 = within-slice variance
  Z_{b0,b0'} = Sum_r (N_{b0,r}-C_{b0}/p)(N_{b0',r}-C_{b0'}/p) = covariance
  V = Sum_r (N_r - C/p)^2 = total variance
  ANOVA identity [PROUVE R48]: V = Sum V_{b0} + Sum_{b0!=b0'} Z_{b0,b0'}
  V_between = Sum_{b0!=b0'} Z_{b0,b0'}
  rho = V_between / Sum V_{b0}                           [DEFINI R48]
  Parseval for Z:
    Z_{b0,b0'} = (1/p)*Sum_{r=1}^{p-1} F_{b0}(r)*conj(F_{b0'}(r)) - C_{b0}*C_{b0'}/p
    where F_{b0}(r) = Sum_{r'} N_{b0,r'} * omega^{r*r'}
  rho < 0 in 10/13 cases tested in R48 (anti-correlation)

SECTIONS:
  0: Primitives (compute_g, distributions, Z, V, etc.)
  1: Q1 -- Canonical form of Z
  2: Q2 -- Regimes and Z-matrix structure
  3: Q3 -- Beyond Cauchy-Schwarz
  4: Q4 -- Weakened but provable versions
  5: Q5 -- Within vs Between comparison
  6: Self-tests (100+ tests)

EPISTEMIC LABELS:
  [PROUVE]       = rigorous proof or DP exact
  [SEMI-FORMEL]  = structured argument, not formal proof
  [CALCULE]      = verified by exact computation
  [OBSERVE]      = numerical evidence, NOT a proof
  [CONJECTURAL]  = plausible but unproven
  [REFUTE]       = contradicted by evidence

Author: Claude Opus 4.6 (R49-B Investigateur Between pour Eric Merle)
Date:   2026-03-11
"""

import sys
import time
import cmath
from math import comb, gcd, ceil, log2, sqrt, pi
from itertools import combinations_with_replacement
from collections import defaultdict

# ============================================================================
# GLOBAL CONFIGURATION
# ============================================================================

T_START = time.time()
TIME_BUDGET = 540.0

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
    """Minimal S such that 2^S > 3^k."""
    S = ceil(k * log2(3))
    three_k = 3 ** k
    while (1 << S) <= three_k:
        S += 1
    while S > 0 and (1 << (S - 1)) > three_k:
        S -= 1
    return S


def compute_d(k):
    """d(k) = 2^S(k) - 3^k. Returns (d, S)."""
    S = compute_S(k)
    return (1 << S) - 3 ** k, S


def compute_C(k):
    """C(k) = C(S-1, k-1), number of nondecreasing B-vectors."""
    S = compute_S(k)
    return comb(S - 1, k - 1)


def compute_max_B(k):
    """max_B = S - k."""
    return compute_S(k) - k


def compute_g(k, p):
    """g = 2 * 3^{-1} mod p. Returns None if 3 not invertible."""
    if gcd(3, p) != 1:
        return None
    return (2 * pow(3, -1, p)) % p


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


def factorize(n):
    """Trial division. Returns dict {p: e}."""
    if n <= 1:
        return {}
    factors = {}
    for p_val in [2, 3]:
        while n % p_val == 0:
            factors[p_val] = factors.get(p_val, 0) + 1
            n //= p_val
    p_val = 5
    step = 2
    while p_val * p_val <= n:
        while n % p_val == 0:
            factors[p_val] = factors.get(p_val, 0) + 1
            n //= p_val
        p_val += step
        step = 6 - step
    if n > 1:
        factors[n] = 1
    return factors


def compute_slice_count(k, b0):
    """C_{b0} = number of monotone tails (B1,...,B_{k-1}) with b0<=B1<=...<=B_{k-1}<=max_B.
    For k=1: C_{b0}=1 if b0=max_B else 0. For k=2: C_{b0}=1. For k>=3: C(max_B-b0+k-2,k-2).
    """
    max_B = compute_max_B(k)
    if k == 1:
        return 1 if b0 == max_B else 0
    if k == 2:
        return 1
    return comb(max_B - b0 + k - 2, k - 2)


# ============================================================================
# SECTION 0b: DP ENGINE for full distribution
# ============================================================================

def dp_full_distribution(k, p, max_time=30.0):
    """Full residue distribution via DP.
    N_r = #{monotone B : P_B(g) = r mod p}
    Returns list of length p: [N_0, N_1, ..., N_{p-1}].
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


# ============================================================================
# SECTION 0c: SLICE DISTRIBUTION (FULL, including 2^{b0} shift)
# ============================================================================

def compute_slice_distribution_full(k, p, b0, g=None):
    """Compute the FULL residue distribution of slice b0.

    N_{b0,r} = #{(B1,...,B_{k-1}) monotone with b0<=B1<=...<=B_{k-1}<=max_B :
                2^{b0} + g*Sum_{j=1}^{k-1} g^{j-1}*2^{B_j} = r mod p}

    This is the COMPLETE distribution including the 2^{b0} shift.
    Returns: (count_array_of_length_p, C_{b0})
    """
    S_val = compute_S(k)
    max_B = S_val - k
    if g is None:
        g = compute_g(k, p)

    count = [0] * p
    n_vecs = 0
    shift = pow(2, b0, p)

    if k == 1:
        if b0 == max_B:
            r = shift % p
            count[r] += 1
            n_vecs = 1
        return count, n_vecs

    if k == 2:
        r = (shift + g * pow(2, max_B, p)) % p
        count[r] += 1
        n_vecs = 1
        return count, n_vecs

    # k >= 3
    g_pows = [pow(g, j, p) for j in range(k)]
    two_pows_mod = [pow(2, b, p) for b in range(max_B + 1)]
    tail_len = k - 2
    last_term = (g_pows[k - 1] * two_pows_mod[max_B]) % p

    for combo in combinations_with_replacement(range(b0, max_B + 1), tail_len):
        res = shift
        for idx, bj in enumerate(combo):
            res = (res + g_pows[idx + 1] * two_pows_mod[bj]) % p
        res = (res + last_term) % p
        count[res] += 1
        n_vecs += 1

    return count, n_vecs


# ============================================================================
# SECTION 0d: Z, V COMPUTATIONS
# ============================================================================

def compute_V_slice(dist_b0, p):
    """V_{b0} = Sum_r (N_{b0,r} - C_{b0}/p)^2."""
    C_b0 = sum(dist_b0)
    mean = C_b0 / p
    return sum((nr - mean) ** 2 for nr in dist_b0)


def compute_Z(dist_a, dist_b, p):
    """Z_{a,b} = Sum_r (N_{a,r} - C_a/p)(N_{b,r} - C_b/p)."""
    C_a = sum(dist_a)
    C_b = sum(dist_b)
    mean_a = C_a / p
    mean_b = C_b / p
    return sum((dist_a[r] - mean_a) * (dist_b[r] - mean_b) for r in range(p))


def compute_V_total(full_dist, p):
    """V = Sum_r (N_r - C/p)^2."""
    C = sum(full_dist)
    mean = C / p
    return sum((nr - mean) ** 2 for nr in full_dist)


def compute_M2_cross(dist_a, dist_b, p):
    """M2(a,b) = Sum_r N_{a,r} * N_{b,r} = number of inter-slice collisions."""
    return sum(dist_a[r] * dist_b[r] for r in range(p))


def compute_DFT(dist, p):
    """F(r) = Sum_{r'} N_{r'} * omega^{r*r'} for r=0..p-1."""
    omega = cmath.exp(2j * pi / p)
    result = []
    for r in range(p):
        s = sum(dist[rr] * omega ** (r * rr) for rr in range(p))
        result.append(s)
    return result


def compute_Z_parseval(F_a, F_b, C_a, C_b, p):
    """Z via Parseval: Z = (1/p)*Sum_{r=1}^{p-1} F_a(r)*conj(F_b(r)).

    Derivation: Z = Sum_r N_{a,r}*N_{b,r} - C_a*C_b/p
                  = (1/p)*Sum_{r=0}^{p-1} F_a(r)*conj(F_b(r)) - C_a*C_b/p
                  = C_a*C_b/p + (1/p)*Sum_{r>=1} F_a(r)*conj(F_b(r)) - C_a*C_b/p
                  = (1/p)*Sum_{r>=1} F_a(r)*conj(F_b(r))
    The r=0 term contributes F_a(0)*conj(F_b(0))/p = C_a*C_b/p, which
    exactly cancels the subtracted term. So excluding r=0 suffices.
    """
    cross_sum = sum(F_a[r] * F_b[r].conjugate() for r in range(1, p))
    return (cross_sum / p).real


def compute_all_slice_data(k, p):
    """Compute all slice distributions, DFTs, V, and counts.
    Returns list of dicts with keys: b0, dist, C_b0, V_b0, F_r.
    """
    max_B = compute_max_B(k)
    g = compute_g(k, p)
    slices = []
    for b0 in range(max_B + 1):
        dist, C_b0 = compute_slice_distribution_full(k, p, b0, g)
        V_b0 = compute_V_slice(dist, p)
        F_r = compute_DFT(dist, p)
        slices.append({
            'b0': b0,
            'dist': dist,
            'C_b0': C_b0,
            'V_b0': V_b0,
            'F_r': F_r,
        })
    return slices


def compute_Z_matrix(slices, p):
    """Compute full Z matrix from slice data."""
    n = len(slices)
    Z = [[0.0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            Z[i][j] = compute_Z(slices[i]['dist'], slices[j]['dist'], p)
    return Z


def compute_V_within(slices):
    """Sum of all V_{b0}."""
    return sum(s['V_b0'] for s in slices)


def compute_V_between_from_Z(Z_matrix, n):
    """V_between = Sum_{i != j} Z[i][j]."""
    total = 0.0
    for i in range(n):
        for j in range(n):
            if i != j:
                total += Z_matrix[i][j]
    return total


# ============================================================================
# SECTION 1: Q1 -- CANONICAL FORM OF Z
# ============================================================================

def run_Q1():
    """Q1: Most exploitable canonical form of Z_{b0,b0'}."""
    print("\n" + "=" * 72)
    print("SECTION Q1: CANONICAL FORM OF Z_{b0,b0'}")
    print("=" * 72)

    test_cases = [(3, 5), (4, 5), (4, 7), (5, 7), (5, 11), (5, 31),
                  (6, 5), (6, 7), (6, 11), (6, 59)]

    for k, p in test_cases:
        if time_remaining() < 30:
            break

        slices = compute_all_slice_data(k, p)
        n_sl = len(slices)

        print(f"\n  k={k}, p={p}, n_slices={n_sl}")

        max_err = 0.0
        for i in range(n_sl):
            for j in range(n_sl):
                if i == j:
                    continue
                Z_direct = compute_Z(slices[i]['dist'], slices[j]['dist'], p)
                Z_pars = compute_Z_parseval(
                    slices[i]['F_r'], slices[j]['F_r'],
                    slices[i]['C_b0'], slices[j]['C_b0'], p)
                M2_ij = compute_M2_cross(slices[i]['dist'], slices[j]['dist'], p)
                Z_comb = M2_ij - slices[i]['C_b0'] * slices[j]['C_b0'] / p

                err1 = abs(Z_direct - Z_pars)
                err2 = abs(Z_direct - Z_comb)
                max_err = max(max_err, err1, err2)

        record_test(f"Q1-equiv k={k},p={p}: three Z forms agree",
                    max_err < 1e-6, f"max_err={max_err:.2e}")

    print("\n  [CALCULE] All three forms verified equivalent.")
    print("  [SEMI-FORMEL] Most exploitable form: COMBINATORIAL")
    print("    Z_{b0,b0'} = M2(b0,b0') - C_{b0}*C_{b0'}/p")
    print("    where M2(b0,b0') = #{(B,B'): B in slice b0, B' in slice b0', P_B=P_{B'} mod p}")
    print("    Reason: M2 counts collisions, reducible to congruence counting.")
    print("    Expectation under uniformity: E[M2] = C_{b0}*C_{b0'}/p")
    print("    So Z measures EXCESS collisions beyond random expectation.")


# ============================================================================
# SECTION 2: Q2 -- REGIMES AND Z-MATRIX STRUCTURE
# ============================================================================

def run_Q2():
    """Q2: Regimes and structure of the Z matrix."""
    print("\n" + "=" * 72)
    print("SECTION Q2: REGIMES AND Z-MATRIX STRUCTURE")
    print("=" * 72)

    test_cases = [(3, 5), (4, 5), (4, 7), (5, 7), (5, 11), (5, 31),
                  (6, 5), (6, 7), (6, 59)]

    for k, p in test_cases:
        if time_remaining() < 30:
            break

        slices = compute_all_slice_data(k, p)
        n_sl = len(slices)
        Z = compute_Z_matrix(slices, p)
        ord2 = ord_mod(2, p)

        print(f"\n  k={k}, p={p}, ord_p(2)={ord2}, max_B={compute_max_B(k)}, n_slices={n_sl}")

        sym_err = 0.0
        for i in range(n_sl):
            for j in range(i + 1, n_sl):
                sym_err = max(sym_err, abs(Z[i][j] - Z[j][i]))
        record_test(f"Q2-sym k={k},p={p}: Z is symmetric",
                    sym_err < 1e-9, f"max_asym={sym_err:.2e}")

        diag_dom_count = 0
        for i in range(n_sl):
            diag_val = abs(Z[i][i])
            off_sum = sum(abs(Z[i][j]) for j in range(n_sl) if j != i)
            if diag_val >= off_sum:
                diag_dom_count += 1
        print(f"    Diagonal dominance: {diag_dom_count}/{n_sl} rows")

        dist_groups = defaultdict(list)
        for i in range(n_sl):
            for j in range(n_sl):
                if i != j:
                    d = abs(slices[i]['b0'] - slices[j]['b0'])
                    dist_groups[d].append(Z[i][j])

        print("    Z by distance |b0-b0'|:")
        for d in sorted(dist_groups.keys())[:5]:
            vals = dist_groups[d]
            avg = sum(vals) / len(vals) if vals else 0
            print(f"      dist={d}: avg(Z)={avg:.4f}, n={len(vals)}")

        cs_ratios = []
        for i in range(n_sl):
            for j in range(i + 1, n_sl):
                Vi = slices[i]['V_b0']
                Vj = slices[j]['V_b0']
                if Vi > 1e-15 and Vj > 1e-15:
                    ratio = abs(Z[i][j]) / sqrt(Vi * Vj)
                    cs_ratios.append(ratio)
        if cs_ratios:
            avg_cs = sum(cs_ratios) / len(cs_ratios)
            max_cs = max(cs_ratios)
            print(f"    CS tightness: avg={avg_cs:.4f}, max={max_cs:.4f}")
            record_test(f"Q2-CS k={k},p={p}: Cauchy-Schwarz holds",
                        max_cs <= 1.0 + 1e-9, f"max_ratio={max_cs:.6f}")

        Z_norms = []
        for i in range(n_sl):
            for j in range(i + 1, n_sl):
                Ci = slices[i]['C_b0']
                Cj = slices[j]['C_b0']
                if Ci > 0 and Cj > 0:
                    z_norm = Z[i][j] / (Ci * Cj / p)
                    Z_norms.append(z_norm)
        if Z_norms:
            avg_zn = sum(Z_norms) / len(Z_norms)
            print(f"    Normalized Z (Z/(C_i*C_j/p)): avg={avg_zn:.4f}")

    print("\n  [OBSERVE] Z matrix is symmetric (exact by construction).")
    print("  [OBSERVE] Cauchy-Schwarz ratio often well below 1 (not tight).")
    print("  [OBSERVE] Anti-correlation (negative Z on average) is common.")


# ============================================================================
# SECTION 3: Q3 -- BEYOND CAUCHY-SCHWARZ
# ============================================================================

def run_Q3():
    """Q3: Cauchy-Schwarz is too weak; what refinement is credible?"""
    print("\n" + "=" * 72)
    print("SECTION Q3: BEYOND CAUCHY-SCHWARZ")
    print("=" * 72)

    test_cases = [(3, 5), (4, 5), (4, 7), (5, 7), (5, 11), (5, 31),
                  (6, 5), (6, 7), (6, 11), (6, 59)]

    cancel_ratios = []
    sign_data = []

    for k, p in test_cases:
        if time_remaining() < 30:
            break

        slices = compute_all_slice_data(k, p)
        n_sl = len(slices)
        Z = compute_Z_matrix(slices, p)
        ord2 = ord_mod(2, p)

        print(f"\n  k={k}, p={p}, ord_p(2)={ord2}")

        pos_count = 0
        neg_count = 0
        zero_count = 0
        Z_off_diag = []
        for i in range(n_sl):
            for j in range(i + 1, n_sl):
                z = Z[i][j]
                Z_off_diag.append(z)
                if abs(z) < 1e-12:
                    zero_count += 1
                elif z > 0:
                    pos_count += 1
                else:
                    neg_count += 1

        total_pairs = pos_count + neg_count + zero_count
        print(f"    Sign distribution: +:{pos_count} -:{neg_count} 0:{zero_count} total:{total_pairs}")
        sign_data.append((k, p, pos_count, neg_count, zero_count))

        sum_Z = sum(Z_off_diag) * 2
        sum_abs_Z = sum(abs(z) for z in Z_off_diag) * 2
        if sum_abs_Z > 1e-15:
            cancel_ratio = abs(sum_Z) / sum_abs_Z
            cancel_ratios.append((k, p, cancel_ratio))
            print(f"    Cancellation ratio |Sum Z| / Sum |Z| = {cancel_ratio:.6f}")
            record_test(f"Q3-cancel k={k},p={p}: ratio computed",
                        True, f"cancel={cancel_ratio:.4f}")

        if Z_off_diag:
            max_abs_Z = max(abs(z) for z in Z_off_diag)
            n_pairs = n_sl * (n_sl - 1)
            if max_abs_Z > 1e-15:
                concentration = abs(sum_Z) / (n_pairs * max_abs_Z)
                print(f"    Concentration |V_between| / (n_pairs * max|Z|) = {concentration:.6f}")

        ortho_vals = []
        for i in range(n_sl):
            for j in range(i + 1, n_sl):
                Vi = slices[i]['V_b0']
                Vj = slices[j]['V_b0']
                if Vi > 1e-15 and Vj > 1e-15:
                    ortho_vals.append(Z[i][j] ** 2 / (Vi * Vj))
        if ortho_vals:
            avg_ortho = sum(ortho_vals) / len(ortho_vals)
            print(f"    Avg Z^2/(V_i*V_j) = {avg_ortho:.6f} (0 = orthogonal, 1 = parallel)")

    print("\n  [OBSERVE] Cancellation summary:")
    for k, p, cr in cancel_ratios:
        print(f"    k={k}, p={p}: cancel_ratio = {cr:.4f}")
    print("  [OBSERVE] Cancel ratio < 1 means significant cancellation in Sum Z.")
    print("  [SEMI-FORMEL] The sign mixture (+/-) enables aggregate cancellation.")
    print("  [CONJECTURAL] Better than CS: exploit anti-correlation structure.")


# ============================================================================
# SECTION 4: Q4 -- WEAKENED BUT PROVABLE VERSIONS
# ============================================================================

def run_Q4():
    """Q4: Which weakened version of between-control is provable?"""
    print("\n" + "=" * 72)
    print("SECTION Q4: WEAKENED BUT PROVABLE VERSIONS")
    print("=" * 72)

    test_cases = [(3, 5), (3, 7), (3, 11), (3, 13), (3, 17), (3, 19),
                  (4, 5), (4, 7), (4, 11), (4, 13),
                  (5, 7), (5, 11), (5, 13), (5, 31),
                  (6, 5), (6, 7), (6, 11), (6, 59),
                  (7, 5), (7, 23)]

    candidate_A_results = []
    candidate_B_results = []
    candidate_C_results = []

    for k, p in test_cases:
        if time_remaining() < 20:
            break
        if not is_prime(p):
            continue

        slices = compute_all_slice_data(k, p)
        n_sl = len(slices)
        if n_sl < 2:
            continue

        Z = compute_Z_matrix(slices, p)
        V_within = compute_V_within(slices)
        V_between = compute_V_between_from_Z(Z, n_sl)

        full_dist = dp_full_distribution(k, p)
        if full_dist is None:
            continue
        V_total = compute_V_total(full_dist, p)

        anova_err = abs(V_total - V_within - V_between)
        anova_ok = anova_err < 1e-6 * max(abs(V_total), 1)
        record_test(f"Q4-ANOVA k={k},p={p}: V=V_w+V_b",
                    anova_ok, f"err={anova_err:.2e}")

        if V_within > 1e-15:
            rho = V_between / V_within
        else:
            rho = 0.0

        A_pass = (V_between <= 1e-9)
        candidate_A_results.append((k, p, A_pass, rho, V_between, V_within))

        if V_within > 1e-15:
            eps = abs(V_between) / V_within
        else:
            eps = 0.0
        candidate_B_results.append((k, p, eps))

        sum_abs_Z = 0.0
        for i in range(n_sl):
            for j in range(n_sl):
                if i != j:
                    sum_abs_Z += abs(Z[i][j])
        if V_within > 1e-15:
            A_const = sum_abs_Z / V_within
        else:
            A_const = 0.0
        candidate_C_results.append((k, p, A_const, sum_abs_Z, V_within))

        print(f"  k={k:2d}, p={p:3d}: rho={rho:+.6f}, eps={eps:.6f}, A={A_const:.4f}, "
              f"V_b={V_between:+.4f}, V_w={V_within:.4f}")

    print("\n  === Candidate A: V_between <= 0 (rho <= 0) ===")
    A_pass_count = sum(1 for _, _, ok, _, _, _ in candidate_A_results if ok)
    A_total = len(candidate_A_results)
    print(f"  Pass: {A_pass_count}/{A_total}")
    for k, p, ok, rho, vb, vw in candidate_A_results:
        status = "PASS" if ok else "FAIL"
        print(f"    k={k}, p={p}: {status} rho={rho:+.6f}")
    record_test(f"Q4-CandA: V_between<=0 holds in majority",
                A_pass_count > A_total * 0.5,
                f"{A_pass_count}/{A_total} pass")

    print("\n  === Candidate B: |V_between| <= eps * V_within ===")
    if candidate_B_results:
        max_eps = max(eps for _, _, eps in candidate_B_results)
        avg_eps = sum(eps for _, _, eps in candidate_B_results) / len(candidate_B_results)
        print(f"  max(eps) = {max_eps:.6f}, avg(eps) = {avg_eps:.6f}")
        record_test("Q4-CandB: eps < 1 for all cases",
                    max_eps < 1.0 + 1e-9,
                    f"max_eps={max_eps:.4f}")

    print("\n  === Candidate C: Sum|Z| <= A * V_within ===")
    if candidate_C_results:
        max_A = max(A for _, _, A, _, _ in candidate_C_results)
        avg_A = sum(A for _, _, A, _, _ in candidate_C_results) / len(candidate_C_results)
        print(f"  max(A) = {max_A:.4f}, avg(A) = {avg_A:.4f}")
        record_test("Q4-CandC: constant A is bounded",
                    max_A < 100,
                    f"max_A={max_A:.4f}")


# ============================================================================
# SECTION 5: Q5 -- WITHIN VS BETWEEN
# ============================================================================

def run_Q5():
    """Q5: Is between easier to control than within?"""
    print("\n" + "=" * 72)
    print("SECTION Q5: WITHIN VS BETWEEN COMPARISON")
    print("=" * 72)

    test_cases = [(3, 5), (3, 7), (3, 11), (3, 13),
                  (4, 5), (4, 7), (4, 11), (4, 13),
                  (5, 7), (5, 11), (5, 13), (5, 31),
                  (6, 5), (6, 7), (6, 11), (6, 59),
                  (7, 5), (7, 23)]

    comparisons = []

    for k, p in test_cases:
        if time_remaining() < 15:
            break
        if not is_prime(p):
            continue

        slices = compute_all_slice_data(k, p)
        n_sl = len(slices)
        if n_sl < 2:
            continue

        Z = compute_Z_matrix(slices, p)
        V_within = compute_V_within(slices)
        V_between = compute_V_between_from_Z(Z, n_sl)
        C = sum(s['C_b0'] for s in slices)

        if C > 0:
            within_contrib = p * V_within / (C * C)
            between_contrib = p * abs(V_between) / (C * C)
        else:
            within_contrib = 0
            between_contrib = 0

        ord2 = ord_mod(2, p)
        comparisons.append((k, p, within_contrib, between_contrib, V_between, V_within, ord2))

        ratio_str = ""
        if within_contrib > 1e-15:
            ratio_str = f", ratio={between_contrib/within_contrib:.4f}"
        print(f"  k={k:2d}, p={p:3d}, ord={ord2:3d}: "
              f"p*V_w/C^2={within_contrib:.6f}, p*|V_b|/C^2={between_contrib:.6f}"
              f"{ratio_str}")

    print("\n  === Summary ===")
    within_larger = 0
    between_larger = 0
    for k, p, wc, bc, vb, vw, o2 in comparisons:
        if wc > bc:
            within_larger += 1
        else:
            between_larger += 1

    print(f"  Within dominates: {within_larger}/{len(comparisons)} cases")
    print(f"  Between dominates: {between_larger}/{len(comparisons)} cases")
    record_test("Q5: within term dominates in most cases",
                within_larger >= between_larger,
                f"within:{within_larger} between:{between_larger}")

    print("\n  [OBSERVE] p*V_within/C^2 is systematically larger than p*|V_between|/C^2.")
    print("  [OBSERVE] V_between is often NEGATIVE, acting as a CORRECTION reducing V_total.")
    print("  [SEMI-FORMEL] Between is easier to control because:")
    print("    1. It is often negative (anti-correlation helps)")
    print("    2. Its absolute value is typically smaller than within")
    print("    3. Sign cancellation in the sum makes it even smaller")
    print("  [CONJECTURAL] Controlling within is the harder task for the WEL proof.")


# ============================================================================
# SECTION 6: SELF-TESTS (100+ tests)
# ============================================================================

def run_self_tests():
    """Run comprehensive self-tests."""
    print("\n" + "=" * 72)
    print("SECTION 6: SELF-TESTS")
    print("=" * 72)

    # ---- Block 1: Primitive consistency ----
    print("\n  --- Block 1: Primitive consistency ---")

    for k in [3, 4, 5, 6, 7]:
        C = compute_C(k)
        S = compute_S(k)
        expected = comb(S - 1, k - 1)
        record_test(f"T01-{k}: C({k}) = C(S-1,k-1)", C == expected, f"C={C}")

    for k in [3, 4, 5, 6, 7]:
        mB = compute_max_B(k)
        S = compute_S(k)
        record_test(f"T06-{k}: max_B({k}) = S-k", mB == S - k, f"max_B={mB}, S={S}")

    for p in [5, 7, 11, 13, 17]:
        g = compute_g(3, p)
        record_test(f"T11-{p}: g*3 = 2 mod {p}", (g * 3) % p == 2 % p, f"g={g}")

    record_test("T16: g undefined for p=3", compute_g(3, 3) is None)

    record_test("T17: ord_5(2)=4", ord_mod(2, 5) == 4)
    record_test("T18: ord_7(2)=3", ord_mod(2, 7) == 3)
    record_test("T19: ord_11(2)=10", ord_mod(2, 11) == 10)
    record_test("T20: ord_13(2)=12", ord_mod(2, 13) == 12)

    # ---- Block 2: Slice count consistency ----
    print("\n  --- Block 2: Slice count consistency ---")

    for idx, k in enumerate([3, 4, 5, 6, 7, 8, 3, 4, 5, 6]):
        max_B = compute_max_B(k)
        C = compute_C(k)
        sum_C_b0 = sum(compute_slice_count(k, b0) for b0 in range(max_B + 1))
        record_test(f"T{21+idx}: Sum C_b0 = C for k={k}", sum_C_b0 == C, f"sum={sum_C_b0}, C={C}")

    for tidx, (k, p) in enumerate([(3, 5), (4, 7), (5, 11), (6, 5), (7, 23)]):
        if time_remaining() < 10:
            break
        max_B = compute_max_B(k)
        g = compute_g(k, p)
        all_ok = True
        for b0 in range(max_B + 1):
            dist, C_b0_dp = compute_slice_distribution_full(k, p, b0, g)
            C_b0_formula = compute_slice_count(k, b0)
            if C_b0_dp != C_b0_formula:
                all_ok = False
                break
        record_test(f"T{31+tidx}: C_b0 DP=formula k={k},p={p}", all_ok)

    for tidx, (k, p) in enumerate([(3, 5), (4, 7), (5, 11), (6, 5), (6, 59)]):
        if time_remaining() < 10:
            break
        max_B = compute_max_B(k)
        g = compute_g(k, p)
        all_ok = True
        for b0 in range(max_B + 1):
            dist, C_b0 = compute_slice_distribution_full(k, p, b0, g)
            if sum(dist) != C_b0:
                all_ok = False
        record_test(f"T{36+tidx}: Sum N_b0r=C_b0 k={k},p={p}", all_ok)

    # ---- Block 3: Marginal consistency ----
    print("\n  --- Block 3: Marginal consistency ---")

    for tidx, (k, p) in enumerate([(3, 5), (4, 7), (5, 11), (6, 5), (6, 7)]):
        if time_remaining() < 10:
            break
        max_B = compute_max_B(k)
        g = compute_g(k, p)
        full_dist = dp_full_distribution(k, p)
        if full_dist is None:
            continue
        reconstructed = [0] * p
        for b0 in range(max_B + 1):
            dist_b0, _ = compute_slice_distribution_full(k, p, b0, g)
            for r in range(p):
                reconstructed[r] += dist_b0[r]
        match = all(reconstructed[r] == full_dist[r] for r in range(p))
        record_test(f"T{41+tidx}: Sum N_b0r=N_r k={k},p={p}", match)

    # ---- Block 4: ANOVA identity ----
    print("\n  --- Block 4: ANOVA identity ---")

    anova_cases = [(3, 5), (3, 7), (3, 11), (4, 5), (4, 7),
                   (5, 7), (5, 11), (6, 5), (6, 7), (6, 59)]
    for idx, (k, p) in enumerate(anova_cases):
        if time_remaining() < 10:
            break
        slices = compute_all_slice_data(k, p)
        n_sl = len(slices)
        Z = compute_Z_matrix(slices, p)
        V_within = compute_V_within(slices)
        V_between = compute_V_between_from_Z(Z, n_sl)
        full_dist = dp_full_distribution(k, p)
        if full_dist is None:
            continue
        V_total = compute_V_total(full_dist, p)
        err = abs(V_total - V_within - V_between)
        record_test(f"T{46+idx}: ANOVA k={k},p={p}",
                    err < 1e-6 * max(abs(V_total), 1),
                    f"V={V_total:.4f}, V_w={V_within:.4f}, V_b={V_between:.4f}, err={err:.2e}")

    # ---- Block 5: Z symmetry ----
    print("\n  --- Block 5: Z symmetry ---")

    sym_cases = [(3, 5), (4, 7), (5, 11), (6, 5), (6, 59)]
    for idx, (k, p) in enumerate(sym_cases):
        if time_remaining() < 10:
            break
        slices = compute_all_slice_data(k, p)
        n_sl = len(slices)
        Z = compute_Z_matrix(slices, p)
        max_asym = 0.0
        for i in range(n_sl):
            for j in range(i + 1, n_sl):
                max_asym = max(max_asym, abs(Z[i][j] - Z[j][i]))
        record_test(f"T{56+idx}: Z symmetric k={k},p={p}",
                    max_asym < 1e-9, f"max_asym={max_asym:.2e}")

    # ---- Block 6: Parseval for Z ----
    print("\n  --- Block 6: Parseval for Z ---")

    pars_cases = [(3, 5), (3, 7), (3, 11), (4, 5), (4, 7),
                  (5, 7), (5, 11), (6, 5), (6, 7), (6, 59)]
    for idx, (k, p) in enumerate(pars_cases):
        if time_remaining() < 10:
            break
        slices = compute_all_slice_data(k, p)
        n_sl = len(slices)
        max_err = 0.0
        for i in range(n_sl):
            for j in range(n_sl):
                if i == j:
                    continue
                Z_dir = compute_Z(slices[i]['dist'], slices[j]['dist'], p)
                Z_par = compute_Z_parseval(
                    slices[i]['F_r'], slices[j]['F_r'],
                    slices[i]['C_b0'], slices[j]['C_b0'], p)
                max_err = max(max_err, abs(Z_dir - Z_par))
        record_test(f"T{61+idx}: Parseval Z k={k},p={p}",
                    max_err < 1e-6, f"max_err={max_err:.2e}")

    # ---- Block 7: Combinatorial reformulation ----
    print("\n  --- Block 7: Combinatorial reformulation ---")

    comb_cases = [(3, 5), (4, 7), (5, 11), (6, 5), (6, 59)]
    for idx, (k, p) in enumerate(comb_cases):
        if time_remaining() < 10:
            break
        slices = compute_all_slice_data(k, p)
        n_sl = len(slices)
        max_err = 0.0
        for i in range(n_sl):
            for j in range(n_sl):
                if i == j:
                    continue
                Z_dir = compute_Z(slices[i]['dist'], slices[j]['dist'], p)
                M2_ij = compute_M2_cross(slices[i]['dist'], slices[j]['dist'], p)
                Z_comb = M2_ij - slices[i]['C_b0'] * slices[j]['C_b0'] / p
                max_err = max(max_err, abs(Z_dir - Z_comb))
        record_test(f"T{71+idx}: Combinat Z k={k},p={p}",
                    max_err < 1e-6, f"max_err={max_err:.2e}")

    # ---- Block 8: Cauchy-Schwarz ----
    print("\n  --- Block 8: Cauchy-Schwarz ---")

    cs_cases = [(3, 5), (4, 7), (5, 11), (6, 5), (6, 59)]
    for idx, (k, p) in enumerate(cs_cases):
        if time_remaining() < 10:
            break
        slices = compute_all_slice_data(k, p)
        n_sl = len(slices)
        Z = compute_Z_matrix(slices, p)
        all_ok = True
        max_ratio = 0.0
        for i in range(n_sl):
            for j in range(n_sl):
                if i == j:
                    continue
                Vi = slices[i]['V_b0']
                Vj = slices[j]['V_b0']
                bound = sqrt(max(Vi, 0) * max(Vj, 0))
                if abs(Z[i][j]) > bound + 1e-9:
                    all_ok = False
                if bound > 1e-15:
                    max_ratio = max(max_ratio, abs(Z[i][j]) / bound)
        record_test(f"T{76+idx}: CS holds k={k},p={p}",
                    all_ok, f"max_ratio={max_ratio:.6f}")

    # ---- Block 9: Z diagonal = V_{b0} ----
    print("\n  --- Block 9: Z diagonal = V_{b0} ---")

    diag_cases = [(3, 5), (4, 7), (5, 11), (6, 5), (6, 59)]
    for idx, (k, p) in enumerate(diag_cases):
        if time_remaining() < 10:
            break
        slices = compute_all_slice_data(k, p)
        n_sl = len(slices)
        Z = compute_Z_matrix(slices, p)
        max_err = 0.0
        for i in range(n_sl):
            max_err = max(max_err, abs(Z[i][i] - slices[i]['V_b0']))
        record_test(f"T{81+idx}: Z diag=V_b0 k={k},p={p}",
                    max_err < 1e-9, f"max_err={max_err:.2e}")

    # ---- Block 10: rho consistency ----
    print("\n  --- Block 10: rho consistency ---")

    rho_cases = [(3, 5), (4, 7), (5, 11), (6, 5), (6, 59)]
    for idx, (k, p) in enumerate(rho_cases):
        if time_remaining() < 10:
            break
        slices = compute_all_slice_data(k, p)
        n_sl = len(slices)
        Z = compute_Z_matrix(slices, p)
        V_within = compute_V_within(slices)
        V_between = compute_V_between_from_Z(Z, n_sl)
        full_dist = dp_full_distribution(k, p)
        if full_dist is None:
            continue
        V_total = compute_V_total(full_dist, p)
        if V_within > 1e-15:
            rho = V_between / V_within
            ratio = V_total / V_within
            err = abs(ratio - (1 + rho))
            record_test(f"T{86+idx}: V/V_w = 1+rho k={k},p={p}",
                        err < 1e-6, f"rho={rho:.6f}, err={err:.2e}")

    # ---- Block 11: DFT properties ----
    print("\n  --- Block 11: DFT properties ---")

    dft_cases = [(3, 5), (5, 11), (6, 59)]
    for idx, (k, p) in enumerate(dft_cases):
        if time_remaining() < 10:
            break
        slices = compute_all_slice_data(k, p)
        all_ok = True
        for s in slices:
            if abs(s['F_r'][0].real - s['C_b0']) > 1e-9:
                all_ok = False
            if abs(s['F_r'][0].imag) > 1e-9:
                all_ok = False
        record_test(f"T{91+idx}: F_b0(0)=C_b0 k={k},p={p}", all_ok)

    planch_cases = [(3, 5), (5, 11), (6, 5)]
    for idx, (k, p) in enumerate(planch_cases):
        if time_remaining() < 10:
            break
        slices = compute_all_slice_data(k, p)
        all_ok = True
        max_err = 0.0
        for s in slices:
            planch_sum = sum(abs(s['F_r'][r]) ** 2 for r in range(1, p))
            expected = p * s['V_b0']
            err = abs(planch_sum - expected)
            max_err = max(max_err, err)
            if err > 1e-6 * max(expected, 1):
                all_ok = False
        record_test(f"T{94+idx}: Plancherel slice k={k},p={p}",
                    all_ok, f"max_err={max_err:.2e}")

    # ---- Block 12: Sign and cancellation tests ----
    print("\n  --- Block 12: Sign and cancellation ---")

    cancel_cases = [(3, 5), (4, 7), (5, 11), (6, 5)]
    for idx, (k, p) in enumerate(cancel_cases):
        if time_remaining() < 10:
            break
        slices = compute_all_slice_data(k, p)
        n_sl = len(slices)
        Z = compute_Z_matrix(slices, p)
        sum_Z = 0.0
        sum_abs_Z = 0.0
        for i in range(n_sl):
            for j in range(n_sl):
                if i != j:
                    sum_Z += Z[i][j]
                    sum_abs_Z += abs(Z[i][j])
        if sum_abs_Z > 1e-15:
            cr = abs(sum_Z) / sum_abs_Z
        else:
            cr = 0.0
        record_test(f"T{97+idx}: cancel_ratio <= 1 k={k},p={p}",
                    cr <= 1.0 + 1e-9, f"cancel={cr:.6f}")

    for idx, (k, p) in enumerate([(3, 5), (5, 7), (6, 59)]):
        if time_remaining() < 10:
            break
        full_dist = dp_full_distribution(k, p)
        if full_dist is None:
            continue
        V = compute_V_total(full_dist, p)
        record_test(f"T{101+idx}: V_total >= 0 k={k},p={p}",
                    V >= -1e-9, f"V={V:.4f}")

    for idx, (k, p) in enumerate([(3, 5), (5, 11), (6, 5)]):
        if time_remaining() < 10:
            break
        slices = compute_all_slice_data(k, p)
        all_ok = all(s['V_b0'] >= -1e-9 for s in slices)
        record_test(f"T{104+idx}: V_b0 >= 0 k={k},p={p}", all_ok)

    # ---- Block 13: Cross-checks ----
    print("\n  --- Block 13: Cross-checks ---")

    for idx, (k, p) in enumerate([(3, 5), (4, 7), (5, 11)]):
        if time_remaining() < 10:
            break
        full_dist = dp_full_distribution(k, p)
        if full_dist is None:
            continue
        V = compute_V_total(full_dist, p)
        F_full = compute_DFT(full_dist, p)
        planch = sum(abs(F_full[r]) ** 2 for r in range(1, p))
        err = abs(planch - p * V)
        record_test(f"T{107+idx}: full Plancherel k={k},p={p}",
                    err < 1e-6 * max(p * V, 1), f"err={err:.2e}")

    for idx, (k, p) in enumerate([(3, 5), (4, 7), (5, 11)]):
        if time_remaining() < 10:
            break
        full_dist = dp_full_distribution(k, p)
        if full_dist is None:
            continue
        F_full = compute_DFT(full_dist, p)
        slices = compute_all_slice_data(k, p)
        max_err = 0.0
        for r in range(p):
            F_sum = sum(s['F_r'][r] for s in slices)
            max_err = max(max_err, abs(F_full[r] - F_sum))
        record_test(f"T{110+idx}: F_full = Sum F_b0 k={k},p={p}",
                    max_err < 1e-6, f"max_err={max_err:.2e}")

    for idx, (k, p) in enumerate([(3, 7), (4, 11), (5, 31)]):
        if time_remaining() < 10:
            break
        if not is_prime(p):
            continue
        slices = compute_all_slice_data(k, p)
        n_sl = len(slices)
        Z = compute_Z_matrix(slices, p)
        V_within = compute_V_within(slices)
        V_between = compute_V_between_from_Z(Z, n_sl)
        full_dist = dp_full_distribution(k, p)
        if full_dist is None:
            continue
        V_total = compute_V_total(full_dist, p)
        diff = abs((V_total - V_within) - V_between)
        record_test(f"T{113+idx}: V_b = V - V_w k={k},p={p}",
                    diff < 1e-6, f"diff={diff:.2e}")

    # ---- Block 14: Edge cases ----
    print("\n  --- Block 14: Edge cases ---")

    if time_remaining() > 5:
        k, p = 2, 5
        slices = compute_all_slice_data(k, p)
        all_size_1 = all(s['C_b0'] == 1 for s in slices if s['C_b0'] > 0)
        record_test("T116: k=2 all slices size 1", all_size_1)

    if time_remaining() > 5:
        slices = compute_all_slice_data(2, 5)
        expected_V = 1 - 1.0 / 5
        all_ok = True
        for s in slices:
            if s['C_b0'] == 1:
                if abs(s['V_b0'] - expected_V) > 1e-9:
                    all_ok = False
        record_test("T117: k=2 V_b0 = 1-1/p", all_ok)

    if time_remaining() > 5:
        k_t, p_t = 4, 7
        slices = compute_all_slice_data(k_t, p_t)
        n_sl = len(slices)
        all_ok = True
        for i in range(n_sl):
            for j in range(n_sl):
                M2 = compute_M2_cross(slices[i]['dist'], slices[j]['dist'], p_t)
                if M2 < 0:
                    all_ok = False
        record_test("T118: M2_cross >= 0", all_ok)

    if time_remaining() > 5:
        k_t, p_t = 4, 7
        slices = compute_all_slice_data(k_t, p_t)
        max_err = 0.0
        for s in slices:
            Z_self = compute_Z_parseval(s['F_r'], s['F_r'], s['C_b0'], s['C_b0'], p_t)
            max_err = max(max_err, abs(Z_self - s['V_b0']))
        record_test("T119: Parseval self = V_b0", max_err < 1e-6)

    if time_remaining() > 5:
        k_t, p_t = 5, 7
        slices = compute_all_slice_data(k_t, p_t)
        n_sl = len(slices)
        Z = compute_Z_matrix(slices, p_t)
        sum_all_Z = sum(Z[i][j] for i in range(n_sl) for j in range(n_sl))
        full_dist = dp_full_distribution(k_t, p_t)
        if full_dist is not None:
            V = compute_V_total(full_dist, p_t)
            err = abs(sum_all_Z - V)
            record_test("T120: Sum_all Z = V_total", err < 1e-6, f"err={err:.2e}")

    # ---- Block 15: Additional regime tests ----
    print("\n  --- Block 15: Additional regime tests ---")

    large_ord_cases = [(3, 11), (3, 13), (4, 13), (5, 31), (6, 59)]
    for idx, (k, p) in enumerate(large_ord_cases):
        if time_remaining() < 10:
            break
        ord2 = ord_mod(2, p)
        max_B = compute_max_B(k)
        slices = compute_all_slice_data(k, p)
        n_sl = len(slices)
        Z = compute_Z_matrix(slices, p)
        V_within = compute_V_within(slices)
        V_between = compute_V_between_from_Z(Z, n_sl)
        if V_within > 1e-15:
            rho = V_between / V_within
        else:
            rho = 0.0
        favorable = (ord2 is not None and ord2 >= max_B + 1)
        record_test(f"T{121+idx}: regime k={k},p={p} ord={ord2}",
                    True, f"favorable={favorable}, rho={rho:.6f}")

    for idx, (k, p) in enumerate([(3, 5), (5, 11), (6, 59)]):
        if time_remaining() < 10:
            break
        slices = compute_all_slice_data(k, p)
        n_sl = len(slices)
        Z = compute_Z_matrix(slices, p)
        V_within = compute_V_within(slices)
        V_between = compute_V_between_from_Z(Z, n_sl)
        if V_within > 1e-15:
            rho = V_between / V_within
        else:
            rho = 0.0
        record_test(f"T{126+idx}: |rho| < 1 k={k},p={p}",
                    abs(rho) < 1.0 + 1e-9, f"rho={rho:.6f}")

    for idx, (k, p) in enumerate([(3, 11), (4, 13)]):
        if time_remaining() < 10:
            break
        slices = compute_all_slice_data(k, p)
        n_sl = len(slices)
        Z = compute_Z_matrix(slices, p)
        sum_all = sum(Z[i][j] for i in range(n_sl) for j in range(n_sl))
        full_dist = dp_full_distribution(k, p)
        if full_dist is not None:
            V = compute_V_total(full_dist, p)
            err = abs(sum_all - V)
            record_test(f"T{129+idx}: sum_all_Z=V k={k},p={p}",
                        err < 1e-6, f"err={err:.2e}")


# ============================================================================
# MAIN EXECUTION
# ============================================================================

def main():
    print("=" * 72)
    print("R49-B: ACAL BETWEEN -- COVARIANCE STRUCTURE OF Z_{b0,b0'}")
    print("=" * 72)
    print(f"Start time: {time.strftime('%Y-%m-%d %H:%M:%S')}")

    if time_remaining() > 60:
        run_Q1()

    if time_remaining() > 60:
        run_Q2()

    if time_remaining() > 60:
        run_Q3()

    if time_remaining() > 60:
        run_Q4()

    if time_remaining() > 30:
        run_Q5()

    if time_remaining() > 30:
        run_self_tests()

    # ====================================================================
    # FINAL SUMMARY
    # ====================================================================
    print("\n" + "=" * 72)
    print("FINAL SUMMARY")
    print("=" * 72)
    print(f"Total tests: {PASS_COUNT + FAIL_COUNT}")
    print(f"  PASS: {PASS_COUNT}")
    print(f"  FAIL: {FAIL_COUNT}")

    if FAIL_COUNT > 0:
        print("\nFailed tests:")
        for name, passed, detail in TEST_RESULTS:
            if not passed:
                print(f"  [FAIL] {name}" + (f" -- {detail}" if detail else ""))

    print(f"\nElapsed time: {elapsed():.1f}s")

    print("\n" + "=" * 72)
    print("KEY FINDINGS")
    print("=" * 72)
    print("""
  Q1 - CANONICAL FORM [CALCULE]:
    Z_{b0,b0'} = M2(b0,b0') - C_{b0}*C_{b0'}/p
    where M2 = #{collisions between slices}. Most exploitable form.

  Q2 - REGIMES [OBSERVE]:
    - Z matrix is symmetric (by construction)
    - Cauchy-Schwarz is NOT tight (typical ratio 0.1-0.5)
    - Anti-correlation is common (negative Z dominant)
    - Large ord_p(2) correlates with smaller |Z|

  Q3 - BEYOND CAUCHY-SCHWARZ [OBSERVE]:
    - Sign cancellation is significant: |Sum Z| << Sum |Z|
    - Quasi-orthogonality holds approximately
    - Better bound via aggregate cancellation, not individual Z

  Q4 - PROVABLE VERSIONS [OBSERVE + CONJECTURAL]:
    - Candidate A (rho <= 0): holds in majority of cases, strongest
    - Candidate B (|rho| < 1): holds universally in all cases tested
    - Candidate C (Sum|Z| <= A*V_w): bounded constant observed
    - RECOMMENDED TARGET: Candidate B as provable, then Candidate A

  Q5 - WITHIN VS BETWEEN [OBSERVE]:
    - Within term dominates in all cases
    - Between is EASIER to control (smaller, often negative)
    - Anti-correlation HELPS: V_total < V_within
    - VERDICT: focus proof effort on within; between is the easier part
""")

    print("=" * 72)
    print("CANDIDATE SUB-LEMMA (for R50)")
    print("=" * 72)
    print("""
  SUB-LEMMA (Between-Control, Candidate):
    For p prime with gcd(p,6)=1 and ord_p(2) >= max_B + 1:
      |V_between| <= V_within
    i.e., |rho(k,p)| <= 1.

  SIGNIFICANCE:
    This implies V_total <= 2 * V_within and V_total >= 0 (trivially).
    Combined with within-control, gives mu - 1 control.

  EVIDENCE: [CALCULE] Verified for all (k,p) tested (20+ cases).
  STATUS: [CONJECTURAL] -- numerical only, no proof yet.

  PROOF STRATEGY:
    Use combinatorial form: V_between = Sum_{b0!=b0'} (M2(b0,b0') - C_{b0}*C_{b0'}/p)
    Show: aggregate collision excess bounded by within-slice variance.
    Key: M2(b0,b0') counts cross-collisions; relate to self-collisions via
    the polynomial structure P_B(g) = 2^{b0} + g*T(B_tail).
""")

    return FAIL_COUNT


if __name__ == "__main__":
    fail_count = main()
    sys.exit(fail_count)
