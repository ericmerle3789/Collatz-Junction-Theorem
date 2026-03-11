#!/usr/bin/env python3
"""
R52-B: HORNER-MU -- Spectral Decomposition of V via Horner/Slicing
===================================================================
Agent R52-B (Investigateur B) -- Round 52, Axe B

MISSION: Study whether the Horner/slicing decomposition allows direct
control of mu (the second moment ratio) through spectral cancellation.

CONTEXT ACQUIRED (DO NOT RE-PROVE):
  P_B(g) = Sum_{j=0}^{k-1} g^j * 2^{B_j} mod p, g = 2*3^{-1} mod p
  B monotone: 0 <= B_0 <= ... <= B_{k-1} <= max_B = S-k, S = ceil(k*log2(3))
  C = C(max_B+k-1, k-1), M2 = Sum N_r^2, V = M2 - C^2/p, mu = M2*p/C^2

  R43: Horner factorization P_c = u_0 * H_0                    [PROUVE]
  R44: Parseval Sum|S(r)|^2 = p*V                              [PROUVE]
       ACL f_p <= 1/p + sqrt((p-1)(pM2-C^2))/(pC)              [PROUVE]
  R47: Slice decomposition S(r) = Sum omega^{r*2^{b0}} * S_{b0}^{(k-1)}(r)  [PROUVE]
  R48: ANOVA V = Sum V_{b0} + V_between                        [PROUVE]
  R51: TQL-mu: mu-1 <= K*p/C                                   [OBSERVE]

SECTIONS:
  0: Mathematical Primitives
  1: Spectral decomposition of V via slicing (>= 20 tests)
  2: Cancellation of cross-terms in R1 (>= 15 tests)
  3: Quasi-orthogonality bound (>= 15 tests)
  4: Horner recursion for V_{b0} (>= 15 tests)
  5: Improved Parseval bound (>= 15 tests)
  6: Viability diagnostic and summary tables

EPISTEMIC LABELS:
  [PROUVE]       = rigorous proof or DP exact
  [SEMI-FORMEL]  = structured argument, not formal proof
  [CALCULE]      = verified by exact computation
  [OBSERVE]      = numerical evidence, NOT a proof
  [CONJECTURAL]  = plausible but unproven
  [REFUTE]       = contradicted by evidence

Author: Claude Opus 4.6 (R52-B Investigateur Horner-Mu pour Eric Merle)
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
TIME_BUDGET = 170.0  # 170s to stay well under 3 minutes

PASS_COUNT = 0
FAIL_COUNT = 0
VERBOSE = True

# Summary accumulators
SUMMARY_ROWS = []

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

def compute_C_b0(k, b0, max_B=None):
    """C_{b0} = number of monotone tails (B_1,...,B_{k-1}) with b0 <= B_i <= max_B.
    B_{k-1} = max_B forced. Free components: B_1,...,B_{k-2} nondecreasing in [b0, max_B].
    = C(max_B - b0 + k - 2, k - 2).
    """
    if max_B is None:
        max_B = compute_max_B(k)
    if k == 1:
        return 1 if b0 == max_B else 0
    if k == 2:
        return 1
    return comb(max_B - b0 + k - 2, k - 2)

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

def classify_regime(k, p):
    """Classify (k,p) into finest sub-regime."""
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


# ============================================================================
# SECTION 0b: DISTRIBUTION ENGINES
# ============================================================================

def dp_full_distribution(k, p, max_time=15.0):
    """Full residue distribution N_r via DP."""
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


def compute_tail_distribution(k, p, b0, g=None):
    """N^{tail}_{b0,r} = tail distribution.
    T(B_tail) = Sum_{j=1}^{k-1} g^{j-1} * 2^{B_j}, B_j in [b0, max_B], B_{k-1}=max_B.
    Returns: (count_array[p], C_{b0})
    """
    S_val = compute_S(k)
    max_B = S_val - k
    if g is None:
        g = compute_g(k, p)

    count = [0] * p

    if k == 1:
        if b0 == max_B:
            count[0] += 1
            return count, 1
        return count, 0

    if k == 2:
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
# SECTION 0c: SPECTRAL COMPUTATIONS
# ============================================================================

def compute_S_r(k, p, dist=None):
    """S(r) = Sum_B omega^{r*P_B(g)} for r=0..p-1, via DFT of distribution."""
    if dist is None:
        dist = dp_full_distribution(k, p)
    if dist is None:
        return None
    omega = cmath.exp(2j * pi / p)
    S_vals = []
    for r in range(p):
        s = sum(dist[res] * omega ** (r * res) for res in range(p))
        S_vals.append(s)
    return S_vals


def compute_S_b0_spectral(k, p, b0, g=None):
    """S_{b0}^{(k-1)}(r) = Sum over monotone tails of omega^{r * Sum g^j * 2^{B_j}}.
    Returns list of complex values for r=0..p-1, plus tail count.
    """
    S_val = compute_S(k)
    max_B = S_val - k
    if g is None:
        g = compute_g(k, p)
    omega = cmath.exp(2j * pi / p)

    # Compute residues for each tail vector
    residues = []
    if k == 2:
        # Only B_1 = max_B, P_tail = g^1 * 2^{max_B}
        res = (g * pow(2, max_B, p)) % p
        residues.append(res)
    else:
        # Enumerate (B_1,...,B_{k-1}) with b0 <= B_1 <= ... <= B_{k-1} = max_B
        for combo in combinations_with_replacement(range(b0, max_B + 1), k - 2):
            B_rest = combo + (max_B,)
            res = 0
            gj = g  # g^1
            for bj in B_rest:
                res = (res + gj * pow(2, bj, p)) % p
                gj = (gj * g) % p
            residues.append(res)

    # Build count distribution and DFT
    count = [0] * p
    for res in residues:
        count[res] += 1

    result = []
    for r in range(p):
        s = sum(count[rr] * omega ** (r * rr) for rr in range(p))
        result.append(s)
    return result, len(residues)


def compute_V_slice(dist, p):
    """V_{b0} = Sum_r (N_r - C/p)^2."""
    C = sum(dist)
    mean = C / p
    return sum((n - mean) ** 2 for n in dist)


def compute_V_total(full_dist, p):
    """V = Sum_r (N_r - C/p)^2."""
    C = sum(full_dist)
    mean = C / p
    return sum((nr - mean) ** 2 for nr in full_dist)


def compute_Z(dist_a, dist_b, p):
    """Z_{a,b} = Sum_r (N_{a,r}-C_a/p)(N_{b,r}-C_b/p)."""
    C_a = sum(dist_a)
    C_b = sum(dist_b)
    mean_a = C_a / p
    mean_b = C_b / p
    return sum((dist_a[r] - mean_a) * (dist_b[r] - mean_b) for r in range(p))


# ============================================================================
# SECTION 0d: TEST CASE GENERATION
# ============================================================================

def generate_R1_cases(k_range=(3, 9), max_p=300, target_R1=8):
    """Generate (k,p) test cases focusing on R1 regime."""
    cases = []
    R1_count = 0
    other_count = 0
    for k in range(k_range[0], k_range[1]):
        max_B = compute_max_B(k)
        # Check feasibility
        C_max = compute_C_b0(k, 0, max_B)
        if C_max > 200000:
            continue
        for p in range(5, max_p):
            if not is_prime(p) or p == 3:
                continue
            reg = classify_regime(k, p)
            o2 = ord_mod(2, p)
            if reg in ('R1', 'R2', 'R3') and R1_count < target_R1:
                cases.append((k, p))
                R1_count += 1
            elif reg == 'R_gen' and other_count < 4:
                cases.append((k, p))
                other_count += 1
            if R1_count >= target_R1 and other_count >= 3:
                break
        if R1_count >= target_R1 and other_count >= 3:
            break
    return cases


def generate_diverse_cases(k_range=(3, 9), max_p=200, max_cases=25):
    """Generate diverse (k,p) test cases across regimes."""
    cases = []
    seen = set()
    for k in range(k_range[0], k_range[1]):
        max_B = compute_max_B(k)
        C_max = compute_C_b0(k, 0, max_B)
        if C_max > 300000:
            continue
        regime_found = {'R1': 0, 'R2': 0, 'R3': 0, 'R_gen': 0}
        for p in range(5, max_p):
            if not is_prime(p) or p == 3:
                continue
            if (k, p) in seen:
                continue
            reg = classify_regime(k, p)
            if regime_found[reg] < 2:
                cases.append((k, p))
                seen.add((k, p))
                regime_found[reg] += 1
            if len(cases) >= max_cases:
                break
        if len(cases) >= max_cases:
            break
    return cases


# ============================================================================
# SECTION 1: SPECTRAL DECOMPOSITION OF V VIA SLICING
# ============================================================================

def run_section1():
    """Section 1: Verify the spectral identity
    V = (1/p) Sum_{r>=1} |S(r)|^2
      = (1/p) Sum_{r>=1} |Sum_{b0} omega^{r*2^{b0}} * S_{b0}(r)|^2
      = (1/p) Sum_{r>=1} [ Sum_{b0} |S_{b0}(r)|^2
                          + Sum_{b0!=b0'} omega^{r*(2^{b0}-2^{b0'})} * S_{b0}(r) * conj(S_{b0'}(r)) ]
    Split into diagonal (within) and off-diagonal (between) parts.
    """
    print("\n" + "=" * 72)
    print("SECTION 1: SPECTRAL DECOMPOSITION OF V VIA SLICING")
    print("=" * 72)

    print("""
  IDENTITY [PROUVE par R44 + R47]:
    V = (1/p) Sum_{r=1}^{p-1} |S(r)|^2
    S(r) = Sum_{b0} phi(r,b0) * S_{b0}(r),  phi(r,b0) = omega^{r*2^{b0}}
    |S(r)|^2 = Sum_{b0} |S_{b0}(r)|^2                    [diagonal]
             + Sum_{b0 != b0'} phi * S_{b0} * conj(S_{b0'})  [off-diagonal]

  Test: separate diagonal vs off-diagonal contributions and verify
  V_diag = (1/p) Sum_r Sum_{b0} |S_{b0}(r)|^2 = V_within
  V_offdiag = V - V_diag = V_between
""")

    test_cases = generate_diverse_cases(max_cases=16)
    n_decomp_ok = 0

    for k, p in test_cases:
        if time_remaining() < 100:
            break
        max_B = compute_max_B(k)
        g = compute_g(k, p)
        o2 = ord_mod(2, p)
        regime = classify_regime(k, p)
        omega = cmath.exp(2j * pi / p)

        # 1. Compute S(r) via DP
        dist = dp_full_distribution(k, p, max_time=5.0)
        if dist is None:
            continue
        C = sum(dist)
        V_total = compute_V_total(dist, p)

        # 2. Compute S_{b0}(r) for each b0
        S_b0_vals = {}  # b0 -> list of complex S_{b0}(r) for r=0..p-1
        C_b0s = {}
        for b0 in range(max_B + 1):
            s_vals, cnt = compute_S_b0_spectral(k, p, b0, g)
            S_b0_vals[b0] = s_vals
            C_b0s[b0] = cnt

        # 3. Diagonal part: (1/p) Sum_{r=1}^{p-1} Sum_{b0} |S_{b0}(r)|^2
        V_diag = 0.0
        for r in range(1, p):
            for b0 in range(max_B + 1):
                V_diag += abs(S_b0_vals[b0][r]) ** 2
        V_diag /= p

        # 4. Off-diagonal part via reconstruction
        V_recon = 0.0
        for r in range(1, p):
            # Reconstruct |S(r)|^2 from slicing
            S_recon = 0j
            for b0 in range(max_B + 1):
                phi = omega ** (r * pow(2, b0, p))
                S_recon += phi * S_b0_vals[b0][r]
            V_recon += abs(S_recon) ** 2
        V_recon /= p

        V_offdiag = V_recon - V_diag

        # 5. Verify V_recon == V_total
        err_recon = abs(V_recon - V_total)
        tol = max(1e-6, V_total * 1e-8)
        ok_recon = err_recon < tol
        record_test(
            f"1.1-V_recon k={k} p={p} ({regime})",
            ok_recon,
            f"V_total={V_total:.6f}, V_recon={V_recon:.6f}, err={err_recon:.2e}"
        )

        # 6. Verify V_diag == V_within (from ANOVA)
        V_within_anova = 0.0
        for b0 in range(max_B + 1):
            sdist, cb0 = compute_slice_distribution_full(k, p, b0, g)
            V_within_anova += compute_V_slice(sdist, p)

        err_within = abs(V_diag - V_within_anova)
        tol_within = max(1e-6, V_within_anova * 1e-8) if V_within_anova > 0 else 1e-6
        ok_within = err_within < tol_within
        record_test(
            f"1.2-V_diag=V_within k={k} p={p} ({regime})",
            ok_within,
            f"V_diag={V_diag:.6f}, V_within={V_within_anova:.6f}, err={err_within:.2e}"
        )

        # 7. Compute ratio
        ratio_offdiag = V_offdiag / V_diag if V_diag > 0 else float('inf')
        rho = V_offdiag / V_within_anova if V_within_anova > 0 else float('inf')

        print(f"    k={k}, p={p}, regime={regime}: "
              f"V_diag/V={V_diag/V_total:.4f}, V_off/V_diag={ratio_offdiag:.4f}, "
              f"rho={rho:.4f}")

        if ok_recon and ok_within:
            n_decomp_ok += 1

        # 8. Per-r analysis: ratio off-diag/diag
        offdiag_over_diag_by_r = []
        for r in range(1, p):
            diag_r = sum(abs(S_b0_vals[b0][r]) ** 2 for b0 in range(max_B + 1))
            # Compute full |S(r)|^2
            S_full_r = sum(
                omega ** (r * pow(2, b0, p)) * S_b0_vals[b0][r]
                for b0 in range(max_B + 1)
            )
            full_sq_r = abs(S_full_r) ** 2
            off_r = full_sq_r - diag_r
            ratio_r = off_r / diag_r if diag_r > 1e-15 else 0.0
            offdiag_over_diag_by_r.append(ratio_r)

        if offdiag_over_diag_by_r:
            avg_ratio_r = sum(offdiag_over_diag_by_r) / len(offdiag_over_diag_by_r)
            max_ratio_r = max(abs(x) for x in offdiag_over_diag_by_r)
            record_test(
                f"1.3-offdiag_bounded k={k} p={p} ({regime})",
                max_ratio_r < 10.0,
                f"|off/diag|_max={max_ratio_r:.4f}, avg={avg_ratio_r:.4f}"
            )

        SUMMARY_ROWS.append({
            'k': k, 'p': p, 'regime': regime, 'o2': o2,
            'V': V_total, 'V_within': V_diag, 'V_between': V_offdiag,
            'ratio_VV': V_total / V_diag if V_diag > 0 else float('inf'),
            'rho': rho, 'C': C,
        })

    print(f"\n  Decomposition identity verified: {n_decomp_ok} cases")


# ============================================================================
# SECTION 2: CANCELLATION OF CROSS-TERMS IN R1
# ============================================================================

def run_section2():
    """Section 2: In R1, phases omega^{r*2^{b0}} are DISTINCT for b0=0..max_B.
    When summing over r=1..p-1, cross-terms with distinct phases cancel partially.
    Quantify cancellation efficiency.
    """
    print("\n" + "=" * 72)
    print("SECTION 2: CANCELLATION OF CROSS-TERMS IN R1")
    print("=" * 72)

    print("""
  KEY IDEA [SEMI-FORMEL]:
    For each pair (b0, b0'), the cross-term contribution to V is:
      X(b0,b0') = (1/p) Sum_{r=1}^{p-1} omega^{r*Delta_2} * S_{b0}(r) * conj(S_{b0'}(r))
    where Delta_2 = 2^{b0} - 2^{b0'} mod p.

    Trivial bound: |X(b0,b0')| <= (1/p) Sum_r |S_{b0}(r)| * |S_{b0'}(r)|
    Actual value: |X(b0,b0')| (with phase cancellation)
    Cancellation ratio = |X_actual| / X_trivial
    Smaller ratio = more cancellation from phase rotation.
""")

    # Focus on R1 cases
    R1_cases = []
    for k in range(3, 9):
        max_B = compute_max_B(k)
        C_max = compute_C_b0(k, 0, max_B)
        if C_max > 100000:
            continue
        for p in range(5, 200):
            if not is_prime(p) or p == 3:
                continue
            reg = classify_regime(k, p)
            if reg in ('R1', 'R2', 'R3'):
                R1_cases.append((k, p, reg))
                if len(R1_cases) >= 12:
                    break
        if len(R1_cases) >= 12:
            break

    cancel_data = []

    for k, p, regime in R1_cases:
        if time_remaining() < 80:
            break
        max_B = compute_max_B(k)
        g = compute_g(k, p)
        omega = cmath.exp(2j * pi / p)

        # Compute S_{b0}(r) for all b0
        S_b0_vals = {}
        for b0 in range(max_B + 1):
            s_vals, cnt = compute_S_b0_spectral(k, p, b0, g)
            S_b0_vals[b0] = s_vals

        n_slices = max_B + 1
        if n_slices < 2:
            continue

        # For each pair (b0, b0'), compute cancellation ratio
        cancel_ratios = []
        for i in range(n_slices):
            for j in range(i + 1, n_slices):
                delta_2 = (pow(2, i, p) - pow(2, j, p)) % p

                # Actual cross-term: (1/p) Sum_r omega^{r*delta_2} * S_i(r) * conj(S_j(r))
                actual = 0j
                trivial = 0.0
                for r in range(1, p):
                    cross = S_b0_vals[i][r] * S_b0_vals[j][r].conjugate()
                    actual += omega ** (r * delta_2) * cross
                    trivial += abs(cross)
                actual /= p
                trivial /= p

                ratio = abs(actual) / trivial if trivial > 1e-15 else 0.0
                cancel_ratios.append(ratio)

        if cancel_ratios:
            avg_cancel = sum(cancel_ratios) / len(cancel_ratios)
            max_cancel = max(cancel_ratios)
            min_cancel = min(cancel_ratios)

            # Test: cancellation is significant (ratio < 1)
            ok = avg_cancel < 1.0
            record_test(
                f"2.1-cancellation k={k} p={p} ({regime})",
                ok,
                f"avg_ratio={avg_cancel:.4f}, max={max_cancel:.4f}, min={min_cancel:.4f}, "
                f"n_pairs={len(cancel_ratios)}"
            )

            # Test: in R1, cancellation should be substantial
            if regime in ('R2', 'R3'):
                ok_strong = avg_cancel < 0.5
                record_test(
                    f"2.2-strong_cancel k={k} p={p} ({regime})",
                    ok_strong,
                    f"avg_ratio={avg_cancel:.4f} (expect < 0.5 in {regime})"
                )

            cancel_data.append({
                'k': k, 'p': p, 'regime': regime,
                'avg_cancel': avg_cancel, 'max_cancel': max_cancel,
                'n_pairs': len(cancel_ratios),
            })

    # Summary
    if cancel_data:
        print("\n  Cancellation summary by regime:")
        for regime in ('R3', 'R2', 'R1'):
            entries = [d for d in cancel_data if d['regime'] == regime]
            if entries:
                avg_of_avg = sum(d['avg_cancel'] for d in entries) / len(entries)
                print(f"    {regime}: avg_cancel_ratio = {avg_of_avg:.4f} "
                      f"({len(entries)} cases)")


# ============================================================================
# SECTION 3: QUASI-ORTHOGONALITY BOUND
# ============================================================================

def run_section3():
    """Section 3: If S_{b0}(r) were quasi-orthogonal on r, then
    V approx V_within (V_between approx 0, |rho| approx 0).
    Measure deviation: V / V_within = 1 + rho.
    """
    print("\n" + "=" * 72)
    print("SECTION 3: QUASI-ORTHOGONALITY BOUND")
    print("=" * 72)

    print("""
  ARGUMENT [SEMI-FORMEL]:
    If S_{b0}(r) are quasi-orthogonal (cross-correlations small), then:
      V = V_within + V_between approx V_within
      => V / V_within = 1 + rho, with rho small
    This would give mu - 1 approx (p/C^2) * Sum V_{b0}
    = (p/C^2) * Sum (C_{b0}/C)^2 * C^2 * (mu_{b0}-1)/p  [weighted average]

    In R1, distinct phases should enforce quasi-orthogonality.
""")

    test_cases = generate_diverse_cases(max_cases=18)
    rho_data = []

    for k, p in test_cases:
        if time_remaining() < 60:
            break
        max_B = compute_max_B(k)
        g = compute_g(k, p)
        regime = classify_regime(k, p)
        o2 = ord_mod(2, p)

        # Compute V_total via DP
        dist = dp_full_distribution(k, p, max_time=5.0)
        if dist is None:
            continue
        C = sum(dist)
        V_total = compute_V_total(dist, p)

        # Compute V_within via slice distributions
        V_within = 0.0
        for b0 in range(max_B + 1):
            sdist, cb0 = compute_slice_distribution_full(k, p, b0, g)
            V_within += compute_V_slice(sdist, p)

        V_between = V_total - V_within
        rho = V_between / V_within if V_within > 0 else float('inf')
        ratio_V = V_total / V_within if V_within > 0 else float('inf')

        # Test: |rho| < 1 universally [OBSERVE from R49]
        ok_rho = abs(rho) < 1.0
        record_test(
            f"3.1-rho_bounded k={k} p={p} ({regime})",
            ok_rho,
            f"rho={rho:.6f}, V/V_within={ratio_V:.6f}"
        )

        # Test: in R1+, rho should be small
        if regime in ('R1', 'R2', 'R3'):
            ok_small = abs(rho) < 0.5
            record_test(
                f"3.2-rho_small_R1 k={k} p={p} ({regime})",
                ok_small,
                f"|rho|={abs(rho):.6f} (expect < 0.5 in {regime})"
            )

        rho_data.append({
            'k': k, 'p': p, 'regime': regime, 'o2': o2,
            'rho': rho, 'V_total': V_total, 'V_within': V_within,
        })

    # Summary
    if rho_data:
        print("\n  Quasi-orthogonality summary:")
        for regime in ('R3', 'R2', 'R1', 'R_gen'):
            entries = [d for d in rho_data if d['regime'] == regime]
            if entries:
                avg_rho = sum(abs(d['rho']) for d in entries) / len(entries)
                max_rho = max(abs(d['rho']) for d in entries)
                print(f"    {regime}: avg|rho|={avg_rho:.4f}, max|rho|={max_rho:.4f} "
                      f"({len(entries)} cases)")


# ============================================================================
# SECTION 4: HORNER RECURSION FOR V_{b0}
# ============================================================================

def run_section4():
    """Section 4: V_{b0} relates to a sub-problem of dimension k-1.
    Test the recursive structure:
      V_{b0} = V(standard problem k-1, [0, max_B - b0])
    and the weighted decomposition:
      V/C^2 = Sum (C_{b0}/C)^2 * (V_{b0}/C_{b0}^2) + V_between/C^2
    """
    print("\n" + "=" * 72)
    print("SECTION 4: HORNER RECURSION FOR V_{b0}")
    print("=" * 72)

    print("""
  STRUCTURE [SEMI-FORMEL]:
    V_{b0} is the within-variance for slice b0.
    The tail problem for slice b0 has (k-1) components in [b0, max_B].
    By change of variable c_i = B_i - b0, this becomes a standard
    (k-1)-component problem with range [0, max_B - b0].

    WEIGHTED DECOMPOSITION:
      mu - 1 = V*p/C^2
      V/C^2 = Sum_{b0} (C_{b0}/C)^2 * (V_{b0}/C_{b0}^2) + V_between/C^2
            = Sum_{b0} w_{b0} * (mu_{b0}-1)/p + V_between/C^2

    If V_between is small (Section 3), then mu-1 is a weighted average
    of sub-problem mu_{b0}-1 values.
""")

    test_cases = generate_diverse_cases(max_cases=18)
    recur_data = []

    for k, p in test_cases:
        if time_remaining() < 40:
            break
        if k < 4:
            continue  # Need k >= 4 for k-1 >= 3 sub-problem
        max_B = compute_max_B(k)
        g = compute_g(k, p)
        regime = classify_regime(k, p)

        # Compute full distribution and V
        dist = dp_full_distribution(k, p, max_time=5.0)
        if dist is None:
            continue
        C = sum(dist)
        V_total = compute_V_total(dist, p)
        mu = V_total * p / (C ** 2) + 1 if C > 0 else float('inf')

        # Compute per-slice V_{b0} and the weighted sum
        weighted_sum = 0.0
        V_within = 0.0
        max_sub_mu = 0.0
        sub_mus = []

        for b0 in range(max_B + 1):
            # Slice distribution
            sdist, cb0 = compute_slice_distribution_full(k, p, b0, g)
            if cb0 == 0:
                continue
            V_b0 = compute_V_slice(sdist, p)
            V_within += V_b0

            # Sub-problem mu
            mu_b0 = V_b0 * p / (cb0 ** 2) + 1
            w_b0 = (cb0 / C) ** 2
            weighted_sum += w_b0 * (mu_b0 - 1) / p
            sub_mus.append(mu_b0)
            max_sub_mu = max(max_sub_mu, mu_b0)

        V_between = V_total - V_within

        # Test: weighted decomposition identity
        # V/C^2 = weighted_sum + V_between/C^2
        lhs = V_total / (C ** 2)
        rhs = weighted_sum + V_between / (C ** 2)
        err = abs(lhs - rhs)
        ok_decomp = err < 1e-10
        record_test(
            f"4.1-decomp_identity k={k} p={p} ({regime})",
            ok_decomp,
            f"V/C^2={lhs:.8f}, weighted+between={rhs:.8f}, err={err:.2e}"
        )

        # Test: mu is bounded by max sub-mu (modulo V_between)
        # mu - 1 = p * V/C^2 = p * weighted_sum + p * V_between/C^2
        # If V_between >= 0: mu - 1 <= max_{b0}(mu_{b0}-1) + p*V_between/C^2
        # If V_between < 0: mu - 1 < max_{b0}(mu_{b0}-1) [even better!]
        if sub_mus:
            bound_from_sub = max(m - 1 for m in sub_mus) + abs(p * V_between / (C ** 2))
            ok_bound = (mu - 1) <= bound_from_sub + 1e-10
            record_test(
                f"4.2-mu_bounded k={k} p={p} ({regime})",
                ok_bound,
                f"mu-1={mu-1:.6f}, bound={bound_from_sub:.6f}, max_sub_mu-1={max_sub_mu-1:.6f}"
            )

        # Test: does the recursion converge? Compare V(k)/C(k)^2 to sub-problem scale
        if sub_mus:
            avg_sub_mu_m1 = sum(m - 1 for m in sub_mus) / len(sub_mus)
            ratio_mu = (mu - 1) / avg_sub_mu_m1 if avg_sub_mu_m1 > 1e-15 else float('inf')
            is_contracting = ratio_mu < 2.0  # rough: mu doesn't blow up
            record_test(
                f"4.3-contraction k={k} p={p} ({regime})",
                is_contracting,
                f"mu-1={mu-1:.6f}, avg_sub(mu-1)={avg_sub_mu_m1:.6f}, ratio={ratio_mu:.4f}"
            )

        recur_data.append({
            'k': k, 'p': p, 'regime': regime,
            'mu': mu, 'max_sub_mu': max_sub_mu,
            'rho': V_between / V_within if V_within > 0 else 0.0,
            'n_slices': max_B + 1,
        })

    # Summary
    if recur_data:
        print("\n  Recursion summary:")
        for d in recur_data:
            print(f"    k={d['k']}, p={d['p']} ({d['regime']}): "
                  f"mu-1={d['mu']-1:.4f}, max_sub_mu-1={d['max_sub_mu']-1:.4f}, "
                  f"rho={d['rho']:.4f}")


# ============================================================================
# SECTION 5: IMPROVED PARSEVAL BOUND
# ============================================================================

def run_section5():
    """Section 5: Can slicing + R1 yield a bound better than Cauchy-Schwarz?

    Standard CS on slicing:
      |S(r)|^2 <= n * Sum_{b0} |S_{b0}(r)|^2   (triangle ineq, n = max_B+1)
    Hence V <= n * V_within.

    But if phases are well-spread (R1), interference is limited:
      |S(r)|^2 <= (1 + epsilon) * Sum |S_{b0}(r)|^2   for large ord_p(2)

    Compare:
      - CS bound: V <= n * V_within
      - Actual V / V_within = 1 + rho (Section 3)
      - Improvement factor = n / (1 + rho)
    """
    print("\n" + "=" * 72)
    print("SECTION 5: IMPROVED PARSEVAL BOUND")
    print("=" * 72)

    print("""
  BOUNDS [OBSERVE]:
    CS: |S(r)|^2 <= n * Sum |S_{b0}(r)|^2, so V <= n * V_within
    Actual: V = (1 + rho) * V_within, with rho observed small in R1
    If rho << n, the Horner decomposition gives a factor-n improvement.

    Testing: for each r, compute |S(r)|^2 / Sum|S_{b0}(r)|^2
    and compare to n (CS bound) and 1+epsilon (improved).
""")

    test_cases = generate_diverse_cases(max_cases=16)
    bound_data = []

    for k, p in test_cases:
        if time_remaining() < 30:
            break
        max_B = compute_max_B(k)
        g = compute_g(k, p)
        regime = classify_regime(k, p)
        n_slices = max_B + 1
        omega = cmath.exp(2j * pi / p)

        # Compute S_{b0}(r) for all b0
        S_b0_vals = {}
        for b0 in range(max_B + 1):
            s_vals, cnt = compute_S_b0_spectral(k, p, b0, g)
            S_b0_vals[b0] = s_vals

        # Per-r ratio analysis: |S(r)|^2 / Sum|S_{b0}(r)|^2
        max_ratio_r = 0.0
        ratios_r = []
        for r in range(1, p):
            diag_r = sum(abs(S_b0_vals[b0][r]) ** 2 for b0 in range(n_slices))
            S_full_r = sum(
                omega ** (r * pow(2, b0, p)) * S_b0_vals[b0][r]
                for b0 in range(n_slices)
            )
            full_sq_r = abs(S_full_r) ** 2
            ratio_r = full_sq_r / diag_r if diag_r > 1e-15 else 1.0
            ratios_r.append(ratio_r)
            max_ratio_r = max(max_ratio_r, ratio_r)

        # CS bound says ratio <= n_slices
        ok_cs = max_ratio_r <= n_slices + 1e-6
        record_test(
            f"5.1-CS_bound k={k} p={p} ({regime})",
            ok_cs,
            f"max|S|^2/Sum|S_b0|^2={max_ratio_r:.4f}, CS_bound={n_slices}"
        )

        # Compute actual V/V_within
        dist = dp_full_distribution(k, p, max_time=5.0)
        if dist is None:
            continue
        C = sum(dist)
        V_total = compute_V_total(dist, p)
        V_within = 0.0
        for b0 in range(max_B + 1):
            sdist, cb0 = compute_slice_distribution_full(k, p, b0, g)
            V_within += compute_V_slice(sdist, p)

        ratio_V = V_total / V_within if V_within > 0 else float('inf')
        improvement = n_slices / ratio_V if ratio_V > 0 else float('inf')

        # Test: Horner gives improvement over CS
        ok_improve = ratio_V < n_slices
        record_test(
            f"5.2-improvement k={k} p={p} ({regime})",
            ok_improve,
            f"V/V_within={ratio_V:.4f}, CS_bound={n_slices}, "
            f"improvement_factor={improvement:.2f}x"
        )

        # Test: in R1, expect 1+epsilon bound with epsilon small
        if regime in ('R1', 'R2', 'R3'):
            epsilon = ratio_V - 1
            ok_eps = epsilon < 1.0
            record_test(
                f"5.3-epsilon_small k={k} p={p} ({regime})",
                ok_eps,
                f"1+eps={ratio_V:.6f}, eps={epsilon:.6f}"
            )

        bound_data.append({
            'k': k, 'p': p, 'regime': regime, 'n_slices': n_slices,
            'max_ratio_r': max_ratio_r, 'V_over_Vw': ratio_V,
            'improvement': improvement, 'C': C,
        })

    # Summary
    if bound_data:
        print("\n  Bound comparison summary:")
        print(f"  {'k':>3} {'p':>4} {'regime':>6} {'n':>3} "
              f"{'V/Vw':>8} {'CS':>4} {'improv':>8} {'max_r':>8}")
        for d in bound_data:
            print(f"  {d['k']:>3} {d['p']:>4} {d['regime']:>6} {d['n_slices']:>3} "
                  f"{d['V_over_Vw']:>8.4f} {d['n_slices']:>4} "
                  f"{d['improvement']:>8.2f}x {d['max_ratio_r']:>8.4f}")


# ============================================================================
# SECTION 6: VIABILITY DIAGNOSTIC AND SUMMARY TABLES
# ============================================================================

def run_section6():
    """Section 6: For each (k,p) in R1, compute viability diagnostic:
    - V_within / C : should be bounded if TQL-mu holds
    - V_between / V_within : should be small (= rho)
    - Cancellation ratio of cross-terms
    - Compare CS alone vs CS + Horner cancellation
    """
    print("\n" + "=" * 72)
    print("SECTION 6: VIABILITY DIAGNOSTIC")
    print("=" * 72)

    print("""
  DIAGNOSTIC [OBSERVE]:
    For the Horner route to beat Cauchy-Schwarz, we need:
      (A) V_between is small relative to V_within (rho << 1)
      (B) Cross-term cancellation from phase rotation is substantial
      (C) The resulting bound V <= (1+rho)*V_within <= (1+rho)*Sum V_{b0}
          is tighter than the naive CS bound V <= n*V_within

    Viability criterion: improvement_factor = n / (1+rho) >> 1
""")

    # Use data already accumulated in SUMMARY_ROWS
    if not SUMMARY_ROWS:
        print("  No data available (earlier sections skipped).")
        return

    # Additional diagnostic tests
    for row in SUMMARY_ROWS:
        k, p, regime = row['k'], row['p'], row['regime']
        C = row['C']
        V = row['V']
        V_within = row['V_within']
        rho = row['rho']
        max_B = compute_max_B(k)
        n_slices = max_B + 1

        # D1: V_within / C bounded
        v_within_over_C = V_within / C if C > 0 else float('inf')
        ok_d1 = v_within_over_C < C  # should be much less than C
        record_test(
            f"6.1-V_within/C k={k} p={p} ({regime})",
            ok_d1,
            f"V_within/C={v_within_over_C:.4f}, C={C}"
        )

        # D2: mu-1 bounded by K*p/C
        mu_m1 = V * p / (C ** 2) if C > 0 else float('inf')
        K_eff = mu_m1 * C / p if p > 0 else float('inf')
        ok_d2 = K_eff < 10.0  # generous bound
        record_test(
            f"6.2-TQL_K k={k} p={p} ({regime})",
            ok_d2,
            f"mu-1={mu_m1:.6f}, K_eff={K_eff:.4f}, p/C={p/C:.4f}"
        )

        # D3: Horner improvement factor
        improvement = n_slices / (1 + abs(rho)) if abs(rho) < n_slices else 1.0
        ok_d3 = improvement > 1.5
        record_test(
            f"6.3-improvement k={k} p={p} ({regime})",
            ok_d3,
            f"n={n_slices}, rho={rho:.4f}, improvement={improvement:.2f}x"
        )

    # Final summary table
    print("\n" + "=" * 72)
    print("FINAL SUMMARY TABLE")
    print("=" * 72)
    print(f"\n  {'k':>3} {'p':>5} {'regime':>6} {'o2':>4} {'C':>8} "
          f"{'mu-1':>10} {'V/Vw':>8} {'rho':>10} {'n':>3} {'improv':>8} {'K_eff':>8}")
    print("  " + "-" * 90)

    for row in sorted(SUMMARY_ROWS, key=lambda r: (r['regime'], r['k'], r['p'])):
        k, p = row['k'], row['p']
        C = row['C']
        V = row['V']
        V_w = row['V_within']
        rho = row['rho']
        regime = row['regime']
        o2 = row['o2']
        max_B = compute_max_B(k)
        n_slices = max_B + 1
        mu_m1 = V * p / (C ** 2) if C > 0 else float('inf')
        K_eff = mu_m1 * C / p if p > 0 else float('inf')
        ratio_VV = row['ratio_VV']
        improvement = n_slices / ratio_VV if ratio_VV > 0 else 0.0

        print(f"  {k:>3} {p:>5} {regime:>6} {o2:>4} {C:>8} "
              f"{mu_m1:>10.6f} {ratio_VV:>8.4f} {rho:>10.6f} {n_slices:>3} "
              f"{improvement:>8.2f}x {K_eff:>8.4f}")

    # Regime-level summary
    print("\n  REGIME-LEVEL AVERAGES:")
    print(f"  {'regime':>6} {'avg_rho':>10} {'avg_improv':>10} {'avg_K_eff':>10} {'count':>6}")
    for regime in ('R3', 'R2', 'R1', 'R_gen'):
        entries = [r for r in SUMMARY_ROWS if r['regime'] == regime]
        if not entries:
            continue
        avg_rho = sum(abs(r['rho']) for r in entries) / len(entries)
        improvements = []
        K_effs = []
        for r in entries:
            k_r = r['k']
            n_sl = compute_max_B(k_r) + 1
            ratio = r['ratio_VV']
            improvements.append(n_sl / ratio if ratio > 0 else 0.0)
            C = r['C']
            p_r = r['p']
            V = r['V']
            mu_m1 = V * p_r / (C ** 2) if C > 0 else 0.0
            K_effs.append(mu_m1 * C / p_r if p_r > 0 else 0.0)
        avg_imp = sum(improvements) / len(improvements)
        avg_K = sum(K_effs) / len(K_effs)
        print(f"  {regime:>6} {avg_rho:>10.4f} {avg_imp:>10.2f}x {avg_K:>10.4f} {len(entries):>6}")

    # Verdict
    print("\n  VIABILITY VERDICT:")
    r1_entries = [r for r in SUMMARY_ROWS if r['regime'] in ('R1', 'R2', 'R3')]
    gen_entries = [r for r in SUMMARY_ROWS if r['regime'] == 'R_gen']

    if r1_entries:
        avg_rho_r1 = sum(abs(r['rho']) for r in r1_entries) / len(r1_entries)
        avg_imp_r1 = sum(
            (compute_max_B(r['k']) + 1) / r['ratio_VV']
            for r in r1_entries if r['ratio_VV'] > 0
        ) / len(r1_entries)
        if avg_rho_r1 < 0.3 and avg_imp_r1 > 2.0:
            verdict = "VIABLE"
            detail = (f"Horner route gives {avg_imp_r1:.1f}x improvement over CS in R1. "
                      f"rho={avg_rho_r1:.4f} << 1 confirms quasi-orthogonality.")
        elif avg_rho_r1 < 0.5:
            verdict = "MARGINAL"
            detail = (f"Some improvement ({avg_imp_r1:.1f}x) but rho={avg_rho_r1:.4f} "
                      f"not negligible. Horner helps but doesn't close the gap alone.")
        else:
            verdict = "NON-VIABLE"
            detail = (f"rho={avg_rho_r1:.4f} too large. Cross-terms don't cancel enough. "
                      f"Improvement only {avg_imp_r1:.1f}x.")
        print(f"    R1+ regime: [{verdict}] -- {detail}")
    else:
        print("    No R1+ data to assess.")

    if gen_entries:
        avg_rho_gen = sum(abs(r['rho']) for r in gen_entries) / len(gen_entries)
        print(f"    R_gen regime: avg|rho|={avg_rho_gen:.4f} "
              f"(expect larger, less cancellation)")


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 72)
    print("R52-B: HORNER-MU -- Spectral Decomposition of V via Horner/Slicing")
    print("=" * 72)
    print(f"  Budget: {TIME_BUDGET:.0f}s")
    print(f"  Start: {time.strftime('%H:%M:%S')}")

    run_section1()
    if time_remaining() > 80:
        run_section2()
    if time_remaining() > 50:
        run_section3()
    if time_remaining() > 30:
        run_section4()
    if time_remaining() > 20:
        run_section5()
    run_section6()

    # Final report
    print("\n" + "=" * 72)
    print(f"TOTAL: {PASS_COUNT + FAIL_COUNT} tests, "
          f"{PASS_COUNT} PASS, {FAIL_COUNT} FAIL")
    rate = PASS_COUNT / (PASS_COUNT + FAIL_COUNT) * 100 if (PASS_COUNT + FAIL_COUNT) > 0 else 0
    print(f"Pass rate: {rate:.1f}%")
    print(f"Runtime: {elapsed():.1f}s / {TIME_BUDGET:.0f}s budget")
    print("=" * 72)

    if FAIL_COUNT > 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
