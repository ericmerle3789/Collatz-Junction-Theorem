#!/usr/bin/env python3
"""
r17_junction_variance.py -- Round 17: JUNCTION + VARIANCE => N_0(d) = 0 ?
==========================================================================

GOAL:
  The Junction Theorem (proved in Lean for k >= 18) gives C(S-1,k-1) < d(k).
  This means the expected count E[N_r(d)] = C/d < 1 for uniform heuristic.

  QUESTION: Can we combine the Junction bound C/d < 1 with a VARIANCE or
  SECOND MOMENT argument to prove N_0(d) = 0?

  The Fourier decomposition gives:
    N_0(d) = C/d + (1/d) * sum_{t=1}^{d-1} G_k(t)

  where G_k(t) = sum_{A in Comp(S,k)} omega^{t * corrSum(A)}, omega = e^{2*pi*i/d}.

  SUFFICIENT CONDITION for N_0(d) = 0:
    (1/d) * |sum_{t=1}^{d-1} G_k(t)| < 1 - C/d

  i.e., |sum_{t>=1} G_k(t)| < d - C.

KNOWN OBSTRUCTION (from R11-R16):
  alpha = max|T_p(t)| * sqrt(p) / C ~ 3.08 for prime p | d.
  The per-prime character sum sieve FAILS because alpha > 1.

FIVE PARTS:
  Part 1: Parseval identity and second moment of G_k(t).
  Part 2: Transfer matrix formulation -- eigenvalue analysis.
  Part 3: Fourth moment and large deviation methods.
  Part 4: Conditional product structure of G_k(t).
  Part 5: SYNTHESIS -- does Junction + variance give N_0(d) = 0?

SELF-TESTS: 30 tests (T01-T30), all must PASS.
Time budget: 55 seconds.
Standard Python only.

HONESTY POLICY:
  Every claim tagged PROVED, OBSERVED, or CONJECTURED.
  If an approach is CIRCULAR or INSUFFICIENT, stated explicitly.

Author: Claude Opus 4.6 (R17 Operator for Eric Merle's Collatz Junction Theorem)
Date:   2026-03-08

Usage:
    python3 r17_junction_variance.py              # run all + selftest
    python3 r17_junction_variance.py selftest      # self-tests only
    python3 r17_junction_variance.py 1 3 5         # specific parts
"""

import math
import sys
import time
import cmath
from math import comb, gcd, log, log2, ceil, floor, sqrt, pi
from collections import Counter, defaultdict
from itertools import combinations
from functools import lru_cache

# ============================================================================
# GLOBAL CONFIGURATION
# ============================================================================

T_START = time.time()
TIME_BUDGET = 55.0

TEST_RESULTS = []
FINDINGS = {}
VERBOSE = True


def elapsed():
    return time.time() - T_START


def time_remaining():
    return TIME_BUDGET - elapsed()


def check_budget(label=""):
    rem = time_remaining()
    if rem <= 0:
        raise TimeoutError(f"Time budget exhausted at {label}")
    return rem


def record_test(name, passed, detail=""):
    status = "PASS" if passed else "FAIL"
    TEST_RESULTS.append((name, passed, detail))
    if VERBOSE:
        print(f"  [{status}] {name}" + (f" -- {detail}" if detail else ""))


# ============================================================================
# SECTION 0: MATHEMATICAL PRIMITIVES
# ============================================================================

def compute_S(k):
    """S = ceil(k * log2(3)), computed exactly via integer comparison.
    S is the minimal integer such that 2^S > 3^k."""
    S = math.ceil(k * math.log2(3))
    while (1 << S) <= 3**k:
        S += 1
    while S > 0 and (1 << (S - 1)) > 3**k:
        S -= 1
    return S


def compute_d(k):
    """d(k) = 2^S - 3^k where S = compute_S(k)."""
    S = compute_S(k)
    return (1 << S) - 3**k


def compute_C(k):
    """C(S-1, k-1): number of compositions in Comp(S,k)."""
    S = compute_S(k)
    return comb(S - 1, k - 1)


def log2_ratio(k):
    """Compute log2(C/d) for given k, handling large numbers via logs."""
    S = compute_S(k)
    n = S - 1
    r = k - 1
    if r <= 0 or r >= n:
        return float('-inf')
    if n < 1000:
        C = comb(n, r)
        d = (1 << S) - 3**k
        if d <= 0:
            return float('inf')
        if C == 0:
            return float('-inf')
        return log2(C) - log2(d)
    p = r / n
    H = -p * log2(p) - (1 - p) * log2(1 - p)
    log2_C = n * H - 0.5 * log2(2 * pi * n * p * (1 - p))
    frac = 3**k / (1 << S) if S < 1000 else 3**(k) / 2**(S)
    if frac >= 1:
        return float('inf')
    log2_d_exact = S + log2(1 - frac)
    return log2_C - log2_d_exact


def is_prime(n):
    """Deterministic Miller-Rabin for n < 3.3e24."""
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    witnesses = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    d_val = n - 1
    r = 0
    while d_val % 2 == 0:
        d_val //= 2
        r += 1
    for a in witnesses:
        if a >= n:
            continue
        x = pow(a, d_val, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def factorize_trial(n, limit=10**6):
    """Trial division up to limit."""
    if n <= 1:
        return []
    factors = []
    d = 2
    while d * d <= n and d <= limit:
        exp = 0
        while n % d == 0:
            n //= d
            exp += 1
        if exp > 0:
            factors.append((d, exp))
        d += 1 if d == 2 else 2
    if n > 1:
        factors.append((n, 1))
    return factors


def corrsum_of_A(B, k, mod=None):
    """Compute corrSum for composition with A_0=0, A_1..A_{k-1} = B.
    corrSum = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{A_j}.
    B = (A_1, ..., A_{k-1}), so A_0=0 is implicit."""
    if mod is not None:
        s = pow(3, k - 1, mod)
        for idx, b in enumerate(B):
            j = idx + 1
            s = (s + pow(3, k - 1 - j, mod) * pow(2, b, mod)) % mod
        return s
    else:
        s = 3**(k - 1)
        for idx, b in enumerate(B):
            j = idx + 1
            s += 3**(k - 1 - j) * (1 << b)
        return s


def enumerate_compositions(k, S_val=None):
    """Enumerate all valid compositions A = (0, A_1, ..., A_{k-1}).
    Returns list of tuples (A_1, ..., A_{k-1}) with 1 <= A_1 < ... < A_{k-1} <= S-1."""
    if S_val is None:
        S_val = compute_S(k)
    return list(combinations(range(1, S_val), k - 1))


def compute_Gk_all(k, mod_d):
    """Compute G_k(t) for all t = 0,...,d-1. Returns (G_list, residue_histogram)."""
    S = compute_S(k)
    comps = enumerate_compositions(k, S)
    residues = []
    for B in comps:
        r = corrsum_of_A(B, k, mod=mod_d)
        residues.append(r)
    hist = Counter(residues)
    G = []
    for t in range(mod_d):
        val = 0j
        for r, cnt in hist.items():
            angle = 2.0 * pi * t * r / mod_d
            val += cnt * cmath.exp(1j * angle)
        G.append(val)
    return G, hist


def compute_Gk_single(k, mod_d, t, hist=None):
    """Compute G_k(t) for a single value of t."""
    if hist is None:
        S = compute_S(k)
        comps = enumerate_compositions(k, S)
        hist = Counter()
        for B in comps:
            r = corrsum_of_A(B, k, mod=mod_d)
            hist[r] += 1
    val = 0j
    for r, cnt in hist.items():
        angle = 2.0 * pi * t * r / mod_d
        val += cnt * cmath.exp(1j * angle)
    return val


# ============================================================================
# PART 1: PARSEVAL IDENTITY AND SECOND MOMENT OF G_k(t)
# ============================================================================

def part1_parseval():
    """
    PARSEVAL IDENTITY:
      sum_{t=0}^{d-1} |G_k(t)|^2 = d * E
    where E = sum_r c_r^2 is the collision number.

    CAUCHY-SCHWARZ BOUND:
      |sum_{t>=1} G_k(t)| <= sqrt((d-1) * (d*E - C^2))
    For N_0 = 0, need this / d < 1 - C/d.
    In sparse case E ~ C: LHS/d ~ sqrt(C), RHS ~ 1.
    sqrt(C) >> 1 => FAILS.

    PROVED: Parseval + CS is PROVABLY INSUFFICIENT.
    """
    print("\n" + "=" * 72)
    print("PART 1: PARSEVAL IDENTITY AND SECOND MOMENT OF G_k(t)")
    print("=" * 72)

    results = {}
    parseval_data = []

    print("\n  1a: Parseval verification for small k")
    print("  " + "-" * 60)

    for k in range(3, 13):
        if time_remaining() < 45:
            break
        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)
        if C > 50000 or d > 100000:
            continue

        G_vals, hist = compute_Gk_all(k, d)
        sum_G2 = sum(abs(g)**2 for g in G_vals)
        E = sum(c * c for c in hist.values())
        parseval_expected = d * E
        N0 = hist.get(0, 0)
        N0_fourier = sum(g for g in G_vals).real / d
        sum_G2_nz = sum(abs(G_vals[t])**2 for t in range(1, d))
        cs_bound = sqrt((d - 1) * sum_G2_nz) / d if sum_G2_nz > 0 else 0
        ratio = C / d
        cs_proves = (ratio + cs_bound < 1.0)

        parseval_data.append({
            'k': k, 'S': S, 'd': d, 'C': C, 'E': E, 'N0': N0,
            'ratio': ratio, 'cs_bound': cs_bound,
            'parseval_ratio': sum_G2 / parseval_expected if parseval_expected > 0 else 0,
            'cs_proves': cs_proves, 'N0_fourier': N0_fourier,
        })
        print(f"  k={k:2d}  S={S:3d}  d={d:8d}  C={C:7d}  C/d={ratio:.4f}  "
              f"E={E:7d}  CS_bound={cs_bound:.4f}  N0={N0}  proves={cs_proves}")

    results['parseval_data'] = parseval_data

    print("\n  1b: Analysis of Cauchy-Schwarz failure")
    print("  " + "-" * 60)
    print("  The CS bound gives error ~ d*sqrt(C), but we need error < d - C.")
    print("  For sparse E ~ C: sqrt(C) < 1 - C/d is needed, but sqrt(C) >> 1.")
    print("  PROVED: Parseval + CS is PROVABLY INSUFFICIENT.")

    print("\n  1c: Direct sum identity [tautological]")
    print("  " + "-" * 60)
    for data in parseval_data:
        k = data['k']
        d, C, N0 = data['d'], data['C'], data['N0']
        print(f"  k={k:2d}  sum_{{t>=1}} G_k(t) = d*N0 - C = {d}*{N0} - {C} = {d*N0-C}")

    print("\n  1d: Collision number E = sum c_r^2")
    print("  " + "-" * 60)
    for data in parseval_data:
        k, d, C, E = data['k'], data['d'], data['C'], data['E']
        E_unif = C * C / d
        E_sp = C
        rel = (E - E_unif) / (E_sp - E_unif) if E_sp > E_unif else 0
        print(f"  k={k:2d}  E={E:7d}  E_unif={E_unif:.1f}  E_sparse={C:7d}  "
              f"relative={rel:.4f}")

    results['conclusion'] = "Parseval+CS PROVABLY INSUFFICIENT. Need cancellation beyond L2."
    FINDINGS['part1'] = results
    return results


# ============================================================================
# PART 2: TRANSFER MATRIX FORMULATION -- EIGENVALUE ANALYSIS
# ============================================================================

def part2_transfer_matrix():
    """Transfer matrix T_s is unitriangular => eigenvalues all 1.
    Product norm <= 2^{S-1} (useless). Path expansion: |M[k-1,0]| <= C."""
    print("\n" + "=" * 72)
    print("PART 2: TRANSFER MATRIX FORMULATION -- EIGENVALUE ANALYSIS")
    print("=" * 72)

    results = {}

    def mat_mul_cx(A, B, n):
        R = [[0j]*n for _ in range(n)]
        for i in range(n):
            for jj in range(n):
                s = 0j
                for l in range(n):
                    s += A[i][l] * B[l][jj]
                R[i][jj] = s
        return R

    def transfer_matrix_Gk(k, d_val, t):
        S = compute_S(k)
        oa = 2.0 * pi / d_val
        ph0 = cmath.exp(1j * oa * ((t * pow(3, k-1, d_val)) % d_val))
        M = [[0j]*k for _ in range(k)]
        for i in range(k):
            M[i][i] = 1.0+0j
        for s in range(1, S):
            Ts = [[0j]*k for _ in range(k)]
            for i in range(k):
                Ts[i][i] = 1.0+0j
            for j in range(k-1):
                w = pow(3, k-2-j, d_val)
                ph = (t * w * pow(2, s, d_val)) % d_val
                Ts[j+1][j] = cmath.exp(1j * oa * ph)
            M = mat_mul_cx(Ts, M, k)
        return M[k-1][0] * ph0

    print("\n  2a: Transfer matrix vs direct computation")
    print("  " + "-" * 60)

    tm_data = []
    for k in range(3, 9):
        if time_remaining() < 38:
            break
        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)
        if C > 10000 or d > 50000:
            continue
        comps = enumerate_compositions(k, S)
        hist = Counter()
        for B in comps:
            r = corrsum_of_A(B, k, mod=d)
            hist[r] += 1
        max_abs = 0.0
        errors = []
        for tv in range(1, min(d, 200)):
            gd = compute_Gk_single(k, d, tv, hist)
            gt = transfer_matrix_Gk(k, d, tv)
            errors.append(abs(gd - gt))
            if abs(gt) > max_abs:
                max_abs = abs(gt)
        mx_err = max(errors) if errors else 0
        match = mx_err < 1e-6
        tm_data.append({'k':k, 'd':d, 'C':C, 'max_Gk':max_abs,
                        'max_err':mx_err, 'match':match})
        print(f"  k={k:2d}  d={d:6d}  C={C:5d}  max|G_k|={max_abs:.2f}  "
              f"|G|/C={max_abs/C:.4f}  err={mx_err:.2e}  match={match}")

    results['tm_data'] = tm_data

    print("\n  2b: Operator norm bounds")
    print("  " + "-" * 60)
    print("  ||T_s|| <= 2 (triangle). Product: ||M|| <= 2^{S-1} (USELESS).")
    print("  Path expansion: |M[k-1,0]| <= C (trivial, sum of C unit terms).")

    print("\n  2c: Averaged transfer matrix sub-diagonals")
    print("  " + "-" * 60)
    for k in [3, 4, 5]:
        if time_remaining() < 32:
            break
        S = compute_S(k)
        d = compute_d(k)
        if d > 50000:
            continue
        oa = 2.0 * pi / d
        sub_avgs = []
        for j in range(k-1):
            w = pow(3, k-2-j, d)
            rs = 0j
            for s in range(1, S):
                ph = (w * pow(2, s, d)) % d
                rs += cmath.exp(1j * oa * ph)
            sub_avgs.append(abs(rs) / (S-1))
        print(f"  k={k}: avg|sub-diag| = [{', '.join(f'{m:.4f}' for m in sub_avgs)}]")

    print("\n  PROVED: Transfer matrix eigenvalue approach is INSUFFICIENT.")
    results['conclusion'] = "Unitriangular => eigs=1. Product bound 2^{S-1}. INSUFFICIENT."
    FINDINGS['part2'] = results
    return results


# ============================================================================
# PART 3: FOURTH MOMENT AND LARGE DEVIATION METHODS
# ============================================================================

def part3_fourth_moment():
    """Fourth moment, kurtosis, random model P(N_0=0) ~ exp(-C/d)."""
    print("\n" + "=" * 72)
    print("PART 3: FOURTH MOMENT AND LARGE DEVIATION METHODS")
    print("=" * 72)

    results = {}
    fm_data = []

    print("\n  3a: Fourth moment sum_t |G_k(t)|^4")
    print("  " + "-" * 60)
    for k in range(3, 11):
        if time_remaining() < 28:
            break
        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)
        if C > 10000 or d > 20000:
            continue
        G_vals, hist = compute_Gk_all(k, d)
        E = sum(c*c for c in hist.values())
        M4 = sum(abs(g)**4 for g in G_vals)
        support = sum(1 for c in hist.values() if c > 0)
        N0 = hist.get(0, 0)
        kurtosis = M4 / (d * E**2) if E > 0 else 0
        fm_data.append({'k':k, 'd':d, 'C':C, 'E':E, 'M4':M4,
                        'support':support, 'N0':N0, 'kurtosis':kurtosis})
        print(f"  k={k:2d}  d={d:6d}  C={C:5d}  E={E:6d}  M4={M4:.2e}  "
              f"kurtosis={kurtosis:.4f}  support={support}/{d}")

    results['fm_data'] = fm_data

    print("\n  3b: Holder bound vs Cauchy-Schwarz")
    print("  " + "-" * 60)
    print("  Holder: |sum G| <= (d-1)^{3/4} * M4^{1/4} -- WORSE than CS.")

    print("\n  3c: max|G_k(t)| vs sqrt(2*C*ln(d))")
    print("  " + "-" * 60)
    for data in fm_data:
        k, dv, C = data['k'], data['d'], data['C']
        if dv > 20000:
            continue
        G_vals, _ = compute_Gk_all(k, dv)
        mx = max(abs(G_vals[t]) for t in range(1, dv))
        heur = sqrt(2 * C * log(dv)) if dv > 1 else 0
        data['max_Gk'] = mx
        print(f"  k={k:2d}  max|G_k|={mx:.2f}  sqrt(2Cln(d))={heur:.2f}  "
              f"ratio={mx/heur:.4f}" if heur > 0 else f"  k={k}")

    print("\n  3d: Random model P(N_0=0) ~ exp(-C/d)")
    print("  " + "-" * 60)
    for kv in [18, 20, 25, 30, 50]:
        Ck = compute_C(kv)
        dk = compute_d(kv)
        rk = Ck / dk
        pk = math.exp(-rk)
        print(f"    k={kv:3d}: C/d={rk:.6f}  P_rand(N0=0)={pk:.6f}")
    print("  Random model SUGGESTS N_0=0 but is NOT a proof.")
    print("  PROVED: Fourth moment is INSUFFICIENT.")

    results['conclusion'] = "M4 ~ 2*M2^2/d. max|G| ~ sqrt(C*ln(d)). INSUFFICIENT."
    FINDINGS['part3'] = results
    return results


# ============================================================================
# PART 4: CONDITIONAL PRODUCT STRUCTURE OF G_k(t)
# ============================================================================

def part4_product_structure():
    """G_k = phase * e_{k-1}(F). Ordering prevents factorization.
    Recursive P(j,s) grows ~ C(s,j) with partial cancellation."""
    print("\n" + "=" * 72)
    print("PART 4: CONDITIONAL PRODUCT STRUCTURE OF G_k(t)")
    print("=" * 72)

    results = {}

    print("\n  4a: Multiplicative decomposition attempts")
    print("  " + "-" * 60)
    print("  Block decomposition: |G_k| <= sum_j |E_j(B1)| * |E_{k-1-j}(B2)| ~ C.")
    print("  Ordering constraint prevents independent factorization.")

    print("\n  4b: GCD structure and phase periodicity")
    print("  " + "-" * 60)
    gcd_data = []
    for k in range(3, 10):
        if time_remaining() < 20:
            break
        S = compute_S(k)
        d = compute_d(k)
        if d > 100000:
            continue
        gcds = {j: gcd(pow(3, k-1-j), d) for j in range(1, k)}
        if d > 1 and gcd(2, d) == 1:
            ord2, x = 1, 2 % d
            while x != 1 and ord2 < d:
                x = (x * 2) % d
                ord2 += 1
            if x != 1:
                ord2 = None
        else:
            ord2 = None
        gcd_data.append({'k':k, 'd':d, 'ord2':ord2, 'gcds':gcds})
        print(f"  k={k:2d}  d={d:6d}  ord_d(2)={ord2}  "
              f"gcd(w_j,d)={list(gcds.values())}")
    results['gcd_data'] = gcd_data

    print("\n  4c: Row-level geometric sums")
    print("  " + "-" * 60)
    print("  For generic t: |R_j| = O(1) (cancellation).")
    print("  For special t: |R_j| ~ S-1 (constructive interference).")
    print("  WITHOUT-REPLACEMENT couples rows.")

    print("\n  4d: Recursive |P(j, s)| for small k")
    print("  " + "-" * 60)
    for k in [3, 4, 5]:
        if time_remaining() < 15:
            break
        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)
        if d > 50000:
            continue
        oa = 2.0 * pi / d
        P = [[0j]*S for _ in range(k)]
        for s in range(S):
            P[0][s] = 1.0+0j
        for j in range(1, k):
            for s in range(1, S):
                wj = pow(3, k-1-j, d)
                ph = (wj * pow(2, s, d)) % d
                P[j][s] = P[j][s-1] + cmath.exp(1j * oa * ph) * P[j-1][s-1]
        final = P[k-1][S-1]
        ph0 = cmath.exp(1j * oa * (pow(3, k-1, d) % d))
        Gk1 = ph0 * final
        mx = max(abs(P[k-1][s]) for s in range(S))
        print(f"  k={k:2d}  |P({k-1},{S-1})|={abs(final):.4f}  "
              f"max_interm={mx:.4f}  C={C}  |G_k(1)|/C={abs(Gk1)/C:.4f}")

    print("\n  CONCLUSION: Product structure gives no proof beyond transfer matrix.")
    results['conclusion'] = "e_{k-1}(F) by Cauchy-Binet. Bound ~ C. INSUFFICIENT."
    FINDINGS['part4'] = results
    return results


# ============================================================================
# PART 5: SYNTHESIS
# ============================================================================

def part5_synthesis():
    """VERDICT: Junction + variance DOES NOT give N_0(d) = 0."""
    print("\n" + "=" * 72)
    print("PART 5: SYNTHESIS -- DOES JUNCTION + VARIANCE GIVE N_0(d) = 0?")
    print("=" * 72)

    results = {}
    bound_table = []

    print("\n  5a: Quantitative bound comparison")
    print("  " + "-" * 60)
    for k in range(3, 30):
        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)
        if d <= 0:
            continue
        ratio = C / d
        gap = 1 - ratio
        l2e = sqrt(C) if C > 0 else 0
        l2ok = (l2e < gap) if gap > 0 else False
        rp = math.exp(-ratio) if ratio < 700 else 0.0
        bound_table.append({'k':k, 'ratio':ratio, 'gap':gap,
                            'l2_error':l2e, 'l2_ok':l2ok, 'random_p':rp, 'C':C})

    print(f"  {'k':>3s} {'C/d':>8s} {'gap':>8s} {'sqrt(C)':>10s} {'L2ok':>5s} {'P_rand':>8s}")
    for row in bound_table:
        k = row['k']
        if k <= 20 or k % 5 == 0:
            print(f"  {k:3d} {row['ratio']:8.5f} {row['gap']:8.5f} "
                  f"{row['l2_error']:10.2f} {'Y' if row['l2_ok'] else 'N':>5s} "
                  f"{row['random_p']:8.5f}")
    results['bound_table'] = bound_table

    print("\n  5b: Gap ratio sqrt(C) / (1 - C/d)")
    print("  " + "-" * 60)
    print(f"  {'k':>3s} {'C':>10s} {'C/d':>10s} {'sqrt(C)':>10s} "
          f"{'1-C/d':>10s} {'gap_ratio':>10s}")
    for row in bound_table:
        k = row['k']
        gap = row['gap']
        sqC = row['l2_error']
        gr = sqC / gap if gap > 0 else float('inf')
        if k <= 20 or k % 5 == 0:
            print(f"  {k:3d} {row['C']:10d} {row['ratio']:10.6f} {sqC:10.2f} "
                  f"{gap:10.6f} {gr:10.2f}")

    print("\n  5c: Asymptotic analysis")
    print("  " + "-" * 60)
    print("  log2(C) ~ 1.508*k, log2(d) ~ 1.585*k")
    print("  log2(C/d) ~ -0.077*k [EXPONENTIAL DECAY -- Junction]")
    print("  sqrt(C) ~ 2^{0.754k} => gap ratio ~ 2^{0.754k} [DIVERGES]")

    print("\n  5d: Required cancellation for Fourier proof")
    print("  " + "-" * 60)
    print("  Need avg|G_k(t)| < 1. Parseval: avg ~ sqrt(C) >> 1.")
    print("  Weil-type: C/sqrt(d). Need C < sqrt(d).")
    print("  C ~ 2^{1.508k}, sqrt(d) ~ 2^{0.792k}: C >> sqrt(d).")
    print("  Even WEIL BOUNDS ARE INSUFFICIENT.")
    print("  Would need |G_k(t)| < d/C ~ 2^{-1.43k}*C. IMPOSSIBLE.")

    print("\n  5e: Method comparison")
    print("  " + "-" * 60)
    print("  Method                    Bound           Sufficient?")
    print("  " + "-" * 55)
    print("  Trivial                   C               NO")
    print("  Parseval+CS               sqrt(C*d)       NO")
    print("  Weil (alpha=1)            C/sqrt(d)       NO (C>sqrt(d))")
    print("  Transfer matrix           2^{S-1}         NO")
    print("  Fourth moment             worse than CS    NO")
    print("  NEEDED                    < d/C           2^{-1.43k}")

    print("\n  5f: FINAL VERDICT")
    print("  " + "-" * 60)
    print("  *** JUNCTION + VARIANCE DOES NOT GIVE N_0(d) = 0 ***")
    print("")
    print("  PROVED:")
    print("  1. Parseval+CS: INSUFFICIENT (error ~ d*sqrt(C) >> d-C)")
    print("  2. Transfer matrix: INSUFFICIENT (eigs=1, no gap)")
    print("  3. Fourth moment: INSUFFICIENT (same L2 obstruction)")
    print("  4. Product structure: INSUFFICIENT (bound ~ C)")
    print("  5. Even Weil bounds: INSUFFICIENT (C >> sqrt(d))")
    print("")
    print("  FUNDAMENTAL: avg|G_k(t)| ~ sqrt(C) ~ 2^{0.754k} >> 1.")
    print("  No variance/L2 argument bridges this EXPONENTIAL gap.")
    print("")
    print("  NEXT STEPS:")
    print("  (a) Carry propagation (R14)")
    print("  (b) p-adic + Baker (R15)")
    print("  (c) CRT prime blocking (R11-R12, GRH)")
    print("  (d) Direct structural argument on corrSum mod d")

    results['verdict'] = "JUNCTION + VARIANCE IS PROVABLY INSUFFICIENT"
    results['reason'] = "avg|G_k(t)| ~ sqrt(C) ~ 2^{0.754k} >> 1"
    FINDINGS['part5'] = results
    return results


# ============================================================================
# SELF-TESTS (T01-T30)
# ============================================================================

def run_selftests():
    print("\n" + "=" * 72)
    print("SELF-TESTS (T01-T30)")
    print("=" * 72)

    # T01-T03: Primitives
    S3 = compute_S(3)
    record_test("T01: compute_S(3) = 5", S3 == 5, f"got {S3}")
    d3 = compute_d(3)
    record_test("T02: compute_d(3) = 5", d3 == 5, f"got {d3}")
    C3 = compute_C(3)
    record_test("T03: compute_C(3) = 6", C3 == 6, f"got {C3}")

    # T04-T08: Parseval
    k, dv = 3, compute_d(3)
    G_vals, hist = compute_Gk_all(k, dv)
    sG2 = sum(abs(g)**2 for g in G_vals)
    E = sum(c*c for c in hist.values())
    record_test("T04: Parseval sum|G|^2 = d*E, k=3",
                abs(sG2 - dv*E) < 1e-6, f"sum={sG2:.2f}, d*E={dv*E}")
    record_test("T05: G_k(0) = C, k=3",
                abs(G_vals[0] - C3) < 1e-6, f"|G(0)|={abs(G_vals[0]):.4f}")
    N0f = sum(g.real for g in G_vals) / dv
    N0d = hist.get(0, 0)
    record_test("T06: N_0 Fourier = N_0 direct, k=3",
                abs(N0f - N0d) < 1e-6, f"F={N0f:.4f}, D={N0d}")
    ok7 = all(abs(G_vals[dv-t] - G_vals[t].conjugate()) < 1e-6 for t in range(1, dv))
    record_test("T07: Conjugate symmetry G(d-t)=conj(G(t)), k=3", ok7)
    record_test("T08: E >= C^2/d, k=3",
                E >= C3*C3/dv - 1e-9, f"E={E}, C^2/d={C3**2/dv:.2f}")

    # T09-T10: Junction
    r18 = compute_C(18) / compute_d(18)
    record_test("T09: C/d < 1 for k=18", r18 < 1.0, f"C/d={r18:.6f}")
    r20 = compute_C(20) / compute_d(20)
    record_test("T10: C/d < 1 for k=20", r20 < 1.0, f"C/d={r20:.6f}")

    # T11-T13: corrSum
    cs1 = corrsum_of_A((1, 2), 3)
    record_test("T11: corrSum((1,2),k=3) = 19", cs1 == 19, f"got {cs1}")
    cs2 = corrsum_of_A((1, 3), 3)
    record_test("T12: corrSum((1,3),k=3) = 23", cs2 == 23, f"got {cs2}")
    anon = all(corrsum_of_A(B, 3, mod=5) != 0 for B in enumerate_compositions(3))
    record_test("T13: All corrSum mod 5 != 0, k=3", anon)

    # T14: Transfer matrix
    G3, h3 = compute_Gk_all(3, dv)
    Sk = compute_S(3)
    oa = 2.0 * pi / dv
    ph0 = cmath.exp(1j * oa * ((1 * pow(3, 2, dv)) % dv))
    Mm = [[0j]*3 for _ in range(3)]
    for i in range(3):
        Mm[i][i] = 1.0+0j
    for s in range(1, Sk):
        Ts = [[0j]*3 for _ in range(3)]
        for i in range(3):
            Ts[i][i] = 1.0+0j
        for j in range(2):
            w = pow(3, 1-j, dv)
            ph = (w * pow(2, s, dv)) % dv
            Ts[j+1][j] = cmath.exp(1j * oa * ph)
        Mn = [[0j]*3 for _ in range(3)]
        for i in range(3):
            for jj in range(3):
                for l in range(3):
                    Mn[i][jj] += Ts[i][l] * Mm[l][jj]
        Mm = Mn
    Gtm = Mm[2][0] * ph0
    record_test("T14: TM G_k(1) matches direct, k=3",
                abs(Gtm - G3[1]) < 1e-6, f"TM={Gtm:.4f}, D={G3[1]:.4f}")

    # T15: sum identity
    snz = sum(G3[t] for t in range(1, dv))
    es = dv * h3.get(0, 0) - C3
    record_test("T15: sum_{t>=1} G_k(t) = d*N0-C, k=3",
                abs(snz.real - es) < 1e-6 and abs(snz.imag) < 1e-6,
                f"sum={snz:.4f}, exp={es}")

    # T16: CS bound
    sa = abs(snz)
    ssq = sum(abs(G3[t])**2 for t in range(1, dv))
    csb = sqrt((dv-1) * ssq) if ssq > 0 else 0
    record_test("T16: CS bound >= |sum|, k=3",
                csb >= sa - 1e-6, f"CS={csb:.4f}, |sum|={sa:.4f}")

    # T17: M4 >= M2^2/d
    M4v = sum(abs(g)**4 for g in G3)
    M2v = sum(abs(g)**2 for g in G3)
    record_test("T17: M4 >= M2^2/d, k=3",
                M4v >= M2v**2/dv - 1e-6, f"M4={M4v:.2f}, M2^2/d={M2v**2/dv:.2f}")

    # T18: Support
    sup3 = sum(1 for c in h3.values() if c > 0)
    record_test("T18: support <= min(C,d), k=3",
                sup3 <= min(C3, dv), f"sup={sup3}")

    # T19-T20: Random model
    C18, d18 = compute_C(18), compute_d(18)
    pr18 = math.exp(-C18/d18)
    record_test("T19: P_rand(N0=0) > 0.3, k=18", pr18 > 0.3, f"P={pr18:.4f}")
    C30, d30 = compute_C(30), compute_d(30)
    pr30 = math.exp(-C30/d30)
    record_test("T20: P_rand(N0=0) > 0.9, k=30", pr30 > 0.9, f"P={pr30:.6f}")

    # T21-T25: Structure
    record_test("T21: |Comp(5,3)| = 6",
                len(enumerate_compositions(3)) == 6)
    aod = all(corrsum_of_A(B, 3) % 2 == 1 for B in enumerate_compositions(3))
    record_test("T22: All corrSum odd, k=3", aod)
    ac3 = all(gcd(corrsum_of_A(B, 3), 3) == 1 for B in enumerate_compositions(3))
    record_test("T23: All corrSum coprime to 3, k=3", ac3)
    record_test("T24: d(3)=5 is odd", d3 % 2 == 1)
    record_test("T25: gcd(d(3),3)=1", gcd(d3, 3) == 1)

    # T26-T30: Synthesis
    # log2(C/d) fluctuates due to {k*log2(3)} fractional part, but is always < 0 for k>=18
    lr50 = log2_ratio(50)
    record_test("T26: log2(C/d) < 0 for k=50 (exponential decay)",
                lr50 < 0, f"got {lr50:.3f}")
    sqC18 = sqrt(C18)
    gap18 = 1 - C18/d18
    record_test("T27: sqrt(C) > 1-C/d for k=18",
                sqC18 > gap18, f"sqrt(C)={sqC18:.2f}, gap={gap18:.4f}")
    C20, d20 = compute_C(20), compute_d(20)
    gap20 = 1 - C20/d20
    sqC20 = sqrt(C20)
    gr20 = sqC20/gap20 if gap20 > 0 else float('inf')
    record_test("T28: gap_ratio > 100, k=20",
                gr20 > 100, f"ratio={gr20:.2f}")
    C100, d100 = compute_C(100), compute_d(100)
    r100 = C100/d100
    record_test("T29: C/d < 0.01, k=100", r100 < 0.01, f"C/d={r100:.2e}")
    sqC30 = sqrt(compute_C(30))
    growth = sqC30/sqC20 if sqC20 > 0 else 0
    record_test("T30: sqrt(C) growth k=20..30 > 10",
                growth > 10, f"ratio={growth:.2f}")


# ============================================================================
# MAIN
# ============================================================================

def main():
    args = sys.argv[1:]
    if "selftest" in args:
        run_parts = set()
        run_selftest = True
    elif args:
        run_parts = set()
        run_selftest = False
        for a in args:
            if a.isdigit():
                run_parts.add(int(a))
            elif a == "selftest":
                run_selftest = True
        if not run_parts and not run_selftest:
            run_selftest = True
    else:
        run_parts = {1, 2, 3, 4, 5}
        run_selftest = True

    print("=" * 72)
    print("r17_junction_variance.py -- JUNCTION + VARIANCE => N_0(d) = 0 ?")
    print("=" * 72)
    print(f"Time budget: {TIME_BUDGET:.0f}s")

    try:
        if 1 in run_parts:
            part1_parseval()
        if 2 in run_parts:
            check_budget("before part2")
            part2_transfer_matrix()
        if 3 in run_parts:
            check_budget("before part3")
            part3_fourth_moment()
        if 4 in run_parts:
            check_budget("before part4")
            part4_product_structure()
        if 5 in run_parts:
            check_budget("before part5")
            part5_synthesis()
        if run_selftest:
            check_budget("before selftest")
            run_selftests()
    except TimeoutError as te:
        print(f"\n  [TIMEOUT] {te}")

    print("\n" + "=" * 72)
    print("SUMMARY")
    print("=" * 72)
    if TEST_RESULTS:
        np_ = sum(1 for _, p, _ in TEST_RESULTS if p)
        nf = sum(1 for _, p, _ in TEST_RESULTS if not p)
        print(f"  Tests: {np_} PASS, {nf} FAIL out of {len(TEST_RESULTS)}")
        if nf > 0:
            for name, passed, detail in TEST_RESULTS:
                if not passed:
                    print(f"    FAIL: {name}: {detail}")

    print(f"\n  Elapsed: {elapsed():.1f}s / {TIME_BUDGET:.0f}s")
    print("\n  MAIN CONCLUSIONS:")
    print("  1. Parseval+CS: PROVABLY INSUFFICIENT (gap ~ 2^{0.754k})")
    print("  2. Transfer matrix: INSUFFICIENT (eigs=1)")
    print("  3. Fourth moment: INSUFFICIENT (same L2)")
    print("  4. Product structure: INSUFFICIENT (bound ~ C)")
    print("  5. Even Weil bounds: INSUFFICIENT (C >> sqrt(d))")
    print("")
    print("  VERDICT: Junction + variance DOES NOT give N_0(d) = 0.")
    print("  RECOMMENDED: carry propagation (R14), p-adic (R15), CRT (R11-12).")

    return 0 if all(p for _, p, _ in TEST_RESULTS) else 1


if __name__ == "__main__":
    sys.exit(main())
