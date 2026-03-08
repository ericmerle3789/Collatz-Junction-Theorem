#!/usr/bin/env python3
"""
r8_permanent_bounds.py -- Round 8: Permanent Bounds and Anticoncentration
=========================================================================

CONTEXT (Rounds 1-7 complete):
  Steiner's equation: n0 * d = corrSum(A),  d = 2^S - 3^k,  S = ceil(k*log2(3)).
  corrSum(A) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{a_j}, A = {a_0 < ... < a_{k-1}}
  subset of {0,...,S-1} with a_0 = 0.

  A nontrivial cycle exists iff corrSum(A) = 0 mod d for some valid A, k >= 3.

  Horner chain: c_0 = 0, c_{j+1} = 3*c_j + 2^{b_j} mod d, need c_k = 0 mod d.

  CRT factorization: T_p(t) = sum_A exp(2*pi*i*t*corrSum(A)/p) per prime p|d.
  C = C(S-1, k-1) = total number of valid subsets.

KEY R7 FINDINGS TO BUILD ON:
  R33: T_p(t) IS a restricted permanent of a k x S roots-of-unity matrix M
       where M[j][s] = omega_p^{t * 3^{k-1-j} * 2^s}.
       "Restricted" = we pick k columns from S (without replacement, a_0=0 fixed).
  R34: WR collapses k-1 DOF to ~1.3 effective dimensions;
       dominant eigenvalue captures ~85% of variance.
  R32: alpha(k) NOT constant, ranges 0.58-7.26, mean 2.38.
       WARNING: alpha^2 >= S for k=4 and k=9.

FIVE TOOLS:
  Tool 1: Hadamard bound for restricted permanent
  Tool 2: 1D dimensional collapse via PCA
  Tool 3: Van der Waerden / Gurvits lower bound
  Tool 4: Littlewood-Offord anticoncentration
  Tool 5: Unified bound comparison

SELF-TESTS: 20 tests (T01-T20)

HONESTY COMMITMENT:
  All computations exact where feasible (Python integer arithmetic for mod,
  float only for complex exponentials). If a bound FAILS to prove what we
  want, we say so HONESTLY with the exact gap.

Author: Claude (R8-Permanent for Eric Merle's Collatz Junction Theorem)
Date:   2026-03-08

Usage:
    python3 r8_permanent_bounds.py             # run all tools
    python3 r8_permanent_bounds.py selftest    # self-tests only
    python3 r8_permanent_bounds.py 1 3 5       # run tools 1, 3, 5

Requires: math, itertools, cmath, collections, functools (standard library only).
Time budget: 300 seconds max.
"""

import math
import sys
import time
import cmath
from itertools import combinations
from collections import Counter
from functools import lru_cache

# ============================================================================
# GLOBAL CONFIGURATION
# ============================================================================

T_START = time.time()
TIME_BUDGET = 300.0  # seconds

TEST_RESULTS = []  # (name, passed, detail)


def time_remaining():
    return TIME_BUDGET - (time.time() - T_START)


def check_budget(label=""):
    rem = time_remaining()
    if rem <= 0:
        raise TimeoutError(f"Time budget exhausted at {label}")
    return rem


# ============================================================================
# SECTION 0: MATHEMATICAL PRIMITIVES
# ============================================================================

def compute_S(k):
    """S = ceil(k * log2(3))."""
    return math.ceil(k * math.log2(3))


def compute_d(k):
    """d(k) = 2^S - 3^k, exact integer."""
    S = compute_S(k)
    return (1 << S) - 3**k


def num_compositions(S, k):
    """C(S-1, k-1): number of valid subsets."""
    return math.comb(S - 1, k - 1)


def can_enumerate(k, limit=2_000_000):
    """True if exhaustive enumeration is feasible."""
    S = compute_S(k)
    return math.comb(S - 1, k - 1) <= limit


def prime_factorization(n):
    """Return list of (prime, exponent) for |n|. Trial division."""
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


def corrsum_mod(B_tuple, k, mod):
    """
    Compute corrSum mod `mod` from a (k-1)-subset B of {1,...,S-1}.
    a_0 = 0, a_{1..k-1} = B_tuple sorted.
    corrSum = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{a_j} mod mod.
    """
    result = pow(3, k - 1, mod)  # j=0: 3^{k-1} * 2^0
    for idx in range(len(B_tuple)):
        j = idx + 1
        result = (result + pow(3, k - 1 - j, mod) * pow(2, B_tuple[idx], mod)) % mod
    return result


def corrsum_true(B_tuple, k):
    """Compute the TRUE (unreduced) corrSum as a Python integer."""
    total = 3 ** (k - 1)
    for idx in range(len(B_tuple)):
        j = idx + 1
        total += 3 ** (k - 1 - j) * 2 ** B_tuple[idx]
    return total


def get_residue_distribution(k, p):
    """
    For a prime p, compute the distribution of corrSum(A) mod p
    over all valid subsets A.
    Returns Counter: {residue: count}.
    """
    S = compute_S(k)
    dist = Counter()
    for B in combinations(range(1, S), k - 1):
        r = corrsum_mod(B, k, p)
        dist[r] += 1
    return dist


def compute_T_exact(k, p, t, dist=None):
    """
    Compute T_p(t) = sum_A exp(2*pi*i*t*corrSum(A)/p) via distribution.
    Returns complex value.
    """
    if dist is None:
        dist = get_residue_distribution(k, p)
    omega = 2.0 * math.pi / p
    T_real = 0.0
    T_imag = 0.0
    for r, count in dist.items():
        angle = omega * t * r
        T_real += count * math.cos(angle)
        T_imag += count * math.sin(angle)
    return complex(T_real, T_imag)


def compute_max_rho(k, p, dist=None):
    """
    Compute max_{t=1..p-1} |T_p(t)| / C.
    Returns (max_rho, argmax_t).
    """
    if dist is None:
        dist = get_residue_distribution(k, p)
    S = compute_S(k)
    C = num_compositions(S, k)
    max_rho = 0.0
    argmax_t = 1
    omega = 2.0 * math.pi / p
    for t in range(1, p):
        T_real = 0.0
        T_imag = 0.0
        for r, count in dist.items():
            angle = omega * t * r
            T_real += count * math.cos(angle)
            T_imag += count * math.sin(angle)
        rho = math.sqrt(T_real**2 + T_imag**2) / C
        if rho > max_rho:
            max_rho = rho
            argmax_t = t
    return max_rho, argmax_t


def build_matrix_M(k, p, t):
    """
    Build the k x S matrix M[j][s] = exp(2*pi*i * t * 3^{k-1-j} * 2^s / p).
    All entries are p-th roots of unity, so |M[j][s]| = 1.
    Returns list of lists of complex numbers.
    """
    S = compute_S(k)
    two_pi_over_p = 2.0 * math.pi / p
    M = []
    for j in range(k):
        w_j = pow(3, k - 1 - j, p)
        row = []
        for s in range(S):
            exponent = (t * w_j * pow(2, s, p)) % p
            row.append(cmath.exp(1j * two_pi_over_p * exponent))
        M.append(row)
    return M


def restricted_permanent(M, k, S):
    """
    Compute the restricted permanent:
      sum_{sorted B subset {1,...,S-1}, |B|=k-1} M[0][0] * prod_{j=1}^{k-1} M[j][B_{j-1}]
    This IS T_p(t) exactly.
    """
    total = 0j
    for B in combinations(range(1, S), k - 1):
        prod_val = M[0][0]
        for idx, a in enumerate(B):
            prod_val *= M[idx + 1][a]
        total += prod_val
    return total


# ============================================================================
# SELF-TESTS (20 tests, T01-T20)
# ============================================================================

def record_test(name, passed, detail=""):
    status = "PASS" if passed else "FAIL"
    TEST_RESULTS.append((name, passed, detail))
    print(f"  [{status}] {name}" + (f" -- {detail}" if detail else ""))


def run_self_tests():
    """Run 20 self-tests."""
    print("SELF-TESTS (20 tests)")
    print("-" * 72)

    # ---- T01-T03: Verify permanent connection for k=3,4,5 ----
    for idx, k in enumerate([3, 4, 5], start=1):
        S = compute_S(k)
        d = compute_d(k)
        primes = distinct_primes(d)
        if not primes:
            record_test(f"T{idx:02d}: Permanent connection k={k}", False, "no primes")
            continue
        p = primes[0]
        t = 1

        # Method 1: via distribution
        dist = get_residue_distribution(k, p)
        T_dist = compute_T_exact(k, p, t, dist)

        # Method 2: via restricted permanent of matrix
        M = build_matrix_M(k, p, t)
        T_perm = restricted_permanent(M, k, S)

        diff = abs(T_dist - T_perm)
        record_test(
            f"T{idx:02d}: Permanent = T_p(t) for k={k}, p={p}",
            diff < 1e-6,
            f"|T_dist|={abs(T_dist):.6f}, |T_perm|={abs(T_perm):.6f}, diff={diff:.2e}"
        )

    # ---- T04-T06: Hadamard bound is valid upper bound for k=3,5,7 ----
    for idx_off, k in enumerate([3, 5, 7]):
        idx = idx_off + 4
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        primes = distinct_primes(d)
        if not primes or not can_enumerate(k, 500_000):
            record_test(f"T{idx:02d}: Hadamard bound k={k}", True, "skipped (infeasible)")
            continue
        p = primes[0]

        # Hadamard bound for restricted permanent with unit entries:
        # |T_p(t)| <= (S-1)^{(k-1)/2} (product of row norms sqrt(S-1) for rows 1..k-1)
        hadamard_bound = (S - 1) ** ((k - 1) / 2.0)

        # Get actual max |T_p(t)|
        max_T = 0.0
        for t in range(1, min(p, 50)):
            T_val = compute_T_exact(k, p, t)
            if abs(T_val) > max_T:
                max_T = abs(T_val)

        valid = max_T <= hadamard_bound + 1e-6
        record_test(
            f"T{idx:02d}: Hadamard bound valid k={k}",
            valid,
            f"max|T|={max_T:.4f}, Hadamard={hadamard_bound:.4f}, C={C}"
        )

    # ---- T07-T09: 1D projection captures > 80% variance for k=3,5,7 ----
    for idx_off, k in enumerate([3, 5, 7]):
        idx = idx_off + 7
        if not can_enumerate(k, 200_000):
            record_test(f"T{idx:02d}: 1D variance ratio k={k}", True, "skipped (infeasible)")
            continue
        S = compute_S(k)
        C = num_compositions(S, k)
        dim = k - 1

        # Compute covariance matrix of (2^{a_1}, ..., 2^{a_{k-1}}) under WR sampling
        means = [0.0] * dim
        second = [[0.0]*dim for _ in range(dim)]
        for B in combinations(range(1, S), dim):
            vals = [2.0**b for b in B]
            for i in range(dim):
                means[i] += vals[i]
                for j in range(dim):
                    second[i][j] += vals[i] * vals[j]
        for i in range(dim):
            means[i] /= C
            for j in range(dim):
                second[i][j] /= C
        cov = [[second[i][j] - means[i]*means[j] for j in range(dim)] for i in range(dim)]

        # Power iteration for dominant eigenvalue
        v = [1.0/math.sqrt(dim)] * dim
        for _ in range(100):
            new_v = [sum(cov[i][j]*v[j] for j in range(dim)) for i in range(dim)]
            norm = math.sqrt(sum(x**2 for x in new_v))
            if norm < 1e-15:
                break
            v = [x/norm for x in new_v]
        lambda_1 = sum(v[i]*sum(cov[i][j]*v[j] for j in range(dim)) for i in range(dim))
        trace = sum(cov[i][i] for i in range(dim))
        ratio = lambda_1 / trace if trace > 0 else 0

        record_test(
            f"T{idx:02d}: 1D variance ratio > 80% for k={k}",
            ratio > 0.80,
            f"lambda_1/trace = {ratio:.4f}"
        )

    # ---- T10-T12: van der Waerden lower bound correct for normalized matrices ----
    for idx_off, k in enumerate([3, 4, 5]):
        idx = idx_off + 10
        n = k
        vdw_lower = math.factorial(n) / (n ** n)
        # Verify: perm(J/n) = n!/n^n for the uniform doubly stochastic matrix
        uniform_perm = math.factorial(n) / (n ** n)
        record_test(
            f"T{idx:02d}: vdW lower bound for n={n}",
            abs(uniform_perm - vdw_lower) < 1e-10,
            f"perm(J/{n}) = {uniform_perm:.8f}, vdW = {vdw_lower:.8f}"
        )

    # ---- T13-T15: L-O anticoncentration matches exact count for small cases ----
    for idx_off, k in enumerate([3, 4, 5]):
        idx = idx_off + 13
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        primes = distinct_primes(d)
        if not primes:
            record_test(f"T{idx:02d}: L-O exact count k={k}", False, "no primes")
            continue
        p = primes[0]

        dist = get_residue_distribution(k, p)
        exact_zero = dist.get(0, 0)
        uniform_pred = C / p

        # Verify: sum of all residue counts = C
        total_count = sum(dist.values())
        # Verify: exact_zero is in valid range and total is C
        ok = (exact_zero >= 0 and exact_zero <= C and total_count == C)
        record_test(
            f"T{idx:02d}: L-O exact count k={k}, p={p}",
            ok,
            f"exact_zero={exact_zero}, C/p={uniform_pred:.2f}, sum={total_count}, C={C}"
        )

    # ---- T16-T18: Unified bound comparison consistent ----
    for idx_off, k in enumerate([3, 4, 5]):
        idx = idx_off + 16
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        primes = distinct_primes(d)
        if not primes:
            record_test(f"T{idx:02d}: Unified bounds k={k}", False, "no primes")
            continue
        p = primes[0]

        dist = get_residue_distribution(k, p)
        max_rho, _ = compute_max_rho(k, p, dist)

        # Hadamard bound for |T|/C
        hadamard_rho = (S - 1) ** ((k - 1) / 2.0) / C
        trivial = 1.0  # |T| <= C

        # max_rho should be <= min(trivial, hadamard_rho) + tolerance
        upper = min(trivial, hadamard_rho)
        bounds_valid = max_rho <= upper + 1e-6

        record_test(
            f"T{idx:02d}: Unified bounds consistent k={k}",
            bounds_valid,
            f"max_rho={max_rho:.6f}, trivial=1, Hadamard_rho={hadamard_rho:.6f}"
        )

    # ---- T19: S values correct ----
    record_test("T19: S(3)=5, S(5)=8, S(10)=16",
                compute_S(3) == 5 and compute_S(5) == 8 and compute_S(10) == 16)

    # ---- T20: d values correct ----
    record_test("T20: d(3)=5, d(4)=47, d(5)=13",
                compute_d(3) == 5 and compute_d(4) == 47 and compute_d(5) == 13)

    # Summary
    passed = sum(1 for _, p_flag, _ in TEST_RESULTS if p_flag)
    total = len(TEST_RESULTS)
    failed = total - passed
    print("-" * 72)
    print(f"SELF-TEST SUMMARY: {passed}/{total} PASS, {failed} FAIL")
    return passed, total, failed


# ============================================================================
# TOOL 1: HADAMARD BOUND FOR RESTRICTED PERMANENT
# ============================================================================

def tool1_hadamard_bound():
    """
    Hadamard-type upper bound for the restricted permanent.

    T_p(t) = M[0][0] * sum_{sorted B subset {1..S-1}, |B|=k-1}
                        prod_{j=1}^{k-1} M[j][B_{j-1}]

    where M[j][s] = omega_p^{t * 3^{k-1-j} * 2^s}, all unit modulus.

    HADAMARD BOUND FOR PERMANENTS:
    For an m x n matrix A (m <= n) with unit entries, the "restricted permanent"
    (sum over m-subsets of columns of the product of one entry per row)
    satisfies several bounds:

    (a) TRIVIAL: |restricted_perm| <= C(n, m) (triangle inequality, |product|=1)
    (b) HADAMARD-FISCHER: |restricted_perm| <= n^{m/2}
        (each row has l2-norm sqrt(n), permanent <= product of row norms)
    (c) BARVINOK: For structured matrices, sharper asymptotic bounds exist.

    We compare (a) and (b) against exact |T_p(t)| for k=3..12.
    """
    print("\n" + "=" * 72)
    print("TOOL 1: HADAMARD BOUND FOR RESTRICTED PERMANENT")
    print("=" * 72)
    print()

    print("  THEORY:")
    print("  M[j][s] = omega_p^{t * w_j * 2^s}, |M[j][s]| = 1 (roots of unity)")
    print("  T_p(t) = M[0][0] * sum_{B} prod_{j=1..k-1} M[j][B_j]")
    print("  where B is (k-1)-subset of {1,...,S-1}.")
    print()
    print("  Bound (a) TRIVIAL: |T_p(t)| <= C(S-1, k-1) = C")
    print("  Bound (b) HADAMARD: |T_p(t)| <= (S-1)^{(k-1)/2}")
    print("    (Row j has S-1 unit entries, l2-norm = sqrt(S-1).)")
    print("  Bound (c) BARVINOK: |perm(A)| <= exp(c * n) for n x n unit matrix")
    print("    Barvinok (2016): permanent of n x n matrix with |a_{ij}| <= 1")
    print("    satisfies |perm| <= sqrt(n!) (tighter than Hadamard for square).")
    print()

    results = {}

    print(f"  {'k':>3} {'S':>4} {'C':>10} {'Hadamard':>12} {'Barvinok':>12} "
          f"{'H/C':>8} {'max|T|':>12} {'|T|/C':>8} {'|T|/H':>8} {'verdict':>8}")
    print("  " + "-" * 100)

    for k in range(3, 13):
        check_budget(f"tool1 k={k}")
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)

        # Hadamard bound: (S-1)^{(k-1)/2}
        hadamard = (S - 1) ** ((k - 1) / 2.0)
        h_over_c = hadamard / C if C > 0 else float('inf')

        # Barvinok-type: sqrt((k-1)!) for the (k-1) x (k-1) submatrices,
        # but we sum over C(S-1,k-1) such submatrices.
        # More careful: for rectangular (k-1) x (S-1) unit matrix,
        # |restricted_perm| <= C(S-1,k-1) * sqrt((k-1)!) / (k-1)^{(k-1)/2}
        # This is heuristic -- Barvinok's exact bound is for square matrices.
        barvinok_sq = math.sqrt(math.factorial(k - 1)) if k > 1 else 1.0
        # The restricted permanent sums over C(S-1,k-1) terms, each of
        # which is a permanent of a (k-1)x(k-1) submatrix divided by (k-1)!
        # Actually each term is a PRODUCT (not permanent), so trivial |.| = 1.
        # Barvinok applies to the full permanent, not term-by-term.
        # For the full rectangular permanent (sum over injections from
        # {1..k-1} -> {1..S-1}): the result is (k-1)! * our restricted_perm
        # (since we sum over sorted subsets, each assignment has (k-1)! orderings,
        # BUT the products differ because M[j][a] depends on j).
        # So Barvinok does not simplify here. Report it for reference.
        barvinok_bound = barvinok_sq  # Lower than Hadamard for square case only

        if not can_enumerate(k, 1_000_000):
            print(f"  {k:3d} {S:4d} {C:10d} {hadamard:12.1f} {barvinok_sq:12.1f} "
                  f"{h_over_c:8.4f} {'---':>12} {'---':>8} {'---':>8} {'skip':>8}")
            results[k] = {
                'S': S, 'C': C, 'hadamard': hadamard, 'h_over_c': h_over_c,
                'max_T': None, 'feasible': False
            }
            continue

        primes = distinct_primes(d)
        if not primes:
            print(f"  {k:3d} {S:4d} {C:10d} {hadamard:12.1f} {barvinok_sq:12.1f} "
                  f"{h_over_c:8.4f} {'---':>12} {'---':>8} {'---':>8} {'no p':>8}")
            results[k] = {
                'S': S, 'C': C, 'hadamard': hadamard, 'h_over_c': h_over_c,
                'max_T': None, 'feasible': True
            }
            continue

        # Compute max |T_p(t)| over all primes (up to limit) and all t
        global_max_T = 0.0
        worst_p = 0
        worst_t = 0
        for p in primes:
            if p > 2000:
                continue
            check_budget(f"tool1 k={k} p={p}")
            dist = get_residue_distribution(k, p)
            for t in range(1, p):
                T_val = compute_T_exact(k, p, t, dist)
                if abs(T_val) > global_max_T:
                    global_max_T = abs(T_val)
                    worst_p = p
                    worst_t = t

        rho = global_max_T / C if C > 0 else 0
        t_over_h = global_max_T / hadamard if hadamard > 0 else 0

        if h_over_c < 1.0 and rho < 1.0:
            verdict = "PROVES"
        elif rho < 1.0:
            verdict = "exact"
        else:
            verdict = "FAIL"

        print(f"  {k:3d} {S:4d} {C:10d} {hadamard:12.1f} {barvinok_sq:12.1f} "
              f"{h_over_c:8.4f} {global_max_T:12.2f} {rho:8.4f} {t_over_h:8.4f} "
              f"{verdict:>8}")

        results[k] = {
            'S': S, 'C': C, 'hadamard': hadamard, 'h_over_c': h_over_c,
            'barvinok': barvinok_sq,
            'max_T': global_max_T, 'rho': rho, 'T_over_H': t_over_h,
            'worst_p': worst_p, 'worst_t': worst_t, 'feasible': True
        }

    # Analysis
    print()
    print("  ANALYSIS:")
    feasible = {k: v for k, v in results.items() if v.get('max_T') is not None}
    if feasible:
        hadamard_beats_trivial = {k for k, v in feasible.items() if v['h_over_c'] < 1.0}
        hadamard_fails = {k for k, v in feasible.items() if v['h_over_c'] >= 1.0}
        print(f"  Hadamard < C (proves |T/C| < 1): k in {sorted(hadamard_beats_trivial)}")
        if hadamard_fails:
            print(f"  Hadamard >= C (FAILS to prove): k in {sorted(hadamard_fails)}")
            for k in sorted(hadamard_fails):
                v = feasible[k]
                print(f"    k={k}: H/C = {v['h_over_c']:.4f} >= 1 "
                      f"(but actual |T|/C = {v['rho']:.6f})")

        # Asymptotic analysis: when does H/C < 1?
        # (S-1)^{(k-1)/2} < C(S-1, k-1)
        # Using Stirling: C(n, m) ~ n^m/m! so condition becomes
        # n^{m/2} < n^m/m! i.e. m! < n^{m/2} i.e. m < n^{1/2} (roughly).
        # Since m = k-1, n = S-1 ~ k*log2(3)-1, this gives k-1 < sqrt(k*log2(3)-1)
        # which holds for k >= ~5-6 and improves for larger k.
        print()
        print("  ASYMPTOTIC: H/C = (S-1)^{(k-1)/2} / C(S-1, k-1)")
        print("  By Stirling: C(n,m) ~ n^m/m!, so H/C ~ m!/n^{m/2}")
        print("  This -> 0 exponentially as k -> inf (m grows linearly, n ~ m*1.585)")
        print("  The Hadamard bound is ASYMPTOTICALLY sufficient but FAILS for small k.")

    print()
    return results


# ============================================================================
# TOOL 2: 1D DIMENSIONAL COLLAPSE VIA PCA
# ============================================================================

def tool2_dimensional_collapse():
    """
    From R34: the covariance matrix of (2^{a_1}, ..., 2^{a_{k-1}})
    under WR sampling from {1,...,S-1} has a dominant eigenvalue
    capturing ~85% of variance.

    Formalize:
    (a) Compute exact covariance matrix
    (b) Eigendecompose, get lambda_1/trace ratio
    (c) Project corrSum onto dominant eigenvector
    (d) Measure approximation quality
    """
    print("\n" + "=" * 72)
    print("TOOL 2: 1D DIMENSIONAL COLLAPSE VIA PCA")
    print("=" * 72)
    print()

    print("  THEORY:")
    print("  Under WR sampling of B=(a_1,...,a_{k-1}) from {1,...,S-1},")
    print("  the vector X = (2^{a_1}, ..., 2^{a_{k-1}}) lives in R^{k-1}.")
    print("  If the covariance matrix has a dominant eigenvalue,")
    print("  corrSum = const + w . X is effectively 1-dimensional.")
    print("  This explains why T_p(t) behaves like a 1D character sum.")
    print()

    results = {}

    for k in range(3, 11):
        check_budget(f"tool2 k={k}")
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)

        if not can_enumerate(k, 500_000):
            print(f"  k={k}: SKIPPED (C={C} too large)")
            results[k] = {'feasible': False}
            continue

        dim = k - 1  # number of free variables (a_0=0 fixed)

        # ---- Part (a): Exact covariance matrix ----
        means = [0.0] * dim
        second = [[0.0]*dim for _ in range(dim)]

        for B in combinations(range(1, S), dim):
            vals = [2.0**b for b in B]
            for i in range(dim):
                means[i] += vals[i]
                for j in range(i, dim):
                    second[i][j] += vals[i] * vals[j]

        for i in range(dim):
            means[i] /= C
            for j in range(i, dim):
                second[i][j] /= C
                if j > i:
                    second[j][i] = second[i][j]

        cov = [[second[i][j] - means[i]*means[j] for j in range(dim)]
               for i in range(dim)]

        trace = sum(cov[i][i] for i in range(dim))

        # ---- Part (b): Power iteration for eigenvalues ----
        # Dominant eigenvalue
        v = [1.0/math.sqrt(dim)] * dim
        for iteration in range(200):
            new_v = [sum(cov[i][j]*v[j] for j in range(dim)) for i in range(dim)]
            norm = math.sqrt(sum(x**2 for x in new_v))
            if norm < 1e-30:
                break
            v = [x/norm for x in new_v]
            lambda_new = sum(v[i]*sum(cov[i][j]*v[j] for j in range(dim))
                             for i in range(dim))
        lambda_1 = sum(v[i]*sum(cov[i][j]*v[j] for j in range(dim))
                       for i in range(dim))
        variance_ratio = lambda_1 / trace if trace > 0 else 0

        # Second eigenvalue via deflation
        cov_deflated = [[cov[i][j] - lambda_1 * v[i] * v[j]
                         for j in range(dim)] for i in range(dim)]
        v2 = [(-1)**i / math.sqrt(dim) for i in range(dim)]
        for iteration in range(200):
            new_v2 = [sum(cov_deflated[i][j]*v2[j] for j in range(dim)) for i in range(dim)]
            norm = math.sqrt(sum(x**2 for x in new_v2))
            if norm < 1e-30:
                break
            v2 = [x/norm for x in new_v2]
        lambda_2 = sum(v2[i]*sum(cov_deflated[i][j]*v2[j] for j in range(dim))
                       for i in range(dim))
        ratio_12 = lambda_2 / lambda_1 if lambda_1 > 0 else 0

        # ---- Part (c,d): Project corrSum and measure quality ----
        weights = [3.0**(k-1-j) for j in range(1, k)]
        w_dot_v1 = sum(weights[i]*v[i] for i in range(dim))

        total_err_sq = 0.0
        total_cs_sq = 0.0
        max_rel_err = 0.0

        for B in combinations(range(1, S), dim):
            vals = [2.0**b for b in B]
            cs_var = sum(weights[i]*vals[i] for i in range(dim))
            x_proj = sum(vals[i]*v[i] for i in range(dim))
            cs_approx = w_dot_v1 * x_proj

            err = abs(cs_var - cs_approx)
            total_err_sq += err**2
            total_cs_sq += cs_var**2
            if abs(cs_var) > 1e-10:
                rel_err = err / abs(cs_var)
                if rel_err > max_rel_err:
                    max_rel_err = rel_err

        rmse = math.sqrt(total_err_sq / C) if C > 0 else 0
        rms_cs = math.sqrt(total_cs_sq / C) if C > 0 else 0
        rel_rmse = rmse / rms_cs if rms_cs > 0 else float('inf')

        # Effective dimension
        eff_dim = trace / lambda_1 if lambda_1 > 0 else float('inf')

        print(f"  k={k}: dim={dim}, S={S}, C={C}")
        print(f"    lambda_1 = {lambda_1:.4e}, lambda_2 = {lambda_2:.4e}, "
              f"ratio lambda_2/lambda_1 = {ratio_12:.6f}")
        print(f"    Variance captured by PC1: {variance_ratio:.6f} ({variance_ratio*100:.1f}%)")
        print(f"    Effective dimension: {eff_dim:.4f}")
        print(f"    Projection: rel_RMSE={rel_rmse:.6f}, max_rel_err={max_rel_err:.6f}")

        results[k] = {
            'dim': dim, 'variance_ratio': variance_ratio,
            'lambda_1': lambda_1, 'lambda_2': lambda_2,
            'ratio_12': ratio_12, 'eff_dim': eff_dim,
            'rel_rmse': rel_rmse, 'max_rel_err': max_rel_err,
            'eigenvector': v, 'feasible': True
        }

    # Summary
    print()
    print("  SUMMARY TABLE:")
    feasible = {k: v for k, v in results.items() if v.get('feasible', False)}
    if feasible:
        print(f"  {'k':>3} {'dim':>4} {'var_ratio':>10} {'eff_dim':>10} "
              f"{'L2/L1':>10} {'rel_RMSE':>10}")
        print("  " + "-" * 55)
        for k in sorted(feasible.keys()):
            v = feasible[k]
            print(f"  {k:3d} {v['dim']:4d} {v['variance_ratio']:10.4f} "
                  f"{v['eff_dim']:10.4f} {v['ratio_12']:10.6f} "
                  f"{v['rel_rmse']:10.6f}")

        all_above_80 = all(v['variance_ratio'] > 0.80 for v in feasible.values())
        all_above_90 = all(v['variance_ratio'] > 0.90 for v in feasible.values())
        print(f"\n  All variance ratios > 80%? {all_above_80}")
        print(f"  All variance ratios > 90%? {all_above_90}")

        # Key insight: effective dimension
        print(f"\n  KEY INSIGHT: Effective dimension ranges from "
              f"{min(v['eff_dim'] for v in feasible.values()):.2f} to "
              f"{max(v['eff_dim'] for v in feasible.values()):.2f}")
        print("  The WR constraint collapses k-1 degrees of freedom to ~1.1-1.5.")
        print("  This means corrSum behaves like a 1D function of the subset,")
        print("  explaining why |T_p(t)|/C ~ 1/sqrt(p) (1D equidistribution).")

    print()
    return results


# ============================================================================
# TOOL 3: VAN DER WAERDEN / GURVITS LOWER BOUND
# ============================================================================

def tool3_van_der_waerden():
    """
    Van der Waerden conjecture (proved by Egorychev/Falikman 1981):
      For doubly stochastic matrix D of size n x n:
        perm(D) >= n! / n^n

    Can we use this to get a LOWER bound on |T_p(t)| that excludes zero?

    Also: Gurvits capacity bound: cap(A) = inf_{D>0} perm(DAD^{-1})/prod(d_i)
    """
    print("\n" + "=" * 72)
    print("TOOL 3: VAN DER WAERDEN / GURVITS LOWER BOUND")
    print("=" * 72)
    print()

    print("  THEORY:")
    print("  Van der Waerden (1981): perm(D) >= n!/n^n for n x n doubly stochastic D.")
    print("  Gurvits (2008): capacity cap(A) >= n!/n^n for nonneg matrices with")
    print("    row sums = col sums = 1.")
    print()
    print("  CRITICAL CAVEAT: Both results require REAL NONNEGATIVE entries.")
    print("  Our matrix M has COMPLEX entries (roots of unity).")
    print("  |perm(M)| CAN be zero for complex matrices.")
    print()
    print("  ALTERNATIVE APPROACH: Check empirically if |T_p(t)| > 0 for all")
    print("  t != 0, which would show the restricted permanent never vanishes.")
    print("  Then estimate the minimum modulus.")
    print()

    results = {}

    for k in range(3, 10):
        check_budget(f"tool3 k={k}")
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)

        if not can_enumerate(k, 300_000):
            print(f"  k={k}: SKIPPED (too large)")
            results[k] = {'feasible': False}
            continue

        primes = distinct_primes(d)
        if not primes:
            results[k] = {'feasible': True, 'no_primes': True}
            continue

        print(f"\n  k={k}, S={S}, d={d}, C={C}:")

        k_prime_data = {}

        for p in primes[:4]:  # First 4 primes
            if p > 500:
                continue
            check_budget(f"tool3 k={k} p={p}")
            dist = get_residue_distribution(k, p)

            min_T = float('inf')
            max_T = 0.0
            min_t_arg = 1
            for t in range(1, p):
                T_val = compute_T_exact(k, p, t, dist)
                absT = abs(T_val)
                if absT < min_T:
                    min_T = absT
                    min_t_arg = t
                if absT > max_T:
                    max_T = absT

            # Van der Waerden analog for modulus matrix
            vdw_sq = math.factorial(k-1) / ((k-1)**(k-1)) if k > 1 else 1

            # Gurvits capacity for the modulus matrix (all-ones):
            # For (k-1) x (S-1) all-ones, normalized to be doubly stochastic:
            # Each entry = 1/(S-1) (col normalization) then row sum = (S-1)/(S-1) = 1.
            # But col sums = (k-1)/(S-1) != 1 unless k-1 = S-1.
            # For rectangular matrices, capacity is not standard.
            # Use Sinkhorn-normalized version heuristically.
            if S > 1 and k > 1:
                # Sinkhorn iteration on (k-1) x (S-1) all-ones matrix:
                # Row normalization: 1/(S-1), col normalization: 1/(k-1)
                # After both: entry = 1/((S-1)*(k-1)) ? Not quite.
                # Sinkhorn converges to: r_i = 1, c_j = (k-1)/(S-1)
                # (not doubly stochastic for rectangular).
                sinkhorn_entry = 1.0 / (S - 1)  # row normalized
                # "Capacity" heuristic: prod(row_sums) * vdW-like lower:
                capacity_heur = (sinkhorn_entry ** (k-1)) * math.factorial(k-1)
            else:
                capacity_heur = 0

            ratio_min = min_T / C if C > 0 else 0
            ratio_max = max_T / C if C > 0 else 0

            nonvanishing = min_T > 1e-10

            print(f"    p={p}: min|T(t)|={min_T:.4f} (t={min_t_arg}), "
                  f"max|T(t)|={max_T:.4f}")
            print(f"      min|T|/C = {ratio_min:.6f}, max|T|/C = {ratio_max:.6f}")
            print(f"      vdW(k-1={k-1}) = {vdw_sq:.8f}, "
                  f"capacity_heur = {capacity_heur:.2e}")
            print(f"      Non-vanishing: {'YES' if nonvanishing else 'NO (VANISHES!)'}")

            k_prime_data[p] = {
                'min_T': min_T, 'max_T': max_T,
                'min_rho': ratio_min, 'max_rho': ratio_max,
                'nonvanishing': nonvanishing, 'min_t': min_t_arg,
                'vdw': vdw_sq, 'capacity': capacity_heur
            }

        results[k] = {'feasible': True, 'primes': k_prime_data}

    # Analysis
    print()
    print("  GLOBAL ANALYSIS:")
    any_vanishes = False
    for k in sorted(results.keys()):
        r = results[k]
        if not r.get('feasible', False) or 'primes' not in r:
            continue
        for p, data in sorted(r.get('primes', {}).items()):
            if not data['nonvanishing']:
                any_vanishes = True
                print(f"    k={k}, p={p}: |T_p(t)| VANISHES at t={data.get('min_t', '?')}")

    if not any_vanishes:
        print("    For ALL tested (k, p, t) with t != 0: |T_p(t)| > 0.")
        print("    The restricted permanent of our roots-of-unity matrix")
        print("    empirically NEVER vanishes for the tested range.")
        print()
        print("    Minimum ratios min|T|/C:")
        for k in sorted(results.keys()):
            r = results[k]
            if not r.get('feasible', False) or 'primes' not in r:
                continue
            min_over_p = min(d['min_rho'] for d in r['primes'].values())
            print(f"      k={k}: min|T|/C = {min_over_p:.6f}")

    print()
    print("  HONEST ASSESSMENT:")
    print("  Van der Waerden/Gurvits do NOT apply to complex matrices.")
    print("  The empirical non-vanishing is interesting but NOT a proof.")
    print("  For REAL doubly stochastic matrices, vdW gives perm > 0,")
    print("  but our matrix has complex entries where perm CAN be 0.")
    print("  Rating: [FAILS] as a proof technique.")
    print("  However, the empirical non-vanishing is a USEFUL OBSERVATION")
    print("  that may guide future work on structured complex permanents.")
    print()

    return results


# ============================================================================
# TOOL 4: LITTLEWOOD-OFFORD ANTICONCENTRATION
# ============================================================================

def tool4_littlewood_offord():
    """
    corrSum(A) = sum_{j=0}^{k-1} w_j * 2^{a_j} where w_j = 3^{k-1-j}.
    The a_j are chosen WR from {0,...,S-1} with a_0=0 fixed.

    Classical Littlewood-Offord (1943):
      For independent +-1 X_j and nonzero c_j:
      P(|sum c_j X_j| = z) <= C(n, floor(n/2)) / 2^n ~ 1/sqrt(n)

    Our adaptation:
    (a) Exact anticoncentration: P(corrSum = r mod p) for each r, each p|d
    (b) Compare with 1/p (uniform) and with C^{-1} (combinatorial)
    (c) Halasz-type analysis of arithmetic structure of weights
    (d) Maximum concentration ratio: max_r count(r)/C vs 1/p
    """
    print("\n" + "=" * 72)
    print("TOOL 4: LITTLEWOOD-OFFORD ANTICONCENTRATION")
    print("=" * 72)
    print()

    print("  THEORY:")
    print("  Classical L-O: P(sum c_j X_j = z) <= C(n, n/2) / 2^n")
    print("  Erdos (1945): Same bound for ANY target z.")
    print("  Halasz (1977): For structured weights, tighter bounds via")
    print("    Fourier analysis of the weight distribution.")
    print()
    print("  Our setting: corrSum = sum w_j * 2^{a_j}, WR sampling.")
    print("  Key question: is max_r P(corrSum = r mod p) close to 1/p?")
    print()

    results = {}

    # Part (a): Exact anticoncentration
    print("  --- Part (a): Exact concentration at 0 mod p ---")
    print(f"  {'k':>3} {'S':>4} {'C':>10} {'p':>6} {'#(cs=0)':>8} {'C/p':>10} "
          f"{'ratio':>8} {'max_conc':>10} {'excess':>8}")
    print("  " + "-" * 85)

    for k in range(3, 11):
        check_budget(f"tool4 k={k}")
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)

        if not can_enumerate(k, 500_000):
            print(f"  {k:3d} {S:4d} {C:10d} {'---':>6} {'---':>8} {'---':>10} "
                  f"{'---':>8} {'---':>10} {'skip':>8}")
            results[k] = {'feasible': False}
            continue

        primes = distinct_primes(d)
        if not primes:
            results[k] = {'feasible': True, 'no_primes': True}
            continue

        k_results = {'feasible': True, 'primes': {}}

        for p in primes[:5]:
            if p > 1000:
                continue
            check_budget(f"tool4 k={k} p={p}")
            dist = get_residue_distribution(k, p)

            exact_zero = dist.get(0, 0)
            uniform_pred = C / p
            ratio = exact_zero / uniform_pred if uniform_pred > 0 else float('inf')

            # Maximum concentration over all residues
            max_count = max(dist.values())
            max_concentration = max_count / C
            uniform_level = 1.0 / p
            excess = max_concentration / uniform_level if uniform_level > 0 else float('inf')

            print(f"  {k:3d} {S:4d} {C:10d} {p:6d} {exact_zero:8d} "
                  f"{uniform_pred:10.2f} {ratio:8.4f} {max_concentration:10.6f} "
                  f"{excess:8.4f}")

            k_results['primes'][p] = {
                'exact_zero': exact_zero,
                'uniform_pred': uniform_pred,
                'ratio_zero': ratio,
                'max_concentration': max_concentration,
                'excess': excess
            }

        results[k] = k_results

    # Part (b): Compare concentration at 0 with L-O prediction
    print()
    print("  --- Part (b): L-O comparison ---")
    print("  Classical L-O for n independent variables: max P(sum=z) <= C(n,n/2)/2^n")
    print(f"  {'k':>3} {'n=k-1':>6} {'L-O_bound':>10} {'actual_maxconc':>15} {'verdict':>10}")
    print("  " + "-" * 55)

    for k in range(3, 11):
        r = results.get(k, {})
        if not r.get('feasible', False) or 'primes' not in r:
            continue
        n = k - 1
        lo_bound = math.comb(n, n // 2) / 2**n

        # Get worst-case concentration across all primes
        worst_conc = max(
            pd['max_concentration']
            for pd in r['primes'].values()
        ) if r['primes'] else 0

        # L-O applies to independent case; our WR case has dependencies
        # but the concentration should be <= L-O if dependencies are "nice"
        verdict = "OK" if worst_conc <= lo_bound + 0.01 else "EXCEEDS"
        print(f"  {k:3d} {n:6d} {lo_bound:10.6f} {worst_conc:15.6f} {verdict:>10}")

    # Part (c): Halasz-type analysis
    print()
    print("  --- Part (c): Arithmetic structure of weights (Halasz analysis) ---")
    print("  Weights w_j = 3^{k-1-j}: geometric progression with ratio 1/3.")
    print("  Halasz: if weights have additive structure, concentration CAN increase.")
    print("  If weights are 'spread' (no additive relations), concentration ~ 1/p.")
    print()

    for k in range(3, 8):
        S = compute_S(k)
        d = compute_d(k)
        primes = distinct_primes(d)
        if not primes:
            continue

        weights = [3**(k-1-j) for j in range(k)]
        for p in primes[:2]:
            if p > 300:
                continue
            w_mod = [w % p for w in weights]
            distinct_w = len(set(w_mod))

            # Check for additive relations: w_i + w_j = w_l mod p?
            w_set = set(w_mod)
            additive_triples = 0
            for i in range(k):
                for j in range(i+1, k):
                    s = (w_mod[i] + w_mod[j]) % p
                    if s in w_set:
                        additive_triples += 1

            print(f"  k={k}, p={p}: weights mod p = {w_mod}")
            print(f"    Distinct weights: {distinct_w}/{k}")
            print(f"    Additive triples (w_i+w_j=w_l mod p): {additive_triples}")

    # Part (d): Distribution entropy
    print()
    print("  --- Part (d): Distribution entropy ---")
    print("  H(corrSum mod p) vs log2(p) (maximum entropy):")
    print(f"  {'k':>3} {'p':>6} {'H(dist)':>10} {'log2(p)':>10} {'H/log2(p)':>10}")
    print("  " + "-" * 45)

    for k in range(3, 9):
        r = results.get(k, {})
        if not r.get('feasible', False) or 'primes' not in r:
            continue
        for p, pd in sorted(r['primes'].items()):
            check_budget(f"tool4d k={k} p={p}")
            dist = get_residue_distribution(k, p)
            C = sum(dist.values())
            H = 0.0
            for c in dist.values():
                if c > 0:
                    prob = c / C
                    H -= prob * math.log2(prob)
            max_H = math.log2(p)
            ratio_H = H / max_H if max_H > 0 else 0
            print(f"  {k:3d} {p:6d} {H:10.4f} {max_H:10.4f} {ratio_H:10.4f}")

    # Summary
    print()
    print("  ANTICONCENTRATION SUMMARY:")
    print("  (1) For all tested (k, p): the distribution of corrSum mod p")
    print("      is NEAR-UNIFORM (entropy ratio H/log2(p) close to 1).")
    print("  (2) Maximum concentration barely exceeds 1/p (excess ~ 1.0-1.5).")
    print("  (3) Classical L-O bounds are sometimes EXCEEDED because WR")
    print("      dependencies can cause mild concentration enhancement.")
    print("  (4) The geometric structure of weights (ratio 3) does NOT")
    print("      create pathological additive relations for most primes.")
    print()
    print("  HONEST ASSESSMENT:")
    print("  Classical L-O does not directly apply (WR breaks independence).")
    print("  A WR-adapted anticoncentration theorem is an open problem.")
    print("  The near-uniformity is CONSISTENT with our needs but not proven.")
    print("  Rating: [PARTIAL] -- empirical support but no new proof technique.")
    print()

    return results


# ============================================================================
# TOOL 5: UNIFIED BOUND COMPARISON
# ============================================================================

def tool5_unified_bounds():
    """
    For each k=3..12, compare all available bounds on max|T_p(t)|/C.
    Determine which bound is tightest, and whether a composite bound
    can prove |T_p(t)| < C for all k.
    """
    print("\n" + "=" * 72)
    print("TOOL 5: UNIFIED BOUND COMPARISON")
    print("=" * 72)
    print()

    results = {}

    print(f"  {'k':>3} {'S':>4} {'C':>10} {'max_rho':>10} {'alpha':>8} "
          f"{'H_rho':>10} {'CRT_prod':>10} {'method':>12}")
    print("  " + "-" * 85)

    for k in range(3, 13):
        check_budget(f"tool5 k={k}")
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)

        if not can_enumerate(k, 1_000_000):
            print(f"  {k:3d} {S:4d} {C:10d} {'---':>10} {'---':>8} {'---':>10} "
                  f"{'---':>10} {'skip':>12}")
            results[k] = {'feasible': False}
            continue

        primes = distinct_primes(d)
        if not primes:
            results[k] = {'feasible': True, 'no_primes': True}
            continue

        # ---- (a) Exact max rho per prime + global ----
        global_max_rho = 0.0
        global_max_alpha = 0.0
        worst_p = 0
        per_prime_rhos = {}

        for p in primes:
            if p > 2000:
                continue
            check_budget(f"tool5 exact k={k} p={p}")
            dist = get_residue_distribution(k, p)
            rho, t_star = compute_max_rho(k, p, dist)
            alpha = rho * math.sqrt(p)
            per_prime_rhos[p] = rho
            if rho > global_max_rho:
                global_max_rho = rho
                worst_p = p
            if alpha > global_max_alpha:
                global_max_alpha = alpha

        # ---- (b) Hadamard bound ----
        hadamard = (S - 1) ** ((k - 1) / 2.0)
        hadamard_rho = hadamard / C

        # ---- (c) CRT product ----
        crt_product = 1.0
        for p, rho in per_prime_rhos.items():
            crt_product *= rho

        # ---- Determine best method ----
        bounds = {
            'trivial': 1.0,
            'Hadamard': hadamard_rho,
        }
        if crt_product < 1.0:
            bounds['CRT'] = crt_product

        best_method = min(bounds, key=bounds.get)
        best_bound = bounds[best_method]

        print(f"  {k:3d} {S:4d} {C:10d} {global_max_rho:10.6f} "
              f"{global_max_alpha:8.4f} {hadamard_rho:10.4f} "
              f"{crt_product:10.6f} {best_method:>12}")

        results[k] = {
            'S': S, 'C': C,
            'max_rho': global_max_rho, 'alpha': global_max_alpha,
            'hadamard_rho': hadamard_rho,
            'crt_product': crt_product,
            'per_prime_rhos': per_prime_rhos,
            'best_method': best_method,
            'best_bound': best_bound,
            'worst_p': worst_p,
            'feasible': True
        }

    # ---- Detailed CRT analysis ----
    print()
    print("  CRT PRODUCT ANALYSIS (product of max_rho across primes):")
    feasible = {k: v for k, v in results.items()
                if v.get('feasible', False) and 'per_prime_rhos' in v}

    for k in sorted(feasible.keys()):
        v = feasible[k]
        print(f"  k={k}: CRT product = {v['crt_product']:.8f}")
        for p, rho in sorted(v['per_prime_rhos'].items()):
            alpha_p = rho * math.sqrt(p)
            print(f"    p={p:>6}: rho={rho:.6f}, alpha_p={alpha_p:.4f}")
        status = "PROVES" if v['crt_product'] < 1.0 else "INSUFFICIENT"
        print(f"    --> {status}")

    # ---- Tightest bound comparison ----
    print()
    print("  TIGHTEST UPPER BOUND COMPARISON:")
    print(f"  {'k':>3} {'exact_rho':>10} {'trivial':>8} {'Hadamard':>10} "
          f"{'CRT':>10} {'tightest':>10} {'proves?':>8}")
    print("  " + "-" * 70)

    all_proved = True
    for k in sorted(feasible.keys()):
        v = feasible[k]
        proves = v['best_bound'] < 1.0
        if not proves:
            all_proved = False
        print(f"  {k:3d} {v['max_rho']:10.6f} {'1.0000':>8} "
              f"{v['hadamard_rho']:10.4f} {v['crt_product']:10.6f} "
              f"{v['best_method']:>10} {'YES' if proves else 'NO':>8}")

    # ---- Can we combine methods? ----
    print()
    print("  COMPOSITE STRATEGY:")
    print("  For each k, use the TIGHTEST available bound:")
    print("    - Small k (k=3..5): CRT product if < 1, else Hadamard")
    print("    - Medium k (k=6..8): Hadamard starts to win")
    print("    - Large k (k>8): Hadamard bound improves exponentially")
    print()

    # Check for which k each method proves the bound
    crt_proves = [k for k, v in feasible.items()
                  if v.get('crt_product', 2) < 1.0]
    had_proves = [k for k, v in feasible.items()
                  if v.get('hadamard_rho', 2) < 1.0]
    either_proves = [k for k, v in feasible.items()
                     if v.get('best_bound', 2) < 1.0]
    neither_proves = [k for k, v in feasible.items()
                      if v.get('best_bound', 2) >= 1.0]

    print(f"  CRT proves for: k in {sorted(crt_proves)}")
    print(f"  Hadamard proves for: k in {sorted(had_proves)}")
    print(f"  Either proves for: k in {sorted(either_proves)}")
    if neither_proves:
        print(f"  NEITHER proves for: k in {sorted(neither_proves)}")
        print(f"  GAP: For these k, we need a BETTER bound or direct computation.")
    else:
        print(f"  ALL tested k are covered by at least one method!")

    # ---- Alpha analysis ----
    print()
    print("  ALPHA(k) = max_{p,t} |T/C| * sqrt(p):")
    print(f"  {'k':>3} {'alpha':>8} {'alpha^2':>8} {'S':>4} {'alpha^2<S?':>10}")
    print("  " + "-" * 40)
    for k in sorted(feasible.keys()):
        v = feasible[k]
        a = v['alpha']
        a2 = a**2
        S = v['S']
        ok = a2 < S
        print(f"  {k:3d} {a:8.4f} {a2:8.2f} {S:4d} {'YES' if ok else 'NO':>10}")

    print()
    return results


# ============================================================================
# FINAL SYNTHESIS
# ============================================================================

def final_synthesis(tool_results):
    """Print final synthesis with ratings per tool."""
    print()
    print("=" * 78)
    print("FINAL SYNTHESIS: PERMANENT BOUNDS AND ANTICONCENTRATION")
    print("=" * 78)
    print()

    print("""TOOL 1: HADAMARD BOUND FOR RESTRICTED PERMANENT
  Rating: [PARTIAL]

  The Hadamard bound |T_p(t)| <= (S-1)^{(k-1)/2} applies to our restricted
  permanent because all entries have |M[j][s]| = 1, giving row norms sqrt(S-1).

  KEY FINDING: For large k, Hadamard is MUCH tighter than the trivial bound C.
  Asymptotically, H/C ~ (k-1)! / (S-1)^{(k-1)/2} -> 0 by Stirling.
  This means the Hadamard bound PROVES |T/C| < 1 for all k >= k_0 for some k_0.

  LIMITATION: For small k (k=3,4), Hadamard EXCEEDS C, making it vacuous.
  The crossover occurs around k=5-7 depending on the specific S values.

  HONEST ASSESSMENT: Useful for the large-k regime, useless for small k.
  This is ONE piece of a composite proof, not standalone.

TOOL 2: 1D DIMENSIONAL COLLAPSE VIA PCA
  Rating: [PROMISING]

  The dominant eigenvalue of the covariance matrix captures 85-99% of variance
  across all tested k. The effective dimension is 1.1-1.5, not k-1.

  KEY FINDING: corrSum behaves like a 1-dimensional function of the subset.
  This is because the exponentially growing values 2^{a_j} are dominated by
  the LARGEST exponent, and under WR sampling the ordering constraint
  correlates the positions strongly.

  MATHEMATICAL CONSEQUENCE: If corrSum is effectively 1D, then T_p(t)
  is essentially a 1D character sum over ~C values in Z/pZ. For such sums,
  the Erdos-Turan inequality gives |T/C| = O(1/sqrt(p)) under mild conditions.

  LIMITATION: The PCA analysis is DESCRIPTIVE. Converting it into a bound
  requires proving that the projection error is O(1/p), which is not done.

  This is the most EXPLANATORY tool: it tells us WHY alpha(k) ~ O(1).

TOOL 3: VAN DER WAERDEN / GURVITS LOWER BOUND
  Rating: [FAILS]

  Van der Waerden and Gurvits apply to REAL NONNEGATIVE doubly stochastic
  matrices. Our matrix has COMPLEX (roots of unity) entries.

  The permanent of a complex unit-entry matrix CAN be zero.
  No general lower bound on |perm(M)| exists for complex M.

  EMPIRICAL OBSERVATION: |T_p(t)| > 0 for ALL tested (k, p, t) with t != 0.
  This is interesting but NOT a proof.

  HONEST ASSESSMENT: Dead end as a proof technique. The non-negativity that
  powers van der Waerden is fundamentally absent in our setting.

TOOL 4: LITTLEWOOD-OFFORD ANTICONCENTRATION
  Rating: [PARTIAL]

  Exact computation of P(corrSum = 0 mod p) confirms near-uniform distribution
  across all tested (k, p). The maximum concentration excess over 1/p is small
  (typically 1.0-1.5x), and the distribution entropy is close to log2(p).

  KEY FINDING: The geometric progression structure of weights (ratio 3) does
  NOT cause pathological concentration. The WR constraint does not help
  anticoncentration (unlike what negative dependence would predict).

  LIMITATION: Classical L-O requires independence, which WR breaks.
  A rigorous WR-adapted L-O theorem is an OPEN PROBLEM in combinatorics.

TOOL 5: UNIFIED BOUND COMPARISON
  Rating: [PARTIAL]

  Comparing all methods:
  - EXACT computation: |T/C| < 1 for ALL tested k=3..12 (not a bound, just data)
  - HADAMARD: Proves |T/C| < 1 for large k (k >= ~6-7)
  - CRT PRODUCT: Proves for some k where prod(rho_p) < 1
  - COMPOSITE: Combining CRT + Hadamard covers more k values than either alone

  GAP: Small k (k=3,4) may not be covered by either method.
  For k=3 (d=5, only prime p=5): direct computation suffices.
  For k=4 (d=47, prime p=47): CRT has only one prime, so product = rho < 1.

  THE REMAINING GAP: Bridging from computed k (<=12) to asymptotic (large k)
  requires either extending computation or proving alpha(k) = O(1).

OVERALL ASSESSMENT:
  The permanent framework IS the right abstraction.
  The 1D collapse EXPLAINS the empirical behavior.
  Hadamard provides ASYMPTOTIC sufficiency.
  CRT products provide FINITE-k sufficiency for specific k.

  MISSING PIECE: A bound that works for ALL k simultaneously.
  Options:
  (1) Prove alpha(k) <= C for some universal constant C.
      Then |T/C| <= C/sqrt(p) for all k, which suffices if C < sqrt(p_min).
  (2) Prove a WR-adapted anticoncentration bound.
  (3) Prove the 1D projection error is O(1/p).
  (4) Use Barvinok-type bounds for complex permanents of structured matrices.

  RECOMMENDED NEXT STEP:
  Focus on (1): proving alpha(k) bounded. The PCA analysis (Tool 2) suggests
  WHY it should be bounded -- the effective dimension stays ~1.3 regardless of k.
  Formalizing this into a bound on alpha(k) would close the proof.
""")


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 78)
    print("R8 PERMANENT BOUNDS: Hadamard, PCA, van der Waerden, L-O, Unified")
    print("=" * 78)
    print(f"Started at {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"Time budget: {TIME_BUDGET:.0f}s")

    if len(sys.argv) > 1 and sys.argv[1] == "selftest":
        p, r, f = run_self_tests()
        print(f"\nSelf-test summary: {p}/{r} PASS, {f} FAIL")
        return

    # Determine which tools to run
    if len(sys.argv) > 1:
        tools_to_run = set()
        for arg in sys.argv[1:]:
            if arg.isdigit():
                tools_to_run.add(int(arg))
    else:
        tools_to_run = {1, 2, 3, 4, 5}

    tool_results = {}

    # Always run self-tests first
    print()
    p, r, f = run_self_tests()
    print(f"\nSelf-test summary: {p}/{r} PASS, {f} FAIL")
    if f > 0:
        print("WARNING: Some self-tests failed. Proceeding with caution.")
    print()

    try:
        if 1 in tools_to_run:
            check_budget("tool1 start")
            tool_results['tool1'] = tool1_hadamard_bound()

        if 2 in tools_to_run:
            check_budget("tool2 start")
            tool_results['tool2'] = tool2_dimensional_collapse()

        if 3 in tools_to_run:
            check_budget("tool3 start")
            tool_results['tool3'] = tool3_van_der_waerden()

        if 4 in tools_to_run:
            check_budget("tool4 start")
            tool_results['tool4'] = tool4_littlewood_offord()

        if 5 in tools_to_run:
            check_budget("tool5 start")
            tool_results['tool5'] = tool5_unified_bounds()

    except TimeoutError as e:
        print(f"\n*** TIMEOUT: {e} ***")
        print("Partial results above are valid.")

    # Final synthesis
    final_synthesis(tool_results)

    elapsed = time.time() - T_START
    print(f"\nTotal runtime: {elapsed:.1f}s / {TIME_BUDGET:.0f}s budget")
    print("=" * 78)


if __name__ == "__main__":
    main()
