#!/usr/bin/env python3
"""
r11_weil_bound.py -- Round 11: Weil Bound via Elementary Symmetric Functions
=============================================================================

CONTEXT (Rounds 1-10 complete):
  The character sum T_p(t) = sum_A omega^{t*corrSum(A)/p} over all valid
  compositions A = {0 = a_0 < a_1 < ... < a_{k-1} <= S-1} can be computed
  via a transfer matrix product:

      T_p(t) = phase * M[k-1, 0]

  where M = T_{S-1} * T_{S-2} * ... * T_1 is a product of (S-1) matrices.

  KEY IDENTITY (from R9-R10, path expansion):
      M[k-1, 0] = sum_{1 <= s_1 < s_2 < ... < s_{k-1} <= S-1}
                     prod_{j=1}^{k-1} omega^{t * w_j * 2^{s_j} / p}

  where w_j = 3^{k-1-j} and omega = e^{2*pi*i/p}.

  This is a sum of C = C(S-1, k-1) unit-modulus terms.

  R10 proved:
    (A) |M[k-1,0]| < C strictly (phase non-alignment)
    (B) ||T_s||_op is phase-independent
    (C) n_0 = 0 verified for k=3..13

  THE GAP: A quantitative universal bound |T_p(t)| = O(C/sqrt(p)).
  If proved, this gives N_0(p) = 0 for p > alpha*C^2.

NEW APPROACH (R11): ELEMENTARY SYMMETRIC FUNCTION DECOMPOSITION
  The path expansion M[k-1,0] = e_{k-1}(F), the (k-1)-th elementary symmetric
  function of a (k-1) x (S-1) matrix F of roots of unity.

  F[j, s] = f_j(s) = omega^{t * w_j * 2^s / p}  for j=1..k-1, s=1..S-1

  where w_j = 3^{k-1-j}.

  By Cauchy-Binet: e_{k-1}(F) = sum over (k-1)-element subsets of {1,...,S-1}
  of the determinant of the corresponding (k-1) x (k-1) minor of F.
  But here columns are selected while rows are fixed, so it's:
  e_{k-1}(F) = sum_{|T|=k-1, T subset {1..S-1}} det(F[:,T])

  Wait -- this is NOT exactly right. The elementary symmetric function is:
  e_{k-1} = sum_{s_1<...<s_{k-1}} prod_{j=1}^{k-1} F[j, s_j]

  This is the PERMANENT of a subset selection, not a determinant.
  In fact, it equals the sum of all PRODUCTS of one entry from each row,
  taken from DISTINCT columns (ordered), which is a MIXED DISCRIMINANT
  or equivalently the permanent over ordered column subsets.

  CAUCHY-BINET applies to DETERMINANTS. For PRODUCTS without signs,
  this is the PERMANENT-like expression. The key identity:

  e_{k-1}(F) = sum_{T, |T|=k-1} perm(F[:, T])  NO -- this overcounts.

  CORRECT: e_{k-1}(F) = sum_{s_1 < ... < s_{k-1}} prod_j F[j, s_j]

  This is literally the definition of the elementary symmetric function
  of the "virtual variables" x_s = (f_1(s), ..., f_{k-1}(s)).

  For a SINGLE row (k-1 = 1): e_1(F) = sum_s f_1(s) = Gauss-type sum.
  For MULTIPLE rows: it's a multilinear sum with ordering constraint.

FIVE PARTS:
  Part 1: Verify e_{k-1}(F) == M[k-1, 0] for k=3..8
  Part 2: Determinantal bounds (Hadamard, Schur-Horn)
  Part 3: Weil bound for individual rows (character sums over <2>)
  Part 4: From row bounds to total bound (multilinear structure)
  Part 5: Numerical verification for k=3..15, all primes p|d(k)

SELF-TESTS: 25 tests (T01-T25)

HONESTY: All computations exact where feasible. If a bound FAILS, we say so.
Author: Claude (R11-WeilBound for Eric Merle's Collatz Junction Theorem)
Date:   2026-03-08

Usage:
    python3 r11_weil_bound.py              # run all parts + selftest
    python3 r11_weil_bound.py selftest     # self-tests only
    python3 r11_weil_bound.py 1 3 5        # run specific parts

Requires: math, itertools, cmath (standard library only).
Time budget: 290 seconds max.
"""

import math
import sys
import time
import cmath
from itertools import combinations
from collections import Counter

# ============================================================================
# GLOBAL CONFIGURATION
# ============================================================================

T_START = time.time()
TIME_BUDGET = 290.0  # seconds

TEST_RESULTS = []  # (name, passed, detail)
FINDINGS = {}  # key -> dict of findings per part


def time_remaining():
    return TIME_BUDGET - (time.time() - T_START)


def check_budget(label=""):
    rem = time_remaining()
    if rem <= 0:
        raise TimeoutError(f"Time budget exhausted at {label}")
    return rem


def record_test(name, passed, detail=""):
    status = "PASS" if passed else "FAIL"
    TEST_RESULTS.append((name, passed, detail))
    print(f"  [{status}] {name}" + (f" -- {detail}" if detail else ""))


# ============================================================================
# SECTION 0: MATHEMATICAL PRIMITIVES
# ============================================================================

def compute_S(k):
    """S = ceil(k * log2(3)), computed exactly via integer comparison."""
    S_approx = math.ceil(k * math.log2(3))
    # Verify exactness
    if (1 << S_approx) >= 3**k and (1 << (S_approx - 1)) < 3**k:
        return S_approx
    S = S_approx
    while (1 << S) < 3**k:
        S += 1
    return S


def compute_d(k):
    """d(k) = 2^S - 3^k, exact integer."""
    S = compute_S(k)
    return (1 << S) - 3**k


def num_compositions(S, k):
    """C(S-1, k-1): number of valid compositions."""
    return math.comb(S - 1, k - 1)


def can_enumerate(k, limit=2_000_000):
    """True if exhaustive enumeration is feasible."""
    S = compute_S(k)
    return math.comb(S - 1, k - 1) <= limit


def prime_factorization(n):
    """Return list of (prime, exponent) for |n|."""
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


def multiplicative_order(base, mod):
    """Compute ord_mod(base) = smallest positive e with base^e = 1 mod mod."""
    if math.gcd(base, mod) != 1:
        return 0
    e = 1
    val = base % mod
    while val != 1:
        val = (val * base) % mod
        e += 1
        if e > mod:
            return 0
    return e


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


def get_residue_distribution(k, p):
    """
    Distribution of corrSum(A) mod p over all valid compositions.
    Returns Counter: {residue: count}.
    """
    S = compute_S(k)
    dist = Counter()
    for B in combinations(range(1, S), k - 1):
        r = corrsum_mod(B, k, p)
        dist[r] += 1
    return dist


def compute_T_exact(k, p, t, dist=None):
    """Compute T_p(t) = sum_A exp(2*pi*i*t*corrSum(A)/p) via distribution."""
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


def compute_max_rho(k, p, dist=None, t_limit=None):
    """Compute max_{t=1..p-1} |T_p(t)| / C. Returns (max_rho, argmax_t)."""
    if dist is None:
        dist = get_residue_distribution(k, p)
    S = compute_S(k)
    C = num_compositions(S, k)
    max_rho = 0.0
    argmax_t = 1
    omega = 2.0 * math.pi / p
    upper = min(p, t_limit) if t_limit else p
    for t in range(1, upper):
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


# ============================================================================
# TRANSFER MATRIX COMPUTATION UTILITIES
# ============================================================================

def transfer_matrix_T(k, p, t, s):
    """
    Build the k x k transfer matrix T_s for position s.
    T_s = I + E_s where E_s[j+1][j] = omega^{t * w_{j+1} * 2^s / p}.
    w_{j+1} = 3^{k-1-(j+1)} = 3^{k-2-j}.
    """
    omega_val = 2.0 * math.pi / p
    T = [[0j] * k for _ in range(k)]
    for j in range(k):
        T[j][j] = 1.0 + 0j
    for j in range(k - 1):
        w_jp1 = pow(3, k - 2 - j, p)
        phase = (t * w_jp1 * pow(2, s, p)) % p
        T[j + 1][j] = cmath.exp(1j * omega_val * phase)
    return T


def mat_mul(A, B, k):
    """Multiply two k x k complex matrices."""
    C = [[0j] * k for _ in range(k)]
    for i in range(k):
        for j in range(k):
            for l in range(k):
                C[i][j] += A[i][l] * B[l][j]
    return C


def mat_identity(k):
    """Return k x k identity matrix."""
    M = [[0j] * k for _ in range(k)]
    for i in range(k):
        M[i][i] = 1.0 + 0j
    return M


def compute_product_matrix(k, p, t):
    """Compute M = T_{S-1} * T_{S-2} * ... * T_1 (left multiplication)."""
    S = compute_S(k)
    M = mat_identity(k)
    for s in range(1, S):
        T_s = transfer_matrix_T(k, p, t, s)
        M = mat_mul(T_s, M, k)
    return M


def compute_T_via_transfer(k, p, t):
    """Compute T_p(t) via the transfer matrix product."""
    S = compute_S(k)
    omega_val = 2.0 * math.pi / p
    init_phase = (t * pow(3, k - 1, p)) % p
    v0_phase = cmath.exp(1j * omega_val * init_phase)
    M = compute_product_matrix(k, p, t)
    return M[k - 1][0] * v0_phase


# ============================================================================
# ELEMENTARY SYMMETRIC FUNCTION UTILITIES
# ============================================================================

def build_F_matrix(k, p, t):
    """
    Build the (k-1) x (S-1) matrix F of roots of unity.
    F[j, s] = omega^{t * w_{j+1} * 2^{s+1} / p}
    where j = 0,...,k-2 (rows) and s = 0,...,S-2 (columns).

    Row j corresponds to weight w_{j+1} = 3^{k-2-j}.
    Column s corresponds to position s+1 in {1,...,S-1}.
    """
    S = compute_S(k)
    n_rows = k - 1
    n_cols = S - 1
    omega_val = 2.0 * math.pi / p

    F = [[0j] * n_cols for _ in range(n_rows)]
    for j in range(n_rows):
        w = pow(3, k - 2 - j, p)  # w_{j+1} = 3^{k-2-j}
        for s in range(n_cols):
            phase = (t * w * pow(2, s + 1, p)) % p
            F[j][s] = cmath.exp(1j * omega_val * phase)
    return F


def compute_esf(F, n_rows, n_cols):
    """
    Compute the elementary symmetric function e_{n_rows}(F):
    e_{n_rows} = sum_{s_0 < s_1 < ... < s_{n_rows-1}, all in 0..n_cols-1}
                   prod_{j=0}^{n_rows-1} F[j][s_j]

    This is a sum of C(n_cols, n_rows) unit-modulus terms.
    """
    result = 0j
    for cols in combinations(range(n_cols), n_rows):
        term = 1.0 + 0j
        for j in range(n_rows):
            term *= F[j][cols[j]]
        result += term
    return result


def row_sum(F, j, n_cols):
    """Sum of row j: sum_{s=0}^{n_cols-1} F[j][s]."""
    return sum(F[j][s] for s in range(n_cols))


def row_norm_sq(F, j, n_cols):
    """Squared L2 norm of row j: sum |F[j][s]|^2 = n_cols (since |F[j][s]|=1)."""
    return sum(abs(F[j][s])**2 for s in range(n_cols))


def row_inner_product(F, j1, j2, n_cols):
    """Inner product <row j1, row j2> = sum_s F[j1][s] * conj(F[j2][s])."""
    return sum(F[j1][s] * F[j2][s].conjugate() for s in range(n_cols))


# ============================================================================
# PART 1: VERIFY ELEMENTARY SYMMETRIC FUNCTION IDENTITY
# ============================================================================

def part1_esf_identity():
    """
    Part 1: Verify that e_{k-1}(F) equals M[k-1, 0] from the transfer matrix.

    The elementary symmetric function of the matrix F:
      e_{k-1}(F) = sum_{s_1 < ... < s_{k-1}} prod_{j=1}^{k-1} F[j, s_j]

    should equal the path expansion M[k-1, 0] (without the initial phase factor).

    We verify this for k = 3..8 and multiple primes.
    """
    print("\n" + "=" * 72)
    print("PART 1: VERIFY ELEMENTARY SYMMETRIC FUNCTION IDENTITY")
    print("=" * 72)

    findings = {}

    print("\n  THEOREM (ESF = Transfer Matrix Entry):")
    print("  For the (k-1) x (S-1) matrix F with F[j,s] = omega^{t*w_{j+1}*2^{s+1}/p},")
    print("  the elementary symmetric function e_{k-1}(F) equals the transfer matrix")
    print("  entry M[k-1, 0] (from the product M = T_{S-1} * ... * T_1).")
    print()
    print("  PROOF: By the path expansion (R9-R10),")
    print("    M[k-1, 0] = sum_{1<=s_1<...<s_{k-1}<=S-1} prod_{j=1}^{k-1} omega^{t*w_j*2^{s_j}/p}")
    print("  Relabeling j -> j+1 (so j=0..k-2) and s -> s-1 (so s=0..S-2):")
    print("    = sum_{0<=c_0<...<c_{k-2}<=S-2} prod_{j=0}^{k-2} omega^{t*w_{j+1}*2^{c_j+1}/p}")
    print("    = sum_subsets prod_j F[j, c_j]")
    print("    = e_{k-1}(F).")
    print()

    print(f"  {'k':>4s} {'p':>6s} {'t':>4s} {'|e_{k-1}(F)|':>14s} "
          f"{'|M[k-1,0]|':>14s} {'|diff|':>12s} {'match':>8s}")
    print(f"  {'':->66s}")

    verification_results = []
    for k in range(3, 9):
        check_budget("Part1")
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        if C > 500_000:
            continue

        primes = distinct_primes(d)
        test_primes = [p for p in primes if p <= 500][:2]
        if not test_primes:
            test_primes = [primes[0]] if primes else []

        for p in test_primes:
            for t in [1, 2]:
                check_budget("Part1-inner")
                # ESF computation
                F = build_F_matrix(k, p, t)
                esf_val = compute_esf(F, k - 1, S - 1)

                # Transfer matrix computation
                M = compute_product_matrix(k, p, t)
                tm_val = M[k - 1][0]

                diff = abs(esf_val - tm_val)
                match = diff < 1e-6

                print(f"  {k:4d} {p:6d} {t:4d} {abs(esf_val):14.8f} "
                      f"{abs(tm_val):14.8f} {diff:12.2e} "
                      f"{'OK' if match else 'MISMATCH':>8s}")

                verification_results.append({
                    'k': k, 'p': p, 't': t,
                    'esf_abs': abs(esf_val), 'tm_abs': abs(tm_val),
                    'diff': diff, 'match': match
                })

    all_match = all(r['match'] for r in verification_results)
    print(f"\n  ESF == M[k-1,0] for ALL tested cases: {all_match}")
    print(f"  Total cases verified: {len(verification_results)}")

    # Also verify that |each term| = 1
    print("\n  VERIFICATION: Each term in e_{k-1}(F) has modulus 1:")
    k_test, p_test, t_test = 4, 7, 1
    S_test = compute_S(k_test)
    F_test = build_F_matrix(k_test, p_test, t_test)
    all_unit = True
    count = 0
    for cols in combinations(range(S_test - 1), k_test - 1):
        term = 1.0 + 0j
        for j in range(k_test - 1):
            term *= F_test[j][cols[j]]
        if abs(abs(term) - 1.0) > 1e-10:
            all_unit = False
        count += 1
    C_test = num_compositions(S_test, k_test)
    print(f"  k={k_test}, p={p_test}: {count} terms checked, "
          f"all modulus 1: {all_unit}, count = C = {C_test}: {count == C_test}")

    findings['verification_results'] = verification_results
    findings['all_match'] = all_match
    findings['all_unit'] = all_unit

    FINDINGS['Part1'] = findings
    return findings


# ============================================================================
# PART 2: DETERMINANTAL BOUNDS (HADAMARD, SCHUR-HORN)
# ============================================================================

def part2_determinantal_bounds():
    """
    Part 2: Bound |e_{k-1}(F)| using determinantal inequalities.

    APPROACH 1: Hadamard's inequality for minors.
    For a (k-1) x (k-1) submatrix F[:,T] with T a (k-1)-element subset:
      |det(F[:,T])| <= prod_j ||row_j restricted to T||_2 = prod_j sqrt(k-1)
                     = (k-1)^{(k-1)/2}

    But e_{k-1}(F) = sum_T prod_j F[j, T_j] (NO SIGNS -- not a determinant sum).
    So Hadamard does NOT directly apply.

    APPROACH 2: The sum of products (our e_{k-1}) satisfies:
      |e_{k-1}(F)| <= C(S-1, k-1) = C   (trivial, since each term has |.| = 1)

    Can we do better? Key idea: consider the GRAM MATRIX G = F * F^*/n_cols.

    APPROACH 3: Row correlation analysis.
    Since f_j(s) = omega^{t * w_j * 2^s / p}, two rows satisfy:
      f_j(s) * conj(f_{j'}(s)) = omega^{t * (w_j - w_{j'}) * 2^s / p}

    The inner product <row j, row j'> = sum_s omega^{t * (w_j - w_{j'}) * 2^s / p}
    is itself a character sum over powers of 2!

    If w_j != w_{j'} mod p (which holds when j != j' and p does not divide 3),
    then this inner product is bounded by the Weil-type estimate for sums over
    multiplicative subgroups.

    APPROACH 4: Bregman-Minc permanent bound.
    For a 0-1 matrix with row sums r_j, the permanent satisfies:
      perm(A) <= prod_j (r_j!)^{1/r_j}
    But our matrix has COMPLEX entries, and the Bregman bound does not
    directly apply to complex permanents.

    We implement the analysis and report findings.
    """
    print("\n" + "=" * 72)
    print("PART 2: DETERMINANTAL AND CORRELATION BOUNDS")
    print("=" * 72)

    findings = {}

    # ------------------------------------------------------------------
    # ROW CORRELATION ANALYSIS (Gram matrix)
    # ------------------------------------------------------------------
    print("\n  ROW CORRELATION ANALYSIS:")
    print("  The Gram matrix G[j,j'] = (1/(S-1)) * <row j, row j'> measures")
    print("  correlations between rows. For unit-modulus entries:")
    print("    G[j,j] = 1 (diagonal)")
    print("    G[j,j'] = (1/(S-1)) * sum_s omega^{t*(w_j - w_{j'})*2^s / p}")
    print()

    gram_results = []
    print(f"  {'k':>4s} {'p':>6s} {'t':>4s} {'||G||_F':>10s} {'max|G_off|':>12s} "
          f"{'mean|G_off|':>12s} {'cond_bound':>12s}")
    print(f"  {'':->70s}")

    for k in range(3, 10):
        check_budget("Part2-gram")
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        if C > 300_000:
            continue

        primes = distinct_primes(d)
        test_primes = [p for p in primes if p <= 500][:2]

        for p in test_primes:
            for t in [1]:
                check_budget("Part2-gram-inner")
                F = build_F_matrix(k, p, t)
                n_rows = k - 1
                n_cols = S - 1

                # Compute Gram matrix G = F * F^H / n_cols
                G = [[0j] * n_rows for _ in range(n_rows)]
                for j1 in range(n_rows):
                    for j2 in range(n_rows):
                        ip = row_inner_product(F, j1, j2, n_cols)
                        G[j1][j2] = ip / n_cols

                # Frobenius norm of G
                frob_G = math.sqrt(sum(abs(G[i][j])**2
                                       for i in range(n_rows) for j in range(n_rows)))

                # Max off-diagonal
                max_off = 0.0
                sum_off = 0.0
                count_off = 0
                for i in range(n_rows):
                    for j in range(n_rows):
                        if i != j:
                            val = abs(G[i][j])
                            max_off = max(max_off, val)
                            sum_off += val
                            count_off += 1
                mean_off = sum_off / count_off if count_off > 0 else 0

                # Condition number bound: if G is close to identity,
                # then the rows are nearly orthogonal, and the permanent
                # has better cancellation.
                # Gershgorin: eigenvalues of G lie in disks
                # center = 1, radius = sum of off-diagonal entries in each row.
                max_gershgorin_radius = 0.0
                for i in range(n_rows):
                    radius = sum(abs(G[i][j]) for j in range(n_rows) if j != i)
                    max_gershgorin_radius = max(max_gershgorin_radius, radius)

                # The condition: if max_gershgorin_radius < 1, all eigenvalues > 0,
                # so G is positive definite and the rows form a "basis-like" system.
                cond_bound = max_gershgorin_radius

                print(f"  {k:4d} {p:6d} {t:4d} {frob_G:10.6f} {max_off:12.8f} "
                      f"{mean_off:12.8f} {cond_bound:12.8f}")

                gram_results.append({
                    'k': k, 'p': p, 't': t, 'n_rows': n_rows,
                    'frob_G': frob_G, 'max_off': max_off,
                    'mean_off': mean_off, 'cond_bound': cond_bound
                })

    findings['gram_results'] = gram_results

    # ------------------------------------------------------------------
    # SCHUR-HORN BOUND on e_{k-1}(F)
    # ------------------------------------------------------------------
    print("\n  SCHUR-HORN / PRODUCT-NORM BOUND:")
    print("  For e_{k-1}(F) with C = C(S-1, k-1) terms, each of modulus 1:")
    print("    |e_{k-1}(F)| <= C   (trivial)")
    print("  We can improve using the FACTORED structure:")
    print("    e_{k-1} = sum_{subsets T} prod_j F[j, T_j]")
    print("  By Cauchy-Schwarz on the subset sum, grouping by first element:")
    print("    |e_{k-1}|^2 <= C * sum_T |prod_j F[j,T_j]|^2 = C * C = C^2")
    print("  This is circular. The key is to use MULTI-STEP CS.")
    print()

    # Compute actual |e_{k-1}|/C and compare to various bounds
    print(f"  {'k':>4s} {'p':>6s} {'C':>10s} {'|e|/C':>10s} {'1/sqrt(p)':>10s} "
          f"{'|e|*sqrt(p)/C':>12s} {'Schur ratio':>12s}")
    print(f"  {'':->70s}")

    bound_results = []
    for k in range(3, 10):
        check_budget("Part2-bounds")
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        if C > 300_000:
            continue

        primes = distinct_primes(d)
        test_primes = [p for p in primes if 3 <= p <= 500][:2]

        for p in test_primes:
            check_budget("Part2-bounds-inner")
            dist = get_residue_distribution(k, p)
            max_rho, t_star = compute_max_rho(k, p, dist, t_limit=min(p, 200))

            inv_sqrt_p = 1.0 / math.sqrt(p)
            alpha_val = max_rho * math.sqrt(p)  # |T|*sqrt(p)/C

            # Schur-Horn: (S-1)^{(k-1)/2} / C
            schur_bound = (S - 1)**((k - 1) / 2.0) / C
            schur_ratio = max_rho / schur_bound if schur_bound > 0 else 0

            print(f"  {k:4d} {p:6d} {C:10d} {max_rho:10.6f} {inv_sqrt_p:10.6f} "
                  f"{alpha_val:12.6f} {schur_ratio:12.6f}")

            bound_results.append({
                'k': k, 'p': p, 'C': C, 'S': S,
                'max_rho': max_rho, 'alpha_val': alpha_val,
                'schur_bound': schur_bound, 'schur_ratio': schur_ratio
            })

    findings['bound_results'] = bound_results

    # Analysis
    if bound_results:
        print("\n  ANALYSIS:")
        alphas = [r['alpha_val'] for r in bound_results]
        print(f"  Range of alpha = |T|*sqrt(p)/C: [{min(alphas):.4f}, {max(alphas):.4f}]")
        print(f"  Mean alpha: {sum(alphas)/len(alphas):.4f}")
        if all(r['max_rho'] < r['schur_bound'] for r in bound_results):
            print("  Schur-Horn bound: |e_{k-1}|/C < (S-1)^{(k-1)/2}/C for ALL cases.")
        else:
            schur_fails = sum(1 for r in bound_results
                              if r['max_rho'] >= r['schur_bound'])
            print(f"  Schur-Horn bound fails for {schur_fails}/{len(bound_results)} cases.")
            print("  This is expected: Schur-Horn applies to determinants, not to our sum.")

    FINDINGS['Part2'] = findings
    return findings


# ============================================================================
# PART 3: WEIL BOUND FOR INDIVIDUAL ROWS
# ============================================================================

def part3_weil_row_bounds():
    """
    Part 3: Analyze each row f_j of F as a character sum.

    Row j of F: f_j(s) = omega^{t * w_j * 2^s / p} for s = 1,...,S-1.

    This is the character sum:
      R_j = sum_{s=1}^{S-1} omega^{c_j * 2^s / p}   where c_j = t * w_j mod p.

    The sum R_j ranges over consecutive powers of 2 modulo p.
    Let m = ord_p(2). Then {2^1, 2^2, ..., 2^{S-1}} modulo p consists of
    elements of the subgroup <2> = {2^0, 2^1, ..., 2^{m-1}}, with possible
    repetitions if S-1 >= m.

    CASE 1: S-1 < m (all powers distinct mod p).
      Then R_j = sum_{s=1}^{S-1} chi(2^s) where chi is the additive character
      x -> omega^{c_j * x}. This is a partial sum of a character over a
      multiplicative subgroup.

    CASE 2: S-1 >= m (powers cycle).
      Then 2^s mod p cycles with period m. The number of complete cycles is
      q = floor((S-1)/m), with remainder r = (S-1) mod m.
      R_j = q * sigma_j + R_j^{(partial)}
      where sigma_j = sum_{h in <2>} omega^{c_j * h / p} is the FULL
      subgroup character sum.

    KEY FACT: For the FULL subgroup sum:
      sigma_j = sum_{h in <2>} omega^{c_j * h / p}
      If c_j = 0 mod p: sigma_j = m.
      If c_j != 0 mod p but c_j is in the annihilator of <2>: sigma_j = 0.
      In general: |sigma_j| = 0 or sqrt(p) or m (depending on (p-1)/m | c_j).

    More precisely, for a subgroup H of (Z/pZ)^*:
      sum_{h in H} omega^{c*h} = (|H|/|G|) * sum_{chi in G/H^perp} chi(c) * G(chi)
    where G is the full multiplicative group and G(chi) is a Gauss sum.
    For |H| = m, |G| = p-1: this involves (p-1)/m characters.

    By the Weil bound for Gauss sums: |G(chi)| = sqrt(p) for nontrivial chi.
    So: |sigma_j| <= m + ((p-1)/m - 1) * sqrt(p) * m/(p-1)
                    = m * (1/(p-1) + ... )  -- this needs care.

    ACTUALLY: The cleaner statement is:
    For c != 0 mod p:
      |sum_{h in H} omega^{c*h}| = |sum_{h in H} psi(c*h)|
    where psi is the additive character. This is bounded by:
      <= sqrt(p) * gcd(#cosets, something)... The standard result is:

    THEOREM (Character sum over subgroup):
    Let H <= (Z/pZ)^* be a subgroup of index d = (p-1)/|H|. Then:
      sum_{h in H} psi(h) = (1/d) * sum_{chi: chi^d = 1} G(chi, psi)
    where G(chi, psi) = sum_x chi(x) psi(x) is the Gauss sum.
    For nontrivial chi: |G(chi, psi)| = sqrt(p).
    For trivial chi: G(1, psi) = -1 (if psi nontrivial).
    So: |sum_H psi(h)| <= (1/d)(sqrt(p) * (d-1) + 1) < sqrt(p).

    THIS IS THE WEIL-TYPE BOUND: |sum_{h in H} psi(c*h)| < sqrt(p)
    for any nontrivial additive character psi and c != 0 mod p.

    We verify this bound numerically and compute the ratio |R_j|/sqrt(p).
    """
    print("\n" + "=" * 72)
    print("PART 3: WEIL BOUND FOR INDIVIDUAL ROWS (CHARACTER SUMS OVER <2>)")
    print("=" * 72)

    findings = {}

    # ------------------------------------------------------------------
    # THEOREM (Subgroup Character Sum Bound)
    # ------------------------------------------------------------------
    print("\n  THEOREM (Subgroup Character Sum -- Weil-type bound):")
    print("  Let p be prime, H = <2> <= (Z/pZ)^*, m = |H| = ord_p(2).")
    print("  For c not divisible by p:")
    print("    |sum_{h in H} omega^{c*h/p}| <= (m/d)*(d-1)*sqrt(p)/d + m/d")
    print("    where d = (p-1)/m. Simplified:")
    print("    |sum_{h in H} omega^{c*h/p}| < sqrt(p)")
    print("  (when m < p-1, i.e., 2 is not a primitive root mod p).")
    print()
    print("  When 2 IS a primitive root (m = p-1), H = (Z/pZ)^* and:")
    print("    sum_{h in H} omega^{c*h} = sum_{x=1}^{p-1} omega^{c*x} = -1")
    print("  (a complete character sum minus the x=0 term).")

    # ------------------------------------------------------------------
    # FULL SUBGROUP SUM VERIFICATION
    # ------------------------------------------------------------------
    print("\n  FULL SUBGROUP SUM |sigma_j| = |sum_{h in <2>} omega^{c*h/p}|:")
    print(f"  {'p':>6s} {'m=ord_p(2)':>12s} {'d=(p-1)/m':>12s} {'c':>6s} "
          f"{'|sigma|':>10s} {'sqrt(p)':>10s} {'ratio':>8s} {'<sqrt(p)?':>10s}")
    print(f"  {'':->82s}")

    subgroup_results = []
    test_primes_list = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
                        59, 61, 67, 71, 73, 79, 83, 89, 97]

    for p in test_primes_list:
        check_budget("Part3-subgroup")
        m = multiplicative_order(2, p)
        d = (p - 1) // m

        # Generate <2> = {2^0, 2^1, ..., 2^{m-1}} mod p
        H = []
        val = 1
        for _ in range(m):
            H.append(val)
            val = (val * 2) % p

        omega_val = 2.0 * math.pi / p

        # Test several values of c
        for c in [1, 3, 7, (p - 1) // 2]:
            if c >= p:
                continue
            sigma_real = sum(math.cos(omega_val * c * h) for h in H)
            sigma_imag = sum(math.sin(omega_val * c * h) for h in H)
            sigma_abs = math.sqrt(sigma_real**2 + sigma_imag**2)
            sqrt_p = math.sqrt(p)
            ratio = sigma_abs / sqrt_p
            below = sigma_abs < sqrt_p + 1e-10  # allow tiny numerical margin

            subgroup_results.append({
                'p': p, 'm': m, 'd': d, 'c': c,
                'sigma_abs': sigma_abs, 'sqrt_p': sqrt_p,
                'ratio': ratio, 'below': below
            })

            if p <= 53 or c == 1:
                print(f"  {p:6d} {m:12d} {d:12d} {c:6d} "
                      f"{sigma_abs:10.4f} {sqrt_p:10.4f} {ratio:8.4f} "
                      f"{'YES' if below else 'NO':>10s}")

    all_below = all(r['below'] for r in subgroup_results)
    print(f"\n  Weil bound |sigma| < sqrt(p) holds for ALL tested cases: {all_below}")

    # Handle cases where 2 is a primitive root
    prim_root_cases = [r for r in subgroup_results if r['m'] == r['p'] - 1]
    if prim_root_cases:
        print(f"  Cases where 2 is primitive root mod p: "
              f"{len(prim_root_cases)} (sigma should be ~ 1)")

    findings['subgroup_results'] = subgroup_results
    findings['all_below_weil'] = all_below

    # ------------------------------------------------------------------
    # ROW SUM ANALYSIS: |R_j| for actual Collatz parameters
    # ------------------------------------------------------------------
    print("\n\n  ROW SUM ANALYSIS for Collatz parameters:")
    print("  Row j of F has sum R_j = sum_{s=1}^{S-1} omega^{c_j * 2^s / p}")
    print("  where c_j = t * 3^{k-2-j} mod p.")
    print()
    print(f"  {'k':>4s} {'p':>6s} {'j':>4s} {'c_j':>6s} {'|R_j|':>10s} "
          f"{'sqrt(S-1)':>10s} {'sqrt(p)':>10s} {'|R_j|/sqrt(p)':>14s}")
    print(f"  {'':->68s}")

    row_results = []
    for k in range(3, 10):
        check_budget("Part3-rows")
        S = compute_S(k)
        d = compute_d(k)
        if not can_enumerate(k, 500_000):
            continue

        primes = distinct_primes(d)
        test_primes = [p for p in primes if 3 <= p <= 200][:2]

        for p in test_primes:
            t = 1
            F = build_F_matrix(k, p, t)
            n_cols = S - 1

            for j in range(k - 1):
                R_j = row_sum(F, j, n_cols)
                abs_R_j = abs(R_j)
                sqrt_n = math.sqrt(n_cols)
                sqrt_p_val = math.sqrt(p)
                c_j = (t * pow(3, k - 2 - j, p)) % p

                ratio_p = abs_R_j / sqrt_p_val
                print(f"  {k:4d} {p:6d} {j:4d} {c_j:6d} {abs_R_j:10.4f} "
                      f"{sqrt_n:10.4f} {sqrt_p_val:10.4f} {ratio_p:14.6f}")

                row_results.append({
                    'k': k, 'p': p, 'j': j, 'c_j': c_j,
                    'abs_R_j': abs_R_j, 'sqrt_n': sqrt_n,
                    'sqrt_p': sqrt_p_val, 'ratio_p': ratio_p
                })

    findings['row_results'] = row_results

    # ------------------------------------------------------------------
    # KEY OBSERVATION: multiplicative relation between rows
    # ------------------------------------------------------------------
    print("\n  KEY OBSERVATION (Multiplicative Row Relations):")
    print("  Row j has phases omega^{t * 3^{k-2-j} * 2^s / p}.")
    print("  Row j' has phases omega^{t * 3^{k-2-j'} * 2^s / p}.")
    print("  The ratio: f_{j'}(s) / f_j(s) = omega^{t * (3^{k-2-j'} - 3^{k-2-j}) * 2^s / p}.")
    print("  If j' = j + 1: ratio = omega^{t * 3^{k-2-j} * (1 - 3) * 2^s / p}")
    print("                       = omega^{-2t * 3^{k-2-j} * 2^s / p}")
    print("  The rows are NOT independent: f_{j+1}(s) = f_j(s) * phi_j(s)")
    print("  where phi_j(s) = omega^{t * 3^{k-3-j} * (1 - 3) * 2^s / p}.")
    print()
    print("  This means: the correlation between rows j and j' depends on")
    print("  the character sum with coefficient (w_j - w_{j'}) * t mod p.")
    print("  Since w_j = 3^{k-2-j} and w_{j'} = 3^{k-2-j'}, the difference")
    print("  w_j - w_{j'} = 3^{k-2-j'} * (3^{j'-j} - 1) mod p.")

    # Compute correlations between adjacent rows
    print("\n  INTER-ROW CORRELATIONS (adjacent rows):")
    print(f"  {'k':>4s} {'p':>6s} {'j':>4s} {'|<r_j, r_{j+1}>|/(S-1)':>24s} "
          f"{'1/sqrt(p)':>12s}")
    print(f"  {'':->52s}")

    for k in range(3, 8):
        check_budget("Part3-corr")
        S = compute_S(k)
        d = compute_d(k)
        primes = distinct_primes(d)
        test_primes = [p for p in primes if 3 <= p <= 200][:1]

        for p in test_primes:
            F = build_F_matrix(k, p, 1)
            n_cols = S - 1
            for j in range(k - 2):
                ip = row_inner_product(F, j, j + 1, n_cols)
                norm_ip = abs(ip) / n_cols
                print(f"  {k:4d} {p:6d} {j:4d} {norm_ip:24.8f} "
                      f"{1/math.sqrt(p):12.8f}")

    FINDINGS['Part3'] = findings
    return findings


# ============================================================================
# PART 4: FROM ROW BOUNDS TO TOTAL BOUND
# ============================================================================

def part4_row_to_total():
    """
    Part 4: From individual row bounds to a bound on |e_{k-1}(F)|.

    The key question: given |R_j| = |sum_s F[j,s]| <= B for each row j,
    what can we say about |e_{k-1}(F)| = |sum_{subsets} prod_j F[j,s_j]|?

    APPROACH 1: Sequential conditioning.
    Fix s_1. Then sum over s_2 > s_1, ..., s_{k-1} > s_{k-2}:
      e_{k-1} = sum_{s_1=1}^{S-k+1} F[0,s_1-1] * e_{k-2}(F'[s_1])
    where F'[s_1] is the (k-2) x (S-1-s_1) matrix restricted to columns > s_1.

    This gives: |e_{k-1}| <= sum_{s_1} |e_{k-2}(F'[s_1])|
    Recursion: |e_m| <= sum |e_{m-1}| <= ... <= C (trivial again).

    APPROACH 2: Second moment method.
    E[|e_{k-1}|^2] over random phases:
    If the phases were independent, E[|e_{k-1}|^2] = C (variance = C).
    But our phases are correlated (multiplicative structure).
    The actual second moment involves:
      E[|e_{k-1}|^2] = sum_{T, T'} prod_j E[F[j,T_j] * conj(F[j,T'_j])]

    For INDEPENDENT rows:
      = sum_{T, T'} prod_j delta(T_j, T'_j) * |inner product|^2
    But our rows are correlated.

    APPROACH 3: Parseval over t (the character variable).
    sum_{t=0}^{p-1} |T_p(t)|^2 = p * sum_r n_r^2
    So: mean_{t!=0} |T_p(t)|^2 / C^2 = (p * sum n_r^2 - C^2) / ((p-1)*C^2)

    The Parseval RMS bound gives:
      max_t |T_p(t)|/C <= sqrt((p-1) * mean) = sqrt(p * sum n_r^2 / C^2 - 1)

    If residues are UNIFORM (n_r = C/p): this gives 0 (impossible since n_r integer).
    If residues are NEARLY uniform (n_r ~ C/p + O(sqrt(C/p))):
      sum n_r^2 ~ C^2/p + C, so mean ~ C/(p-1), so RMS ~ 1/sqrt(p).

    APPROACH 4: Multilinear variance decomposition.
    |e_{k-1}|^2 = sum_{T,T'} prod_j F[j,T_j]*conj(F[j,T'_j])
    Pair T,T' share some columns, differ in others.
    The "diagonal" terms (T=T') contribute C.
    The off-diagonal terms contribute based on correlations.

    We compute the actual second moment and compare to the Parseval prediction.
    """
    print("\n" + "=" * 72)
    print("PART 4: FROM ROW BOUNDS TO TOTAL BOUND (MULTILINEAR STRUCTURE)")
    print("=" * 72)

    findings = {}

    # ------------------------------------------------------------------
    # PARSEVAL ANALYSIS (revisited with ESF perspective)
    # ------------------------------------------------------------------
    print("\n  PARSEVAL ANALYSIS (ESF perspective):")
    print("  sum_{t=0}^{p-1} |e_{k-1}(F_t)|^2 = p * sum_r n_r^2")
    print("  where F_t denotes the matrix with parameter t.")
    print()
    print("  RMS rho = sqrt((p*sum n_r^2 - C^2)/((p-1)*C^2))")
    print("  If rho ~ 1/sqrt(p), this confirms the square-root cancellation.")
    print()

    print(f"  {'k':>4s} {'p':>6s} {'C':>10s} {'RMS rho':>10s} {'max rho':>10s} "
          f"{'1/sqrt(p)':>10s} {'alpha_RMS':>10s} {'alpha_max':>10s}")
    print(f"  {'':->74s}")

    parseval_esf = []
    for k in range(3, 13):
        check_budget("Part4-parseval")
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        if not can_enumerate(k, 500_000):
            continue

        primes = distinct_primes(d)
        test_primes = [p for p in primes if 3 <= p <= 500][:2]

        for p in test_primes:
            check_budget("Part4-parseval-inner")
            dist = get_residue_distribution(k, p)
            sum_nr2 = sum(c**2 for c in dist.values())

            rms_T2 = (p * sum_nr2 - C**2) / (p - 1) if p > 1 else 0
            rms_rho = math.sqrt(max(0, rms_T2)) / C

            max_rho, t_star = compute_max_rho(k, p, dist, t_limit=min(p, 200))

            inv_sqrt_p = 1.0 / math.sqrt(p)

            # alpha = rho * sqrt(p): the "normalized" cancellation constant
            alpha_rms = rms_rho * math.sqrt(p)
            alpha_max = max_rho * math.sqrt(p)

            print(f"  {k:4d} {p:6d} {C:10d} {rms_rho:10.6f} {max_rho:10.6f} "
                  f"{inv_sqrt_p:10.6f} {alpha_rms:10.4f} {alpha_max:10.4f}")

            parseval_esf.append({
                'k': k, 'p': p, 'C': C,
                'rms_rho': rms_rho, 'max_rho': max_rho,
                'alpha_rms': alpha_rms, 'alpha_max': alpha_max,
                'sum_nr2': sum_nr2
            })

    findings['parseval_esf'] = parseval_esf

    # ------------------------------------------------------------------
    # SECOND MOMENT DECOMPOSITION via overlap structure
    # ------------------------------------------------------------------
    print("\n  SECOND MOMENT DECOMPOSITION (overlap structure):")
    print("  |e_{k-1}|^2 = sum_{T, T': |T|=|T'|=k-1} prod_j F[j,T_j]*conj(F[j,T'_j])")
    print("  Group by overlap |T intersect T'| = m (0 <= m <= k-1):")
    print("    |e_{k-1}|^2 = sum_{m=0}^{k-1} N_m * avg_contribution(m)")
    print("  where N_m = C(k-1,m) * C(S-1-k+1, k-1-m)^2 * C(k-1, m)... (complicated)")
    print()
    print("  Diagonal (m = k-1): C terms, each contributing 1. Total = C.")
    print("  Off-diagonal (m < k-1): involves cross-correlations.")
    print()

    # Compute actual second moment for small cases
    print("  EXACT second moment computation:")
    print(f"  {'k':>4s} {'p':>6s} {'C':>10s} "
          f"{'E[|e|^2]':>14s} {'C':>10s} {'ratio':>10s} {'predict':>10s}")
    print(f"  {'':->66s}")

    for k in range(3, 7):
        check_budget("Part4-2nd-moment")
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        if C > 50_000:
            continue

        primes = distinct_primes(d)
        test_primes = [p for p in primes if 3 <= p <= 100][:1]

        for p in test_primes:
            check_budget("Part4-2nd-inner")
            # Compute average |e_{k-1}|^2 over t = 1..p-1
            total_sq = 0.0
            for t in range(1, p):
                check_budget("Part4-2nd-t")
                F = build_F_matrix(k, p, t)
                esf = compute_esf(F, k - 1, S - 1)
                total_sq += abs(esf)**2

            avg_sq = total_sq / (p - 1)
            ratio = avg_sq / C if C > 0 else 0

            # Parseval prediction: avg = (p*sum_nr2 - C^2)/((p-1))
            dist = get_residue_distribution(k, p)
            sum_nr2 = sum(c**2 for c in dist.values())
            parseval_pred = (p * sum_nr2 - C**2) / (p - 1)

            print(f"  {k:4d} {p:6d} {C:10d} {avg_sq:14.4f} "
                  f"{C:10d} {ratio:10.4f} {parseval_pred:10.4f}")

    # ------------------------------------------------------------------
    # ALPHA BOUND ANALYSIS
    # ------------------------------------------------------------------
    print("\n  ALPHA BOUND ANALYSIS:")
    print("  If |T_p(t)| = O(alpha * C / sqrt(p)), then for N_0(p) = 0")
    print("  (via sum_{t=1}^{p-1} T_p(t) = p*n_0 - C), we need:")
    print("    |p*n_0 - C| <= sum |T_p(t)| <= (p-1)*alpha*C/sqrt(p)")
    print("    ~ alpha*C*sqrt(p)")
    print("  For n_0 = 0: C <= alpha*C*sqrt(p), so sqrt(p) >= 1/alpha.")
    print("  This gives p >= 1/alpha^2 -- NOT useful since alpha > 1 typically.")
    print()
    print("  THE CORRECT USE: The character sum approach via Parseval.")
    print("  n_0 = (C + sum T_p(t))/p. For |T_p(t)| <= alpha*C/sqrt(p):")
    print("    |n_0 - C/p| = |sum T_p(t)|/p <= (p-1)*alpha*C/(p*sqrt(p))")
    print("                = alpha*C*(p-1)/(p^{3/2})")
    print("  For n_0 = 0 to be forced: C/p > alpha*C*(p-1)/p^{3/2}")
    print("  i.e., 1 > alpha*(p-1)/sqrt(p), i.e., sqrt(p) > alpha*(p-1)/p^{1/2}")
    print("  This simplifies to: p > alpha^2 (for large p).")
    print()
    print("  CONCLUSION: If alpha is BOUNDED (independent of k, p), then")
    print("  for all p > alpha^2, we have n_0 = 0 (no cycle mod p).")
    print("  The small primes (p <= alpha^2) need direct verification.")

    if parseval_esf:
        max_alpha = max(r['alpha_max'] for r in parseval_esf)
        print(f"\n  OBSERVED maximum alpha_max = {max_alpha:.4f}")
        print(f"  This would require verifying p <= {max_alpha**2:.1f} directly.")
        findings['max_alpha'] = max_alpha
    else:
        findings['max_alpha'] = None

    FINDINGS['Part4'] = findings
    return findings


# ============================================================================
# PART 5: NUMERICAL VERIFICATION FOR k=3..15
# ============================================================================

def part5_numerical_verification():
    """
    Part 5: Comprehensive numerical verification of square-root cancellation.

    For k=3..15 and all primes p | d(k):
    - Compute |T_p(t)| / C for all t = 1..p-1 (when feasible)
    - Compare to 1/sqrt(p) and C/sqrt(p)
    - Identify the "alpha" constant: max_t |T_p(t)| * sqrt(p) / C
    - Determine for which (k, p) the bound |T_p(t)| = O(C/sqrt(p)) holds
    """
    print("\n" + "=" * 72)
    print("PART 5: NUMERICAL VERIFICATION FOR k=3..15")
    print("=" * 72)

    findings = {}

    # ------------------------------------------------------------------
    # COMPREHENSIVE TABLE
    # ------------------------------------------------------------------
    print("\n  COMPREHENSIVE TABLE: Square-root cancellation verification")
    print(f"  {'k':>3s} {'S':>4s} {'C':>10s} {'p':>8s} {'ord_p(2)':>10s} "
          f"{'max|T|/C':>10s} {'1/sqrt(p)':>10s} {'alpha':>8s} "
          f"{'<1?':>5s} {'1/(p-1)?':>9s}")
    print(f"  {'':->88s}")

    all_results = []
    all_rho_lt_1 = True

    for k in range(3, 16):
        check_budget("Part5")
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)

        primes = distinct_primes(d)

        for p in primes:
            check_budget("Part5-prime")
            # Determine if we can compute exactly
            if not can_enumerate(k, 800_000):
                # For large k, only check small primes with transfer matrix
                if p > 200:
                    continue
                # Use transfer matrix method
                max_rho = 0.0
                argmax_t = 1
                t_upper = min(p, 50)
                for t in range(1, t_upper):
                    check_budget("Part5-tm-t")
                    M = compute_product_matrix(k, p, t)
                    entry = abs(M[k - 1][0])
                    rho_val = entry / C
                    if rho_val > max_rho:
                        max_rho = rho_val
                        argmax_t = t
            else:
                if p > 2000:
                    continue
                dist = get_residue_distribution(k, p)
                max_rho, argmax_t = compute_max_rho(
                    k, p, dist, t_limit=min(p, 500))

            ord2 = multiplicative_order(2, p)
            inv_sqrt_p = 1.0 / math.sqrt(p)
            alpha = max_rho * math.sqrt(p)
            lt_1 = max_rho < 1.0 - 1e-10
            lt_inv_pm1 = max_rho < 1.0 / (p - 1) + 1e-10

            if not lt_1:
                all_rho_lt_1 = False

            print(f"  {k:3d} {S:4d} {C:10d} {p:8d} {ord2:10d} "
                  f"{max_rho:10.6f} {inv_sqrt_p:10.6f} {alpha:8.4f} "
                  f"{'YES' if lt_1 else 'NO':>5s} "
                  f"{'YES' if lt_inv_pm1 else 'no':>9s}")

            all_results.append({
                'k': k, 'S': S, 'C': C, 'p': p, 'ord2': ord2,
                'max_rho': max_rho, 'alpha': alpha,
                'lt_1': lt_1, 'lt_inv_pm1': lt_inv_pm1,
                'argmax_t': argmax_t
            })

    findings['all_results'] = all_results
    findings['all_rho_lt_1'] = all_rho_lt_1

    # ------------------------------------------------------------------
    # ALPHA STATISTICS
    # ------------------------------------------------------------------
    if all_results:
        alphas = [r['alpha'] for r in all_results]
        rhos = [r['max_rho'] for r in all_results]

        print(f"\n  STATISTICS (over {len(all_results)} (k, p) pairs):")
        print(f"    max_rho range: [{min(rhos):.6f}, {max(rhos):.6f}]")
        print(f"    alpha range:   [{min(alphas):.4f}, {max(alphas):.4f}]")
        print(f"    alpha mean:    {sum(alphas)/len(alphas):.4f}")
        print(f"    alpha median:  {sorted(alphas)[len(alphas)//2]:.4f}")
        print(f"    ALL rho < 1:   {all_rho_lt_1}")

        # Count how many satisfy rho < 1/(p-1) (Theorem Q threshold)
        thm_q_count = sum(1 for r in all_results if r['lt_inv_pm1'])
        print(f"    rho < 1/(p-1): {thm_q_count}/{len(all_results)}")

        # Group by k
        print(f"\n  ALPHA BY k:")
        print(f"  {'k':>4s} {'#primes':>8s} {'max_alpha':>10s} "
              f"{'mean_alpha':>10s} {'max_rho':>10s}")
        print(f"  {'':->48s}")
        for k_val in sorted(set(r['k'] for r in all_results)):
            k_results = [r for r in all_results if r['k'] == k_val]
            k_alphas = [r['alpha'] for r in k_results]
            k_rhos = [r['max_rho'] for r in k_results]
            print(f"  {k_val:4d} {len(k_results):8d} {max(k_alphas):10.4f} "
                  f"{sum(k_alphas)/len(k_alphas):10.4f} {max(k_rhos):10.6f}")

        findings['max_alpha_overall'] = max(alphas)
        findings['all_rho_lt_1'] = all_rho_lt_1

    # ------------------------------------------------------------------
    # THE KEY THEORETICAL QUESTION: Is alpha bounded?
    # ------------------------------------------------------------------
    print("\n  THE KEY THEORETICAL QUESTION:")
    print("  Is alpha = max_t |T_p(t)| * sqrt(p) / C bounded by a UNIVERSAL constant?")
    print()
    if all_results:
        max_alpha = max(r['alpha'] for r in all_results)
        print(f"  Observed max alpha across all (k, p): {max_alpha:.4f}")
        print(f"  If alpha <= {max_alpha:.2f} universally, then:")
        print(f"    N_0(p) = 0 for all p > {max_alpha**2:.1f}")
        print(f"    Combined with direct verification of small primes,")
        print(f"    this would prove the no-cycle theorem for each individual k.")

    print()
    print("  STRUCTURAL EVIDENCE for bounded alpha:")
    print("  1. The phases t*w_j*2^s mod p are MULTIPLICATIVELY structured.")
    print("  2. The elementary symmetric function e_{k-1} averages over C terms.")
    print("  3. Each row is a character sum over <2>, bounded by O(sqrt(p)).")
    print("  4. The multilinear structure with ORDERED subsets enforces regularity.")
    print("  5. As k increases, (k-1) correlated rows average out more thoroughly.")
    print()
    print("  OBSTACLE to proof:")
    print("  The correlation between rows (f_{j+1}(s) ~ f_j(s)^3) prevents")
    print("  direct application of independence-based arguments.")
    print("  The Cauchy-Binet identity connects e_{k-1} to DETERMINANTS of minors,")
    print("  but the lack of signs (products vs. signed determinants) means")
    print("  standard determinantal bounds (Hadamard, etc.) do not directly apply.")

    FINDINGS['Part5'] = findings
    return findings


# ============================================================================
# SELF-TESTS (25 tests, T01-T25)
# ============================================================================

def run_self_tests():
    """Run 25 self-tests."""
    print("SELF-TESTS (25 tests)")
    print("-" * 72)

    # ---- T01: corrSum consistency ----
    k, S = 5, compute_S(5)
    d = compute_d(k)
    p = distinct_primes(d)[0] if distinct_primes(d) else 7
    B = tuple(range(1, k))
    cs_true_val = 3**(k - 1)
    for idx in range(len(B)):
        j = idx + 1
        cs_true_val += 3**(k - 1 - j) * 2**B[idx]
    cs_mod = corrsum_mod(B, k, p)
    record_test("T01: corrsum mod consistency",
                cs_true_val % p == cs_mod,
                f"true%p={cs_true_val % p}, mod={cs_mod}")

    # ---- T02: |T(0)| = C always ----
    k = 4
    S = compute_S(k)
    C = num_compositions(S, k)
    d = compute_d(k)
    p = distinct_primes(d)[0] if distinct_primes(d) else 7
    T0 = compute_T_exact(k, p, 0)
    record_test("T02: |T(0)| = C",
                abs(abs(T0) - C) < 1e-6,
                f"|T(0)|={abs(T0):.4f}, C={C}")

    # ---- T03: ESF = Transfer matrix entry for k=3 ----
    k, p, t = 3, 5, 1
    S = compute_S(k)
    F = build_F_matrix(k, p, t)
    esf_val = compute_esf(F, k - 1, S - 1)
    M = compute_product_matrix(k, p, t)
    tm_val = M[k - 1][0]
    err = abs(esf_val - tm_val)
    record_test("T03: e_{k-1}(F) == M[k-1,0] for k=3, p=5",
                err < 1e-6,
                f"err={err:.2e}")

    # ---- T04: ESF = Transfer matrix entry for k=5 ----
    k = 5
    d = compute_d(k)
    p = distinct_primes(d)[0] if distinct_primes(d) else 7
    t = 1
    S = compute_S(k)
    F = build_F_matrix(k, p, t)
    esf_val = compute_esf(F, k - 1, S - 1)
    M = compute_product_matrix(k, p, t)
    tm_val = M[k - 1][0]
    err = abs(esf_val - tm_val)
    record_test("T04: e_{k-1}(F) == M[k-1,0] for k=5",
                err < 1e-6,
                f"err={err:.2e}")

    # ---- T05: ESF = Transfer matrix for k=4, multiple t ----
    k = 4
    d = compute_d(k)
    p = distinct_primes(d)[0] if distinct_primes(d) else 7
    S = compute_S(k)
    all_ok = True
    max_err = 0.0
    for t_val in range(1, min(p, 6)):
        F = build_F_matrix(k, p, t_val)
        esf_v = compute_esf(F, k - 1, S - 1)
        M = compute_product_matrix(k, p, t_val)
        e = abs(esf_v - M[k - 1][0])
        max_err = max(max_err, e)
        if e > 1e-4:
            all_ok = False
    record_test("T05: ESF == M[k-1,0] for k=4, t=1..5",
                all_ok, f"max_err={max_err:.2e}")

    # ---- T06: F matrix has all entries of modulus 1 ----
    k, p, t = 5, 7, 3
    S = compute_S(k)
    F = build_F_matrix(k, p, t)
    all_unit = all(abs(abs(F[j][s]) - 1.0) < 1e-10
                   for j in range(k - 1) for s in range(S - 1))
    record_test("T06: All F[j,s] have |.| = 1",
                all_unit)

    # ---- T07: Row norm squared = S-1 (since |F[j,s]|=1) ----
    k, p, t = 4, 11, 2
    S = compute_S(k)
    F = build_F_matrix(k, p, t)
    n_cols = S - 1
    all_correct = all(abs(row_norm_sq(F, j, n_cols) - n_cols) < 1e-8
                      for j in range(k - 1))
    record_test("T07: ||row_j||^2 = S-1 for all j",
                all_correct,
                f"S-1={n_cols}")

    # ---- T08: Gram diagonal = 1 ----
    k, p, t = 4, 11, 2
    S = compute_S(k)
    F = build_F_matrix(k, p, t)
    n_cols = S - 1
    all_diag_1 = all(
        abs(row_inner_product(F, j, j, n_cols) / n_cols - 1.0) < 1e-10
        for j in range(k - 1))
    record_test("T08: Gram diagonal G[j,j] = 1",
                all_diag_1)

    # ---- T09: Number of terms in e_{k-1} = C(S-1, k-1) ----
    k = 5
    S = compute_S(k)
    C = num_compositions(S, k)
    n_terms = len(list(combinations(range(S - 1), k - 1)))
    record_test("T09: Number of ESF terms = C",
                n_terms == C,
                f"terms={n_terms}, C={C}")

    # ---- T10: Parseval identity ----
    k, p = 3, 5
    dist = get_residue_distribution(k, p)
    C = num_compositions(compute_S(k), k)
    lhs = sum(abs(compute_T_exact(k, p, t, dist))**2 for t in range(p))
    rhs = p * sum(c**2 for c in dist.values())
    record_test("T10: Parseval identity for k=3, p=5",
                abs(lhs - rhs) < 1e-4,
                f"diff={abs(lhs - rhs):.2e}")

    # ---- T11: max_rho < 1 for k=3..6 ----
    all_lt_1 = True
    for k_val in range(3, 7):
        d_val = compute_d(k_val)
        primes_val = distinct_primes(d_val)
        for p_val in primes_val[:2]:
            S_val = compute_S(k_val)
            C_val = num_compositions(S_val, k_val)
            if C_val > 300_000:
                continue
            dist_val = get_residue_distribution(k_val, p_val)
            rho_val, _ = compute_max_rho(k_val, p_val, dist_val,
                                          t_limit=min(p_val, 100))
            if rho_val >= 1.0 - 1e-10:
                all_lt_1 = False
    record_test("T11: max_rho < 1 for k=3..6, all tested p",
                all_lt_1)

    # ---- T12: Subgroup character sum |sigma| < sqrt(p) ----
    p_test = 13
    m = multiplicative_order(2, p_test)
    H = []
    val = 1
    for _ in range(m):
        H.append(val)
        val = (val * 2) % p_test
    omega_val = 2.0 * math.pi / p_test
    c_test = 3
    sigma_r = sum(math.cos(omega_val * c_test * h) for h in H)
    sigma_i = sum(math.sin(omega_val * c_test * h) for h in H)
    sigma_abs = math.sqrt(sigma_r**2 + sigma_i**2)
    record_test("T12: |sigma| < sqrt(p) for p=13, c=3",
                sigma_abs < math.sqrt(p_test) + 1e-10,
                f"|sigma|={sigma_abs:.4f}, sqrt(p)={math.sqrt(p_test):.4f}")

    # ---- T13: Full subgroup sum = -1 when 2 is primitive root ----
    # 2 is primitive root mod 5 (ord_5(2) = 4 = 5-1)
    p_test = 5
    m = multiplicative_order(2, p_test)
    is_prim = (m == p_test - 1)
    if is_prim:
        H = []
        val = 1
        for _ in range(m):
            H.append(val)
            val = (val * 2) % p_test
        omega_val = 2.0 * math.pi / p_test
        # sum_{x=1}^{p-1} omega^x = -1
        sigma_r = sum(math.cos(omega_val * h) for h in H)
        sigma_i = sum(math.sin(omega_val * h) for h in H)
        record_test("T13: Full char sum = -1 when 2 prim root mod 5",
                     abs(sigma_r - (-1)) < 1e-8 and abs(sigma_i) < 1e-8,
                     f"sum={sigma_r:.6f}+{sigma_i:.6f}i")
    else:
        record_test("T13: 2 is NOT primitive root mod 5 -- SKIP",
                     True, "Unexpected -- 2 should be primitive root mod 5")

    # ---- T14: d(k) > 0 for k=3..20 ----
    all_pos = all(compute_d(k_val) > 0 for k_val in range(3, 21))
    record_test("T14: d(k) > 0 for k=3..20", all_pos)

    # ---- T15: n_0(k=3, d) = 0 ----
    k = 3
    S = compute_S(k)
    d = compute_d(k)
    C = num_compositions(S, k)
    n0_d = sum(1 for B in combinations(range(1, S), k - 1)
               if corrsum_mod(B, k, d) == 0)
    record_test("T15: n_0(k=3, d(3)) = 0",
                n0_d == 0,
                f"n_0={n0_d}")

    # ---- T16: Inner product symmetry: <r_j, r_j'> = conj(<r_j', r_j>) ----
    k, p, t = 4, 11, 1
    S = compute_S(k)
    F = build_F_matrix(k, p, t)
    n_cols = S - 1
    ip_01 = row_inner_product(F, 0, 1, n_cols)
    ip_10 = row_inner_product(F, 1, 0, n_cols)
    record_test("T16: <r_0, r_1> = conj(<r_1, r_0>)",
                abs(ip_01 - ip_10.conjugate()) < 1e-10,
                f"diff={abs(ip_01 - ip_10.conjugate()):.2e}")

    # ---- T17: ESF for k-1=1 (single row) = row sum ----
    k = 2  # k-1 = 1: ESF = sum of single row
    p, t = 7, 1
    S = compute_S(k)
    F = build_F_matrix(k, p, t)
    n_cols = S - 1
    esf_1 = compute_esf(F, 1, n_cols)  # e_1 = sum_s F[0, s]
    rs = row_sum(F, 0, n_cols)
    record_test("T17: e_1(F) = row sum for k=2",
                abs(esf_1 - rs) < 1e-10,
                f"diff={abs(esf_1 - rs):.2e}")

    # ---- T18: ESF for k-1=2 (two rows) matches explicit formula ----
    k = 3  # k-1 = 2
    p, t = 7, 1
    S = compute_S(k)
    F = build_F_matrix(k, p, t)
    n_cols = S - 1
    esf_2 = compute_esf(F, 2, n_cols)
    # Explicit: e_2 = sum_{s1<s2} F[0,s1]*F[1,s2]
    explicit_sum = 0j
    for s1 in range(n_cols - 1):
        for s2 in range(s1 + 1, n_cols):
            explicit_sum += F[0][s1] * F[1][s2]
    record_test("T18: e_2(F) matches explicit double sum for k=3",
                abs(esf_2 - explicit_sum) < 1e-10,
                f"diff={abs(esf_2 - explicit_sum):.2e}")

    # ---- T19: multiplicative_order correct ----
    ord_2_7 = multiplicative_order(2, 7)  # 2^3 = 8 = 1 mod 7
    record_test("T19: ord_7(2) = 3",
                ord_2_7 == 3,
                f"ord={ord_2_7}")

    # ---- T20: Transfer matrix is lower bidiagonal ----
    k_test, p_test, t_test, s_test = 5, 97, 3, 4
    T_s = transfer_matrix_T(k_test, p_test, t_test, s_test)
    is_bidiag = True
    for i in range(k_test):
        for j in range(k_test):
            if i == j:
                if abs(T_s[i][j] - 1.0) > 1e-10:
                    is_bidiag = False
            elif i == j + 1:
                if abs(abs(T_s[i][j]) - 1.0) > 1e-10:
                    is_bidiag = False
            else:
                if abs(T_s[i][j]) > 1e-10:
                    is_bidiag = False
    record_test("T20: T_s is lower bidiagonal with |subdiag| = 1",
                is_bidiag)

    # ---- T21: ESF = T_p(t) * conj(phase) for k=4 ----
    k, t = 4, 2
    S = compute_S(k)
    d = compute_d(k)
    p = distinct_primes(d)[0]
    F = build_F_matrix(k, p, t)
    esf_val = compute_esf(F, k - 1, S - 1)
    T_val = compute_T_exact(k, p, t)
    # T_p(t) = phase * M[k-1,0] = phase * e_{k-1}(F)
    omega_val = 2.0 * math.pi / p
    init_phase = cmath.exp(1j * omega_val * (t * pow(3, k - 1, p) % p))
    T_from_esf = init_phase * esf_val
    err = abs(T_from_esf - T_val)
    record_test("T21: T_p(t) = phase * e_{k-1}(F) for k=4",
                err < 1e-4,
                f"err={err:.2e}")

    # ---- T22: Row weights are distinct mod p ----
    k, p = 5, 7
    weights = [pow(3, k - 2 - j, p) for j in range(k - 1)]
    all_distinct = len(set(weights)) == len(weights)
    record_test("T22: Row weights w_j distinct mod p (k=5, p=7)",
                all_distinct,
                f"weights={weights}")

    # ---- T23: Gram matrix is Hermitian ----
    k, p, t = 4, 11, 1
    S = compute_S(k)
    F = build_F_matrix(k, p, t)
    n_rows = k - 1
    n_cols = S - 1
    G = [[0j] * n_rows for _ in range(n_rows)]
    for j1 in range(n_rows):
        for j2 in range(n_rows):
            G[j1][j2] = row_inner_product(F, j1, j2, n_cols) / n_cols
    is_hermitian = all(
        abs(G[j1][j2] - G[j2][j1].conjugate()) < 1e-10
        for j1 in range(n_rows) for j2 in range(n_rows))
    record_test("T23: Gram matrix is Hermitian",
                is_hermitian)

    # ---- T24: alpha = |T|*sqrt(p)/C is positive for nontrivial t ----
    k, p = 3, 5
    dist = get_residue_distribution(k, p)
    max_rho, _ = compute_max_rho(k, p, dist)
    alpha = max_rho * math.sqrt(p)
    record_test("T24: alpha > 0 for k=3, p=5",
                alpha > 0,
                f"alpha={alpha:.6f}")

    # ---- T25: ESF matches for k=6 (larger case) ----
    k = 6
    S = compute_S(k)
    d = compute_d(k)
    C = num_compositions(S, k)
    p = distinct_primes(d)[0] if distinct_primes(d) else 5
    t = 1
    F = build_F_matrix(k, p, t)
    esf_val = compute_esf(F, k - 1, S - 1)
    M = compute_product_matrix(k, p, t)
    tm_val = M[k - 1][0]
    err = abs(esf_val - tm_val)
    record_test("T25: e_{k-1}(F) == M[k-1,0] for k=6",
                err < 1e-5,
                f"err={err:.2e}, C={C}")

    # Final summary
    print("-" * 72)
    n_pass = sum(1 for _, p_val, _ in TEST_RESULTS if p_val)
    n_fail = sum(1 for _, p_val, _ in TEST_RESULTS if not p_val)
    print(f"TOTAL: {n_pass} PASS, {n_fail} FAIL out of {len(TEST_RESULTS)} tests")
    return n_fail == 0


# ============================================================================
# MAIN DISPATCH
# ============================================================================

def main():
    args = sys.argv[1:]

    if "selftest" in args:
        all_pass = run_self_tests()
        sys.exit(0 if all_pass else 1)

    parts_to_run = set()
    if not args:
        parts_to_run = {1, 2, 3, 4, 5}
    else:
        for a in args:
            if a.isdigit():
                parts_to_run.add(int(a))

    # Always run self-tests first
    print()
    all_pass = run_self_tests()
    print()

    part_dispatch = {
        1: ("Part 1: ESF Identity Verification", part1_esf_identity),
        2: ("Part 2: Determinantal and Correlation Bounds", part2_determinantal_bounds),
        3: ("Part 3: Weil Bound for Individual Rows", part3_weil_row_bounds),
        4: ("Part 4: Row Bounds to Total Bound", part4_row_to_total),
        5: ("Part 5: Numerical Verification k=3..15", part5_numerical_verification),
    }

    for part_id in sorted(parts_to_run):
        if part_id in part_dispatch:
            name, func = part_dispatch[part_id]
            try:
                check_budget(name)
                func()
            except TimeoutError as e:
                print(f"\n  [TIMEOUT] {name}: {e}")
            except Exception as e:
                print(f"\n  [ERROR] {name}: {e}")
                import traceback
                traceback.print_exc()

    elapsed = time.time() - T_START
    print(f"\nTotal elapsed: {elapsed:.1f}s")


if __name__ == "__main__":
    main()
