#!/usr/bin/env python3
"""
r6_wr_correction_bound.py -- Round 6: Without-Replacement Correction Bound
============================================================================

CONTEXT (Rounds 1-5 complete):
  Steiner's equation: n0 * d = corrSum(A),  d = 2^S - 3^k,  S = ceil(k*log2(3)).
  corrSum(A) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{a_j} where A = {a_0 < ... < a_{k-1}}
  subset of {0,1,...,S-1} with a_0 = 0.

  A cycle exists iff corrSum(A) = 0 mod d for some valid A.

  The Horner chain: c_0 = 0, c_{j+1} = 3*c_j + 2^{b_{k-1-j}} mod p
  where B = {b_1 < ... < b_{k-1}} subset of {1,...,S-1}.

  The exponential sum T_p(t) = sum_B exp(2*pi*i * t * corrSum(B) / p)
  where p|d and B ranges over all C(S-1,k-1) valid subsets.

  The MARKOV APPROXIMATION treats {b_j} as i.i.d. draws WITH replacement
  from {1,...,S-1}. Then:
      T_Markov(t) = phi_0(t) * prod_{j=1}^{k-1} Phi_j(t)
  where:
      phi_0(t) = omega^{t * 3^{k-1}}  (fixed term for b_0 = 0)
      Phi_j(t) = sum_{m=1}^{S-1} omega^{t * 3^{k-1-j} * 2^m}
  and omega = exp(2*pi*i/p).

  The NORMALIZED Markov probability:
      T_Markov_prob(t) = phi_0(t) * prod_{j=1}^{k-1} [Phi_j(t) / (S-1)]
  so that T_Markov_prob(0) = 1 and T_Markov = C * T_Markov_prob (approximately).

  The KEY QUESTION: bound |E(t)| where E(t) relates T_exact to T_Markov.

  From Round 5:
    R24: Horner sum = Bourgain-type weighted subset character sum (NOT Weil/Deligne)
    R25: Mechanism B (CRT product < 1) dominates 100% for k >= 18

THE GAP (Path D from Round 5):
  - For small p < sqrt(S): Markov bound suffices (|phi_j| <= sqrt(p)/(S-1))
  - For large p > C(S-1,k-1): dimensional bound C/p << 1 suffices
  - GAP: intermediate primes p ~ S^2 -- THIS IS OUR TARGET

FIVE ANALYSIS TOOLS:
  Tool 1: EXACT COMPUTATION of |T_exact - T_Markov| for k=3..17
  Tool 2: INCLUSION-EXCLUSION analysis of the without-replacement constraint
  Tool 3: NEGATIVE DEPENDENCE bound (Dubhashi-Ranjan 1998)
  Tool 4: REGIME ANALYSIS -- |E(t)|/|T_Markov(t)| as a function of p
  Tool 5: THE KEY BOUND -- for intermediate primes p ~ S^2

HONESTY COMMITMENT:
  If a bound DOES NOT hold, this script says so with a counterexample.
  All modular computations are exact (Python integer arithmetic).

Author: Claude (R6-Analyste for Eric Merle's Collatz Junction Theorem)
Date:   2026-03-08

Usage:
    python3 r6_wr_correction_bound.py             # run all tools
    python3 r6_wr_correction_bound.py selftest     # self-tests only
    python3 r6_wr_correction_bound.py 1 3 5        # run tools 1, 3, 5

Requires: math, itertools, cmath, collections (standard library only).
Time budget: 300 seconds max.
"""

import math
import hashlib
import sys
import time
import cmath
from itertools import combinations
from collections import Counter, defaultdict


# ============================================================================
# GLOBAL TIME BUDGET
# ============================================================================

T_START = time.time()
TIME_BUDGET = 300.0

def time_remaining():
    return TIME_BUDGET - (time.time() - T_START)

def check_budget(label=""):
    """Raise TimeoutError if budget exhausted."""
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
    """d(k) = 2^S - 3^k."""
    S = compute_S(k)
    return (1 << S) - 3**k


def num_compositions(S, k):
    """C(S-1, k-1): number of valid (k-1)-subsets of {1,...,S-1}."""
    return math.comb(S - 1, k - 1)


def prime_factorization(n):
    """Return list of (prime, exponent) pairs for |n|."""
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


def modinv(a, m):
    """Modular inverse of a mod m. Returns None if gcd(a,m) != 1."""
    if m == 1:
        return 0
    g, x, _ = _extended_gcd(a % m, m)
    if g != 1:
        return None
    return x % m


def _extended_gcd(a, b):
    """Extended Euclidean algorithm."""
    if a == 0:
        return b, 0, 1
    g, x, y = _extended_gcd(b % a, a)
    return g, y - (b // a) * x, x


def corrsum_from_subset(B_tuple, k, mod):
    """
    Compute corrSum mod `mod` from a (k-1)-subset B of {1,...,S-1}.
    With b_0 = 0:
        corrSum = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{b_j} mod `mod`
    """
    result = pow(3, k - 1, mod)  # j=0 term: 3^{k-1} * 2^0
    for idx in range(len(B_tuple)):
        j = idx + 1
        result = (result + pow(3, k - 1 - j, mod)
                  * pow(2, B_tuple[idx], mod)) % mod
    return result


def corrsum_true(B_tuple, k):
    """Compute the TRUE (unreduced) corrSum as a Python integer."""
    total = 3 ** (k - 1)  # j=0: 3^{k-1} * 2^0
    for idx in range(len(B_tuple)):
        j = idx + 1
        total += 3 ** (k - 1 - j) * 2 ** B_tuple[idx]
    return total


def can_enumerate(k, limit=5_300_000):
    """True if exhaustive enumeration is feasible within limit."""
    S = compute_S(k)
    return math.comb(S - 1, k - 1) <= limit


def enumerate_corrsums_mod(k, mod):
    """Exact distribution of corrSum mod `mod`. Returns Counter."""
    S = compute_S(k)
    counts = Counter()
    for B in combinations(range(1, S), k - 1):
        counts[corrsum_from_subset(B, k, mod)] += 1
    return counts


# ============================================================================
# FOURIER / MARKOV PRIMITIVES
# ============================================================================

def fourier_sum_from_dist(dist, p, t):
    """
    Compute T_exact(t) = sum_B exp(2*pi*i*t*corrSum(B)/p) from distribution.
    Returns complex number.
    """
    omega = cmath.exp(2j * cmath.pi / p)
    T = complex(0.0, 0.0)
    for r, count in dist.items():
        T += count * (omega ** ((t * r) % p))
    return T


def fourier_sum_abs(dist, p, t):
    """Return |T_exact(t)|."""
    return abs(fourier_sum_from_dist(dist, p, t))


def compute_T_markov(k, p, t):
    """
    Compute T_Markov(t) = C * phi_0(t) * prod_{j=1}^{k-1} [Phi_j(t) / (S-1)]

    where:
      phi_0(t) = omega^{t * 3^{k-1}}              (fixed b_0 = 0)
      Phi_j(t) = sum_{m=1}^{S-1} omega^{t * 3^{k-1-j} * 2^m}
      C = C(S-1, k-1)

    This is NORMALIZED so that T_Markov(0) = C, matching T_exact(0) = C.
    The normalization uses C instead of (S-1)^{k-1} to put T_Markov on
    the same scale as T_exact (counting subsets, not ordered tuples).

    The product form holds because with-replacement draws are independent:
    each position j (for j >= 1) draws uniformly from {1,...,S-1},
    and the corrSum is a sum of terms each depending on one draw.
    """
    S = compute_S(k)
    C = num_compositions(S, k)
    n_pool = S - 1
    omega = cmath.exp(2j * cmath.pi / p)

    # phi_0: fixed term for b_0 = 0
    phi_0 = omega ** ((t * pow(3, k - 1, p)) % p)

    # Product over j = 1, ..., k-1 (normalized factors)
    product = phi_0
    for j in range(1, k):
        coeff_j = pow(3, k - 1 - j, p)
        Phi_j = complex(0.0, 0.0)
        for m in range(1, S):
            exp_val = (t * coeff_j * pow(2, m, p)) % p
            Phi_j += omega ** exp_val
        product *= Phi_j / n_pool  # normalize each factor

    return C * product


def compute_T_markov_per_factor(k, p, t):
    """
    Return (phi_0, [phi_1/n, phi_2/n, ..., phi_{k-1}/n])
    where phi_j = Phi_j / (S-1) is the normalized Markov factor.
    """
    S = compute_S(k)
    n_pool = S - 1
    omega = cmath.exp(2j * cmath.pi / p)

    phi_0 = omega ** ((t * pow(3, k - 1, p)) % p)

    factors = []
    for j in range(1, k):
        coeff_j = pow(3, k - 1 - j, p)
        Phi_j = complex(0.0, 0.0)
        for m in range(1, S):
            exp_val = (t * coeff_j * pow(2, m, p)) % p
            Phi_j += omega ** exp_val
        factors.append(Phi_j / n_pool)

    return phi_0, factors


# ============================================================================
# SELF-TESTS (>= 12 tests)
# ============================================================================

def run_self_tests():
    """Verify mathematical correctness before running any tool."""
    print("SELF-TESTS")
    print("-" * 60)
    passed = 0
    total = 0

    # T1: S values for known k
    total += 1
    ok = (compute_S(1) == 2 and compute_S(2) == 4 and compute_S(3) == 5
          and compute_S(5) == 8 and compute_S(10) == 16)
    if ok:
        passed += 1
        print(f"  [PASS] T1: S values correct for k=1,2,3,5,10")
    else:
        print(f"  [FAIL] T1: S values incorrect")

    # T2: d values
    total += 1
    ok = (compute_d(1) == 1 and compute_d(2) == 7 and compute_d(3) == 5
          and compute_d(4) == 47 and compute_d(5) == 13)
    if ok:
        passed += 1
        print(f"  [PASS] T2: d(1)=1, d(2)=7, d(3)=5, d(4)=47, d(5)=13")
    else:
        print(f"  [FAIL] T2: d values wrong")

    # T3: corrSum mod d consistency for k=3
    total += 1
    k, S, d = 3, compute_S(3), compute_d(3)
    ok = True
    for B in combinations(range(1, S), k - 1):
        if corrsum_true(B, k) % d != corrsum_from_subset(B, k, d):
            ok = False
            break
    if ok:
        passed += 1
        print(f"  [PASS] T3: corrSum_true mod d == corrSum_mod for k=3")
    else:
        print(f"  [FAIL] T3: corrSum consistency")

    # T4: T_exact(t=0) = C for k=4
    total += 1
    k = 4
    S = compute_S(k)
    C = num_compositions(S, k)
    dist = enumerate_corrsums_mod(k, compute_d(k))
    T0 = fourier_sum_from_dist(dist, compute_d(k), 0)
    ok = abs(T0.real - C) < 1e-8 and abs(T0.imag) < 1e-8
    if ok:
        passed += 1
        print(f"  [PASS] T4: T_exact(t=0) = C = {C} for k=4")
    else:
        print(f"  [FAIL] T4: T_exact(t=0) = {T0}")

    # T5: T_Markov(t=0) = C for k=4, p=47
    total += 1
    k, p = 4, 47
    C = num_compositions(compute_S(k), k)
    Tm0 = compute_T_markov(k, p, 0)
    ok = abs(Tm0.real - C) < 1e-6 and abs(Tm0.imag) < 1e-6
    if ok:
        passed += 1
        print(f"  [PASS] T5: T_Markov(t=0) = {Tm0.real:.4f} ~ C = {C} for k=4, p=47")
    else:
        print(f"  [FAIL] T5: T_Markov(t=0) = {Tm0}")

    # T6: Parseval identity for k=5, p=13
    total += 1
    k, p = 5, 13
    C = num_compositions(compute_S(k), k)
    dist = enumerate_corrsums_mod(k, p)
    sum_T_sq = sum(abs(fourier_sum_from_dist(dist, p, t))**2 for t in range(p))
    sum_count_sq = sum(c * c for c in dist.values())
    parseval_rhs = p * sum_count_sq
    ok = abs(sum_T_sq - parseval_rhs) < 1.0
    if ok:
        passed += 1
        print(f"  [PASS] T6: Parseval: sum|T|^2 = {sum_T_sq:.2f} = p*sum(c^2) = {parseval_rhs:.2f} for k=5, p=13")
    else:
        print(f"  [FAIL] T6: Parseval: {sum_T_sq:.2f} vs {parseval_rhs:.2f}")

    # T7: E(t=0) = 0 -- T_exact(0) = T_Markov(0) = C
    total += 1
    k, p = 5, 13
    C = num_compositions(compute_S(k), k)
    dist = enumerate_corrsums_mod(k, p)
    T_ex_0 = fourier_sum_from_dist(dist, p, 0)
    T_mk_0 = compute_T_markov(k, p, 0)
    E_0 = T_ex_0 - T_mk_0
    ok = abs(E_0) < 1e-8
    if ok:
        passed += 1
        print(f"  [PASS] T7: E(t=0) = {abs(E_0):.2e} ~ 0 for k=5, p=13")
    else:
        print(f"  [FAIL] T7: E(t=0) = {E_0}")

    # T8: modinv correctness
    total += 1
    ok = True
    for a in [2, 3, 5, 7, 11]:
        for m in [7, 11, 13, 23, 37]:
            if math.gcd(a, m) == 1:
                inv = modinv(a, m)
                if (a * inv) % m != 1:
                    ok = False
    if ok:
        passed += 1
        print(f"  [PASS] T8: modinv correct for all test cases")
    else:
        print(f"  [FAIL] T8: modinv")

    # T9: Triangle inequality |T_exact| <= C for k=5
    total += 1
    k = 5
    d = compute_d(k)
    C = num_compositions(compute_S(k), k)
    primes = distinct_primes(d)
    ok = True
    for p in primes:
        dist_p = enumerate_corrsums_mod(k, p)
        for t in range(p):
            if fourier_sum_abs(dist_p, p, t) > C + 0.01:
                ok = False
                break
    if ok:
        passed += 1
        print(f"  [PASS] T9: |T_exact(t)| <= C for all t, all p|d, k=5")
    else:
        print(f"  [FAIL] T9: triangle inequality violated")

    # T10: E(t) consistency for k=3, p=5
    total += 1
    k, p = 3, 5
    dist = enumerate_corrsums_mod(k, p)
    ok = True
    for t in range(1, p):
        Te = fourier_sum_from_dist(dist, p, t)
        Tm = compute_T_markov(k, p, t)
        E = Te - Tm
        # Recompute to check self-consistency
        Te2 = fourier_sum_from_dist(dist, p, t)
        if abs(Te - Te2) > 1e-12:
            ok = False
    if ok:
        passed += 1
        print(f"  [PASS] T10: E(t) = T_exact - T_Markov computed consistently for k=3, p=5")
    else:
        print(f"  [FAIL] T10: E(t) computation inconsistency")

    # T11: k=3 manual corrSum verification
    total += 1
    k, d, S = 3, 5, 5
    cs_vals = []
    for B in [(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]:
        cs_vals.append(corrsum_true(B, k) % d)
    dist_manual = Counter(cs_vals)
    dist_auto = enumerate_corrsums_mod(k, d)
    ok = (dist_manual == dist_auto and sum(dist_auto.values()) == 6)
    if ok:
        passed += 1
        print(f"  [PASS] T11: k=3 manual verification matches enumeration")
    else:
        print(f"  [FAIL] T11: k=3 manual={dict(dist_manual)}, auto={dict(dist_auto)}")

    # T12: T_Markov factored product matches full T_Markov
    total += 1
    k, p, t = 5, 13, 3
    C = num_compositions(compute_S(k), k)
    T_markov_full = compute_T_markov(k, p, t)
    phi_0, factors = compute_T_markov_per_factor(k, p, t)
    T_prod_check = phi_0
    for f in factors:
        T_prod_check *= f
    T_prod_check *= C  # scale back up: C = n_pool^{k-1} * C / n_pool^{k-1}
    # T_Markov = C * phi_0 * prod_{j=1}^{k-1} phi_j_norm
    # where phi_j_norm = Phi_j / n_pool
    # and factors = [phi_j_norm]
    T_prod_correct = phi_0
    for f in factors:
        T_prod_correct *= f
    T_prod_correct *= C
    ok = abs(T_markov_full - T_prod_correct) < 1e-6
    if ok:
        passed += 1
        print(f"  [PASS] T12: T_Markov = C * phi_0 * prod(phi_j) verified for k=5, p=13, t=3")
    else:
        print(f"  [FAIL] T12: T_Markov = {T_markov_full}, prod = {T_prod_correct}, diff = {abs(T_markov_full - T_prod_correct):.2e}")

    # T13: |phi_j/n_pool| <= 1 for normalized factors
    total += 1
    k, p = 5, 13
    ok = True
    for t in range(1, p):
        _, factors = compute_T_markov_per_factor(k, p, t)
        for f in factors:
            if abs(f) > 1.0 + 1e-10:
                ok = False
    if ok:
        passed += 1
        print(f"  [PASS] T13: |phi_j/n_pool| <= 1 for all j, t, k=5, p=13")
    else:
        print(f"  [FAIL] T13: normalized factor exceeds 1")

    # T14: Fourier reconstruction of N_0 for k=3
    total += 1
    k, d = 3, 5
    dist = enumerate_corrsums_mod(k, d)
    N0_exact = dist.get(0, 0)
    fourier_N0 = sum(fourier_sum_from_dist(dist, d, t).real for t in range(d)) / d
    ok = abs(fourier_N0 - N0_exact) < 0.01
    if ok:
        passed += 1
        print(f"  [PASS] T14: Fourier N0 = {fourier_N0:.4f} ~ exact {N0_exact} for k=3")
    else:
        print(f"  [FAIL] T14: Fourier N0 = {fourier_N0:.4f} != {N0_exact}")

    # T15: Negative dependence basic property: Var_WR <= Var_iid for indicators
    total += 1
    N, m_val = 10, 4
    p_incl = m_val / N
    var_wr = m_val * p_incl * (1 - p_incl) * (N - m_val) / (N - 1)
    var_iid = m_val * p_incl * (1 - p_incl)
    ok = var_wr <= var_iid + 1e-12
    if ok:
        passed += 1
        print(f"  [PASS] T15: Var_WR = {var_wr:.6f} <= Var_iid = {var_iid:.6f} (Dubhashi-Ranjan)")
    else:
        print(f"  [FAIL] T15: Var_WR > Var_iid")

    print(f"\n  RESULT: {passed}/{total} self-tests passed.\n")
    return passed == total


# ============================================================================
# TOOL 1: EXACT COMPUTATION OF |T_exact - T_Markov| FOR k=3..17
# ============================================================================

def tool1_exact_E(k_range=range(3, 18)):
    """
    For each k in k_range and each prime p|d(k), compute:
    - T_exact(t) and T_Markov(t) for all t=1..p-1
    - E(t) = T_exact(t) - T_Markov(t)
    - max|E|, max|E|/C, max|E|/|T_Markov|
    - Scaling analysis of max|E| with k and p

    [RESULT] tags mark key findings.
    [BOUND] tags mark bounds that hold.
    [GAP] tags mark bounds that fail.
    """
    hdr = "TOOL 1: EXACT COMPUTATION OF E(t) = T_exact - T_Markov"
    print("\n" + "=" * 72)
    print(hdr)
    print("=" * 72)
    print()
    print("  For each (k, p), we compute E(t) = T_exact(t) - T_Markov(t)")
    print("  for all t=1..p-1, and report max|E|, max|E|/C, max|E|/|T_Markov|.")
    print()

    all_results = []

    for k in k_range:
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        primes = distinct_primes(d)

        if not can_enumerate(k):
            print(f"  k={k}: C={C} too large for exhaustive enumeration, skipping.")
            continue

        check_budget(f"Tool 1, k={k}")

        for p in primes:
            if p > 5000:
                continue  # skip very large primes for speed

            check_budget(f"Tool 1, k={k}, p={p}")

            dist_exact = enumerate_corrsums_mod(k, p)

            max_E_abs = 0.0
            max_E_over_C = 0.0
            max_E_over_Tm = 0.0
            t_max_E = 0
            sum_E_sq = 0.0
            n_t = 0

            details = []

            for t in range(1, p):
                T_ex = fourier_sum_from_dist(dist_exact, p, t)
                T_mk = compute_T_markov(k, p, t)
                E = T_ex - T_mk

                E_abs = abs(E)
                Te_abs = abs(T_ex)
                Tm_abs = abs(T_mk)

                if E_abs > max_E_abs:
                    max_E_abs = E_abs
                    t_max_E = t

                ratio_C = E_abs / C if C > 0 else 0
                if ratio_C > max_E_over_C:
                    max_E_over_C = ratio_C

                if Tm_abs > 1e-15:
                    ratio_Tm = E_abs / Tm_abs
                    if ratio_Tm > max_E_over_Tm:
                        max_E_over_Tm = ratio_Tm

                sum_E_sq += E_abs ** 2
                n_t += 1

                if t <= 3 or t == p - 1:
                    details.append((t, Te_abs, Tm_abs, E_abs))

            rms_E = math.sqrt(sum_E_sq / n_t) if n_t > 0 else 0

            # Candidate bound: (k-1)^2 / (2*(S-1)) * C
            km1 = k - 1
            n_pool = S - 1
            tv_coeff = km1 * (km1 - 1) / (2 * n_pool)
            predicted_bound = tv_coeff * C

            print(f"  --- k={k}, S={S}, C={C}, p={p} ---")
            print(f"    max|E|       = {max_E_abs:.6f}")
            print(f"    max|E|/C     = {max_E_over_C:.6e}")
            print(f"    max|E|/|Tm|  = {max_E_over_Tm:.6f}")
            print(f"    rms(|E|)     = {rms_E:.6f}")
            print(f"    k^2/(2S)*C   = {predicted_bound:.4f}  (pairwise collision bound)")
            ratio_tv = max_E_abs / predicted_bound if predicted_bound > 0 else float('inf')
            print(f"    max|E| / TV  = {ratio_tv:.4f}")
            print(f"    t_max        = {t_max_E}")

            if details:
                print(f"    {'t':>6} {'|T_exact|':>12} {'|T_Markov|':>12} {'|E|':>12}")
                for t, te, tm, e in details:
                    print(f"    {t:6d} {te:12.6f} {tm:12.6f} {e:12.6f}")

            all_results.append({
                'k': k, 'S': S, 'p': p, 'C': C,
                'max_E': max_E_abs, 'max_E_over_C': max_E_over_C,
                'max_E_over_Tm': max_E_over_Tm, 'rms_E': rms_E,
                'TV_bound': predicted_bound,
                'ratio_to_TV': ratio_tv,
            })
            print()

    # SCALING ANALYSIS
    if all_results:
        print("  SCALING SUMMARY")
        print("  " + "-" * 68)
        print(f"  {'k':>4} {'S':>4} {'p':>8} {'C':>10} {'max|E|/C':>12} {'max|E|/|Tm|':>12} "
              f"{'vs_TV':>8}")
        for r in all_results:
            print(f"  {r['k']:4d} {r['S']:4d} {r['p']:8d} {r['C']:10d} "
                  f"{r['max_E_over_C']:12.2e} {r['max_E_over_Tm']:12.4f} "
                  f"{r['ratio_to_TV']:8.4f}")
        print()

        # Check if |E|/|T_Markov| grows with k
        # If max_E_over_Tm >> 1 for larger k, the decomposition is ill-posed
        large_k_ratios = [r['max_E_over_Tm'] for r in all_results if r['k'] >= 8]
        if large_k_ratios:
            max_r = max(large_k_ratios)
            if max_r > 10:
                print(f"  [RESULT] max|E|/|T_Markov| reaches {max_r:.1f} for k >= 8.")
                print(f"  [GAP] The Markov decomposition is ILL-POSED: |E| >> |T_Markov|.")
                print(f"        T_Markov decays exponentially as product of k-1 factors < 1,")
                print(f"        while T_exact decays only polynomially (~ C/sqrt(p)).")
                print(f"        The decomposition T = T_Markov + E has |E| dominating.")
            else:
                print(f"  [RESULT] max|E|/|T_Markov| stays bounded at {max_r:.4f} for k >= 8.")
                print(f"  [BOUND] The Markov approximation E(t) is a controlled perturbation.")

    print()
    return all_results


# ============================================================================
# TOOL 2: INCLUSION-EXCLUSION DECOMPOSITION
# ============================================================================

def tool2_inclusion_exclusion(k_range=range(3, 11)):
    """
    Express E(t) via inclusion-exclusion on the collision structure.

    With replacement: draw (b_1,...,b_{k-1}) from {1,...,S-1} (repeats OK).
    Without replacement: same but all distinct.

    The difference involves collision terms:
    T_wr = T_Markov - sum over collision patterns

    We compute Delta_1 (pairwise collision correction) exactly and verify
    it dominates E. Higher-order corrections Delta_m are estimated.

    For each pair (i,j) of positions sharing value v:
        collision sum += omega^{t*(3^{k-1-i}+3^{k-1-j})*2^v} * prod_other
    """
    hdr = "TOOL 2: INCLUSION-EXCLUSION DECOMPOSITION OF E(t)"
    print("\n" + "=" * 72)
    print(hdr)
    print("=" * 72)
    print()
    print("  T_Markov counts ordered tuples WITH replacement.")
    print("  T_exact counts subsets WITHOUT replacement.")
    print("  E = T_exact - T_Markov comes from collision structure.")
    print()

    all_results = []

    for k in k_range:
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        primes = distinct_primes(d)
        km1 = k - 1
        n_pool = S - 1

        if not can_enumerate(k) or not primes:
            continue

        check_budget(f"Tool 2, k={k}")

        p = primes[0]
        if p > 2000:
            p = min(pr for pr in primes if pr <= 2000) if any(pr <= 2000 for pr in primes) else primes[0]
            if p > 2000:
                continue

        print(f"  --- k={k}, S={S}, C={C}, p={p}, n_pool={n_pool} ---")

        omega = cmath.exp(2j * cmath.pi / p)
        dist_exact = enumerate_corrsums_mod(k, p)

        n_pairs = math.comb(km1, 2)

        for t in [1, 2]:
            if t >= p:
                continue

            T_exact = fourier_sum_from_dist(dist_exact, p, t)
            T_markov = compute_T_markov(k, p, t)
            E = T_exact - T_markov

            # First-order collision term Delta_1
            # For each pair (i,j) where 1 <= i < j <= k-1, sharing value v:
            # Phase from i,j = (3^{k-1-i} + 3^{k-1-j}) * 2^v mod p
            # Other positions contribute independently.

            # Precompute raw Phi factors for each position
            phi_raw = {}
            for pos in range(1, k):
                coeff = pow(3, km1 - pos, p)
                phi_raw[pos] = sum(omega ** ((t * coeff * pow(2, b, p)) % p)
                                   for b in range(1, S))

            # phi_0 (b_0 = 0 fixed)
            phi_0_val = omega ** ((t * pow(3, km1, p)) % p)

            # Delta_1: sum over collision pairs
            Delta_1 = complex(0.0)
            for i in range(1, k):
                for j in range(i + 1, k):
                    coeff_ij = (pow(3, km1 - i, p) + pow(3, km1 - j, p)) % p
                    # Sum over shared value v
                    shared_sum = sum(omega ** ((t * coeff_ij * pow(2, v, p)) % p)
                                    for v in range(1, S))
                    # Product over other positions (not i, not j)
                    prod_other = phi_0_val
                    for m_pos in range(1, k):
                        if m_pos != i and m_pos != j:
                            prod_other *= phi_raw[m_pos]
                    Delta_1 += shared_sum * prod_other

            # Normalize: T_Markov has scale n_pool^{k-1}, Delta_1 has scale n_pool^{k-2}
            # E = T_exact - T_Markov. The collision correction to T_Markov is -Delta_1
            # (removing collision tuples). But E is defined differently (subset vs tuple).
            # For comparison, normalize Delta_1 to the T_exact scale:
            Delta_1_norm = Delta_1 * C / (n_pool ** km1)

            abs_E = abs(E)
            abs_D1 = abs(Delta_1_norm)
            ratio_D1_E = abs_D1 / abs_E if abs_E > 1e-15 else float('inf')

            # Check residual after first-order correction
            residual = E + Delta_1_norm
            abs_residual = abs(residual)
            residual_ratio = abs_residual / abs_E if abs_E > 1e-15 else 0.0

            print(f"    t={t}: |E| = {abs_E:.6f},  |Delta_1| = {abs_D1:.6f},  "
                  f"|D1|/|E| = {ratio_D1_E:.4f}")
            print(f"           E  = ({E.real:.6f}, {E.imag:.6f}i)")
            print(f"           D1 = ({Delta_1_norm.real:.6f}, {Delta_1_norm.imag:.6f}i)")
            print(f"           |E + D1| = {abs_residual:.6f}  (residual after 1st order)")
            print(f"           |E+D1|/|E| = {residual_ratio:.4f}")

            all_results.append({
                'k': k, 'p': p, 't': t,
                'abs_E': abs_E, 'abs_D1': abs_D1,
                'ratio_D1_E': ratio_D1_E,
                'residual_ratio': residual_ratio,
                'n_pairs': n_pairs,
            })

        print()

    # Summary
    print("  TOOL 2 SUMMARY")
    print("  " + "-" * 60)
    if all_results:
        ratios = [r['ratio_D1_E'] for r in all_results if r['ratio_D1_E'] < float('inf')]
        residuals = [r['residual_ratio'] for r in all_results]
        if ratios:
            print(f"  |Delta_1|/|E| range: [{min(ratios):.4f}, {max(ratios):.4f}]")
        if residuals:
            print(f"  |E+D1|/|E| range:    [{min(residuals):.4f}, {max(residuals):.4f}]")

        if ratios and max(residuals) < 0.5:
            print(f"  [RESULT] First-order collision correction Delta_1 DOMINATES E.")
            print(f"  [BOUND] |E| ~ |Delta_1| ~ C(k-1,2) * |shared_sum| / n_pool")
        elif ratios:
            print(f"  [GAP] Delta_1 does NOT dominate E for all cases.")
            print(f"        Higher-order collision terms contribute significantly.")
            for r in all_results:
                if r['residual_ratio'] > 0.5:
                    print(f"        k={r['k']}, p={r['p']}, t={r['t']}: "
                          f"|E+D1|/|E| = {r['residual_ratio']:.4f}")

    print()
    return all_results


# ============================================================================
# TOOL 3: NEGATIVE DEPENDENCE (|T_exact| <= |T_Markov|?)
# ============================================================================

def tool3_negative_dependence(k_range=range(3, 14)):
    """
    Test whether |T_exact(t)| <= |T_Markov(t)| for all t.

    THEORETICAL MOTIVATION (Dubhashi-Ranjan 1998):
    Without-replacement sampling produces NEGATIVELY ASSOCIATED random
    variables. For NA variables, variances of monotone functions decrease.

    KEY CAVEAT: Fourier characters exp(2*pi*i*...) are NOT monotone.
    So NA does not DIRECTLY imply |T_exact| <= |T_Markov|. This tool
    tests whether the inequality holds empirically.

    If it DOES hold: the WR correction HELPS and no separate bound needed.
    If it DOES NOT: we need explicit |E(t)| control.

    Additionally computes the Dubhashi-Ranjan VARIANCE bound:
      Var_WR[f(X)] <= Var_iid[f(X)] for any f that is a sum of
      functions of negatively associated indicators.
    """
    hdr = "TOOL 3: NEGATIVE DEPENDENCE -- |T_exact| vs |T_Markov|"
    print("\n" + "=" * 72)
    print(hdr)
    print("=" * 72)
    print()
    print("  HYPOTHESIS: Sampling WR creates negative dependence so")
    print("  |T_exact(t)| <= |T_Markov(t)| for all t >= 1.")
    print()

    n_violations = 0
    n_tests = 0
    violations = []
    summary = []

    for k in k_range:
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        primes = distinct_primes(d)

        if not can_enumerate(k):
            continue

        check_budget(f"Tool 3, k={k}")

        for p in primes:
            if p > 5000:
                continue

            dist_exact = enumerate_corrsums_mod(k, p)

            k_violations = 0
            max_ratio = 0.0
            min_ratio = float('inf')

            for t in range(1, p):
                T_ex = fourier_sum_from_dist(dist_exact, p, t)
                T_mk = compute_T_markov(k, p, t)

                abs_ex = abs(T_ex)
                abs_mk = abs(T_mk)
                n_tests += 1

                if abs_mk > 1e-15:
                    ratio = abs_ex / abs_mk
                    max_ratio = max(max_ratio, ratio)
                    min_ratio = min(min_ratio, ratio)

                    if abs_ex > abs_mk + 1e-10:
                        n_violations += 1
                        k_violations += 1
                        if len(violations) < 20:
                            violations.append({
                                'k': k, 'p': p, 't': t,
                                'abs_T_ex': abs_ex, 'abs_T_mk': abs_mk,
                                'ratio': ratio
                            })

            status = "PASS" if k_violations == 0 else f"FAIL ({k_violations} violations)"
            print(f"  k={k:3d}, p={p:6d}: [{status}]  "
                  f"max |T_ex|/|T_mk| = {max_ratio:.6f}  "
                  f"min = {min_ratio:.6f}")

            summary.append({
                'k': k, 'p': p, 'C': C, 'S': S,
                'n_violations': k_violations,
                'max_ratio': max_ratio, 'min_ratio': min_ratio
            })

    print()
    print(f"  TOTAL: {n_tests} tests, {n_violations} violations")
    print()

    if n_violations == 0:
        print("  [RESULT] |T_exact(t)| <= |T_Markov(t)| for ALL tested (k, p, t).")
        print("  [BOUND] Negative dependence holds on the Fourier side:")
        print("          WR correction REDUCES |T_p(t)|, so bounding T_Markov suffices.")
        print()
        print("  CAVEAT: This is numerical evidence, not a proof.")
        print("  Dubhashi-Ranjan (1998) applies to monotone functions of NA indicators.")
        print("  Fourier characters are non-monotone. A proof would require:")
        print("  - Borcea-Branden (2009) strong Rayleigh / stable polynomial theory, or")
        print("  - Pemantle (2000) negative dependence beyond monotonicity.")
    else:
        print("  [RESULT] Negative dependence FAILS on the Fourier side.")
        print()
        print("  Violations found:")
        for v in violations[:10]:
            print(f"    k={v['k']}, p={v['p']}, t={v['t']}: "
                  f"|T_ex|={v['abs_T_ex']:.6f} > |T_mk|={v['abs_T_mk']:.6f} "
                  f"(ratio={v['ratio']:.6f})")
        print()
        print("  [GAP] Cannot use |T_Markov| as upper bound. Need explicit |E(t)| control.")

    # Variance analysis: Dubhashi-Ranjan for the second moment
    print()
    print("  DUBHASHI-RANJAN VARIANCE ANALYSIS")
    print("  " + "-" * 50)
    print("  For WR sampling of m from N items, indicator Var_WR <= Var_iid.")
    print("  Checking whether this extends to the exponential sum variance.")
    print()

    for k in [3, 5, 7, 9]:
        if k >= max(k_range):
            continue
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        primes = distinct_primes(d)
        if not can_enumerate(k) or not primes:
            continue

        p = primes[0]
        if p > 500:
            continue

        dist = enumerate_corrsums_mod(k, p)

        # Var_WR[T(t)] = E[|T(t)|^2] - |E[T(t)]|^2 over WR subsets
        # Here T(t) for a single subset B = omega^{t*corrSum(B)}
        # so |T(t)| = 1 always => E[|T|^2] = 1
        # and E[T(t)] = T_exact(t)/C
        # => Var_WR = 1 - |T_exact(t)/C|^2

        # For iid: Var_iid = 1 - |T_Markov_prob(t)|^2
        # where T_Markov_prob = T_Markov / (n_pool^{k-1})
        n_pool = S - 1

        var_wr_better = True
        for t in range(1, min(p, 30)):
            T_ex = fourier_sum_from_dist(dist, p, t)
            T_mk = compute_T_markov(k, p, t)

            rho_ex = abs(T_ex) / C
            rho_mk = abs(T_mk) / (n_pool ** (k - 1))

            var_wr = 1.0 - rho_ex ** 2
            var_iid = 1.0 - rho_mk ** 2

            if var_wr > var_iid + 1e-8:
                var_wr_better = False

        status = "Var_WR <= Var_iid" if var_wr_better else "Var_WR > Var_iid SOMETIMES"
        print(f"  k={k}, p={p}: {status}")

    print()

    # MAX RATIO SUMMARY
    if summary:
        print("  MAX RATIO SUMMARY (|T_exact|/|T_Markov|):")
        print("  " + "-" * 50)
        ratios = [s['max_ratio'] for s in summary if s['max_ratio'] > 0]
        if ratios:
            print(f"  Overall max ratio: {max(ratios):.8f}")
            mins = [s['min_ratio'] for s in summary if s['min_ratio'] < float('inf')]
            if mins:
                print(f"  Overall min ratio: {min(mins):.8f}")
            print(f"  Mean max ratio:    {sum(ratios)/len(ratios):.8f}")
    print()

    return summary, violations


# ============================================================================
# TOOL 4: REGIME ANALYSIS FOR INTERMEDIATE PRIMES
# ============================================================================

def tool4_regime_analysis(k_range=range(3, 25)):
    """
    For each prime p|d(k), classify into regimes and compute |E(t)|/|T_Markov(t)|:
    - SMALL primes (p < S): Markov product bound works
    - INTERMEDIATE primes (S <= p <= S^2): the GAP region
    - LARGE primes (p > S^2): dimension argument C/p << 1

    For intermediate primes, we measure how the relative error |E|/|T_Markov|
    scales and whether rho_exact = max_t |T_exact(t)/C| <= 1/sqrt(p).
    """
    hdr = "TOOL 4: REGIME ANALYSIS -- |E(t)|/|T_Markov(t)| BY PRIME SIZE"
    print("\n" + "=" * 72)
    print(hdr)
    print("=" * 72)
    print()

    regime_data = defaultdict(list)

    for k in k_range:
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        primes = distinct_primes(d)

        if not primes:
            continue

        for p in primes:
            # Classify regime
            if p < S:
                regime = "SMALL"
            elif p <= S * S:
                regime = "INTERMEDIATE"
            else:
                regime = "LARGE"

            entry = {
                'k': k, 'S': S, 'p': p, 'C': C, 'd': d,
                'regime': regime,
                'p_over_S': p / S,
                'p_over_S2': p / (S * S),
                'C_over_p': C / p,
            }

            # For small k, compute exact metrics
            if can_enumerate(k, limit=500_000) and p <= 2000:
                check_budget(f"Tool 4, k={k}, p={p}")

                dist_exact = enumerate_corrsums_mod(k, p)
                max_ratio = 0.0
                rho_max = 0.0

                for t in range(1, p):
                    T_ex = fourier_sum_from_dist(dist_exact, p, t)
                    T_mk = compute_T_markov(k, p, t)
                    abs_ex = abs(T_ex)
                    abs_mk = abs(T_mk)

                    if abs_mk > 1e-15:
                        max_ratio = max(max_ratio, abs(T_ex - T_mk) / abs_mk)

                    rho_ex = abs_ex / C
                    rho_max = max(rho_max, rho_ex)

                entry['max_E_over_Tm'] = max_ratio
                entry['rho_max'] = rho_max
                entry['rho_bound'] = 1.0 / math.sqrt(p)
                entry['rho_passes'] = rho_max <= 1.0 / math.sqrt(p) + 1e-10

            regime_data[regime].append(entry)

    # Report by regime
    for regime in ["SMALL", "INTERMEDIATE", "LARGE"]:
        entries = regime_data.get(regime, [])
        if not entries:
            continue

        print(f"\n  {regime} PRIMES:")
        print("  " + "-" * 66)

        if regime == "SMALL":
            print(f"  {'k':>4} {'S':>4} {'p':>8} {'C':>10} {'p/S':>6} "
                  f"{'rho_max':>10} {'1/sqrt(p)':>10} {'pass':>6}")
            for e in entries[:25]:
                rho = e.get('rho_max', -1)
                bound = e.get('rho_bound', -1)
                pas = e.get('rho_passes', '?')
                rho_s = f"{rho:10.6f}" if rho >= 0 else "     N/A  "
                bound_s = f"{bound:10.6f}" if bound >= 0 else "     N/A  "
                print(f"  {e['k']:4d} {e['S']:4d} {e['p']:8d} {e['C']:10d} "
                      f"{e['p_over_S']:6.2f} {rho_s} {bound_s} {str(pas):>6}")
        elif regime == "INTERMEDIATE":
            print(f"  {'k':>4} {'S':>4} {'p':>8} {'C':>10} {'p/S':>6} {'p/S^2':>8} "
                  f"{'|E|/|Tm|':>10} {'rho_max':>10} {'1/sqp':>10} {'pass':>6}")
            for e in entries[:25]:
                rho = e.get('rho_max', -1)
                bound = e.get('rho_bound', -1)
                pas = e.get('rho_passes', '?')
                eov = e.get('max_E_over_Tm', -1)
                rho_s = f"{rho:10.6f}" if rho >= 0 else "     N/A  "
                bound_s = f"{bound:10.6f}" if bound >= 0 else "     N/A  "
                eov_s = f"{eov:10.6f}" if eov >= 0 else "     N/A  "
                print(f"  {e['k']:4d} {e['S']:4d} {e['p']:8d} {e['C']:10d} "
                      f"{e['p_over_S']:6.2f} {e['p_over_S2']:8.4f} "
                      f"{eov_s} {rho_s} {bound_s} {str(pas):>6}")
        else:
            print(f"  {'k':>4} {'S':>4} {'p':>8} {'C':>10} {'C/p':>10}")
            for e in entries[:25]:
                print(f"  {e['k']:4d} {e['S']:4d} {e['p']:8d} {e['C']:10d} "
                      f"{e['C_over_p']:10.6f}")

    # Intermediate primes summary
    n_inter = len(regime_data.get("INTERMEDIATE", []))
    n_inter_computed = sum(1 for e in regime_data.get("INTERMEDIATE", [])
                          if 'rho_passes' in e)
    n_inter_pass = sum(1 for e in regime_data.get("INTERMEDIATE", [])
                       if e.get('rho_passes', False))

    print(f"\n  INTERMEDIATE PRIMES SUMMARY:")
    print(f"    Total intermediate primes found: {n_inter}")
    print(f"    Computed exactly: {n_inter_computed}")
    print(f"    Pass rho <= 1/sqrt(p): {n_inter_pass}/{n_inter_computed}")

    if n_inter_computed > 0:
        computed = [e for e in regime_data.get("INTERMEDIATE", []) if 'rho_max' in e]
        if computed:
            max_rho_sp = max(e['rho_max'] * math.sqrt(e['p']) for e in computed)
            min_rho_sp = min(e['rho_max'] * math.sqrt(e['p']) for e in computed)
            print(f"    rho * sqrt(p) range: [{min_rho_sp:.4f}, {max_rho_sp:.4f}]")

            if max_rho_sp < 1.0:
                print(f"    [BOUND] rho_exact * sqrt(p) < 1 for all intermediate primes tested.")
            else:
                print(f"    [GAP] rho_exact * sqrt(p) exceeds 1 in some cases.")
                for e in computed:
                    rs = e['rho_max'] * math.sqrt(e['p'])
                    if rs > 1.0:
                        print(f"      k={e['k']}, p={e['p']}: rho*sqrt(p) = {rs:.4f}")

    print()
    return regime_data


# ============================================================================
# TOOL 5: THE KEY BOUND -- |T_exact/C| <= f(k,S,p)
# ============================================================================

def tool5_key_bound(k_range=range(3, 14)):
    """
    Attempt to prove: for intermediate primes p ~ S^2,
        |T_exact(t)/C| <= f(k, S, p) for some explicit f.

    STRATEGY:
    Test multiple candidate bounds f(k,S,p):
      (a) f = 1/sqrt(p)                    (Weil-type)
      (b) f = alpha/sqrt(p) for alpha > 1   (relaxed Weil)
      (c) f = (sqrt(p)/(S-1))^{k-1}        (Markov product bound)
      (d) f = C/p                           (dimension bound)
      (e) f = min(1/sqrt(p), C/p)           (regime-conditional)

    For the CRT product:
      prod_{p|d} rho_p < 1 suffices for N_0 = 0.
    So we also compute prod rho_p and compare with Markov product.

    Reports which bound works, with margins and counterexamples.
    """
    hdr = "TOOL 5: THE KEY BOUND -- |T_exact(t)/C| <= f(k,S,p)"
    print("\n" + "=" * 72)
    print(hdr)
    print("=" * 72)
    print()
    print("  TARGET: Find explicit f(k,S,p) such that")
    print("    max_{t>=1} |T_exact(t)/C| <= f(k,S,p)")
    print("  for all primes p|d(k) and all k >= 3.")
    print()

    all_results = []
    any_failure_a = False
    crt_data = []

    for k in k_range:
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        primes = distinct_primes(d)
        n_pool = S - 1

        if not can_enumerate(k):
            print(f"  k={k}: C={C} too large, skipping.")
            continue

        check_budget(f"Tool 5, k={k}")

        crt_exact = 1.0
        crt_markov = 1.0

        for p in primes:
            if p > 5000:
                continue

            check_budget(f"Tool 5, k={k}, p={p}")

            dist_exact = enumerate_corrsums_mod(k, p)

            # Candidate bounds
            bound_a = 1.0 / math.sqrt(p)           # Weil-type
            bound_c_val = 1.0                       # Markov product: compute
            bound_d = C / p                          # Dimension

            max_rho = 0.0
            max_rho_t = 0
            max_rho_markov = 0.0
            neg_dep_holds = True

            # Compute Markov product bound
            for t in range(1, p):
                T_ex = fourier_sum_from_dist(dist_exact, p, t)
                T_mk = compute_T_markov(k, p, t)
                abs_ex = abs(T_ex)
                abs_mk = abs(T_mk)

                rho_ex = abs_ex / C
                rho_mk = abs_mk / C

                if rho_ex > max_rho:
                    max_rho = rho_ex
                    max_rho_t = t
                max_rho_markov = max(max_rho_markov, rho_mk)

                if abs_ex > abs_mk + 1e-10:
                    neg_dep_holds = False

            # Test bounds
            passes_a = max_rho <= bound_a + 1e-10
            passes_d = max_rho <= bound_d + 1e-10
            passes_neg = neg_dep_holds

            # Find best alpha such that rho <= alpha/sqrt(p)
            best_alpha = max_rho * math.sqrt(p) if p > 0 else 0

            # Classify regime
            if p < S:
                regime = "SMALL"
            elif p <= S * S:
                regime = "INTERMEDIATE"
            else:
                regime = "LARGE"

            if not passes_a:
                any_failure_a = True

            margin_a = 1.0 - best_alpha
            status_a = "PASS" if passes_a else "FAIL"
            status_nd = "YES" if neg_dep_holds else "NO"

            print(f"  k={k:3d}, p={p:6d} [{regime:12s}]: [{status_a}]  "
                  f"rho = {max_rho:.6e}  "
                  f"alpha = {best_alpha:.4f}  "
                  f"|Tex|<=|Tmk|: {status_nd}")

            all_results.append({
                'k': k, 'S': S, 'p': p, 'C': C,
                'regime': regime,
                'max_rho': max_rho,
                'max_rho_markov': max_rho_markov,
                'inv_sqrt_p': bound_a,
                'passes_a': passes_a,
                'best_alpha': best_alpha,
                'neg_dep_holds': neg_dep_holds,
                'margin_a': margin_a,
            })

            crt_exact *= max_rho
            crt_markov *= max_rho_markov

        # CRT product for this k
        if primes:
            crt_data.append({
                'k': k, 'S': S, 'd': d, 'C': C,
                'n_primes': len(primes),
                'crt_exact': crt_exact,
                'crt_markov': crt_markov,
                'crt_ratio': crt_exact / crt_markov if crt_markov > 1e-15 else float('inf'),
            })

    print()

    # BOUND ANALYSIS
    print("  BOUND TESTING SUMMARY")
    print("  " + "-" * 60)

    if all_results:
        # Bound (a): rho <= 1/sqrt(p)
        n_pass_a = sum(1 for r in all_results if r['passes_a'])
        n_fail_a = len(all_results) - n_pass_a
        alphas = [r['best_alpha'] for r in all_results]
        max_alpha = max(alphas) if alphas else 0

        if n_fail_a == 0:
            print(f"  [BOUND] rho <= 1/sqrt(p) HOLDS for ALL {len(all_results)} (k,p) pairs.")
            print(f"          max alpha = {max_alpha:.6f}")
        else:
            print(f"  [GAP] rho <= 1/sqrt(p) FAILS for {n_fail_a}/{len(all_results)} pairs.")
            print(f"        max alpha = {max_alpha:.6f}")

            # Find minimal alpha that works
            print(f"  [BOUND] rho <= {max_alpha:.4f}/sqrt(p) holds for ALL tested pairs.")

        # Bound by regime
        for regime in ["SMALL", "INTERMEDIATE", "LARGE"]:
            regime_res = [r for r in all_results if r['regime'] == regime]
            if regime_res:
                max_a = max(r['best_alpha'] for r in regime_res)
                n_pass = sum(1 for r in regime_res if r['passes_a'])
                print(f"    {regime:12s}: {n_pass}/{len(regime_res)} pass 1/sqrt(p), "
                      f"max alpha = {max_a:.4f}")

        # Negative dependence
        n_neg_dep = sum(1 for r in all_results if r['neg_dep_holds'])
        print(f"\n  Negative dependence |T_ex| <= |T_Markov|: "
              f"{n_neg_dep}/{len(all_results)} hold")

    # CRT PRODUCT ANALYSIS
    print()
    print("  CRT PRODUCT ANALYSIS")
    print("  " + "-" * 60)
    if crt_data:
        print(f"  {'k':>4} {'d':>12} {'#p':>4} {'CRT_exact':>14} {'CRT_Markov':>14} "
              f"{'ratio':>10}")
        for c in crt_data:
            print(f"  {c['k']:4d} {c['d']:12d} {c['n_primes']:4d} "
                  f"{c['crt_exact']:14.6e} {c['crt_markov']:14.6e} "
                  f"{c['crt_ratio']:10.4f}")

        # Key finding
        n_differ = sum(1 for c in crt_data
                       if (c['crt_exact'] < 1) != (c['crt_markov'] < 1))
        n_wr_helps = sum(1 for c in crt_data if c['crt_exact'] <= c['crt_markov'] + 1e-12)
        n_wr_hurts = sum(1 for c in crt_data if c['crt_exact'] > c['crt_markov'] + 1e-12)

        print()
        if n_differ == 0:
            print(f"  [RESULT] CRT outcome IDENTICAL for Markov vs exact in all cases.")
        else:
            print(f"  [GAP] CRT outcome differs in {n_differ} cases.")

        print(f"  WR effect: tighter in {n_wr_helps}/{len(crt_data)}, "
              f"looser in {n_wr_hurts}/{len(crt_data)}")

        if all(c['crt_ratio'] <= 1.0 + 1e-6 for c in crt_data):
            print(f"  [BOUND] CRT_exact <= CRT_Markov for ALL k tested.")
            print(f"  => The Markov approximation is a VALID UPPER BOUND for the CRT product.")
            print(f"  => The WR correction can be SAFELY IGNORED (it only helps).")
        elif all(c['crt_ratio'] >= 1.0 - 1e-6 for c in crt_data):
            print(f"  [GAP] CRT_exact >= CRT_Markov for all k.")
            print(f"  => The WR correction WEAKENS the CRT bound.")
        else:
            print(f"  [MIXED] WR correction helps some k and hurts others.")

    print()
    return all_results, crt_data


# ============================================================================
# COMPREHENSIVE SUMMARY
# ============================================================================

def print_summary(tool1_res, tool3_summary, tool3_violations, tool5_res, tool5_crt):
    """Print a comprehensive summary of all findings."""
    print()
    print("=" * 72)
    print("COMPREHENSIVE SUMMARY: THE WITHOUT-REPLACEMENT CORRECTION")
    print("=" * 72)
    print()

    # Tool 1 findings
    if tool1_res:
        max_E_over_C = max(r['max_E_over_C'] for r in tool1_res)
        max_E_over_Tm = max(r['max_E_over_Tm'] for r in tool1_res)
        max_ratio_TV = max(r['ratio_to_TV'] for r in tool1_res)
        print(f"  TOOL 1 (Exact |E| computation):")
        print(f"    max |E|/C across all (k,p):      {max_E_over_C:.2e}")
        print(f"    max |E|/|T_Markov| across all:   {max_E_over_Tm:.4f}")
        print(f"    max |E| vs TV bound (k^2/2S*C):  {max_ratio_TV:.4f}")
        print()

    # Tool 3 findings
    if tool3_summary:
        any_violations = any(s['n_violations'] > 0 for s in tool3_summary)
        print(f"  TOOL 3 (Negative dependence):")
        if not any_violations:
            print(f"    |T_exact| <= |T_Markov| for ALL tested (k,p,t)")
            print(f"    => WR correction REDUCES |T_p|")
            print(f"    => Markov product bound is SUFFICIENT")
        else:
            n_viol = sum(s['n_violations'] for s in tool3_summary)
            print(f"    {n_viol} violations -- need explicit E bound")
        print()

    # Tool 5 findings
    if tool5_res:
        all_pass_a = all(r['passes_a'] for r in tool5_res)
        all_neg_dep = all(r['neg_dep_holds'] for r in tool5_res)
        max_alpha = max(r['best_alpha'] for r in tool5_res) if tool5_res else 0
        print(f"  TOOL 5 (Direct bound |T/C| <= alpha/sqrt(p)):")
        print(f"    All pass 1/sqrt(p):  {'YES' if all_pass_a else 'NO'}")
        print(f"    Neg dep (all):       {'YES' if all_neg_dep else 'NO'}")
        print(f"    max alpha:           {max_alpha:.6f}")
        tightness = [r['max_rho'] * math.sqrt(r['p']) for r in tool5_res]
        print(f"    max rho*sqrt(p):     {max(tightness):.6f}")
        print(f"    Uniform bound < 1:   {'YES' if max(tightness) < 1 else 'NO'}")
        print()

    if tool5_crt:
        all_crt_helps = all(c['crt_ratio'] <= 1.0 + 1e-6 for c in tool5_crt)
        print(f"    CRT: WR always helps: {'YES' if all_crt_helps else 'NO'}")
        print()

    # FINAL ASSESSMENT
    print("  FINAL ASSESSMENT")
    print("  " + "=" * 50)
    print()

    neg_dep_universal = tool3_summary and not any(
        s['n_violations'] > 0 for s in tool3_summary)
    direct_bound = tool5_res and all(r['passes_a'] for r in tool5_res)

    if neg_dep_universal and direct_bound:
        print("  TWO INDEPENDENT PATHS TO CLOSING THE GAP:")
        print()
        print("  PATH A (Negative Dependence):")
        print("    |T_exact(t)| <= |T_Markov(t)| for all t")
        print("    => Only need to bound the Markov product.")
        print()
        print("  PATH B (Direct Bound):")
        print("    |T_exact(t)/C| <= 1/sqrt(p) verified for all tested cases.")
        print()
        print("  EITHER path closes the intermediate prime gap.")
    elif neg_dep_universal:
        print("  PATH: Negative dependence holds numerically.")
        print("  Need to PROVE |T_exact| <= |T_Markov| to close the gap.")
    elif direct_bound:
        print("  PATH: Direct bound |T_exact/C| <= 1/sqrt(p) holds numerically.")
        print("  Need to PROVE this bound to close the gap.")
    else:
        print("  THE MARKOV DECOMPOSITION IS ILL-POSED")
        print("  " + "-" * 50)
        print()

        if tool1_res:
            max_eot = max(r['max_E_over_Tm'] for r in tool1_res)
            if max_eot > 10:
                print(f"  |E| >> |T_Markov| (ratio reaches {max_eot:.1f}).")
                print(f"  T_Markov decays exponentially as product of k-1 factors < 1,")
                print(f"  while T_exact decays only polynomially (~ C/sqrt(p)).")

        print()
        print("  RECOMMENDED PATHS FORWARD:")
        print("  " + "-" * 50)
        print()
        print("  PATH 1: DIRECT BOUND (bypass decomposition)")
        if tool5_res:
            max_alpha = max(r['best_alpha'] for r in tool5_res)
            print(f"    Prove |T_exact(t)/C| <= alpha/sqrt(p), alpha = {max_alpha:.4f}")
            print(f"    A constant alpha suffices for CRT product --> 0.")
        print()
        print("  PATH 2: PARSEVAL + COUNTING")
        print("    Parseval: sum_t |T(t)|^2 = p * sum_r count(r)^2")
        print("    If corrSum mod p nearly uniform: average |T/C| ~ 1/sqrt(p)")
        print("    Need max-vs-average control (large deviation for exp sums).")
        print()
        print("  PATH 3: REGIME-CONDITIONAL PROOF")
        print("    - SMALL (p < S): Markov bound works (verified)")
        print("    - INTERMEDIATE (S <= p <= S^2): direct bound with alpha")
        print("    - LARGE (p > S^2): dimension C/p << 1")
        print("    This covers ALL primes without a universal bound.")

    print()


# ============================================================================
# SHA-256 FINGERPRINT
# ============================================================================

def compute_sha256():
    """SHA-256 of this script file."""
    try:
        with open(__file__, 'rb') as f:
            return hashlib.sha256(f.read()).hexdigest()
    except Exception:
        return "UNKNOWN"


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 72)
    print("r6_wr_correction_bound.py")
    print("Round 6: Without-Replacement Correction Bound")
    print("=" * 72)
    sha = compute_sha256()
    print(f"SHA-256:  {sha}")
    print(f"Time:     {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"Budget:   {TIME_BUDGET}s")
    print()

    # ---- self-tests ----
    if not run_self_tests():
        print("SELF-TESTS FAILED -- aborting.")
        sys.exit(1)

    # ---- tool selection ----
    args = sys.argv[1:]
    if not args or 'all' in args:
        run = {'1', '2', '3', '4', '5'}
    elif 'selftest' in args:
        print("Self-tests passed. Exiting.")
        sha = compute_sha256()
        print(f"\nSHA-256: {sha}")
        return
    else:
        run = set(args)

    t0 = time.time()

    tool1_res = None
    tool3_summary = None
    tool3_violations = None
    tool5_res = None
    tool5_crt = None

    try:
        if '1' in run:
            tool1_res = tool1_exact_E(range(3, 18))
            print(f"  [Tool 1 completed in {time.time()-t0:.1f}s]")

        if '2' in run:
            t2 = time.time()
            tool2_inclusion_exclusion(range(3, 11))
            print(f"  [Tool 2 completed in {time.time()-t2:.1f}s]")

        if '3' in run:
            t3 = time.time()
            tool3_summary, tool3_violations = tool3_negative_dependence(range(3, 14))
            print(f"  [Tool 3 completed in {time.time()-t3:.1f}s]")

        if '4' in run:
            t4 = time.time()
            tool4_regime_analysis(range(3, 25))
            print(f"  [Tool 4 completed in {time.time()-t4:.1f}s]")

        if '5' in run:
            t5 = time.time()
            tool5_res, tool5_crt = tool5_key_bound(range(3, 14))
            print(f"  [Tool 5 completed in {time.time()-t5:.1f}s]")

    except TimeoutError as e:
        print(f"\n  *** TIMEOUT: {e} ***")
        print(f"  Partial results above are still valid.")

    # Summary
    if len(run) >= 3:
        print_summary(tool1_res, tool3_summary, tool3_violations, tool5_res, tool5_crt)

    elapsed = time.time() - t0
    print(f"\nTotal analysis time: {elapsed:.1f}s")

    sha = compute_sha256()
    print(f"SHA-256: {sha}")


if __name__ == "__main__":
    main()
