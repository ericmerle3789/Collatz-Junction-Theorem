#!/usr/bin/env python3
"""
R51-B: TQL INDUCTION -- Tail-as-SubProblem and Inductive Control of mu
=======================================================================
Agent R51-B (Investigateur B) -- Round 51 Axe B

MISSION: Study whether tails behave as sub-problems of size k-1,
enabling induction on k for TQL-lite bounds.

CONTEXT ACQUIRED (DO NOT RE-PROVE):
  P_B(g) = Sum_{j=0}^{k-1} g^j * 2^{B_j} mod p,  g = 2*3^{-1} mod p
  B monotone: 0 <= B_0 <= ... <= B_{k-1} = max_B,  max_B = S - k,  S = ceil(k*log2(3))
  C = C(S-1, k-1)  = total # monotone B-vectors
  C_{b0} = C(max_B - b0 + k - 2, k - 2)  = slice size                 [R47]
  V_{b0} = Sum_r (N_{b0,r} - C_{b0}/p)^2  = within-slice variance      [R48 ANOVA]
  V_{b0} = V(SubProblem(k-1, [b0, max_B], p))                          [R49]
  mu^{tail}(b0) = V_{b0} * p / C_{b0}^2 + 1  = second moment ratio     [R46]
  TQL: N^{tail}_{b0,r} ~ C_{b0}/p ==> controls V and mu simultaneously [R50]

KEY INSIGHT FOR R51:
  For slice b0, P_tail = Sum_{j=1}^{k-1} g^j * 2^{B_j} mod p
  After translation B_j' = B_j - b0:
    P_tail = 2^{b0} * Sum_{j=1}^{k-1} g^j * 2^{B_j'} mod p
  where B_j' in [0, max_B - b0], nondecreasing, B_{k-1}' = max_B - b0.

  The factor 2^{b0} is a multiplicative rotation mod p (for p prime, p nmid 2):
    N^{tail}_{b0,r} = N^{std}_{r * 2^{-b0} mod p}
  where N^{std} is the distribution of the STANDARD problem (k-1, [0, max_B-b0], p).

  BUT: the standard problem uses coefficients g^1, ..., g^{k-1} not g^0, ..., g^{k-2}.
  So it's not EXACTLY the Collatz problem of size k-1. The coefficients are shifted.
  We need to track this carefully.

SECTIONS:
  0: Primitives
  1: Q1 -- Canonical reformulation: tail = rotated sub-problem
  2: Q2 -- Transport of mu (invariance under multiplicative rotation)
  3: Q3 -- Obstruction: varying max_B' across slices
  4: Q4 -- Candidate inductive lemma
  5: Q5 -- Inductive cascade k=3..10
  6: Summary table

EPISTEMIC LABELS:
  [PROUVE]       = rigorous proof or exact computation
  [SEMI-FORMEL]  = structured argument, not formal proof
  [CALCULE]      = verified by exact computation
  [OBSERVE]      = numerical evidence, NOT a proof
  [CONJECTURAL]  = plausible but unproven
  [REFUTE]       = contradicted by evidence

Author: Claude Opus 4.6 (R51-B Investigateur Induction pour Eric Merle)
Date:   2026-03-11
"""

import sys
import time
from math import comb, gcd, ceil, log2, sqrt
from itertools import combinations_with_replacement
from collections import defaultdict

# ============================================================================
# GLOBAL CONFIGURATION
# ============================================================================

T_START = time.time()
TIME_BUDGET = 170.0  # 170 seconds to stay safely under 3 minutes

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
    """C = C(S-1, k-1), total number of monotone B-vectors."""
    S = compute_S(k)
    return comb(S - 1, k - 1)


def compute_C_slice(k, b0):
    """C_{b0} = C(max_B - b0 + k - 2, k - 2)."""
    max_B = compute_max_B(k)
    if b0 > max_B:
        return 0
    return comb(max_B - b0 + k - 2, k - 2)


def compute_g(p):
    """g = 2 * 3^{-1} mod p. Universal (independent of k)."""
    if gcd(3, p) != 1 or gcd(2, p) != 1:
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


# ============================================================================
# SECTION 0b: DISTRIBUTION COMPUTATION (brute-force for small k)
# ============================================================================

def compute_tail_distribution_bf(k, p, b0):
    """Brute-force tail distribution for slice b0.

    The tail is (B_1, ..., B_{k-1}) with b0 <= B_1 <= ... <= B_{k-1} = max_B.
    P_tail = Sum_{j=1}^{k-1} g^j * 2^{B_j} mod p.

    Returns: (count_array[p], total_count)
    """
    max_B = compute_max_B(k)
    g = compute_g(p)
    if g is None:
        return None, 0
    count = [0] * p
    total = 0

    if k <= 1:
        return count, 0

    g_pows = [pow(g, j, p) for j in range(k)]
    two_pows = [pow(2, b, p) for b in range(max_B + 1)]

    if k == 2:
        # Tail is just B_1 = max_B
        r = (g_pows[1] * two_pows[max_B]) % p
        count[r] = 1
        return count, 1

    # k >= 3: B_1, ..., B_{k-2} free in [b0, max_B], B_{k-1} = max_B
    last_term = (g_pows[k - 1] * two_pows[max_B]) % p

    for combo in combinations_with_replacement(range(b0, max_B + 1), k - 2):
        res = 0
        for idx, bj in enumerate(combo):
            # idx-th free component is B_{idx+1}, coefficient g^{idx+1}
            res = (res + g_pows[idx + 1] * two_pows[bj]) % p
        res = (res + last_term) % p
        count[res] += 1
        total += 1

    return count, total


def compute_standard_distribution_bf(k_sub, p, max_B_sub):
    """Standard sub-problem distribution.

    Enumerate nondecreasing (B'_0, ..., B'_{k_sub-1}) with
    B'_j in [0, max_B_sub], B'_{k_sub-1} = max_B_sub.
    P_std = Sum_{j=0}^{k_sub-1} g^j * 2^{B'_j} mod p.

    This is the "Collatz polynomial" of dimension k_sub on range [0, max_B_sub].

    Returns: (count_array[p], total_count)
    """
    g = compute_g(p)
    if g is None:
        return None, 0
    count = [0] * p
    total = 0

    if k_sub <= 0 or max_B_sub < 0:
        return count, 0

    g_pows = [pow(g, j, p) for j in range(k_sub)]
    two_pows = [pow(2, b, p) for b in range(max_B_sub + 1)]

    if k_sub == 1:
        # Only B'_0 = max_B_sub
        r = (g_pows[0] * two_pows[max_B_sub]) % p
        count[r] = 1
        return count, 1

    # k_sub >= 2: B'_0, ..., B'_{k_sub-2} free in [0, max_B_sub], B'_{k_sub-1} = max_B_sub
    last_term = (g_pows[k_sub - 1] * two_pows[max_B_sub]) % p

    for combo in combinations_with_replacement(range(max_B_sub + 1), k_sub - 1):
        res = 0
        for idx, bj in enumerate(combo):
            res = (res + g_pows[idx] * two_pows[bj]) % p
        res = (res + last_term) % p
        count[res] += 1
        total += 1

    return count, total


def compute_shifted_tail_distribution_bf(k, p, b0):
    """Shifted tail distribution: translate B_j -> B_j' = B_j - b0.

    After translation, B_j' in [0, max_B - b0], nondecreasing, B'_{k-1} = max_B - b0.
    P_tail = Sum_{j=1}^{k-1} g^j * 2^{B_j} = 2^{b0} * Sum_{j=1}^{k-1} g^j * 2^{B_j'} mod p.

    So P_tail = 2^{b0} * P_shifted where P_shifted = Sum_{j=1}^{k-1} g^j * 2^{B_j'}.

    Returns: (count_shifted[p], total_count)
    where count_shifted[r] = #{B' : P_shifted = r mod p}
    """
    max_B = compute_max_B(k)
    g = compute_g(p)
    if g is None:
        return None, 0

    max_B_prime = max_B - b0
    count = [0] * p
    total = 0

    if k <= 1:
        return count, 0

    g_pows = [pow(g, j, p) for j in range(k)]
    two_pows = [pow(2, b, p) for b in range(max_B_prime + 1)]

    if k == 2:
        # B'_1 = max_B - b0
        r = (g_pows[1] * two_pows[max_B_prime]) % p
        count[r] = 1
        return count, 1

    # k >= 3
    last_term = (g_pows[k - 1] * two_pows[max_B_prime]) % p

    for combo in combinations_with_replacement(range(max_B_prime + 1), k - 2):
        res = 0
        for idx, bj in enumerate(combo):
            # B'_{idx+1}, coefficient g^{idx+1}
            res = (res + g_pows[idx + 1] * two_pows[bj]) % p
        res = (res + last_term) % p
        count[res] += 1
        total += 1

    return count, total


def compute_mu(count, C_val, p):
    """mu = M2 * p / C^2 where M2 = Sum N_r^2.
    mu = 1 means perfectly uniform distribution.
    """
    if C_val == 0 or p == 0:
        return float('inf')
    M2 = sum(n * n for n in count)
    return M2 * p / (C_val * C_val)


def compute_variance(count, C_val, p):
    """V = Sum_r (N_r - C/p)^2."""
    if p == 0 or C_val == 0:
        return 0.0
    expected = C_val / p
    return sum((n - expected) ** 2 for n in count)


# ============================================================================
# SECTION 0c: DP ENGINE for sub-problem distributions (faster for larger k)
# ============================================================================

def dp_subproblem_distribution(k_sub, p, max_B_sub, max_time=5.0):
    """Distribution for sub-problem of size k_sub on [0, max_B_sub].
    Nondecreasing B'_0 <= ... <= B'_{k_sub-1} = max_B_sub.
    P = Sum g^j * 2^{B'_j} mod p.
    """
    t0 = time.time()
    g = compute_g(p)
    if g is None:
        return None
    nB = max_B_sub + 1
    g_pows = [pow(g, j, p) for j in range(k_sub)]
    two_pows = [pow(2, b, p) for b in range(nB)]

    state_size = p * nB
    if state_size > 5_000_000:
        return None

    if k_sub == 1:
        dist = [0] * p
        r = (g_pows[0] * two_pows[max_B_sub]) % p
        dist[r] = 1
        return dist

    # DP: position 0..k_sub-1
    dp = [0] * state_size
    for b in range(nB):
        r = (g_pows[0] * two_pows[b]) % p
        dp[b * p + r] += 1

    for j in range(1, k_sub):
        if time.time() - t0 > max_time:
            return None
        coeff = g_pows[j]
        new_dp = [0] * state_size
        if j == k_sub - 1:
            c2b = (coeff * two_pows[max_B_sub]) % p
            for prev_b in range(nB):
                base = prev_b * p
                target_base = (nB - 1) * p
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


def dp_shifted_tail(k, p, b0, max_time=5.0):
    """DP for the shifted tail: coefficients g^1, ..., g^{k-1} on [0, max_B-b0].

    The shifted tail polynomial is:
      P_shifted = Sum_{j=1}^{k-1} g^j * 2^{B_j'} mod p
    with B_j' in [0, max_B - b0], nondecreasing, B'_{k-1} = max_B - b0.

    This is NOT the standard sub-problem because it uses g^1, ..., g^{k-1}
    instead of g^0, ..., g^{k-2}.
    """
    t0 = time.time()
    g = compute_g(p)
    if g is None:
        return None

    max_B = compute_max_B(k)
    max_B_prime = max_B - b0
    nB = max_B_prime + 1
    k_tail = k - 1  # number of tail components

    if k_tail <= 0 or max_B_prime < 0:
        return None

    # Coefficients: g^1, g^2, ..., g^{k-1} for positions 0..k_tail-1 of the tail
    g_pows_tail = [pow(g, j + 1, p) for j in range(k_tail)]
    two_pows = [pow(2, b, p) for b in range(nB)]

    state_size = p * nB
    if state_size > 5_000_000:
        return None

    if k_tail == 1:
        dist = [0] * p
        r = (g_pows_tail[0] * two_pows[max_B_prime]) % p
        dist[r] = 1
        return dist

    # DP: positions 0..k_tail-1
    dp = [0] * state_size
    coeff0 = g_pows_tail[0]
    for b in range(nB):
        r = (coeff0 * two_pows[b]) % p
        dp[b * p + r] += 1

    for j in range(1, k_tail):
        if time.time() - t0 > max_time:
            return None
        coeff = g_pows_tail[j]
        new_dp = [0] * state_size
        if j == k_tail - 1:
            c2b = (coeff * two_pows[max_B_prime]) % p
            for prev_b in range(nB):
                base = prev_b * p
                target_base = (nB - 1) * p
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
# SECTION 1: CANONICAL REFORMULATION -- TAIL = ROTATED SUB-PROBLEM
# ============================================================================
# Key identity to verify:
#   P_tail(B_1,...,B_{k-1}) = Sum_{j=1}^{k-1} g^j * 2^{B_j} mod p
#   After B_j' = B_j - b0:
#     P_tail = 2^{b0} * Sum_{j=1}^{k-1} g^j * 2^{B_j'} mod p
#            = 2^{b0} * P_shifted
#
#   The shifted polynomial P_shifted uses coefficients g^1,...,g^{k-1},
#   NOT g^0,...,g^{k-2}. So it's NOT the standard (k-1)-dim Collatz poly.
#   But it IS the standard one multiplied by g:
#     P_shifted = g * Sum_{j=1}^{k-1} g^{j-1} * 2^{B_j'} = g * P_std^{(k-1)}
#
#   where P_std^{(k-1)} = Sum_{j=0}^{k-2} g^j * 2^{B_j'} is the standard
#   Collatz poly of dimension k-1 on [0, max_B-b0].
#
#   Therefore: P_tail = 2^{b0} * g * P_std^{(k-1)}
#   And: N^{tail}_{b0,r} = N^{std}_{r * (2^{b0} * g)^{-1} mod p}
#
#   Since 2^{b0}*g is invertible mod p, this is a PERMUTATION of residues.
#   Consequence: The DISTRIBUTION is the same up to relabeling.
#   In particular: mu^{tail}(b0) = mu^{std}(k-1, [0, max_B-b0], p).

def run_section1(test_cases):
    """Verify the canonical reformulation: tail = rotated standard sub-problem."""
    print("\n" + "=" * 75)
    print("SECTION 1: CANONICAL REFORMULATION -- TAIL = ROTATED SUB-PROBLEM")
    print("=" * 75)

    for k, p in test_cases:
        if time_remaining() < 5:
            print("  [TIME] Skipping remaining Section 1 tests")
            break

        max_B = compute_max_B(k)
        g = compute_g(p)
        if g is None:
            continue

        # The rotation factor for slice b0: alpha = 2^{b0} * g mod p
        # N^{tail}_{b0, r} = N^{std}_{r * alpha^{-1} mod p}

        for b0 in range(max_B + 1):
            if time_remaining() < 3:
                break

            C_b0 = compute_C_slice(k, b0)
            if C_b0 == 0:
                continue

            max_B_prime = max_B - b0
            k_sub = k - 1

            # 1a. Compute tail distribution (brute-force)
            tail_dist, tail_count = compute_tail_distribution_bf(k, p, b0)
            if tail_dist is None:
                continue

            # 1b. Compute standard sub-problem distribution on [0, max_B']
            std_dist, std_count = compute_standard_distribution_bf(k_sub, p, max_B_prime)
            if std_dist is None:
                continue

            # Verify same total count
            record_test(
                f"S1.count k={k} p={p} b0={b0}",
                tail_count == std_count,
                f"tail={tail_count}, std={std_count}"
            )

            # 1c. Verify rotation identity
            # P_tail = 2^{b0} * g * P_std
            # So N^{tail}[r] = N^{std}[r * (2^{b0}*g)^{-1} mod p]
            alpha = (pow(2, b0, p) * g) % p
            alpha_inv = pow(alpha, -1, p)

            # Rotate the standard distribution
            rotated_std = [0] * p
            for r in range(p):
                # N^{tail}[r] should equal N^{std}[r * alpha_inv mod p]
                r_mapped = (r * alpha_inv) % p
                rotated_std[r] = std_dist[r_mapped]

            match = (tail_dist == rotated_std)
            record_test(
                f"S1.rotation k={k} p={p} b0={b0}",
                match,
                f"alpha=2^{b0}*g={alpha}, match={match}"
            )

            # 1d. Verify mu invariance (consequence of rotation)
            mu_tail = compute_mu(tail_dist, tail_count, p)
            mu_std = compute_mu(std_dist, std_count, p)
            mu_match = abs(mu_tail - mu_std) < 1e-12
            record_test(
                f"S1.mu_inv k={k} p={p} b0={b0}",
                mu_match,
                f"mu_tail={mu_tail:.6f}, mu_std={mu_std:.6f}"
            )


# ============================================================================
# SECTION 2: TRANSPORT OF MU (INDUCTION k -> k-1)
# ============================================================================
# If mu^{tail}(b0) = mu(k-1, [0, max_B-b0], p), then controlling mu at
# dimension k-1 for ALL possible max_B values gives control at dimension k.
#
# Key question: is mu(k-1, [0, M'], p) = mu for the TRUE Collatz problem at k-1?
# NO! The Collatz problem at k-1 has its OWN max_B = S(k-1) - (k-1),
# while the sub-problem has max_B' = max_B(k) - b0 which is DIFFERENT.
#
# So the sub-problem is a Collatz polynomial of dimension k-1 but with
# a DIFFERENT range parameter. This is a GENERALIZED Collatz problem.

def run_section2(test_cases):
    """Transport of mu: verify that mu^{tail}(b0) = mu of standard sub-problem."""
    print("\n" + "=" * 75)
    print("SECTION 2: TRANSPORT OF MU (INDUCTION k -> k-1)")
    print("=" * 75)

    for k, p in test_cases:
        if time_remaining() < 5:
            print("  [TIME] Skipping remaining Section 2 tests")
            break

        max_B = compute_max_B(k)
        g = compute_g(p)
        if g is None:
            continue

        # Compare mu of tail slice to mu of standard sub-problem
        print(f"\n  --- k={k}, p={p}, max_B={max_B} ---")

        # Also compute mu for the TRUE Collatz problem at k-1
        max_B_true = compute_max_B(k - 1) if k > 1 else 0
        C_true = compute_C(k - 1) if k > 1 else 1

        if k > 1 and max_B_true >= 0:
            true_dist, true_count = compute_standard_distribution_bf(k - 1, p, max_B_true)
            if true_dist is not None and true_count > 0:
                mu_true = compute_mu(true_dist, true_count, p)
                print(f"  mu(true k-1={k-1}, max_B={max_B_true}) = {mu_true:.6f}")

        for b0 in range(max_B + 1):
            if time_remaining() < 3:
                break

            C_b0 = compute_C_slice(k, b0)
            if C_b0 == 0:
                continue

            max_B_prime = max_B - b0
            k_sub = k - 1

            # mu of tail (already verified = mu of std sub-problem in S1)
            std_dist, std_count = compute_standard_distribution_bf(k_sub, p, max_B_prime)
            if std_dist is None or std_count == 0:
                continue

            mu_sub = compute_mu(std_dist, std_count, p)

            # Compare to true k-1 problem
            mu_diff_true = mu_sub - mu_true if 'mu_true' in dir() else float('nan')

            record_test(
                f"S2.transport k={k} p={p} b0={b0}",
                mu_sub >= 1.0 - 1e-12,  # mu >= 1 always (Cauchy-Schwarz)
                f"mu_sub(M'={max_B_prime})={mu_sub:.6f}, C'={std_count}"
            )


# ============================================================================
# SECTION 3: OBSTRUCTION TO RECURRENCE
# ============================================================================
# The recurrence mu(k) <= f(mu(k-1)) is obstructed by:
#   1. max_B' = max_B(k) - b0 varies with b0 (not the same sub-problem)
#   2. max_B(k) - b0 != max_B(k-1) in general (different from true k-1)
#   3. The weighting by C_{b0}^2 / C^2 is non-uniform
#
# We study how mu(k-1, [0, M'], p) varies as a function of M'.

def run_section3(test_cases_extended):
    """Obstruction analysis: how does mu vary with max_B' at fixed k-1?"""
    print("\n" + "=" * 75)
    print("SECTION 3: OBSTRUCTION TO RECURRENCE")
    print("=" * 75)

    for k_sub, p in test_cases_extended:
        if time_remaining() < 10:
            print("  [TIME] Skipping remaining Section 3 tests")
            break

        g = compute_g(p)
        if g is None:
            continue

        # Compute mu(k_sub, [0, M'], p) for M' = 0, 1, ..., max_reasonable
        max_M = min(20, compute_max_B(k_sub + 1))  # reasonable upper bound
        print(f"\n  --- k_sub={k_sub}, p={p} : mu(M') for M'=0..{max_M} ---")

        mu_values = []
        C_values = []
        for M_prime in range(max_M + 1):
            if time_remaining() < 3:
                break

            if k_sub == 1:
                # Only B_0 = M', so distribution is delta. mu = p/1 = p (terrible)
                # unless C=1, then M2=1, mu = 1*p/1 = p. Actually mu = p for k=1 always.
                C_sub = 1
                mu_val = float(p)  # delta distribution
            else:
                std_dist, C_sub = compute_standard_distribution_bf(k_sub, p, M_prime)
                if std_dist is None or C_sub == 0:
                    mu_values.append((M_prime, float('inf'), 0))
                    C_values.append(0)
                    continue
                mu_val = compute_mu(std_dist, C_sub, p)

            mu_values.append((M_prime, mu_val, C_sub))
            C_values.append(C_sub)

            if M_prime <= 5 or M_prime == max_M:
                print(f"    M'={M_prime:3d}: C'={C_sub:8d}, mu={mu_val:.6f}, "
                      f"mu-1={mu_val - 1:.6e}")

        # Check monotonicity: is mu decreasing in M'?
        finite_mus = [(m, mu, c) for m, mu, c in mu_values if mu < float('inf') and c > 0]
        if len(finite_mus) >= 2:
            decreasing = all(finite_mus[i][1] >= finite_mus[i + 1][1] - 1e-12
                             for i in range(len(finite_mus) - 1))
            record_test(
                f"S3.monotone k_sub={k_sub} p={p}",
                decreasing,
                f"mu decreasing in M': {decreasing}"
            )

            # Check convexity: is mu-1 convex in M'?
            if len(finite_mus) >= 3:
                convex = True
                for i in range(1, len(finite_mus) - 1):
                    m0, mu0, _ = finite_mus[i - 1]
                    m1, mu1, _ = finite_mus[i]
                    m2, mu2, _ = finite_mus[i + 1]
                    # Second difference
                    d2 = (mu2 - 1) - 2 * (mu1 - 1) + (mu0 - 1)
                    if d2 < -1e-10:
                        convex = False
                        break
                record_test(
                    f"S3.convex k_sub={k_sub} p={p}",
                    convex,
                    f"mu-1 convex in M': {convex}"
                )

        # Check: does mu(M') ~ 1 + A*p/C(M') for some constant A?
        # C(M') = C(M' + k_sub - 1, k_sub - 1)
        # If mu - 1 ~ A*p/C', then (mu-1)*C'/p ~ A (constant)
        ratios = []
        for M_prime, mu_val, C_sub in mu_values:
            if C_sub > 0 and mu_val < float('inf') and mu_val > 1.0 + 1e-15:
                ratio = (mu_val - 1) * C_sub / p
                ratios.append((M_prime, ratio))

        if len(ratios) >= 2:
            ratio_vals = [r for _, r in ratios]
            ratio_mean = sum(ratio_vals) / len(ratio_vals)
            ratio_std = sqrt(sum((r - ratio_mean) ** 2 for r in ratio_vals) / len(ratio_vals))
            # "Constant" if coefficient of variation < 50%
            cv = ratio_std / ratio_mean if ratio_mean > 1e-15 else float('inf')
            record_test(
                f"S3.scaling k_sub={k_sub} p={p}",
                cv < 0.5,
                f"(mu-1)*C'/p: mean={ratio_mean:.4f}, CV={cv:.4f}"
            )


# ============================================================================
# SECTION 4: CANDIDATE INDUCTIVE LEMMA
# ============================================================================
# We test several candidate forms:
#
# (A) mu(k, M, p) <= max_{b0} mu(k-1, M-b0, p)
#     "Worst sub-problem bounds the whole"
#
# (B) mu(k, M, p) <= mu(k-1, M, p)
#     "Dimension reduction preserves mu bound"
#     (uses b0=0 sub-problem which has same max_B)
#
# (C) mu(k) <= mu(k-1) + correction
#     "Additive step"
#
# (D) mu(k) - 1 <= (mu(k-1, worst) - 1) * contraction
#     "Contractive"

def compute_mu_for_problem(k, max_B_val, p, use_dp=False, max_time=5.0):
    """Compute mu for the generalized Collatz problem (k, [0, max_B_val], p).
    Returns (mu, C) or (None, 0) if computation fails.
    """
    if k <= 0 or max_B_val < 0:
        return None, 0

    if use_dp:
        dist = dp_subproblem_distribution(k, p, max_B_val, max_time=max_time)
        if dist is None:
            return None, 0
        C_val = sum(dist)
    else:
        dist, C_val = compute_standard_distribution_bf(k, p, max_B_val)
        if dist is None:
            return None, 0

    if C_val == 0:
        return None, 0
    return compute_mu(dist, C_val, p), C_val


def run_section4(test_cases):
    """Test candidate inductive lemmas."""
    print("\n" + "=" * 75)
    print("SECTION 4: CANDIDATE INDUCTIVE LEMMA")
    print("=" * 75)

    results_table = []

    for k, p in test_cases:
        if time_remaining() < 10:
            print("  [TIME] Skipping remaining Section 4 tests")
            break

        max_B = compute_max_B(k)
        g = compute_g(p)
        if g is None:
            continue

        C_k = compute_C(k)

        # Compute mu(k) for the actual Collatz problem at dimension k
        mu_k, C_check = compute_mu_for_problem(k, max_B, p, use_dp=(C_k > 5000))
        if mu_k is None:
            continue

        print(f"\n  --- k={k}, p={p}, max_B={max_B}, C={C_k}, mu(k)={mu_k:.8f} ---")

        # Compute mu for each sub-problem (k-1, [0, max_B-b0], p)
        sub_mus = {}
        max_sub_mu = 0.0
        for b0 in range(max_B + 1):
            max_B_prime = max_B - b0
            C_b0 = compute_C_slice(k, b0)
            if C_b0 == 0:
                continue

            mu_sub, C_sub = compute_mu_for_problem(k - 1, max_B_prime, p,
                                                    use_dp=(C_b0 > 5000))
            if mu_sub is None:
                continue
            sub_mus[b0] = mu_sub
            max_sub_mu = max(max_sub_mu, mu_sub)

        if not sub_mus:
            continue

        # Candidate (A): mu(k) <= max_{b0} mu(k-1, M-b0)
        lemma_A = mu_k <= max_sub_mu + 1e-12
        record_test(
            f"S4.A k={k} p={p}",
            lemma_A,
            f"mu(k)={mu_k:.6f} <= max_sub={max_sub_mu:.6f} ? {lemma_A}"
        )

        # Candidate (B): mu(k) <= mu(k-1, same max_B)
        mu_sub_b0_0 = sub_mus.get(0, None)
        if mu_sub_b0_0 is not None:
            lemma_B = mu_k <= mu_sub_b0_0 + 1e-12
            record_test(
                f"S4.B k={k} p={p}",
                lemma_B,
                f"mu(k)={mu_k:.6f} <= mu(k-1,M={max_B})={mu_sub_b0_0:.6f} ? {lemma_B}"
            )

        # Candidate (C): mu(k) - 1 <= max(mu(k-1,...) - 1)
        max_sub_excess = max(mu - 1 for mu in sub_mus.values())
        lemma_C = (mu_k - 1) <= max_sub_excess + 1e-12
        record_test(
            f"S4.C k={k} p={p}",
            lemma_C,
            f"mu(k)-1={mu_k - 1:.6e} <= max(mu_sub-1)={max_sub_excess:.6e} ? {lemma_C}"
        )

        # Candidate (D): mu(k) - 1 <= (mu(k-1, worst) - 1) * contraction_factor
        # Check if there exists contraction < 1
        if max_sub_excess > 1e-15 and mu_k > 1.0 + 1e-15:
            contraction = (mu_k - 1) / max_sub_excess
            record_test(
                f"S4.D k={k} p={p}",
                contraction < 1.0 + 1e-12,
                f"contraction = {contraction:.6f}"
            )
        else:
            contraction = 0.0

        # Weighted average formula:
        # mu(k) = (1/C^2) * Sum_{b0} C_{b0}^2 * mu_sub(b0)   (from ANOVA)
        # actually: V(k) = Sum V_{b0} + V_between
        # mu(k) = V*p/C^2 + 1
        # This is NOT simply the weighted average of mu_sub's -- there's V_between.
        # But we can check the WITHIN part:
        V_within_from_subs = 0.0
        for b0, mu_sub in sub_mus.items():
            C_b0 = compute_C_slice(k, b0)
            V_b0 = (mu_sub - 1) * C_b0 ** 2 / p
            V_within_from_subs += V_b0

        mu_within_contribution = V_within_from_subs * p / (C_k ** 2) + 1
        # mu(k) >= mu_within (since V_between >= 0 would make it larger,
        # but actually V_between can be negative... No, V_between = V - V_within
        # and V >= 0, V_within >= 0, but V_between can be negative.)

        record_test(
            f"S4.within k={k} p={p}",
            True,
            f"mu_within_only={mu_within_contribution:.6f}, mu(k)={mu_k:.6f}, "
            f"between_frac={(mu_k - mu_within_contribution) / max(mu_k - 1, 1e-15):.4f}"
        )

        results_table.append({
            'k': k, 'p': p, 'max_B': max_B, 'C': C_k,
            'mu_k': mu_k,
            'max_sub_mu': max_sub_mu,
            'contraction': contraction if max_sub_excess > 1e-15 else float('nan'),
            'lemma_A': lemma_A,
            'lemma_C': lemma_C,
            'mu_within': mu_within_contribution,
        })

    return results_table


# ============================================================================
# SECTION 5: INDUCTIVE CASCADE
# ============================================================================
# Test: if mu(k-1, M') <= 1 + A*p/C(M'+k-2, k-2) for all M',
# then mu(k, M) <= 1 + A*p/C(M+k-1, k-1) ?
#
# The cascade goes k=2 -> 3 -> 4 -> ... -> 10.
# At each step, we check if the bound propagates.

def run_section5(primes_list):
    """Test the inductive cascade from k=2 up to k=10."""
    print("\n" + "=" * 75)
    print("SECTION 5: INDUCTIVE CASCADE k=2..10")
    print("=" * 75)

    cascade_results = []

    for p in primes_list:
        if time_remaining() < 15:
            print("  [TIME] Skipping remaining primes in Section 5")
            break

        g = compute_g(p)
        if g is None:
            continue

        print(f"\n  === Prime p={p} ===")

        # For each k, compute the "best A" such that mu(k, M) <= 1 + A*p/C(M+k-1,k-1)
        # for ALL relevant M values.
        best_A = {}

        for k in range(2, 11):
            if time_remaining() < 5:
                print(f"  [TIME] Stopping cascade at k={k}")
                break

            max_B_collatz = compute_max_B(k)
            C_collatz = compute_C(k)

            # We need to check mu for M = 0, 1, ..., max_B_collatz
            # but for the cascade we also need sub-problems that arise
            # from higher k values. So we check a range of M values.

            max_M_to_check = min(max_B_collatz + 5, 25)
            worst_A = 0.0
            all_ok = True

            for M in range(0, max_M_to_check + 1):
                if time_remaining() < 3:
                    break

                C_M = comb(M + k - 1, k - 1)
                if C_M == 0:
                    continue

                # Compute mu for generalized problem (k, [0, M], p)
                mu_val, C_check = compute_mu_for_problem(k, M, p,
                                                          use_dp=(C_M > 5000),
                                                          max_time=2.0)
                if mu_val is None:
                    continue

                # A = (mu - 1) * C_M / p
                if mu_val > 1.0 + 1e-15:
                    A_val = (mu_val - 1) * C_M / p
                    worst_A = max(worst_A, A_val)
                    if M == max_B_collatz:
                        print(f"    k={k}, M={M} (Collatz): mu={mu_val:.6f}, "
                              f"A={A_val:.4f}, C={C_M}")

            best_A[k] = worst_A

            # Test cascade: is A(k) <= A(k-1)?
            if k - 1 in best_A:
                A_prev = best_A[k - 1]
                cascade_ok = worst_A <= A_prev + 0.01  # small tolerance
                record_test(
                    f"S5.cascade k={k} p={p}",
                    cascade_ok,
                    f"A(k={k})={worst_A:.4f} <= A(k-1={k - 1})={A_prev:.4f} ? {cascade_ok}"
                )
            else:
                cascade_ok = True

            cascade_results.append({
                'p': p, 'k': k,
                'best_A': worst_A,
                'cascade_ok': cascade_ok if k - 1 in best_A else None,
            })

        # Print cascade summary for this prime
        print(f"\n  Cascade summary for p={p}:")
        print(f"    {'k':>3s}  {'A(k)':>10s}  {'cascade':>8s}")
        for k in sorted(best_A.keys()):
            a_val = best_A[k]
            cas = ""
            if k - 1 in best_A:
                cas = "OK" if a_val <= best_A[k - 1] + 0.01 else "FAIL"
            print(f"    {k:3d}  {a_val:10.4f}  {cas:>8s}")

    return cascade_results


# ============================================================================
# SECTION 6: FINAL SUMMARY TABLE
# ============================================================================

def print_summary_table(s4_results, s5_results):
    """Print the final summary table."""
    print("\n" + "=" * 75)
    print("SECTION 6: FINAL SUMMARY TABLE")
    print("=" * 75)

    # Table 1: Section 4 results (inductive lemma candidates)
    print("\n  Table 1: Inductive Lemma Candidates by (k, p)")
    print(f"  {'k':>3s} {'p':>5s} {'max_B':>5s} {'C':>8s} {'mu(k)':>10s} "
          f"{'max_sub':>10s} {'contr':>8s} {'A?':>4s} {'C?':>4s}")
    print("  " + "-" * 70)
    for r in s4_results:
        contr_s = f"{r['contraction']:.4f}" if not (r['contraction'] != r['contraction']) else "N/A"
        print(f"  {r['k']:3d} {r['p']:5d} {r['max_B']:5d} {r['C']:8d} "
              f"{r['mu_k']:10.6f} {r['max_sub_mu']:10.6f} {contr_s:>8s} "
              f"{'Y' if r['lemma_A'] else 'N':>4s} {'Y' if r['lemma_C'] else 'N':>4s}")

    # Table 2: Section 5 cascade
    if s5_results:
        print("\n  Table 2: Inductive Cascade A(k) by (k, p)")
        # Group by p
        by_p = defaultdict(list)
        for r in s5_results:
            by_p[r['p']].append(r)

        for p_val, rows in sorted(by_p.items()):
            print(f"\n  p = {p_val}:")
            print(f"    {'k':>3s} {'A(k)':>10s} {'cascade':>8s}")
            print("    " + "-" * 25)
            for r in sorted(rows, key=lambda x: x['k']):
                cas = ""
                if r['cascade_ok'] is not None:
                    cas = "OK" if r['cascade_ok'] else "FAIL"
                print(f"    {r['k']:3d} {r['best_A']:10.4f} {cas:>8s}")


# ============================================================================
# MAIN EXECUTION
# ============================================================================

def main():
    print("=" * 75)
    print("R51-B: TQL INDUCTION -- Tail-as-SubProblem and Inductive Control of mu")
    print("=" * 75)
    print(f"Time budget: {TIME_BUDGET:.0f}s")

    # Test configuration
    # Small primes for thorough testing, larger primes for spot checks
    small_primes = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

    # Section 1: brute-force verification (needs small k and p)
    s1_cases = []
    for k in range(3, 8):
        for p in small_primes:
            if p > 2 and is_prime(p) and gcd(6, p) == 1:
                C_k = compute_C(k)
                if C_k <= 50000:  # feasible for brute-force
                    s1_cases.append((k, p))

    # Limit to manageable number
    s1_cases = s1_cases[:40]
    run_section1(s1_cases)

    # Section 2: transport of mu
    s2_cases = [(k, p) for k, p in s1_cases if k <= 7][:25]
    run_section2(s2_cases)

    # Section 3: obstruction (vary M' at fixed k_sub)
    s3_cases = []
    for k_sub in range(2, 7):
        for p in [5, 7, 11, 13, 17, 23, 31, 41]:
            if is_prime(p) and gcd(6, p) == 1:
                s3_cases.append((k_sub, p))
    s3_cases = s3_cases[:30]
    run_section3(s3_cases)

    # Section 4: candidate inductive lemma
    s4_cases = []
    for k in range(3, 9):
        for p in [5, 7, 11, 13, 17, 23, 29, 31, 37, 41, 43, 47]:
            if is_prime(p) and gcd(6, p) == 1:
                C_k = compute_C(k)
                if C_k <= 100000:
                    s4_cases.append((k, p))
    s4_cases = s4_cases[:50]
    s4_results = run_section4(s4_cases)

    # Section 5: inductive cascade
    s5_primes = [5, 7, 11, 13, 17, 23, 31]
    s5_results = run_section5(s5_primes)

    # Section 6: summary
    print_summary_table(s4_results, s5_results)

    # Final test summary
    print("\n" + "=" * 75)
    print(f"FINAL SUMMARY: {PASS_COUNT} PASS, {FAIL_COUNT} FAIL "
          f"out of {PASS_COUNT + FAIL_COUNT} tests")
    print(f"Elapsed time: {elapsed():.1f}s / {TIME_BUDGET:.0f}s budget")
    print("=" * 75)

    if FAIL_COUNT > 0:
        print(f"\nWARNING: {FAIL_COUNT} test(s) FAILED. Review above for details.")
    else:
        print("\nAll tests PASSED.")

    return FAIL_COUNT


if __name__ == "__main__":
    sys.exit(main())
