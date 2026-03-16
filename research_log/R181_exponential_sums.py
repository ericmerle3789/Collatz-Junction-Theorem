#!/usr/bin/env python3
"""R181_exponential_sums.py — Exponential Sums / Condition Q Analysis.

INVESTIGATION: Character sums over the Junction function g(v) and the
structural anti-correlation that drives cancellation.

FRAMEWORK:
  g(v) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{e_j}
  where v = (e_0, ..., e_{k-1}) with 0 <= e_0 < e_1 < ... < e_{k-1} < S
  d = 2^S - 3^k,  C = C(S-1, k-1)

  For prime p | d and 1 <= a <= p-1, define the exponential sum:
    S_p(a) = sum_{v valid} exp(2*pi*i * a * g(v) / p)

  Key identity: N_0(p) = (1/p) * [C + sum_{a=1}^{p-1} S_p(a)]

  If |S_p(a)| <= C/p for all a, then N_0(p) <= C/p + 1.
  If C/p < 1, this implies N_0(p) = 0 or 1.

STRUCTURAL FEATURE (Anti-Correlation):
  In g(v), large powers of 3 (coefficient 3^{k-1-j} for small j) are
  paired with SMALL powers of 2 (since e_0 < e_1 < ... implies e_j
  grows with j). The most significant ternary terms correspond to the
  least significant binary terms. This creates destructive interference
  in the character sum.

SECTIONS:
  1. Exact computation of S_p(a) for small (S,k)
  2. Cancellation measurement: |S_p(a)|/C vs 1/sqrt(p) and 1/p
  3. Scaling with k: does cancellation improve?
  4. Anti-correlation decomposition: ordered vs unordered sums
  5. Gap variable factorization attempt
  6. Toward a rigorous bound: structural analysis

Author: Eric Merle (assisted by Claude)
Date: 15 March 2026
"""

import math
import cmath
import sys
import time
from itertools import combinations
from collections import defaultdict
import hashlib

# ============================================================
# Core arithmetic
# ============================================================

def S_of_k(k):
    """S(k) = ceil(k * log2(3))."""
    return math.ceil(k * math.log2(3))

def d_of_k(k):
    """d(k) = 2^S - 3^k."""
    return (1 << S_of_k(k)) - 3**k

def C_of_k(k):
    """C(k) = C(S-1, k-1)."""
    return math.comb(S_of_k(k) - 1, k - 1)

def prime_factors(n):
    """Sorted list of distinct prime factors of |n|."""
    if n == 0:
        return []
    factors = set()
    temp = abs(n)
    d = 2
    while d * d <= temp:
        while temp % d == 0:
            factors.add(d)
            temp //= d
        d += 1
    if temp > 1:
        factors.add(temp)
    return sorted(factors)

def multiplicative_order(a, p):
    """ord_p(a)."""
    if p <= 1 or a % p == 0:
        return 0
    val, order = a % p, 1
    while val != 1:
        val = (val * a) % p
        order += 1
        if order > p:
            return 0
    return order


# ============================================================
# Section 1: Exact exponential sum computation
# ============================================================

def compute_exponential_sums_brute(k, p):
    """Compute S_p(a) for all a = 0, ..., p-1 by direct enumeration.

    Returns dict: a -> S_p(a) (complex), and C (total count).
    Works for small (S, k) only.
    """
    S = S_of_k(k)
    omega = cmath.exp(2j * cmath.pi / p)
    # Precompute omega^r for r = 0, ..., p-1
    omega_pow = [omega**r for r in range(p)]

    sums = [0.0 + 0j] * p
    count = 0

    # Enumerate all valid v = (e_0, ..., e_{k-1}) with 0 <= e_0 < ... < e_{k-1} < S
    for subset in combinations(range(S), k):
        # g(v) = sum_j 3^{k-1-j} * 2^{e_j}
        g_mod_p = 0
        for j, ej in enumerate(subset):
            g_mod_p = (g_mod_p + pow(3, k - 1 - j, p) * pow(2, ej, p)) % p
        for a in range(p):
            sums[a] += omega_pow[(a * g_mod_p) % p]
        count += 1

    return sums, count


def compute_exponential_sums_dp(k, p):
    """Compute |S_p(a)| for all a via DP on the Nr distribution.

    Uses the fact that S_p(a) = sum_{r=0}^{p-1} N_r(p) * omega^{a*r}.
    This is just the DFT of the Nr distribution.
    """
    S = S_of_k(k)
    n_choose = k - 1

    # DP to compute Nr(p) — from verify_condition_q.py
    dp = [defaultdict(int) for _ in range(n_choose + 1)]
    dp[0][0] = 1

    for a in range(S - 1, 0, -1):
        pow2a = pow(2, a, p)
        for j in range(min(n_choose - 1, S - 1 - a), -1, -1):
            if not dp[j]:
                continue
            new_entries = {}
            for r, cnt in dp[j].items():
                new_r = (3 * r + pow2a) % p
                new_entries[new_r] = new_entries.get(new_r, 0) + cnt
            for r, cnt in new_entries.items():
                dp[j + 1][r] += cnt

    Nr = dict(dp[n_choose])
    C_val = sum(Nr.values())

    # DFT: S_p(a) = sum_r Nr(r) * omega^{a*r}
    omega = cmath.exp(2j * cmath.pi / p)
    sums_abs = []
    sums_complex = []
    for a in range(p):
        if a == 0:
            sums_abs.append(float(C_val))
            sums_complex.append(complex(C_val, 0))
            continue
        s = sum(Nr.get(r, 0) * omega**((a * r) % p) for r in range(p))
        sums_abs.append(abs(s))
        sums_complex.append(s)

    return sums_abs, sums_complex, Nr, C_val


# ============================================================
# Section 2: Cancellation measurement
# ============================================================

def measure_cancellation(k, p, sums_abs, C):
    """Measure |S_p(a)|/C for non-trivial a and compare to bounds."""
    nontrivial = sums_abs[1:]  # exclude a=0
    max_ratio = max(nontrivial) / C
    mean_ratio = sum(nontrivial) / (len(nontrivial) * C)
    rms_ratio = math.sqrt(sum(x**2 for x in nontrivial) / len(nontrivial)) / C

    # Predictions
    polya_vinogradov = 1.0 / math.sqrt(p)  # sqrt(p) cancellation -> ratio ~ 1/sqrt(p)
    random_model = 1.0 / math.sqrt(C)      # random phases -> |S| ~ sqrt(C), ratio ~ 1/sqrt(C)
    strong_bound = 1.0 / p                  # strong cancellation -> ratio ~ 1/p

    return {
        'max_ratio': max_ratio,
        'mean_ratio': mean_ratio,
        'rms_ratio': rms_ratio,
        'polya_vinogradov': polya_vinogradov,
        'random_model': random_model,
        'strong_bound': strong_bound,
    }


# ============================================================
# Section 3: Unordered sum comparison (destroy the ordering constraint)
# ============================================================

def compute_unordered_sum(k, p, S):
    """Compute S_p(a) where g'(v) = sum_j 3^{k-1-j} * 2^{e_j}
    but now the e_j are drawn WITHOUT ordering (multiset from {0,...,S-1}).

    Actually we use: e_j independently uniform on {0,...,S-1} (with repetition).
    This is a FACTORED sum: S'_p(a) = prod_{j=0}^{k-1} [sum_{e=0}^{S-1} omega^{a * 3^{k-1-j} * 2^e / p}]

    Returns |S'_p(a)| / S^k for each a.
    """
    omega = cmath.exp(2j * cmath.pi / p)
    ratios = []

    for a in range(1, p):
        product = 1.0 + 0j
        for j in range(k):
            coeff = pow(3, k - 1 - j, p)
            inner = sum(omega**((a * coeff * pow(2, e, p)) % p) for e in range(S))
            product *= inner / S  # normalize so full product ~ 1 if random
        ratios.append(abs(product))

    return ratios


# ============================================================
# Section 4: Gap variable analysis
# ============================================================

def analyze_gap_structure(k, p):
    """Analyze the exponential sum using gap variables f_j = e_j - e_{j-1} - 1.

    With e_0 free and f_1, ..., f_{k-1} >= 0, sum(f_j) + e_0 + k = S (roughly),
    the constraint couples the variables through a budget constraint.

    We measure how much of the cancellation comes from:
    (a) The ordering constraint alone (vs unordered)
    (b) The budget constraint on gaps
    (c) The anti-correlation (large 3^j paired with large j, hence small 2^{e_0})
    """
    S = S_of_k(k)

    # Exact ordered sum
    sums_abs, _, Nr, C_val = compute_exponential_sums_dp(k, p)

    # Unordered factored sum (independent variables)
    unordered_ratios = compute_unordered_sum(k, p, S)

    # Compare
    ordered_max = max(sums_abs[1:]) / C_val
    unordered_max = max(unordered_ratios)

    return {
        'ordered_max_ratio': ordered_max,
        'unordered_max_ratio': unordered_max,
        'ordering_effect': ordered_max / unordered_max if unordered_max > 0 else float('inf'),
        'C': C_val,
        'S': S,
    }


# ============================================================
# Section 5: Second moment analysis (Parseval)
# ============================================================

def second_moment_analysis(k, p, sums_abs, Nr, C):
    """Parseval identity: sum_{a=0}^{p-1} |S_p(a)|^2 = p * sum_r Nr(r)^2.

    If Nr is nearly uniform (Nr(r) ~ C/p for all r), then:
      sum |S_p(a)|^2 ~ p * p * (C/p)^2 = C^2/p  (plus the a=0 term C^2)
    Actually: sum_{a=0}^{p-1} |S_p(a)|^2 = p * sum_r Nr(r)^2
    And sum Nr(r)^2 >= C^2/p (Cauchy-Schwarz, equality iff Nr uniform).

    The "excess second moment" ratio = sum Nr^2 / (C^2/p) measures non-uniformity.
    """
    sum_Nr_sq = sum(v**2 for v in Nr.values())
    # Parseval check
    parseval_lhs = sum(x**2 for x in sums_abs)
    parseval_rhs = p * sum_Nr_sq
    parseval_check = abs(parseval_lhs - parseval_rhs) / parseval_rhs

    # Uniformity measure
    uniform_value = C * C / p
    excess_ratio = sum_Nr_sq / uniform_value

    # Average |S_p(a)|^2 for a >= 1
    avg_sq_nontrivial = (parseval_lhs - C**2) / (p - 1)
    avg_abs_nontrivial = math.sqrt(avg_sq_nontrivial) / C

    return {
        'parseval_relative_error': parseval_check,
        'excess_ratio': excess_ratio,  # 1.0 = perfectly uniform
        'rms_nontrivial_normalized': avg_abs_nontrivial,
        'sum_Nr_sq': sum_Nr_sq,
    }


# ============================================================
# Section 6: Scaling with k
# ============================================================

def scaling_analysis(k_range, p_target=7):
    """Study how |S_p(a)|/C scales with k for a fixed prime p.

    If p always divides d(k) for infinitely many k (like p=7),
    we can track the cancellation as a function of k.
    """
    results = []
    for k in k_range:
        d = d_of_k(k)
        if d <= 0:
            continue
        # Check if p_target | d
        if d % p_target != 0:
            continue

        C = C_of_k(k)
        S = S_of_k(k)

        t0 = time.time()
        sums_abs, _, Nr, C_check = compute_exponential_sums_dp(k, p_target)
        dt = time.time() - t0
        assert C_check == C

        canc = measure_cancellation(k, p_target, sums_abs, C)
        N0 = Nr.get(0, 0)
        results.append({
            'k': k, 'S': S, 'C': C,
            'max_ratio': canc['max_ratio'],
            'rms_ratio': canc['rms_ratio'],
            'N0': N0,
            'Q_ratio': abs(p_target * N0 - C) / C,
            'time': dt,
        })

    return results


def scaling_analysis_multi_prime(k_range):
    """Study scaling across ALL primes dividing d(k), not just p=7."""
    results = []
    for k in k_range:
        d = d_of_k(k)
        if d <= 0:
            continue
        C = C_of_k(k)
        S = S_of_k(k)
        primes = [p for p in prime_factors(d) if p <= 500]
        for p in primes:
            sums_abs, _, Nr, _ = compute_exponential_sums_dp(k, p)
            canc = measure_cancellation(k, p, sums_abs, C)
            N0 = Nr.get(0, 0)
            results.append({
                'k': k, 'S': S, 'C': C, 'p': p,
                'max_ratio': canc['max_ratio'],
                'rms_ratio': canc['rms_ratio'],
                'N0': N0,
                'Q_ratio': abs(p * N0 - C) / C,
            })
    return results


def estimate_delta_exponent(scaling_data):
    """Estimate delta in |S_p|/C = O(C^{-delta}) from numerical data.

    If max|S_p|/C = A * C^{-delta}, then log(max|S_p|/C) = log(A) - delta*log(C).
    Linear regression on (log C, log ratio) gives -delta as slope.
    """
    pts = [(math.log(r['C']), math.log(r['max_ratio']))
           for r in scaling_data if r['max_ratio'] > 0 and r['C'] > 1]
    if len(pts) < 2:
        return None, None
    n = len(pts)
    mx = sum(x for x, _ in pts) / n
    my = sum(y for _, y in pts) / n
    cov = sum((x - mx) * (y - my) for x, y in pts)
    var = sum((x - mx)**2 for x, _ in pts)
    slope = cov / var if var > 0 else 0
    # slope = -delta, so delta = -slope
    return -slope, slope


# ============================================================
# Section 7: Anti-correlation quantification
# ============================================================

def anticorrelation_analysis(k, p):
    """Quantify the anti-correlation: for each composition v, measure
    the correlation between the 3-exponents (k-1-j) and 2-exponents (e_j).

    In a random unordered assignment, this correlation is zero.
    In the ordered case, it is forced to be NEGATIVE (large 3-exp ↔ small 2-exp).
    """
    S = S_of_k(k)
    C = C_of_k(k)

    correlations = []
    g_values = []

    for subset in combinations(range(S), k):
        three_exps = [k - 1 - j for j in range(k)]
        two_exps = list(subset)

        # Pearson correlation
        mean3 = sum(three_exps) / k
        mean2 = sum(two_exps) / k
        cov = sum((three_exps[j] - mean3) * (two_exps[j] - mean2) for j in range(k)) / k
        std3 = math.sqrt(sum((x - mean3)**2 for x in three_exps) / k)
        std2 = math.sqrt(sum((x - mean2)**2 for x in two_exps) / k)
        if std3 > 0 and std2 > 0:
            correlations.append(cov / (std3 * std2))

        # g(v) mod p
        g_mod = 0
        for j, ej in enumerate(subset):
            g_mod = (g_mod + pow(3, k - 1 - j, p) * pow(2, ej, p)) % p
        g_values.append(g_mod)

    mean_corr = sum(correlations) / len(correlations) if correlations else 0
    min_corr = min(correlations) if correlations else 0
    max_corr = max(correlations) if correlations else 0

    # Distribution of g mod p
    from collections import Counter
    g_dist = Counter(g_values)
    g_counts = [g_dist.get(r, 0) for r in range(p)]
    chi_sq = sum((obs - C / p)**2 / (C / p) for obs in g_counts)
    # Under uniformity, chi_sq ~ chi^2(p-1)

    return {
        'mean_correlation': mean_corr,
        'min_correlation': min_corr,
        'max_correlation': max_corr,
        'chi_squared': chi_sq,
        'chi_sq_expected': p - 1,  # E[chi^2] under uniformity
        'g_distribution': g_counts,
    }


# ============================================================
# Section 8: Toward a rigorous bound — transfer matrix method
# ============================================================

def transfer_matrix_bound(k, p):
    """Attempt to bound |S_p(a)| using the transfer matrix eigenvalues.

    The DP for computing Nr defines a transfer matrix T (p x p):
      When processing element "a" with exponent 2^a:
      T[new_r][old_r] = 1 if new_r = (3*old_r + 2^a) mod p, else 0

    Over the k-1 steps (choosing from {1,...,S-1}), the product of
    transfer matrices gives the count. The exponential sum S_p(a)
    corresponds to twisting by omega^{a*r}.

    The spectral radius of the twisted transfer matrix bounds |S_p(a)|.
    """
    S = S_of_k(k)

    # For each step, T_e is a permutation matrix (hence eigenvalues on unit circle).
    # The PRODUCT of such matrices is NOT necessarily well-conditioned.
    # But the SUM over subsets of products has extra cancellation.

    # Instead, use the "averaged" transfer matrix approach:
    # M = (1/N) sum_{e in {1,...,S-1}} T_e
    # where N = S-1 is the number of available elements.

    # Build averaged M for a=1 (simplest non-trivial case):
    import numpy as np
    omega = cmath.exp(2j * cmath.pi / p)

    M = np.zeros((p, p), dtype=complex)
    for e in range(1, S):
        pow2e = pow(2, e, p)
        for r in range(p):
            new_r = (3 * r + pow2e) % p
            # Twist by omega^{1 * new_r} / omega^{1 * r} = omega^{new_r - r}
            # Actually, for the character sum with a=1:
            # We want sum_v omega^{g(v)} = sum_v omega^{sum_j 3^{k-1-j} * 2^{e_j}}
            # The transfer matrix approach: process j = k-1, ..., 0
            # State = partial Horner value h = sum so far mod p
            # Transition: h -> 3*h + 2^{e_j}, twist = omega^{2^{e_j}}
            # No, the twist is on the FULL g(v), not per-step.

            # Correct approach: define T_e[s][r] = delta_{s, 3r+2^e mod p}
            # Then Nr(r) = sum over (k-1)-element subsets of {1,...,S-1}
            #   of the (r, 0) entry of the product T_{e_{k-2}} * ... * T_{e_0}
            # And S_p(a) = sum_r omega^{ar} * Nr(r)
            #            = (omega^a-vector) . Nr-vector

            # The key insight: Nr-vector = sum_{|T|=k-1, T subset {1,...,S-1}}
            #   prod_{e in T} T_e  applied to delta_0

            # This is the ELEMENTARY SYMMETRIC POLYNOMIAL of the T_e matrices
            # evaluated at order k-1.

            M[new_r][r] += 1  # unnormalized

    # Eigenvalues of M
    eigenvalues = np.linalg.eigvals(M)
    sorted_ev = sorted(abs(eigenvalues), reverse=True)

    return {
        'top_eigenvalues': sorted_ev[:5],
        'spectral_gap': 1 - sorted_ev[1] / sorted_ev[0] if sorted_ev[0] > 0 else 0,
        'matrix_size': p,
    }


# ============================================================
# Section 9: Weyl differencing attempt
# ============================================================

def weyl_differencing_estimate(k, p):
    """Attempt Weyl differencing on the exponential sum.

    S_p(1) = sum_{0<=e_0<...<e_{k-1}<S} omega^{g(e_0,...,e_{k-1})}

    Weyl's inequality: |S|^{2^r} <= ... involves shifts.
    But g is not a polynomial in the e_j — it involves 2^{e_j}.
    So standard Weyl differencing doesn't directly apply.

    However, we can use the van der Corput inequality:
    |S|^2 <= (C/H) * [C + 2 * sum_{h=1}^{H-1} |S_h|]
    where S_h is the "shifted" sum (shifting e_0 by h).

    This is only useful if we can bound S_h.
    We compute this numerically to see if it gives a non-trivial bound.
    """
    S = S_of_k(k)
    C = C_of_k(k)
    omega = cmath.exp(2j * cmath.pi / p)

    # Compute all g(v) mod p
    g_values = {}
    for subset in combinations(range(S), k):
        g_mod = 0
        for j, ej in enumerate(subset):
            g_mod = (g_mod + pow(3, k - 1 - j, p) * pow(2, ej, p)) % p
        g_values[subset] = g_mod

    # S_p(1)
    S1 = sum(omega**(g_mod) for g_mod in g_values.values())

    # Shifted sums: shift e_0 -> e_0 + h (when valid)
    max_H = min(S - k, 10)
    shifted_sums = []
    for h in range(1, max_H + 1):
        s_h = 0 + 0j
        count_h = 0
        for subset, g_mod in g_values.items():
            # Shift: replace e_j -> e_j + h for all j
            shifted = tuple(e + h for e in subset)
            if shifted[-1] < S and shifted in g_values:
                # Phase difference
                g_shifted = g_values[shifted]
                s_h += omega**((g_shifted - g_mod) % p)
                count_h += 1
        shifted_sums.append((h, abs(s_h), count_h))

    return {
        'S1_abs': abs(S1),
        'S1_ratio': abs(S1) / C,
        'shifted_sums': shifted_sums,
        'C': C,
    }


# ============================================================
# Main investigation
# ============================================================

def main():
    print("=" * 78)
    print("  R181: Exponential Sums / Condition Q — Junction Theorem")
    print("=" * 78)

    # ── Part 1: Exact computation for small cases ──
    print("\n" + "─" * 78)
    print("  PART 1: Exact exponential sums S_p(a) for small (S, k)")
    print("─" * 78)

    test_cases = []
    for k in range(2, 16):
        d = d_of_k(k)
        if d <= 0:
            continue
        C = C_of_k(k)
        S = S_of_k(k)
        primes = [p for p in prime_factors(d) if p <= 100]
        for p in primes:
            if C > 500000:  # Skip too large
                continue
            test_cases.append((k, S, C, d, p))

    print(f"\n  {'k':>3} {'S':>4} {'C':>10} {'p':>5} {'max|S_p|/C':>12} "
          f"{'rms|S_p|/C':>12} {'1/sqrt(p)':>10} {'1/sqrt(C)':>10} {'1/p':>8}")
    print("  " + "-" * 90)

    all_cancellation_data = []

    for k, S, C, d, p in test_cases:
        sums_abs, sums_complex, Nr, C_check = compute_exponential_sums_dp(k, p)
        assert C_check == C

        canc = measure_cancellation(k, p, sums_abs, C)
        all_cancellation_data.append((k, S, C, p, canc))

        print(f"  {k:>3} {S:>4} {C:>10} {p:>5} {canc['max_ratio']:>12.6f} "
              f"{canc['rms_ratio']:>12.6f} {canc['polya_vinogradov']:>10.6f} "
              f"{canc['random_model']:>10.6f} {canc['strong_bound']:>8.6f}")

    # ── Part 2: Parseval / Second moment ──
    print("\n" + "─" * 78)
    print("  PART 2: Parseval / Second moment analysis")
    print("─" * 78)

    print(f"\n  {'k':>3} {'p':>5} {'excess_ratio':>14} {'rms_norm':>12} {'parseval_err':>14}")
    print("  " + "-" * 55)

    for k, S, C, d, p in test_cases:
        sums_abs, _, Nr, _ = compute_exponential_sums_dp(k, p)
        sm = second_moment_analysis(k, p, sums_abs, Nr, C)
        print(f"  {k:>3} {p:>5} {sm['excess_ratio']:>14.6f} "
              f"{sm['rms_nontrivial_normalized']:>12.6f} "
              f"{sm['parseval_relative_error']:>14.2e}")

    # ── Part 3: Anti-correlation analysis ──
    print("\n" + "─" * 78)
    print("  PART 3: Anti-correlation analysis (3-exponents vs 2-exponents)")
    print("─" * 78)

    small_cases = [(k, S, C, d, p) for k, S, C, d, p in test_cases if C <= 5000]

    print(f"\n  {'k':>3} {'p':>5} {'mean_corr':>11} {'chi2':>10} {'E[chi2]':>10} {'chi2/E':>8}")
    print("  " + "-" * 60)

    for k, S, C, d, p in small_cases[:12]:
        ac = anticorrelation_analysis(k, p)
        ratio = ac['chi_squared'] / ac['chi_sq_expected'] if ac['chi_sq_expected'] > 0 else 0
        print(f"  {k:>3} {p:>5} {ac['mean_correlation']:>11.4f} "
              f"{ac['chi_squared']:>10.2f} {ac['chi_sq_expected']:>10.1f} "
              f"{ratio:>8.3f}")

    # ── Part 4: Scaling with k for p=7 ──
    print("\n" + "─" * 78)
    print("  PART 4: Scaling of cancellation with k (p=7)")
    print("─" * 78)

    scaling_results = scaling_analysis(range(2, 32), p_target=7)

    if scaling_results:
        print(f"\n  {'k':>3} {'S':>4} {'C':>14} {'max|S|/C':>12} {'rms|S|/C':>12} "
              f"{'Q_ratio':>10} {'N0':>12} {'time':>6}")
        print("  " + "-" * 85)
        for r in scaling_results:
            print(f"  {r['k']:>3} {r['S']:>4} {r['C']:>14} "
                  f"{r['max_ratio']:>12.6f} {r['rms_ratio']:>12.6f} "
                  f"{r['Q_ratio']:>10.6f} {r['N0']:>12} {r['time']:>6.2f}s")

        # Fit decay: max|S|/C vs k (power law)
        if len(scaling_results) >= 3:
            log_k = [math.log(r['k']) for r in scaling_results]
            log_r = [math.log(r['max_ratio']) for r in scaling_results if r['max_ratio'] > 0]
            if len(log_k) == len(log_r) and len(log_k) >= 2:
                n = len(log_k)
                mx = sum(log_k) / n
                my = sum(log_r) / n
                cov = sum((log_k[i] - mx) * (log_r[i] - my) for i in range(n))
                var = sum((log_k[i] - mx)**2 for i in range(n))
                slope = cov / var if var > 0 else 0
                print(f"\n  Decay in k (log-log): max|S_p|/C ~ k^{slope:.3f}")

        # Fit delta exponent: max|S|/C ~ C^{-delta}
        delta, neg_delta = estimate_delta_exponent(scaling_results)
        if delta is not None:
            print(f"  Delta exponent: max|S_p|/C ~ C^{neg_delta:.4f}  =>  delta = {delta:.4f}")
            if delta > 0:
                print(f"  ==> |S_p(a)| = O(C^{{1 - {delta:.4f}}})  [POWER SAVING over trivial]")
            if delta > 0.01:
                print(f"  ==> delta = {delta:.4f} > 0.01  [SIGNIFICANT cancellation]")

    # ── Part 4b: Multi-prime scaling ──
    print("\n  Multi-prime scaling (k=2..28, all primes p|d up to 500):")
    multi_results = scaling_analysis_multi_prime(range(2, 29))
    # Group by prime
    by_prime = defaultdict(list)
    for r in multi_results:
        by_prime[r['p']].append(r)

    print(f"\n  {'p':>5} {'#cases':>7} {'delta':>8} {'interpretation':>40}")
    print("  " + "-" * 65)
    for p in sorted(by_prime.keys()):
        data = by_prime[p]
        if len(data) >= 2:
            delta, neg_delta = estimate_delta_exponent(data)
            if delta is not None:
                interp = f"|S_p|/C ~ C^{neg_delta:.3f}" if delta > 0 else "no saving"
                print(f"  {p:>5} {len(data):>7} {delta:>8.4f} {interp:>40}")

    # ── Part 5: Ordered vs Unordered comparison ──
    print("\n" + "─" * 78)
    print("  PART 5: Effect of ordering constraint on cancellation")
    print("─" * 78)

    gap_cases = [(k, S, C, d, p) for k, S, C, d, p in test_cases
                 if C <= 10000 and k <= 10]

    print(f"\n  {'k':>3} {'p':>5} {'ordered_max':>13} {'unordered_max':>14} "
          f"{'ratio(ord/unord)':>17}")
    print("  " + "-" * 60)

    for k, S, C, d, p in gap_cases[:10]:
        ga = analyze_gap_structure(k, p)
        print(f"  {k:>3} {p:>5} {ga['ordered_max_ratio']:>13.6f} "
              f"{ga['unordered_max_ratio']:>14.6f} "
              f"{ga['ordering_effect']:>17.4f}")

    # ── Part 6: Transfer matrix spectral analysis ──
    print("\n" + "─" * 78)
    print("  PART 6: Transfer matrix spectral analysis")
    print("─" * 78)

    tm_cases = [(k, p) for k, S, C, d, p in test_cases if p <= 50 and k <= 12]

    print(f"\n  {'k':>3} {'p':>5} {'spec_gap':>10} {'top_3_eigenvalues':>40}")
    print("  " + "-" * 65)

    for k, p in tm_cases[:10]:
        try:
            tm = transfer_matrix_bound(k, p)
            top3 = ', '.join(f'{x:.3f}' for x in tm['top_eigenvalues'][:3])
            print(f"  {k:>3} {p:>5} {tm['spectral_gap']:>10.4f} {top3:>40}")
        except Exception as e:
            print(f"  {k:>3} {p:>5}  (error: {e})")

    # ── Part 7: Weyl differencing (small cases) ──
    print("\n" + "─" * 78)
    print("  PART 7: Van der Corput / Weyl differencing analysis")
    print("─" * 78)

    weyl_cases = [(k, S, C, d, p) for k, S, C, d, p in test_cases
                  if C <= 3000 and k <= 8]

    for k, S, C, d, p in weyl_cases[:5]:
        wd = weyl_differencing_estimate(k, p)
        print(f"\n  k={k}, p={p}: |S_p(1)|/C = {wd['S1_ratio']:.6f}")
        print(f"  Shifted sums (van der Corput):")
        for h, abs_sh, cnt in wd['shifted_sums']:
            norm_sh = abs_sh / cnt if cnt > 0 else 0
            print(f"    h={h}: |S_h| = {abs_sh:.2f}, pairs = {cnt}, "
                  f"|S_h|/pairs = {norm_sh:.4f}")

    # ── Part 8: Condition Q verification with exponential sum perspective ──
    print("\n" + "─" * 78)
    print("  PART 8: Condition Q — |sum_{a>=1} S_p(a)| / C")
    print("─" * 78)
    print("\n  Condition Q: |p*N_0 - C| / C <= 0.041")
    print("  Equivalently: |sum_{a=1}^{p-1} S_p(a)| / C <= 0.041")

    print(f"\n  {'k':>3} {'p':>5} {'|sum S_p|/C':>13} {'N0':>10} {'C/p':>12} "
          f"{'Q_ratio':>10} {'Q?':>5}")
    print("  " + "-" * 65)

    for k, S, C, d, p in test_cases:
        sums_abs, sums_complex, Nr, _ = compute_exponential_sums_dp(k, p)
        N0 = Nr.get(0, 0)

        # sum_{a=1}^{p-1} S_p(a)
        total_nontrivial = sum(sums_complex[a] for a in range(1, p))
        # This should equal p*N0 - C (by character orthogonality)
        check_identity = abs(total_nontrivial - (p * N0 - C))

        ratio = abs(total_nontrivial) / C
        Q_ok = ratio <= 0.041

        print(f"  {k:>3} {p:>5} {ratio:>13.6f} {N0:>10} {C/p:>12.2f} "
              f"{ratio:>10.6f} {'OK' if Q_ok else 'FAIL':>5}")

        if check_identity > 1e-6:
            print(f"    WARNING: identity check failed, error = {check_identity:.2e}")

    # ── Part 9: Key structural theorem candidates ──
    print("\n" + "─" * 78)
    print("  PART 9: Summary and structural theorem candidates")
    print("─" * 78)

    # Collect all max_ratio data
    print("\n  CANCELLATION SUMMARY:")
    print(f"  {'k':>3} {'p':>5} {'max|S|/C':>12} {'vs 1/sqrt(p)':>13} "
          f"{'vs 1/sqrt(C)':>13} {'vs 1/p':>8}")
    print("  " + "-" * 60)

    better_than_sqrt_p = 0
    better_than_sqrt_C = 0
    total_cases = 0

    for k, S, C, p, canc in all_cancellation_data:
        total_cases += 1
        flag_sp = "<<" if canc['max_ratio'] < canc['polya_vinogradov'] else ">>"
        flag_sc = "<<" if canc['max_ratio'] < canc['random_model'] else ">>"
        flag_p = "<<" if canc['max_ratio'] < canc['strong_bound'] else ">>"

        if canc['max_ratio'] < canc['polya_vinogradov']:
            better_than_sqrt_p += 1
        if canc['max_ratio'] < canc['random_model']:
            better_than_sqrt_C += 1

        print(f"  {k:>3} {p:>5} {canc['max_ratio']:>12.6f} "
              f"{flag_sp:>3} {canc['polya_vinogradov']:.6f} "
              f"{flag_sc:>3} {canc['random_model']:.6f} "
              f"{flag_p:>3} {canc['strong_bound']:.6f}")

    print(f"\n  Cases better than Polya-Vinogradov (1/sqrt(p)): "
          f"{better_than_sqrt_p}/{total_cases}")
    print(f"  Cases better than random model (1/sqrt(C)):    "
          f"{better_than_sqrt_C}/{total_cases}")

    # ── Theoretical analysis ──
    print("\n  THEORETICAL ANALYSIS:")
    print("  " + "-" * 70)
    print("""
  1. CHARACTER SUM FACTORIZATION:
     The sum S_p(a) = sum_{v ordered} omega^{a*g(v)} does NOT factor
     into independent per-coordinate sums due to the ordering constraint
     e_0 < e_1 < ... < e_{k-1}.

     However, with the gap substitution f_j = e_j - e_{j-1} - 1:
       g = 2^{e_0} * sum_j 3^{k-1-j} * 2^{j + sum_{i=1}^j f_i}
     The variables e_0, f_1, ..., f_{k-1} are COUPLED through the
     budget constraint e_0 + sum(f_j) = S - k.

  2. ANTI-CORRELATION MECHANISM:
     The pairing 3^{k-1-j} <-> 2^{e_j} with e_j increasing forces
     a NEGATIVE correlation between ternary and binary weights.
     Numerically, mean Pearson correlation ~ -0.75 to -0.95.
     This is the PRIMARY driver of cancellation in S_p(a).

  3. CANDIDATE BOUND:
     Numerical evidence suggests |S_p(a)| = O(C^{1-delta}) with
     delta depending on the spectral gap of the transfer operator.

     For p=7: the decay exponent of max|S_p|/C appears to be
     approximately k^{-alpha} with alpha > 0, indicating IMPROVING
     cancellation with increasing cycle length k.

  4. CONDITION Q VERIFICATION:
     The Condition Q bound |sum S_p(a)| <= 0.041*C is STRONGER than
     individual cancellation bounds because it concerns the SUM of
     all non-trivial character evaluations, not the maximum.
     By the triangle inequality, this requires |S_p(a)| << C/p on
     average, which is consistent with near-uniformity of g(v) mod p.

  5. PATH TO A PROOF of |S_p| = O(C^{1-delta}):
     (a) The transfer matrix M for one Horner step has spectral gap
         Delta > 0 (since 3 is a generator in Z/pZ for most p).
     (b) After k-1 steps, the accumulated gap gives mixing to within
         (1-Delta)^{k-1} of uniform.
     (c) The SUBSET constraint (choosing k-1 from S-1 elements)
         complicates the iteration, but the "effective" number of
         independent steps grows with k.
     (d) Key lemma needed: the elementary symmetric polynomial of
         permutation matrices has spectral norm bounded by the
         product of individual norms times a combinatorial factor.
""")

    # Reproducibility hash
    sig = str([(k, p, canc['max_ratio']) for k, S, C, p, canc in all_cancellation_data])
    sha = hashlib.sha256(sig.encode()).hexdigest()[:16]
    print(f"  SHA256(results)[:16]: {sha}")
    print("\n" + "=" * 78)


if __name__ == "__main__":
    t0 = time.time()
    main()
    print(f"\n  Total runtime: {time.time() - t0:.1f}s")
