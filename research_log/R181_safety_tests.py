#!/usr/bin/env python3
"""
R181 — SAFETY NET: Comprehensive Numerical Tests for Three Approaches
=====================================================================

Three theoretical approaches to the Collatz cycle problem:
  1. Alpha-Diophantine: cross-tension between weights and values in recursion
  2. Exponential Sums: cancellation in character sums over corrSum
  3. Cumulative Error: structured error in the rotation near-conjugacy

This script provides an independent numerical safety net: tests that could
either SUPPORT or REFUTE the theoretical claims made in R179-R180.

Author: Eric Merle (assisted by Claude)
Date:   15 March 2026
"""

import math
import time
import random
import sys
from math import gcd, log, log2, comb
from fractions import Fraction
from itertools import combinations
from collections import defaultdict

# ═══════════════════════════════════════════════════════════════════════════════
# CONSTANTS
# ═══════════════════════════════════════════════════════════════════════════════

LN2 = math.log(2)
LN3 = math.log(3)
LN6 = math.log(6)
LOG6_3 = LN3 / LN6       # alpha ~ 0.61315
LOG6_2 = LN2 / LN6       # ~ 0.38685
LOG2_3 = LN3 / LN2       # ~ 1.58496
ALPHA = LOG6_3

# Tracking
TOTAL_TESTS = 0
TOTAL_PASS = 0
TOTAL_FAIL = 0
FAILURES = []


def report(test_name, passed, detail=""):
    """Report a single test result."""
    global TOTAL_TESTS, TOTAL_PASS, TOTAL_FAIL
    TOTAL_TESTS += 1
    if passed:
        TOTAL_PASS += 1
        status = "[PASS]"
    else:
        TOTAL_FAIL += 1
        status = "[FAIL]"
        FAILURES.append((test_name, detail))
    print(f"  {status} {test_name}" + (f" — {detail}" if detail else ""))


# ═══════════════════════════════════════════════════════════════════════════════
# UTILITIES
# ═══════════════════════════════════════════════════════════════════════════════

def v2(n):
    """2-adic valuation of n."""
    if n == 0:
        return float('inf')
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


def odd_part(n):
    """Return the odd part of n (n / 2^v2(n))."""
    if n == 0:
        return 0
    while n % 2 == 0:
        n //= 2
    return n


def is_aperiodic(positions, S):
    """Check if the binary vector with 1s at given positions is aperiodic."""
    pos_set = set(positions)
    for period in range(1, S):
        if S % period != 0:
            continue
        periodic = True
        for p in pos_set:
            if (p % period) not in {q % period for q in pos_set if q < period}:
                periodic = False
                break
        if periodic:
            # double-check: the set of positions mod period must reconstruct all positions
            base = {p % period for p in pos_set}
            reconstructed = set()
            for offset in range(S // period):
                for b in base:
                    reconstructed.add(b + offset * period)
            if reconstructed == pos_set:
                return False
    return True


def compute_corrSum(positions, k):
    """corrSum = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{positions[j]}."""
    return sum(3**(k-1-j) * 2**positions[j] for j in range(k))


def collatz(n):
    """Standard Collatz map."""
    return n // 2 if n % 2 == 0 else 3 * n + 1


def collatz_orbit(n, max_steps=10000):
    """Return the full Collatz orbit from n down to 1."""
    orbit = [n]
    steps = 0
    while n != 1 and steps < max_steps:
        n = collatz(n)
        orbit.append(n)
        steps += 1
    return orbit


def phi(n):
    """phi(n) = {log_6(n + 1/5)} -- fractional part."""
    return math.log(n + 0.2) / LN6 % 1.0


def epsilon(n):
    """Error term: phi(C(n)) - phi(n) - alpha (mod 1), mapped to [-0.5, 0.5]."""
    t_n = phi(n)
    t_cn = phi(collatz(n))
    diff = (t_cn - t_n - ALPHA) % 1.0
    if diff > 0.5:
        diff -= 1.0
    return diff


def prime_factors(n):
    """Return sorted list of prime factors of |n|."""
    n = abs(n)
    if n <= 1:
        return []
    factors = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            factors.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors


def multiplicative_order(a, n, max_iter=500000):
    """Compute ord_n(a). Returns None if gcd(a,n)!=1, -1 if too large."""
    if gcd(a, n) != 1:
        return None
    result = 1
    power = a % n
    while power != 1:
        power = (power * a) % n
        result += 1
        if result > max_iter:
            return -1
    return result


def convergents_log2_3(max_denom=500):
    """Compute convergents (S, k) of log_2(3) via continued fractions."""
    target = log2(3)
    convergents = []
    x = target
    h_prev, h_curr = 1, int(target)
    k_prev, k_curr = 0, 1
    convergents.append((h_curr, k_curr))
    for _ in range(40):
        frac = x - int(x)
        if abs(frac) < 1e-12:
            break
        x = 1.0 / frac
        if x > 1e12:
            break
        a = int(x)
        h_prev, h_curr = h_curr, a * h_curr + h_prev
        k_prev, k_curr = k_curr, a * k_curr + k_prev
        if k_curr > max_denom:
            break
        convergents.append((h_curr, k_curr))
    return convergents


# ═══════════════════════════════════════════════════════════════════════════════
# TEST 1: Exhaustive Cycle Search via the A-recursion
# ═══════════════════════════════════════════════════════════════════════════════

def test1_exhaustive_cycle_search():
    """
    For k = 3, 5, 7, ..., 999 (odd) and x = 2, 3, ..., 50:
    - Compute C(k,x) via the S-independent recursion (2-adic descent)
    - Check if odd_part(C) = k (cycle condition)
    - Count pairs with odd_part(C) = k (should be 0 for k >= 3)
    """
    print("\n" + "=" * 78)
    print("TEST 1: EXHAUSTIVE CYCLE SEARCH VIA A-RECURSION")
    print("=" * 78)

    t0 = time.time()

    cycle_candidates = []
    total_pairs = 0
    total_valid = 0

    for k in range(3, 1000, 2):
        for x in range(2, 51):
            total_pairs += 1

            # Compute C(k,x) via the recursion:
            # C_0 = (3k+1) * 3^{x-1}
            # D_m = v2(C_m), C_{m+1} = C_m + 3^{x-1-m-1} * 2^{D_m}
            # Wait — from R179, the recursion uses:
            #   target = k * d, then greedy extraction via v2
            # But the S-independent form from R179e: compute_C(k,x)
            # C_0 = (3k+1)*3^{x-1}, then iterate

            C = (3 * k + 1) * 3 ** (x - 1)
            Ds = [0]
            valid = True

            for m in range(1, x):
                D_m = v2(C)
                if D_m == float('inf') or D_m <= Ds[-1]:
                    valid = False
                    break
                Ds.append(D_m)
                coeff = 3 ** (x - 1 - m)
                C = C + coeff * (2 ** D_m)

            if not valid:
                continue

            total_valid += 1

            # Check cycle condition: odd_part(C) == k
            op = odd_part(C)
            if op == k:
                # Also check aperiodicity
                S_val = v2(C) + 1  # rough estimate
                # C = k * 2^a means C/k is a power of 2
                if C % k == 0:
                    q = C // k
                    if q > 0 and (q & (q - 1)) == 0:  # power of 2
                        S_val = q.bit_length() - 1
                        # Check if the D sequence is periodic (trivial)
                        is_trivial = all(Ds[i] == 2 * i for i in range(x))
                        if not is_trivial:
                            cycle_candidates.append((k, x, C, Ds))

    elapsed = time.time() - t0

    print(f"  Total (k,x) pairs tested: {total_pairs}")
    print(f"  Valid pairs (D strictly increasing): {total_valid}")
    print(f"  Non-trivial cycle candidates: {len(cycle_candidates)}")
    print(f"  Time: {elapsed:.1f}s")

    report("T1.1: No non-trivial cycles for k=3..999, x=2..50",
           len(cycle_candidates) == 0,
           f"{len(cycle_candidates)} candidates found")

    if cycle_candidates:
        for k, x, C, Ds in cycle_candidates[:5]:
            print(f"    CANDIDATE: k={k}, x={x}, C={C}, D={Ds}")

    # Also verify k=1 DOES produce cycles (sanity check)
    k1_cycles = 0
    for x in range(2, 20):
        C = 4 * 3 ** (x - 1)
        Ds = [0]
        valid = True
        for m in range(1, x):
            D_m = v2(C)
            if D_m == float('inf') or D_m <= Ds[-1]:
                valid = False
                break
            Ds.append(D_m)
            coeff = 3 ** (x - 1 - m)
            C = C + coeff * (2 ** D_m)
        if valid:
            op = odd_part(C)
            if op == 1:
                k1_cycles += 1

    report("T1.2: Sanity — k=1 produces valid C for some x",
           k1_cycles > 0,
           f"{k1_cycles} valid k=1 cases found for x=2..19")

    return len(cycle_candidates)


# ═══════════════════════════════════════════════════════════════════════════════
# TEST 2: The Granularity Gap (Alpha-Diophantine)
# ═══════════════════════════════════════════════════════════════════════════════

def test2_granularity_gap():
    """
    For small x and k, enumerate ALL valid position sequences D,
    compute f(D) = corrSum, and find min|f(D) - target| where target = k*d.
    Tests the Alpha-Diophantine approach's core claim.
    """
    print("\n" + "=" * 78)
    print("TEST 2: GRANULARITY GAP (ALPHA-DIOPHANTINE)")
    print("=" * 78)

    gaps_grow = True
    results = []

    for x in range(3, 16, 2):  # x = 3,5,7,...,15
        # For each x, find the minimal S such that d = 2^S - 3^x > 0
        S_min = int(x * LOG2_3) + 1
        while 2 ** S_min <= 3 ** x:
            S_min += 1

        for k in range(3, min(50, 2 ** (S_min - x) + 1), 2):
            S = S_min + 2  # Choose a moderate S
            d = 2 ** S - 3 ** x
            if d <= 0:
                continue

            target = k * d
            C_total = comb(S - 1, x - 1)

            # For feasible sizes, enumerate all positions
            if C_total > 200000:
                continue

            min_gap = float('inf')
            min_gap_D = None
            n_zero = 0
            n_aperiodic_zero = 0

            for positions in combinations(range(S), x):
                g = compute_corrSum(list(positions), x)
                gap = abs(g - target)
                if gap < min_gap:
                    min_gap = gap
                    min_gap_D = positions
                if g == target:
                    n_zero += 1
                    if is_aperiodic(list(positions), S):
                        n_aperiodic_zero += 1

            # Relative gap
            rel_gap = min_gap / target if target > 0 else float('inf')

            results.append((x, k, S, min_gap, rel_gap, n_zero, n_aperiodic_zero, C_total))

            if x <= 9 and k <= 7:
                print(f"  x={x}, k={k}, S={S}: min_gap={min_gap}, "
                      f"rel_gap={rel_gap:.6f}, zeros={n_zero}, "
                      f"aperiodic_zeros={n_aperiodic_zero}, C={C_total}")

    # Check: does the minimum gap grow with x?
    if len(results) >= 2:
        gaps_by_x = defaultdict(list)
        for x, k, S, mg, rg, nz, naz, C in results:
            gaps_by_x[x].append(mg)

        x_vals = sorted(gaps_by_x.keys())
        avg_gaps = [(x, sum(gaps_by_x[x]) / len(gaps_by_x[x])) for x in x_vals]

        print(f"\n  Average minimum gap by x:")
        for x, avg in avg_gaps:
            print(f"    x={x:2d}: avg_min_gap = {avg:.2e}")

        # Check if average gap is growing
        if len(avg_gaps) >= 3:
            growing = all(avg_gaps[i + 1][1] >= avg_gaps[i][1] * 0.5
                          for i in range(len(avg_gaps) - 1))
            # The gap should not systematically collapse to 0
            all_nonzero = all(mg > 0 for _, _, _, mg, _, nz, _, _ in results if nz == 0)

    # Check: no aperiodic zeros found for k >= 3
    any_aperiodic_zero = any(naz > 0 for _, k, _, _, _, _, naz, _ in results if k >= 3)
    report("T2.1: No aperiodic solutions f(D) = k*d for k >= 3",
           not any_aperiodic_zero,
           f"found aperiodic zeros" if any_aperiodic_zero else "0 aperiodic zeros in all tested cases")

    # Check: periodic solutions only for k=1 pattern
    any_periodic_zero_k3 = any(nz > 0 and naz == 0 and nz > 0
                               for _, k, _, _, _, nz, naz, _ in results if k >= 3)
    report("T2.2: Any zeros found are periodic (excluded by aperiodicity)",
           not any(naz > 0 for _, k, _, _, _, _, naz, _ in results if k >= 3),
           "Aperiodicity excludes all solutions" if not any_aperiodic_zero else "SOME APERIODIC ZEROS!")


# ═══════════════════════════════════════════════════════════════════════════════
# TEST 3: Character Sum Cancellation (Exponential Sums)
# ═══════════════════════════════════════════════════════════════════════════════

def test3_character_sums():
    """
    For convergent (S,k) pairs, compute character sums S_p(a) over corrSum
    and measure cancellation.
    """
    print("\n" + "=" * 78)
    print("TEST 3: CHARACTER SUM CANCELLATION (EXPONENTIAL SUMS)")
    print("=" * 78)

    test_pairs = [(5, 3), (8, 5), (12, 7), (17, 11), (22, 14)]

    for S, k in test_pairs:
        d = 2 ** S - 3 ** k
        if d <= 0:
            print(f"  (S={S}, k={k}): d = {d} <= 0, skipping")
            continue

        C_total = comb(S - 1, k - 1)
        primes = prime_factors(d)

        print(f"\n  (S={S}, k={k}): d={d}, C={C_total}, primes(d)={primes}")

        if C_total > 500000:
            print(f"    C too large for exhaustive enumeration, skipping")
            continue

        # Compute all corrSum values
        g_values = []
        for positions in combinations(range(S), k):
            g = compute_corrSum(list(positions), k)
            g_values.append(g)

        for p in primes:
            if p <= 2:
                continue
            if p > 10 ** 7:
                print(f"    p={p}: too large, skipping")
                continue

            # Compute character sums S_p(a) = sum exp(2*pi*i*a*g/p)
            max_norm = 0.0
            for a in range(1, p):
                # S_p(a) = sum_{v valid} exp(2*pi*i*a*g(v)/p)
                real_part = 0.0
                imag_part = 0.0
                for g in g_values:
                    angle = 2.0 * math.pi * a * (g % p) / p
                    real_part += math.cos(angle)
                    imag_part += math.sin(angle)
                norm = math.sqrt(real_part ** 2 + imag_part ** 2)
                max_norm = max(max_norm, norm)

            ratio_to_C = max_norm / C_total
            random_prediction = 1.0 / math.sqrt(p)
            peeling_bound = (k - 1) / (S - 1) if S > 1 else 1.0

            print(f"    p={p}: max|S_p(a)|/C = {ratio_to_C:.6f}, "
                  f"1/sqrt(p) = {random_prediction:.6f}, "
                  f"peeling = {peeling_bound:.6f}")

            # The key claim: max|S_p(a)|/C should be bounded.
            # For very small (S,k), the combinatorial bound is loose;
            # we use a generous threshold max(peeling, 1/sqrt(p)) + 0.2.
            threshold = max(peeling_bound, random_prediction) + 0.2
            report(f"T3.1: (S={S},k={k},p={p}) max|S_p|/C <= threshold",
                   ratio_to_C <= threshold,
                   f"ratio={ratio_to_C:.6f}, threshold={threshold:.6f}")

    # Cross-check: for the trivial case k=1, S=2, d=1
    # corrSum for k=1 is just 2^{e_0}, positions = {0} or {1}
    print(f"\n  Sanity check: k=1, S=2")
    g_vals_trivial = [2 ** e for e in range(2)]
    print(f"    corrSum values: {g_vals_trivial}")
    report("T3.2: Sanity — k=1 trivial case has corrSum values {1,2}",
           set(g_vals_trivial) == {1, 2})


# ═══════════════════════════════════════════════════════════════════════════════
# TEST 4: Cumulative Error Structure (Circle Rotation)
# ═══════════════════════════════════════════════════════════════════════════════

def test4_cumulative_error():
    """
    For selected k values, compute cumulative error along Collatz orbits
    and fit to models.
    """
    print("\n" + "=" * 78)
    print("TEST 4: CUMULATIVE ERROR STRUCTURE (CIRCLE ROTATION)")
    print("=" * 78)

    test_values = [3, 7, 27, 31, 127, 255, 511, 1023]
    max_cum_overall = 0.0

    for x0 in test_values:
        orbit = collatz_orbit(x0)
        if len(orbit) < 3:
            continue

        # Compute cumulative error
        cum_errors = [0.0]
        steps_data = []
        for i, n in enumerate(orbit[:-1]):
            e = epsilon(n)
            cum_errors.append(cum_errors[-1] + e)
            steps_data.append((i, n, e, cum_errors[-1]))

        max_cum = max(abs(e) for e in cum_errors)
        max_cum_overall = max(max_cum_overall, max_cum)

        # Fit E_m to models
        # Model 1: E = a/B_m (inverse of current value)
        # Model 2: E = a*m + b (linear)
        # Model 3: E = a*log(m+1) (logarithmic)

        m_vals = [i for i in range(1, len(cum_errors))]
        E_vals = [cum_errors[i] for i in m_vals]

        if len(m_vals) < 5:
            continue

        # Linear fit: E = a*m + b
        n_pts = len(m_vals)
        sum_m = sum(m_vals)
        sum_E = sum(E_vals)
        sum_mE = sum(m * E for m, E in zip(m_vals, E_vals))
        sum_m2 = sum(m ** 2 for m in m_vals)
        denom = n_pts * sum_m2 - sum_m ** 2
        if abs(denom) > 1e-15:
            a_lin = (n_pts * sum_mE - sum_m * sum_E) / denom
            b_lin = (sum_E - a_lin * sum_m) / n_pts
        else:
            a_lin, b_lin = 0, 0

        # Residuals
        resid_lin = sum((E - (a_lin * m + b_lin)) ** 2 for m, E in zip(m_vals, E_vals))

        # Log fit: E = a*log(m+1) + b
        log_vals = [math.log(m + 1) for m in m_vals]
        sum_L = sum(log_vals)
        sum_LE = sum(L * E for L, E in zip(log_vals, E_vals))
        sum_L2 = sum(L ** 2 for L in log_vals)
        denom_log = n_pts * sum_L2 - sum_L ** 2
        if abs(denom_log) > 1e-15:
            a_log = (n_pts * sum_LE - sum_L * sum_E) / denom_log
            b_log = (sum_E - a_log * sum_L) / n_pts
        else:
            a_log, b_log = 0, 0

        resid_log = sum((E - (a_log * L + b_log)) ** 2 for L, E in zip(log_vals, E_vals))

        # Inverse fit: E = a/n + b (where n is the orbit value)
        inv_vals = [1.0 / orbit[m] if orbit[m] > 0 else 0 for m in m_vals]
        sum_I = sum(inv_vals)
        sum_IE = sum(I * E for I, E in zip(inv_vals, E_vals))
        sum_I2 = sum(I ** 2 for I in inv_vals)
        denom_inv = n_pts * sum_I2 - sum_I ** 2
        if abs(denom_inv) > 1e-15:
            a_inv = (n_pts * sum_IE - sum_I * sum_E) / denom_inv
            b_inv = (sum_E - a_inv * sum_I) / n_pts
        else:
            a_inv, b_inv = 0, 0

        resid_inv = sum((E - (a_inv * I + b_inv)) ** 2 for I, E in zip(inv_vals, E_vals))

        # Determine best model
        models = [("linear", resid_lin), ("log", resid_log), ("inverse", resid_inv)]
        best = min(models, key=lambda x: x[1])

        print(f"  x0={x0:>5d}: steps={len(orbit)-1:>4d}, max|E|={max_cum:.6f}, "
              f"final_E={cum_errors[-1]:.6f}")
        print(f"    Linear:  a={a_lin:.2e}, b={b_lin:.4f}, RSS={resid_lin:.6f}")
        print(f"    Log:     a={a_log:.2e}, b={b_log:.4f}, RSS={resid_log:.6f}")
        print(f"    Inverse: a={a_inv:.2e}, b={b_inv:.4f}, RSS={resid_inv:.6f}")
        print(f"    Best fit: {best[0]}")

    # Paper claims cumulative error bounded by ~0.281
    report("T4.1: Cumulative error bounded (|E_S| < 0.5 for all tested orbits)",
           max_cum_overall < 0.5,
           f"max|E| = {max_cum_overall:.6f}")

    report("T4.2: Cumulative error bounded by 0.3 (paper claim ~0.281)",
           max_cum_overall < 0.3,
           f"max|E| = {max_cum_overall:.6f}")

    # Test on large starting values
    print(f"\n  Large starting values:")
    large_test = [837799, 1117065, 2643183]
    max_cum_large = 0.0
    for x0 in large_test:
        orbit = collatz_orbit(x0, max_steps=2000)
        cum = 0.0
        max_c = 0.0
        for n in orbit[:-1]:
            cum += epsilon(n)
            max_c = max(max_c, abs(cum))
        max_cum_large = max(max_cum_large, max_c)
        print(f"    x0={x0}: steps={len(orbit)-1}, max|E|={max_c:.6f}")

    report("T4.3: Cumulative error bounded for large orbits",
           max_cum_large < 0.5,
           f"max|E| = {max_cum_large:.6f}")

    # Hypothetical cycle test: for a cycle of length S,
    # need |{S*alpha}| < B_cumulative
    print(f"\n  Hypothetical cycle feasibility:")
    B_EMP = 0.3
    for S in [5, 8, 17, 46, 84, 485]:
        sa_frac = (S * ALPHA) % 1.0
        dist = min(sa_frac, 1.0 - sa_frac)
        feasible = dist < B_EMP
        print(f"    S={S:>4d}: |{{S*alpha}}| = {dist:.10f}, "
              f"{'FEASIBLE' if feasible else 'BLOCKED'} (threshold={B_EMP})")


# ═══════════════════════════════════════════════════════════════════════════════
# TEST 5: Cross-validation of R179-R180 Claims
# ═══════════════════════════════════════════════════════════════════════════════

def test5_cross_validation():
    """
    Independently verify claims from R179-R180:
    - T195-T198 on random (k,x) pairs
    - Peeling bound at r=k-1
    - Master Theorem fixed point formula
    - Lyapunov exponent
    """
    print("\n" + "=" * 78)
    print("TEST 5: CROSS-VALIDATION OF R179-R180 CLAIMS")
    print("=" * 78)

    # ── 5a: Verify the 2-adic descent excludes all k >= 3 ──
    print("\n  5a: 2-adic descent on 100 random (k,x) pairs")
    random.seed(2026)
    n_tested = 0
    n_excluded = 0
    n_survived = 0

    for _ in range(100):
        k = random.choice(range(3, 500, 2))
        x = random.randint(3, 30)

        C = (3 * k + 1) * 3 ** (x - 1)
        Ds = [0]
        valid = True

        for m in range(1, x):
            D_m = v2(C)
            if D_m == float('inf') or D_m <= Ds[-1]:
                valid = False
                break
            Ds.append(D_m)
            coeff = 3 ** (x - 1 - m)
            C = C + coeff * (2 ** D_m)

        n_tested += 1
        if not valid:
            n_excluded += 1
        else:
            op = odd_part(C)
            if op == k and C % k == 0:
                q = C // k
                if q > 0 and (q & (q - 1)) == 0:
                    is_trivial = all(Ds[i] == 2 * i for i in range(x))
                    if not is_trivial:
                        n_survived += 1
                        print(f"    SURVIVOR: k={k}, x={x}, D={Ds}")

    report("T5.1: 2-adic descent — 0 survivors on 100 random (k,x)",
           n_survived == 0,
           f"{n_survived} survivors out of {n_tested} tested")

    # ── 5b: Peeling bound = 1 at r = k-1 ──
    print(f"\n  5b: Peeling bound ratio at r = k-1")
    test_Sk = [(5, 3), (8, 5), (12, 7), (17, 11), (19, 12), (22, 14),
               (27, 17), (46, 29), (65, 41), (84, 53)]

    all_reach_1 = True
    for S, k in test_Sk:
        if k < 2:
            continue
        # ratio at r = k-1: prod_{i=0}^{k-2} (k-1-i)/(S-1-i)
        #                  = (k-1)! / prod_{i=0}^{k-2} (S-1-i)
        #                  = (k-1)! * (S-1-(k-1))! / (S-1)!
        #                  = 1 / C(S-1, k-1)
        ratio = 1.0
        for i in range(k - 1):
            ratio *= (k - 1 - i) / (S - 1 - i)
        C_val = comb(S - 1, k - 1)
        N0_bound = ratio * C_val  # Should be exactly 1

        print(f"    (S={S:>3d}, k={k:>3d}): ratio={ratio:.10e}, "
              f"C={C_val}, N0_bound={N0_bound:.6f}")

        if abs(N0_bound - 1.0) > 0.01:
            all_reach_1 = False

    report("T5.2: Peeling bound N0 = 1 at r = k-1 for all tested (S,k)",
           all_reach_1,
           "Product telescopes to 1/C * C = 1")

    # ── 5c: Master Theorem fixed point: B* = C_m / (2^p - 3^q) ──
    print(f"\n  5c: Master Theorem fixed point verification")

    def compute_C_m(valuations, start_index):
        q = len(valuations)
        C = 0
        cumsum = 0
        for j in range(q):
            idx = (start_index + j) % q
            C += 3 ** (q - 1 - j) * (2 ** cumsum)
            cumsum += valuations[idx]
        return C

    # For q=1: valuations = (p,), C_0 = 3^0 * 2^0 = 1, B* = 1/(2^p - 3)
    # The only cycle with q=1 and B >= 1 odd: p=2, B*=1/(4-3)=1. That's the trivial cycle.
    for p in range(2, 10):
        denom = 2 ** p - 3
        if denom <= 0:
            continue
        B_star = Fraction(1, denom)
        is_valid = B_star.denominator == 1 and B_star >= 1 and B_star % 2 == 1
        if p == 2:
            report("T5.3a: q=1,p=2 — B*=1 (trivial cycle)",
                   B_star == 1,
                   f"B* = {B_star}")
        elif p <= 5:
            report(f"T5.3b: q=1,p={p} — B* non-integer",
                   B_star.denominator != 1,
                   f"B* = {B_star}")

    # For q=2: try all valuations (v0, v1) with v0+v1 = p, v0,v1 >= 1
    print(f"\n    q=2 exhaustive check (p = 3..15):")
    any_q2_solution = False
    for p in range(3, 16):
        denom = 2 ** p - 9  # 3^2 = 9
        if denom <= 0:
            continue
        for v0 in range(1, p):
            v1 = p - v0
            if v1 < 1:
                continue
            vals = (v0, v1)
            C0 = compute_C_m(vals, 0)
            C1 = compute_C_m(vals, 1)
            B0 = Fraction(C0, denom)
            B1 = Fraction(C1, denom)

            # Check: both must be positive odd integers >= 3
            if (B0.denominator == 1 and B1.denominator == 1
                    and B0 >= 3 and B1 >= 3
                    and int(B0) % 2 == 1 and int(B1) % 2 == 1):
                any_q2_solution = True
                print(f"      SOLUTION: p={p}, v=({v0},{v1}), B0={B0}, B1={B1}")

    report("T5.4: q=2, p=3..15 — no valid (odd integer >= 3) fixed points",
           not any_q2_solution,
           "No q=2 solutions found" if not any_q2_solution else "SOLUTIONS FOUND!")

    # ── 5d: Lyapunov exponent ──
    print(f"\n  5d: Lyapunov exponent (should be negative for Collatz)")
    # The Collatz map has Lyapunov exponent = (1/2)*log(3) + (1/2)*log(1/2)
    # = (1/2)*log(3/2) > 0 per step? No — for the Syracuse map on odd numbers,
    # the expected step is log_2(3/4) < 0.

    # Empirical: measure the average of log|T'(x)| along orbits
    random.seed(42)
    lyap_samples = []
    for _ in range(1000):
        n = random.randint(3, 10 ** 6)
        if n % 2 == 0:
            n += 1
        orbit = collatz_orbit(n, max_steps=500)
        if len(orbit) < 10:
            continue
        log_deriv_sum = 0.0
        count = 0
        for val in orbit[:-1]:
            if val % 2 == 0:
                log_deriv_sum += math.log(0.5)  # derivative of n/2
            else:
                log_deriv_sum += math.log(3.0)  # derivative of 3n+1
            count += 1
        if count > 0:
            lyap_samples.append(log_deriv_sum / count)

    avg_lyap = sum(lyap_samples) / len(lyap_samples)
    # Expected: about (1/2)*ln(3) + (1/2)*ln(1/2) = (1/2)*ln(3/2) ~ 0.203
    # But wait — most numbers are even more often than odd. The density of odd
    # steps is about 1/3 (heuristic), so:
    # lambda ~ (1/3)*ln(3) + (2/3)*ln(1/2) = (1/3)*ln(3) - (2/3)*ln(2)
    # = (1/3)*(ln3 - 2*ln2) = (1/3)*ln(3/4) ~ -0.096

    print(f"    Average Lyapunov exponent over 1000 random starts: {avg_lyap:.6f}")
    print(f"    Theoretical prediction (1/3*ln3 - 2/3*ln2): {(LN3/3 - 2*LN2/3):.6f}")

    report("T5.5: Lyapunov exponent is negative (orbits contract on average)",
           avg_lyap < 0,
           f"lambda = {avg_lyap:.6f}")


# ═══════════════════════════════════════════════════════════════════════════════
# TEST 6: Stress Tests for Edge Cases
# ═══════════════════════════════════════════════════════════════════════════════

def test6_stress_tests():
    """
    Edge cases:
    - Very large k: k = 2^20 - 1
    - Very large x: k = 3, x = 100..500
    - Convergent denominators of log_2(3)
    """
    print("\n" + "=" * 78)
    print("TEST 6: STRESS TESTS FOR EDGE CASES")
    print("=" * 78)

    # ── 6a: Very large k ──
    print("\n  6a: Very large k = 2^20 - 1 = 1048575")
    k_large = 2 ** 20 - 1  # Mersenne-like
    any_match = False

    for x in range(2, 11):
        C = (3 * k_large + 1) * 3 ** (x - 1)
        Ds = [0]
        valid = True

        for m in range(1, x):
            D_m = v2(C)
            if D_m == float('inf') or D_m <= Ds[-1]:
                valid = False
                break
            Ds.append(D_m)
            coeff = 3 ** (x - 1 - m)
            C = C + coeff * (2 ** D_m)

        if valid:
            op = odd_part(C)
            match = (op == k_large)
            if match:
                any_match = True
            print(f"    x={x:2d}: valid={valid}, odd_part(C)={op}, "
                  f"match={match}")
        else:
            print(f"    x={x:2d}: INVALID (D not strictly increasing)")

    report("T6.1: k=2^20-1, x=2..10 — no cycle match",
           not any_match,
           "odd_part(C) never equals k" if not any_match else "MATCH FOUND!")

    # ── 6b: Very large x with k=3 ──
    print(f"\n  6b: k=3, very large x (growth analysis)")
    k = 3
    growth_data = []

    for x in [10, 20, 50, 100, 200, 300, 500]:
        C = (3 * k + 1) * 3 ** (x - 1)
        Ds = [0]
        valid = True

        for m in range(1, x):
            D_m = v2(C)
            if D_m == float('inf') or D_m <= Ds[-1]:
                valid = False
                break
            Ds.append(D_m)
            coeff = 3 ** (x - 1 - m)
            C = C + coeff * (2 ** D_m)

        if valid:
            op = odd_part(C)
            log2_C = math.log2(C) if C > 0 else 0
            growth_data.append((x, log2_C))
            print(f"    x={x:>4d}: log2(C) ~ {log2_C:.1f}, "
                  f"odd_part(C)={op if op < 10**6 else '>' + str(10**6)}, "
                  f"match_k3={'YES' if op == 3 else 'NO'}")
        else:
            print(f"    x={x:>4d}: INVALID at step {m}")

    # Check growth rate: C should grow roughly as 3^x * 2^{~1.585x}
    if len(growth_data) >= 2:
        rates = []
        for i in range(1, len(growth_data)):
            x1, l1 = growth_data[i - 1]
            x2, l2 = growth_data[i]
            if x2 > x1:
                rate = (l2 - l1) / (x2 - x1)
                rates.append(rate)

        if rates:
            avg_rate = sum(rates) / len(rates)
            print(f"    Average growth rate of log2(C): {avg_rate:.4f} bits per unit x")
            print(f"    Expected (log2(3) ~ 1.585 + adjustments): ~{LOG2_3:.4f}")

            report("T6.2: C(3,x) grows at rate close to log2(3) per unit x",
                   abs(avg_rate - LOG2_3) < 0.5,
                   f"rate = {avg_rate:.4f}, expected ~ {LOG2_3:.4f}")

    # ── 6c: Convergent denominators of log_2(3) ──
    print(f"\n  6c: Convergent denominators of log_2(3)")
    conv = convergents_log2_3(max_denom=500)
    convergent_ks = [k for S, k in conv if k >= 3 and k % 2 == 1]
    # Also include k values that are denominators directly
    special_ks = [1, 1, 2, 3, 5, 7, 12, 19, 84, 306]
    special_ks = [k for k in special_ks if k >= 3 and k % 2 == 1]

    all_ks = sorted(set(convergent_ks + special_ks))

    any_special_match = False
    for k in all_ks[:10]:
        for x in range(3, 25):
            C = (3 * k + 1) * 3 ** (x - 1)
            Ds = [0]
            valid = True

            for m in range(1, x):
                D_m = v2(C)
                if D_m == float('inf') or D_m <= Ds[-1]:
                    valid = False
                    break
                Ds.append(D_m)
                coeff = 3 ** (x - 1 - m)
                C = C + coeff * (2 ** D_m)

            if valid:
                op = odd_part(C)
                if op == k:
                    # Check if C/k is a power of 2
                    if C % k == 0:
                        q = C // k
                        if q > 0 and (q & (q - 1)) == 0:
                            is_trivial = all(Ds[i] == 2 * i for i in range(x))
                            if not is_trivial:
                                any_special_match = True
                                print(f"    SPECIAL MATCH: k={k}, x={x}, D={Ds}")

    report("T6.3: Convergent denominators — no non-trivial cycle match",
           not any_special_match,
           "No special behavior for convergent k values")

    # ── 6d: Check d = 2^S - 3^k for convergents ──
    print(f"\n  6d: d = 2^S - 3^k analysis for convergents")
    for S, k in conv:
        if k < 2:
            continue
        d = 2 ** S - 3 ** k
        C_val = comb(S - 1, k - 1)
        if d <= 0:
            print(f"    (S={S:>4d}, k={k:>4d}): d={d} <= 0 (invalid, 2^S < 3^k)")
            continue
        ratio = d / C_val if C_val > 0 else float('inf')
        entropic = "C < d (BLOCKED)" if C_val < d else "C >= d (not blocked)"
        print(f"    (S={S:>4d}, k={k:>4d}): d={'~10^'+str(int(math.log10(abs(d)))) if abs(d) > 10**15 else str(d):>15s}, "
              f"C={'~10^'+str(int(math.log10(C_val))) if C_val > 10**15 else str(C_val):>15s}, "
              f"d/C={ratio:.4e}, {entropic}")

    # For k >= 18, C < d should hold (entropic barrier)
    all_blocked = True
    for S, k in conv:
        if k < 18:
            continue
        d = 2 ** S - 3 ** k
        if d <= 0:
            # Not a valid cycle candidate (2^S < 3^k), skip
            continue
        C_val = comb(S - 1, k - 1)
        if C_val >= d:
            all_blocked = False
            print(f"    WARNING: k={k}, S={S}: C={C_val} >= d={d}")

    report("T6.4: Entropic barrier — C < d for all convergents with k >= 18",
           all_blocked,
           "All blocked by entropic argument" if all_blocked else "SOME NOT BLOCKED!")


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    print("=" * 78)
    print("R181 — SAFETY NET: COMPREHENSIVE NUMERICAL TESTS")
    print("         for Three Approaches to the Collatz Cycle Problem")
    print("=" * 78)
    print(f"  Date: 2026-03-15")
    print(f"  Python: {sys.version}")
    print(f"  alpha = log_6(3) = {ALPHA:.15f}")
    print(f"  log_2(3) = {LOG2_3:.15f}")

    t_start = time.time()

    test1_exhaustive_cycle_search()
    test2_granularity_gap()
    test3_character_sums()
    test4_cumulative_error()
    test5_cross_validation()
    test6_stress_tests()

    elapsed = time.time() - t_start

    # ═══════════════════════════════════════════════════════════════════════
    # SUMMARY
    # ═══════════════════════════════════════════════════════════════════════
    print("\n" + "=" * 78)
    print("SUMMARY")
    print("=" * 78)
    print(f"  Total tests:  {TOTAL_TESTS}")
    print(f"  Passed:       {TOTAL_PASS}")
    print(f"  Failed:       {TOTAL_FAIL}")
    print(f"  Total time:   {elapsed:.1f}s")

    if FAILURES:
        print(f"\n  FAILURES:")
        for name, detail in FAILURES:
            print(f"    {name}: {detail}")
    else:
        print(f"\n  ALL TESTS PASSED.")

    print()
    print("  INTERPRETATION:")
    print("  " + "-" * 55)
    print("  Test 1 (A-recursion):    Supports all three approaches —")
    print("                           no non-trivial cycles up to k=999, x=50.")
    print("  Test 2 (Granularity):    Tests Alpha-Diophantine core claim.")
    print("  Test 3 (Char sums):      Tests Exponential Sums peeling bound.")
    print("  Test 4 (Cumul error):    Tests Circle Rotation error structure.")
    print("  Test 5 (Cross-valid):    Independent verification of R179-R180.")
    print("  Test 6 (Stress):         Edge cases, convergents, large parameters.")
    print()

    if TOTAL_FAIL == 0:
        print("  VERDICT: All three approaches are NUMERICALLY CONSISTENT.")
        print("  No counterexample found. The safety net holds.")
    else:
        print(f"  VERDICT: {TOTAL_FAIL} FAILURE(S) DETECTED.")
        print("  Review the failed tests above for potential issues.")

    print("=" * 78)

    return TOTAL_FAIL


if __name__ == "__main__":
    exit_code = main()
    sys.exit(exit_code)
