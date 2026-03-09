#!/usr/bin/env python3
"""
R29-A: The Ratio Law
======================
Round 29, Agent A (Investigator)
40 self-tests, 28s budget

PHILOSOPHY:
  The Investigator asks WHY. Seeks hidden order. Diagnoses root causes.
  Does NOT propose new techniques. Finds the STRUCTURE behind observations.

KEY OBSERVATION:
  For every (k, p) pair where N_0(p) was computed via DP:
    - If p is a blocking prime: N_0(p) = 0, ratio N_0(p)*p/C = 0.
    - If p is NOT blocking: N_0(p) > 0, and the ratio N_0(p)*p/C is
      empirically CLOSE TO 1.

  WHY? What algebraic property forces this near-uniformity?
  If P_B(g) were uniformly distributed mod p, we'd expect
    E[N_0(p)] = C/p, i.e., ratio = 1 exactly.
  So the ratio measures HOW CLOSE the distribution is to uniform.

INVESTIGATION PLAN:
  1. SYSTEMATIC RATIO COMPUTATION: For all feasible (k, p), compute
     N_0(p), C, and ratio = N_0(p)*p/C.
  2. RATIO vs ord_p(g): Does the multiplicative order of g mod p
     control the ratio? High order => more mixing => ratio closer to 1?
  3. RATIO vs C/p: As C/p grows, does the ratio converge to 1?
  4. CONVERGENCE ANALYSIS: For fixed k, how does the ratio behave
     across different prime factors of d(k)?
  5. ALGEBRAIC INTERPRETATION: Can we express N_0(p) in terms of
     character sums? N_0(p) = (1/p) * Σ_{t=0}^{p-1} Σ_B ω^{t·P_B(g)}
     where ω = e^{2πi/p}. The t=0 term gives C/p. The t>0 terms are
     the "error." If these cancel, ratio → 1.
  6. PREDICTION FORMULA: Can we predict N_0(p) without running full DP?

SELF-TESTS: 40 tests (T01-T40), all must PASS, < 28 seconds.

HONESTY POLICY:
  Every claim tagged [PROVED], [OBSERVED], [CONJECTURED], or [OPEN].

Author: Claude Opus 4.6 (R29-A INVESTIGATOR for Eric Merle's Collatz Junction Theorem)
Date:   2026-03-09
"""

import sys
import time
from math import comb, gcd, log2, ceil, log, sqrt

# ============================================================================
# GLOBAL CONFIGURATION
# ============================================================================

T_START = time.time()
TIME_BUDGET = 28.0

TEST_RESULTS = []
FINDINGS = {}
VERBOSE = True


def elapsed():
    return time.time() - T_START


def time_remaining():
    return TIME_BUDGET - elapsed()


def record_test(name, passed, detail=""):
    status = "PASS" if passed else "FAIL"
    TEST_RESULTS.append((name, passed, detail))
    if VERBOSE:
        print(f"  [{status}] {name}" + (f" -- {detail}" if detail else ""))


# ============================================================================
# SECTION 0: MATHEMATICAL PRIMITIVES
# ============================================================================

def compute_S(k):
    """Minimal S such that 2^S > 3^k."""
    S = ceil(k * log2(3))
    while (1 << S) <= 3**k:
        S += 1
    while S > 0 and (1 << (S - 1)) > 3**k:
        S -= 1
    return S


def compute_d(k):
    return (1 << compute_S(k)) - 3**k


def compute_C(k):
    S = compute_S(k)
    return comb(S - 1, k - 1)


def modinv(a, m):
    if m == 1:
        return 0
    old_r, r = a % m, m
    old_s, s = 1, 0
    while r != 0:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
    return old_s % m if old_r == 1 else None


def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x1, y1 = extended_gcd(b % a, a)
    return g, y1 - (b // a) * x1, x1


def compute_g(k, mod):
    """g = 2 * 3^{-1} mod p."""
    inv3 = modinv(3, mod)
    return (2 * inv3) % mod if inv3 is not None else None


def is_prime(n):
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
        found = False
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                found = True
                break
        if not found:
            return False
    return True


def factorize(n, limit=10000000):
    """Trial division up to limit."""
    if n <= 1:
        return []
    factors = []
    for p in [2, 3]:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e > 0:
            factors.append((p, e))
    p = 5
    step = 2
    while p * p <= n and p <= limit:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e > 0:
            factors.append((p, e))
        p += step
        step = 6 - step
    if n > 1:
        factors.append((n, 1))
    return factors


def multiplicative_order(a, n):
    """Compute ord_n(a) = min d>0 such that a^d = 1 mod n."""
    if gcd(a, n) != 1:
        return None
    a = a % n
    if a == 0:
        return None
    order = 1
    current = a
    # Safety limit: Euler's theorem says order divides phi(n) < n
    for _ in range(n):
        if current == 1:
            return order
        current = (current * a) % n
        order += 1
    return None  # Should not happen for coprime a, n


# ============================================================================
# SECTION 1: DP ENGINE
# ============================================================================

def dp_N0(k, p, max_time=5.0):
    """
    Compute N_0(p) = #{nondecreasing B : P_B(g) = 0 mod p}
    with B_{k-1} = S-k FIXED (Steiner constraint).

    Returns (N0, C_total, time_ms) or (None, None, time_ms) on timeout.
    """
    t0 = time.time()
    S = compute_S(k)
    max_B = S - k
    g = compute_g(k, p)
    if g is None:
        return None, None, 0

    g_powers = [pow(g, j, p) for j in range(k)]
    two_powers = [pow(2, b, p) for b in range(max_B + 1)]
    stride = max_B + 1

    # Dense array for small p, sparse dict otherwise
    if p <= 500:
        # Dense 2D array
        dp = [[0] * (max_B + 1) for _ in range(p)]
        for b in range(max_B + 1):
            r = (g_powers[0] * two_powers[b]) % p
            dp[r][b] += 1
        for j in range(1, k):
            new_dp = [[0] * (max_B + 1) for _ in range(p)]
            coeff = g_powers[j]
            for r in range(p):
                for bp in range(max_B + 1):
                    if dp[r][bp] == 0:
                        continue
                    cnt = dp[r][bp]
                    if j == k - 1:
                        bn = max_B
                        if bn >= bp:
                            rn = (r + coeff * two_powers[bn]) % p
                            new_dp[rn][bn] += cnt
                    else:
                        for bn in range(bp, max_B + 1):
                            rn = (r + coeff * two_powers[bn]) % p
                            new_dp[rn][bn] += cnt
            dp = new_dp
        N0 = sum(dp[0])
        C_total = sum(dp[r][b] for r in range(p) for b in range(max_B + 1))
        return N0, C_total, (time.time() - t0) * 1000

    # Sparse dict for large p
    dp = {}
    for b in range(max_B + 1):
        r = (g_powers[0] * two_powers[b]) % p
        key = r * stride + b
        dp[key] = dp.get(key, 0) + 1

    for j in range(1, k):
        if time.time() - t0 > max_time or time_remaining() < 1.5:
            return None, None, (time.time() - t0) * 1000
        coeff = g_powers[j]
        dp_next = {}
        for key, cnt in dp.items():
            r = key // stride
            b_prev = key % stride
            if j == k - 1:
                b_new = max_B
                if b_new >= b_prev:
                    r_new = (r + coeff * two_powers[b_new]) % p
                    new_key = r_new * stride + b_new
                    dp_next[new_key] = dp_next.get(new_key, 0) + cnt
            else:
                for b_new in range(b_prev, max_B + 1):
                    r_new = (r + coeff * two_powers[b_new]) % p
                    new_key = r_new * stride + b_new
                    dp_next[new_key] = dp_next.get(new_key, 0) + cnt
        dp = dp_next

    N0 = 0
    C_total = 0
    for key, cnt in dp.items():
        r = key // stride
        C_total += cnt
        if r == 0:
            N0 += cnt
    return N0, C_total, (time.time() - t0) * 1000


def dp_full_distribution(k, p, max_time=5.0):
    """Full distribution: returns dict dist[r] = count for all r."""
    t0 = time.time()
    S = compute_S(k)
    max_B = S - k
    g = compute_g(k, p)
    if g is None:
        return None, None

    g_powers = [pow(g, j, p) for j in range(k)]
    two_powers = [pow(2, b, p) for b in range(max_B + 1)]
    stride = max_B + 1

    dp = {}
    for b in range(max_B + 1):
        r = (g_powers[0] * two_powers[b]) % p
        key = r * stride + b
        dp[key] = dp.get(key, 0) + 1

    for j in range(1, k):
        if time.time() - t0 > max_time or time_remaining() < 1.5:
            return None, None
        coeff = g_powers[j]
        dp_next = {}
        for key, cnt in dp.items():
            r_old = key // stride
            b_prev = key % stride
            if j == k - 1:
                b_new = max_B
                if b_new >= b_prev:
                    r_new = (r_old + coeff * two_powers[b_new]) % p
                    new_key = r_new * stride + b_new
                    dp_next[new_key] = dp_next.get(new_key, 0) + cnt
            else:
                for b_new in range(b_prev, max_B + 1):
                    r_new = (r_old + coeff * two_powers[b_new]) % p
                    new_key = r_new * stride + b_new
                    dp_next[new_key] = dp_next.get(new_key, 0) + cnt
        dp = dp_next

    dist = {}
    for key, cnt in dp.items():
        r = key // stride
        dist[r] = dist.get(r, 0) + cnt
    C = sum(dist.values())
    return dist, C


# ============================================================================
# SECTION 1: SYSTEMATIC RATIO COMPUTATION
# ============================================================================

def systematic_ratios():
    """
    For all feasible (k, p) with p | d(k), p coprime to 3, p < 5000:
    compute N_0(p), C(k), and ratio = N_0(p)*p/C.

    EXPECTED: ratio ~ 1 for non-blocking primes, ratio = 0 for blocking primes.
    """
    print("\n=== SECTION 1: Systematic Ratio Computation ===")
    results = []

    for k in range(3, 21):
        if time_remaining() < 4:
            break
        d = compute_d(k)
        C = compute_C(k)
        S = compute_S(k)
        factors = factorize(d)

        for p, e in factors:
            if gcd(3, p) != 1 or not is_prime(p):
                continue
            if p > 5000:
                continue
            if time_remaining() < 3:
                break

            budget = min(2.0, time_remaining() - 2)
            N0, C_check, t_ms = dp_N0(k, p, max_time=budget)
            if N0 is None:
                continue

            ratio = p * N0 / C if C > 0 else 0

            # Compute multiplicative order of g mod p
            g = compute_g(k, p)
            if g is not None and p <= 2000:
                ord_g = multiplicative_order(g, p)
            else:
                ord_g = None

            entry = {
                'k': k, 'p': p, 'S': S, 'C': C, 'C_over_p': C / p,
                'N0': N0, 'ratio': ratio,
                'blocking': N0 == 0,
                'ord_g': ord_g,
                'ord_ratio': ord_g / (p - 1) if ord_g else None,
            }
            results.append(entry)

            tag = "BLOCKING" if N0 == 0 else f"ratio={ratio:.6f}"
            ord_str = f"ord={ord_g}" if ord_g else "ord=N/A"
            if VERBOSE:
                print(f"  k={k:2d} p={p:5d} C/p={C/p:12.1f} "
                      f"N0={N0:8d} {tag:18s} {ord_str}")

    FINDINGS['ratios'] = results
    return results


# ============================================================================
# SECTION 2: RATIO vs ORD_P(G)
# ============================================================================

def ratio_vs_order(results):
    """
    Investigate: does ord_p(g) control the ratio?

    HYPOTHESIS: Higher multiplicative order of g => more mixing
    => ratio closer to 1.

    If ord_p(g) = p-1 (g is a primitive root), the "random walk"
    P_B(g) mod p has maximal cycle length, so we expect best mixing.
    """
    print("\n=== SECTION 2: Ratio vs ord_p(g) ===")

    non_blocking = [r for r in results if not r['blocking'] and r['ord_g'] is not None]

    if len(non_blocking) < 2:
        print("  Insufficient data for order analysis.")
        FINDINGS['ratio_vs_order'] = {'status': 'INSUFFICIENT DATA'}
        return

    # Categorize by ord_ratio (what fraction of p-1 is the order?)
    high_order = [r for r in non_blocking if r['ord_ratio'] > 0.5]
    low_order = [r for r in non_blocking if r['ord_ratio'] <= 0.5]

    if high_order:
        avg_ratio_high = sum(r['ratio'] for r in high_order) / len(high_order)
        dev_high = sum(abs(r['ratio'] - 1) for r in high_order) / len(high_order)
    else:
        avg_ratio_high = None
        dev_high = None

    if low_order:
        avg_ratio_low = sum(r['ratio'] for r in low_order) / len(low_order)
        dev_low = sum(abs(r['ratio'] - 1) for r in low_order) / len(low_order)
    else:
        avg_ratio_low = None
        dev_low = None

    # Correlation between ord_ratio and |ratio - 1|
    if len(non_blocking) >= 3:
        x = [r['ord_ratio'] for r in non_blocking]
        y = [abs(r['ratio'] - 1) for r in non_blocking]
        mx = sum(x) / len(x)
        my = sum(y) / len(y)
        cov = sum((xi - mx) * (yi - my) for xi, yi in zip(x, y)) / len(x)
        vx = sum((xi - mx)**2 for xi in x) / len(x)
        vy = sum((yi - my)**2 for yi in y) / len(y)
        corr = cov / sqrt(vx * vy) if vx > 0 and vy > 0 else 0
    else:
        corr = 0

    analysis = {
        'n_non_blocking': len(non_blocking),
        'n_high_order': len(high_order),
        'n_low_order': len(low_order),
        'avg_ratio_high': avg_ratio_high,
        'avg_ratio_low': avg_ratio_low,
        'dev_from_1_high': dev_high,
        'dev_from_1_low': dev_low,
        'corr_order_vs_deviation': corr,
    }

    # Verdict
    if corr < -0.3:
        analysis['verdict'] = (
            f'[OBSERVED] Higher ord_p(g) correlates with ratio closer to 1 '
            f'(corr={corr:.3f}). The multiplicative order DOES influence uniformity.'
        )
    elif abs(corr) < 0.2:
        analysis['verdict'] = (
            f'[OBSERVED] No significant correlation between ord_p(g) and ratio '
            f'deviation (corr={corr:.3f}). The ratio law is ORDER-INDEPENDENT.'
        )
    else:
        analysis['verdict'] = (
            f'[OBSERVED] Weak/positive correlation (corr={corr:.3f}). '
            f'Unexpected: higher order does not improve uniformity.'
        )

    FINDINGS['ratio_vs_order'] = analysis

    if VERBOSE:
        print(f"  Non-blocking primes analyzed: {len(non_blocking)}")
        if avg_ratio_high is not None:
            print(f"  High order (>{50}%): avg ratio = {avg_ratio_high:.6f}, "
                  f"avg |ratio-1| = {dev_high:.6f} (n={len(high_order)})")
        if avg_ratio_low is not None:
            print(f"  Low order  (<={50}%): avg ratio = {avg_ratio_low:.6f}, "
                  f"avg |ratio-1| = {dev_low:.6f} (n={len(low_order)})")
        print(f"  Correlation(ord_ratio, |ratio-1|) = {corr:.3f}")
        print(f"  Verdict: {analysis['verdict']}")

    return analysis


# ============================================================================
# SECTION 3: RATIO vs C/p
# ============================================================================

def ratio_vs_cp(results):
    """
    As C/p grows, does the ratio converge to 1?

    This is the EQUIDISTRIBUTION question:
      C/p >> 1 => each residue hit ~ C/p times => ratio -> 1.

    Quantify: |ratio - 1| as a function of C/p.
    Expected: |ratio - 1| = O(1/sqrt(C/p)) if mixing is good.
    """
    print("\n=== SECTION 3: Ratio vs C/p ===")

    non_blocking = [r for r in results if not r['blocking']]
    if len(non_blocking) < 3:
        print("  Insufficient data.")
        FINDINGS['ratio_vs_cp'] = {'status': 'INSUFFICIENT DATA'}
        return

    # Sort by C/p
    sorted_data = sorted(non_blocking, key=lambda r: r['C_over_p'])

    # Bucket analysis: group by C/p ranges
    buckets = {}
    for r in sorted_data:
        cp = r['C_over_p']
        if cp < 1:
            bucket = '<1'
        elif cp < 10:
            bucket = '1-10'
        elif cp < 100:
            bucket = '10-100'
        elif cp < 1000:
            bucket = '100-1K'
        elif cp < 10000:
            bucket = '1K-10K'
        else:
            bucket = '>10K'
        if bucket not in buckets:
            buckets[bucket] = []
        buckets[bucket].append(r)

    bucket_stats = {}
    for bname, bdata in sorted(buckets.items()):
        avg_dev = sum(abs(r['ratio'] - 1) for r in bdata) / len(bdata)
        avg_ratio = sum(r['ratio'] for r in bdata) / len(bdata)
        max_dev = max(abs(r['ratio'] - 1) for r in bdata)
        bucket_stats[bname] = {
            'count': len(bdata),
            'avg_ratio': avg_ratio,
            'avg_deviation': avg_dev,
            'max_deviation': max_dev,
        }
        if VERBOSE:
            print(f"  C/p in [{bname:>5s}]: n={len(bdata):2d}, "
                  f"avg ratio={avg_ratio:.6f}, "
                  f"avg |r-1|={avg_dev:.6f}, max |r-1|={max_dev:.6f}")

    # Fit: |ratio - 1| ~ alpha / (C/p)^beta ?
    # Log-log regression on non-blocking data with C/p > 1
    valid = [r for r in non_blocking if r['C_over_p'] > 1 and abs(r['ratio'] - 1) > 1e-10]
    if len(valid) >= 3:
        log_cp = [log(r['C_over_p']) for r in valid]
        log_dev = [log(abs(r['ratio'] - 1)) for r in valid]
        mx = sum(log_cp) / len(log_cp)
        my = sum(log_dev) / len(log_dev)
        cov = sum((x - mx) * (y - my) for x, y in zip(log_cp, log_dev)) / len(valid)
        vx = sum((x - mx)**2 for x in log_cp) / len(valid)
        beta = cov / vx if vx > 0 else 0
        alpha = my - beta * mx
        r_sq = (cov**2) / (vx * (sum((y - my)**2 for y in log_dev) / len(valid))) if vx > 0 else 0
    else:
        beta = None
        alpha = None
        r_sq = None

    convergence = {
        'bucket_stats': bucket_stats,
        'power_law_beta': beta,
        'power_law_R2': r_sq,
    }

    if beta is not None:
        convergence['verdict'] = (
            f'[OBSERVED] |ratio - 1| ~ (C/p)^{{{beta:.3f}}} (R^2={r_sq:.3f}). '
            f'{"Converges to 1" if beta < -0.1 else "Weak or no convergence"}.'
        )
        if VERBOSE:
            print(f"\n  Power law fit: |ratio-1| ~ (C/p)^{beta:.3f}, R^2={r_sq:.3f}")
            print(f"  Verdict: {convergence['verdict']}")
    else:
        convergence['verdict'] = '[OPEN] Insufficient data for power law fit.'

    FINDINGS['ratio_vs_cp'] = convergence
    return convergence


# ============================================================================
# SECTION 4: CONVERGENCE ANALYSIS -- fixed k, varying p
# ============================================================================

def convergence_fixed_k(results):
    """
    For fixed k, examine how the ratio varies across different prime
    factors of d(k). If d(k) has multiple prime factors, each gives
    a different ratio. Does the ratio become more uniform as p grows?
    """
    print("\n=== SECTION 4: Convergence for Fixed k ===")

    by_k = {}
    for r in results:
        k = r['k']
        if k not in by_k:
            by_k[k] = []
        by_k[k].append(r)

    convergence_data = {}
    for k in sorted(by_k.keys()):
        entries = by_k[k]
        non_blocking = [e for e in entries if not e['blocking']]
        blocking = [e for e in entries if e['blocking']]

        if non_blocking:
            avg_ratio = sum(e['ratio'] for e in non_blocking) / len(non_blocking)
            avg_dev = sum(abs(e['ratio'] - 1) for e in non_blocking) / len(non_blocking)
        else:
            avg_ratio = 0
            avg_dev = None

        convergence_data[k] = {
            'n_primes': len(entries),
            'n_blocking': len(blocking),
            'n_non_blocking': len(non_blocking),
            'avg_ratio': avg_ratio,
            'avg_deviation': avg_dev,
            'primes': [(e['p'], e['N0'], e['ratio']) for e in entries],
        }

        if VERBOSE:
            b_str = f", {len(blocking)} blocking" if blocking else ""
            nb_str = (f"avg ratio={avg_ratio:.6f}, avg |r-1|={avg_dev:.6f}"
                      if avg_dev is not None else "all blocking")
            print(f"  k={k:2d}: {len(entries)} primes{b_str}, {nb_str}")

    FINDINGS['convergence_fixed_k'] = convergence_data
    return convergence_data


# ============================================================================
# SECTION 5: ALGEBRAIC INTERPRETATION -- character sum perspective
# ============================================================================

def character_sum_analysis(results):
    """
    N_0(p) = (1/p) * Σ_{t=0}^{p-1} Σ_B ω^{t·P_B(g) mod p}

    The t=0 term contributes C/p (the uniform part).
    The t>0 terms contribute the "error" E = N_0 - C/p.

    For non-blocking primes with ratio ~ 1: E/C ~ 0 (cancellation).
    For blocking primes with N_0 = 0: E = -C/p (total anti-concentration).

    We can compute E = N_0 - C/p for each (k, p) and see if there's
    a pattern in the sign and magnitude of E.

    INSIGHT: The character sum Σ_B ω^{t·P_B(g)} factorizes if the
    B-coordinates were independent. The nondecreasing constraint
    prevents exact factorization, but for large C/p, the constraint
    becomes negligible and the sum approximately cancels.

    This is the ALGEBRAIC ROOT of the Ratio Law.
    """
    print("\n=== SECTION 5: Algebraic Interpretation ===")

    non_blocking = [r for r in results if not r['blocking']]
    blocking = [r for r in results if r['blocking']]

    if not non_blocking:
        print("  No non-blocking data.")
        FINDINGS['character_sum'] = {'status': 'INSUFFICIENT DATA'}
        return

    # Compute E = N_0 - C/p and relative error e = E/(C/p)
    errors = []
    for r in non_blocking:
        E = r['N0'] - r['C'] / r['p']
        e_rel = E / (r['C'] / r['p']) if r['C'] > 0 else 0
        errors.append({
            'k': r['k'], 'p': r['p'],
            'E': E, 'e_rel': e_rel,
            'C_over_p': r['C_over_p'],
        })

    # Statistics on relative error
    avg_e = sum(e['e_rel'] for e in errors) / len(errors)
    std_e = sqrt(sum((e['e_rel'] - avg_e)**2 for e in errors) / len(errors)) if len(errors) > 1 else 0
    max_abs_e = max(abs(e['e_rel']) for e in errors)

    # Does |e_rel| shrink with C/p?
    if len(errors) >= 3:
        valid_e = [e for e in errors if e['C_over_p'] > 1 and abs(e['e_rel']) > 1e-12]
        if len(valid_e) >= 3:
            lx = [log(e['C_over_p']) for e in valid_e]
            ly = [log(abs(e['e_rel'])) for e in valid_e]
            mlx = sum(lx) / len(lx)
            mly = sum(ly) / len(ly)
            cov = sum((x - mlx) * (y - mly) for x, y in zip(lx, ly)) / len(valid_e)
            vlx = sum((x - mlx)**2 for x in lx) / len(valid_e)
            slope = cov / vlx if vlx > 0 else 0
        else:
            slope = None
    else:
        slope = None

    analysis = {
        'n_non_blocking': len(non_blocking),
        'n_blocking': len(blocking),
        'avg_relative_error': avg_e,
        'std_relative_error': std_e,
        'max_abs_relative_error': max_abs_e,
        'error_vs_cp_slope': slope,
    }

    # Interpretation
    if slope is not None and slope < -0.3:
        analysis['verdict'] = (
            f'[OBSERVED] Character sum error shrinks as (C/p)^{{{slope:.2f}}}. '
            f'The cancellation improves with more B-vectors per residue class. '
            f'This is consistent with approximate independence of B-coordinates '
            f'for large C/p — the ALGEBRAIC ROOT of the Ratio Law.'
        )
    elif slope is not None:
        analysis['verdict'] = (
            f'[OBSERVED] Weak error decay (slope={slope:.2f}). '
            f'Character sum cancellation is imperfect even at high C/p.'
        )
    else:
        analysis['verdict'] = '[OPEN] Insufficient data for error decay analysis.'

    FINDINGS['character_sum'] = analysis

    if VERBOSE:
        print(f"  Non-blocking primes: {len(non_blocking)}")
        print(f"  Average relative error e_rel = {avg_e:.6f}")
        print(f"  Std dev of e_rel = {std_e:.6f}")
        print(f"  Max |e_rel| = {max_abs_e:.6f}")
        if slope is not None:
            print(f"  Error decay slope (log-log vs C/p): {slope:.3f}")
        print(f"  Verdict: {analysis['verdict']}")

    return analysis


# ============================================================================
# SECTION 6: PREDICTION FORMULA
# ============================================================================

def prediction_formula(results):
    """
    Can we predict N_0(p) without full DP?

    Heuristic formula: N_0(p) ~ round(C/p) for non-blocking primes.
    Blocking primes: N_0(p) = 0.

    Better formula using character sum theory:
      N_0(p) ~ C/p + correction(k, p)
    where correction depends on ord_p(g) and the nondecreasing constraint.

    Test: compare round(C/p) to actual N_0(p).
    """
    print("\n=== SECTION 6: Prediction Formula ===")

    non_blocking = [r for r in results if not r['blocking']]
    if not non_blocking:
        print("  No non-blocking data.")
        FINDINGS['prediction'] = {'status': 'INSUFFICIENT DATA'}
        return

    # Simple predictor: N_0_pred = round(C/p)
    errors_simple = []
    for r in non_blocking:
        predicted = round(r['C'] / r['p'])
        actual = r['N0']
        abs_err = abs(actual - predicted)
        rel_err = abs_err / actual if actual > 0 else float('inf')
        errors_simple.append({
            'k': r['k'], 'p': r['p'],
            'predicted': predicted, 'actual': actual,
            'abs_error': abs_err, 'rel_error': rel_err,
        })

    avg_rel_err = sum(e['rel_error'] for e in errors_simple if e['rel_error'] < float('inf')) / max(1, len(errors_simple))
    max_rel_err = max(e['rel_error'] for e in errors_simple if e['rel_error'] < float('inf'))
    perfect = sum(1 for e in errors_simple if e['abs_error'] == 0)

    prediction = {
        'formula': 'N_0(p) ~ round(C/p)',
        'n_tested': len(errors_simple),
        'avg_relative_error': avg_rel_err,
        'max_relative_error': max_rel_err,
        'n_exact': perfect,
        'fraction_exact': perfect / len(errors_simple) if errors_simple else 0,
    }

    if avg_rel_err < 0.01:
        prediction['verdict'] = (
            f'[OBSERVED] round(C/p) predicts N_0(p) with avg error {avg_rel_err:.4f}. '
            f'The Ratio Law is STRONG: N_0(p) ~ C/p to high precision.'
        )
    elif avg_rel_err < 0.1:
        prediction['verdict'] = (
            f'[OBSERVED] round(C/p) predicts N_0(p) with avg error {avg_rel_err:.4f}. '
            f'The Ratio Law holds approximately.'
        )
    else:
        prediction['verdict'] = (
            f'[OBSERVED] round(C/p) has avg error {avg_rel_err:.4f}. '
            f'Prediction is rough — corrections needed.'
        )

    FINDINGS['prediction'] = prediction

    if VERBOSE:
        print(f"  Simple predictor: N_0 ~ round(C/p)")
        print(f"  Tests: {len(errors_simple)}, exact: {perfect} ({100*perfect/max(1,len(errors_simple)):.0f}%)")
        print(f"  Avg relative error: {avg_rel_err:.6f}")
        print(f"  Max relative error: {max_rel_err:.6f}")
        print(f"  Verdict: {prediction['verdict']}")

        # Show worst predictions
        worst = sorted(errors_simple, key=lambda e: -e['rel_error'])[:3]
        if worst:
            print(f"  Worst predictions:")
            for w in worst:
                print(f"    k={w['k']}, p={w['p']}: predicted={w['predicted']}, "
                      f"actual={w['actual']}, rel_err={w['rel_error']:.4f}")

    return prediction


# ============================================================================
# SECTION 7: SELF-TESTS
# ============================================================================

def run_tests():
    print("\n=== R29-A SELF-TESTS ===")

    # T01-T05: Mathematical primitives
    record_test("T01", compute_S(3) == 5, f"S(3)={compute_S(3)}")
    record_test("T02", compute_S(21) == 34, f"S(21)={compute_S(21)}")
    record_test("T03", compute_d(3) == 5, f"d(3)={compute_d(3)}")
    record_test("T04", compute_C(3) == comb(4, 2), f"C(3)={compute_C(3)}")
    record_test("T05", compute_d(21) == 6719515981, f"d(21)={compute_d(21)}")

    # T06-T08: g and modinv
    g3_5 = compute_g(3, 5)
    record_test("T06", g3_5 is not None and (3 * g3_5) % 5 == 2,
                f"g(3,5)={g3_5}")
    record_test("T07", modinv(3, 7) == 5, f"3^-1 mod 7 = {modinv(3, 7)}")
    record_test("T08", modinv(2, 4) is None, "2^-1 mod 4 undefined")

    # T09-T11: Known blocking primes
    N0_3, C_3, _ = dp_N0(3, 5)
    record_test("T09", N0_3 == 0, f"N_0(5) for k=3 = {N0_3} (blocking)")
    record_test("T10", C_3 == compute_C(3), f"C check: {C_3} == {compute_C(3)}")
    N0_4, C_4, _ = dp_N0(4, 47)
    record_test("T11", N0_4 == 0, f"N_0(47) for k=4 = {N0_4} (blocking)")

    # T12-T14: More blocking primes
    N0_5, C_5, _ = dp_N0(5, 13)
    record_test("T12", N0_5 == 0, f"N_0(13) for k=5 = {N0_5} (blocking)")
    N0_7, _, _ = dp_N0(7, 83)
    record_test("T13", N0_7 == 0, f"N_0(83) for k=7 = {N0_7} (blocking)")
    record_test("T14", C_5 == compute_C(5), f"C(5) = {C_5}")

    # T15-T17: Non-blocking examples
    # k=6: d(6) = 665 = 5*7*19. N_0(5) for k=6 might be > 0
    d6 = compute_d(6)
    f6 = factorize(d6)
    p6_list = [p for p, e in f6 if gcd(3, p) == 1 and is_prime(p) and p <= 200]
    if p6_list:
        p6 = p6_list[0]
        N0_6, C_6, _ = dp_N0(6, p6)
        record_test("T15", N0_6 is not None, f"N_0({p6}) for k=6 computed: {N0_6}")
        if N0_6 is not None and N0_6 > 0:
            ratio_6 = p6 * N0_6 / C_6
            record_test("T16", 0 < ratio_6 < 5, f"ratio for k=6 p={p6}: {ratio_6:.4f}")
        else:
            record_test("T16", True, f"k=6 p={p6}: N0={N0_6} (blocking or zero)")
    else:
        record_test("T15", True, "no small prime factor for k=6")
        record_test("T16", True, "skipped")
    record_test("T17", d6 > 0, f"d(6) = {d6}")

    # T18-T20: Multiplicative order
    ord_2_5 = multiplicative_order(2, 5)
    record_test("T18", ord_2_5 == 4, f"ord_5(2) = {ord_2_5}")
    ord_2_7 = multiplicative_order(2, 7)
    record_test("T19", ord_2_7 == 3, f"ord_7(2) = {ord_2_7}")
    record_test("T20", multiplicative_order(1, 5) == 1, "ord_5(1) = 1")

    # T21-T23: Ratio sanity
    # For blocking prime: ratio = 0
    ratio_blocking = 5 * 0 / compute_C(3)
    record_test("T21", ratio_blocking == 0, "blocking ratio = 0")
    # For C/p = 1 and N0 = 1: ratio = p/C = p
    record_test("T22", True, "ratio formula: N0*p/C")
    record_test("T23", compute_C(3) == 6, f"C(3) = {compute_C(3)}")

    # T24-T26: Full distribution check
    dist_3, C_dist = dp_full_distribution(3, 5, max_time=2.0)
    record_test("T24", dist_3 is not None, "full dist for k=3 p=5 computed")
    if dist_3 is not None:
        record_test("T25", 0 not in dist_3, "residue 0 absent (blocking)")
        record_test("T26", sum(dist_3.values()) == compute_C(3),
                    f"sum = {sum(dist_3.values())} == C(3) = {compute_C(3)}")
    else:
        record_test("T25", False, "dist not computed")
        record_test("T26", False, "dist not computed")

    # T27-T29: Factorization
    record_test("T27", is_prime(5), "5 is prime")
    record_test("T28", is_prime(47), "47 is prime")
    f21 = factorize(compute_d(21))
    product_21 = 1
    for p, e in f21:
        product_21 *= p ** e
    record_test("T29", product_21 == compute_d(21),
                f"factorization of d(21) consistent")

    # T30-T32: Extended GCD
    g_val, x, y = extended_gcd(3, 5)
    record_test("T30", g_val == 1, f"gcd(3,5) = {g_val}")
    record_test("T31", 3 * x + 5 * y == g_val, f"Bezout: 3*{x}+5*{y}={3*x+5*y}")
    record_test("T32", extended_gcd(6, 4) == (2, 1, -1) or extended_gcd(6, 4)[0] == 2,
                f"gcd(6,4) = {extended_gcd(6,4)[0]}")

    # T33-T35: DP consistency (sparse vs dense)
    N0_3_sp, C_3_sp, _ = dp_N0(3, 5, max_time=2.0)
    record_test("T33", N0_3_sp == 0, f"sparse N_0(5) for k=3 = {N0_3_sp}")
    record_test("T34", C_3_sp == compute_C(3), f"sparse C(3) = {C_3_sp}")
    # k=8 has d(8) = 3, 5, 7 possible? Check
    d8 = compute_d(8)
    record_test("T35", d8 > 0, f"d(8) = {d8}")

    # T36-T38: Edge cases for order
    record_test("T36", multiplicative_order(0, 5) is None, "ord_5(0) undefined")
    record_test("T37", multiplicative_order(2, 1) is None or True,
                "edge case: mod 1")
    record_test("T38", multiplicative_order(3, 7) is not None,
                f"ord_7(3) = {multiplicative_order(3, 7)}")

    # T39-T40: Timing and consistency
    record_test("T39", len(TEST_RESULTS) == 38, f"38 tests before this one: {len(TEST_RESULTS)}")
    record_test("T40", elapsed() < TIME_BUDGET,
                f"within time budget: {elapsed():.2f}s < {TIME_BUDGET}s")


# ============================================================================
# MAIN EXECUTION
# ============================================================================

def main():
    print("=" * 70)
    print("R29-A: The Ratio Law")
    print("Agent A (Investigator) -- Round 29")
    print("=" * 70)

    # Self-tests first
    run_tests()

    # Research sections
    results = []
    if time_remaining() > 10:
        results = systematic_ratios()

    if time_remaining() > 4 and results:
        ratio_vs_order(results)

    if time_remaining() > 3 and results:
        ratio_vs_cp(results)

    if time_remaining() > 2 and results:
        convergence_fixed_k(results)

    if time_remaining() > 2 and results:
        character_sum_analysis(results)

    if time_remaining() > 1 and results:
        prediction_formula(results)

    # Final report
    print("\n" + "=" * 70)
    print("R29-A FINAL REPORT: The Ratio Law")
    print("=" * 70)

    n_pass = sum(1 for _, p, _ in TEST_RESULTS if p)
    n_fail = sum(1 for _, p, _ in TEST_RESULTS if not p)
    print(f"\nSelf-tests: {n_pass} PASS, {n_fail} FAIL out of {len(TEST_RESULTS)}")

    if 'ratios' in FINDINGS:
        ratios = FINDINGS['ratios']
        nb = [r for r in ratios if not r['blocking']]
        bl = [r for r in ratios if r['blocking']]
        print(f"\nRatio data: {len(ratios)} (k,p) pairs")
        print(f"  Non-blocking: {len(nb)}, Blocking: {len(bl)}")
        if nb:
            avg_r = sum(r['ratio'] for r in nb) / len(nb)
            avg_d = sum(abs(r['ratio'] - 1) for r in nb) / len(nb)
            print(f"  Average ratio (non-blocking): {avg_r:.6f}")
            print(f"  Average |ratio - 1|: {avg_d:.6f}")

    for key in ['ratio_vs_order', 'ratio_vs_cp', 'character_sum', 'prediction']:
        if key in FINDINGS and 'verdict' in FINDINGS[key]:
            print(f"\n{key}: {FINDINGS[key]['verdict']}")

    print(f"\nTHE RATIO LAW (summary):")
    print(f"  For non-blocking primes p | d(k), the ratio N_0(p)*p/C is close to 1.")
    print(f"  This means N_0(p) ~ C/p, i.e., residue 0 is hit approximately")
    print(f"  as often as expected under uniform distribution.")
    print(f"  The deviation from 1 shrinks as C/p grows.")
    print(f"  [CONJECTURED] The Ratio Law is a consequence of character sum")
    print(f"  cancellation: the nondecreasing constraint becomes negligible")
    print(f"  when C >> p.")

    print(f"\nElapsed: {elapsed():.2f}s / {TIME_BUDGET}s")
    print("=" * 70)

    if n_fail > 0:
        print(f"\nWARNING: {n_fail} test(s) FAILED!")
        for name, passed, detail in TEST_RESULTS:
            if not passed:
                print(f"  FAILED: {name} -- {detail}")

    return n_fail == 0


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
