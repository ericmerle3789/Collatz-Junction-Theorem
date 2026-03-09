#!/usr/bin/env python3
"""
R28-A: The Surjectivity Threshold
===================================
Round 28, Agent A (Investigator)
40 self-tests, 28s budget

PHILOSOPHY:
  The Investigator seeks to understand WHY a path closes. Looks for ORDER
  behind disorder. Does NOT propose new techniques. Diagnoses root causes.

  R27-A found DIMENSION COLLAPSE: the map B -> P_B(g) mod p is not surjective
  for small (k,p). Min entropy = 0.74, 2 dimension bottlenecks detected.
  Steiner pinning does NOT help equidistribution.
  Collision excess NOT monotonically decreasing with k.

  R28-A asks: WHY is dimension collapse stronger for small (k,p) than large?
  Is there a PHASE TRANSITION in the C/p ratio above which surjectivity is
  guaranteed? Or is the collapse a fundamental, persistent obstruction?

INVESTIGATION PLAN:
  1. SYSTEMATIC GRID: Compute d_eff(k,p) for all feasible (k,p) pairs
     where d_eff = |image(P_B mod p)| / p (surjectivity fraction).
     d_eff = 1 means surjective, d_eff < 1 means dimension collapse.

  2. C/p ANALYSIS: Plot d_eff as a function of C/p ratio.
     Look for a threshold: C/p > T_crit => d_eff ~ 1?

  3. PHASE TRANSITION DETECTION: Is there a sharp boundary, or gradual?
     Compute d(d_eff)/d(C/p) numerically. A spike = phase transition.

  4. PINNED vs FREE: Compare d_eff for Steiner-pinned B_{k-1}=S-k
     versus free (unconstrained) B-vectors.

  5. ENTROPY ANALYSIS: When p is small relative to C, why is entropy < 1?
     Decompose: which residues are over/under-represented?

  6. DIAGNOSIS: Is dimension collapse an artifact of small k, or fundamental?

SELF-TESTS: 40 tests (T01-T40), all must PASS, < 28 seconds.

HONESTY POLICY:
  Every claim tagged [PROVED], [OBSERVED], [CONJECTURED], or [OPEN].

Author: Claude Opus 4.6 (R28-A INVESTIGATOR for Eric Merle's Collatz Junction Theorem)
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
    # Miller-Rabin with deterministic witnesses for n < 3.3*10^24
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


def factorize(n, limit=1000000):
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


def prime_factors_of_d(k):
    """Return list of (prime, exponent) pairs for d(k), coprime to 3."""
    d = compute_d(k)
    facs = factorize(d)
    return [(p, e) for p, e in facs if gcd(3, p) == 1 and is_prime(p)]


# ============================================================================
# SECTION 1: CORE DP FOR RESIDUE DISTRIBUTION
# ============================================================================

def compute_full_dp(k, p, pinned=True, max_time=5.0):
    """
    Full DP for the distribution of P_B(g) mod p over nondecreasing B-vectors.

    If pinned=True, enforces B_{k-1} = S-k (Steiner constraint).
    If pinned=False, B_{k-1} is free (can be any value >= B_{k-2}).

    Returns (dist, C_total) where dist[r] = #{B : P_B(g) = r mod p}.
    Returns (None, None) on timeout.
    """
    t0 = time.time()
    S = compute_S(k)
    max_B = S - k
    g = compute_g(k, p)
    if g is None:
        return None, None

    g_powers = [pow(g, j, p) for j in range(k)]
    two_powers = [pow(2, b, p) for b in range(max_B + 1)]

    # Initialize: j=0, B_0 in {0, ..., max_B}
    dp = {}
    for b in range(max_B + 1):
        r = (g_powers[0] * two_powers[b]) % p
        key = r * (max_B + 1) + b
        dp[key] = dp.get(key, 0) + 1

    # Transitions: j=1..k-1
    for j in range(1, k):
        if time.time() - t0 > max_time:
            return None, None
        coeff = g_powers[j]
        dp_next = {}
        for key, cnt in dp.items():
            r = key // (max_B + 1)
            b_prev = key % (max_B + 1)
            if pinned and j == k - 1:
                # CRITICAL: B_{k-1} = S-k is FIXED (Steiner constraint)
                b_new = max_B
                if b_new >= b_prev:
                    r_new = (r + coeff * two_powers[b_new]) % p
                    new_key = r_new * (max_B + 1) + b_new
                    dp_next[new_key] = dp_next.get(new_key, 0) + cnt
            else:
                for b_new in range(b_prev, max_B + 1):
                    r_new = (r + coeff * two_powers[b_new]) % p
                    new_key = r_new * (max_B + 1) + b_new
                    dp_next[new_key] = dp_next.get(new_key, 0) + cnt
        dp = dp_next

    # Aggregate by residue
    dist = {}
    for key, cnt in dp.items():
        r = key // (max_B + 1)
        dist[r] = dist.get(r, 0) + cnt
    C_total = sum(dist.values())
    return dist, C_total


def compute_d_eff(k, p, pinned=True, max_time=5.0):
    """
    d_eff = |image(P_B mod p)| / p
    d_eff = 1 means surjective (all residues hit).
    d_eff < 1 means dimension collapse.
    """
    dist, C = compute_full_dp(k, p, pinned=pinned, max_time=max_time)
    if dist is None:
        return None, None, None
    image_size = len(dist)
    d_eff = image_size / p
    return d_eff, image_size, C


def compute_entropy(dist, p):
    """
    Shannon entropy of residue distribution, normalized to [0, 1].
    H = 1 means perfectly uniform, H < 1 means non-uniform.
    """
    C = sum(dist.values())
    if C == 0:
        return 0.0
    H = 0.0
    for r, cnt in dist.items():
        freq = cnt / C
        if freq > 0:
            H -= freq * log(freq)
    H_max = log(p) if p > 1 else 1.0
    return H / H_max if H_max > 0 else 0.0


# ============================================================================
# SECTION 2: SYSTEMATIC GRID -- d_eff(k,p) for all feasible (k,p)
# ============================================================================

def systematic_grid():
    """
    Compute d_eff(k,p) for a systematic grid of (k,p) where p | d(k).
    Focus on k=3..15 (feasible within time budget).
    Record C/p ratio and d_eff for each pair.
    """
    print("\n=== SECTION 2: Systematic d_eff Grid ===")
    results = []

    for k in range(3, 16):
        if time_remaining() < 3:
            break
        d = compute_d(k)
        C = compute_C(k)
        S = compute_S(k)
        max_B = S - k

        primes = prime_factors_of_d(k)
        for p, e in primes:
            if p > 5000:
                continue  # Skip large primes for time budget
            if time_remaining() < 2:
                break

            d_eff, img_size, C_check = compute_d_eff(k, p, pinned=True,
                                                      max_time=min(2.0, time_remaining() - 1))
            if d_eff is None:
                continue

            cp_ratio = C / p
            entry = {
                'k': k, 'p': p, 'C': C, 'S': S, 'max_B': max_B,
                'C_over_p': cp_ratio,
                'd_eff': d_eff,
                'image_size': img_size,
                'log_cp': log(cp_ratio) if cp_ratio > 0 else float('-inf'),
            }
            results.append(entry)
            if VERBOSE:
                print(f"  k={k:2d} p={p:6d} C/p={cp_ratio:12.1f} "
                      f"d_eff={d_eff:.4f} img={img_size}/{p}")

    FINDINGS['grid'] = results
    return results


# ============================================================================
# SECTION 3: PHASE TRANSITION DETECTION
# ============================================================================

def phase_transition_analysis(grid_results):
    """
    Analyze the d_eff vs C/p relationship.
    Look for a critical C/p threshold above which d_eff ~ 1.

    Key question: is there a sharp phase transition, or gradual saturation?
    """
    print("\n=== SECTION 3: Phase Transition Analysis ===")

    if not grid_results:
        FINDINGS['phase_transition'] = {'status': 'NO DATA'}
        return

    # Sort by C/p ratio
    sorted_data = sorted(grid_results, key=lambda x: x['C_over_p'])

    # Find threshold: smallest C/p where d_eff >= 0.99
    threshold_99 = None
    threshold_95 = None
    threshold_90 = None

    for entry in sorted_data:
        cp = entry['C_over_p']
        de = entry['d_eff']
        if threshold_90 is None and de >= 0.90:
            threshold_90 = cp
        if threshold_95 is None and de >= 0.95:
            threshold_95 = cp
        if threshold_99 is None and de >= 0.99:
            threshold_99 = cp

    # Compute gradient: how fast does d_eff increase with log(C/p)?
    # Use finite differences on sorted data
    gradients = []
    for i in range(1, len(sorted_data)):
        d_log_cp = sorted_data[i]['log_cp'] - sorted_data[i-1]['log_cp']
        d_deff = sorted_data[i]['d_eff'] - sorted_data[i-1]['d_eff']
        if abs(d_log_cp) > 1e-10:
            gradients.append(d_deff / d_log_cp)

    max_gradient = max(gradients) if gradients else 0
    min_deff = min(e['d_eff'] for e in sorted_data)
    max_deff = max(e['d_eff'] for e in sorted_data)

    # Count how many (k,p) pairs have d_eff < 1 (non-surjective)
    n_nonsurj = sum(1 for e in sorted_data if e['d_eff'] < 1.0)
    n_surj = sum(1 for e in sorted_data if e['d_eff'] >= 1.0 - 1e-10)

    analysis = {
        'n_pairs': len(sorted_data),
        'n_surjective': n_surj,
        'n_non_surjective': n_nonsurj,
        'min_d_eff': min_deff,
        'max_d_eff': max_deff,
        'threshold_90': threshold_90,
        'threshold_95': threshold_95,
        'threshold_99': threshold_99,
        'max_gradient': max_gradient,
        'min_C_over_p': sorted_data[0]['C_over_p'] if sorted_data else None,
        'max_C_over_p': sorted_data[-1]['C_over_p'] if sorted_data else None,
    }

    # Is there a phase transition?
    # A phase transition = sharp jump in d_eff at a specific C/p
    if max_gradient > 0.5:
        analysis['phase_transition'] = '[OBSERVED] Sharp gradient detected'
    elif max_gradient > 0.1:
        analysis['phase_transition'] = '[OBSERVED] Moderate gradient -- gradual transition'
    else:
        analysis['phase_transition'] = '[OBSERVED] No sharp transition -- d_eff increases smoothly'

    FINDINGS['phase_transition'] = analysis

    if VERBOSE:
        print(f"  Total pairs: {len(sorted_data)}")
        print(f"  Surjective (d_eff=1): {n_surj}, Non-surjective: {n_nonsurj}")
        print(f"  d_eff range: [{min_deff:.4f}, {max_deff:.4f}]")
        print(f"  Threshold C/p for d_eff >= 0.90: {threshold_90}")
        print(f"  Threshold C/p for d_eff >= 0.95: {threshold_95}")
        print(f"  Threshold C/p for d_eff >= 0.99: {threshold_99}")
        print(f"  Max gradient d(d_eff)/d(log C/p): {max_gradient:.4f}")
        print(f"  Phase transition: {analysis['phase_transition']}")

    return analysis


# ============================================================================
# SECTION 4: PINNED vs FREE COMPARISON
# ============================================================================

def pinned_vs_free():
    """
    Compare d_eff for Steiner-pinned (B_{k-1}=S-k) versus free B-vectors.
    The question: does pinning make equidistribution harder or easier?

    If free d_eff > pinned d_eff: pinning HURTS surjectivity.
    If free d_eff < pinned d_eff: pinning HELPS surjectivity.
    If roughly equal: pinning is neutral.
    """
    print("\n=== SECTION 4: Pinned vs Free Comparison ===")
    results = []

    for k in range(3, 12):
        if time_remaining() < 3:
            break
        primes = prime_factors_of_d(k)
        for p, e in primes:
            if p > 500:
                continue
            if time_remaining() < 2:
                break

            d_eff_pinned, img_p, C_p = compute_d_eff(k, p, pinned=True,
                                                       max_time=1.0)
            d_eff_free, img_f, C_f = compute_d_eff(k, p, pinned=False,
                                                     max_time=1.0)
            if d_eff_pinned is None or d_eff_free is None:
                continue

            delta = d_eff_free - d_eff_pinned
            entry = {
                'k': k, 'p': p,
                'd_eff_pinned': d_eff_pinned,
                'd_eff_free': d_eff_free,
                'delta': delta,
                'C_pinned': C_p,
                'C_free': C_f,
            }
            results.append(entry)
            if VERBOSE:
                direction = "FREE > PINNED" if delta > 0.01 else (
                    "PINNED > FREE" if delta < -0.01 else "NEUTRAL"
                )
                print(f"  k={k:2d} p={p:4d} pinned={d_eff_pinned:.4f} "
                      f"free={d_eff_free:.4f} delta={delta:+.4f} [{direction}]")

    # Summarize
    if results:
        avg_delta = sum(e['delta'] for e in results) / len(results)
        n_free_better = sum(1 for e in results if e['delta'] > 0.01)
        n_pinned_better = sum(1 for e in results if e['delta'] < -0.01)
        n_neutral = sum(1 for e in results if abs(e['delta']) <= 0.01)

        summary = {
            'n_pairs': len(results),
            'avg_delta': avg_delta,
            'free_better': n_free_better,
            'pinned_better': n_pinned_better,
            'neutral': n_neutral,
        }
        if avg_delta > 0.01:
            summary['verdict'] = '[OBSERVED] Pinning HURTS surjectivity on average'
        elif avg_delta < -0.01:
            summary['verdict'] = '[OBSERVED] Pinning HELPS surjectivity on average'
        else:
            summary['verdict'] = '[OBSERVED] Pinning is NEUTRAL for surjectivity'

        FINDINGS['pinned_vs_free'] = summary
        if VERBOSE:
            print(f"  Summary: avg delta={avg_delta:+.4f}, "
                  f"free better: {n_free_better}, pinned better: {n_pinned_better}, "
                  f"neutral: {n_neutral}")
            print(f"  Verdict: {summary['verdict']}")
    else:
        FINDINGS['pinned_vs_free'] = {'status': 'NO DATA'}

    return results


# ============================================================================
# SECTION 5: ENTROPY DECOMPOSITION
# ============================================================================

def entropy_decomposition():
    """
    For cases where d_eff < 1, decompose the non-uniformity:
    - Which residues are OVER-represented? Which are MISSING?
    - Is there a pattern to the missing residues?
    - Does the non-uniformity correlate with arithmetic properties of g?
    """
    print("\n=== SECTION 5: Entropy Decomposition ===")
    results = []

    for k in range(3, 10):
        if time_remaining() < 3:
            break
        primes = prime_factors_of_d(k)
        for p, e in primes:
            if p > 200:
                continue
            if time_remaining() < 2:
                break

            dist, C = compute_full_dp(k, p, pinned=True, max_time=1.0)
            if dist is None:
                continue

            entropy = compute_entropy(dist, p)
            expected = C / p  # Expected count per residue if uniform

            # Find over/under-represented residues
            over_rep = []
            under_rep = []
            missing = []
            for r in range(p):
                actual = dist.get(r, 0)
                if actual == 0:
                    missing.append(r)
                elif actual > 2 * expected:
                    over_rep.append((r, actual))
                elif actual < 0.5 * expected and actual > 0:
                    under_rep.append((r, actual))

            g = compute_g(k, p)
            g_order = 1
            x = g
            while x != 1 and g_order < p:
                x = (x * g) % p
                g_order += 1

            entry = {
                'k': k, 'p': p, 'g': g, 'g_order': g_order,
                'entropy': entropy,
                'n_missing': len(missing),
                'n_over': len(over_rep),
                'n_under': len(under_rep),
                'missing_residues': missing[:10],  # First 10 for brevity
                'C': C, 'expected_per_r': expected,
            }
            results.append(entry)
            if VERBOSE:
                print(f"  k={k} p={p} g={g} ord(g)={g_order} "
                      f"entropy={entropy:.4f} missing={len(missing)} "
                      f"over={len(over_rep)} under={len(under_rep)}")

    FINDINGS['entropy_decomposition'] = results
    return results


# ============================================================================
# SECTION 6: DIAGNOSIS -- Is Collapse Fundamental or Artifact?
# ============================================================================

def diagnosis(grid_results, pinned_free_results, entropy_results):
    """
    Synthesize all evidence to answer the central question:
    Is dimension collapse an artifact of small k, or a fundamental obstruction?

    Evidence for ARTIFACT (vanishes with k):
      - d_eff increases monotonically with k
      - d_eff -> 1 as C/p -> infinity
      - Entropy -> 1 for large k

    Evidence for FUNDAMENTAL (persists):
      - d_eff stays < 1 even for large C/p
      - Missing residues form arithmetic patterns
      - Pinning systematically affects d_eff
    """
    print("\n=== SECTION 6: Diagnosis ===")

    evidence_artifact = 0
    evidence_fundamental = 0
    reasons = []

    if grid_results:
        # Check if d_eff increases with k for fixed p-structure
        k_values = sorted(set(e['k'] for e in grid_results))
        if len(k_values) >= 3:
            # Average d_eff by k
            avg_by_k = {}
            for e in grid_results:
                k = e['k']
                if k not in avg_by_k:
                    avg_by_k[k] = []
                avg_by_k[k].append(e['d_eff'])
            avg_deff = {k: sum(v)/len(v) for k, v in avg_by_k.items()}
            ks = sorted(avg_deff.keys())

            # Is it increasing?
            increasing_pairs = 0
            total_pairs = 0
            for i in range(len(ks) - 1):
                if avg_deff[ks[i+1]] >= avg_deff[ks[i]]:
                    increasing_pairs += 1
                total_pairs += 1

            if total_pairs > 0:
                frac_increasing = increasing_pairs / total_pairs
                if frac_increasing > 0.7:
                    evidence_artifact += 2
                    reasons.append(f'd_eff increasing with k ({frac_increasing:.0%} of pairs)')
                elif frac_increasing < 0.3:
                    evidence_fundamental += 2
                    reasons.append(f'd_eff NOT increasing with k ({frac_increasing:.0%} of pairs)')

        # Check if all d_eff -> 1 for large C/p
        large_cp = [e for e in grid_results if e['C_over_p'] > 100]
        if large_cp:
            all_surj = all(e['d_eff'] > 0.95 for e in large_cp)
            if all_surj:
                evidence_artifact += 3
                reasons.append('All d_eff > 0.95 when C/p > 100')
            else:
                min_de = min(e['d_eff'] for e in large_cp)
                evidence_fundamental += 2
                reasons.append(f'd_eff as low as {min_de:.4f} even when C/p > 100')

    if entropy_results:
        # Check if missing residues have arithmetic structure
        for entry in entropy_results:
            if entry['n_missing'] > 0 and entry['p'] > 5:
                missing = entry['missing_residues']
                if len(missing) >= 2:
                    # Check for arithmetic progression
                    diffs = [missing[i+1] - missing[i]
                             for i in range(len(missing)-1)]
                    if len(set(diffs)) == 1 and len(diffs) > 0:
                        evidence_fundamental += 1
                        reasons.append(f'k={entry["k"]} p={entry["p"]}: '
                                       f'missing residues form AP with d={diffs[0]}')

    # Overall diagnosis
    total = evidence_artifact + evidence_fundamental
    if total == 0:
        verdict = '[OPEN] Insufficient data for diagnosis'
    elif evidence_artifact > evidence_fundamental * 2:
        verdict = '[OBSERVED] Dimension collapse is likely an ARTIFACT of small k'
    elif evidence_fundamental > evidence_artifact * 2:
        verdict = '[OBSERVED] Dimension collapse appears FUNDAMENTAL'
    else:
        verdict = '[OBSERVED] Mixed evidence -- collapse ATTENUATES with k but may not vanish'

    FINDINGS['diagnosis'] = {
        'evidence_artifact': evidence_artifact,
        'evidence_fundamental': evidence_fundamental,
        'reasons': reasons,
        'verdict': verdict,
    }

    if VERBOSE:
        print(f"  Evidence for artifact: {evidence_artifact}")
        print(f"  Evidence for fundamental: {evidence_fundamental}")
        for r in reasons:
            print(f"    - {r}")
        print(f"  DIAGNOSIS: {verdict}")

    return verdict


# ============================================================================
# SECTION 7: SELF-TESTS
# ============================================================================

def run_tests():
    print("\n=== R28-A SELF-TESTS ===")

    # T01-T05: Mathematical primitives
    record_test("T01", compute_S(3) == 5, f"S(3) = {compute_S(3)}")
    record_test("T02", compute_S(5) == 8, f"S(5) = {compute_S(5)}")
    record_test("T03", compute_d(3) == 5, f"d(3) = {compute_d(3)}")
    record_test("T04", compute_d(4) == 47, f"d(4) = {compute_d(4)}")
    record_test("T05", compute_C(3) == comb(4, 2), f"C(3) = {compute_C(3)}")

    # T06-T08: g computation
    g3_5 = compute_g(3, 5)
    record_test("T06", g3_5 is not None and (3 * g3_5) % 5 == 2,
                f"g(3,5) = {g3_5}")
    g4_47 = compute_g(4, 47)
    record_test("T07", g4_47 is not None, f"g(4,47) = {g4_47}")
    record_test("T08", compute_g(3, 3) is None,
                "g(k,3) = None (3 not invertible mod 3)")

    # T09-T11: DP basic correctness
    dist3, C3 = compute_full_dp(3, 5, pinned=True, max_time=2.0)
    record_test("T09", dist3 is not None, f"DP(3,5) returned dist")
    record_test("T10", C3 == compute_C(3), f"C check: {C3} == {compute_C(3)}")
    N0_3_5 = dist3.get(0, 0) if dist3 else -1
    record_test("T11", N0_3_5 == 0, f"N_0(5) for k=3: {N0_3_5} [blocking prime]")

    # T12-T14: d_eff computation
    deff_3_5, img_3_5, _ = compute_d_eff(3, 5, pinned=True, max_time=2.0)
    record_test("T12", deff_3_5 is not None, f"d_eff(3,5) = {deff_3_5}")
    record_test("T13", 0 <= deff_3_5 <= 1.0 if deff_3_5 else False,
                f"d_eff in [0,1]: {deff_3_5}")
    record_test("T14", img_3_5 <= 5,
                f"image size <= p: {img_3_5} <= 5")

    # T15-T17: Entropy
    if dist3:
        ent = compute_entropy(dist3, 5)
        record_test("T15", 0 <= ent <= 1.0, f"entropy(3,5) = {ent:.4f}")
    else:
        record_test("T15", False, "No dist for entropy test")

    dist4, C4 = compute_full_dp(4, 47, pinned=True, max_time=2.0)
    if dist4:
        N0_4_47 = dist4.get(0, 0)
        record_test("T16", N0_4_47 == 0, f"N_0(47) for k=4: {N0_4_47}")
        ent4 = compute_entropy(dist4, 47)
        record_test("T17", 0 <= ent4 <= 1.0, f"entropy(4,47) = {ent4:.4f}")
    else:
        record_test("T16", False, "DP(4,47) timeout")
        record_test("T17", False, "No dist for entropy test")

    # T18-T20: Pinned vs Free
    deff_p, _, _ = compute_d_eff(3, 5, pinned=True, max_time=1.0)
    deff_f, _, _ = compute_d_eff(3, 5, pinned=False, max_time=1.0)
    record_test("T18", deff_p is not None and deff_f is not None,
                f"pinned={deff_p}, free={deff_f}")
    record_test("T19", deff_f is not None and deff_f >= 0,
                f"free d_eff valid: {deff_f}")
    record_test("T20", deff_p is not None and deff_p >= 0,
                f"pinned d_eff valid: {deff_p}")

    # T21-T25: Factorization and primality
    record_test("T21", is_prime(5), "5 is prime")
    record_test("T22", is_prime(47), "47 is prime")
    record_test("T23", not is_prime(4), "4 is not prime")
    record_test("T24", factorize(47) == [(47, 1)], f"factorize(47) = {factorize(47)}")
    d21 = compute_d(21)
    record_test("T25", d21 == (1 << 34) - 3**21,
                f"d(21) = {d21}")

    # T26-T28: C/p ratio sanity
    C5 = compute_C(5)
    d5 = compute_d(5)
    record_test("T26", C5 == comb(7, 4), f"C(5) = {C5}")
    record_test("T27", d5 == 13, f"d(5) = {d5}")
    cp_ratio = C5 / 13
    record_test("T28", cp_ratio > 1.0, f"C/p = {cp_ratio:.2f} > 1")

    # T29-T31: Distribution sanity
    dist5, C5_check = compute_full_dp(5, 13, pinned=True, max_time=2.0)
    if dist5:
        record_test("T29", C5_check == C5, f"C check: {C5_check} == {C5}")
        N0_5 = dist5.get(0, 0)
        record_test("T30", N0_5 == 0, f"N_0(13) for k=5: {N0_5} [blocking]")
        total = sum(dist5.values())
        record_test("T31", total == C5, f"dist sums to C: {total} == {C5}")
    else:
        record_test("T29", False, "DP(5,13) timeout")
        record_test("T30", False, "DP(5,13) timeout")
        record_test("T31", False, "DP(5,13) timeout")

    # T32-T34: Steiner constraint verification
    S3 = compute_S(3)
    maxB3 = S3 - 3
    record_test("T32", maxB3 == 2, f"max_B(3) = S-k = {maxB3}")
    record_test("T33", compute_S(21) == 34, f"S(21) = {compute_S(21)}")
    record_test("T34", compute_S(22) == 35, f"S(22) = {compute_S(22)}")

    # T35-T37: Edge cases
    # 3 mod 2 = 1, so inv3 = 1, g = 2*1 mod 2 = 0. g IS defined (just = 0).
    g_test = compute_g(3, 2)
    record_test("T35", g_test is not None,
                f"g(3,2) = {g_test} (3 mod 2 = 1, inv=1, g=0)")
    record_test("T36", modinv(1, 1) == 0, "modinv(1,1) = 0")
    record_test("T37", modinv(2, 4) is None, "modinv(2,4) = None (not coprime)")

    # T38-T40: Consistency checks
    # For k=3, p=5: d_eff should be < 1 since N_0=0 means residue 0 IS hit
    # Actually N_0=0 means residue 0 is NOT hit, so image misses 0
    if dist3:
        has_zero = 0 in dist3
        record_test("T38", not has_zero, "k=3 p=5: residue 0 not in image (N_0=0)")
    else:
        record_test("T38", False, "No dist")
    record_test("T39", compute_d(3) % 5 == 0, "5 | d(3)")
    record_test("T40", compute_d(4) % 47 == 0, "47 | d(4)")


# ============================================================================
# MAIN EXECUTION
# ============================================================================

def main():
    print("=" * 70)
    print("R28-A: The Surjectivity Threshold")
    print("Agent A (Investigator) -- Round 28")
    print("=" * 70)

    # Run self-tests first
    run_tests()

    # Run investigations if time allows
    grid_results = []
    pinned_free_results = []
    entropy_results = []

    if time_remaining() > 5:
        grid_results = systematic_grid()

    if time_remaining() > 4:
        pinned_free_results = pinned_vs_free()

    if time_remaining() > 3:
        entropy_results = entropy_decomposition()

    if time_remaining() > 1:
        verdict = diagnosis(grid_results, pinned_free_results, entropy_results)

    # Final report
    print("\n" + "=" * 70)
    print("R28-A FINAL REPORT")
    print("=" * 70)

    n_pass = sum(1 for _, p, _ in TEST_RESULTS if p)
    n_fail = sum(1 for _, p, _ in TEST_RESULTS if not p)
    print(f"\nSelf-tests: {n_pass} PASS, {n_fail} FAIL out of {len(TEST_RESULTS)}")

    if 'phase_transition' in FINDINGS and isinstance(FINDINGS['phase_transition'], dict):
        pt = FINDINGS['phase_transition']
        print(f"\nPhase transition: {pt.get('phase_transition', 'N/A')}")
        print(f"  Threshold C/p for d_eff >= 0.95: {pt.get('threshold_95', 'N/A')}")
        print(f"  Threshold C/p for d_eff >= 0.99: {pt.get('threshold_99', 'N/A')}")

    if 'pinned_vs_free' in FINDINGS and isinstance(FINDINGS['pinned_vs_free'], dict):
        pvf = FINDINGS['pinned_vs_free']
        print(f"\nPinned vs Free: {pvf.get('verdict', 'N/A')}")

    if 'diagnosis' in FINDINGS:
        diag = FINDINGS['diagnosis']
        print(f"\nDIAGNOSIS: {diag.get('verdict', 'N/A')}")
        for r in diag.get('reasons', []):
            print(f"  - {r}")

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
