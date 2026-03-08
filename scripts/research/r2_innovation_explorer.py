#!/usr/bin/env python3
"""
r2_innovation_explorer.py — Discovery Toolbox for the Collatz corrSum Distribution
===================================================================================

Mathematical Setup
------------------
A nontrivial cycle of length k in the 3x+1 map requires:
    d = 2^S - 3^k   where  S = ceil(k * log2(3))

For a composition A = (a_1, ..., a_k) of S into k positive parts:
    corrSum(A) = sum_{j=1}^{k} 3^{k-j} * 2^{a_1+...+a_j}

Equivalently, if B = {b_1 < ... < b_{k-1}} is the (k-1)-subset of {1,...,S-1}
formed by prefix sums b_j = a_1 + ... + a_j, with b_0 = 0 and b_k = S:
    corrSum = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{b_j}

The evaluation map Ev_d sends C(S-1, k-1) compositions to Z/dZ.
A cycle exists iff 0 is in the image.

Known invariants:
    - corrSum is always odd
    - corrSum is never 0 mod 3
    - corrSum mod 4 in {1, 3}

FIVE DISCOVERY TOOLS:
    1. Distribution Fingerprint: histogram + chi-squared + KS + forbidden residues
    2. Modular Pattern Scan: per-prime residue distribution and uniformity
    3. Spectral Analysis: DFT of indicator over Z/pZ, dominant frequencies
    4. Algebraic Invariant Search: forbidden residues mod m for m up to 64
    5. Pair Correlation: additive structure in Im(corrSum)

Author: Claude (discovery toolbox for Eric Merle's Collatz Junction Theorem)
Date:   2026-03-08

Usage:
    python3 r2_innovation_explorer.py          # run all tools
    python3 r2_innovation_explorer.py 1 3      # run tools 1 and 3 only
    python3 r2_innovation_explorer.py selftest  # run self-tests only

Requires: numpy, scipy.stats (will warn if missing but core tools work without).
"""

import math
import hashlib
import sys
import time
import random
import cmath
from itertools import combinations
from collections import Counter, defaultdict

# Optional dependencies
try:
    import numpy as np
    HAS_NUMPY = True
except ImportError:
    HAS_NUMPY = False

try:
    from scipy import stats as sp_stats
    HAS_SCIPY = True
except ImportError:
    HAS_SCIPY = False


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


def distinct_prime_factors(n):
    """Return sorted list of distinct prime factors of |n|."""
    return [p for p, _ in prime_factorization(n)]


def extended_gcd(a, b):
    """Extended Euclidean algorithm.  Returns (gcd, x, y) with a*x + b*y = gcd."""
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x


def modinv(a, m):
    """Modular inverse of a mod m (None if it does not exist)."""
    if m == 1:
        return 0
    g, x, _ = extended_gcd(a % m, m)
    if g != 1:
        return None
    return x % m


def corrsum_from_subset(B_tuple, k, mod):
    """
    Compute corrSum mod `mod` from a (k-1)-subset B of {1,...,S-1}.

    With b_0 = 0:
        corrSum = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{b_j}  mod `mod`
    """
    result = pow(3, k - 1, mod)          # j=0 term: 3^{k-1} * 2^0
    for idx in range(len(B_tuple)):
        j = idx + 1                      # j runs 1 .. k-1
        result = (result + pow(3, k - 1 - j, mod)
                  * pow(2, B_tuple[idx], mod)) % mod
    return result


def corrsum_true(B_tuple, k):
    """
    Compute the TRUE (unreduced) corrSum as a Python integer.
    B_tuple = (b_1,...,b_{k-1}) with b_0 = 0 implicit.
    """
    total = 3 ** (k - 1)                 # j=0
    for idx in range(len(B_tuple)):
        j = idx + 1
        total += 3 ** (k - 1 - j) * 2 ** B_tuple[idx]
    return total


def corrsum_from_composition(parts, mod):
    """
    Compute corrSum mod `mod` from a composition A = (a_1,...,a_k) of S.

    Uses the SUBSET convention:
        corrSum = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{b_j}
    where b_0 = 0, b_j = a_1 + ... + a_j for j = 1..k-1.
    (The last prefix sum b_k = S is NOT included.)
    """
    k = len(parts)
    # b_0 = 0
    result = pow(3, k - 1, mod)  # j=0: 3^{k-1} * 2^0
    prefix = 0
    for j in range(k - 1):     # j = 0..k-2 => contributes b_{j+1}
        prefix += parts[j]
        result = (result + pow(3, k - 2 - j, mod) * pow(2, prefix, mod)) % mod
    return result


def num_compositions(S, k):
    """C(S-1, k-1): number of compositions of S into k positive parts."""
    return math.comb(S - 1, k - 1)


def can_enumerate_exactly(k, limit=5_000_000):
    """True if exhaustive enumeration is feasible."""
    S = compute_S(k)
    return math.comb(S - 1, k - 1) <= limit


# ============================================================================
# ENUMERATION / SAMPLING
# ============================================================================

def enumerate_all_corrsums_mod(k, mod):
    """Exact distribution of corrSum mod `mod`.  Returns Counter."""
    S = compute_S(k)
    counts = Counter()
    for B in combinations(range(1, S), k - 1):
        counts[corrsum_from_subset(B, k, mod)] += 1
    return counts


def sample_corrsums_mod(k, mod, n_samples=200_000):
    """Sampled distribution of corrSum mod `mod`.  Returns Counter."""
    S = compute_S(k)
    pool = list(range(1, S))
    counts = Counter()
    for _ in range(n_samples):
        B = tuple(sorted(random.sample(pool, k - 1)))
        counts[corrsum_from_subset(B, k, mod)] += 1
    return counts


def get_corrsum_distribution(k, mod, n_samples=200_000):
    """
    Returns (Counter, is_exact, total_count).
    Uses exact enumeration when feasible, otherwise sampling.
    """
    if can_enumerate_exactly(k):
        c = enumerate_all_corrsums_mod(k, mod)
        return c, True, sum(c.values())
    else:
        c = sample_corrsums_mod(k, mod, n_samples)
        return c, False, n_samples


# ============================================================================
# SELF-TESTS
# ============================================================================

def run_self_tests():
    """Verify mathematical correctness before running any tool."""
    print("=" * 72)
    print("SELF-TESTS")
    print("=" * 72)

    # ST-1  Basic S, d
    assert compute_S(3) == 5
    assert compute_S(5) == 8
    assert compute_d(3) == 5
    assert compute_d(5) == 13
    print("[PASS] ST-1  S(k) and d(k)")

    # ST-2  Composition <=> subset equivalence
    for kk in (3, 4, 5, 6):
        SS = compute_S(kk)
        dd = compute_d(kk)
        for B in combinations(range(1, SS), kk - 1):
            # build composition from subset
            parts = []
            prev = 0
            for b in B:
                parts.append(b - prev)
                prev = b
            parts.append(SS - prev)
            assert sum(parts) == SS and all(p >= 1 for p in parts)
            v1 = corrsum_from_subset(B, kk, dd)
            v2 = corrsum_from_composition(parts, dd)
            assert v1 == v2, f"k={kk} B={B}: {v1}!={v2}"
    print("[PASS] ST-2  composition <=> subset (k=3..6)")

    # ST-3  corrSum is always odd
    for kk in (3, 4, 5, 6, 7):
        SS = compute_S(kk)
        for B in combinations(range(1, SS), kk - 1):
            assert corrsum_true(B, kk) % 2 == 1
    print("[PASS] ST-3  corrSum always odd (k=3..7)")

    # ST-4  corrSum never 0 mod 3
    for kk in (3, 4, 5, 6, 7):
        SS = compute_S(kk)
        for B in combinations(range(1, SS), kk - 1):
            assert corrsum_true(B, kk) % 3 != 0
    print("[PASS] ST-4  corrSum never 0 mod 3 (k=3..7)")

    # ST-5  corrSum mod 4 in {1, 3}
    for kk in (3, 4, 5, 6, 7):
        SS = compute_S(kk)
        for B in combinations(range(1, SS), kk - 1):
            assert corrsum_true(B, kk) % 4 in (1, 3)
    print("[PASS] ST-5  corrSum mod 4 in {1,3} (k=3..7)")

    # ST-6  No cycles for k=3..10
    for kk in range(3, 11):
        SS = compute_S(kk)
        dd = compute_d(kk)
        for B in combinations(range(1, SS), kk - 1):
            assert corrsum_from_subset(B, kk, dd) != 0
    print("[PASS] ST-6  corrSum != 0 mod d for k=3..10 (no cycles)")

    # ST-7  prime_factorization
    assert prime_factorization(12) == [(2, 2), (3, 1)]
    assert prime_factorization(13) == [(13, 1)]
    assert prime_factorization(100) == [(2, 2), (5, 2)]
    print("[PASS] ST-7  prime_factorization")

    # ST-8  num_compositions
    assert num_compositions(8, 5) == math.comb(7, 4) == 35
    assert num_compositions(5, 3) == math.comb(4, 2) == 6
    print("[PASS] ST-8  num_compositions")

    # ST-9  Tool 1 mini-run on k=3 (d=5, C(4,2)=6)
    counts = enumerate_all_corrsums_mod(3, 5)
    assert sum(counts.values()) == 6, f"Expected 6 compositions, got {sum(counts.values())}"
    assert 0 not in counts, "0 should not be in Im(corrSum) for k=3"
    print("[PASS] ST-9  Tool 1 mini-run k=3")

    # ST-10 Tool 4 mini-run: known invariants reproduced for k=5
    S5 = 8
    hit2, hit3, hit4 = set(), set(), set()
    for B in combinations(range(1, S5), 4):
        cs = corrsum_true(B, 5)
        hit2.add(cs % 2)
        hit3.add(cs % 3)
        hit4.add(cs % 4)
    assert hit2 == {1}
    assert 0 not in hit3
    assert hit4 == {1, 3}
    print("[PASS] ST-10 Known invariants reproduce (k=5)")

    print()
    print("ALL 10 SELF-TESTS PASSED")
    print("=" * 72)
    print()
    return True


# ============================================================================
# TOOL 1: DISTRIBUTION FINGERPRINT
# ============================================================================

def tool1_distribution_fingerprint(k_range=range(3, 21)):
    """
    For each k, compute the full distribution of corrSum(A) mod d.
    - Histogram statistics (min/max/mean count)
    - Chi-squared test against uniform
    - Kolmogorov-Smirnov test
    - Forbidden residues (values never hit)
    - Specifically: what residues mod d are NEVER in Im(corrSum)?
    """
    hdr = "TOOL 1: DISTRIBUTION FINGERPRINT"
    print("\n" + "=" * 72)
    print(hdr)
    print("=" * 72 + "\n")

    summary_rows = []

    for k in k_range:
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)
        primes_d = distinct_prime_factors(d)

        print(f"--- k={k}  S={S}  d={d}  C(S-1,k-1)={C}  primes(d)={primes_d} ---")

        counts, is_exact, total = get_corrsum_distribution(k, d)
        tag = "EXACT" if is_exact else f"SAMPLE({total})"

        n_distinct = len(counts)
        coverage   = n_distinct / d

        # --- forbidden residues ---
        n_forbidden = 0
        forbidden   = []
        if is_exact:
            hit_set   = set(counts.keys())
            forbidden = sorted(set(range(d)) - hit_set)
            n_forbidden = len(forbidden)

        zero_count = counts.get(0, 0)

        # --- histogram statistics ---
        vals      = list(counts.values())
        min_c     = min(vals)
        max_c     = max(vals)
        mean_c    = total / d if d > 0 else 0.0
        median_c  = sorted(vals)[len(vals) // 2]

        # --- chi-squared against uniform ---
        chi2_pval = None
        if is_exact and d <= 100_000:
            expected = total / d
            if expected > 0:
                chi2_stat = sum((counts.get(r, 0) - expected) ** 2 / expected
                                for r in range(d))
                df = d - 1
                if HAS_SCIPY:
                    chi2_pval = float(sp_stats.chi2.sf(chi2_stat, df))

        # --- KS test against uniform ---
        ks_pval = None
        if is_exact and HAS_SCIPY and d <= 100_000 and total > 0:
            all_vals_list = []
            for r, cnt in counts.items():
                all_vals_list.extend([r] * cnt)
            ks_stat, ks_pval = sp_stats.kstest(
                all_vals_list, 'uniform', args=(0, d))
            ks_pval = float(ks_pval)

        # --- report ---
        print(f"  Method:  {tag}")
        print(f"  Distinct residues hit: {n_distinct}/{d}  "
              f"(coverage={coverage:.6f})")
        print(f"  corrSum=0 count: {zero_count}  "
              f"{'>>> NO CYCLE <<<' if zero_count == 0 else '>>> CYCLE CANDIDATE! <<<'}")
        if is_exact:
            print(f"  Forbidden residues: {n_forbidden}")
            if 0 < n_forbidden <= 40:
                print(f"    {forbidden}")
            elif n_forbidden > 40:
                even_f = sum(1 for r in forbidden if r % 2 == 0)
                odd_f  = n_forbidden - even_f
                m3     = Counter(r % 3 for r in forbidden)
                m4     = Counter(r % 4 for r in forbidden)
                print(f"    (showing first 20) {forbidden[:20]}...")
                print(f"    even:{even_f}  odd:{odd_f}  mod3:{dict(m3)}  mod4:{dict(m4)}")
        print(f"  Count range: [{min_c}, {max_c}]  mean={mean_c:.2f}  median={median_c}")
        if chi2_pval is not None:
            print(f"  Chi-squared vs uniform: p={chi2_pval:.4e}")
        if ks_pval is not None:
            print(f"  KS test vs uniform:     p={ks_pval:.4e}")

        # even/odd split
        even_total = sum(counts.get(r, 0) for r in counts if r % 2 == 0)
        odd_total  = total - even_total
        print(f"  Even residue total: {even_total}  Odd: {odd_total}")
        if even_total == 0 and is_exact:
            print(f"  >>> ALL values odd (consistent with known invariant)")

        # top/bottom 5
        top5 = counts.most_common(5)
        bot5 = counts.most_common()[:-6:-1]
        print(f"  Top-5:    {top5}")
        print(f"  Bottom-5: {bot5}")

        summary_rows.append({
            'k': k, 'S': S, 'd': d, 'C': C,
            'n_hit': n_distinct, 'n_forb': n_forbidden if is_exact else '?',
            'coverage': coverage, 'zero_hit': zero_count > 0,
            'chi2_p': chi2_pval, 'ks_p': ks_pval, 'tag': tag
        })
        print()

    # === summary table ===
    print("=" * 72)
    print("TOOL 1  SUMMARY TABLE")
    print("=" * 72)
    hdr_fmt = (f"{'k':>3} {'S':>4} {'d':>12} {'C':>12} "
               f"{'#hit':>8} {'%cov':>8} {'#forb':>6} "
               f"{'0 hit':>5} {'chi2 p':>10}")
    print(hdr_fmt)
    print("-" * len(hdr_fmt))
    for r in summary_rows:
        cp = f"{r['chi2_p']:.2e}" if r['chi2_p'] is not None else "---"
        z  = "Y" if r['zero_hit'] else "N"
        nf = str(r['n_forb'])
        print(f"{r['k']:>3} {r['S']:>4} {r['d']:>12} {r['C']:>12} "
              f"{r['n_hit']:>8} {r['coverage']:>8.4f} {nf:>6} "
              f"{z:>5} {cp:>10}")
    print()
    return summary_rows


# ============================================================================
# TOOL 2: MODULAR PATTERN SCAN
# ============================================================================

def tool2_modular_pattern_scan(k_range=range(3, 21)):
    """
    For each prime p dividing d(k):
    - Distribution of corrSum mod p
    - Uniformity test on Z/pZ
    - Uniformity test on Z/pZ \\ {0}
    - Uniformity test on odd residues only
    - Exact fraction per residue class
    """
    hdr = "TOOL 2: MODULAR PATTERN SCAN (per prime factor of d)"
    print("\n" + "=" * 72)
    print(hdr)
    print("=" * 72 + "\n")

    prime_data = defaultdict(list)

    for k in k_range:
        S  = compute_S(k)
        d  = compute_d(k)
        pf = distinct_prime_factors(d)
        if not pf:
            continue

        print(f"--- k={k}  d={d}  primes={pf} ---")

        for p in pf:
            if p > 50_000:
                print(f"  p={p}: SKIPPED (large)")
                continue

            counts, is_exact, total = get_corrsum_distribution(k, p)
            hit_set  = set(counts.keys())
            forb_p   = sorted(set(range(p)) - hit_set)
            fracs    = {r: counts.get(r, 0) / total for r in range(p)}

            # chi2 vs uniform on all of Z/pZ
            chi2_p_all = None
            if is_exact and HAS_SCIPY:
                exp_all = total / p
                if exp_all > 0:
                    chi2_stat = sum((counts.get(r, 0) - exp_all) ** 2 / exp_all
                                    for r in range(p))
                    chi2_p_all = float(sp_stats.chi2.sf(chi2_stat, p - 1))

            # chi2 vs uniform on Z/pZ \ {0}
            chi2_p_nz = None
            if is_exact and HAS_SCIPY and p >= 3:
                nz_total = sum(counts.get(r, 0) for r in range(1, p))
                exp_nz   = nz_total / (p - 1) if (p - 1) > 0 else 0
                if exp_nz > 0:
                    chi2_nz = sum((counts.get(r, 0) - exp_nz) ** 2 / exp_nz
                                  for r in range(1, p))
                    chi2_p_nz = float(sp_stats.chi2.sf(chi2_nz, p - 2))

            # chi2 vs uniform on odd residues only
            chi2_p_odd = None
            if is_exact and HAS_SCIPY:
                odd_res = [r for r in range(p) if r % 2 == 1]
                if len(odd_res) >= 2:
                    odd_total = sum(counts.get(r, 0) for r in odd_res)
                    exp_odd   = odd_total / len(odd_res)
                    if exp_odd > 0:
                        chi2_odd = sum((counts.get(r, 0) - exp_odd) ** 2 / exp_odd
                                        for r in odd_res)
                        chi2_p_odd = float(sp_stats.chi2.sf(chi2_odd,
                                           len(odd_res) - 1))

            print(f"  p={p}  {'EXACT' if is_exact else 'SAMPLE'}  "
                  f"{len(hit_set)}/{p} hit  "
                  f"forbidden={forb_p if len(forb_p) <= 15 else f'{len(forb_p)} residues'}")
            if p <= 30:
                frac_strs = [f"{r}:{fracs[r]:.4f}" for r in range(p)]
                print(f"    fractions: {', '.join(frac_strs)}")
            print(f"    0 mod {p} frac: {fracs.get(0, 0):.6f}")
            if chi2_p_all is not None:
                print(f"    chi2 uniform(Z/{p}Z):       p={chi2_p_all:.4e}")
            if chi2_p_nz is not None:
                print(f"    chi2 uniform(Z/{p}Z\\{{0}}): p={chi2_p_nz:.4e}")
            if chi2_p_odd is not None:
                print(f"    chi2 uniform(odd only):    p={chi2_p_odd:.4e}")

            prime_data[p].append({
                'k': k, 'd': d, 'hit_set': hit_set, 'forb': forb_p,
                'frac_zero': fracs.get(0, 0), 'is_exact': is_exact,
                'chi2_all': chi2_p_all, 'chi2_nz': chi2_p_nz,
                'chi2_odd': chi2_p_odd
            })
        print()

    # ---- cross-k analysis ----
    print("=" * 72)
    print("TOOL 2  CROSS-k PRIME ANALYSIS")
    print("=" * 72)
    for p in sorted(prime_data.keys()):
        entries = prime_data[p]
        if len(entries) < 2:
            continue
        print(f"\n  Prime p={p}  (appears for {len(entries)} values of k)")

        exact_entries = [e for e in entries if e['is_exact']]
        if len(exact_entries) >= 2:
            common_forb = set(exact_entries[0]['forb'])
            for e in exact_entries[1:]:
                common_forb &= set(e['forb'])
            if common_forb:
                print(f"    UNIVERSAL forbidden mod {p}: {sorted(common_forb)}")
                if 0 in common_forb:
                    print(f"    >>> 0 ALWAYS forbidden mod {p}")
            else:
                print(f"    No universally forbidden residue mod {p}")

        zf = [(e['k'], f"{e['frac_zero']:.6f}") for e in entries]
        print(f"    frac(0) by k: {zf}")

    print()
    return prime_data


# ============================================================================
# TOOL 3: SPECTRAL ANALYSIS
# ============================================================================

def tool3_spectral_analysis(k_range=range(3, 16)):
    """
    For each prime p | d(k), compute the DFT of the indicator function
    1_{corrSum(A) = r} over r in Z/pZ.
    Identify dominant frequencies and anomalously large Fourier coefficients.
    """
    hdr = "TOOL 3: SPECTRAL ANALYSIS (DFT over Z/pZ)"
    print("\n" + "=" * 72)
    print(hdr)
    print("=" * 72 + "\n")

    if not HAS_NUMPY:
        print("NOTE: numpy not available, using manual DFT (slower).\n")

    results = {}

    for k in k_range:
        S  = compute_S(k)
        d  = compute_d(k)
        pf = distinct_prime_factors(d)

        print(f"--- k={k}  d={d}  primes={pf} ---")

        for p in pf:
            if p > 5000:
                print(f"  p={p}: SKIPPED (>5000)")
                continue

            counts, is_exact, total = get_corrsum_distribution(k, p)

            # distribution vector  f[r] = #{A : corrSum = r mod p}
            f_vec = [counts.get(r, 0) for r in range(p)]

            # DFT:  F[t] = sum_r f[r] * exp(-2*pi*i*t*r / p)
            if HAS_NUMPY:
                F = np.fft.fft(np.array(f_vec, dtype=np.float64))
                mags = np.abs(F).tolist()
            else:
                F = []
                mags = []
                for t in range(p):
                    val = sum(f_vec[r] * cmath.exp(-2j * cmath.pi * t * r / p)
                              for r in range(p))
                    F.append(val)
                    mags.append(abs(val))

            dc = mags[0]
            if dc == 0:
                continue

            normalized = [mags[t] / dc for t in range(p)]

            # For truly uniform: |F[t]|=0 for t!=0.
            # For random noise: |F[t]| ~ sqrt(total), norm ~ 1/sqrt(total).
            rand_thresh = 3.0 / math.sqrt(total) if total > 0 else 1.0

            anomalies = [(t, normalized[t]) for t in range(1, p)
                         if normalized[t] > rand_thresh]

            ranked = sorted([(t, normalized[t]) for t in range(1, p)],
                            key=lambda x: -x[1])
            top5 = ranked[:5]

            print(f"  p={p}  DC={dc:.0f}  random_threshold={rand_thresh:.6f}")
            print(f"    Top-5 freq: {[(t, f'{n:.6f}') for t, n in top5]}")

            if anomalies:
                print(f"    ANOMALIES (>{rand_thresh:.4f}): "
                      f"{[(t, f'{n:.6f}') for t, n in anomalies[:12]]}")
                afreqs = [t for t, _ in anomalies]
                if len(afreqs) >= 2:
                    g = afreqs[0]
                    for f2 in afreqs[1:]:
                        g = math.gcd(g, f2)
                    if g > 1:
                        print(f"    >>> Anomaly frequencies share gcd={g} "
                              f"(potential subgroup of order {p // g})")
            else:
                print(f"    Spectrally flat (no anomalies)")

            results[(k, p)] = {
                'top5': top5, 'n_anomalies': len(anomalies),
                'rand_thresh': rand_thresh
            }
        print()

    # summary table
    print("=" * 72)
    print("TOOL 3  SPECTRAL SUMMARY")
    print("=" * 72)
    print(f"{'k':>4} {'p':>8} {'#anom':>6} {'max|F|/DC':>12} {'threshold':>12}")
    print("-" * 50)
    for (k, p) in sorted(results):
        r = results[(k, p)]
        mx = r['top5'][0][1] if r['top5'] else 0.0
        print(f"{k:>4} {p:>8} {r['n_anomalies']:>6} {mx:>12.6f} "
              f"{r['rand_thresh']:>12.6f}")
    print()
    return results


# ============================================================================
# TOOL 4: ALGEBRAIC INVARIANT SEARCH
# ============================================================================

def tool4_algebraic_invariants(k_range=range(3, 21), moduli=None):
    """
    Beyond known invariants (odd, not 0 mod 3, mod 4 in {1,3}):
    For each modulus m, compute the exact set of residues hit for each k.
    Identify NEW universal invariants (never hit for ALL k).
    Check if the set of forbidden residues GROWS with k.
    """
    hdr = "TOOL 4: ALGEBRAIC INVARIANT SEARCH"
    print("\n" + "=" * 72)
    print(hdr)
    print("=" * 72 + "\n")

    if moduli is None:
        moduli = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
                  17, 18, 19, 20, 21, 24, 25, 27, 32, 36, 48, 64]

    ever_hit = {m: set() for m in moduli}
    per_k    = {m: {} for m in moduli}

    for k in k_range:
        S = compute_S(k)

        if can_enumerate_exactly(k):
            for B in combinations(range(1, S), k - 1):
                cs = corrsum_true(B, k)
                for m in moduli:
                    r = cs % m
                    ever_hit[m].add(r)
                    per_k[m].setdefault(k, set()).add(r)
        else:
            pool = list(range(1, S))
            n_samp = 300_000
            for _ in range(n_samp):
                B = tuple(sorted(random.sample(pool, k - 1)))
                cs = corrsum_true(B, k)
                for m in moduli:
                    r = cs % m
                    ever_hit[m].add(r)
                    per_k[m].setdefault(k, set()).add(r)

        print(f"  k={k}  {'EXACT' if can_enumerate_exactly(k) else 'SAMPLED'}  done")

    # ---- universal invariants ----
    print("\n" + "=" * 72)
    print("UNIVERSAL INVARIANTS (residues never hit for ANY k in range)")
    print("=" * 72 + "\n")

    discoveries = {}

    # A helper to check if a forbidden set is "explained" by smaller moduli
    def is_explained_by_known(m, never_set):
        """Check if every element in never_set is forbidden by mod 2, 3, or 4."""
        for r in never_set:
            # An element r mod m is explained if:
            #   r mod 2 == 0 (even => forbidden by oddness)
            #   OR r mod 3 == 0 (forbidden by mod 3 invariant)
            #   OR r mod 4 in {0, 2} (forbidden by mod 4 invariant)
            if r % 2 != 0 and r % 3 != 0 and r % 4 not in (0, 2):
                return False  # at least one element not explained
        return True

    for m in moduli:
        never = sorted(set(range(m)) - ever_hit[m])
        if not never:
            print(f"  mod {m:>3}: ALL residues hit (no invariant)")
            continue

        explained = is_explained_by_known(m, never)
        if m == 2 and never == [0]:
            label = " [KNOWN: always odd]"
        elif m == 3 and set(never) == {0}:
            label = " [KNOWN: never 0 mod 3]"
        elif m == 4 and set(never) == {0, 2}:
            label = " [KNOWN: mod 4 in {1,3}]"
        elif explained:
            label = " [derived from mod 2/3/4]"
        else:
            label = ""

        is_new = not explained and m not in (2, 3, 4)
        tag = ">>> NEW <<<" if is_new else "known"
        print(f"  mod {m:>3}: never={never}  ({tag}){label}")

        if is_new:
            discoveries[m] = never

    # ---- detailed analysis of new discoveries ----
    if discoveries:
        print("\n" + "=" * 72)
        print("DETAILED ANALYSIS OF NEW INVARIANTS")
        print("=" * 72)
        for m, forb in discoveries.items():
            print(f"\n  mod {m}: forbidden = {forb}")
            k_list = sorted(per_k[m].keys())
            for k in k_list:
                hit  = sorted(per_k[m][k])
                nf_k = len(set(range(m)) - per_k[m][k])
                exact = "E" if can_enumerate_exactly(k) else "S"
                print(f"    k={k:>2} [{exact}]: hit={hit}  "
                      f"({len(hit)}/{m}, {nf_k} forbidden)")

            # does forbidden set grow monotonically?
            exact_ks = [k for k in k_list if can_enumerate_exactly(k)]
            if len(exact_ks) >= 3:
                prev_f = set(range(m)) - per_k[m][exact_ks[0]]
                growing = True
                for k2 in exact_ks[1:]:
                    curr_f = set(range(m)) - per_k[m][k2]
                    if not curr_f >= prev_f:
                        growing = False
                        break
                    prev_f = curr_f
                if growing:
                    print(f"    >>> FORBIDDEN SET GROWS MONOTONICALLY (exact k)")
    else:
        print("\n  No new universal invariants discovered beyond mod 2, 3, 4.")
        print("  This is itself informative: the known invariants appear to be tight.")

    # ---- per-k stability for interesting moduli ----
    print("\n" + "=" * 72)
    print("PER-k FORBIDDEN RESIDUE STABILITY (selected moduli)")
    print("=" * 72)
    for m in [5, 7, 8, 9, 11, 12, 13, 16, 24]:
        if m not in per_k:
            continue
        exact_ks = sorted(k for k in per_k[m] if can_enumerate_exactly(k))
        if len(exact_ks) < 3:
            continue
        forb_sets = [set(range(m)) - per_k[m][k] for k in exact_ks]
        common = forb_sets[0]
        for fs in forb_sets[1:]:
            common &= fs
        if common:
            print(f"  mod {m:>3}: common forbidden (exact k) = {sorted(common)}")
        else:
            nonempty = sum(1 for fs in forb_sets if fs)
            print(f"  mod {m:>3}: no common forbidden; "
                  f"{nonempty}/{len(exact_ks)} have some forbidden")

    print()
    return discoveries, per_k


# ============================================================================
# TOOL 5: PAIR CORRELATION
# ============================================================================

def tool5_pair_correlation(k_range=range(3, 16)):
    """
    For pairs (A, A') of compositions, compute corrSum(A) - corrSum(A') mod d.
    - Is the difference distribution uniform?
    - Are there forbidden differences?
    - What is the size of Im + Im?
    Tests additive structure of Im(corrSum).
    """
    hdr = "TOOL 5: PAIR CORRELATION (additive structure of Im)"
    print("\n" + "=" * 72)
    print(hdr)
    print("=" * 72 + "\n")

    results = {}

    for k in k_range:
        S = compute_S(k)
        d = compute_d(k)
        C = num_compositions(S, k)

        print(f"--- k={k}  S={S}  d={d}  C={C} ---")

        exact_pairs = can_enumerate_exactly(k) and C <= 3000

        if exact_pairs:
            # --- exact full-pair analysis ---
            all_vals = []
            for B in combinations(range(1, S), k - 1):
                all_vals.append(corrsum_from_subset(B, k, d))

            val_set = set(all_vals)

            # pairwise differences (ordered: both A-B and B-A)
            diff_counts = Counter()
            for i in range(len(all_vals)):
                for j in range(i + 1, len(all_vals)):
                    diff_counts[(all_vals[i] - all_vals[j]) % d] += 1
                    diff_counts[(all_vals[j] - all_vals[i]) % d] += 1
            # self-differences give 0
            for _ in all_vals:
                diff_counts[0] += 1

            n_diff_distinct = len(diff_counts)
            forb_diffs      = sorted(set(range(d)) - set(diff_counts.keys()))

            # sumset Im + Im
            sumset = set()
            for v1 in val_set:
                for v2 in val_set:
                    sumset.add((v1 + v2) % d)

            # doubling 2*Im
            doubleset = set((2 * v) % d for v in val_set)

            print(f"  EXACT  |Im|={len(val_set)}  "
                  f"|diff|={n_diff_distinct}/{d}")
            if forb_diffs:
                show = forb_diffs if len(forb_diffs) <= 20 else forb_diffs[:20]
                print(f"  Forbidden differences ({len(forb_diffs)}): {show}"
                      f"{'...' if len(forb_diffs) > 20 else ''}")
                if 0 in forb_diffs:
                    print(f"  >>> 0 is forbidden diff => all corrSum values DISTINCT")
            else:
                print(f"  No forbidden differences")

            print(f"  |Im+Im|={len(sumset)}  |2*Im|={len(doubleset)}  d={d}")
            if len(sumset) < d:
                missing = sorted(set(range(d)) - sumset)
                print(f"  >>> Im+Im INCOMPLETE: missing {len(missing)} values")
                if len(missing) <= 15:
                    print(f"      {missing}")

            # multiplicative symmetries of Im
            symmetries = []
            for r in range(2, min(d, 1000)):
                if math.gcd(r, d) != 1:
                    continue
                if set((r * v) % d for v in val_set) == val_set:
                    symmetries.append(r)
            if symmetries:
                print(f"  >>> Im is invariant under mult by: "
                      f"{symmetries if len(symmetries) <= 10 else symmetries[:10]}")

            results[k] = {
                'n_vals': len(all_vals), 'n_distinct': len(val_set),
                'n_diff_distinct': n_diff_distinct, 'd': d,
                'n_forb_diffs': len(forb_diffs), 'sumset': len(sumset),
                'doubleset': len(doubleset), 'symmetries': symmetries,
                'method': 'EXACT'
            }

        else:
            # --- sampled pair analysis ---
            pool = list(range(1, S))
            n_samp = min(200_000, C)
            vals = []
            for _ in range(n_samp):
                B = tuple(sorted(random.sample(pool, k - 1)))
                vals.append(corrsum_from_subset(B, k, d))

            n_distinct_samp = len(set(vals))

            # sampled differences
            diff_counts = Counter()
            n_diff_samp = min(500_000, n_samp * (n_samp - 1) // 2)
            for _ in range(n_diff_samp):
                i, j = random.sample(range(n_samp), 2)
                diff_counts[(vals[i] - vals[j]) % d] += 1

            n_diff_hit  = len(diff_counts)
            total_diffs = sum(diff_counts.values())

            zero_diff  = diff_counts.get(0, 0)
            exp_zero   = total_diffs / d if d > 0 else 0
            ratio_zero = zero_diff / exp_zero if exp_zero > 0 else 0.0

            print(f"  SAMPLED  n={n_samp}  distinct={n_distinct_samp}  "
                  f"diff_hit={n_diff_hit}/{d}")
            print(f"  diff=0 count: {zero_diff}  expected: {exp_zero:.1f}  "
                  f"ratio: {ratio_zero:.4f}")
            if ratio_zero > 1.5:
                print(f"  >>> Zero-difference ENRICHED (collisions in Im)")
            elif ratio_zero < 0.5:
                print(f"  >>> Zero-difference DEPLETED (values spread out)")

            results[k] = {
                'n_samp': n_samp, 'n_distinct': n_distinct_samp,
                'n_diff_hit': n_diff_hit, 'd': d,
                'ratio_zero': ratio_zero, 'method': 'SAMPLED'
            }
        print()

    # summary
    print("=" * 72)
    print("TOOL 5  PAIR CORRELATION SUMMARY")
    print("=" * 72)
    print(f"{'k':>3} {'d':>10} {'|Im|':>8} {'|diff|':>8} "
          f"{'|Im+Im|':>8} {'structure':>15}")
    print("-" * 65)
    for k in sorted(results):
        r = results[k]
        ss = str(r.get('sumset', '?'))
        if 'n_forb_diffs' in r:
            st = f"{r['n_forb_diffs']} forb" if r['n_forb_diffs'] else "full"
        else:
            st = f"z0={r['ratio_zero']:.2f}"
        nh = r.get('n_diff_distinct', r.get('n_diff_hit', '?'))
        print(f"{k:>3} {r['d']:>10} {r['n_distinct']:>8} {nh:>8} "
              f"{ss:>8} {st:>15}")
    print()
    return results


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
    print("r2_innovation_explorer.py")
    print("Discovery Toolbox -- Collatz corrSum Distribution")
    print("=" * 72)
    sha = compute_sha256()
    print(f"SHA-256:  {sha}")
    print(f"Time:     {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"numpy:    {'yes' if HAS_NUMPY else 'NO'}")
    print(f"scipy:    {'yes' if HAS_SCIPY else 'NO'}")
    print()

    random.seed(42)
    if HAS_NUMPY:
        np.random.seed(42)

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
        return
    else:
        run = set(args)

    t0 = time.time()

    if '1' in run:
        tool1_distribution_fingerprint(range(3, 21))

    if '2' in run:
        tool2_modular_pattern_scan(range(3, 21))

    if '3' in run:
        tool3_spectral_analysis(range(3, 16))

    if '4' in run:
        tool4_algebraic_invariants(range(3, 21))

    if '5' in run:
        tool5_pair_correlation(range(3, 16))

    elapsed = time.time() - t0

    print("=" * 72)
    print(f"ALL REQUESTED TOOLS COMPLETE   ({elapsed:.1f}s)")
    print(f"SHA-256: {sha}")
    print("=" * 72)


if __name__ == '__main__':
    main()
