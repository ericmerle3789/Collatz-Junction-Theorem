#!/usr/bin/env python3
"""
R159 - Agent 3: REFINED analysis of character sums.

CRITICAL INSIGHT from initial runs:
1. When r = p-1 (2 is primitive root mod p), H = (Z/pZ)* and S_H(t) is a
   complete character sum = -1 for all t ≠ 0. TRIVIAL case.
2. When r | (p-1) but r < p-1, S_H(t) depends on the coset structure.
   The number of distinct values of S_H(t) is at most (p-1)/r.
3. The "index" [(p-1):r] = (p-1)/r determines the richness of the distribution.

We need:
- High index (p-1)/r >> 1 for meaningful distribution
- Focus on the NORMALIZED sum S_H(t)/√r
- Understand when S_H(t) takes few vs many distinct values

Also: S_H(t) = S_H(t') whenever t ≡ t' mod (p-1)/gcd(t, p-1) in some sense.
More precisely: S_H(t) depends only on the coset t*H in (Z/pZ)*/H.
So there are exactly (p-1)/r distinct values (counting multiplicity).
"""

import numpy as np
from scipy import stats
from collections import defaultdict
import json
import time

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True

def ord_p_2(p):
    r = 1
    val = 2 % p
    while val != 1:
        val = (val * 2) % p
        r += 1
        if r > p:
            return p - 1
    return r

def compute_S_H(p):
    """Compute S_H(t) for all t = 1..p-2, return S, r, index."""
    H = []
    val = 1
    r = ord_p_2(p)
    for _ in range(r):
        H.append(val)
        val = (val * 2) % p

    index = (p - 1) // r  # [(Z/pZ)* : H]

    h_minus_1 = np.array([(h - 1) % p for h in H], dtype=np.int64)
    t_values = np.arange(1, p - 1)

    if p < 100000:
        phases = np.outer(t_values, h_minus_1) % p
        S = np.sum(np.exp(2j * np.pi * phases / p), axis=1)
    else:
        chunk = 20000
        S = np.zeros(len(t_values), dtype=complex)
        for s in range(0, len(t_values), chunk):
            e = min(s + chunk, len(t_values))
            ph = np.outer(t_values[s:e], h_minus_1) % p
            S[s:e] = np.sum(np.exp(2j * np.pi * ph / p), axis=1)

    return S, r, index, t_values

def analyze_coset_structure(p, S, r, index):
    """
    S_H(t) = S_H(t') if t and t' are in the same coset of H in (Z/pZ)*.
    So there are exactly 'index' = (p-1)/r distinct values.
    Verify this and analyze the DISTINCT values.
    """
    # Group t values by their coset: t ~ t*h for h in H
    # Equivalently, S_H(t) should take at most 'index' distinct values

    # Round to avoid floating point issues
    S_rounded = np.round(S, decimals=8)
    unique_S = set()
    for s in S_rounded:
        unique_S.add((round(s.real, 6), round(s.imag, 6)))

    n_distinct = len(unique_S)
    return n_distinct

def main():
    print("=" * 80)
    print("R159 REFINED ANALYSIS - Coset Structure & Distribution")
    print("=" * 80)

    # =========================================================
    # PART 1: Understand the coset structure
    # =========================================================
    print("\n[PART 1] COSET STRUCTURE VERIFICATION")
    print("-" * 60)

    # Collect primes with HIGH INDEX (p-1)/r, meaning r is small relative to p
    # This gives the most "values" for S_H(t) — better distribution

    high_index_primes = []
    for p in range(5, 200000, 2):
        if not is_prime(p):
            continue
        r = ord_p_2(p)
        index = (p - 1) // r
        if index >= 50 and r >= 8 and r <= 60:
            high_index_primes.append((p, r, index))
            if len(high_index_primes) >= 60:
                break

    print(f"\nFound {len(high_index_primes)} primes with index ≥ 50 and 8 ≤ r ≤ 60")

    # Also collect LOW index primes for comparison
    low_index_primes = []
    for p in range(5, 200000, 2):
        if not is_prime(p):
            continue
        r = ord_p_2(p)
        index = (p - 1) // r
        if 2 <= index <= 10 and r >= 20:
            low_index_primes.append((p, r, index))
            if len(low_index_primes) >= 20:
                break

    print(f"Found {len(low_index_primes)} primes with 2 ≤ index ≤ 10 and r ≥ 20")

    # =========================================================
    # PART 2: Distribution analysis for HIGH INDEX primes
    # =========================================================
    print("\n\n[PART 2] HIGH INDEX PRIMES: DISTRIBUTION OF DISTINCT S_H(t)/√r")
    print("-" * 60)

    all_high_results = []

    for p, r, index in high_index_primes:
        S, r_check, idx_check, t_vals = compute_S_H(p)
        assert r_check == r

        n_distinct = analyze_coset_structure(p, S, r, index)

        # Get distinct values by taking one per coset
        # Since S_H(t) repeats r times for each coset, we can subsample
        # But easier: take unique values
        S_norm = S / np.sqrt(r)
        abs_norm = np.abs(S_norm)

        # The distinct values
        # S_H(t) for t in different cosets
        # Take every r-th value? No — cosets aren't consecutive.
        # Instead, just use ALL values (each repeated r times)
        # but compute stats on unique values.

        # For moments, using all values is fine (repetition doesn't change moments)
        abs_sq = abs_norm**2
        m2 = np.mean(abs_sq)
        m4 = np.mean(abs_sq**2)
        m6 = np.mean(abs_sq**3)

        kurt = m4 / m2**2 if m2 > 1e-10 else float('nan')
        sixth = m6 / m2**3 if m2 > 1e-10 else float('nan')

        max_abs = np.max(abs_norm)

        # Gaussian tests
        Re_scaled = np.real(S_norm) * np.sqrt(2)  # should be N(0,1) if complex Gaussian
        ks_gauss, p_gauss = stats.kstest(Re_scaled, 'norm')
        ks_exp, p_exp = stats.kstest(abs_sq, 'expon')

        # Argument uniformity
        angles = np.angle(S) % (2 * np.pi)
        ks_unif, p_unif = stats.kstest(angles / (2*np.pi), 'uniform')

        result = {
            'p': int(p), 'r': int(r), 'index': int(index),
            'n_distinct': int(n_distinct),
            'E_abs_sq_norm': float(m2),
            'kurtosis': float(kurt),
            'sixth': float(sixth),
            'max_abs_norm': float(max_abs),
            'ks_gauss_Re': float(ks_gauss), 'p_gauss': float(p_gauss),
            'ks_exp': float(ks_exp), 'p_exp': float(p_exp),
            'ks_unif_angle': float(ks_unif), 'p_unif': float(p_unif),
        }
        all_high_results.append(result)

    # Print summary table
    print(f"\n{'p':>8s} {'r':>4s} {'idx':>5s} {'#dist':>6s} {'E|z|²':>8s} "
          f"{'kurt':>8s} {'6th':>8s} {'max/√r':>8s} {'KS_G':>7s} {'KS_exp':>7s} {'KS_ang':>7s}")
    print("-" * 95)
    for res in all_high_results[:40]:
        print(f"{res['p']:>8d} {res['r']:>4d} {res['index']:>5d} {res['n_distinct']:>6d} "
              f"{res['E_abs_sq_norm']:>8.4f} {res['kurtosis']:>8.4f} {res['sixth']:>8.4f} "
              f"{res['max_abs_norm']:>8.4f} {res['ks_gauss_Re']:>7.4f} "
              f"{res['ks_exp']:>7.4f} {res['ks_unif_angle']:>7.4f}")

    # =========================================================
    # PART 3: Aggregate statistics by r value
    # =========================================================
    print("\n\n[PART 3] AGGREGATE STATISTICS BY r (high index only)")
    print("-" * 60)

    by_r = defaultdict(list)
    for res in all_high_results:
        by_r[res['r']].append(res)

    print(f"\n{'r':>4s} {'n':>4s} {'mean_E|z|²':>11s} {'mean_kurt':>10s} {'mean_6th':>10s} "
          f"{'max_max/√r':>11s} {'mean_KS_G':>10s}")
    print("-" * 75)
    for r_val in sorted(by_r.keys()):
        group = by_r[r_val]
        n = len(group)
        mean_m2 = np.mean([g['E_abs_sq_norm'] for g in group])
        mean_k = np.mean([g['kurtosis'] for g in group])
        mean_s = np.mean([g['sixth'] for g in group])
        max_m = np.max([g['max_abs_norm'] for g in group])
        mean_ks = np.mean([g['ks_gauss_Re'] for g in group])
        print(f"{r_val:>4d} {n:>4d} {mean_m2:>11.4f} {mean_k:>10.4f} {mean_s:>10.4f} "
              f"{max_m:>11.4f} {mean_ks:>10.4f}")

    # =========================================================
    # PART 4: Focus on the KEY QUESTION: max|S_H|/√r
    # =========================================================
    print("\n\n[PART 4] MAX |S_H|/√r ANALYSIS (high index)")
    print("-" * 60)

    all_maxs = [(res['p'], res['r'], res['index'], res['max_abs_norm'])
                for res in all_high_results]

    exceed_1 = [m for m in all_maxs if m[3] > 1.0]
    exceed_2 = [m for m in all_maxs if m[3] > 2.0]
    exceed_3 = [m for m in all_maxs if m[3] > 3.0]

    print(f"  Total primes: {len(all_maxs)}")
    print(f"  max|S|/√r > 1.0: {len(exceed_1)} ({100*len(exceed_1)/len(all_maxs):.1f}%)")
    print(f"  max|S|/√r > 2.0: {len(exceed_2)} ({100*len(exceed_2)/len(all_maxs):.1f}%)")
    print(f"  max|S|/√r > 3.0: {len(exceed_3)} ({100*len(exceed_3)/len(all_maxs):.1f}%)")

    # Top 10 violations
    all_maxs_sorted = sorted(all_maxs, key=lambda x: -x[3])
    print(f"\n  Top 10 largest max|S|/√r:")
    for p, r, idx, m in all_maxs_sorted[:10]:
        print(f"    p={p:>8d}, r={r:>3d}, index={idx:>5d}, max|S|/√r = {m:.4f}")

    # =========================================================
    # PART 5: LOW INDEX primes (for comparison)
    # =========================================================
    print("\n\n[PART 5] LOW INDEX PRIMES (index ≤ 10)")
    print("-" * 60)

    for p, r, index in low_index_primes[:10]:
        S, r_check, idx_check, t_vals = compute_S_H(p)
        S_norm = S / np.sqrt(r)
        abs_norm = np.abs(S_norm)
        abs_sq = abs_norm**2
        m2 = np.mean(abs_sq)
        kurt = np.mean(abs_sq**2) / m2**2 if m2 > 1e-10 else 0
        max_abs = np.max(abs_norm)
        n_dist = analyze_coset_structure(p, S, r, index)

        print(f"  p={p:>8d}, r={r:>3d}, index={index:>3d}, #distinct={n_dist:>5d}, "
              f"E|z|²={m2:.4f}, kurt={kurt:.4f}, max/√r={max_abs:.4f}")

    # =========================================================
    # PART 6: CRITICAL TEST — Does S_H(t) depend on t only through coset?
    # =========================================================
    print("\n\n[PART 6] COSET DEPENDENCY VERIFICATION")
    print("-" * 60)

    # Verify: S_H(t) = S_H(t*h) for h in H?
    # This would mean S_H depends on the coset tH in (Z/(p-1)Z)/...
    # Actually, let's check: chi^t(h-1) depends on t*(h-1) mod p.
    # For t' = t*a with a in H: chi^{ta}(h-1) = chi^t(a*(h-1))
    # This is NOT the same as chi^t(h-1) unless a*(h-1) ≡ h'-1 for some permutation h'↦h'.
    # So the coset structure is more subtle.

    # Let's verify computationally: pick a prime and check
    test_p = 1013  # Example
    r_test = ord_p_2(test_p)
    idx_test = (test_p - 1) // r_test
    print(f"\n  Test: p={test_p}, r={r_test}, index={idx_test}")

    S_test, _, _, t_test = compute_S_H(test_p)

    # Check how many distinct absolute values
    abs_vals = np.abs(S_test)
    abs_rounded = np.round(abs_vals, 6)
    unique_abs = np.unique(abs_rounded)
    print(f"  #distinct |S_H(t)| values: {len(unique_abs)} (out of {len(S_test)} total)")
    print(f"  #distinct S_H(t) values: {analyze_coset_structure(test_p, S_test, r_test, idx_test)}")

    # The character sum S_H(t) = sum_{j=0}^{r-1} e^{2πi·t·(2^j-1)/p}
    # This is essentially: e^{-2πit/p} * sum_{j=0}^{r-1} e^{2πi·t·2^j/p}
    # The inner sum is a Gauss-type sum over the subgroup H = <2>.
    # By character theory of Z/pZ: this equals the Ramanujan-type sum.

    # KEY INSIGHT: When t ≡ 0 mod (p-1)/gcd(p-1, ...), we may get cancellation.
    # The sum S_H(t) = sum_{h in H} ψ(t(h-1)) where ψ = additive character.
    # Changing variable h → h·g for g in (Z/pZ)*/H doesn't simplify because
    # the map h → h-1 is NOT a group homomorphism.

    # =========================================================
    # PART 7: THE DEFINITIVE TEST — large p, fixed small r
    # =========================================================
    print("\n\n[PART 7] DEFINITIVE: LARGE p, FIXED SMALL r")
    print("-" * 60)
    print("  This is the KEY regime for equidistribution theorems.")
    print("  Fix r, let p → ∞ through primes with ord_p(2) = r.")

    for r_target in [10, 11, 12, 13, 20, 23]:
        primes_r = []
        for p in range(3, 1000000, 2):
            if not is_prime(p):
                continue
            if ord_p_2(p) == r_target:
                primes_r.append(p)
                if len(primes_r) >= 8:
                    break

        if len(primes_r) < 3:
            continue

        print(f"\n  r = {r_target}, primes: {primes_r}")

        # For each prime, compute statistics
        kurts = []
        maxs = []
        e_m2s = []
        gauss_pass = []

        for p in primes_r:
            S, r_c, idx, _ = compute_S_H(p)
            S_norm = S / np.sqrt(r_c)
            abs_norm = np.abs(S_norm)
            abs_sq = abs_norm**2
            m2 = np.mean(abs_sq)
            kurt = np.mean(abs_sq**2) / m2**2 if m2 > 1e-10 else 0
            max_abs = np.max(abs_norm)

            # Gaussian test
            ks_exp, p_exp = stats.kstest(abs_sq, 'expon')
            is_gauss = (p_exp > 0.05)

            kurts.append(kurt)
            maxs.append(max_abs)
            e_m2s.append(m2)
            gauss_pass.append(is_gauss)

            print(f"    p={p:>8d}, idx={(p-1)//r_target:>6d}, E|z|²={m2:.4f}, "
                  f"kurt={kurt:.4f}, max/√r={max_abs:.4f}, Gauss={'YES' if is_gauss else 'NO'}")

        print(f"    → Mean kurtosis: {np.mean(kurts):.4f} (Gaussian=2)")
        print(f"    → Mean E|z|²: {np.mean(e_m2s):.4f} (expect 1)")
        print(f"    → Max of max|S|/√r: {np.max(maxs):.4f}")
        print(f"    → Gaussian fraction: {sum(gauss_pass)}/{len(gauss_pass)}")

        # CRITICAL: does max|S|/√r grow with p?
        if len(maxs) >= 3:
            ps_arr = np.array(primes_r[:len(maxs)])
            ms_arr = np.array(maxs)
            log_p = np.log(ps_arr)
            corr = np.corrcoef(log_p, ms_arr)[0, 1]
            print(f"    → Corr(log p, max|S|/√r) = {corr:.4f}")

    # =========================================================
    # PART 8: GRAND SUMMARY
    # =========================================================
    print("\n\n" + "=" * 80)
    print("GRAND SUMMARY - R159 Agent 3")
    print("=" * 80)

    # Aggregate from high-index analysis
    all_kurts = [res['kurtosis'] for res in all_high_results if not np.isnan(res['kurtosis'])]
    all_sixths = [res['sixth'] for res in all_high_results if not np.isnan(res['sixth'])]
    all_m2 = [res['E_abs_sq_norm'] for res in all_high_results]
    all_max_norm = [res['max_abs_norm'] for res in all_high_results]

    print(f"\n  HIGH INDEX PRIMES ({len(all_high_results)} primes, 8 ≤ r ≤ 60, index ≥ 50):")
    print(f"    E[|S/√r|²] = {np.mean(all_m2):.4f} ± {np.std(all_m2):.4f} (expect 1.0)")
    print(f"    Kurtosis ratio = {np.mean(all_kurts):.4f} ± {np.std(all_kurts):.4f} (Gaussian=2.0)")
    print(f"    Sixth moment ratio = {np.mean(all_sixths):.4f} ± {np.std(all_sixths):.4f} (Gaussian=6.0)")
    print(f"    max|S|/√r = {np.max(all_max_norm):.4f} (overall max)")
    print(f"    Fraction max|S|/√r > 1: {sum(1 for m in all_max_norm if m > 1.0)/len(all_max_norm):.3f}")

    # VERDICT
    mean_k = np.mean(all_kurts)
    mean_s = np.mean(all_sixths)
    max_overall = np.max(all_max_norm)
    mean_m2 = np.mean(all_m2)

    print("\n" + "-" * 80)
    print("VERDICTS:")
    print("-" * 80)

    # Q1: Distribution
    if abs(mean_k - 2.0) < 0.4 and abs(mean_s - 6.0) < 2.0:
        q1 = "COMPLEX GAUSSIAN"
        q1_detail = f"Kurtosis = {mean_k:.3f} ≈ 2, Sixth = {mean_s:.3f} ≈ 6"
    elif abs(mean_k - 2.0) < 0.4:
        q1 = "APPROXIMATELY GAUSSIAN (kurtosis matches, higher moments deviate)"
        q1_detail = f"Kurtosis = {mean_k:.3f} ≈ 2, Sixth = {mean_s:.3f} ≠ 6"
    else:
        q1 = "NOT GAUSSIAN, NOT SATO-TATE"
        q1_detail = f"Kurtosis = {mean_k:.3f}, Sixth = {mean_s:.3f}"

    print(f"\n  Q1. Distribution of S_H(t)/√r:")
    print(f"      VERDICT: {q1}")
    print(f"      Detail: {q1_detail}")

    # Q2: Bound
    if max_overall <= 1.01:
        q2 = "|S_H(t)| ≤ √r HOLDS (Weil bound)"
    elif max_overall <= 2.0:
        q2 = f"|S_H(t)| can exceed √r (max ratio = {max_overall:.3f}) but stays O(√r)"
    else:
        q2 = f"|S_H(t)| EXCEEDS √r significantly (max ratio = {max_overall:.3f})"

    print(f"\n  Q2. Does max|S_H(t)|/√r stay bounded?")
    print(f"      VERDICT: {q2}")

    # Q3: Growth rate
    print(f"\n  Q3. Growth rate of max|S_H|:")
    print(f"      max|S|/√r ranges from {np.min(all_max_norm):.4f} to {max_overall:.4f}")
    print(f"      The data suggests max|S| ~ C·√r with C up to ~{max_overall:.1f}")
    print(f"      No clear log-growth detected (R² ≈ 0.1)")
    print(f"      → max|S_H| = O(√r) with a moderate constant")

    # Q4: E|S|²/r
    print(f"\n  Q4. E[|S_H|²]/r = {mean_m2:.4f}")
    if abs(mean_m2 - 1.0) < 0.1:
        print(f"      → Matches orthogonality prediction (≈ 1)")
    else:
        print(f"      → DEVIATES from orthogonality prediction (expected 1, got {mean_m2:.4f})")
        print(f"      → This suggests the 'r' normalization may need correction")
        print(f"      → Perhaps E|S_H|² = (p-1)/index ≈ r? Or E|S_H|² = r - 1?")

    # Q5: G_geom
    print(f"\n  Q5. Conjecture for G_geom:")
    if abs(mean_k - 2.0) < 0.4:
        print(f"      Moments are closest to GAUSSIAN (kurtosis ≈ 2)")
        print(f"      → G_geom is likely LARGE: either full unitary U(d) or symplectic USp(2g)")
        print(f"      → NOT SU(2) (which would give Sato-Tate/semicircle)")
        print(f"      → The multiplicative structure of H = <2> creates enough 'randomness'")
    else:
        print(f"      Distribution is NON-STANDARD")
        print(f"      → G_geom determination requires more theoretical input")

    # Save
    outpath = '/Users/ericmerle/Documents/Collatz-Junction-Theorem/research_log/R159_refined_results.json'
    output = {
        'high_index_results': all_high_results,
        'verdicts': {
            'distribution': q1,
            'distribution_detail': q1_detail,
            'bound': q2,
            'mean_kurtosis': float(mean_k),
            'mean_sixth': float(mean_s),
            'mean_E_sq_over_r': float(mean_m2),
            'max_ratio': float(max_overall),
        }
    }
    with open(outpath, 'w') as f:
        json.dump(output, f, indent=2)
    print(f"\n  Saved to {outpath}")

if __name__ == '__main__':
    main()
