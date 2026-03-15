#!/usr/bin/env python3
"""
R159 - Agent 3: Numerical investigation of character sums S_H(t)
for the Collatz Junction Theorem.

S_H(t) = sum_{h in H} chi^t(h-1)
where H = <2> in (Z/pZ)*, chi = exp(2*pi*i/p), |H| = r = ord_p(2).

We compute distributions, test against Sato-Tate/Gaussian, compute moments,
and analyze maximum value statistics.
"""

import numpy as np
from scipy import stats
from collections import defaultdict
import json
import time
import sys

# ============================================================
# CORE COMPUTATIONS
# ============================================================

def ord_p_2(p):
    """Compute ord_p(2) = smallest r such that 2^r = 1 mod p."""
    r = 1
    val = 2 % p
    while val != 1:
        val = (val * 2) % p
        r += 1
        if r > p:
            return p - 1  # fallback
    return r

def compute_H(p):
    """Compute H = <2> in (Z/pZ)* as a list of elements."""
    H = []
    val = 1
    r = ord_p_2(p)
    for _ in range(r):
        H.append(val)
        val = (val * 2) % p
    return H, r

def compute_S_H(p):
    """
    Compute S_H(t) for all t = 1, ..., p-2.
    S_H(t) = sum_{h in H} chi^t(h-1) where chi(x) = exp(2*pi*i*x/p).

    Note: chi^t(h-1) = exp(2*pi*i*t*(h-1)/p).
    """
    H, r = compute_H(p)
    # Precompute (h-1) mod p for h in H
    h_minus_1 = np.array([(h - 1) % p for h in H], dtype=np.int64)

    # For each t = 1, ..., p-2, compute S_H(t)
    t_values = np.arange(1, p - 1)

    # S_H(t) = sum_{h in H} exp(2*pi*i*t*(h-1)/p)
    # Use vectorized computation
    # Shape: (len(t_values), len(H))
    # phases[i,j] = t_values[i] * h_minus_1[j] mod p
    # For large p, we need to be careful with memory

    if p < 50000:
        # Vectorized for moderate p
        phases = np.outer(t_values, h_minus_1) % p
        exp_vals = np.exp(2j * np.pi * phases / p)
        S = np.sum(exp_vals, axis=1)
    else:
        # Chunk computation for large p
        chunk_size = 10000
        S = np.zeros(len(t_values), dtype=complex)
        for start in range(0, len(t_values), chunk_size):
            end = min(start + chunk_size, len(t_values))
            t_chunk = t_values[start:end]
            phases = np.outer(t_chunk, h_minus_1) % p
            exp_vals = np.exp(2j * np.pi * phases / p)
            S[start:end] = np.sum(exp_vals, axis=1)

    return S, r, t_values

def find_primes_with_order(target_r, max_p=100000, count=20):
    """Find primes p where ord_p(2) = target_r."""
    results = []
    # p must satisfy p | (2^r - 1), so p divides 2^target_r - 1
    # But we also need ord_p(2) = target_r exactly (not a divisor)
    for p in range(3, max_p, 2):
        if not is_prime(p):
            continue
        if ord_p_2(p) == target_r:
            results.append(p)
            if len(results) >= count:
                break
    return results

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

def find_good_primes(max_p=200000, max_count=200):
    """Find primes with various orders of 2, collecting a diverse set."""
    primes_by_order = defaultdict(list)
    for p in range(3, max_p, 2):
        if not is_prime(p):
            continue
        r = ord_p_2(p)
        if 8 <= r <= 120:
            primes_by_order[r].append(p)
            if sum(len(v) for v in primes_by_order.values()) >= max_count:
                break
    return primes_by_order

# ============================================================
# STATISTICAL TESTS
# ============================================================

def test_sato_tate(real_parts_normalized):
    """
    Test if Re(S_H)/sqrt(r) follows the Sato-Tate (semicircle) distribution.
    Sato-Tate density on [-1,1]: f(x) = (2/pi)*sqrt(1-x^2).
    The CDF is: F(x) = 1/2 + (1/pi)*(x*sqrt(1-x^2) + arcsin(x)) for x in [-1,1].
    """
    x = real_parts_normalized
    # Clip to [-1, 1] for ST test
    x_clip = np.clip(x, -0.999, 0.999)
    fraction_in_range = np.mean((x >= -1) & (x <= 1))

    # Sato-Tate CDF
    def st_cdf(x):
        x = np.clip(x, -1, 1)
        return 0.5 + (1/np.pi) * (x * np.sqrt(1 - x**2) + np.arcsin(x))

    # KS test against Sato-Tate
    sorted_x = np.sort(x_clip)
    n = len(sorted_x)
    empirical_cdf = np.arange(1, n+1) / n
    theoretical_cdf = st_cdf(sorted_x)
    ks_stat = np.max(np.abs(empirical_cdf - theoretical_cdf))

    return ks_stat, fraction_in_range

def test_gaussian(complex_values_normalized):
    """Test if S_H/sqrt(r) follows complex Gaussian N(0,1)."""
    real = np.real(complex_values_normalized)
    imag = np.imag(complex_values_normalized)

    # Each of Re, Im should be ~ N(0, 1/2) for standard complex Gaussian
    # |S/sqrt(r)|^2 should be ~ Exp(1) (i.e., chi-squared with 2 dof / 2)

    ks_real, p_real = stats.kstest(real * np.sqrt(2), 'norm')
    ks_imag, p_imag = stats.kstest(imag * np.sqrt(2), 'norm')

    # |z|^2 should be Exp(1)
    abs_sq = np.abs(complex_values_normalized)**2
    ks_exp, p_exp = stats.kstest(abs_sq, 'expon')

    return {
        'ks_real': ks_real, 'p_real': p_real,
        'ks_imag': ks_imag, 'p_imag': p_imag,
        'ks_exp': ks_exp, 'p_exp': p_exp,
    }

def test_uniform_argument(complex_values):
    """Test if arg(S_H) is uniform on [0, 2*pi)."""
    angles = np.angle(complex_values) % (2 * np.pi)
    angles_normalized = angles / (2 * np.pi)
    ks_stat, p_val = stats.kstest(angles_normalized, 'uniform')
    return ks_stat, p_val

def compute_moments(S, r):
    """Compute key moments of S_H."""
    abs_S = np.abs(S)
    abs_sq = abs_S**2

    E_abs_sq = np.mean(abs_sq)
    E_abs_4 = np.mean(abs_sq**2)
    kurtosis_ratio = E_abs_4 / E_abs_sq**2 if E_abs_sq > 0 else float('nan')

    # For complex Gaussian: E|z|^4 / (E|z|^2)^2 = 2
    # For uniform phase, fixed amplitude: = 1

    # Normalized moments
    S_norm = S / np.sqrt(r)
    E_norm_sq = np.mean(np.abs(S_norm)**2)

    # 6th moment
    E_abs_6 = np.mean(abs_sq**3)
    sixth_ratio = E_abs_6 / E_abs_sq**3 if E_abs_sq > 0 else float('nan')
    # For complex Gaussian: E|z|^6/(E|z|^2)^3 = 6

    return {
        'E_abs_sq': E_abs_sq,
        'E_abs_sq_over_r': E_abs_sq / r,
        'kurtosis_ratio': kurtosis_ratio,  # should be ~2 for Gaussian
        'sixth_moment_ratio': sixth_ratio,  # should be ~6 for Gaussian
        'E_norm_sq': E_norm_sq,
    }

# ============================================================
# MAIN COMPUTATION
# ============================================================

def analyze_prime(p, verbose=False):
    """Full analysis for a single prime."""
    S, r, t_values = compute_S_H(p)
    S_norm = S / np.sqrt(r)

    abs_S = np.abs(S)
    max_abs = np.max(abs_S)
    max_abs_norm = max_abs / np.sqrt(r)

    # Distribution tests
    real_norm = np.real(S_norm)

    # Sato-Tate test
    st_ks, st_frac = test_sato_tate(real_norm)

    # Gaussian test
    gauss = test_gaussian(S_norm)

    # Uniform argument test
    arg_ks, arg_p = test_uniform_argument(S)

    # Moments
    moments = compute_moments(S, r)

    result = {
        'p': int(p),
        'r': int(r),
        'n_values': int(len(S)),
        'max_abs_S': float(max_abs),
        'max_abs_norm': float(max_abs_norm),
        'sqrt_r': float(np.sqrt(r)),
        'max_over_sqrt_r': float(max_abs_norm),
        'mean_abs': float(np.mean(abs_S)),
        'std_abs': float(np.std(abs_S)),
        'sato_tate_ks': float(st_ks),
        'sato_tate_frac_in_range': float(st_frac),
        'gaussian_ks_real': float(gauss['ks_real']),
        'gaussian_p_real': float(gauss['p_real']),
        'gaussian_ks_imag': float(gauss['ks_imag']),
        'gaussian_p_imag': float(gauss['p_imag']),
        'gaussian_ks_exp': float(gauss['ks_exp']),
        'gaussian_p_exp': float(gauss['p_exp']),
        'arg_uniform_ks': float(arg_ks),
        'arg_uniform_p': float(arg_p),
        'E_abs_sq_over_r': float(moments['E_abs_sq_over_r']),
        'kurtosis_ratio': float(moments['kurtosis_ratio']),
        'sixth_moment_ratio': float(moments['sixth_moment_ratio']),
    }

    if verbose:
        print(f"  p={p}, r={r}, max|S|/√r={max_abs_norm:.4f}, "
              f"E|S|²/r={moments['E_abs_sq_over_r']:.4f}, "
              f"kurt={moments['kurtosis_ratio']:.4f}, "
              f"ST_KS={st_ks:.4f}, G_KS_exp={gauss['ks_exp']:.4f}")

    return result

def main():
    print("=" * 80)
    print("R159 - Character Sum Distribution Analysis")
    print("S_H(t) = Σ_{h∈H} χ^t(h-1), H = ⟨2⟩ ⊂ (Z/pZ)*")
    print("=" * 80)

    # Find primes with various orders
    print("\n[1] Finding primes with various ord_p(2)...")
    t0 = time.time()
    primes_by_order = find_good_primes(max_p=500000, max_count=500)

    # Select a diverse set
    target_orders = [8, 10, 11, 12, 14, 16, 18, 20, 23, 24, 28, 30,
                     36, 40, 48, 52, 60, 66, 72, 80, 84, 90, 100]

    selected_primes = []
    for r_target in target_orders:
        if r_target in primes_by_order:
            primes = primes_by_order[r_target]
            # Take up to 3 primes per order
            for p in primes[:3]:
                selected_primes.append((p, r_target))

    # Also add some large primes with moderate r
    for r_val, primes in sorted(primes_by_order.items()):
        if r_val >= 40 and len([s for s in selected_primes if s[1] == r_val]) == 0:
            for p in primes[:2]:
                selected_primes.append((p, r_val))

    # Cap at reasonable number
    selected_primes = selected_primes[:80]
    selected_primes.sort(key=lambda x: (x[1], x[0]))

    print(f"  Found {len(selected_primes)} primes across orders "
          f"{sorted(set(r for _, r in selected_primes))}")
    print(f"  Time: {time.time()-t0:.1f}s")

    # Analyze each prime
    print("\n[2] Computing S_H(t) for each prime...")
    all_results = []

    for i, (p, r) in enumerate(selected_primes):
        if i % 10 == 0:
            print(f"  Progress: {i}/{len(selected_primes)}...")
        result = analyze_prime(p, verbose=(i < 20 or r >= 40))
        all_results.append(result)

    # ============================================================
    # AGGREGATE ANALYSIS
    # ============================================================

    print("\n" + "=" * 80)
    print("[3] AGGREGATE RESULTS")
    print("=" * 80)

    # 3a. E[|S|²]/r should be ≈ 1
    print("\n--- E[|S_H|²] / r (expected ≈ 1 by orthogonality) ---")
    for res in all_results[:20]:
        print(f"  p={res['p']:>7d}, r={res['r']:>3d}, E|S|²/r = {res['E_abs_sq_over_r']:.6f}")

    all_E_ratio = [r['E_abs_sq_over_r'] for r in all_results]
    print(f"\n  Mean E|S|²/r = {np.mean(all_E_ratio):.6f} ± {np.std(all_E_ratio):.6f}")
    print(f"  Range: [{np.min(all_E_ratio):.6f}, {np.max(all_E_ratio):.6f}]")

    # 3b. Kurtosis ratio (2 = Gaussian, 1 = uniform amplitude)
    print("\n--- Kurtosis ratio E|S|⁴/(E|S|²)² (Gaussian → 2) ---")
    by_r = defaultdict(list)
    for res in all_results:
        by_r[res['r']].append(res['kurtosis_ratio'])

    for r_val in sorted(by_r.keys()):
        vals = by_r[r_val]
        print(f"  r={r_val:>3d}: kurtosis = {np.mean(vals):.4f} ± {np.std(vals):.4f} "
              f"(n={len(vals)})")

    all_kurt = [r['kurtosis_ratio'] for r in all_results]
    print(f"\n  Overall kurtosis ratio = {np.mean(all_kurt):.4f} ± {np.std(all_kurt):.4f}")

    # 3c. Sixth moment ratio (6 = Gaussian)
    print("\n--- Sixth moment ratio E|S|⁶/(E|S|²)³ (Gaussian → 6) ---")
    all_sixth = [r['sixth_moment_ratio'] for r in all_results]
    print(f"  Overall = {np.mean(all_sixth):.4f} ± {np.std(all_sixth):.4f}")

    # 3d. Sato-Tate test
    print("\n--- Sato-Tate KS test (Re(S)/√r vs semicircle) ---")
    st_by_r = defaultdict(list)
    for res in all_results:
        st_by_r[res['r']].append(res['sato_tate_ks'])
    for r_val in sorted(st_by_r.keys())[:15]:
        vals = st_by_r[r_val]
        print(f"  r={r_val:>3d}: KS = {np.mean(vals):.4f} ± {np.std(vals):.4f}")

    # 3e. Gaussian test
    print("\n--- Gaussian test (S/√r vs complex N(0,1)) ---")
    gauss_by_r = defaultdict(list)
    for res in all_results:
        gauss_by_r[res['r']].append(res['gaussian_ks_exp'])
    for r_val in sorted(gauss_by_r.keys())[:15]:
        vals = gauss_by_r[r_val]
        print(f"  r={r_val:>3d}: KS(|z|² vs Exp) = {np.mean(vals):.4f} ± {np.std(vals):.4f}")

    # 3f. Uniform argument test
    print("\n--- Uniform argument test ---")
    arg_by_r = defaultdict(list)
    for res in all_results:
        arg_by_r[res['r']].append((res['arg_uniform_ks'], res['arg_uniform_p']))
    for r_val in sorted(arg_by_r.keys())[:15]:
        vals = arg_by_r[r_val]
        mean_ks = np.mean([v[0] for v in vals])
        mean_p = np.mean([v[1] for v in vals])
        print(f"  r={r_val:>3d}: KS = {mean_ks:.4f}, mean p-val = {mean_p:.4f}")

    # 3g. Maximum value statistics (KEY QUESTION)
    print("\n" + "=" * 80)
    print("[4] MAXIMUM VALUE STATISTICS (CRITICAL)")
    print("=" * 80)

    print("\n--- max|S_H(t)|/√r by prime ---")
    max_by_r = defaultdict(list)
    for res in all_results:
        max_by_r[res['r']].append(res['max_over_sqrt_r'])

    for r_val in sorted(max_by_r.keys()):
        vals = max_by_r[r_val]
        print(f"  r={r_val:>3d}: max|S|/√r = {np.mean(vals):.4f} ± {np.std(vals):.4f} "
              f"(max={np.max(vals):.4f}, n={len(vals)})")

    # Is max|S|/√r bounded?
    all_max = [(res['r'], res['p'], res['max_over_sqrt_r']) for res in all_results]
    all_max.sort(key=lambda x: x[0])

    print("\n--- Growth rate analysis ---")
    rs = np.array([x[0] for x in all_max])
    max_vals = np.array([x[2] for x in all_max])

    # Test: max|S|/√r vs various growth rates
    # If bounded by constant: max ~ C
    # If √(log r): max ~ √(log r)
    # If log r: max ~ log r

    unique_rs = sorted(set(rs))
    max_per_r = []
    for r_val in unique_rs:
        mask = rs == r_val
        max_per_r.append((r_val, np.max(max_vals[mask])))

    r_arr = np.array([x[0] for x in max_per_r])
    m_arr = np.array([x[1] for x in max_per_r])

    print(f"  Range of r: {r_arr[0]} to {r_arr[-1]}")
    print(f"  Range of max|S|/√r: {m_arr.min():.4f} to {m_arr.max():.4f}")

    # Fit: max = a * sqrt(log(r)) + b
    if len(r_arr) > 3:
        log_r = np.log(r_arr)
        sqrt_log_r = np.sqrt(log_r)

        # Linear regression: m = a * sqrt(log r) + b
        A = np.vstack([sqrt_log_r, np.ones(len(sqrt_log_r))]).T
        coeffs, residuals, _, _ = np.linalg.lstsq(A, m_arr, rcond=None)
        print(f"\n  Fit max|S|/√r = {coeffs[0]:.4f} * √(log r) + {coeffs[1]:.4f}")
        pred = coeffs[0] * sqrt_log_r + coeffs[1]
        r2_sqrt = 1 - np.sum((m_arr - pred)**2) / np.sum((m_arr - np.mean(m_arr))**2)
        print(f"  R² = {r2_sqrt:.4f}")

        # Fit: max = a * log(r) + b
        A2 = np.vstack([log_r, np.ones(len(log_r))]).T
        coeffs2, _, _, _ = np.linalg.lstsq(A2, m_arr, rcond=None)
        print(f"\n  Fit max|S|/√r = {coeffs2[0]:.4f} * log(r) + {coeffs2[1]:.4f}")
        pred2 = coeffs2[0] * log_r + coeffs2[1]
        r2_log = 1 - np.sum((m_arr - pred2)**2) / np.sum((m_arr - np.mean(m_arr))**2)
        print(f"  R² = {r2_log:.4f}")

        # Constant fit
        r2_const = 0  # by definition
        print(f"\n  Constant model: mean = {np.mean(m_arr):.4f}")
        print(f"  R² = 0 (by definition)")

        print(f"\n  BEST FIT: ", end="")
        if r2_sqrt > r2_log and r2_sqrt > 0.3:
            print(f"√(log r) growth (R²={r2_sqrt:.4f})")
        elif r2_log > r2_sqrt and r2_log > 0.3:
            print(f"log r growth (R²={r2_log:.4f})")
        else:
            print(f"Approximately bounded/constant")

    # Check if |S_H(t)| <= sqrt(r) EVER violated
    print("\n--- Does |S_H(t)| ≤ √r hold? ---")
    violations = [res for res in all_results if res['max_over_sqrt_r'] > 1.0]
    print(f"  Primes where max|S|/√r > 1: {len(violations)}/{len(all_results)}")
    if violations:
        for v in violations[:10]:
            print(f"    p={v['p']}, r={v['r']}, max|S|/√r = {v['max_over_sqrt_r']:.4f}")

    violations2 = [res for res in all_results if res['max_over_sqrt_r'] > 2.0]
    print(f"  Primes where max|S|/√r > 2: {len(violations2)}/{len(all_results)}")

    # ============================================================
    # VERDICTS
    # ============================================================

    print("\n" + "=" * 80)
    print("[5] VERDICTS")
    print("=" * 80)

    mean_kurt = np.mean(all_kurt)
    mean_sixth = np.mean(all_sixth)

    # Verdict on distribution
    print("\n--- Distribution of S_H(t)/√r ---")
    if abs(mean_kurt - 2.0) < 0.3:
        print(f"  KURTOSIS RATIO = {mean_kurt:.4f} ≈ 2 → CONSISTENT WITH COMPLEX GAUSSIAN")
    elif abs(mean_kurt - 1.0) < 0.3:
        print(f"  KURTOSIS RATIO = {mean_kurt:.4f} ≈ 1 → CONSISTENT WITH UNIFORM AMPLITUDE")
    else:
        print(f"  KURTOSIS RATIO = {mean_kurt:.4f} → NON-STANDARD DISTRIBUTION")

    if abs(mean_sixth - 6.0) < 1.0:
        print(f"  SIXTH MOMENT RATIO = {mean_sixth:.4f} ≈ 6 → GAUSSIAN CONFIRMED")
    else:
        print(f"  SIXTH MOMENT RATIO = {mean_sixth:.4f} (Gaussian would give 6)")

    # Verdict on Sato-Tate
    mean_st = np.mean([r['sato_tate_ks'] for r in all_results])
    mean_gauss_exp = np.mean([r['gaussian_ks_exp'] for r in all_results])

    print(f"\n  Sato-Tate KS (smaller=better): {mean_st:.4f}")
    print(f"  Gaussian KS (|z|² vs Exp):     {mean_gauss_exp:.4f}")

    if mean_gauss_exp < mean_st:
        print(f"  → GAUSSIAN fits better than Sato-Tate")
    else:
        print(f"  → SATO-TATE fits better than Gaussian")

    # Verdict on G_geom
    print("\n--- Conjecture for G_geom ---")
    if abs(mean_kurt - 2.0) < 0.3 and mean_gauss_exp < mean_st:
        print("  Distribution is COMPLEX GAUSSIAN")
        print("  → G_geom is likely LARGE (full unitary group U(r) or similar)")
        print("  → NOT SU(2) [which would give Sato-Tate]")
        print("  → Consistent with maximal monodromy")
    elif mean_st < mean_gauss_exp:
        print("  Distribution closer to SATO-TATE")
        print("  → G_geom likely SU(2)")
    else:
        print("  Distribution is NON-STANDARD")
        print("  → G_geom needs further investigation")

    # Verdict on maximum bound
    print("\n--- Maximum |S_H| bound ---")
    max_ratio_overall = np.max(max_vals)
    if max_ratio_overall <= 1.0:
        print(f"  max|S_H(t)|/√r ≤ {max_ratio_overall:.4f} ≤ 1")
        print(f"  → WEIL BOUND |S_H| ≤ √r appears to HOLD")
    elif max_ratio_overall <= 2.0:
        print(f"  max|S_H(t)|/√r up to {max_ratio_overall:.4f}")
        print(f"  → Weil bound slightly violated, but max ~ O(√r)")
    else:
        print(f"  max|S_H(t)|/√r up to {max_ratio_overall:.4f}")
        print(f"  → SIGNIFICANT violations of √r bound")
        print(f"  → max|S_H| grows FASTER than √r")

    # Save results
    output = {
        'all_results': all_results,
        'summary': {
            'n_primes': len(all_results),
            'mean_E_abs_sq_over_r': float(np.mean(all_E_ratio)),
            'mean_kurtosis_ratio': float(mean_kurt),
            'mean_sixth_moment_ratio': float(mean_sixth),
            'mean_sato_tate_ks': float(mean_st),
            'mean_gaussian_ks_exp': float(mean_gauss_exp),
            'max_max_over_sqrt_r': float(max_ratio_overall),
            'fraction_violating_sqrt_r': float(len(violations)/len(all_results)),
        }
    }

    outpath = '/Users/ericmerle/Documents/Collatz-Junction-Theorem/research_log/R159_results.json'
    with open(outpath, 'w') as f:
        json.dump(output, f, indent=2)
    print(f"\n  Results saved to {outpath}")

    return output

if __name__ == '__main__':
    main()
