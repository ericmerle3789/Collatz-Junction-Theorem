#!/usr/bin/env python3
"""
R159 - Agent 3: Deep analysis of character sum distributions.
Focus on:
1. Detailed histogram comparison (Gaussian vs Sato-Tate)
2. Maximum growth rate with more primes
3. Correlation structure between S_H(t) values
4. Eigenvalue angle distribution (if Sato-Tate)
"""

import numpy as np
from scipy import stats
from collections import defaultdict
import json
import time

def ord_p_2(p):
    r = 1
    val = 2 % p
    while val != 1:
        val = (val * 2) % p
        r += 1
        if r > p:
            return p - 1
    return r

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

def compute_S_H_full(p):
    """Compute S_H(t) for all t = 1..p-2."""
    # H = <2> mod p
    H = []
    val = 1
    r = ord_p_2(p)
    for _ in range(r):
        H.append(val)
        val = (val * 2) % p

    h_minus_1 = np.array([(h - 1) % p for h in H], dtype=np.int64)
    t_values = np.arange(1, p - 1)

    if p < 100000:
        phases = np.outer(t_values, h_minus_1) % p
        exp_vals = np.exp(2j * np.pi * phases / p)
        S = np.sum(exp_vals, axis=1)
    else:
        chunk = 20000
        S = np.zeros(len(t_values), dtype=complex)
        for s in range(0, len(t_values), chunk):
            e = min(s + chunk, len(t_values))
            ph = np.outer(t_values[s:e], h_minus_1) % p
            S[s:e] = np.sum(np.exp(2j * np.pi * ph / p), axis=1)

    return S, r

def detailed_distribution_analysis():
    """
    For a few well-chosen primes, do detailed distribution comparison.
    """
    print("=" * 80)
    print("DETAILED DISTRIBUTION ANALYSIS")
    print("=" * 80)

    # Pick specific primes with known orders
    test_cases = []
    for p in range(3, 200000, 2):
        if not is_prime(p):
            continue
        r = ord_p_2(p)
        if r in [12, 20, 28, 36, 48, 60]:
            test_cases.append((p, r))
            if len(test_cases) >= 18:
                break

    results = []

    for p, r in test_cases:
        print(f"\n--- p = {p}, r = {r} ---")
        S, r_check = compute_S_H_full(p)
        assert r_check == r
        n = len(S)

        S_norm = S / np.sqrt(r)
        Re_norm = np.real(S_norm)
        Im_norm = np.imag(S_norm)
        abs_norm = np.abs(S_norm)
        abs_sq_norm = abs_norm**2
        angles = np.angle(S) % (2 * np.pi)

        # --- Moment analysis ---
        m2 = np.mean(abs_sq_norm)
        m4 = np.mean(abs_sq_norm**2)
        m6 = np.mean(abs_sq_norm**3)
        m8 = np.mean(abs_sq_norm**4)

        # Complex Gaussian N(0,1): E|z|^{2k} = k!
        # So m2=1, m4/m2^2=2, m6/m2^3=6, m8/m2^4=24
        kurt = m4 / m2**2
        sixth = m6 / m2**3
        eighth = m8 / m2**4

        print(f"  E|S/√r|² = {m2:.4f} (expect 1)")
        print(f"  E|S/√r|⁴/(E|S/√r|²)² = {kurt:.4f} (Gaussian=2, Sato-Tate≈1.5)")
        print(f"  E|S/√r|⁶/(E|S/√r|²)³ = {sixth:.4f} (Gaussian=6)")
        print(f"  E|S/√r|⁸/(E|S/√r|²)⁴ = {eighth:.4f} (Gaussian=24)")

        # --- Real part distribution ---
        # Gaussian: Re ~ N(0, 1/2), so Re*sqrt(2) ~ N(0,1)
        ks_gauss_re, p_gauss_re = stats.kstest(Re_norm * np.sqrt(2), 'norm')

        # Sato-Tate: density (2/pi)*sqrt(1-x^2) on [-1,1]
        # For the real part Re(S/sqrt(r)), IF Sato-Tate applied to each angle,
        # the distribution would be semicircular.
        # But S is a SUM of r terms, so central limit theorem applies for large r.

        # More precisely, for Sato-Tate on S_H itself (not individual angles),
        # if G_geom = SU(2), the trace Tr(Frob) has Sato-Tate distribution.
        # The character sum S_H relates to eigenvalues of Frobenius.
        # For rank 1 sheaf: S_H(t) = α(t) where |α|=√r, angle ~ ST.
        # For higher rank: it's a sum of eigenvalues.

        # Quantile comparison with standard normal
        sorted_Re = np.sort(Re_norm * np.sqrt(2))
        n_pts = len(sorted_Re)
        theoretical_q = stats.norm.ppf(np.arange(1, n_pts+1) / (n_pts + 1))
        # QQ correlation
        qq_corr = np.corrcoef(sorted_Re, theoretical_q)[0, 1]

        # --- Exponential test for |S/√r|² ---
        ks_exp, p_exp = stats.kstest(abs_sq_norm, 'expon')

        # --- Rayleigh test for |S/√r| ---
        # If S/√r ~ CN(0,1), then |S/√r| ~ Rayleigh(1/√2)
        ks_ray, p_ray = stats.kstest(abs_norm, stats.rayleigh(scale=1/np.sqrt(2)).cdf)

        # --- Uniform angle ---
        ks_unif, p_unif = stats.kstest(angles / (2*np.pi), 'uniform')

        print(f"  KS Gaussian Re: {ks_gauss_re:.4f} (p={p_gauss_re:.2e})")
        print(f"  KS Exp |z|²:    {ks_exp:.4f} (p={p_exp:.2e})")
        print(f"  KS Rayleigh |z|:{ks_ray:.4f} (p={p_ray:.2e})")
        print(f"  KS Unif angle:  {ks_unif:.4f} (p={p_unif:.2e})")
        print(f"  QQ corr (Re):   {qq_corr:.6f}")

        # Max values
        max_abs_norm = np.max(abs_norm)
        print(f"  max|S|/√r = {max_abs_norm:.4f}")

        # Percentiles
        pcts = [50, 90, 95, 99, 99.9]
        print(f"  Percentiles of |S|/√r: ", end="")
        for pct in pcts:
            print(f"p{pct}={np.percentile(abs_norm, pct):.3f} ", end="")
        print()

        # Expected percentiles for Rayleigh(1/√2)
        print(f"  Rayleigh(1/√2) theory: ", end="")
        for pct in pcts:
            rv = stats.rayleigh(scale=1/np.sqrt(2))
            print(f"p{pct}={rv.ppf(pct/100):.3f} ", end="")
        print()

        results.append({
            'p': int(p), 'r': int(r),
            'E_abs_sq_norm': float(m2),
            'kurtosis': float(kurt),
            'sixth': float(sixth),
            'eighth': float(eighth),
            'ks_gauss_re': float(ks_gauss_re),
            'ks_exp': float(ks_exp),
            'ks_rayleigh': float(ks_ray),
            'ks_angle_unif': float(ks_unif),
            'qq_corr_re': float(qq_corr),
            'max_abs_norm': float(max_abs_norm),
        })

    return results

def maximum_growth_rate_study():
    """
    Study max|S_H(t)|/√r for many primes to determine growth rate.
    """
    print("\n" + "=" * 80)
    print("MAXIMUM GROWTH RATE STUDY")
    print("=" * 80)

    # Collect (p, r, max|S|/√r) for many primes
    data = []
    count = 0
    for p in range(5, 500000, 2):
        if not is_prime(p):
            continue
        r = ord_p_2(p)
        if r < 8:
            continue

        S, r_check = compute_S_H_full(p)
        max_norm = float(np.max(np.abs(S)) / np.sqrt(r))
        data.append((p, r, max_norm))
        count += 1

        if count % 100 == 0:
            print(f"  Processed {count} primes (p up to {p})...")

        if count >= 500:
            break

    # Analysis
    data.sort(key=lambda x: x[1])  # sort by r

    rs = np.array([d[1] for d in data])
    ps = np.array([d[0] for d in data])
    maxs = np.array([d[2] for d in data])

    # Envelope: for each r, what's the maximum observed?
    unique_rs = sorted(set(rs))
    envelope = []
    for r_val in unique_rs:
        mask = rs == r_val
        envelope.append((r_val, np.max(maxs[mask]), np.sum(mask)))

    print(f"\n  Total primes analyzed: {len(data)}")
    print(f"  r range: {min(rs)} to {max(rs)}")
    print(f"  max|S|/√r range: {min(maxs):.4f} to {max(maxs):.4f}")

    # Does max|S|/√r exceed 1?
    exceed_1 = sum(1 for m in maxs if m > 1.0)
    exceed_1_5 = sum(1 for m in maxs if m > 1.5)
    exceed_2 = sum(1 for m in maxs if m > 2.0)
    exceed_3 = sum(1 for m in maxs if m > 3.0)

    print(f"\n  Fraction max|S|/√r > 1.0: {exceed_1}/{len(data)} = {exceed_1/len(data):.3f}")
    print(f"  Fraction max|S|/√r > 1.5: {exceed_1_5}/{len(data)} = {exceed_1_5/len(data):.3f}")
    print(f"  Fraction max|S|/√r > 2.0: {exceed_2}/{len(data)} = {exceed_2/len(data):.3f}")
    print(f"  Fraction max|S|/√r > 3.0: {exceed_3}/{len(data)} = {exceed_3/len(data):.3f}")

    # Print envelope
    print(f"\n  Envelope (maximum of max|S|/√r per r value):")
    for r_val, m, cnt in envelope:
        if cnt >= 2 or r_val in [8, 10, 12, 16, 20, 24, 28, 30, 36, 40, 48, 52, 60, 80, 100]:
            bar = "█" * int(m * 10)
            flag = " ***" if m > 1.0 else ""
            print(f"    r={r_val:>3d} (n={cnt:>3d}): max={m:.4f} {bar}{flag}")

    # Growth rate regression on envelope
    env_r = np.array([e[0] for e in envelope if e[2] >= 2])
    env_m = np.array([e[1] for e in envelope if e[2] >= 2])

    if len(env_r) > 5:
        # Model 1: constant
        mean_m = np.mean(env_m)

        # Model 2: sqrt(log r)
        x2 = np.sqrt(np.log(env_r))
        A2 = np.vstack([x2, np.ones(len(x2))]).T
        c2, _, _, _ = np.linalg.lstsq(A2, env_m, rcond=None)
        pred2 = c2[0] * x2 + c2[1]
        r2_2 = 1 - np.sum((env_m - pred2)**2) / np.sum((env_m - mean_m)**2)

        # Model 3: log r
        x3 = np.log(env_r)
        A3 = np.vstack([x3, np.ones(len(x3))]).T
        c3, _, _, _ = np.linalg.lstsq(A3, env_m, rcond=None)
        pred3 = c3[0] * x3 + c3[1]
        r2_3 = 1 - np.sum((env_m - pred3)**2) / np.sum((env_m - mean_m)**2)

        # Model 4: r^alpha
        # log(max) = alpha*log(r) + C → same as model 3 actually
        # Try: max = a * r^b → log(max) = log(a) + b*log(r)
        log_m = np.log(env_m + 0.001)
        log_r = np.log(env_r)
        A4 = np.vstack([log_r, np.ones(len(log_r))]).T
        c4, _, _, _ = np.linalg.lstsq(A4, log_m, rcond=None)

        print(f"\n  Growth rate fits (on envelope, r with n≥2):")
        print(f"    Constant:   mean = {mean_m:.4f}")
        print(f"    √(log r):   {c2[0]:.4f}*√(log r) + {c2[1]:.4f}, R²={r2_2:.4f}")
        print(f"    log r:      {c3[0]:.4f}*log(r) + {c3[1]:.4f}, R²={r2_3:.4f}")
        print(f"    Power law:  max ~ r^{c4[0]:.4f}, R²=N/A")

    # Also look at max|S|/√r as a function of p (not just r)
    data_by_p = sorted(data, key=lambda x: x[0])
    ps_sorted = np.array([d[0] for d in data_by_p])
    maxs_sorted = np.array([d[2] for d in data_by_p])

    # Running maximum
    running_max = np.maximum.accumulate(maxs_sorted)
    print(f"\n  Running maximum of max|S|/√r as p grows:")
    checkpoints = [100, 500, 1000, 5000, 10000, 50000, 100000, 200000, 500000]
    for cp in checkpoints:
        mask = ps_sorted <= cp
        if np.any(mask):
            rm = np.max(maxs_sorted[mask])
            n_primes = np.sum(mask)
            print(f"    p ≤ {cp:>7d}: max = {rm:.4f} ({n_primes} primes)")

    return data

def correlation_study():
    """Study correlation between S_H(t) for different t."""
    print("\n" + "=" * 80)
    print("CORRELATION STRUCTURE")
    print("=" * 80)

    # For a few primes, check if S_H(t) values are (approximately) independent
    for p in [1021, 4093, 8191]:
        if not is_prime(p):
            continue
        r = ord_p_2(p)
        S, _ = compute_S_H_full(p)
        n = len(S)

        # Autocorrelation of Re(S)
        Re = np.real(S)
        Im = np.imag(S)
        Re_centered = Re - np.mean(Re)
        var_Re = np.var(Re)
        if var_Re > 0:
            autocorr = np.correlate(Re_centered, Re_centered, mode='full') / (var_Re * n)
            autocorr = autocorr[n-1:]  # positive lags only
            print(f"\n  p={p}, r={r}: Autocorrelation of Re(S_H(t)):")
            print(f"    lag 0: {autocorr[0]:.4f}")
            for lag in [1, 2, 3, 5, 10, 20]:
                if lag < len(autocorr):
                    print(f"    lag {lag}: {autocorr[lag]:.6f}")

        # Check: are consecutive S_H values correlated?
        if n > 100:
            corr_consec = np.corrcoef(np.abs(S[:-1]), np.abs(S[1:]))[0, 1]
            print(f"    Corr(|S(t)|, |S(t+1)|) = {corr_consec:.6f}")

            corr_real = np.corrcoef(Re[:-1], Re[1:])[0, 1]
            print(f"    Corr(Re(S(t)), Re(S(t+1))) = {corr_real:.6f}")

def main():
    t0 = time.time()

    results_detail = detailed_distribution_analysis()
    data_max = maximum_growth_rate_study()
    correlation_study()

    # FINAL SUMMARY
    print("\n" + "=" * 80)
    print("FINAL SUMMARY AND VERDICT (R159 Agent 3)")
    print("=" * 80)

    # Aggregate kurtosis
    kurts = [r['kurtosis'] for r in results_detail]
    sixths = [r['sixth'] for r in results_detail]
    eighths = [r['eighth'] for r in results_detail]

    print(f"\n  Moment ratios (averaged over {len(results_detail)} primes):")
    print(f"    E|z|⁴/(E|z|²)² = {np.mean(kurts):.4f} ± {np.std(kurts):.4f}  [Gaussian: 2]")
    print(f"    E|z|⁶/(E|z|²)³ = {np.mean(sixths):.4f} ± {np.std(sixths):.4f}  [Gaussian: 6]")
    print(f"    E|z|⁸/(E|z|²)⁴ = {np.mean(eighths):.4f} ± {np.std(eighths):.4f}  [Gaussian: 24]")

    # Maximum statistics
    all_maxs = [d[2] for d in data_max]
    print(f"\n  Maximum |S_H|/√r statistics ({len(data_max)} primes):")
    print(f"    Overall max: {max(all_maxs):.4f}")
    print(f"    Fraction > 1: {sum(1 for m in all_maxs if m > 1)/len(all_maxs):.3f}")

    # Determine verdict
    mean_k = np.mean(kurts)
    if abs(mean_k - 2.0) < 0.3:
        dist_verdict = "COMPLEX GAUSSIAN N(0,1)"
        geom_verdict = "G_geom is LARGE (likely maximal, possibly full unitary)"
    elif abs(mean_k - 1.5) < 0.3:
        dist_verdict = "SATO-TATE (semicircle)"
        geom_verdict = "G_geom likely SU(2)"
    else:
        dist_verdict = f"NON-STANDARD (kurtosis ratio = {mean_k:.3f})"
        geom_verdict = "G_geom requires further investigation"

    max_overall = max(all_maxs)
    if max_overall <= 1.05:
        bound_verdict = "|S_H(t)| ≤ √r appears to HOLD (Weil bound satisfied)"
    elif max_overall <= 2.0:
        bound_verdict = f"|S_H(t)| can exceed √r (max ratio = {max_overall:.3f}), but stays O(√r)"
    else:
        bound_verdict = f"|S_H(t)| SIGNIFICANTLY exceeds √r (max ratio = {max_overall:.3f})"

    print(f"\n  VERDICT 1 (Distribution): {dist_verdict}")
    print(f"  VERDICT 2 (G_geom):       {geom_verdict}")
    print(f"  VERDICT 3 (Bound):        {bound_verdict}")

    elapsed = time.time() - t0
    print(f"\n  Total computation time: {elapsed:.1f}s")

    # Save
    outpath = '/Users/ericmerle/Documents/Collatz-Junction-Theorem/research_log/R159_deep_results.json'
    output = {
        'detailed_results': results_detail,
        'max_data_sample': [(int(d[0]), int(d[1]), float(d[2])) for d in data_max[:100]],
        'verdicts': {
            'distribution': dist_verdict,
            'G_geom': geom_verdict,
            'bound': bound_verdict,
            'mean_kurtosis': float(mean_k),
            'mean_sixth': float(np.mean(sixths)),
            'mean_eighth': float(np.mean(eighths)),
            'max_ratio_overall': float(max_overall),
        }
    }
    with open(outpath, 'w') as f:
        json.dump(output, f, indent=2)
    print(f"  Results saved to {outpath}")

if __name__ == '__main__':
    main()
