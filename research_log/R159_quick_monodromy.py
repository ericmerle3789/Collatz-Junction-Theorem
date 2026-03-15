#!/usr/bin/env python3
"""
R159 — Quick monodromy analysis: distribution of S_H(t)/√r
Key questions:
1. Is S_H/√r Gaussian?
2. Does max|S_H|/√r stay bounded?
3. What does this suggest about G_geom?
"""
import sys
import numpy as np
from scipy import stats

def ord_p_2(p):
    r, val = 1, 2 % p
    while val != 1:
        val = (val * 2) % p
        r += 1
    return r

def compute_S_H(p, r):
    """Compute S_H(t) = Σ_{h∈H} e_p(t*(h-1)) for all t = 1..p-2."""
    H = []
    val = 1
    for _ in range(r):
        H.append(val)
        val = (val * 2) % p
    h_minus_1 = np.array([(h - 1) % p for h in H], dtype=np.int64)

    # Vectorized for moderate p
    t_vals = np.arange(1, p - 1)
    phases = np.outer(t_vals, h_minus_1) % p
    S = np.sum(np.exp(2j * np.pi * phases / p), axis=1)
    return S

# Primes with good r values (not primitive root cases where r = p-1)
test_cases = [
    (89, 11),    # r=11, index=8
    (127, 7),    # r=7, index=18
    (151, 15),   # r=15, index=10
    (233, 29),   # r=29, index=8
    (283, 20),   # r=20, index ~14
    (397, 44),   # check
    (631, 18),   # r=18, index=35
    (1013, 22),  # r=22, index=46
    (2551, 50),  # r=50, index=51
    (4513, 24),  # r=24, index ~188
]

print("=" * 85)
print("R159 — DISTRIBUTION DE S_H(t)/√r : TEST GAUSSIEN & MAX")
print("=" * 85)
print(f"{'p':>8} {'r':>4} {'idx':>5} {'E|z|²':>7} {'kurt':>7} {'6th':>7} "
      f"{'max/√r':>8} {'KS_G':>7} {'KS_ang':>7}")
print("-" * 85)
sys.stdout.flush()

all_results = []

for p_target, r_expected in test_cases:
    r = ord_p_2(p_target)
    if r != r_expected:
        print(f"{p_target:>8} r={r} (attendu {r_expected}), SKIP")
        sys.stdout.flush()
        continue

    idx = (p_target - 1) // r
    if idx < 3:
        print(f"{p_target:>8} r={r} idx={idx} (index trop petit, trivial), SKIP")
        sys.stdout.flush()
        continue

    S = compute_S_H(p_target, r)
    S_norm = S / np.sqrt(r)
    abs_norm = np.abs(S_norm)
    abs_sq = abs_norm**2

    m2 = np.mean(abs_sq)
    m4 = np.mean(abs_sq**2)
    m6 = np.mean(abs_sq**3)
    kurt = m4 / m2**2 if m2 > 1e-10 else float('nan')
    sixth = m6 / m2**3 if m2 > 1e-10 else float('nan')
    max_norm = np.max(abs_norm)

    # Gaussian test on real part
    Re_scaled = np.real(S_norm) * np.sqrt(2)
    ks_g, p_g = stats.kstest(Re_scaled, 'norm')

    # Angle uniformity
    angles = np.angle(S) % (2 * np.pi)
    ks_u, p_u = stats.kstest(angles / (2*np.pi), 'uniform')

    print(f"{p_target:>8} {r:>4} {idx:>5} {m2:>7.4f} {kurt:>7.4f} {sixth:>7.4f} "
          f"{max_norm:>8.4f} {ks_g:>7.4f} {ks_u:>7.4f}")
    sys.stdout.flush()

    all_results.append({
        'p': p_target, 'r': r, 'index': idx,
        'E_abs_sq': m2, 'kurtosis': kurt, 'sixth': sixth,
        'max_over_sqrt_r': max_norm,
        'ks_gauss': ks_g, 'ks_angle': ks_u,
    })

# Larger primes (chunk computation)
print("\n--- GRANDS PREMIERS (calcul par chunks) ---")
sys.stdout.flush()

large_primes = []
for p in range(5000, 100000, 2):
    if p % 2 == 0:
        continue
    is_p = True
    for d in range(3, int(p**0.5) + 1, 2):
        if p % d == 0:
            is_p = False
            break
    if not is_p:
        continue
    r = ord_p_2(p)
    idx = (p - 1) // r
    if 10 <= r <= 60 and idx >= 20:
        large_primes.append((p, r, idx))
        if len(large_primes) >= 15:
            break

for p_target, r, idx in large_primes:
    H = []
    val = 1
    for _ in range(r):
        H.append(val)
        val = (val * 2) % p_target
    h_minus_1 = np.array([(h - 1) % p_target for h in H], dtype=np.int64)

    # Chunk computation
    chunk = 10000
    t_vals = np.arange(1, p_target - 1)
    S_all = np.zeros(len(t_vals), dtype=complex)
    for start in range(0, len(t_vals), chunk):
        end = min(start + chunk, len(t_vals))
        phases = np.outer(t_vals[start:end], h_minus_1) % p_target
        S_all[start:end] = np.sum(np.exp(2j * np.pi * phases / p_target), axis=1)

    S_norm = S_all / np.sqrt(r)
    abs_norm = np.abs(S_norm)
    abs_sq = abs_norm**2

    m2 = np.mean(abs_sq)
    m4 = np.mean(abs_sq**2)
    m6 = np.mean(abs_sq**3)
    kurt = m4 / m2**2
    sixth = m6 / m2**3
    max_norm = np.max(abs_norm)

    Re_scaled = np.real(S_norm) * np.sqrt(2)
    ks_g, _ = stats.kstest(Re_scaled, 'norm')
    angles = np.angle(S_all) % (2 * np.pi)
    ks_u, _ = stats.kstest(angles / (2*np.pi), 'uniform')

    print(f"{p_target:>8} {r:>4} {idx:>5} {m2:>7.4f} {kurt:>7.4f} {sixth:>7.4f} "
          f"{max_norm:>8.4f} {ks_g:>7.4f} {ks_u:>7.4f}")
    sys.stdout.flush()

    all_results.append({
        'p': p_target, 'r': r, 'index': idx,
        'E_abs_sq': m2, 'kurtosis': kurt, 'sixth': sixth,
        'max_over_sqrt_r': max_norm,
        'ks_gauss': ks_g, 'ks_angle': ks_u,
    })

# VERDICT
print("\n" + "=" * 85)
print("VERDICT")
print("=" * 85)

maxes = [r['max_over_sqrt_r'] for r in all_results]
kurts = [r['kurtosis'] for r in all_results]
ks_gs = [r['ks_gauss'] for r in all_results]

print(f"\nmax|S_H|/√r : min={min(maxes):.4f}, max={max(maxes):.4f}, mean={np.mean(maxes):.4f}")
print(f"Kurtosis    : min={min(kurts):.4f}, max={max(kurts):.4f}, mean={np.mean(kurts):.4f}")
print(f"  (Gaussien complexe → kurtosis = 2.0)")
print(f"KS Gaussian : min={min(ks_gs):.4f}, max={max(ks_gs):.4f}")

exceed = [r for r in all_results if r['max_over_sqrt_r'] > 1.0]
print(f"\nPrimes avec max|S_H|/√r > 1.0 : {len(exceed)}/{len(all_results)}")
if exceed:
    print("  → La conjecture |S_H| ≤ √r est FAUSSE numériquement pour certains p")
    for r in sorted(exceed, key=lambda x: -x['max_over_sqrt_r'])[:5]:
        print(f"    p={r['p']}, r={r['r']}, max/√r = {r['max_over_sqrt_r']:.4f}")
else:
    print("  → Compatible avec |S_H| ≤ √r")
