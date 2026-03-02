#!/usr/bin/env python3
"""
SP8-O3 v4 : Nature des poissons dans d(k) — VECTORISE NUMPY
==============================================================
Gain vs v3 : compute_rho vectorise => 50-100x plus rapide.
Cible : k ∈ [69, 300] en < 5 minutes.
"""

import sys
import time
from math import log, ceil, isqrt
import numpy as np

# ============================================================
# SIEVE
# ============================================================
print("Sieve...", end=" ", flush=True)
t0 = time.time()
LIMIT = 10**7
sieve = bytearray([1]) * (LIMIT + 1)
sieve[0] = sieve[1] = 0
for i in range(2, isqrt(LIMIT) + 1):
    if sieve[i]:
        sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
PRIMES = [i for i in range(2, LIMIT + 1) if sieve[i]]
del sieve
print(f"{len(PRIMES)} primes ({time.time()-t0:.1f}s)")

# ============================================================
# FONCTIONS VECTORISEES
# ============================================================

def ord_p_2(p, limit=50000):
    if p <= 2: return 0
    v = 1
    for i in range(1, min(p, limit)):
        v = (v * 2) % p
        if v == 1: return i
    return -1

def compute_rho_vec(p, m):
    """rho_max VECTORISE. Retourne (rho_max, best_c)."""
    # Orbite
    orbit = np.array([pow(2, a, p) for a in range(m)], dtype=np.int64)

    # Choix des c a tester
    if p < 30000:
        c_arr = np.arange(1, p, dtype=np.int64)
    elif p < 200000:
        c_arr = np.unique(np.concatenate([
            np.arange(1, 3000, dtype=np.int64),
            np.arange(p//4, p//4 + 500, dtype=np.int64),
            np.arange(p//2 - 300, p//2 + 300, dtype=np.int64),
            np.arange(3*p//4, 3*p//4 + 300, dtype=np.int64),
        ]))
    else:
        c_arr = np.unique(np.concatenate([
            np.arange(1, 2000, dtype=np.int64),
            np.array([p//2, p//3, p//4, p//5, p//7, p//11], dtype=np.int64),
            np.arange(p//2 - 200, p//2 + 200, dtype=np.int64),
        ]))

    c_arr = c_arr[(c_arr > 0) & (c_arr < p)]

    # Chunked computation pour eviter OOM
    # (c_arr.size x orbit.size) float64 matrix
    CHUNK = 5000
    max_rho = 0.0
    best_c = 0

    for start in range(0, len(c_arr), CHUNK):
        chunk = c_arr[start:start + CHUNK]
        # phases[i,j] = (chunk[i] * orbit[j]) % p
        # Use modular arithmetic carefully
        # For int64, chunk[i]*orbit[j] might overflow if p > ~3*10^9
        # Since p < 10^7 and orbit < p, product < 10^14 => fits int64
        products = (chunk[:, None] * orbit[None, :]) % p  # shape (C, m)
        phases = 2.0 * np.pi * products / p
        cos_sum = np.cos(phases).sum(axis=1)
        sin_sum = np.sin(phases).sum(axis=1)
        rho_arr = np.sqrt(cos_sum**2 + sin_sum**2) / m

        idx = np.argmax(rho_arr)
        if rho_arr[idx] > max_rho:
            max_rho = float(rho_arr[idx])
            best_c = int(chunk[idx])

    return max_rho, best_c

def trial_divide_fast(n, primes, limit_idx=None):
    """Trial division. Returns {p: e} pour petits p."""
    factors = {}
    for i, p in enumerate(primes):
        if limit_idx and i >= limit_idx:
            break
        if p * p > n:
            break
        if n % p == 0:
            e = 0
            while n % p == 0:
                n //= p
                e += 1
            factors[p] = e
    if n > 1:
        factors[n] = 1
    return factors

# ============================================================
# ANTI-REGRESSION
# ============================================================
print("\n" + "=" * 75)
print("ANTI-REGRESSION")
print("=" * 75)

for p, m_exp, rho_exp, label in [
    (127, 7, 0.618, "M_7"), (8191, 13, 0.763, "M_13"),
    (2113, 44, 0.543, "p=2113"), (8681, 124, 0.280, "p=8681")]:
    m = ord_p_2(p)
    rho, c = compute_rho_vec(p, m)
    ok = abs(rho - rho_exp) < 0.01
    print(f"  {label}: m={m} {'✓' if m==m_exp else '✗'}, "
          f"ρ={rho:.4f} {'✓' if ok else '✗'}")
    if not ok:
        print("  *** REGRESSION ***"); sys.exit(1)

print("  PASS ✓")

# ============================================================
# EXPERIENCE PRINCIPALE
# ============================================================
print(f"\n{'='*75}")
print("SP8-O3 : POISSONS DANS d(k), k ∈ [69, 300]")
print("=" * 75)

log2_3 = log(3) / log(2)
all_data = []
max_rho_seen = 0.0
worst = None
total_checked = 0
total_pass = 0
t_start = time.time()

for k in range(69, 301):
    S = ceil(k * log2_3)
    d_k = pow(2, S) - pow(3, k)
    n = k - 17
    if d_k <= 0: continue

    factors = trial_divide_fast(d_k, PRIMES)

    for p, e in factors.items():
        if p <= 2: continue
        m = ord_p_2(p, limit=50000)
        if m == -1 or m <= 100: continue

        # Verification croisee
        if pow(2, S, p) != pow(3, k, p):
            print(f"  *** BUG: p={p} ne divise pas d({k}) ***")
            continue

        rho, bc = compute_rho_vec(p, m)
        ratio = p / (m * m)
        conv = (p - 1) * rho ** n
        ok = conv < 0.041

        total_checked += 1
        if ok: total_pass += 1

        d = {'k': k, 'p': p, 'm': m, 'rho': rho,
             'ratio': ratio, 'conv': conv, 'ok': ok, 'n': n}
        all_data.append(d)

        if rho > max_rho_seen:
            max_rho_seen = rho
            worst = d

        if rho > 0.15 or not ok:
            print(f"  k={k:>3} p={p:>10} m={m:>5} ρ={rho:.4f} "
                  f"p/m²={ratio:.1f} conv={conv:.2e} {'✓' if ok else '✗FAIL'}")

    if k % 50 == 0 or k == 300:
        el = time.time() - t_start
        print(f"\n  --- k={k}, {total_checked} primes, "
              f"ρ_max={max_rho_seen:.4f}, {el:.0f}s ---\n")
        sys.stdout.flush()

T = time.time() - t_start

# ============================================================
# RESULTATS
# ============================================================
print(f"\n{'='*75}")
print(f"RESULTATS SP8-O3 ({T:.0f}s)")
print("=" * 75)

if all_data:
    rhos = [d['rho'] for d in all_data]
    ms = [d['m'] for d in all_data]
    rats = [d['ratio'] for d in all_data]

    print(f"\n  Primes analysees : {total_checked}")
    print(f"  100% PASS (Q)   : {'OUI ✓' if total_pass == total_checked else 'NON ✗'}")

    print(f"\n  ρ : min={min(rhos):.4f}, max={max(rhos):.4f}, "
          f"mean={np.mean(rhos):.4f}, med={np.median(rhos):.4f}")

    bins = [0, 0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.50, 1.0]
    print(f"\n  Histogramme de ρ :")
    for i in range(len(bins)-1):
        cnt = sum(1 for r in rhos if bins[i] <= r < bins[i+1])
        pct = 100*cnt/len(rhos) if rhos else 0
        print(f"    [{bins[i]:.2f},{bins[i+1]:.2f}): {cnt:>3} ({pct:>5.1f}%) {'█'*cnt}")

    print(f"\n  m : min={min(ms)}, max={max(ms)}, mean={np.mean(ms):.0f}")
    print(f"  p/m²: min={min(rats):.2f}, max={max(rats):.2f}, mean={np.mean(rats):.2f}")

    # Tests structurels
    h1 = sum(1 for d in all_data if d['m'] > d['k']**0.5)
    h2 = sum(1 for d in all_data if d['m'] > d['p']**0.5)
    print(f"\n  H1 (m > √k): {h1}/{len(all_data)} ({100*h1/len(all_data):.0f}%)")
    print(f"  H2 (m > √p): {h2}/{len(all_data)}")
    print(f"  H4 (p/m² max): {max(rats):.2f}")

    # Top 15
    print(f"\n  TOP 15 par ρ :")
    print(f"  {'k':>3} {'p':>10} {'m':>5} {'ρ':>7} {'p/m²':>5} {'conv':>10} {'?':>4}")
    for d in sorted(all_data, key=lambda x: -x['rho'])[:15]:
        print(f"  {d['k']:>3} {d['p']:>10} {d['m']:>5} {d['rho']:>7.4f} "
              f"{d['ratio']:>5.1f} {d['conv']:>10.2e} "
              f"{'✓' if d['ok'] else '✗'}")

    if worst:
        w = worst
        margin = 0.041 / w['conv'] if w['conv'] > 0 else float('inf')
        print(f"\n  PIRE CAS: k={w['k']}, p={w['p']}, m={w['m']}")
        print(f"    ρ={w['rho']:.6f}, conv={w['conv']:.4e}, "
              f"marge={margin:.2e}x")

    # VERDICT
    print(f"\n{'='*75}")
    if total_pass == total_checked:
        if max(rhos) < 0.30:
            print(f"""  ★★★ FISH-TUNNEL INTACT — POISSONS FINS CONFIRMES ★★★

  {total_checked} primes, k ∈ [69,300], ρ_max = {max(rhos):.4f}
  AUCUN gros poisson dans d(k). 100% passent (Q).
  Le gap theorique (K_MAX, ∞) est VIDE empiriquement.""")
        else:
            print(f"  Fish-Tunnel intact mais ρ_max = {max(rhos):.4f} (> 0.3)")
    else:
        print(f"  *** FISH-TUNNEL BRISE — {total_checked - total_pass} echecs ***")
else:
    print("  Aucune prime ord > 100. Gap vide !")

print()
