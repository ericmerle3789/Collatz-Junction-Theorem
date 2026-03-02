#!/usr/bin/env python3
"""
SP9-O3 : Practical Scan k ∈ [69, 500]
======================================
Approche : Compute d(k) as bignum, trial divide by primes < 1M.
           Only compute ord and ρ for primes that divide.
"""
import time, sys
import numpy as np
from math import log, ceil, gcd

def sieve_primes(limit):
    """Crible d'Ératosthène."""
    is_prime = [True] * (limit + 1)
    is_prime[0] = is_prime[1] = False
    for i in range(2, int(limit**0.5) + 1):
        if is_prime[i]:
            for j in range(i*i, limit + 1, i):
                is_prime[j] = False
    return [i for i in range(2, limit + 1) if is_prime[i]]

def compute_ord(base, p):
    if gcd(base, p) != 1: return 0
    r, m = 1, 0
    for m in range(1, p):
        r = (r * base) % p
        if r == 1: return m
    return p - 1

def compute_rho(p, m, max_c=10000):
    orbit = []
    h = 1
    for _ in range(m):
        orbit.append(h)
        h = (h * 2) % p
    assert len(set(orbit)) == m and h == 1
    orbit_arr = np.array(orbit, dtype=np.int64)
    c_lim = min(p - 1, max_c)
    best = 0.0
    for c in range(1, c_lim + 1):
        mods = (c * orbit_arr) % p
        phases = 2.0 * np.pi * mods.astype(np.float64) / p
        s = abs(np.sum(np.exp(1j * phases)))
        r = s / m
        if r > best: best = r
    return best

# ANTI-RÉGRESSION
print("Anti-régression...", flush=True)
for pk, em, erho in [(127,7,0.618),(8191,13,0.763),(2113,44,0.543),(8681,124,0.280)]:
    m = compute_ord(2, pk)
    assert m == em
    rho = compute_rho(pk, m, max_c=pk-1)
    assert abs(rho - erho) < 0.01
print("  4/4 PASS ✓\n", flush=True)

# SIEVE
LIMIT = 1_000_000
print(f"Sieve primes < {LIMIT}...", flush=True)
primes = sieve_primes(LIMIT)
print(f"  {len(primes)} primes\n", flush=True)

# SCAN
K_MIN, K_MAX = 69, 500
all_data = []
start = time.time()

print(f"Scanning k ∈ [{K_MIN}, {K_MAX}]...", flush=True)

for k in range(K_MIN, K_MAX + 1):
    S = ceil(k * log(3) / log(2))
    dk = pow(2, S) - pow(3, k)
    if dk <= 0: continue

    # Trial division
    remaining = dk
    for p in primes:
        if p * p > remaining: break
        if remaining % p != 0: continue

        # p | d(k) — extract all copies
        while remaining % p == 0:
            remaining //= p

        m = compute_ord(2, p)
        if m <= 100: continue

        # Vérifications
        assert pow(2, S, p) == pow(3, k, p)
        r = S % m
        assert pow(2, r, p) == pow(3, k, p)

        rho = compute_rho(p, m)
        assert rho <= 1.0 + 1e-10
        pm2 = p / (m * m)

        if rho > 1e-15:
            log_conv = (k - 17) * np.log(rho) + np.log(p - 1)
            q_pass = log_conv < np.log(0.041)
        else:
            q_pass = True

        all_data.append({'k':k,'p':p,'m':m,'rho':rho,'pm2':pm2,'q_pass':q_pass,
                         'rho_weil':(p**0.5)/m})

    # Check if remaining is a prime > LIMIT with ord > 100
    if remaining > 1 and remaining < 10**12:
        p = remaining
        # Test primality (simple for numbers < 10^12)
        is_p = True
        for d in range(2, min(int(p**0.5) + 1, 10**6)):
            if p % d == 0:
                is_p = False
                break
        if is_p:
            m = compute_ord(2, p)
            if m > 100:
                assert pow(2, S, p) == pow(3, k, p)
                r = S % m
                assert pow(2, r, p) == pow(3, k, p)
                rho = compute_rho(p, m)
                assert rho <= 1.0 + 1e-10
                pm2 = p / (m * m)
                if rho > 1e-15:
                    log_conv = (k - 17) * np.log(rho) + np.log(p - 1)
                    q_pass = log_conv < np.log(0.041)
                else:
                    q_pass = True
                all_data.append({'k':k,'p':p,'m':m,'rho':rho,'pm2':pm2,'q_pass':q_pass,
                                 'rho_weil':(p**0.5)/m})

    if k % 25 == 0 or k == K_MAX:
        e = time.time() - start
        print(f"  k={k:4d}: {len(all_data):5d} primes, time={e:.0f}s", flush=True)

elapsed = time.time() - start
N = len(all_data)

print(f"\n{'='*70}", flush=True)
print("RÉSULTATS SP9-O3", flush=True)
print(f"{'='*70}", flush=True)
print(f"Plage : k ∈ [{K_MIN}, {K_MAX}]", flush=True)
print(f"Prime limit : {LIMIT}", flush=True)
print(f"Primes (ord>100, divisant d(k)) : {N}", flush=True)
print(f"Temps : {elapsed:.0f}s", flush=True)

if N > 0:
    rhos = [e['rho'] for e in all_data]
    pm2s = [e['pm2'] for e in all_data]
    qf = sum(1 for e in all_data if not e['q_pass'])

    print(f"\n(Q) PASS: {N-qf}/{N}, FAIL: {qf}", flush=True)
    print(f"ρ_max={max(rhos):.6f}, ρ_mean={np.mean(rhos):.6f}, ρ_median={np.median(rhos):.6f}", flush=True)
    print(f"p/m²_max={max(pm2s):.6f}", flush=True)

    print("\nDistribution ρ:", flush=True)
    for lo,hi in [(0,.05),(.05,.10),(.10,.15),(.15,.20),(.20,.25),(.25,.50),(.50,1)]:
        c = sum(1 for r in rhos if lo <= r < hi)
        print(f"  [{lo:.2f},{hi:.2f}): {c:4d} ({100*c/N:.1f}%)", flush=True)

    print("\nDistribution p/m²:", flush=True)
    for lo,hi in [(0,.10),(.10,.25),(.25,.50),(.50,1),(1,1.5),(1.5,100)]:
        c = sum(1 for r in pm2s if lo <= r < hi)
        print(f"  [{lo:.2f},{hi:.2f}): {c:4d} ({100*c/N:.1f}%)", flush=True)

    wo = sum(1 for e in all_data if e['rho_weil'] < 0.5)
    print(f"\nWeil suffisant: {wo}/{N} ({100*wo/N:.1f}%)", flush=True)

    print("\nPar tranche:", flush=True)
    for kl,kh in [(69,100),(100,200),(200,300),(300,400),(400,500)]:
        s = [e for e in all_data if kl <= e['k'] <= kh]
        if s:
            print(f"  [{kl},{kh}]: {len(s):4d}, ρ_max={max(e['rho'] for e in s):.4f}, "
                  f"p/m²_max={max(e['pm2'] for e in s):.4f}", flush=True)

    print("\nTop 10 pires ρ:", flush=True)
    for i,e in enumerate(sorted(all_data, key=lambda x:-x['rho'])[:10]):
        print(f"  {i+1:2d}. k={e['k']:3d} p={e['p']:10d} m={e['m']:5d} "
              f"ρ={e['rho']:.6f} p/m²={e['pm2']:.4f}", flush=True)

    print("\nTop 10 pires p/m²:", flush=True)
    for i,e in enumerate(sorted(all_data, key=lambda x:-x['pm2'])[:10]):
        print(f"  {i+1:2d}. k={e['k']:3d} p={e['p']:10d} m={e['m']:5d} "
              f"ρ={e['rho']:.6f} p/m²={e['pm2']:.4f}", flush=True)

    print(f"\n{'='*70}", flush=True)
    if qf == 0:
        print(f"VERDICT: 100% PASS — {N} primes, ρ_max={max(rhos):.4f}, p/m²_max={max(pm2s):.4f}", flush=True)
    else:
        print(f"VERDICT: {qf} FAIL(S)", flush=True)
    print("="*70, flush=True)
