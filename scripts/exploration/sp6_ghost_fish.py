#!/usr/bin/env python3
"""
GPS Phase 6 : "Les Poissons Fantômes"
======================================
Question : Les 17 primes "dures" (Mersenne-type, petit ord_p(2))
divisent-elles réellement d(k) = 2^S - 3^k pour k ≥ 18 ?

Si NON → la barrière de Mersenne est une illusion (poissons fantômes).
Si OUI → on sait EXACTEMENT quels (k, p) attaquer.

Anti-hallucination : tout est calculé, rien n'est deviné.
"""

from math import ceil, log2, gcd, log, sqrt
from sympy import factorint, isprime
import numpy as np

print("=" * 70)
print("GPS PHASE 6 : LES POISSONS FANTOMES")
print("=" * 70)

# =====================================================================
# STEP 1 : Recenser les primes "dures" (celles qui FAIL à k=18)
# =====================================================================

def ord_mod(a, n):
    """Compute multiplicative order of a mod n."""
    if gcd(a, n) != 1:
        return None
    o = 1
    x = a % n
    while x != 1:
        x = (x * a) % n
        o += 1
        if o > n:
            return None
    return o

def compute_rho(p):
    """Compute ρ_p = max_{c≠0} |orbit character sum| / ord_p(2)."""
    m = ord_mod(2, p)
    omega = np.exp(2j * np.pi / p)
    orbit = [pow(2, a, p) for a in range(m)]

    max_rho = 0
    for c in range(1, p):
        char_sum = sum(omega ** (c * h) for h in orbit)
        rho_c = abs(char_sum) / m
        max_rho = max(max_rho, rho_c)

    return max_rho, m

# Collect all primes with small ord_p(2) by factoring 2^m - 1
print("\n--- Recensement des primes avec ord_p(2) ≤ 60 ---")

all_primes = {}
max_ord = 60

for m in range(2, max_ord + 1):
    N = (1 << m) - 1
    try:
        factors = factorint(N, limit=10**8)
    except Exception:
        continue

    for p in factors:
        if p < 3 or p in all_primes:
            continue
        actual_ord = ord_mod(2, p)
        if p <= 600000:  # Can compute ρ exactly
            rho, _ = compute_rho(p)
            bound_17 = (p - 1) * rho ** 17
            all_primes[p] = {
                'ord_2': actual_ord, 'rho': rho, 'bound_17': bound_17,
                'status': 'PASS' if bound_17 < 0.041 else 'FAIL'
            }
        else:
            all_primes[p] = {
                'ord_2': actual_ord, 'rho': None, 'bound_17': None,
                'status': 'LARGE'
            }

# Filter: only the FAIL ones (the "hard" primes)
hard_primes = {p: v for p, v in all_primes.items() if v['status'] == 'FAIL'}
print(f"\nTotal primes: {len(all_primes)}")
print(f"PASS: {sum(1 for v in all_primes.values() if v['status']=='PASS')}")
print(f"FAIL: {len(hard_primes)}")
print(f"LARGE: {sum(1 for v in all_primes.values() if v['status']=='LARGE')}")

print(f"\n{'='*70}")
print(f"LES 17 POISSONS SUSPECTS (primes FAIL à k=18)")
print(f"{'='*70}")
print(f"{'p':>10} {'ord_2':>6} {'ρ':>10} {'(p-1)ρ^17':>14} {'k_min':>6}")
print("-" * 52)

for p in sorted(hard_primes.keys()):
    v = hard_primes[p]
    # Compute k_min (where convolution bound passes)
    rho = v['rho']
    k_min = 18
    for k in range(18, 200):
        if (p - 1) * rho ** (k - 1) < 0.041:
            k_min = k
            break
    else:
        k_min = 200  # Didn't converge
    v['k_min'] = k_min
    print(f"{p:>10} {v['ord_2']:>6} {rho:>10.6f} {v['bound_17']:>14.6f} {k_min:>6}")

# =====================================================================
# STEP 2 : Pour chaque prime dure, trouver les k où p | d(k)
# =====================================================================

print(f"\n{'='*70}")
print(f"NAGENT-ILS DANS NOTRE OCEAN ? (p | d(k) pour k ≥ 18 ?)")
print(f"{'='*70}")

def S_of_k(k):
    """S = ⌈k · log₂(3)⌉"""
    return ceil(k * log2(3))

def d_mod_p(k, p):
    """Compute d(k) mod p = (2^S - 3^k) mod p."""
    S = S_of_k(k)
    return (pow(2, S, p) - pow(3, k, p)) % p

# For each hard prime, scan k = 18 to max(200, 2*k_min)
ghost_count = 0
real_count = 0

all_appearances = {}  # p -> list of k where p | d(k)

for p in sorted(hard_primes.keys()):
    v = hard_primes[p]
    k_max_scan = max(300, 3 * v['k_min'])

    appearances = []
    for k in range(18, k_max_scan):
        if d_mod_p(k, p) == 0:
            appearances.append(k)

    all_appearances[p] = appearances

    # Also check: period of d(k) mod p
    # d(k) mod p = 2^{S(k)} - 3^k mod p
    # ord_p(3) gives the period of 3^k mod p
    ord_3 = ord_mod(3, p)
    ord_2 = v['ord_2']

    # The period of 2^{S(k)} mod p is more complex because S(k) = ⌈k·log₂3⌉
    # But 2^S mod p has period ord_2 in S, and S ≈ 1.585·k
    # So the combined period in k is lcm(ord_2 * ???, ord_3)

    if len(appearances) == 0:
        ghost_count += 1
        status = "FANTOME !! (n'apparaît JAMAIS)"
    else:
        real_count += 1
        # Check: are the dangerous appearances in the k_min range?
        dangerous = [k for k in appearances if k < v['k_min']]
        if len(dangerous) == 0:
            status = f"Apparaît mais JAMAIS dans [18, {v['k_min']-1}] — safe!"
        else:
            status = f"REEL et DANGEREUX: {len(dangerous)} cas dans [18, {v['k_min']-1}]"

    n_appear = len(appearances)
    first_few = appearances[:8] if appearances else []
    density = len(appearances) / (k_max_scan - 18)

    print(f"\np = {p} (ord_2={ord_2}, ord_3={ord_3}, k_min={v['k_min']})")
    print(f"  Scan k ∈ [18, {k_max_scan}): {n_appear} apparitions")
    print(f"  Densité: {density:.4f} (≈ 1/{1/density:.1f} si > 0)" if density > 0 else f"  Densité: 0")
    print(f"  Premières: {first_few}")
    print(f"  >>> {status}")

# =====================================================================
# STEP 3 : Verdict global
# =====================================================================

print(f"\n{'='*70}")
print(f"VERDICT GLOBAL")
print(f"{'='*70}")
print(f"Fantômes (n'apparaissent jamais): {ghost_count}/{len(hard_primes)}")
print(f"Réels (apparaissent au moins une fois): {real_count}/{len(hard_primes)}")

# Detailed analysis of the real ones
print(f"\n--- Analyse détaillée des poissons REELS ---")
dangerous_pairs = []
safe_pairs = []

for p in sorted(hard_primes.keys()):
    appearances = all_appearances[p]
    if len(appearances) == 0:
        continue

    v = hard_primes[p]
    k_min = v['k_min']

    # Appearances in the "danger zone" [18, k_min)
    dangerous = [k for k in appearances if 18 <= k < k_min]
    safe_above = [k for k in appearances if k >= k_min]

    print(f"\np = {p}:")
    print(f"  k_min (convolution passe) = {k_min}")
    print(f"  Apparitions dans [18, {k_min}): {dangerous}")
    print(f"  Apparitions dans [{k_min}, ...): {safe_above[:10]}...")

    if dangerous:
        for k in dangerous:
            dangerous_pairs.append((k, p))
            # What is the actual bound at this k?
            S = S_of_k(k)
            C = 1
            for i in range(k - 1):
                C = C * (S - 1 - i) // (i + 1)
            d_val = pow(2, S) - pow(3, k)
            assert d_val % p == 0, f"Bug: {p} should divide d({k})"

            # Can we check if this (k, p) satisfies Condition (Q)?
            # For that we need N_0(p), which requires DP for large k
            print(f"    (k={k}, p={p}): S={S}, C=C({S-1},{k-1}), d(k)/p = {d_val//p}")
    else:
        print(f"  >>> SAFE: aucune apparition dangereuse")

print(f"\n{'='*70}")
print(f"PAIRES (k, p) DANGEREUSES (nécessitent vérification directe)")
print(f"{'='*70}")
print(f"Total: {len(dangerous_pairs)}")
for k, p in sorted(dangerous_pairs):
    print(f"  k={k}, p={p}, ord_2={hard_primes[p]['ord_2']}, ρ={hard_primes[p]['rho']:.6f}")

# =====================================================================
# STEP 4 : Structure périodique des apparitions
# =====================================================================

print(f"\n{'='*70}")
print(f"STRUCTURE PERIODIQUE DES APPARITIONS")
print(f"{'='*70}")

for p in sorted(hard_primes.keys()):
    appearances = all_appearances[p]
    if len(appearances) < 2:
        continue

    # Check for periodicity
    gaps = [appearances[i+1] - appearances[i] for i in range(len(appearances)-1)]
    unique_gaps = sorted(set(gaps))

    ord_3 = ord_mod(3, p)
    ord_2 = hard_primes[p]['ord_2']

    print(f"\np = {p} (ord_2={ord_2}, ord_3={ord_3}):")
    print(f"  Gaps entre apparitions: {gaps[:20]}")
    print(f"  Gaps uniques: {unique_gaps}")

    if len(unique_gaps) == 1:
        period = unique_gaps[0]
        print(f"  >>> PERIODIQUE avec période {period}")
        # Check if period divides ord_3 or lcm(ord_2, ord_3)
        from math import lcm
        l = lcm(ord_2, ord_3)
        print(f"  ord_3 = {ord_3}, lcm(ord_2, ord_3) = {l}")
        print(f"  période divise ord_3? {ord_3 % period == 0}")
        print(f"  période divise lcm? {l % period == 0}")
    elif len(unique_gaps) <= 3:
        print(f"  >>> QUASI-PERIODIQUE ({len(unique_gaps)} gaps distincts)")
        print(f"  Somme des gaps sur un cycle: {sum(unique_gaps)}")
    else:
        print(f"  >>> Structure complexe ({len(unique_gaps)} gaps distincts)")
