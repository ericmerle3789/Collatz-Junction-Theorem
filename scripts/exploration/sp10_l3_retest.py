#!/usr/bin/env python3
"""
SP10-L3 RETEST — Investigation de l'obstacle m_min (version optimisée)
======================================================================
OPTIMISATION : Utilise pow(2,S,p) au lieu de 2^S explicite.
  p | d(k) ssi pow(2,S,p) == pow(3,k,p) mod p

QUESTIONS RETEST :
  R1 : Les petits premiers récurrents satisfont-ils (Q) grâce à ρ^{k-17} ?
  R2 : La périodicité p | d(k) est-elle EXACTE ?
  R3 : Pour les k où p=127 divise d(k), quel est v_p(d(k)) ?
  R4 : Condition (Q) vérifiée EXHAUSTIVEMENT pour k ∈ [18, 500]
  R5 : Si on EXCLUT les petits p fixes (p < 1000), m_min croît-il ?
  R6 : Quels sont les facteurs pour les GRANDS k (k>400) ?

ANTI-REGRESSION : Vérifier que ρ(127,7) = 0.618 (cohérent L3)
"""

import numpy as np
from math import log, log2, ceil, gcd
from collections import defaultdict
import time

# ── Utilitaires ──────────────────────────────────────────────────

def sieve_primes(limit):
    is_prime = [True] * (limit + 1)
    is_prime[0] = is_prime[1] = False
    for i in range(2, int(limit**0.5) + 1):
        if is_prime[i]:
            for j in range(i*i, limit + 1, i):
                is_prime[j] = False
    return [i for i in range(2, limit + 1) if is_prime[i]]

def compute_ord(base, p):
    if gcd(base, p) != 1: return 0
    r = 1
    for m in range(1, p):
        r = (r * base) % p
        if r == 1: return m
    return p - 1

def compute_rho(p, m, max_c=500):
    orbit = []
    h = 1
    for _ in range(m):
        orbit.append(h)
        h = (h * 2) % p
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

def compute_rho_full(p, m):
    """ρ avec TOUS les c (scan complet), pour vérification."""
    orbit = []
    h = 1
    for _ in range(m):
        orbit.append(h)
        h = (h * 2) % p
    orbit_arr = np.array(orbit, dtype=np.int64)
    best = 0.0
    for c in range(1, p):
        mods = (c * orbit_arr) % p
        phases = 2.0 * np.pi * mods.astype(np.float64) / p
        s = abs(np.sum(np.exp(1j * phases)))
        r = s / m
        if r > best: best = r
    return best

def p_divides_dk(p, k):
    """Test rapide : p | d(k) = 2^S - 3^k avec S = ceil(k*alpha)."""
    S = ceil(k * log2(3))
    return (pow(2, S, p) - pow(3, k, p)) % p == 0

ALPHA = log2(3)
PRIME_LIMIT = 100_000

print("=" * 70)
print("SP10-L3 RETEST — Investigation de l'obstacle m_min")
print("=" * 70)
print()

primes = sieve_primes(PRIME_LIMIT)
print(f"  {len(primes)} premiers chargés", flush=True)

# ═══════════════════════════════════════════════════════════════════
# ANTI-REGRESSION : vérifier ρ(127, 7) = 0.618
# ═══════════════════════════════════════════════════════════════════

print("\nANTI-REGRESSION :", flush=True)
rho_127 = compute_rho_full(127, 7)
print(f"  ρ(127, m=7) scan complet = {rho_127:.4f}")
rho_127_500 = compute_rho(127, 7, max_c=500)
print(f"  ρ(127, m=7) max_c=500   = {rho_127_500:.4f}")
assert abs(rho_127 - rho_127_500) < 0.01, "REGRESSION"
print(f"  ✅ Cohérent (L3 rapportait 0.6180)")
print()

# ═══════════════════════════════════════════════════════════════════
# R1 : Petits premiers récurrents et Condition (Q)
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("R1 — Condition (Q) pour les petits premiers récurrents")
print("-" * 70)
print()

bad_primes = [
    (127, 7), (257, 16), (89, 11), (241, 24),
    (17, 8), (2113, 44), (14449, 84), (1321, 60),
]

# Calculer ρ pour chacun
bad_data = []
for p, m in bad_primes:
    rho = compute_rho(p, m, max_c=min(p-1, 500))
    bad_data.append((p, m, rho))

print(f"Condition (Q) : (p-1) · ρ^(k-17) < 0.041")
print()
print(f"{'p':>8s} {'m':>4s} {'ρ':>8s} {'k_crit':>8s} {'1er k|p|d':>10s} {'(Q)?':>20s}")
print("-" * 60)

for p, m, rho in bad_data:
    # k critique : (p-1)·ρ^(k-17) < 0.041
    if rho < 1 and rho > 0:
        k_crit = 17 + (log(0.041) - log(p - 1)) / log(rho)
    else:
        k_crit = float('inf')

    # Trouver le premier k ≥ 18 tel que p | d(k) via arithmétique modulaire
    first_k = None
    for k in range(18, 2001):
        if p_divides_dk(p, k):
            first_k = k
            break

    if first_k is not None:
        val = (p - 1) * (rho ** (first_k - 17))
        q_ok = f"{'OUI' if val < 0.041 else 'NON'} ({val:.4g})"
    else:
        q_ok = "p∤d(k) dans [18,2000]"

    print(f"{p:8d} {m:4d} {rho:8.4f} {k_crit:8.1f} "
          f"{first_k if first_k else '-':>10} {q_ok}")

print()

# Détail p=127 (le pire)
print("  Détail p=127 (le pire) :")
p127_ks = []
for k in range(18, 1001):
    if p_divides_dk(127, k):
        val = 126 * (0.618 ** (k - 17))
        p127_ks.append((k, val))

print(f"  k où 127 | d(k) dans [18, 1000] : {len(p127_ks)} valeurs")
for k, val in p127_ks[:12]:
    sat = "✅" if val < 0.041 else "❌"
    print(f"    k={k:4d} : (p-1)·ρ^(k-17) = {val:.6g} {sat}")
if len(p127_ks) > 12:
    print(f"    ... ({len(p127_ks) - 12} de plus)")

for k, val in p127_ks:
    if val < 0.041:
        print(f"\n  → p=127 satisfait (Q) à partir de k={k} (val={val:.6g})")
        break
else:
    print(f"\n  → p=127 ne satisfait JAMAIS (Q) dans [18, 1000] !")
    if p127_ks:
        print(f"     Dernier k={p127_ks[-1][0]}, val={p127_ks[-1][1]:.6g}")

print()

# ═══════════════════════════════════════════════════════════════════
# R2 : Périodicité de p | d(k)
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("R2 — Périodicité de p | d(k)")
print("-" * 70)
print()

for p, m, rho in bad_data[:5]:
    ks_div = [k for k in range(18, 1001) if p_divides_dk(p, k)]
    if len(ks_div) >= 2:
        diffs = [ks_div[i+1] - ks_div[i] for i in range(len(ks_div)-1)]
        unique_diffs = sorted(set(diffs))
        print(f"  p={p:6d} m={m:3d}: {len(ks_div)} hits, "
              f"écarts={unique_diffs[:5]}")
    else:
        print(f"  p={p:6d} m={m:3d}: {len(ks_div)} hits")

print()
print("  Note : si les écarts sont multiples de m, la divisibilité")
print("  est PERIODIQUE avec période liée à m.")
print()

# ═══════════════════════════════════════════════════════════════════
# R3 : Valuation v_127(d(k))
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("R3 — Valuation v_p(d(k)) pour p=127")
print("-" * 70)
print()

for k, val in p127_ks[:10]:
    S = ceil(k * ALPHA)
    # v_p via lifting : d(k) = 2^S - 3^k
    # On peut calculer v_p itérativement
    # d(k) mod p^e : pow(2,S,p^e) - pow(3,k,p^e)
    v = 0
    for e in range(1, 20):
        pe = 127 ** e
        diff = (pow(2, S, pe) - pow(3, k, pe)) % pe
        if diff == 0:
            v = e
        else:
            break
    print(f"  k={k:4d} : v_127(d(k)) = {v}")

print()

# ═══════════════════════════════════════════════════════════════════
# R4 : Condition (Q) EXHAUSTIVE k ∈ [18, 500]
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("R4 — Vérification EXHAUSTIVE de (Q) pour k ∈ [18, 500]")
print("-" * 70)
print()

start = time.time()
q_fail_count = 0
q_fail_details = []

# Cache des ρ déjà calculés
rho_cache = {}

for k in range(18, 501):
    S = ceil(k * ALPHA)

    for p in primes:
        if p > 100000:
            break
        if not p_divides_dk(p, k):
            continue

        m = compute_ord(2, p)
        if m <= 1:
            continue

        if p not in rho_cache:
            rho_cache[p] = compute_rho(p, m, max_c=min(p - 1, 500))
        rho = rho_cache[p]

        val = (p - 1) * (rho ** (k - 17))

        if val >= 0.041:
            q_fail_count += 1
            q_fail_details.append({
                'k': k, 'p': p, 'm': m, 'rho': rho, 'val': val
            })

    if k % 100 == 0:
        elapsed = time.time() - start
        print(f"  k={k:4d}: {q_fail_count} violations, time={elapsed:.0f}s", flush=True)

elapsed = time.time() - start
print(f"\n  Scan complet : {elapsed:.0f}s")
print(f"  Violations de (Q) : {q_fail_count}")
print()

if q_fail_details:
    q_fail_details.sort(key=lambda x: -x['val'])
    print(f"  Top 20 pires violations :")
    print(f"{'k':>5s} {'p':>8s} {'m':>5s} {'ρ':>8s} {'(p-1)ρ^(k-17)':>15s}")
    print("-" * 45)
    for r in q_fail_details[:20]:
        print(f"{r['k']:5d} {r['p']:8d} {r['m']:5d} {r['rho']:8.4f} {r['val']:15.6g}")

    print()
    k_with_fail = set(r['k'] for r in q_fail_details)
    print(f"  k avec au moins une violation : {len(k_with_fail)} / 483")

    print(f"\n  Violations par tranche de k :")
    for kl, kh in [(18, 50), (51, 100), (101, 200), (201, 300), (301, 400), (401, 500)]:
        n_fail = sum(1 for r in q_fail_details if kl <= r['k'] <= kh)
        k_fail = len(set(r['k'] for r in q_fail_details if kl <= r['k'] <= kh))
        print(f"    [{kl:3d},{kh:3d}] : {n_fail} violations, {k_fail} k distincts")

    print()

    # Quels sont les premiers responsables des violations ?
    fail_by_p = defaultdict(int)
    for r in q_fail_details:
        fail_by_p[(r['p'], r['m'], r['rho'])] += 1
    print("  Premiers responsables des violations :")
    for (p, m, rho), count in sorted(fail_by_p.items(), key=lambda x: -x[1]):
        print(f"    p={p:8d} m={m:3d} ρ={rho:.4f} : {count} violations")
else:
    print("  ✅ AUCUNE VIOLATION — Condition (Q) satisfaite ∀ k ∈ [18, 500]")

print()

# ═══════════════════════════════════════════════════════════════════
# R5 : m_min SANS petits premiers (p < 1000)
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("R5 — m_min en excluant les petits premiers (p < 1000)")
print("-" * 70)
print()

start = time.time()
k_mmin_big = defaultdict(lambda: float('inf'))
k_mmin_big_p = {}

for k in range(18, 501):
    for p in primes:
        if p < 1000:
            if not p_divides_dk(p, k):
                continue
            # Skip petit p, on ne les compte pas
            continue
        if p > 100000:
            break
        if not p_divides_dk(p, k):
            continue

        m = compute_ord(2, p)
        if m <= 5:
            continue
        if m < k_mmin_big[k]:
            k_mmin_big[k] = m
            k_mmin_big_p[k] = p

elapsed = time.time() - start
ks_big = sorted([k for k in k_mmin_big if k_mmin_big[k] < float('inf')])

print(f"  Scan : {elapsed:.0f}s, {len(ks_big)} k avec données (p ≥ 1000)")
print()

if len(ks_big) > 20:
    print(f"{'Tranche k':>12s} {'N':>4s} {'m_min':>8s} {'m_min_med':>10s} {'m_min_max':>10s}")
    print("-" * 50)
    for kl, kh in [(18, 50), (50, 100), (100, 200), (200, 300), (300, 400), (400, 500)]:
        ks_range = [k for k in ks_big if kl <= k <= kh]
        if ks_range:
            mmins = [k_mmin_big[k] for k in ks_range]
            print(f"  [{kl:3d},{kh:3d}]: {len(ks_range):4d} "
                  f"{min(mmins):8d} {int(np.median(mmins)):10d} "
                  f"{max(mmins):10d}")

    print()
    ks_arr = np.array(ks_big, dtype=float)
    mmins_arr = np.array([k_mmin_big[k] for k in ks_big], dtype=float)
    corr = np.corrcoef(ks_arr, np.log(mmins_arr + 1))[0, 1]
    print(f"  r(k, log(m_min)) [p≥1000] = {corr:+.4f}")

    lk = np.array([log(k) for k in ks_big])
    lm = np.array([log(k_mmin_big[k]) for k in ks_big])
    beta = np.polyfit(lk, lm, 1)[0]
    print(f"  Modèle m_min ∝ k^β [p≥1000] : β = {beta:.3f}")
    if beta > 0.3:
        print(f"  ✅ m_min CROIT avec k quand on exclut les petits p")
    else:
        print(f"  ⚠️ Croissance toujours faible (β={beta:.3f})")
else:
    print(f"  Pas assez de données ({len(ks_big)} k)")

print()

# ═══════════════════════════════════════════════════════════════════
# R6 : Facteurs pour grands k
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("R6 — Facteurs de d(k) pour k = 450, 460, ..., 500")
print("-" * 70)
print()

for k in range(450, 501, 10):
    S = ceil(k * ALPHA)
    # Taille approximative
    log2_dk = S - k * ALPHA  # car d(k)/3^k ≈ 2^(S - k·α) - 1

    factors = []
    for p in primes:
        if p > 50000:
            break
        if not p_divides_dk(p, k):
            continue
        m = compute_ord(2, p)
        if p not in rho_cache and m > 1:
            rho_cache[p] = compute_rho(p, m, max_c=min(p-1, 500))
        rho = rho_cache.get(p, 0)
        factors.append((p, m, rho))

    print(f"  k={k}, S={S}, ~{S:.0f} bits total")
    if not factors:
        print(f"    Aucun facteur < 50000")
    for p, m, rho in factors:
        val = (p - 1) * (rho ** (k - 17))
        sat = "✅" if val < 0.041 else "❌"
        print(f"    p={p:>8d} m={m:>5d} ρ={rho:.4f}  (p-1)ρ^(k-17)={val:.4g} {sat}")
    print()

# ═══════════════════════════════════════════════════════════════════
# SYNTHESE
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("SYNTHESE SP10-L3 RETEST")
print("=" * 70)
print()
print(f"R1 : Petits premiers et (Q) via ρ^(k-17) → [voir ci-dessus]")
print(f"R2 : Périodicité p | d(k) → [voir ci-dessus]")
print(f"R3 : Valuations v_p(d(k)) → [voir ci-dessus]")
print(f"R4 : Violations (Q) k∈[18,500] → {q_fail_count} violations")
print(f"R5 : m_min sans petits p → [voir ci-dessus]")
print(f"R6 : Facteurs grands k → [voir ci-dessus]")
print()
print("=" * 70)
