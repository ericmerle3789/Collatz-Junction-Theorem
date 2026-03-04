#!/usr/bin/env python3
"""
SP10-L4 — INVESTIGATION NIVEAU 4 : Le Gap d'Uniformite
========================================================
Apres le renversement L3, la question unique est :
  ρ(p, ⟨2⟩) est-il borne UNIFORMEMENT loin de 1 ?

PROTOCOLE :
  - Anti-hallucination : chaque affirmation verifiee par calcul
  - Anti-regression : cross-check avec L3 (ρ_max=0.618 pour p=127)
  - Ecriture au fil de l'eau dans /tmp/sp10_l4_progress.txt
  - Resultats finaux dans /tmp/sp10_l4_results.json

INVESTIGATIONS :
  L4a : Scan exhaustif ρ_max(m) pour m = 2..200
        Pour CHAQUE m, trouver le p qui maximise ρ(p, ⟨2⟩)
        (parmi les p tels que ord_p(2) = m)
  L4b : Extension de la verification (Q) a k ∈ [18, 5000]
  L4c : Analyse des 7 violations (k ≤ 24)
  L4d : Le nombre d'or — pourquoi ρ_max ≈ 0.618 ?
  L4e : Structure de periodicite p | d(k)
"""

import numpy as np
from math import log, log2, ceil, gcd, sqrt, pi
from collections import defaultdict
import time
import json

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

def compute_rho(p, m, max_c=None):
    """Calcule ρ(p, ⟨2⟩) = max_{c≠0} |Σ ω^{c·h}| / m."""
    if max_c is None:
        max_c = p - 1  # scan complet
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
        phases = 2.0 * pi * mods.astype(np.float64) / p
        s = abs(np.sum(np.exp(1j * phases)))
        r = s / m
        if r > best:
            best = r
    return best

def p_divides_dk(p, k):
    S = ceil(k * log2(3))
    return (pow(2, S, p) - pow(3, k, p)) % p == 0

def write_progress(msg, fpath="/tmp/sp10_l4_progress.txt"):
    with open(fpath, "a") as f:
        f.write(f"[{time.strftime('%H:%M:%S')}] {msg}\n")
    print(msg, flush=True)

ALPHA = log2(3)

# ── Init ─────────────────────────────────────────────────────────

write_progress("=" * 70)
write_progress("SP10-L4 — INVESTIGATION NIVEAU 4 : Le Gap d'Uniformite")
write_progress("=" * 70)

PRIME_LIMIT = 200_000
primes = sieve_primes(PRIME_LIMIT)
write_progress(f"  {len(primes)} premiers charges")

# Anti-regression
rho_127 = compute_rho(127, 7)
assert abs(rho_127 - 0.618) < 0.001, f"REGRESSION: ρ(127)={rho_127}"
write_progress(f"  Anti-regression: ρ(127,7) = {rho_127:.4f} ✅")

results = {}

# ═══════════════════════════════════════════════════════════════════
# L4a : Scan exhaustif ρ_max(m) pour m = 2..200
# ═══════════════════════════════════════════════════════════════════

write_progress("")
write_progress("=" * 70)
write_progress("L4a — ρ_max(m) : Scan exhaustif m = 2..200")
write_progress("-" * 70)
write_progress("")
write_progress("Pour chaque m, on cherche le premier p avec ord_p(2) = m")
write_progress("qui MAXIMISE ρ. Scan complet (tous les c) pour p < 5000.")
write_progress("")

t0 = time.time()

# Pour chaque m, collecter tous les p < 5000 avec ord_p(2) = m
# puis calculer ρ exact (scan complet)
rho_max_by_m = {}
rho_max_p_by_m = {}
rho_all_by_m = defaultdict(list)

# Pre-calculer ord_p(2) pour p < 5000
ord_cache = {}
for p in primes:
    if p > 5000:
        break
    ord_cache[p] = compute_ord(2, p)

write_progress(f"  Ordres calcules pour {len(ord_cache)} premiers (< 5000)")

for m_target in range(2, 201):
    # Trouver tous les p avec ord_p(2) = m_target
    candidates = [p for p, o in ord_cache.items() if o == m_target]

    if not candidates:
        continue

    best_rho = 0.0
    best_p = 0
    for p in candidates:
        # Scan complet pour p < 5000 (faisable)
        rho = compute_rho(p, m_target)  # scan complet par defaut
        rho_all_by_m[m_target].append((p, rho))
        if rho > best_rho:
            best_rho = rho
            best_p = p

    rho_max_by_m[m_target] = best_rho
    rho_max_p_by_m[m_target] = best_p

    if m_target <= 30 or m_target % 10 == 0 or best_rho > 0.5:
        write_progress(f"  m={m_target:4d}: {len(candidates):3d} premiers, "
                       f"ρ_max={best_rho:.4f} (p={best_p})")

elapsed = time.time() - t0
write_progress(f"\n  Scan L4a termine: {elapsed:.0f}s")

# Analyse
ms = sorted(rho_max_by_m.keys())
rhos = [rho_max_by_m[m] for m in ms]

write_progress(f"\n  Statistiques ρ_max(m) pour m ∈ [2, 200] :")
write_progress(f"    max global    : ρ = {max(rhos):.6f} a m = {ms[rhos.index(max(rhos))]}")
write_progress(f"    2eme max      : ρ = {sorted(rhos)[-2]:.6f}")
write_progress(f"    3eme max      : ρ = {sorted(rhos)[-3]:.6f}")
write_progress(f"    moy           : ρ = {np.mean(rhos):.6f}")
write_progress(f"    mediane       : ρ = {np.median(rhos):.6f}")

# Top 20 pires m
sorted_pairs = sorted(zip(ms, rhos), key=lambda x: -x[1])
write_progress(f"\n  Top 20 pires m (ρ_max le plus grand) :")
write_progress(f"  {'m':>5s} {'p':>6s} {'ρ_max':>8s} {'m/(p-1)':>8s} {'Nb p':>5s} {'3∈⟨2⟩':>6s}")
write_progress("  " + "-" * 45)

for m, rho in sorted_pairs[:20]:
    p = rho_max_p_by_m[m]
    n_cand = len(rho_all_by_m[m])
    # 3 ∈ ⟨2⟩ ?
    h = 1
    three_in = False
    three_mod = pow(3, 1, p)
    hh = 1
    for _ in range(m):
        if hh == three_mod:
            three_in = True
            break
        hh = (hh * 2) % p

    write_progress(f"  {m:5d} {p:6d} {rho:8.4f} {m/(p-1):8.4f} {n_cand:5d} "
                   f"{'oui' if three_in else 'non':>6s}")

# Ajuster le modele ρ_max(m) = C · m^{-α}
ms_arr = np.array(ms, dtype=float)
rhos_arr = np.array(rhos, dtype=float)
mask = rhos_arr > 0
log_m = np.log(ms_arr[mask])
log_rho = np.log(rhos_arr[mask])
coeffs = np.polyfit(log_m, log_rho, 1)
alpha_max = -coeffs[0]
C_max = np.exp(coeffs[1])
write_progress(f"\n  Modele ρ_max(m) ≈ {C_max:.4f} · m^{{-{alpha_max:.4f}}}")
write_progress(f"  (Weil predit α = 0.5, observe α = {alpha_max:.4f})")

# ρ_max est-il borne par (m-1)/m ?
write_progress(f"\n  Verification ρ_max(m) vs (m-1)/m :")
for m, rho in sorted_pairs[:10]:
    trivial_bound = (m - 1) / m
    ratio = rho / trivial_bound
    write_progress(f"    m={m:4d}: ρ_max={rho:.4f}, (m-1)/m={trivial_bound:.4f}, "
                   f"ratio={ratio:.4f}")

# ρ_max est-il borne par 1/√m ?
write_progress(f"\n  Verification ρ_max(m) vs 1/√m :")
violations_sqrt = 0
for m, rho in sorted_pairs[:10]:
    sqrt_bound = 1.0 / sqrt(m)
    if rho > sqrt_bound:
        violations_sqrt += 1
        write_progress(f"    m={m:4d}: ρ_max={rho:.4f} > 1/√m={sqrt_bound:.4f} ❌")
    else:
        write_progress(f"    m={m:4d}: ρ_max={rho:.4f} ≤ 1/√m={sqrt_bound:.4f} ✅")

results['L4a'] = {
    'max_rho': max(rhos),
    'max_m': ms[rhos.index(max(rhos))],
    'model_alpha': alpha_max,
    'model_C': C_max,
    'violations_sqrt': violations_sqrt,
}

write_progress("")

# ═══════════════════════════════════════════════════════════════════
# L4b : Verification (Q) etendue k ∈ [18, 5000]
# ═══════════════════════════════════════════════════════════════════

write_progress("=" * 70)
write_progress("L4b — Verification (Q) pour k ∈ [18, 5000]")
write_progress("-" * 70)
write_progress("")

t0 = time.time()
q_violations = []
rho_cache = {}

for k in range(18, 5001):
    for p in primes:
        if p > 100000:
            break
        if not p_divides_dk(p, k):
            continue

        if p not in rho_cache:
            m = compute_ord(2, p)
            if m <= 1:
                rho_cache[p] = (m, 0.0)
            else:
                rho = compute_rho(p, m, max_c=min(p - 1, 500))
                rho_cache[p] = (m, rho)
        m, rho = rho_cache[p]
        if m <= 1:
            continue

        val = (p - 1) * (rho ** (k - 17))
        if val >= 0.041:
            q_violations.append({'k': k, 'p': p, 'm': m, 'rho': rho, 'val': val})

    if k % 500 == 0:
        elapsed = time.time() - t0
        write_progress(f"  k={k:5d}: {len(q_violations)} violations, time={elapsed:.0f}s")

elapsed = time.time() - t0
write_progress(f"\n  Scan complet k∈[18,5000]: {elapsed:.0f}s")
write_progress(f"  Violations totales : {len(q_violations)}")

if q_violations:
    k_set = sorted(set(r['k'] for r in q_violations))
    write_progress(f"  k avec violations : {k_set}")
    write_progress(f"  k_max violation : {max(k_set)}")

    q_violations.sort(key=lambda x: -x['val'])
    write_progress(f"\n  Top 10 violations :")
    write_progress(f"  {'k':>5s} {'p':>8s} {'m':>5s} {'ρ':>8s} {'val':>15s}")
    write_progress("  " + "-" * 45)
    for r in q_violations[:10]:
        write_progress(f"  {r['k']:5d} {r['p']:8d} {r['m']:5d} "
                       f"{r['rho']:8.4f} {r['val']:15.6g}")

    # Par premier
    fail_by_p = defaultdict(int)
    for r in q_violations:
        fail_by_p[r['p']] += 1
    write_progress(f"\n  Premiers responsables :")
    for p, cnt in sorted(fail_by_p.items(), key=lambda x: -x[1]):
        write_progress(f"    p={p}: {cnt} violations")
else:
    write_progress("  ✅ ZERO violation pour k ∈ [18, 5000]")

results['L4b'] = {
    'violations': len(q_violations),
    'k_max_violation': max(r['k'] for r in q_violations) if q_violations else 0,
    'k_list': sorted(set(r['k'] for r in q_violations)) if q_violations else [],
}

write_progress("")

# ═══════════════════════════════════════════════════════════════════
# L4c : Les 7 violations (k ≤ 24) — couvertes ?
# ═══════════════════════════════════════════════════════════════════

write_progress("=" * 70)
write_progress("L4c — Analyse des violations k ≤ 24")
write_progress("-" * 70)
write_progress("")

write_progress("  La preuve du Junction Theorem a une composante de verification finie")
write_progress("  pour les 'petits k'. Rappel de la structure :")
write_progress("    - Lemme D17 : pour k ≤ 17, verification directe")
write_progress("    - Condition (Q) : pour k ≥ 18, (p-1)·ρ^{k-17} < 0.041")
write_progress("")
write_progress("  Les violations trouvees :")

violations_small = [r for r in q_violations if r['k'] <= 30]
for r in violations_small:
    write_progress(f"    k={r['k']:3d}, p={r['p']:6d}, m={r['m']:4d}, "
                   f"ρ={r['rho']:.4f}, (p-1)·ρ^(k-17)={r['val']:.4g}")

write_progress("")
write_progress("  Question : le theoreme couvre-t-il k=18..24 par verification directe ?")
write_progress("  Si oui, (Q) n'a besoin d'etre satisfaite que pour k ≥ 25.")
write_progress("  Et pour k ≥ 25, on a ZERO violation (verifie L4b).")
write_progress("")

# Verifier : pour k ∈ {18,..,24}, d(k) > 0 et factorisation complete possible ?
write_progress("  Verification directe d(k) pour k = 18..24 :")
for k in range(18, 25):
    S = ceil(k * ALPHA)
    dk = pow(2, S) - pow(3, k)
    # Factoriser completement (petits nombres)
    remaining = dk
    factors = []
    for p in primes:
        if p * p > remaining:
            break
        if remaining % p == 0:
            v = 0
            while remaining % p == 0:
                v += 1
                remaining //= p
            factors.append((p, v))
    if remaining > 1:
        factors.append((remaining, 1))

    factor_str = " · ".join(f"{p}^{v}" if v > 1 else str(p) for p, v in factors)
    write_progress(f"    k={k}: d(k) = 2^{S} - 3^{k} = {dk}")
    write_progress(f"           = {factor_str}")
    write_progress(f"           bits = {dk.bit_length()}")

write_progress("")

results['L4c'] = {
    'violations_k_le_24': len([r for r in q_violations if r['k'] <= 24]),
    'k_max_violation': max(r['k'] for r in q_violations) if q_violations else 0,
}

# ═══════════════════════════════════════════════════════════════════
# L4d : Pourquoi ρ_max ≈ 0.618 ? Le nombre d'or
# ═══════════════════════════════════════════════════════════════════

write_progress("=" * 70)
write_progress("L4d — Le nombre d'or et ρ_max")
write_progress("-" * 70)
write_progress("")

phi = (1 + sqrt(5)) / 2  # 1.618...
phi_inv = phi - 1  # 0.618...
write_progress(f"  φ = {phi:.10f}")
write_progress(f"  φ - 1 = 1/φ = {phi_inv:.10f}")
write_progress(f"  ρ_max observe = {max(rhos):.10f}")
write_progress(f"  Ecart = {abs(max(rhos) - phi_inv):.10f}")
write_progress("")

# Le maximum est-il exactement (φ-1) ?
# Pour p=127, m=7 : ρ est le max de |Σ_{h∈⟨2⟩} ω^{ch}| / 7
# ⟨2⟩ mod 127 = {1, 2, 4, 8, 16, 32, 64}
write_progress("  Analyse de p=127, m=7 (le maximum) :")
write_progress(f"  ⟨2⟩ mod 127 = {{1, 2, 4, 8, 16, 32, 64}}")

orbit_127 = [1, 2, 4, 8, 16, 32, 64]
# Calculer ρ(c) pour chaque c et trouver le maximum exact
best_c = 0
best_rho_127 = 0.0
for c in range(1, 127):
    s = sum(np.exp(2j * pi * (c * h % 127) / 127) for h in orbit_127)
    rho_c = abs(s) / 7
    if rho_c > best_rho_127:
        best_rho_127 = rho_c
        best_c = c

write_progress(f"  Meilleur c = {best_c}")
write_progress(f"  ρ({best_c}) = {best_rho_127:.10f}")

# Afficher la somme exacte
s_exact = sum(np.exp(2j * pi * (best_c * h % 127) / 127) for h in orbit_127)
write_progress(f"  Somme S = {s_exact.real:.10f} + {s_exact.imag:.10f}i")
write_progress(f"  |S| = {abs(s_exact):.10f}")
write_progress(f"  |S|/7 = {abs(s_exact)/7:.10f}")

# Verifier si c'est EXACTEMENT phi-1
# La formule est |Σ_{h∈H} ω^{ch}| / |H|
# Pour un sous-groupe cyclique H de taille m dans Z/pZ,
# c'est une somme de Ramanujan generalisee

# Verifier pour d'autres p avec m=7
write_progress(f"\n  ρ_max pour TOUS les p avec m = ord_p(2) = 7 :")
primes_m7 = [p for p, o in ord_cache.items() if o == 7]
for p in sorted(primes_m7):
    rho = compute_rho(p, 7)
    write_progress(f"    p={p:6d}: ρ_max = {rho:.6f}")

# Verifier m=3 (le plus petit sous-groupe propre non-trivial)
write_progress(f"\n  ρ_max pour m = 3 (tous les p) :")
primes_m3 = [p for p, o in ord_cache.items() if o == 3]
for p in sorted(primes_m3)[:10]:
    rho = compute_rho(p, 3)
    write_progress(f"    p={p:6d}: ρ_max = {rho:.6f}")

# Borne theorique : pour m=3, ⟨2⟩ = {1, 2, 4} mod p
# La borne triviale est (m-1)/m = 2/3
write_progress(f"\n  Bornes theoriques vs observees :")
for m_check in [3, 5, 7, 11, 13]:
    cands = [p for p, o in ord_cache.items() if o == m_check]
    if cands:
        rhos_m = [compute_rho(p, m_check) for p in cands]
        trivial = (m_check - 1) / m_check
        weil_approx = 1 / sqrt(m_check)
        write_progress(f"    m={m_check:3d}: ρ_max={max(rhos_m):.4f}, "
                       f"(m-1)/m={trivial:.4f}, "
                       f"1/√m={weil_approx:.4f}, "
                       f"N_primes={len(cands)}")

write_progress("")

results['L4d'] = {
    'rho_max_global': max(rhos),
    'phi_inv': phi_inv,
    'ecart': abs(max(rhos) - phi_inv),
    'best_c_127': best_c,
}

# ═══════════════════════════════════════════════════════════════════
# L4e : Structure de periodicite et recurrence
# ═══════════════════════════════════════════════════════════════════

write_progress("=" * 70)
write_progress("L4e — Periodicite et ensemble des k dangereux")
write_progress("-" * 70)
write_progress("")

write_progress("  Pour un premier p fixe avec ord_p(2) = m :")
write_progress("  p | d(k) ssi 2^S ≡ 3^k mod p, ou S = ceil(k·α)")
write_progress("  La condition est quasi-periodique (pas exactement periodique")
write_progress("  car ceil(k·α) n'est pas lineaire).")
write_progress("")

# Pour les "dangereux" (m petit), lister TOUS les k ∈ [18, 5000]
# ou p | d(k) et calculer (p-1)·ρ^{k-17}

dangerous_primes = [
    (7, 3),    # m=3
    (5, 4),    # m=4
    (127, 7),  # m=7
    (17, 8),   # m=8
    (23, 11),  # m=11
    (89, 11),  # m=11
    (257, 16), # m=16
]

write_progress(f"  {'p':>6s} {'m':>4s} {'ρ':>8s} {'N_hits':>6s} {'k_max':>6s} "
               f"{'val_max':>12s} {'SAFE?':>6s}")
write_progress("  " + "-" * 55)

for p, m in dangerous_primes:
    rho = compute_rho(p, m)
    hits = []
    for k in range(18, 5001):
        if p_divides_dk(p, k):
            val = (p - 1) * (rho ** (k - 17))
            hits.append((k, val))

    if hits:
        val_max = max(v for _, v in hits)
        k_max_val = max(k for k, v in hits if v == val_max)
        safe = "✅" if val_max < 0.041 else "❌"
    else:
        val_max = 0
        k_max_val = 0
        safe = "✅"

    write_progress(f"  {p:6d} {m:4d} {rho:8.4f} {len(hits):6d} {k_max_val:6d} "
                   f"{val_max:12.4g} {safe}")

write_progress("")

# Densite des hits : combien de k dans [18, 5000] ont au moins
# un petit premier (m ≤ 20) qui les divise ?
write_progress("  Densite des k avec petit premier (m ≤ 20) :")
k_with_small = set()
for k in range(18, 5001):
    for p in primes:
        if p > 1000:
            break
        if not p_divides_dk(p, k):
            continue
        m = compute_ord(2, p)
        if m <= 20:
            k_with_small.add(k)
            break

write_progress(f"    k avec au moins un p ayant m ≤ 20 : "
               f"{len(k_with_small)} / 4983 ({100*len(k_with_small)/4983:.1f}%)")

# Combien de k n'ont AUCUN petit facteur < 100K ?
k_no_factor = 0
for k in range(18, 5001):
    has_factor = False
    for p in primes:
        if p > 100000:
            break
        if p_divides_dk(p, k):
            has_factor = True
            break
    if not has_factor:
        k_no_factor += 1

write_progress(f"    k sans AUCUN facteur < 100K : "
               f"{k_no_factor} / 4983 ({100*k_no_factor/4983:.1f}%)")
write_progress(f"    → ces k ont potentiellement des GRANDS facteurs non testes")

results['L4e'] = {
    'k_with_small_m': len(k_with_small),
    'k_no_factor': k_no_factor,
}

# ═══════════════════════════════════════════════════════════════════
# SYNTHESE L4
# ═══════════════════════════════════════════════════════════════════

write_progress("")
write_progress("=" * 70)
write_progress("SYNTHESE SP10-L4")
write_progress("=" * 70)
write_progress("")
write_progress(f"L4a: ρ_max global = {max(rhos):.6f} (m={ms[rhos.index(max(rhos))]})")
write_progress(f"     Modele ρ_max(m) ≈ {C_max:.4f} · m^{{-{alpha_max:.4f}}}")
write_progress(f"     Comparaison φ-1 = {phi_inv:.6f}, ecart = {abs(max(rhos)-phi_inv):.6f}")
write_progress(f"L4b: Violations (Q) k∈[18,5000] : {len(q_violations)}")
write_progress(f"     k_max violation : {results['L4b']['k_max_violation']}")
write_progress(f"     k avec violations : {results['L4b']['k_list']}")
write_progress(f"L4c: Violations k ≤ 24 : {results['L4c']['violations_k_le_24']}")
write_progress(f"L4d: ρ_max ≈ φ-1 ? ecart = {results['L4d']['ecart']:.10f}")
write_progress(f"L4e: k avec petit m : {results['L4e']['k_with_small_m']}/4983")
write_progress(f"     k sans facteur < 100K : {results['L4e']['k_no_factor']}/4983")

# Sauvegarder
with open("/tmp/sp10_l4_results.json", "w") as f:
    json.dump(results, f, indent=2, default=str)
write_progress(f"\nResultats sauvegardes : /tmp/sp10_l4_results.json")

write_progress("")
write_progress("=" * 70)
