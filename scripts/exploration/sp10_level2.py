#!/usr/bin/env python3
"""
SP10-L2 — Motor B2 Diagnostic Niveau 2
========================================
Le niveau 1 a montre que f(k) et ρ sont INDEPENDANTS.
La minceur du batiment ne contraint pas les portes.

QUESTIONS NIVEAU 2 :
  L2-Q1 : ω(d(k)) correle-t-il avec worst ρ ? (diversite → petites portes ?)
  L2-Q2 : Le PLUS GRAND facteur premier correle-t-il avec ρ ?
  L2-Q3 : La structure p ≡ 1 mod m est-elle biaisee pour p | d(k) ?
  L2-Q4 : Existe-t-il un AUTRE parametre de d(k) qui correle avec ρ ?
  L2-Q5 : Quel est le mecanisme : pourquoi ρ est-il toujours petit ?

IDEE MOTEUR ALTERNATIF :
  Si la taille ne controle pas ρ, peut-etre que ρ est controle
  par une propriete INTRINSEQUE du sous-groupe ⟨2⟩ mod p,
  independamment de d(k). Autrement dit : ρ < 1-δ pour TOUT p,
  pas seulement pour les p | d(k).
"""

import numpy as np
from math import log, log2, ceil, gcd, sqrt
import time

# ── Utilitaires (identiques a sp10_diagnostic.py) ───────────────

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

ALPHA = log2(3)
PRIME_LIMIT = 100_000

print("=" * 70)
print("SP10-L2 — DIAGNOSTIC NIVEAU 2")
print("=" * 70)
print()

# ── Crible ──────────────────────────────────────────────────────

primes = sieve_primes(PRIME_LIMIT)
print(f"  {len(primes)} premiers\n", flush=True)

# ═══════════════════════════════════════════════════════════════════
# L2-Q1 : ω(d(k)) correle-t-il avec worst ρ ?
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("L2-Q1 — Correlation ω(d(k)) ↔ worst ρ")
print("-" * 70)

k_records = []
start = time.time()

for k in range(18, 301):
    S = ceil(k * ALPHA)
    dk = pow(2, S) - pow(3, k)
    if dk <= 0: continue
    fk = (k * ALPHA) % 1

    # Factorisation + mesures
    remaining = dk
    distinct_primes = []
    for p in primes:
        if p * p > remaining: break
        if remaining % p != 0: continue
        distinct_primes.append(p)
        while remaining % p == 0:
            remaining //= p
    has_large_cofactor = remaining > 1
    if has_large_cofactor:
        largest_found = remaining
        distinct_primes.append(remaining)
    else:
        largest_found = distinct_primes[-1] if distinct_primes else 1

    omega = len(distinct_primes)
    log2_largest = log(largest_found) / log(2) if largest_found > 1 else 0
    log2_dk = log(dk) / log(2) if dk > 0 else 0

    # Worst rho parmi les premiers trouves
    worst_rho = 0.0
    worst_p = 0
    worst_m = 0
    n_rho = 0

    for p in distinct_primes:
        if p > PRIME_LIMIT: continue
        m = compute_ord(2, p)
        if m <= 10: continue
        rho = compute_rho(p, m, max_c=min(p-1, 500))
        n_rho += 1
        if rho > worst_rho:
            worst_rho = rho
            worst_p = p
            worst_m = m

    k_records.append({
        'k': k, 'omega': omega, 'worst_rho': worst_rho,
        'largest_found': largest_found, 'log2_largest': log2_largest,
        'log2_dk': log2_dk, 'fk': fk,
        'has_large_cofactor': has_large_cofactor,
        'n_rho': n_rho, 'worst_p': worst_p, 'worst_m': worst_m
    })

elapsed = time.time() - start
print(f"  Scan termine : {len(k_records)} valeurs de k, {elapsed:.0f}s\n")

# Filtrer les k avec donnees rho
kr = [r for r in k_records if r['worst_rho'] > 0]
print(f"  {len(kr)} valeurs de k avec ρ > 0\n")

if len(kr) > 20:
    omegas = np.array([r['omega'] for r in kr])
    rhos = np.array([r['worst_rho'] for r in kr])
    log2_lp = np.array([r['log2_largest'] for r in kr])
    log2_dks = np.array([r['log2_dk'] for r in kr])
    ks = np.array([r['k'] for r in kr])

    corr_omega_rho = np.corrcoef(omegas, rhos)[0, 1]
    print(f"  r(ω, worst_ρ) = {corr_omega_rho:+.4f}  "
          f"{'← SIGNIFICATIF' if abs(corr_omega_rho) > 0.2 else '← non significatif'}")
    print()

    if abs(corr_omega_rho) > 0.2:
        print(f"  → ω et ρ CORRELES. Plus de facteurs = {'portes plus petites' if corr_omega_rho < 0 else 'portes plus grandes'}.")
    else:
        print(f"  → ω et ρ INDEPENDANTS. La diversite des facteurs ne controle pas ρ.")

print()

# ═══════════════════════════════════════════════════════════════════
# L2-Q2 : Le plus grand facteur correle-t-il avec ρ ?
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("L2-Q2 — Correlation plus grand facteur ↔ worst ρ")
print("-" * 70)

if len(kr) > 20:
    corr_lp_rho = np.corrcoef(log2_lp, rhos)[0, 1]
    print(f"  r(log₂(plus_grand_p), worst_ρ) = {corr_lp_rho:+.4f}  "
          f"{'← SIGNIFICATIF' if abs(corr_lp_rho) > 0.2 else '← non significatif'}")
    print()

    # Aussi : ratio plus grand facteur / d(k)
    ratios_lp = log2_lp / log2_dks
    corr_ratio_rho = np.corrcoef(ratios_lp, rhos)[0, 1]
    print(f"  r(log₂(p_max)/log₂(d(k)), worst_ρ) = {corr_ratio_rho:+.4f}  "
          f"{'← SIGNIFICATIF' if abs(corr_ratio_rho) > 0.2 else '← non significatif'}")

print()

# ═══════════════════════════════════════════════════════════════════
# L2-Q4 : Y a-t-il un parametre cache qui correle avec ρ ?
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("L2-Q4 — Recherche de parametre cache")
print("-" * 70)

if len(kr) > 20:
    # Tester plein de parametres
    params = {
        'k': ks,
        'ω': omegas,
        'log₂(d(k))': log2_dks,
        'log₂(p_max)': log2_lp,
        'p_max/d(k)': ratios_lp,
        'k mod 2': ks % 2,
        'k mod 3': ks % 3,
        'k mod 6': ks % 6,
    }

    print("  Correlations Pearson avec worst_ρ :")
    print()
    for name, vals in params.items():
        corr = np.corrcoef(vals, rhos)[0, 1]
        sig = "***" if abs(corr) > 0.3 else ("** " if abs(corr) > 0.2 else ("*  " if abs(corr) > 0.1 else "   "))
        print(f"    {name:20s} : r = {corr:+.4f} {sig}")

    print()
    print("  Legende : *** |r| > 0.3,  ** |r| > 0.2,  * |r| > 0.1")

print()

# ═══════════════════════════════════════════════════════════════════
# L2-Q5 : ρ est-il INTRINSEQUEMENT petit pour ⟨2⟩ ?
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("L2-Q5 — ρ intrinseque : est-il petit pour TOUT p, pas juste p | d(k) ?")
print("-" * 70)
print()
print("TEST CRUCIAL : Calculer ρ pour des premiers ALEATOIRES (non lies a d(k))")
print("Si ρ est aussi petit → c'est une propriete de ⟨2⟩, pas de d(k).")
print("Si ρ est plus grand → d(k) a un effet protecteur.")
print()

# Prendre des premiers aleatoires dans la meme gamme de taille
# que ceux trouvees dans d(k)
if len(kr) > 0:
    dk_primes = [(r['worst_p'], r['worst_m']) for r in kr if r['worst_p'] > 100]
    dk_rhos = [r['worst_rho'] for r in kr if r['worst_p'] > 100]

    # Primes aleatoires avec ord > 10
    rng = np.random.RandomState(42)
    random_primes_pool = [p for p in primes if p > 100]
    rng.shuffle(random_primes_pool)

    random_rhos = []
    random_tested = 0
    for p in random_primes_pool[:500]:
        m = compute_ord(2, p)
        if m <= 10:
            continue
        rho = compute_rho(p, m, max_c=min(p-1, 500))
        random_rhos.append(rho)
        random_tested += 1
        if random_tested >= 200:
            break

    print(f"Premiers divisant d(k) (avec ρ) : {len(dk_rhos)}")
    print(f"  ρ moy = {np.mean(dk_rhos):.4f}, med = {np.median(dk_rhos):.4f}, "
          f"max = {max(dk_rhos):.4f}")
    print()
    print(f"Premiers ALEATOIRES (meme gamme) : {len(random_rhos)}")
    print(f"  ρ moy = {np.mean(random_rhos):.4f}, med = {np.median(random_rhos):.4f}, "
          f"max = {max(random_rhos):.4f}")
    print()

    # Comparaison
    mean_diff = np.mean(dk_rhos) - np.mean(random_rhos)
    pooled_std = np.sqrt((np.var(dk_rhos) + np.var(random_rhos)) / 2)
    effect = abs(mean_diff) / pooled_std if pooled_std > 0 else 0

    print(f"Difference moyennes : {mean_diff:+.4f}")
    print(f"Cohen's d : {effect:.4f}")
    print()

    if effect < 0.2:
        print("VERDICT L2-Q5 : PAS DE DIFFERENCE")
        print("  → ρ est petit pour ⟨2⟩ en GENERAL, pas specifiquement pour p | d(k)")
        print("  → C'EST UNE PROPRIETE INTRINSEQUE DE ⟨2⟩ !")
        print("  → Le moteur n'est PAS dans d(k), il est dans la NATURE de 2.")
        q5_intrinsic = True
    elif mean_diff < 0:
        print("VERDICT L2-Q5 : d(k) a un EFFET PROTECTEUR")
        print("  → Les premiers divisant d(k) ont ρ PLUS PETIT que les aleatoires")
        print("  → La structure de d(k) aide. Motor B2 a une piste.")
        q5_intrinsic = False
    else:
        print("VERDICT L2-Q5 : d(k) a un EFFET AGGRAVANT")
        print("  → Les premiers divisant d(k) ont ρ PLUS GRAND que les aleatoires")
        print("  → Mauvaise nouvelle pour Motor B2.")
        q5_intrinsic = False

print()

# ═══════════════════════════════════════════════════════════════════
# L2-Q5b : Distribution de ρ par tranche de m
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("L2-Q5b — ρ en fonction de m = ord_p(2)")
print("-" * 70)
print()
print("Si ρ decroit avec m → la decroissance est automatique pour grands ordres.")
print()

# Collecter tous les (m, rho) pour les premiers de d(k)
all_m_rho = []
for k in range(18, 301):
    S = ceil(k * ALPHA)
    dk = pow(2, S) - pow(3, k)
    if dk <= 0: continue
    remaining = dk
    for p in primes:
        if p * p > remaining: break
        if remaining % p != 0: continue
        while remaining % p == 0:
            remaining //= p
        m = compute_ord(2, p)
        if m > 10:
            rho = compute_rho(p, m, max_c=min(p-1, 500))
            all_m_rho.append((m, rho, p))

print(f"Paires (m, ρ) : {len(all_m_rho)}")
print()

if all_m_rho:
    ms = np.array([x[0] for x in all_m_rho])
    rhos_all = np.array([x[1] for x in all_m_rho])

    # Par tranche de m
    tranches = [(11, 30), (30, 100), (100, 500), (500, 2000), (2000, 100000)]
    print(f"{'Tranche m':>15s} {'N':>5s} {'ρ_moy':>8s} {'ρ_med':>8s} {'ρ_max':>8s}")
    print("-" * 50)
    for lo, hi in tranches:
        mask = (ms >= lo) & (ms < hi)
        n = np.sum(mask)
        if n > 0:
            r = rhos_all[mask]
            print(f"  [{lo:5d},{hi:5d}): {n:5d} {np.mean(r):8.4f} "
                  f"{np.median(r):8.4f} {np.max(r):8.4f}")

    # Correlation m vs rho
    corr_m_rho = np.corrcoef(np.log(ms), rhos_all)[0, 1]
    print(f"\n  r(log(m), ρ) = {corr_m_rho:+.4f}")

    if corr_m_rho < -0.3:
        print("  → ρ DECROIT avec m (log-lineaire). Plus le clan est grand, plus la porte est petite.")
        print("  → C'EST LE MECANISME CHERCHE !")
    elif corr_m_rho < -0.1:
        print("  → Tendance faible a la decroissance.")
    else:
        print("  → Pas de decroissance claire avec m.")

print()

# ═══════════════════════════════════════════════════════════════════
# SYNTHESE NIVEAU 2
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("SYNTHESE SP10 NIVEAU 2")
print("=" * 70)
print()
print("CARTE MISE A JOUR :")
print()
print("  [W] Weyl ──→ [E] Equidist ──→ [G] Taille typique")
print("        ✅           ✅                ✅")
print()
print("  MAIS : la taille ne controle PAS ρ (T4, T5)")
print()
print("  NOUVELLE PISTE :")
print("  ρ pourrait etre controle par la NATURE INTRINSEQUE de ⟨2⟩,")
print("  independamment de d(k).")
print()
print("  Le mecanisme serait :")
print("  Grand m → ⟨2⟩ bien distribue → ρ petit → Condition (Q)")
print()
print("  Et la question se reduit a :")
print("  'Tout premier p | d(k) avec grand m a-t-il ρ < 1-δ ?'")
print("  Ce qui est EXACTEMENT le probleme BGK, mais specialise a base=2.")
print()
print("=" * 70)
