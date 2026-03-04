#!/usr/bin/env python3
"""
SP10-L3 — Investigation Niveau 3 : Le Mecanisme m → ρ
=======================================================
ACQUIS L2 :
  - f(k) et ρ sont INDEPENDANTS (Motor B2 naif mort)
  - r(log(m), ρ) = -0.61 : ρ decroit avec m (MECANISME)
  - d(k) selectionne des premiers avec ρ aggrave (Cohen d=1.26)
  - k mod 6 correle avec ρ (r=-0.27)

QUESTIONS L3 :
  L3a : k mod 6 — pourquoi correle avec ρ ?
  L3b : Le biais d(k) — s'explique-t-il par la distribution de m ?
  L3c : Modele ρ = C · m^{-α} — quel α ?
  L3d : Anatomie des "mauvais" premiers (ρ > 0.3)
  L3e : [CLE] m_min(k) croit-il avec k ?

ANTI-REGRESSION : Verification croisee avec donnees SP9 (k≤500)
"""

import numpy as np
from math import log, log2, ceil, gcd, sqrt
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

def is_in_subgroup_2(val, p, m):
    """Verifie si val est dans ⟨2⟩ mod p."""
    h = 1
    for _ in range(m):
        if h == val % p:
            return True
        h = (h * 2) % p
    return False

ALPHA = log2(3)
PRIME_LIMIT = 100_000

print("=" * 70)
print("SP10-L3 — INVESTIGATION NIVEAU 3 : Le Mecanisme m → ρ")
print("=" * 70)
print()

# ── Crible + Scan complet ────────────────────────────────────────

primes = sieve_primes(PRIME_LIMIT)
print(f"  {len(primes)} premiers\n", flush=True)

# Scan etendu k ∈ [18, 500] pour cross-validation avec SP9
K_MIN, K_MAX = 18, 500
all_records = []  # (k, p, m, rho, pm2, m_over_p1, fk, three_in_2)

print(f"Scan k ∈ [{K_MIN}, {K_MAX}]...", flush=True)
start = time.time()

for k in range(K_MIN, K_MAX + 1):
    S = ceil(k * ALPHA)
    dk = pow(2, S) - pow(3, k)
    if dk <= 0:
        continue
    fk = (k * ALPHA) % 1

    remaining = dk
    for p in primes:
        if p * p > remaining:
            break
        if remaining % p != 0:
            continue
        while remaining % p == 0:
            remaining //= p

        m = compute_ord(2, p)
        if m <= 5:
            continue

        rho = compute_rho(p, m, max_c=min(p - 1, 500))
        pm2 = p / (m * m)
        m_over_p1 = m / (p - 1)

        # 3 est-il dans ⟨2⟩ mod p ?
        three_in_2 = is_in_subgroup_2(3, p, m)

        all_records.append({
            'k': k, 'p': p, 'm': m, 'rho': rho,
            'pm2': pm2, 'm_over_p1': m_over_p1, 'fk': fk,
            'three_in_2': three_in_2, 'S': S
        })

    if k % 100 == 0 or k == K_MAX:
        elapsed = time.time() - start
        print(f"  k={k:4d}: {len(all_records)} records, time={elapsed:.0f}s", flush=True)

elapsed = time.time() - start
N = len(all_records)
print(f"\nScan termine : {N} records, {elapsed:.0f}s\n", flush=True)

# ═══════════════════════════════════════════════════════════════════
# ANTI-REGRESSION : Verifier coherence avec SP9
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("ANTI-REGRESSION — Coherence avec SP9")
print("-" * 70)

# SP9 rapportait : 541 primes, rho_max=0.2548, pour k∈[69,500], ord>100
sp9_subset = [r for r in all_records if r['k'] >= 69 and r['m'] > 100]
if sp9_subset:
    sp9_rho_max = max(r['rho'] for r in sp9_subset)
    print(f"SP9 (ord>100, k≥69) : {len(sp9_subset)} records")
    print(f"  ρ_max SP10 = {sp9_rho_max:.4f} (SP9 rapportait 0.2548)")
    # Note: SP9 used max_c = full p-1, we use max_c=500, so rho might differ slightly
    if abs(sp9_rho_max - 0.2548) < 0.05:
        print("  ✅ COHERENT (marge max_c)")
    else:
        print(f"  ⚠️ ECART (attendu ~0.25, obtenu {sp9_rho_max:.4f})")
        print(f"     Cause probable : max_c=500 vs full scan SP9")
print()

# ═══════════════════════════════════════════════════════════════════
# L3a — k mod 6 : DECOMPOSITION PAR CLASSE
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("L3a — k mod 6 : Decomposition par classe")
print("-" * 70)
print()

# Grouper par k mod 6
by_kmod6 = defaultdict(list)
for r in all_records:
    by_kmod6[r['k'] % 6].append(r)

print(f"{'k%6':>4s} {'N':>5s} {'ρ_moy':>8s} {'ρ_med':>8s} {'ρ_max':>8s} "
      f"{'m_moy':>8s} {'3∈⟨2⟩':>6s}")
print("-" * 55)

for mod in range(6):
    recs = by_kmod6[mod]
    if not recs:
        continue
    rhos = [r['rho'] for r in recs]
    ms = [r['m'] for r in recs]
    t_in = sum(1 for r in recs if r['three_in_2'])
    print(f"  {mod:2d}  {len(recs):5d} {np.mean(rhos):8.4f} {np.median(rhos):8.4f} "
          f"{max(rhos):8.4f} {np.mean(ms):8.1f} {100*t_in/len(recs):5.1f}%")

print()
print("INTERPRETATION L3a :")

# Le biais k mod 6 vient-il du biais sur m ?
for mod in range(6):
    recs = by_kmod6[mod]
    if recs:
        avg_m = np.mean([r['m'] for r in recs])
        avg_rho = np.mean([r['rho'] for r in recs])
        # nop - just collect

# Test : correlation disparait-elle si on controle m ?
print("  Test : correlation k%6 ↔ ρ APRES controle de log(m)")
all_rhos = np.array([r['rho'] for r in all_records])
all_ms = np.array([r['m'] for r in all_records])
all_kmod6 = np.array([r['k'] % 6 for r in all_records])
log_ms = np.log(all_ms)

# Regression residuelle : ρ - β·log(m)
beta = np.polyfit(log_ms, all_rhos, 1)[0]
residuals = all_rhos - beta * log_ms
corr_residual = np.corrcoef(all_kmod6, residuals)[0, 1]
print(f"  r(k%6, ρ) brut = {np.corrcoef(all_kmod6, all_rhos)[0,1]:+.4f}")
print(f"  r(k%6, residus apres log(m)) = {corr_residual:+.4f}")
if abs(corr_residual) < 0.1:
    print("  → L'effet k%6 DISPARAIT apres controle de m.")
    print("  → k%6 n'agit pas directement, il biaise m.")
else:
    print("  → L'effet k%6 PERSISTE apres controle de m.")
    print("  → k%6 a un effet PROPRE sur ρ, independant de m.")
print()

# ═══════════════════════════════════════════════════════════════════
# L3b — Le biais d(k) s'explique-t-il par m ?
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("L3b — Biais d(k) : distribution de m comparee")
print("-" * 70)
print()

# Distribution de m pour les premiers de d(k)
dk_ms = [r['m'] for r in all_records]

# Distribution de m pour premiers aleatoires
rng = np.random.RandomState(42)
random_pool = [p for p in primes if p > 50]
rng.shuffle(random_pool)
rand_ms = []
for p in random_pool[:1000]:
    m = compute_ord(2, p)
    if m > 5:
        rand_ms.append(m)
    if len(rand_ms) >= 500:
        break

print(f"  Premiers d(k) : {len(dk_ms)} records")
print(f"  Premiers aleatoires : {len(rand_ms)} records")
print()

bins_m = [(6, 20), (20, 50), (50, 200), (200, 1000), (1000, 5000), (5000, 100000)]
print(f"{'Tranche m':>15s} {'d(k) %':>8s} {'Aleat %':>8s} {'Ratio':>8s}")
print("-" * 45)
for lo, hi in bins_m:
    dk_pct = 100 * sum(1 for m in dk_ms if lo <= m < hi) / len(dk_ms)
    rand_pct = 100 * sum(1 for m in rand_ms if lo <= m < hi) / max(len(rand_ms), 1)
    ratio = dk_pct / rand_pct if rand_pct > 0 else float('inf')
    print(f"  [{lo:5d},{hi:5d}): {dk_pct:7.1f}% {rand_pct:7.1f}% {ratio:7.2f}x")

print()
dk_m_mean = np.mean(dk_ms)
rand_m_mean = np.mean(rand_ms)
print(f"  m moyen d(k) : {dk_m_mean:.1f}")
print(f"  m moyen aleat : {rand_m_mean:.1f}")
print(f"  Ratio : {dk_m_mean/rand_m_mean:.2f}x")
print()

if dk_m_mean < rand_m_mean * 0.8:
    print("  VERDICT L3b : d(k) a des m PLUS PETITS que les aleatoires.")
    print("  → Le biais sur ρ S'EXPLIQUE par le biais sur m.")
    print("  → d(k) selectionne des premiers avec petits ordres → grands ρ.")
    l3b_explained = True
else:
    print("  VERDICT L3b : m similaires → le biais ρ a une AUTRE cause.")
    l3b_explained = False
print()

# ═══════════════════════════════════════════════════════════════════
# L3c — Modele ρ = C · m^{-α}
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("L3c — Ajustement ρ = C · m^{-α}")
print("-" * 70)
print()

# Fit log(ρ) = log(C) - α·log(m)
valid = [(r['m'], r['rho']) for r in all_records if r['rho'] > 0.001]
if len(valid) > 50:
    log_m = np.array([log(m) for m, _ in valid])
    log_rho = np.array([log(rho) for _, rho in valid])

    # Regression lineaire
    coeffs = np.polyfit(log_m, log_rho, 1)
    alpha_fit = -coeffs[0]
    C_fit = np.exp(coeffs[1])
    # R²
    predicted = coeffs[0] * log_m + coeffs[1]
    ss_res = np.sum((log_rho - predicted)**2)
    ss_tot = np.sum((log_rho - np.mean(log_rho))**2)
    r_squared = 1 - ss_res / ss_tot

    print(f"  Modele : ρ ≈ {C_fit:.3f} · m^{{-{alpha_fit:.3f}}}")
    print(f"  R² = {r_squared:.4f}")
    print()
    print(f"  α = {alpha_fit:.3f}")
    print(f"    Weil predit α = 0.5 (borne ρ ≤ √p/m ∝ m^{{-0.5}} si p ∝ m²)")
    print(f"    BGK predit α > 0 (sans valeur)")
    print()

    if alpha_fit > 0.3:
        print(f"  ✅ α = {alpha_fit:.3f} > 0.3 → decroissance confirmee")
    else:
        print(f"  ⚠️ α = {alpha_fit:.3f} faible")

    # VERIFICATION CROISEE : ajuster separement k∈[18,200] et k∈[201,500]
    print()
    print("  CROSS-VALIDATION :")
    for kl, kh, label in [(18, 200, "train"), (201, 500, "test")]:
        subset = [(r['m'], r['rho']) for r in all_records
                  if kl <= r['k'] <= kh and r['rho'] > 0.001]
        if len(subset) > 20:
            lm = np.array([log(m) for m, _ in subset])
            lr = np.array([log(rho) for _, rho in subset])
            c = np.polyfit(lm, lr, 1)
            a = -c[0]
            pred = c[0] * lm + c[1]
            r2 = 1 - np.sum((lr - pred)**2) / np.sum((lr - np.mean(lr))**2)
            print(f"    [{kl},{kh}] ({label}): α={a:.3f}, R²={r2:.4f}, N={len(subset)}")
        else:
            print(f"    [{kl},{kh}] ({label}): pas assez de donnees ({len(subset)})")
print()

# ═══════════════════════════════════════════════════════════════════
# L3d — Anatomie des "mauvais" premiers (ρ > 0.3)
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("L3d — Anatomie des 'mauvais' premiers (ρ > 0.3)")
print("-" * 70)
print()

bad = [r for r in all_records if r['rho'] > 0.3]
print(f"Nombre de 'mauvais' premiers : {len(bad)} / {N} ({100*len(bad)/N:.1f}%)")
print()

if bad:
    print(f"{'k':>4s} {'p':>8s} {'m':>5s} {'ρ':>8s} {'p/m²':>8s} {'m/(p-1)':>8s} {'3∈⟨2⟩':>6s}")
    print("-" * 55)
    for r in sorted(bad, key=lambda x: -x['rho'])[:20]:
        print(f"{r['k']:4d} {r['p']:8d} {r['m']:5d} {r['rho']:8.4f} "
              f"{r['pm2']:8.4f} {r['m_over_p1']:8.4f} "
              f"{'oui' if r['three_in_2'] else 'non'}")

    bad_ms = [r['m'] for r in bad]
    bad_pm2 = [r['pm2'] for r in bad]
    bad_3in2 = sum(1 for r in bad if r['three_in_2'])
    print()
    print(f"  m : min={min(bad_ms)}, max={max(bad_ms)}, moy={np.mean(bad_ms):.1f}")
    print(f"  p/m² : min={min(bad_pm2):.4f}, max={max(bad_pm2):.4f}")
    print(f"  3 ∈ ⟨2⟩ : {bad_3in2}/{len(bad)} ({100*bad_3in2/len(bad):.0f}%)")
    print()

    # Tous les mauvais ont-ils m petit ?
    all_small_m = all(m < 100 for m in bad_ms)
    print(f"  Tous m < 100 ? {'OUI' if all_small_m else 'NON'}")
    if all_small_m:
        print("  → TOUS les mauvais premiers ont un petit ordre.")
        print("  → Si on prouve m ≥ 100 pour tout p | d(k) quand k est grand,")
        print("     les mauvais premiers disparaissent AUTOMATIQUEMENT.")
    else:
        max_bad_m = max(bad_ms)
        print(f"  → Mauvais premier avec m = {max_bad_m} detecte.")
print()

# ═══════════════════════════════════════════════════════════════════
# L3e — [CLE] m_min(k) croit-il avec k ?
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("L3e — [QUESTION CLE] m_min(k) croit-il avec k ?")
print("-" * 70)
print()

# Pour chaque k, trouver le m minimum parmi les premiers divisant d(k)
k_mmin = defaultdict(lambda: float('inf'))
k_mmin_p = {}
k_mmin_rho = {}

for r in all_records:
    k = r['k']
    if r['m'] < k_mmin[k]:
        k_mmin[k] = r['m']
        k_mmin_p[k] = r['p']
        k_mmin_rho[k] = r['rho']

# Filtrer les k avec des donnees
ks_with_data = sorted([k for k in k_mmin if k_mmin[k] < float('inf')])

if len(ks_with_data) > 20:
    print(f"Valeurs de k avec donnees : {len(ks_with_data)}")
    print()

    # Par tranches de k
    print(f"{'Tranche k':>12s} {'N':>4s} {'m_min':>8s} {'m_min_med':>10s} "
          f"{'m_min_max':>10s} {'ρ_worst':>8s}")
    print("-" * 60)
    for kl, kh in [(18, 50), (50, 100), (100, 200), (200, 300), (300, 400), (400, 500)]:
        ks_range = [k for k in ks_with_data if kl <= k <= kh]
        if ks_range:
            mmins = [k_mmin[k] for k in ks_range]
            rhos_worst = [k_mmin_rho[k] for k in ks_range]
            print(f"  [{kl:3d},{kh:3d}]: {len(ks_range):4d} "
                  f"{min(mmins):8d} {int(np.median(mmins)):10d} "
                  f"{max(mmins):10d} {max(rhos_worst):8.4f}")

    print()

    # Regression : m_min(k) en fonction de k
    ks_arr = np.array(ks_with_data, dtype=float)
    mmins_arr = np.array([k_mmin[k] for k in ks_with_data], dtype=float)

    corr_k_mmin = np.corrcoef(ks_arr, mmins_arr)[0, 1]
    corr_k_log_mmin = np.corrcoef(ks_arr, np.log(mmins_arr + 1))[0, 1]
    corr_log_k_log_mmin = np.corrcoef(np.log(ks_arr), np.log(mmins_arr + 1))[0, 1]

    print(f"  r(k, m_min) = {corr_k_mmin:+.4f}")
    print(f"  r(k, log(m_min)) = {corr_k_log_mmin:+.4f}")
    print(f"  r(log(k), log(m_min)) = {corr_log_k_log_mmin:+.4f}")
    print()

    # Test : m_min croit-il lineairement ? Comme k^β ?
    # Fit log(m_min) = a + β·log(k)
    valid_km = [(k, k_mmin[k]) for k in ks_with_data if k_mmin[k] > 1]
    if len(valid_km) > 20:
        lk = np.array([log(k) for k, _ in valid_km])
        lm = np.array([log(mm) for _, mm in valid_km])
        coeffs_km = np.polyfit(lk, lm, 1)
        beta_km = coeffs_km[0]
        print(f"  Modele m_min ∝ k^β : β = {beta_km:.3f}")
        if beta_km > 0.3:
            print(f"  ✅ m_min CROIT avec k (exposant {beta_km:.2f})")
        elif beta_km > 0:
            print(f"  ⚠️ Croissance faible (exposant {beta_km:.2f})")
        else:
            print(f"  ❌ m_min ne croit PAS avec k")

    print()

    # TOP 10 pires cas (m_min le plus petit pour k >= 69)
    print("  Top 10 pires cas (m_min le plus petit, k ≥ 69) :")
    worst_km = sorted([(k, k_mmin[k], k_mmin_p.get(k, 0), k_mmin_rho.get(k, 0))
                       for k in ks_with_data if k >= 69],
                      key=lambda x: x[1])[:10]
    for i, (k, mm, p, rho) in enumerate(worst_km):
        print(f"    {i+1:2d}. k={k:3d} m_min={mm:5d} p={p:8d} ρ={rho:.4f}")

print()

# ═══════════════════════════════════════════════════════════════════
# L3f — BONUS : 3 ∈ ⟨2⟩ et son effet
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("L3f — Effet de '3 ∈ ⟨2⟩' sur ρ")
print("-" * 70)
print()

three_yes = [r for r in all_records if r['three_in_2']]
three_no = [r for r in all_records if not r['three_in_2']]

if three_yes and three_no:
    print(f"  3 ∈ ⟨2⟩ : {len(three_yes):5d} records, "
          f"ρ_moy={np.mean([r['rho'] for r in three_yes]):.4f}, "
          f"m_moy={np.mean([r['m'] for r in three_yes]):.1f}")
    print(f"  3 ∉ ⟨2⟩ : {len(three_no):5d} records, "
          f"ρ_moy={np.mean([r['rho'] for r in three_no]):.4f}, "
          f"m_moy={np.mean([r['m'] for r in three_no]):.1f}")
    print()

    # Apres controle de m
    # Comparer ρ pour m similaires
    print("  Apres controle de m (meme tranche) :")
    for lo, hi in [(11, 50), (50, 200), (200, 1000), (1000, 100000)]:
        y_rhos = [r['rho'] for r in three_yes if lo <= r['m'] < hi]
        n_rhos = [r['rho'] for r in three_no if lo <= r['m'] < hi]
        if len(y_rhos) > 5 and len(n_rhos) > 5:
            print(f"    m∈[{lo},{hi}): 3∈⟨2⟩ ρ={np.mean(y_rhos):.4f} (N={len(y_rhos)}) | "
                  f"3∉⟨2⟩ ρ={np.mean(n_rhos):.4f} (N={len(n_rhos)})")
print()

# ═══════════════════════════════════════════════════════════════════
# SYNTHESE L3
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("SYNTHESE SP10-L3")
print("=" * 70)
print()
print("RESULTATS :")
print()
print("  L3a (k mod 6) : [voir ci-dessus]")
print("  L3b (biais m) : [voir ci-dessus]")
print(f"  L3c (modele)  : ρ ≈ {C_fit:.3f} · m^{{-{alpha_fit:.3f}}}, R²={r_squared:.3f}" if 'C_fit' in dir() else "  L3c : donnees insuffisantes")
print("  L3d (mauvais) : [voir ci-dessus]")
print("  L3e (m_min)   : [voir ci-dessus]")
print()
print("CARTE MISE A JOUR :")
print()
print("  ┌──────────────────────────────────────────────────────┐")
print("  │  CHAINE CAUSALE IDENTIFIEE :                         │")
print("  │                                                      │")
print("  │  k grand → m_min(k) grand → ρ_max petit → (Q)       │")
print("  │     ?          ?              ✅ (r=-0.61)     ?     │")
print("  │                                                      │")
print("  │  QUESTION UNIQUE RESTANTE :                          │")
print("  │  m_min(k) → ∞ quand k → ∞ ?                         │")
print("  │  (ou au moins m_min(k) ≥ f(k) assez grand)          │")
print("  └──────────────────────────────────────────────────────┘")
print()
print("=" * 70)

# ── Sauvegarde resultats bruts pour post-analyse ─────────────────

output = {
    'N': N,
    'K_range': [K_MIN, K_MAX],
    'alpha_fit': float(alpha_fit) if 'alpha_fit' in dir() else None,
    'C_fit': float(C_fit) if 'C_fit' in dir() else None,
    'r_squared': float(r_squared) if 'r_squared' in dir() else None,
    'n_bad': len(bad) if 'bad' in dir() else 0,
    'bad_max_m': max(bad_ms) if 'bad' in dir() and bad else None,
}

outpath = '/tmp/sp10_l3_results.json'
with open(outpath, 'w') as f:
    json.dump(output, f, indent=2)
print(f"\nResultats sauvegardes : {outpath}")
