#!/usr/bin/env python3
"""
SP10 — Motor B2 Diagnostic : Equidistribution → Typicalite → Condition (Q)
===========================================================================
HYPOTHESE : L'equidistribution de {k·log₂(3)} implique que d(k) = 2^S - 3^k
a une factorisation "typique" suffisante pour Condition (Q).

5 TESTS DIAGNOSTIQUES :
  T1 : Equidistribution de f(k) = {k·log₂(3)} dans [0,1]
  T2 : Nombre de facteurs premiers ω(d(k)) vs prediction Erdos-Kac
  T3 : Distribution de m/(p-1) pour p | d(k) vs prediction Artin
  T4 : Correlation entre f(k) et worst ρ par k
  T5 : Batiments minces (f(k) > 0.7) vs epais (f(k) < 0.3)

FORMULE CLE :
  d(k) = 2^S - 3^k = 3^k · (2^{1-{kα}} - 1)  ou α = log₂(3)
  f(k) = {kα} ∈ (0,1), equidistribue par Weyl
"""

import numpy as np
from math import log, log2, ceil, gcd, sqrt
from collections import defaultdict
import time

# ── Utilitaires ──────────────────────────────────────────────────

def sieve_primes(limit):
    """Crible d'Eratosthene."""
    is_prime = [True] * (limit + 1)
    is_prime[0] = is_prime[1] = False
    for i in range(2, int(limit**0.5) + 1):
        if is_prime[i]:
            for j in range(i*i, limit + 1, i):
                is_prime[j] = False
    return [i for i in range(2, limit + 1) if is_prime[i]]

def compute_ord(base, p):
    """Ordre multiplicatif de base mod p."""
    if gcd(base, p) != 1: return 0
    r = 1
    for m in range(1, p):
        r = (r * base) % p
        if r == 1: return m
    return p - 1

def compute_rho(p, m, max_c=500):
    """Calcul de rho = max_c |S(c)|/m pour c in [1, min(p-1, max_c)]."""
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

# ── Constantes ───────────────────────────────────────────────────

ALPHA = log2(3)  # 1.58496250072...
PRIME_LIMIT = 100_000
K_MIN, K_MAX = 18, 300
ORD_THRESHOLD_RHO = 10  # Calculer rho seulement pour ord > seuil

print("=" * 70)
print("SP10 — MOTOR B2 DIAGNOSTIC")
print("Equidistribution → Typicalite → Condition (Q)")
print("=" * 70)
print()

# ── Crible ───────────────────────────────────────────────────────

print(f"Crible des premiers < {PRIME_LIMIT}...", flush=True)
primes = sieve_primes(PRIME_LIMIT)
print(f"  {len(primes)} premiers\n", flush=True)

# ── Scan principal ───────────────────────────────────────────────

k_data = []        # Donnees par k
prime_data = []    # Donnees par premier (pour primes avec ord > seuil)

print(f"Scan k ∈ [{K_MIN}, {K_MAX}]...", flush=True)
start = time.time()

for k in range(K_MIN, K_MAX + 1):
    S = ceil(k * ALPHA)
    fk = (k * ALPHA) % 1  # {k·log₂(3)}
    dk = pow(2, S) - pow(3, k)
    if dk <= 0:
        continue

    log2_dk = log(dk) / log(2)

    # Division par essai
    remaining = dk
    distinct_primes = []

    for p in primes:
        if p * p > remaining:
            break
        if remaining % p != 0:
            continue
        distinct_primes.append(p)
        while remaining % p == 0:
            remaining //= p

    if remaining > 1:
        distinct_primes.append(remaining)

    omega = len(distinct_primes)

    # Prediction Erdos-Kac (pour nombres de taille dk)
    if dk > 10:
        ek_mean = log(log(dk))
        ek_std = sqrt(max(log(log(dk)), 0.01))
    else:
        ek_mean, ek_std = 1.0, 1.0

    # Calculer ord et rho pour chaque premier
    worst_rho = 0.0
    k_prime_count = 0

    for p in distinct_primes:
        if p > 5_000_000:
            continue  # Trop gros pour calculer ord efficacement

        m = compute_ord(2, p)
        m_over_p1 = m / (p - 1) if p > 1 else 0
        pm2 = p / (m * m) if m > 0 else 0

        rho = None
        if m > ORD_THRESHOLD_RHO and p <= PRIME_LIMIT:
            rho = compute_rho(p, m, max_c=min(p - 1, 500))
            if rho > worst_rho:
                worst_rho = rho
            k_prime_count += 1

        prime_data.append({
            'k': k, 'p': p, 'm': m, 'rho': rho,
            'pm2': pm2, 'm_over_p1': m_over_p1, 'fk': fk
        })

    k_data.append({
        'k': k, 'S': S, 'fk': fk, 'omega': omega,
        'log2_dk': log2_dk, 'worst_rho': worst_rho,
        'ek_mean': ek_mean, 'ek_std': ek_std,
        'n_primes_rho': k_prime_count
    })

    if k % 50 == 0 or k == K_MAX:
        elapsed = time.time() - start
        print(f"  k={k:4d}: ω={omega:2d}, f(k)={fk:.4f}, "
              f"worst_ρ={worst_rho:.4f}, primes_ρ={k_prime_count}, "
              f"time={elapsed:.0f}s", flush=True)

elapsed = time.time() - start
N_k = len(k_data)
N_p = len(prime_data)
N_p_rho = sum(1 for d in prime_data if d['rho'] is not None)
print(f"\nScan termine : {N_k} valeurs de k, {N_p} premiers, "
      f"{N_p_rho} avec ρ, {elapsed:.0f}s\n", flush=True)

# ═══════════════════════════════════════════════════════════════════
# T1 — EQUIDISTRIBUTION DE f(k)
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("T1 — Equidistribution de f(k) = {k·log₂(3)}")
print("-" * 70)

fks = [d['fk'] for d in k_data]
n_bins = 10
hist, _ = np.histogram(fks, bins=n_bins, range=(0, 1))
expected = N_k / n_bins

print(f"N = {N_k}, bins = {n_bins}, attendu/bin = {expected:.1f}")
print()
for i in range(n_bins):
    bar = "█" * int(hist[i] * 40 / max(hist))
    dev = (hist[i] - expected) / expected * 100
    print(f"  [{i/n_bins:.1f}, {(i+1)/n_bins:.1f}): {hist[i]:3d}  {bar}  ({dev:+.0f}%)")

chi2 = sum((h - expected)**2 / expected for h in hist)
dof = n_bins - 1
# Critical value chi2(9, 0.05) = 16.92
t1_pass = chi2 < 16.92
print(f"\nχ² = {chi2:.2f} (seuil 5% pour {dof} ddl : 16.92)")
print(f"VERDICT T1 : {'✅ PASS — equidistribue' if t1_pass else '❌ FAIL — non equidistribue'}")
print()

# ═══════════════════════════════════════════════════════════════════
# T2 — ω(d(k)) VS ERDOS-KAC
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("T2 — Nombre de facteurs premiers ω(d(k)) vs Erdos-Kac")
print("-" * 70)

omegas = [d['omega'] for d in k_data]
ek_means = [d['ek_mean'] for d in k_data]
ek_stds = [d['ek_std'] for d in k_data]

print(f"ω observe  : min={min(omegas)}, max={max(omegas)}, "
      f"moyenne={np.mean(omegas):.2f}, mediane={np.median(omegas):.1f}")
print(f"Erdos-Kac  : moyenne predite = {np.mean(ek_means):.2f}, "
      f"σ predite = {np.mean(ek_stds):.2f}")
print(f"NOTE : ω sous-estime (division par essai < {PRIME_LIMIT} seulement)")
print()

# Deviations normalisees
deviations = [(d['omega'] - d['ek_mean']) / max(d['ek_std'], 0.1)
              for d in k_data]
dev_mean = np.mean(deviations)
dev_std = np.std(deviations)

print(f"Deviations normalisees (ω - E[ω])/σ :")
print(f"  moyenne = {dev_mean:.2f} (attendu ≈ 0)")
print(f"  ecart-type = {dev_std:.2f} (attendu ≈ 1)")

t2_verdict = "COMPATIBLE" if abs(dev_mean) < 2 else "ANOMALOUS"
t2_bias = "negatif (moins de facteurs)" if dev_mean < -0.5 else (
    "positif (plus de facteurs)" if dev_mean > 0.5 else "neutre")
print(f"VERDICT T2 : {t2_verdict}, biais {t2_bias}")
print()

# ═══════════════════════════════════════════════════════════════════
# T3 — DISTRIBUTION DE m/(p-1) VS ARTIN
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("T3 — Distribution de m/(p-1) pour p | d(k)")
print("-" * 70)

# Filtrer : primes raisonnables (pas les gros cofacteurs)
m_over_p1s = [d['m_over_p1'] for d in prime_data
              if d['p'] < PRIME_LIMIT and d['p'] > 3]
N_m = len(m_over_p1s)

if N_m > 0:
    primitive_roots = sum(1 for x in m_over_p1s if x > 0.999)
    pct_prim = 100 * primitive_roots / N_m

    print(f"Premiers analyses : {N_m}")
    print(f"Racines primitives (m = p-1) : {primitive_roots} ({pct_prim:.1f}%)")
    print(f"Prediction Artin : ~37.4%")
    print()

    # Distribution par tranches
    bins_mp = [0, 0.1, 0.2, 0.3, 0.5, 0.7, 1.001]
    hist_mp, _ = np.histogram(m_over_p1s, bins=bins_mp)
    for i in range(len(bins_mp) - 1):
        pct = 100 * hist_mp[i] / N_m
        bar = "█" * int(pct * 0.5)
        print(f"  m/(p-1) ∈ [{bins_mp[i]:.1f}, {bins_mp[i+1]:.1f}): "
              f"{hist_mp[i]:4d} ({pct:5.1f}%)  {bar}")

    # Verdict
    t3_anomalous = abs(pct_prim - 37.4) > 15  # Deviation > 15 points
    t3_verdict = "ANOMALOUS" if t3_anomalous else "COMPATIBLE avec Artin"
    print(f"\nVERDICT T3 : {t3_verdict}")
    if t3_anomalous:
        if pct_prim > 37.4:
            print(f"  → PLUS de racines primitives qu'attendu : d(k) favorise les grands ordres")
        else:
            print(f"  → MOINS de racines primitives qu'attendu : d(k) favorise les petits ordres")
else:
    print("Pas assez de donnees pour T3")
    t3_verdict = "INSUFFICIENT DATA"
print()

# ═══════════════════════════════════════════════════════════════════
# T4 — CORRELATION f(k) ↔ WORST ρ
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("T4 — Correlation entre f(k) et worst ρ par k")
print("-" * 70)

# Seulement les k avec donnees ρ
k_with_rho = [d for d in k_data if d['worst_rho'] > 0]
N_rho = len(k_with_rho)

if N_rho > 20:
    fks_r = np.array([d['fk'] for d in k_with_rho])
    rhos_r = np.array([d['worst_rho'] for d in k_with_rho])
    ks_r = np.array([d['k'] for d in k_with_rho])
    log2s_r = np.array([d['log2_dk'] for d in k_with_rho])

    # Correlations
    corr_fk_rho = np.corrcoef(fks_r, rhos_r)[0, 1]
    corr_log2_rho = np.corrcoef(log2s_r, rhos_r)[0, 1]
    corr_k_rho = np.corrcoef(ks_r, rhos_r)[0, 1]

    print(f"N = {N_rho} valeurs de k avec donnees ρ")
    print()
    print(f"  r(f(k), worst_ρ)     = {corr_fk_rho:+.4f}  "
          f"{'← SIGNIFICATIF' if abs(corr_fk_rho) > 0.2 else '← non significatif'}")
    print(f"  r(log₂(d(k)), worst_ρ) = {corr_log2_rho:+.4f}  "
          f"{'← SIGNIFICATIF' if abs(corr_log2_rho) > 0.2 else '← non significatif'}")
    print(f"  r(k, worst_ρ)        = {corr_k_rho:+.4f}  "
          f"{'← SIGNIFICATIF' if abs(corr_k_rho) > 0.2 else '← non significatif'}")

    # Interpretation
    t4_significant = abs(corr_fk_rho) > 0.2
    print(f"\nVERDICT T4 : {'CORRELATION SIGNIFICATIVE' if t4_significant else 'PAS DE CORRELATION'}")
    if t4_significant:
        direction = "POSITIF" if corr_fk_rho > 0 else "NEGATIF"
        print(f"  → Sens {direction} : "
              f"{'batiments minces → ρ plus petit' if corr_fk_rho > 0 else 'batiments minces → ρ plus grand'}")
    else:
        print(f"  → f(k) et worst ρ sont INDEPENDANTS")
        print(f"  → La minceur du batiment ne contraint pas directement ρ")
else:
    print(f"Pas assez de donnees ({N_rho} < 20)")
    t4_significant = False
print()

# ═══════════════════════════════════════════════════════════════════
# T5 — BATIMENTS MINCES VS EPAIS
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("T5 — Batiments minces (f(k) > 0.7) vs epais (f(k) < 0.3)")
print("-" * 70)

thin_primes = [d for d in prime_data if d['fk'] > 0.7 and d['rho'] is not None]
thick_primes = [d for d in prime_data if d['fk'] < 0.3 and d['rho'] is not None]

if len(thin_primes) > 5 and len(thick_primes) > 5:
    thin_rhos = [d['rho'] for d in thin_primes]
    thick_rhos = [d['rho'] for d in thick_primes]
    thin_pm2 = [d['pm2'] for d in thin_primes]
    thick_pm2 = [d['pm2'] for d in thick_primes]
    thin_m_p1 = [d['m_over_p1'] for d in thin_primes]
    thick_m_p1 = [d['m_over_p1'] for d in thick_primes]

    print(f"Minces (f>0.7) : {len(thin_primes):4d} premiers")
    print(f"  ρ    : moy={np.mean(thin_rhos):.4f}, med={np.median(thin_rhos):.4f}, "
          f"max={max(thin_rhos):.4f}")
    print(f"  p/m² : moy={np.mean(thin_pm2):.4f}, max={max(thin_pm2):.4f}")
    print(f"  m/(p-1): moy={np.mean(thin_m_p1):.4f}")
    print()
    print(f"Epais (f<0.3) : {len(thick_primes):4d} premiers")
    print(f"  ρ    : moy={np.mean(thick_rhos):.4f}, med={np.median(thick_rhos):.4f}, "
          f"max={max(thick_rhos):.4f}")
    print(f"  p/m² : moy={np.mean(thick_pm2):.4f}, max={max(thick_pm2):.4f}")
    print(f"  m/(p-1): moy={np.mean(thick_m_p1):.4f}")
    print()

    # Test non-parametrique simple (sans scipy)
    mean_diff = abs(np.mean(thin_rhos) - np.mean(thick_rhos))
    pooled_std = np.sqrt((np.var(thin_rhos) + np.var(thick_rhos)) / 2)
    effect_size = mean_diff / pooled_std if pooled_std > 0 else 0

    print(f"Difference moyennes ρ : {mean_diff:.4f}")
    print(f"Taille d'effet (Cohen's d) : {effect_size:.4f}")
    print(f"  (petit < 0.2, moyen 0.2-0.8, grand > 0.8)")

    t5_significant = effect_size > 0.3
    print(f"\nVERDICT T5 : {'DIFFERENCE SIGNIFICATIVE' if t5_significant else 'PAS DE DIFFERENCE'}")
    if not t5_significant:
        print(f"  → Minces et epais produisent des ρ similaires")
        print(f"  → La minceur ne determine PAS la taille des portes")
else:
    print(f"Pas assez de donnees (minces: {len(thin_primes)}, epais: {len(thick_primes)})")
    t5_significant = False
print()

# ═══════════════════════════════════════════════════════════════════
# SYNTHESE
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("SYNTHESE SP10")
print("=" * 70)
print()

print(f"T1 (equidistribution f(k))     : {'✅ PASS' if t1_pass else '❌ FAIL'}")
print(f"T2 (Erdos-Kac ω(d(k)))         : {t2_verdict}")
print(f"T3 (Artin m/(p-1))             : {t3_verdict}")
print(f"T4 (correlation f(k) ↔ ρ)      : {'SIGNIFICATIVE' if t4_significant else 'NON SIGNIFICATIVE'}")
print(f"T5 (minces vs epais)           : {'SIGNIFICATIVE' if t5_significant else 'NON SIGNIFICATIVE'}")
print()

# Interpretation globale
print("INTERPRETATION :")
if t1_pass and not t4_significant and not t5_significant:
    print("  [W] equidistribution confirmee, mais f(k) et ρ sont INDEPENDANTS.")
    print("  → Motor B2 dans sa forme naive est INSUFFISANT.")
    print("  → La minceur du batiment ne contraint pas la taille des portes.")
    print("  → Il faut un mecanisme INTERMEDIAIRE entre equidistribution et ρ.")
    print("  → Pistes : exploiter la STRUCTURE de d(k), pas juste sa taille.")
elif t1_pass and t4_significant:
    print("  [W] equidistribution confirmee ET correlation f(k)↔ρ detectee !")
    print("  → Motor B2 a des JAMBES. Explorer le mecanisme causal.")
    print("  → Piste : quantifier comment f(k) controle la factorisation → ρ.")
elif t1_pass and t5_significant:
    print("  [W] equidistribution confirmee, difference minces/epais detectee.")
    print("  → Motor B2 a un signal. Approfondir le lien structural.")
print()

print("PROCHAINES ETAPES :")
if not t4_significant:
    print("  1. Tester si ω(d(k)) correle avec worst ρ (lien via diversite)")
    print("  2. Tester si le PLUS GRAND facteur premier correle avec worst ρ")
    print("  3. Explorer Piste A : structure specifique 2^S - 3^k")
    print("  4. Explorer si d(k) a des proprietes SPECIALES exploitables")
else:
    print("  1. Quantifier le mecanisme f(k) → factorisation → ρ")
    print("  2. Formaliser la chaine causale")
    print("  3. Chercher une preuve du lien")

print()
print("=" * 70)
