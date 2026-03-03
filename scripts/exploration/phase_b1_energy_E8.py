#!/usr/bin/env python3
"""phase_b1_energy_E8.py — Phase B1 : Estimation numérique de E₈(H) mod p

Pour chaque k dans un sous-ensemble de [5, 67], pour chaque premier p | d(k) :
1. Construire H = {2^0, 2^1, ..., 2^{m-1}} mod p où m = ord₂(p)
2. Calculer E₄(H) et E₈(H) via FFT (identité de Parseval généralisée)
3. Comparer aux valeurs triviales en Z :
   - E₄^{triv} = 2m² - m  (Théorème 3, quasi-Sidon)
   - E₈^{triv} = 4!² × C(m,4) = 576 × C(m,4)  (Lemme 9, permutations)
4. Mesurer le ratio E₈^{obs} / E₈^{triv} (corrections modulaires)
5. Calculer la borne Weyl ordre 2 :
   |μ̂_k(t)|² ≤ (E₈(H) / m^8)^{1/4}
   → mixing si k grand assez que le produit décroît

Identités clés :
  E_{2r}(H) = (1/p) × Σ_{u=0}^{p-1} |G(u)|^{2r}
  où G(u) = Σ_{j=0}^{m-1} e(2πi·u·2^j/p)

Protocole anti-hallucination :
  - Vérification Parseval : Σ|G(u)|² = p × m
  - Vérification E₄ vs formule exacte pour petits p (Mersenne)
  - Cross-validation FFT vs double boucle pour petits m

Auteur : Eric Merle (assisté par Claude)
Date :   3 mars 2026
"""

import math
import time
import numpy as np
from collections import Counter

# ============================================================================
# Configuration
# ============================================================================

# k values à tester (représentatifs du gap + calibration)
K_VALUES = [5, 6, 7, 8, 10, 12, 15, 18, 20, 25, 30, 35, 40]

TRIAL_BOUND = 10**6  # Pour factoriser d(k)
MAX_FFT_SIZE = 10**7  # Limite p pour FFT (mémoire)

# ============================================================================
# Helpers arithmétiques (réutilisés de Phase A)
# ============================================================================

def ceil_log2_3_exact(k):
    """S = ceil(k * log2(3)) exact."""
    three_k = 3 ** k
    S = k
    while (1 << S) < three_k:
        S += 1
    return S


def mult_ord(a, m):
    """Ordre multiplicatif de a mod m (naïf, pour petits m)."""
    if math.gcd(a, m) != 1:
        return 0
    cur, step = a % m, 1
    while cur != 1:
        cur = (cur * a) % m
        step += 1
        if step > m:
            return 0
    return step


def trial_factor(n, bound=TRIAL_BOUND):
    """Factorisation par division d'essai."""
    if n <= 1:
        return [], n
    factors = []
    d = 2
    while d * d <= n and d <= bound:
        if n % d == 0:
            e = 0
            while n % d == 0:
                n //= d
                e += 1
            factors.append((d, e))
        d += (1 if d == 2 else 2)
    return factors, n


def is_probably_prime(n):
    """Miller-Rabin déterministe pour n < 3.3 × 10^24."""
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0:
        return False
    s, d = 0, n - 1
    while d % 2 == 0:
        s += 1
        d //= 2
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]:
        if a >= n:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


# ============================================================================
# Calcul d'énergie via FFT
# ============================================================================

def compute_energies_fft(p, m):
    """Calculer E₄(H) et E₈(H) via FFT.

    H = {2^0, 2^1, ..., 2^{m-1}} mod p

    E_{2r}(H) = (1/p) × Σ_{u=0}^{p-1} |G(u)|^{2r}
    """
    # Construire le vecteur indicateur f : Z/pZ → {0,1}
    f = np.zeros(p, dtype=np.float64)
    h = 1
    for j in range(m):
        f[h % p] += 1.0
        h = (h * 2) % p

    # FFT
    F = np.fft.fft(f)
    mags = np.abs(F)

    # Parseval check : Σ|G(u)|² = p × |H| = p × m
    parseval = np.sum(mags ** 2)
    parseval_expected = p * m
    parseval_err = abs(parseval - parseval_expected) / parseval_expected

    # E₄ = (1/p) × Σ|G(u)|⁴
    sum_S4 = np.sum(mags ** 4)
    E4 = sum_S4 / p

    # E₈ = (1/p) × Σ|G(u)|⁸
    sum_S8 = np.sum(mags ** 8)
    E8 = sum_S8 / p

    # E₆ = (1/p) × Σ|G(u)|⁶ (bonus)
    sum_S6 = np.sum(mags ** 6)
    E6 = sum_S6 / p

    # ρ = max_{u≠0} |G(u)| / m
    mags_nz = mags.copy()
    mags_nz[0] = 0
    rho = np.max(mags_nz) / m

    # Distribution de |G(u)| (percentiles)
    mags_sorted = np.sort(mags_nz[mags_nz > 0])[::-1]
    pct = {}
    if len(mags_sorted) > 0:
        pct['max'] = mags_sorted[0]
        pct['p95'] = np.percentile(mags_sorted, 95) if len(mags_sorted) > 20 else mags_sorted[0]
        pct['median'] = np.median(mags_sorted)
        pct['rms'] = np.sqrt(np.mean(mags_sorted ** 2))

    return {
        'E4': E4, 'E6': E6, 'E8': E8,
        'parseval_err': parseval_err,
        'rho': rho,
        'percentiles': pct,
    }


def compute_E4_brute(p, m):
    """E₄ par double boucle (référence pour cross-validation)."""
    elements = []
    h = 1
    for j in range(m):
        elements.append(h % p)
        h = (h * 2) % p
    sums = Counter()
    for a in elements:
        for b in elements:
            sums[(a + b) % p] += 1
    return sum(v * v for v in sums.values())


# ============================================================================
# Valeurs triviales (en Z)
# ============================================================================

def E4_trivial(m):
    """E₄^{triv} = 2m² - m (quasi-Sidon, Théorème 3)."""
    return 2 * m * m - m


def E8_trivial_Z(m):
    """E₈^{triv} en Z : toutes les solutions permutations (Lemme 9).

    Pour chaque multiset de taille 4 issu de {0,...,m-1}, le nombre
    de paires ordonnées (a, b) où b est permutation de a est
    [4!/prod(n_i!)]² où n_i sont les multiplicités.

    Types de multisets et contributions :
    - {a,b,c,d} (4 distincts) : C(m,4) × (4!)² = C(m,4) × 576
    - {a,a,b,c} (1 paire)    : m×C(m-1,2) × (4!/2!)² = m(m-1)(m-2)/2 × 144
    - {a,a,b,b} (2 paires)   : C(m,2) × (4!/(2!2!))² = C(m,2) × 36
    - {a,a,a,b} (triple)     : m(m-1) × (4!/3!)² = m(m-1) × 16
    - {a,a,a,a} (quadruple)  : m × 1² = m
    """
    t1 = 576 * math.comb(m, 4)           # 4 distincts
    t2 = 144 * m * (m - 1) * (m - 2) // 2  # 1 paire
    t3 = 36 * math.comb(m, 2)            # 2 paires
    t4 = 16 * m * (m - 1)                # triple
    t5 = m                                # quadruple
    return t1 + t2 + t3 + t4 + t5


def E6_trivial_Z(m):
    """E₆^{triv} en Z : toutes les solutions permutations.

    Types de multisets de taille 3 :
    - {a,b,c} (3 distincts) : C(m,3) × (3!)² = C(m,3) × 36
    - {a,a,b} (1 paire)     : m(m-1) × (3!/2!)² = m(m-1) × 9
    - {a,a,a} (triple)      : m × 1² = m
    """
    t1 = 36 * math.comb(m, 3)
    t2 = 9 * m * (m - 1)
    t3 = m
    return t1 + t2 + t3


# ============================================================================
# Borne Weyl ordre 2
# ============================================================================

def weyl_bound_order2(E8, m, k):
    """Borne Weyl : |μ̂_k(t)|² ≤ (E₈/m⁸)^{k/4} (simplifié).

    Plus précisément, pour la marche de Riesz :
      |μ̂_k(t)| ≤ (E₈/m⁸)^{k/8}

    Le mixing requiert que pour le pire t ≠ 0 :
      (p-1) × |μ̂_k(t)| < 0.041 (seuil Condition Q)
    """
    if E8 <= 0 or m <= 0:
        return None
    ratio = E8 / (m ** 8)
    # |μ̂_k(t)| ≤ ratio^{k/8}
    if ratio >= 1:
        return ratio  # Pas de décroissance
    log_bound = (k / 8.0) * math.log(ratio)
    return math.exp(log_bound)


# ============================================================================
# Anti-régression
# ============================================================================

def anti_regression():
    """Vérifications sur cas connus."""
    # Mersenne M7 : p = 127, m = 7
    p, m = 127, 7
    res = compute_energies_fft(p, m)

    # E₄(H) = 2×49 - 7 = 91
    E4_expected = E4_trivial(m)  # 91
    E4_brute = compute_E4_brute(p, m)
    assert abs(res['E4'] - E4_expected) < 1.0, \
        f"E₄ FFT = {res['E4']:.1f}, attendu {E4_expected}"
    assert E4_brute == E4_expected, \
        f"E₄ brute = {E4_brute}, attendu {E4_expected}"

    # E₈^{triv_Z} = full permutation count including repeated indices
    E8_triv = E8_trivial_Z(m)  # 36715 for m=7
    assert E8_triv == 36715, f"E₈ trivial(7) = {E8_triv}, attendu 36715"
    # E₈ mod p ≥ E₈^{triv_Z} (corrections modulaires ajoutent des solutions)
    assert res['E8'] >= E8_triv - 1, \
        f"E₈ FFT = {res['E8']:.1f} < E₈ triv = {E8_triv}"
    # Pour p=127 petit, les corrections modulaires sont significatives (attendu ≈ 1.6×)
    print(f"  E₈(127, m=7) = {res['E8']:.0f}, triv_Z = {E8_triv}, "
          f"ratio = {res['E8']/E8_triv:.4f}")

    # Parseval
    assert res['parseval_err'] < 1e-10, \
        f"Parseval err = {res['parseval_err']:.2e}"

    # ρ ≈ 0.618
    assert abs(res['rho'] - 0.618) < 0.01, \
        f"ρ(127,7) = {res['rho']:.4f}, attendu ≈ 0.618"

    # Cross-validation E₄ FFT vs brute pour M13 = 8191
    p2, m2 = 8191, 13
    res2 = compute_energies_fft(p2, m2)
    E4_brute2 = compute_E4_brute(p2, m2)
    E4_triv2 = E4_trivial(m2)  # 2×169 - 13 = 325
    assert abs(res2['E4'] - E4_brute2) < 1.0, \
        f"E₄ cross-val failed: FFT={res2['E4']:.1f}, brute={E4_brute2}"
    assert E4_brute2 == E4_triv2, \
        f"E₄ brute(8191) = {E4_brute2}, attendu {E4_triv2}"

    return True


# ============================================================================
# Analyse d'un premier p
# ============================================================================

def analyze_prime(p, m, k, verbose=True):
    """Analyse complète de E_r(H) pour H = ⟨2⟩ mod p."""
    if p > MAX_FFT_SIZE:
        if verbose:
            print(f"    SKIP p={p:,} (> MAX_FFT={MAX_FFT_SIZE:,})")
        return None

    t0 = time.time()
    res = compute_energies_fft(p, m)
    t_fft = time.time() - t0

    E4_obs = res['E4']
    E6_obs = res['E6']
    E8_obs = res['E8']

    E4_triv = E4_trivial(m)
    E6_triv = E6_trivial_Z(m)
    E8_triv = E8_trivial_Z(m)

    # Ratios (corrections modulaires)
    r4 = E4_obs / E4_triv if E4_triv > 0 else float('inf')
    r6 = E6_obs / E6_triv if E6_triv > 0 else float('inf')
    r8 = E8_obs / E8_triv if E8_triv > 0 else float('inf')

    # Borne Weyl
    weyl = weyl_bound_order2(E8_obs, m, k)

    if verbose:
        print(f"    p={p:>10,}  m={m:>5}  ρ={res['rho']:.4f}  "
              f"Parseval={res['parseval_err']:.1e}  [{t_fft:.2f}s]")
        print(f"      E₄={E4_obs:>14.0f}  triv={E4_triv:>14}  ratio={r4:.6f}")
        print(f"      E₆={E6_obs:>14.0f}  triv={E6_triv:>14}  ratio={r6:.6f}")
        print(f"      E₈={E8_obs:>14.0f}  triv={E8_triv:>14}  ratio={r8:.6f}")
        if weyl is not None:
            print(f"      Weyl(k={k}): |μ̂|≤{weyl:.3e}  "
                  f"(p-1)·|μ̂|={(p-1)*weyl:.3e}")

    return {
        'p': p, 'm': m, 'k': k,
        'E4': E4_obs, 'E6': E6_obs, 'E8': E8_obs,
        'E4_triv': E4_triv, 'E6_triv': E6_triv, 'E8_triv': E8_triv,
        'r4': r4, 'r6': r6, 'r8': r8,
        'rho': res['rho'], 'parseval_err': res['parseval_err'],
        'weyl': weyl,
    }


# ============================================================================
# Main
# ============================================================================

def main():
    t_global = time.time()

    print("=" * 72)
    print("PHASE B1 — ESTIMATION NUMÉRIQUE E₈(H) mod p")
    print("Programme de Fermeture du Gap Collatz")
    print(f"Date : {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"Config : MAX_FFT={MAX_FFT_SIZE:,}, TRIAL_BOUND={TRIAL_BOUND:,}")
    print("=" * 72)

    # Anti-régression
    print("\n─── Anti-régression ───")
    t0 = time.time()
    anti_regression()
    print(f"  ✓ Tous les contrôles passés [{time.time()-t0:.2f}s]")

    # Analyse par k
    all_results = []

    for k in K_VALUES:
        S = ceil_log2_3_exact(k)
        d = (1 << S) - pow(3, k)

        print(f"\n{'─'*72}")
        print(f"k = {k}, S = {S}, d(k) = [{len(str(d))} digits]")
        print(f"{'─'*72}")

        if d <= 1:
            print("  d(k) trop petit, skip")
            continue

        # Factoriser d(k)
        factors, cofactor = trial_factor(d)

        # Collecter les premiers avec leur ord₂
        primes_to_test = []
        for p_val, e in factors:
            if p_val <= MAX_FFT_SIZE:
                m = mult_ord(2, p_val)
                if m > 0:
                    primes_to_test.append((p_val, m))

        # Ajouter cofacteur si premier et petit
        if cofactor > 1 and cofactor <= MAX_FFT_SIZE and is_probably_prime(cofactor):
            m_cof = mult_ord(2, cofactor)
            if m_cof > 0:
                primes_to_test.append((cofactor, m_cof))

        if not primes_to_test:
            print(f"  Aucun premier ≤ {MAX_FFT_SIZE:,} trouvé, skip")
            continue

        print(f"  {len(primes_to_test)} premiers à analyser")

        for p_val, m in primes_to_test:
            result = analyze_prime(p_val, m, k)
            if result is not None:
                all_results.append(result)

    # ── Synthèse ──
    print(f"\n{'='*72}")
    print("SYNTHÈSE PHASE B1")
    print(f"{'='*72}")

    if not all_results:
        print("  Aucun résultat.")
        return

    # Tableau condensé
    print(f"\n  {'k':>3} {'p':>10} {'m':>5} {'ρ':>7} "
          f"{'E₄/triv':>8} {'E₆/triv':>8} {'E₈/triv':>8} "
          f"{'Weyl':>10} {'(p-1)·W':>10}")
    print("  " + "-" * 85)

    for r in all_results:
        weyl_str = f"{r['weyl']:.2e}" if r['weyl'] is not None else "N/A"
        pw_str = f"{(r['p']-1)*r['weyl']:.2e}" if r['weyl'] is not None else "N/A"
        print(f"  {r['k']:>3} {r['p']:>10,} {r['m']:>5} {r['rho']:>7.4f} "
              f"{r['r4']:>8.4f} {r['r6']:>8.4f} {r['r8']:>8.4f} "
              f"{weyl_str:>10} {pw_str:>10}")

    # Statistiques des ratios
    r4_vals = [r['r4'] for r in all_results]
    r6_vals = [r['r6'] for r in all_results]
    r8_vals = [r['r8'] for r in all_results]

    print(f"\n  Ratios E_r^{{obs}} / E_r^{{triv}} :")
    print(f"    E₄ : min={min(r4_vals):.6f}, max={max(r4_vals):.6f}, "
          f"mean={np.mean(r4_vals):.6f}")
    print(f"    E₆ : min={min(r6_vals):.6f}, max={max(r6_vals):.6f}, "
          f"mean={np.mean(r6_vals):.6f}")
    print(f"    E₈ : min={min(r8_vals):.6f}, max={max(r8_vals):.6f}, "
          f"mean={np.mean(r8_vals):.6f}")

    # Analyse du mixing
    print(f"\n  ── Analyse mixing ──")
    for r in all_results:
        if r['weyl'] is not None:
            pw = (r['p'] - 1) * r['weyl']
            status = "PASS" if pw < 0.041 else "FAIL"
            print(f"    k={r['k']:>2} p={r['p']:>10,}: "
                  f"(p-1)·|μ̂| = {pw:.3e} → {status}")

    # Conclusion
    n_pass = sum(1 for r in all_results
                 if r['weyl'] is not None and (r['p']-1)*r['weyl'] < 0.041)
    n_fail = sum(1 for r in all_results
                 if r['weyl'] is not None and (r['p']-1)*r['weyl'] >= 0.041)
    n_na = sum(1 for r in all_results if r['weyl'] is None)

    print(f"\n  Mixing (Weyl ordre 2) : {n_pass} PASS, {n_fail} FAIL, {n_na} N/A")

    # Vérification anti-hallucination : Parseval
    max_parseval = max(r['parseval_err'] for r in all_results)
    print(f"\n  Parseval max erreur : {max_parseval:.2e}")
    assert max_parseval < 1e-8, f"Parseval ÉCHEC: {max_parseval}"
    print(f"  ✓ Parseval OK pour tous les cas")

    # E₄ ratio ≈ 1.000 confirme quasi-Sidon
    close_to_1 = all(abs(r['r4'] - 1.0) < 0.1 for r in all_results)
    print(f"  {'✓' if close_to_1 else '⚠️'} E₄/triv ≈ 1.000 : "
          f"{'quasi-Sidon confirmé' if close_to_1 else 'DÉVIATION DÉTECTÉE'}")

    t_total = time.time() - t_global
    print(f"\nTemps total : {t_total:.1f}s")

    print(f"\n{'='*72}")
    print("FIN PHASE B1")
    print(f"{'='*72}")


if __name__ == '__main__':
    main()
