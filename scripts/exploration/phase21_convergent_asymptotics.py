#!/usr/bin/env python3
"""phase21_convergent_asymptotics.py — Asymptotique C/d aux convergents.

Question : Pour les convergents q_n de log₂3, C(S-1,k-1)/d(k) → 0 ?
Si oui, à quelle vitesse ? C'est la clé pour la preuve de l'Hypothèse H.

Rappel :
  - Convergents p_n/q_n de log₂3 : 1/1, 2/1, 3/2, 8/5, 19/12, 65/41, 84/53, 485/306, ...
  - Pour k = q_n : S = ⌈q_n · log₂3⌉, et d = 2^S - 3^{q_n} est petit
  - C = C(S-1, k-1)
  - Si C/d < 1, le modèle Poisson prédit N₀ = 0 avec probabilité 1-C/d

Auteur : Eric Merle (assisté par Claude)
Date : 28 février 2026
"""

import math
from decimal import Decimal, getcontext
import time

getcontext().prec = 100  # 100 digits de précision

# ═══════════════════════════════════════════════════════════════════════
# Section 0 : Fractions continues de log₂3
# ═══════════════════════════════════════════════════════════════════════

def continued_fraction_log2_3(n_terms: int = 30):
    """Calcule la fraction continue de log₂3 par l'algorithme standard.

    log₂3 = [1; 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55, 1, 4, 3, 1, 1, ...]

    Retourne les convergents p_n/q_n.
    """
    # Haute précision pour log₂3
    from decimal import Decimal, getcontext
    getcontext().prec = 100

    # log₂3 = ln3/ln2
    # Calculer par série de Taylor ? Non, utilisons mpmath si dispo, sinon float
    try:
        import mpmath
        mpmath.mp.dps = 80
        log2_3 = mpmath.log(3) / mpmath.log(2)
        x = Decimal(str(log2_3))
    except ImportError:
        x = Decimal('1.5849625007211561814537389439478165286367982874940899517691172240')

    # Algorithme de fraction continue
    cf = []
    convergents = []  # (p_n, q_n)

    p_prev, p_curr = 0, 1
    q_prev, q_curr = 1, 0

    for i in range(n_terms):
        a_n = int(x)
        cf.append(a_n)

        # Mise à jour des convergents
        p_new = a_n * p_curr + p_prev
        q_new = a_n * q_curr + q_prev

        convergents.append((int(p_new), int(q_new)))

        p_prev, p_curr = p_curr, p_new
        q_prev, q_curr = q_curr, q_new

        # Partie fractionnaire
        frac = x - a_n
        if frac == 0:
            break
        x = 1 / frac

    return cf, convergents


# ═══════════════════════════════════════════════════════════════════════
# Section 1 : Calcul exact de C/d pour les convergents
# ═══════════════════════════════════════════════════════════════════════

def compute_C_over_d_exact(k: int) -> dict:
    """Calcule C/d exactement (ou en haute précision) pour un k donné."""
    S = math.ceil(k * math.log2(3))

    # d = 2^S - 3^k (arithmétique exacte Python)
    d = (1 << S) - (3 ** k)

    # C = C(S-1, k-1)
    C = math.comb(S - 1, k - 1)

    # log₂ pour les grandes valeurs
    log2_C = sum(math.log2(S - 1 - i) - math.log2(i + 1) for i in range(k - 1)) if k > 1 else 0
    log2_d = math.log2(d) if d > 0 else float('-inf')

    C_over_d = C / d if d > 0 else float('inf')

    return {
        'k': k, 'S': S, 'd': d, 'C': C,
        'log2_C': log2_C, 'log2_d': log2_d,
        'log2_C_over_d': log2_C - log2_d if d > 0 else float('inf'),
        'C_over_d': C_over_d,
        'gamma': S - k * math.log2(3),  # déficit entropique
    }


# ═══════════════════════════════════════════════════════════════════════
# Section 2 : Borne théorique sur C/d
# ═══════════════════════════════════════════════════════════════════════

def theoretical_bound_C_over_d(k: int, S: int) -> dict:
    """Borne théorique sur C/d par Stirling + analyse du déficit.

    C = C(S-1, k-1) ≈ 2^{(S-1)·H₂((k-1)/(S-1))} / √(2π(S-1)·f·(1-f))
    où f = (k-1)/(S-1) et H₂ est l'entropie binaire.

    d = 2^S - 3^k = 3^k · (2^{S-k·log₂3} - 1) ≈ 3^k · γ · ln2
    où γ = S - k·log₂3 est le déficit entropique.

    Donc log₂(C/d) ≈ (S-1)·H₂(f) - k·log₂3 - log₂(γ·ln2) + ...
    """
    f = (k - 1) / (S - 1) if S > 1 else 0.5
    H2_f = -f * math.log2(f) - (1 - f) * math.log2(1 - f) if 0 < f < 1 else 0

    gamma = S - k * math.log2(3)  # déficit entropique

    # Composantes
    log2_C_stirling = (S - 1) * H2_f - 0.5 * math.log2(2 * math.pi * (S - 1) * f * (1 - f))
    log2_d_approx = k * math.log2(3) + math.log2(max(1e-100, (2**gamma - 1)))

    log2_ratio = log2_C_stirling - log2_d_approx

    # Le terme dominant : (S-1)·H₂(f) - S
    # = (S-1)·H₂(f) - S = S·(H₂(f) - 1) - H₂(f) + correction
    # Puisque H₂(f) < 1 pour f ≠ 1/2, le terme dominant est NÉGATIF
    deficit_H2 = H2_f - 1  # toujours ≤ 0
    dominant_term = S * deficit_H2

    return {
        'f': f,
        'H2_f': H2_f,
        'gamma': gamma,
        'log2_C_stirling': log2_C_stirling,
        'log2_d_approx': log2_d_approx,
        'log2_ratio_approx': log2_ratio,
        'deficit_H2': deficit_H2,
        'dominant_term': dominant_term,
        'decay_rate_per_k': deficit_H2 * math.log2(3),  # ≈ -0.075 par unité de k
    }


# ═══════════════════════════════════════════════════════════════════════
# Section 3 : Programme principal
# ═══════════════════════════════════════════════════════════════════════

def main():
    t0 = time.time()

    print("=" * 82)
    print("Phase 21e — Asymptotique C/d aux Convergents de log₂3")
    print("Programme Merle — Projet Collatz-Junction-Theorem")
    print("=" * 82)

    # ──────────────────────────────────────────
    # S0 : Fractions continues de log₂3
    # ──────────────────────────────────────────
    print(f"\n{'─' * 82}")
    print("S0. Fractions continues de log₂3")
    print(f"{'─' * 82}")

    cf, convergents = continued_fraction_log2_3(25)
    print(f"\n  log₂3 = [{cf[0]}; {', '.join(str(a) for a in cf[1:])}]")
    print(f"\n  {'n':>3} {'p_n':>8} {'q_n':>8} {'p/q':>14} {'erreur':>14} {'conv?':>6}")
    print(f"  {'─'*3} {'─'*8} {'─'*8} {'─'*14} {'─'*14} {'─'*6}")

    log2_3_exact = math.log2(3)
    for i, (p_n, q_n) in enumerate(convergents[:15]):
        ratio = p_n / q_n
        err = ratio - log2_3_exact
        # Vérifie si k=q_n est un convergent qui rend d petit
        S = math.ceil(q_n * log2_3_exact)
        d = (1 << S) - 3**q_n if q_n <= 300 else None
        conv = "★" if d is not None and abs(d) < 3**q_n * 0.01 else ""
        print(f"  {i:3d} {p_n:8d} {q_n:8d} {ratio:14.10f} {err:+14.2e} {conv:>6}")

    # ──────────────────────────────────────────
    # S1 : C/d exact pour tous les k ≤ 68
    # ──────────────────────────────────────────
    print(f"\n{'─' * 82}")
    print("S1. C/d exact pour k = 2..68 (seuil Junction Theorem)")
    print(f"{'─' * 82}")

    # Identifier les convergents
    convergent_ks = set(q for _, q in convergents[:15] if q <= 68)

    print(f"\n  {'k':>3} {'S':>3} {'γ':>8} {'log₂C':>10} {'log₂d':>10} "
          f"{'log₂(C/d)':>10} {'C/d':>12} {'★':>2}")
    print(f"  {'─'*3} {'─'*3} {'─'*8} {'─'*10} {'─'*10} {'─'*10} {'─'*12} {'─'*2}")

    hard_cases = []
    for k in range(2, 69):
        result = compute_C_over_d_exact(k)
        marker = "★" if k in convergent_ks else ""

        if result['C_over_d'] > 0.5:
            hard_cases.append(result)

        # Limiter l'affichage
        if k <= 25 or k in convergent_ks or result['C_over_d'] > 0.5 or k == 68:
            print(f"  {k:3d} {result['S']:3d} {result['gamma']:8.5f} "
                  f"{result['log2_C']:10.3f} {result['log2_d']:10.3f} "
                  f"{result['log2_C_over_d']:10.3f} "
                  f"{result['C_over_d']:12.6f} {marker:>2}")

    # ──────────────────────────────────────────
    # S2 : Focus sur les cas difficiles (C/d > 0.5)
    # ──────────────────────────────────────────
    print(f"\n{'─' * 82}")
    print("S2. Cas difficiles : C/d > 0.5")
    print(f"{'─' * 82}")

    print(f"\n  {'k':>3} {'C/d':>12} {'γ':>8} {'d':>15} {'convergent?':>12}")
    print(f"  {'─'*3} {'─'*12} {'─'*8} {'─'*15} {'─'*12}")

    for r in sorted(hard_cases, key=lambda x: -x['C_over_d']):
        marker = "q_n ★" if r['k'] in convergent_ks else ""
        print(f"  {r['k']:3d} {r['C_over_d']:12.6f} {r['gamma']:8.5f} "
              f"{r['d']:15,d} {marker:>12}")

    # ──────────────────────────────────────────
    # S3 : Extrapolation aux grands convergents
    # ──────────────────────────────────────────
    print(f"\n{'─' * 82}")
    print("S3. C/d pour les grands convergents (q_n > 68)")
    print(f"{'─' * 82}")

    print(f"\n  Convergents de log₂3 avec q_n > 68 :")
    print(f"  {'n':>3} {'q_n':>8} {'S':>8} {'γ':>10} {'log₂(C/d)':>12} {'C/d':>15}")
    print(f"  {'─'*3} {'─'*8} {'─'*8} {'─'*10} {'─'*12} {'─'*15}")

    for i, (p_n, q_n) in enumerate(convergents[:15]):
        if q_n <= 68:
            continue

        k = q_n
        S = math.ceil(k * log2_3_exact)
        gamma = S - k * log2_3_exact

        # log₂C par Stirling
        if k > 1 and S > k:
            f_val = (k - 1) / (S - 1)
            H2 = -f_val * math.log2(f_val) - (1 - f_val) * math.log2(1 - f_val)
            log2_C = (S - 1) * H2 - 0.5 * math.log2(2 * math.pi * (S - 1) * f_val * (1 - f_val))
        else:
            log2_C = 0

        # log₂d : d = 2^S - 3^k = 3^k·(2^γ - 1) ≈ 3^k·γ·ln2
        # log₂d ≈ k·log₂3 + log₂(2^γ - 1)
        two_gamma = 2**gamma
        log2_d = k * log2_3_exact + math.log2(two_gamma - 1) if two_gamma > 1 else float('-inf')

        log2_ratio = log2_C - log2_d
        C_over_d_approx = 2**log2_ratio if log2_ratio < 100 else float('inf')

        print(f"  {i:3d} {q_n:8d} {S:8d} {gamma:10.6f} {log2_ratio:12.3f} "
              f"{C_over_d_approx:15.6e}")

    # ──────────────────────────────────────────
    # S4 : Taux de décroissance asymptotique
    # ──────────────────────────────────────────
    print(f"\n{'─' * 82}")
    print("S4. Taux de decroissance asymptotique de C/d")
    print(f"{'─' * 82}")

    # Estimation théorique
    f_inf = 1 / math.log2(3)  # → 0.63093
    H2_inf = -f_inf * math.log2(f_inf) - (1 - f_inf) * math.log2(1 - f_inf)
    deficit = H2_inf - 1  # H₂(f∞) - 1 < 0

    # log₂(C/d) ≈ S·(H₂(f) - 1) - log₂(γ·ln2) + corrections
    # ≈ k·log₂3·deficit - log₂(γ·ln2) + O(log k)
    rate_per_k = math.log2(3) * deficit

    print(f"""
  Paramètres asymptotiques :
    f∞ = 1/log₂3 = {f_inf:.6f}
    H₂(f∞) = {H2_inf:.6f}
    H₂(f∞) - 1 = {deficit:.6f}  (DEFICIT D'ENTROPIE BINAIRE)

  Taux de décroissance :
    log₂(C/d) ≈ {rate_per_k:.4f} · k + O(log k)

  Donc C/d ≈ 2^{{{rate_per_k:.4f}·k}} = {2**rate_per_k:.6f}^k

  Pour k ≥ K₀ : C/d < 2^{{{rate_per_k:.4f}·K₀}} < 1
  Il suffit que K₀ > {math.ceil(-1/rate_per_k)} (pour C/d < 1/2)
""")

    # Vérification numérique du taux
    print(f"  Verification numerique du taux de decroissance :")
    print(f"  {'k':>3} {'log₂(C/d)':>12} {'predict':>12} {'erreur':>10}")
    print(f"  {'─'*3} {'─'*12} {'─'*12} {'─'*10}")

    for k in range(5, 69, 5):
        result = compute_C_over_d_exact(k)
        predicted = rate_per_k * k  # sans terme logarithmique
        error = result['log2_C_over_d'] - predicted
        print(f"  {k:3d} {result['log2_C_over_d']:12.3f} {predicted:12.3f} {error:+10.3f}")

    # ──────────────────────────────────────────
    # S5 : Synthèse pour la preuve
    # ──────────────────────────────────────────
    print(f"\n{'=' * 82}")
    print("SYNTHESE — STRATEGIE DE PREUVE POUR L'HYPOTHESE H")
    print(f"{'=' * 82}")

    # Trouver K₀ tel que C/d < 0.5 pour tout k > K₀
    K0 = 2
    for k in range(2, 69):
        result = compute_C_over_d_exact(k)
        if result['C_over_d'] >= 0.5:
            K0 = k

    print(f"""
  RESULTATS CLES :

  1. TAUX DE DECROISSANCE : log₂(C/d) ≈ {rate_per_k:.4f} · k
     → C/d décroît EXPONENTIELLEMENT avec k (facteur {2**rate_per_k:.4f} par unité de k)
     → C'est le DEFICIT D'ENTROPIE BINAIRE : H₂(1/log₂3) - 1 = {deficit:.6f}

  2. SEUIL : Dernier k avec C/d ≥ 0.5 : k = {K0}

  3. CAS DIFFICILES (C/d > 1) :""")

    for r in sorted(hard_cases, key=lambda x: -x['C_over_d']):
        if r['C_over_d'] > 1:
            marker = " ★ CONVERGENT" if r['k'] in convergent_ks else ""
            print(f"     k = {r['k']}: C/d = {r['C_over_d']:.4f}{marker}")

    print(f"""
  4. STRATEGIE DE PREUVE :

     ETAPE 1 : Pour k = 2, ..., 68 : vérification par calcul.
               (Déjà réalisé — 81 théorèmes Lean, Phase 19)

     ETAPE 2 : Pour k > 68 :
               Prouver que C/d < 2^{{{rate_per_k:.4f} · 68}} = {2**(rate_per_k*68):.6f}
               C'est une borne sur les coefficients binomiaux vs l'écart 2^S - 3^k.

     ETAPE 3 : Déduire N₀ = 0 de C/d < 1.
               Argument : si C < d, il y a plus de classes de résidus que
               de compositions, donc au moins une classe (et possiblement 0)
               est vide. MAIS ce n'est pas suffisant — il faut prouver que
               c'est SPECIFIQUEMENT la classe 0 qui est vide.

     ETAPE 3 bis : Argument de STRUCTURE.
               corrSum(A) = Σ 3^{{k-1-i}} · 2^{{Aᵢ}} ≥ 3^{{k-1}} (car 2^{{A₀}} ≥ 1)
               corrSum(A) ≡ 0 mod d ⟺ corrSum(A) = m·d pour m ∈ N
               Or corrSum(A) ∈ [cs_min, cs_max] avec cs_min ≥ 3^{{k-1}}
               Et d = 2^S - 3^k > 3^{{k-1}} pour k ≥ 3 (car d > 3^{{k-1}})
               Donc m ≥ 1, et corrSum(A) ≥ d > 3^{{k-1}}
               Le nombre de multiples de d dans [cs_min, cs_max] est ≤ cs_max/d ≈ C·??

     OBSTACLE CENTRAL :
               C/d < 1 ne garantit PAS N₀ = 0 formellement.
               Le lien manquant est : la DISTRIBUTION de corrSum mod d
               est-elle assez uniforme pour exclure la concentration sur 0 ?
""")

    elapsed = time.time() - t0
    print(f"Temps d'execution : {elapsed:.1f}s")
    print(f"{'=' * 82}")


if __name__ == "__main__":
    main()
