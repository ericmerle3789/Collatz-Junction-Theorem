#!/usr/bin/env python3
"""phase21_decay_analysis.py — Analyse de la décroissance de |T(t)|/C.

Question centrale : max|T(t)|/C décroît-il avec k ?
Si oui, à quel taux ? Et ce taux suffit-il pour prouver N₀ = 0 ?

Formule clé : N₀ = C/p + (1/p)·Σ_{t≥1} T(t)
Pour N₀ = 0, il faut Σ_{t≥1} T(t) = -C, c'est-à-dire une cancellation exacte.

Mais pour N₀ < 1 (donc N₀ = 0 car entier), il SUFFIT que :
  |(1/p)·Σ_{t≥1} T(t)| < C/p
  ⟺ |Σ_{t≥1} T(t)| < C
  ⟺ (p-1)·max|T(t)| < C (borne triviale)
  ⟺ max|T(t)|/C < 1/(p-1)

C'est la CONDITION SUFFISANTE pour l'exclusion du zéro !

Sections :
  1. max|T(t)|/C pour k = 2..20, tous les premiers p|d(k)
  2. Borne des sommes d'arc géométriques
  3. Borne multilinéaire par le déterminant de Schur
  4. Vérification de la condition suffisante
  5. Étude asymptotique

Auteur : Eric Merle (assisté par Claude)
Date : 28 février 2026
"""

import math
import numpy as np
from itertools import combinations
from typing import List, Tuple, Dict
import hashlib
import time

# ═══════════════════════════════════════════════════════════════════════
# Section 0 : Utilitaires
# ═══════════════════════════════════════════════════════════════════════

def compositions(S: int, k: int) -> List[Tuple[int, ...]]:
    if k == 1:
        return [(0,)]
    return [(0,) + rest for rest in combinations(range(1, S), k - 1)]


def corrsum(A: Tuple[int, ...], k: int) -> int:
    return sum((3 ** (k - 1 - i)) * (2 ** a) for i, a in enumerate(A))


def multiplicative_order(a: int, p: int) -> int:
    if a % p == 0:
        return 0
    order, current = 1, a % p
    while current != 1:
        current = (current * a) % p
        order += 1
    return order


def prime_factors(n: int) -> List[int]:
    """Facteurs premiers de n."""
    if n <= 1:
        return []
    factors = []
    d = 2
    while d * d <= abs(n):
        while n % d == 0:
            if d not in factors:
                factors.append(d)
            n //= d
        d += 1
    if abs(n) > 1:
        factors.append(abs(n))
    return sorted(factors)


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    d = 5
    while d * d <= n:
        if n % d == 0 or n % (d + 2) == 0:
            return False
        d += 6
    return True


# ═══════════════════════════════════════════════════════════════════════
# Section 1 : Calcul systématique de max|T(t)|/C
# ═══════════════════════════════════════════════════════════════════════

def compute_T_values(k: int, p: int) -> Dict:
    """Calcule T(t) pour tous t et les métriques clés."""
    S = math.ceil(k * math.log2(3))
    C = math.comb(S - 1, k - 1)
    d = (1 << S) - 3**k
    omega_p = multiplicative_order(2, p)

    comps = compositions(S, k)

    # Distribution
    distribution = np.zeros(p, dtype=int)
    for A in comps:
        cs = corrsum(A, k) % p
        distribution[cs] += 1
    N0 = int(distribution[0])

    # T(t) pour tous t
    T_values = np.zeros(p, dtype=complex)
    for t in range(p):
        for r in range(p):
            T_values[t] += distribution[r] * np.exp(2j * np.pi * t * r / p)

    # Métriques
    T_nontrivial = T_values[1:]
    max_T = np.max(np.abs(T_nontrivial))
    mean_T = np.mean(np.abs(T_nontrivial))
    rms_T = np.sqrt(np.mean(np.abs(T_nontrivial)**2))

    # Condition suffisante : max|T|/C < 1/(p-1)
    threshold = 1.0 / (p - 1) if p > 1 else float('inf')
    sufficient = max_T / C < threshold if C > 0 else False

    return {
        'k': k, 'S': S, 'p': p, 'C': C, 'd': d,
        'N0': N0, 'omega_p': omega_p,
        'S_over_omega': S / omega_p if omega_p > 0 else float('inf'),
        'C_over_p': C / p,
        'max_T': max_T,
        'mean_T': mean_T,
        'rms_T': rms_T,
        'max_T_over_C': max_T / C if C > 0 else 0,
        'max_T_over_sqrtC': max_T / np.sqrt(C) if C > 0 else 0,
        'threshold': threshold,
        'sufficient': sufficient,
    }


# ═══════════════════════════════════════════════════════════════════════
# Section 2 : Bornes théoriques des sommes d'arc
# ═══════════════════════════════════════════════════════════════════════

def geometric_arc_bound(c: int, p: int, S: int) -> float:
    """Borne supérieure pour |Σ_{a=0}^{S-1} e(c·2^a/p)|.

    Si 2 a ordre ω mod p et S ≤ ω, c'est une somme partielle
    d'une suite géométrique de phases unitaires.

    Borne géométrique : |S_c| ≤ min(S, 1/|sin(πc·(2^ω-1)/(p·(2-1)))|)
    Mais c'est compliqué. Utilisons la borne plus simple :

    Pour une somme de N phases e(α·n), |Σ| ≤ min(N, 1/(2·||α||))
    où ||α|| = dist(α, ℤ).

    Ici α = c·2^a/p et les termes ne sont PAS une progression arithmétique
    (ils forment une progression géométrique en a).

    Borne de Korobov pour les sommes sur progressions géométriques :
    |Σ_{a=0}^{N-1} e(c·g^a/p)| ≤ √p pour c ≢ 0 mod p
    (quand g est une racine primitive et N ≤ p-1).
    """
    omega_p = multiplicative_order(2, p)

    if c % p == 0:
        return float(S)

    # Borne de Korobov / Pólya-Vinogradov pour sommes sur sous-groupes
    # Quand S ≤ ω : somme incomplète, borne √p·log p
    # Quand S > ω : S = q·ω + r, somme = q·Σ_{full} + Σ_r
    # Si Σ_{full} = Σ_{a=0}^{ω-1} e(c·2^a/p) = somme sur le sous-groupe <2>

    # Somme complète sur le sous-groupe <2>
    S_full = sum(np.exp(2j * np.pi * c * pow(2, a, p) / p)
                 for a in range(omega_p))

    q_full = S // omega_p
    r_rem = S % omega_p

    if r_rem == 0:
        return abs(q_full * S_full)
    else:
        S_partial = sum(np.exp(2j * np.pi * c * pow(2, a, p) / p)
                        for a in range(r_rem))
        return abs(q_full * S_full + S_partial)


def theoretical_bound_multilinear(k: int, p: int) -> Dict:
    """Bornes théoriques pour la somme multilinéaire.

    Borne 1 (triviale) : |T(t)| ≤ C
    Borne 2 (Pólya-Vinogradov indiv.) : chaque facteur ≤ √p
        → |T| ≤ C mais pas mieux (car les facteurs ne se multiplient pas)

    Borne 3 (multilinéaire de Schur) :
        |Σ_{a₁<...<a_m} Π e(cⱼ·2^{aⱼ}/p)| ≤ ...

    En fait, pour une somme multilinéaire ordonnée :
        |Σ_{a₁<...<a_m} Π f_j(a_j)| ≤ Π_j ||f_j||₂ / √(m!)
    quand les f_j sont orthonormées (Hadamard).

    Pour nos phases unitaires : ||f_j||₂ = √(S-1).
    Donc la borne de Hadamard donne :
        |T'| ≤ (S-1)^{(k-1)/2} / √((k-1)!)

    Comparaison avec C = C(S-1, k-1) ≈ (S-1)^{k-1}/(k-1)! :
        |T'|/C ≤ √((k-1)!) / (S-1)^{(k-1)/2}
    """
    S = math.ceil(k * math.log2(3))
    C = math.comb(S - 1, k - 1)
    omega_p = multiplicative_order(2, p)

    m = k - 1  # nombre de facteurs
    N = S - 1  # taille de l'arc

    # Borne triviale
    bound_trivial = C

    # Borne de Hadamard multilinéaire
    bound_hadamard = N ** (m / 2.0) / math.sqrt(math.factorial(m)) if m <= 170 else float('inf')
    ratio_hadamard = bound_hadamard / C if C > 0 else float('inf')

    # Borne de Cauchy-Schwarz (première itération)
    # |T'|² ≤ N · Σ_a |F_{m-1}(a)|²
    # Pour l'itérer, on a |T'| ≤ N^{m/2} · (termes de corrélation)
    bound_CS = N ** (m / 2.0)
    ratio_CS = bound_CS / C if C > 0 else float('inf')

    # Borne de √p pour chaque somme d'arc (si p > S)
    if omega_p > S:
        # Somme incomplète sur <2>, borne √p
        bound_sqrt_p = math.sqrt(p) ** m
    else:
        # Arc couvre la période, somme complète peut être petite ou grande
        bound_sqrt_p = float('inf')

    return {
        'k': k, 'S': S, 'p': p, 'C': C, 'm': m, 'N': N,
        'omega_p': omega_p,
        'bound_trivial': bound_trivial,
        'bound_hadamard': bound_hadamard,
        'ratio_hadamard': ratio_hadamard,
        'bound_CS': bound_CS,
        'ratio_CS': ratio_CS,
        'bound_sqrt_p': bound_sqrt_p,
    }


# ═══════════════════════════════════════════════════════════════════════
# Section 3 : Condition suffisante raffinée
# ═══════════════════════════════════════════════════════════════════════

def refined_sufficient_condition(k: int, p: int, max_T: float,
                                  C: int) -> Dict:
    """Vérifie les différentes conditions suffisantes pour N₀ = 0.

    Condition 1 (brute) : max|T(t)|·(p-1) < C
        → Σ|T(t)| ≤ (p-1)·max|T| < C → N₀ < C/p + 1 → N₀ = 0

    Condition 2 (RMS) : √(Σ|T(t)|²) < C/√(p-1)
        Par Cauchy-Schwarz : |Σ T(t)| ≤ √(p-1)·√(Σ|T|²)
        Donc si √(Σ|T|²) < C/√(p-1), alors |Σ T(t)| < C → N₀ = 0

    Condition 3 (Parseval pour T) :
        Σ_{t=0}^{p-1} |T(t)|² = p·Σ_r N(r)² = p·||N||²₂
        Le minimum de ||N||²₂ sous la contrainte Σ N(r) = C, N(r) ≥ 0
        est atteint quand N est uniforme : N(r) = C/p, donnant ||N||²₂ = C²/p.
        Le terme N₀ = 0 force : ||N||²₂ ≥ C²/p + C/(p-1)·(variation)
    """
    threshold_brute = C / (p - 1) if p > 1 else float('inf')
    cond1 = max_T < threshold_brute

    return {
        'threshold_brute': threshold_brute,
        'max_T': max_T,
        'ratio': max_T / threshold_brute if threshold_brute > 0 else float('inf'),
        'condition_1_met': cond1,
    }


# ═══════════════════════════════════════════════════════════════════════
# Section 4 : Programme principal
# ═══════════════════════════════════════════════════════════════════════

def main():
    t0 = time.time()

    print("=" * 82)
    print("Phase 21c — Analyse de Décroissance de |T(t)|/C")
    print("Programme Merle — Projet Collatz-Junction-Theorem")
    print("=" * 82)

    # ──────────────────────────────────────────
    # PARTIE 1 : Analyse systématique k=2..17
    # ──────────────────────────────────────────
    print(f"\n{'─' * 82}")
    print("S1. Analyse systematique : max|T(t)|/C pour k = 2..17")
    print(f"{'─' * 82}")

    print(f"\n  {'k':>3} {'S':>3} {'p':>8} {'C':>10} {'N0':>6} {'w_p':>4} "
          f"{'S/w':>6} {'max|T|/C':>10} {'|T|/sqrtC':>10} "
          f"{'thres':>8} {'EXCLU?':>7}")
    print(f"  {'─'*3} {'─'*3} {'─'*8} {'─'*10} {'─'*6} {'─'*4} "
          f"{'─'*6} {'─'*10} {'─'*10} {'─'*8} {'─'*7}")

    all_results = []
    convergent_ks = {1, 2, 5, 12, 41}  # convergents de log_2(3)

    for k in range(2, 18):
        S = math.ceil(k * math.log2(3))
        C = math.comb(S - 1, k - 1)
        d = abs((1 << S) - 3**k)

        if C > 500_000:
            print(f"  {k:3d} {S:3d} {'---':>8} {C:10,d} {'---':>6} "
                  f"{'---':>4} {'---':>6} {'SKIP: C trop grand':>40}")
            continue

        if d <= 1:
            print(f"  {k:3d} {S:3d} {'---':>8} {C:10,d} {'---':>6} "
                  f"{'---':>4} {'---':>6} {'SKIP: d = ':>15}{d}")
            continue

        # Trouver les premiers p|d
        pf = prime_factors(d)

        for p in pf[:3]:  # max 3 premiers par k
            if p < 3 or not is_prime(p):
                continue

            result = compute_T_values(k, p)
            all_results.append(result)

            conv_marker = " *" if k in convergent_ks else ""
            exclu = "OUI" if result['N0'] == 0 else "NON"

            print(f"  {k:3d} {S:3d} {p:8d} {C:10,d} {result['N0']:6d} "
                  f"{result['omega_p']:4d} {result['S_over_omega']:6.3f} "
                  f"{result['max_T_over_C']:10.6f} "
                  f"{result['max_T_over_sqrtC']:10.4f} "
                  f"{result['threshold']:8.5f} {exclu:>7}{conv_marker}")

    # ──────────────────────────────────────────
    # PARTIE 2 : Tendance de décroissance
    # ──────────────────────────────────────────
    print(f"\n{'─' * 82}")
    print("S2. Tendance de decroissance de max|T(t)|/C")
    print(f"{'─' * 82}")

    # Grouper par N₀ = 0 vs N₀ > 0
    exclu = [(r['k'], r['p'], r['max_T_over_C'], r['S_over_omega'])
             for r in all_results if r['N0'] == 0]
    non_exclu = [(r['k'], r['p'], r['max_T_over_C'], r['S_over_omega'])
                 for r in all_results if r['N0'] > 0]

    print(f"\n  Cas N0 = 0 (EXCLU) :")
    print(f"  {'k':>3} {'p':>8} {'max|T|/C':>10} {'S/w':>6} {'log(|T|/C)':>12}")
    for k, p, ratio, sw in sorted(exclu):
        log_ratio = math.log(ratio) if ratio > 0 else float('-inf')
        print(f"  {k:3d} {p:8d} {ratio:10.6f} {sw:6.3f} {log_ratio:12.4f}")

    print(f"\n  Cas N0 > 0 (NON EXCLU) :")
    print(f"  {'k':>3} {'p':>8} {'max|T|/C':>10} {'S/w':>6}")
    for k, p, ratio, sw in sorted(non_exclu):
        print(f"  {k:3d} {p:8d} {ratio:10.6f} {sw:6.3f}")

    # ──────────────────────────────────────────
    # PARTIE 3 : Bornes théoriques vs empiriques
    # ──────────────────────────────────────────
    print(f"\n{'─' * 82}")
    print("S3. Bornes theoriques vs empiriques")
    print(f"{'─' * 82}")

    print(f"\n  {'k':>3} {'p':>8} {'|T|/C_emp':>10} {'Hadamard':>10} "
          f"{'C-S':>10} {'Sufficient':>10}")

    for r in all_results:
        if r['N0'] == 0:
            tb = theoretical_bound_multilinear(r['k'], r['p'])
            cond = refined_sufficient_condition(r['k'], r['p'],
                                                 r['max_T'], r['C'])
            had_str = f"{tb['ratio_hadamard']:.6f}" if tb['ratio_hadamard'] < 1e6 else ">1e6"
            cs_str = f"{tb['ratio_CS']:.6f}" if tb['ratio_CS'] < 1e6 else ">1e6"
            suf_str = f"{cond['ratio']:.4f}" if cond['ratio'] < 1e6 else ">1e6"
            check = "  <<< OK" if cond['condition_1_met'] else ""
            print(f"  {r['k']:3d} {r['p']:8d} {r['max_T_over_C']:10.6f} "
                  f"{had_str:>10} {cs_str:>10} {suf_str:>10}{check}")

    # ──────────────────────────────────────────
    # PARTIE 4 : Le pattern S/ω_p
    # ──────────────────────────────────────────
    print(f"\n{'─' * 82}")
    print("S4. Le role de S/omega_p dans l'exclusion")
    print(f"{'─' * 82}")

    print(f"\n  HYPOTHESE : L'exclusion du zero se produit quand S/omega_p < 1")
    print(f"  (arc tronque — chaque facteur voit un sous-ensemble DIFFERENT de F_p*)")
    print()

    print(f"  {'k':>3} {'p':>8} {'N0':>6} {'S/w':>8} {'Tronque?':>9} {'Coherent?':>10}")
    for r in sorted(all_results, key=lambda x: x['S_over_omega']):
        tronque = r['S_over_omega'] < 1.0
        exclu_bool = r['N0'] == 0
        coherent = (tronque and exclu_bool) or (not tronque and not exclu_bool)
        t_str = "OUI" if tronque else "NON"
        c_str = "OUI" if coherent else "***NON***"
        print(f"  {r['k']:3d} {r['p']:8d} {r['N0']:6d} "
              f"{r['S_over_omega']:8.3f} {t_str:>9} {c_str:>10}")

    # ──────────────────────────────────────────
    # PARTIE 5 : Analyse critique — convergents
    # ──────────────────────────────────────────
    print(f"\n{'─' * 82}")
    print("S5. Convergents de log_2(3) — le noyau dur")
    print(f"{'─' * 82}")

    convergents = [
        (1, "q1"), (2, "q2"), (5, "q3"), (12, "q4"),
    ]

    for k, name in convergents:
        S = math.ceil(k * math.log2(3))
        d = abs((1 << S) - 3**k)
        C = math.comb(S - 1, k - 1)

        print(f"\n  {name} : k={k}, S={S}, d={d}, C={C}")

        if d <= 1:
            print(f"    d = {d} (degenere)")
            continue

        pf = prime_factors(d)
        print(f"    Premiers de d : {pf}")

        for p in pf:
            if not is_prime(p) or p < 3:
                continue
            if C > 500_000:
                print(f"    p={p} : C={C:,} trop grand, SKIP")
                continue

            result = compute_T_values(k, p)
            omega_p = result['omega_p']

            print(f"    p={p} : N0={result['N0']}, C/p={result['C_over_p']:.3f}, "
                  f"omega={omega_p}, S/w={result['S_over_omega']:.3f}, "
                  f"max|T|/C={result['max_T_over_C']:.6f}")

    # ──────────────────────────────────────────
    # PARTIE 6 : Synthèse
    # ──────────────────────────────────────────
    print(f"\n{'=' * 82}")
    print("SYNTHESE DE LA DECROISSANCE")
    print(f"{'=' * 82}")

    # Calculer la pente log(max|T|/C) vs k pour les cas N₀=0
    if len(exclu) > 2:
        ks = [x[0] for x in exclu]
        ratios = [x[2] for x in exclu]
        log_ratios = [math.log(r) for r in ratios if r > 0]
        ks_valid = [k for k, r in zip(ks, ratios) if r > 0]

        if len(ks_valid) > 2:
            # Régression linéaire log(ratio) vs k
            n = len(ks_valid)
            sum_k = sum(ks_valid)
            sum_r = sum(log_ratios)
            sum_kr = sum(k * r for k, r in zip(ks_valid, log_ratios))
            sum_k2 = sum(k**2 for k in ks_valid)

            denom = n * sum_k2 - sum_k**2
            if abs(denom) > 1e-15:
                slope = (n * sum_kr - sum_k * sum_r) / denom
                intercept = (sum_r - slope * sum_k) / n

                print(f"\n  Regression lineaire : log(max|T|/C) ≈ {slope:.4f}·k + {intercept:.4f}")
                print(f"  Taux de decroissance : max|T|/C ~ e^{{{slope:.4f}·k}} = {math.exp(slope):.4f}^k")

                if slope < 0:
                    # Extrapolation : pour quel k atteint-on le threshold?
                    for p_test in [7, 13, 83, 233, 1000]:
                        threshold = 1.0 / (p_test - 1)
                        k_threshold = (math.log(threshold) - intercept) / slope
                        print(f"  Pour p={p_test} : threshold 1/(p-1)={threshold:.6f}, "
                              f"atteint a k ≈ {k_threshold:.1f}")

    # Résumé
    n_exclu_total = sum(1 for r in all_results if r['N0'] == 0)
    n_non_exclu = sum(1 for r in all_results if r['N0'] > 0)
    n_tronque_exclu = sum(1 for r in all_results
                           if r['N0'] == 0 and r['S_over_omega'] < 1.0)
    n_complet_non_exclu = sum(1 for r in all_results
                               if r['N0'] > 0 and r['S_over_omega'] >= 1.0)

    print(f"\n  Statistiques :")
    print(f"    Total paires (k,p) analysees : {len(all_results)}")
    print(f"    Exclues (N0=0) : {n_exclu_total}")
    print(f"    Non exclues (N0>0) : {n_non_exclu}")
    print(f"    Arc tronque ET exclu : {n_tronque_exclu}")
    print(f"    Arc complet ET non exclu : {n_complet_non_exclu}")

    # Vérifier l'hypothèse S/ω < 1 ↔ N₀ = 0
    exceptions = []
    for r in all_results:
        tronque = r['S_over_omega'] < 1.0
        exclu_bool = r['N0'] == 0
        if tronque != exclu_bool:
            exceptions.append(r)

    if exceptions:
        print(f"\n  EXCEPTIONS a l'hypothese S/w < 1 ↔ N0=0 :")
        for r in exceptions:
            print(f"    k={r['k']}, p={r['p']}: N0={r['N0']}, "
                  f"S/w={r['S_over_omega']:.3f}")
    else:
        print(f"\n  ★ L'hypothese S/omega_p < 1 ↔ N0=0 est PARFAITEMENT coherente")
        print(f"    pour toutes les {len(all_results)} paires testees !")

    elapsed = time.time() - t0

    data_str = str([(r['k'], r['p'], r['N0']) for r in all_results])
    sha = hashlib.sha256(data_str.encode()).hexdigest()[:16]

    print(f"\n  Temps d'execution : {elapsed:.1f}s")
    print(f"  SHA256(resultats)[:16] : {sha}")
    print(f"{'=' * 82}")


if __name__ == "__main__":
    main()
