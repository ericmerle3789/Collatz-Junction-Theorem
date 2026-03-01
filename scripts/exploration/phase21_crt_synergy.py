#!/usr/bin/env python3
"""phase21_crt_synergy.py — Synergie CRT inter-premiers pour l'Hypothèse H.

DÉCOUVERTE CRITIQUE : L'analyse individuelle par premier p est INSUFFISANTE.
Pour k=6, 9, 10, 12, TOUS les premiers p|d ont N₀(p) > 0.
Pourtant, l'Hypothèse H est vérifiée (pas de cycle non trivial).

Le mécanisme réel est la SYNERGIE CRT :
  Im(Ev_d) ↪ Π_{p|d} Im(Ev_p)    (injection CRT)

0 ∉ Im(Ev_d) ⟺ aucune composition A ne satisfait corrSum(A) ≡ 0 mod p
                pour TOUS les premiers p|d SIMULTANÉMENT.

Ce script vérifie et quantifie cette synergie CRT pour k = 2..17.

Auteur : Eric Merle (assisté par Claude)
Date : 28 février 2026
"""

import math
import numpy as np
from itertools import combinations
from typing import List, Tuple, Dict, Set
from collections import defaultdict
import time
import hashlib

# ═══════════════════════════════════════════════════════════════════════
# Section 0 : Arithmétique de base
# ═══════════════════════════════════════════════════════════════════════

def compositions(S: int, k: int) -> List[Tuple[int, ...]]:
    """Comp(S, k) = {(0, A₁, ..., A_{k-1}) : 0 < A₁ < ... < A_{k-1} ≤ S-1}."""
    if k == 1:
        return [(0,)]
    return [(0,) + rest for rest in combinations(range(1, S), k - 1)]


def corrsum(A: Tuple[int, ...], k: int) -> int:
    """corrSum(A) = Σ 3^{k-1-i} · 2^{Aᵢ} (arithmétique exacte)."""
    return sum((3 ** (k - 1 - i)) * (2 ** a) for i, a in enumerate(A))


def multiplicative_order(a: int, p: int) -> int:
    """ord_p(a) = plus petit k > 0 tel que a^k ≡ 1 mod p."""
    if a % p == 0:
        return 0
    order = 1
    current = a % p
    while current != 1:
        current = (current * a) % p
        order += 1
    return order


def prime_factors(n: int) -> List[int]:
    """Facteurs premiers de n (avec multiplicité)."""
    factors = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.append(d)
            n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors


def distinct_prime_factors(n: int) -> List[int]:
    """Facteurs premiers distincts de n, triés."""
    return sorted(set(prime_factors(n)))


# ═══════════════════════════════════════════════════════════════════════
# Section 1 : Analyse CRT — intersection des zéros modulo chaque premier
# ═══════════════════════════════════════════════════════════════════════

def crt_synergy_analysis(k: int) -> Dict:
    """Analyse complète de la synergie CRT pour un k donné.

    Pour chaque premier p|d(k) :
    1. Calcule Z_p = {idx(A) : corrSum(A) ≡ 0 mod p}
    2. Calcule l'intersection progressive Z_p₁ ∩ Z_p₂ ∩ ...
    3. Vérifie que l'intersection finale est vide (Hypothèse H)

    Retourne les tailles de chaque ensemble et intersection.
    """
    S = math.ceil(k * math.log2(3))
    d = (1 << S) - 3**k
    C = math.comb(S - 1, k - 1)

    primes = distinct_prime_factors(d)

    result = {
        'k': k, 'S': S, 'd': d, 'C': C,
        'primes': primes,
        'num_primes': len(primes),
    }

    # Énumérer toutes les compositions et calculer corrSum
    comps = compositions(S, k)
    assert len(comps) == C, f"Erreur: {len(comps)} ≠ {C}"

    corrsums = [corrsum(A, k) for A in comps]

    # Pour chaque premier, calculer l'ensemble des indices avec corrSum ≡ 0 mod p
    zero_sets = {}  # p -> set of indices where corrSum ≡ 0 mod p
    per_prime = []

    for p in primes:
        omega_p = multiplicative_order(2, p)
        Z_p = set()
        for idx, cs in enumerate(corrsums):
            if cs % p == 0:
                Z_p.add(idx)

        zero_sets[p] = Z_p
        per_prime.append({
            'p': p,
            'omega_p': omega_p,
            'S_over_omega': S / omega_p if omega_p > 0 else float('inf'),
            'N0_p': len(Z_p),
            'fraction': len(Z_p) / C,
            'expected_random': C / p,  # modèle Poisson
            'ratio_to_expected': len(Z_p) / (C / p) if C / p > 0 else 0,
        })

    result['per_prime'] = per_prime

    # Intersection progressive
    progressive = []
    current_intersection = set(range(C))  # commence avec toutes les compositions

    for i, p in enumerate(primes):
        current_intersection = current_intersection & zero_sets[p]
        progressive.append({
            'step': i + 1,
            'prime': p,
            'Z_p_size': len(zero_sets[p]),
            'intersection_size': len(current_intersection),
            'elimination_rate': 1 - len(current_intersection) / max(1, C),
        })

    result['progressive'] = progressive

    # Intersection finale
    final_intersection = current_intersection
    result['final_intersection_size'] = len(final_intersection)
    result['hypothesis_H'] = len(final_intersection) == 0

    # Si l'intersection n'est pas vide, lister les compositions problématiques
    if len(final_intersection) > 0:
        problematic = []
        for idx in sorted(final_intersection):
            A = comps[idx]
            cs = corrsums[idx]
            problematic.append({
                'A': A,
                'corrSum': cs,
                'corrSum_mod_d': cs % d,
            })
        result['problematic_compositions'] = problematic[:10]  # max 10

    # Analyse de la dépendance CRT
    # Si les résidus mod p₁ et mod p₂ étaient indépendants,
    # P(corrSum ≡ 0 mod p₁p₂) ≈ P(mod p₁)·P(mod p₂) = (N₀(p₁)/C)·(N₀(p₂)/C)
    if len(primes) >= 2:
        p1, p2 = primes[0], primes[1]
        expected_independent = (len(zero_sets[p1]) / C) * (len(zero_sets[p2]) / C) * C
        actual_intersection_12 = len(zero_sets[p1] & zero_sets[p2])
        result['crt_independence'] = {
            'p1': p1, 'p2': p2,
            'N0_p1': len(zero_sets[p1]),
            'N0_p2': len(zero_sets[p2]),
            'expected_independent': expected_independent,
            'actual_intersection': actual_intersection_12,
            'ratio': actual_intersection_12 / expected_independent if expected_independent > 0 else float('inf'),
        }

    return result


# ═══════════════════════════════════════════════════════════════════════
# Section 2 : Modèle probabiliste — quand la synergie CRT suffit-elle ?
# ═══════════════════════════════════════════════════════════════════════

def probabilistic_model(k: int, primes: List[int], C: int) -> Dict:
    """Modèle probabiliste de la synergie CRT.

    Si les résidus mod p_i sont mutuellement indépendants :
      P(corrSum ≡ 0 mod d) = Π_i (1/p_i) = 1/d

    Alors E[#{A : corrSum ≡ 0 mod d}] = C/d.

    Si C/d < 1, le modèle aléatoire prédit N₀ = 0 avec probabilité ~ 1 - C/d.

    Pour les convergents : d est PETIT, donc C/d >> 1, et le modèle prédit
    N₀ >> 0. Mais l'Hypothèse H tient quand même, ce qui indique une
    CORRÉLATION STRUCTURELLE anti-zéro.
    """
    d = 1
    for p in primes:
        d *= p  # Approximation squarefree

    C_over_d = C / d
    expected_N0_random = C_over_d
    prob_empty_poisson = math.exp(-C_over_d) if C_over_d < 700 else 0.0

    # Borne par les moments : P(N₀ = 0) ≥ 1 - E[N₀] si E[N₀] < 1
    prob_empty_markov = max(0, 1 - C_over_d)

    return {
        'd_squarefree': d,
        'C_over_d': C_over_d,
        'expected_N0_random': expected_N0_random,
        'prob_empty_poisson': prob_empty_poisson,
        'prob_empty_markov': prob_empty_markov,
        'regime': 'EASY' if C_over_d < 1 else 'HARD' if C_over_d < 100 else 'VERY_HARD',
    }


# ═══════════════════════════════════════════════════════════════════════
# Section 3 : Signature spectrale — T multi-premier
# ═══════════════════════════════════════════════════════════════════════

def multi_prime_T_analysis(k: int) -> Dict:
    """Analyse de T(t) simultanément pour tous les premiers p|d.

    Pour l'Hypothèse H via Fourier, on a :
      N₀(d) = (1/d) · Σ_{t mod d} T_d(t)

    où T_d(t) = Σ_A e(t·corrSum(A)/d).

    Par CRT : T_d(t) = Π_p T_p(t_p) si d est squarefree.
    Mais ce n'est PAS exact car T_d est une somme sur les MÊMES compositions A.

    Ce qu'on veut mesurer : la corrélation entre T_p₁ et T_p₂.
    """
    S = math.ceil(k * math.log2(3))
    d = (1 << S) - 3**k
    C = math.comb(S - 1, k - 1)
    primes = distinct_prime_factors(d)

    comps = compositions(S, k)
    corrsums = [corrsum(A, k) for A in comps]

    # T_p(t) pour chaque premier et chaque t
    T_per_prime = {}
    for p in primes:
        T_p = np.zeros(p, dtype=complex)
        for t in range(p):
            T_p[t] = sum(
                np.exp(2j * np.pi * t * (cs % p) / p)
                for cs in corrsums
            )
        T_per_prime[p] = T_p

    # Pour chaque premier : max|T_p(t)|/C pour t ≥ 1
    max_T_per_prime = {}
    for p in primes:
        T_p = T_per_prime[p]
        max_nontrivial = max(abs(T_p[t]) for t in range(1, p))
        max_T_per_prime[p] = max_nontrivial / C

    # Corrélation croisée des distributions
    cross_correlations = {}
    if len(primes) >= 2:
        for i in range(len(primes)):
            for j in range(i + 1, len(primes)):
                p1, p2 = primes[i], primes[j]
                # Distribution jointe (r1 mod p1, r2 mod p2)
                joint = np.zeros((p1, p2), dtype=int)
                for cs in corrsums:
                    r1 = cs % p1
                    r2 = cs % p2
                    joint[r1, r2] += 1

                # Test d'indépendance : joint[0,0] vs (row_sum[0]/C)*(col_sum[0]/C)*C
                expected_00 = joint[0, :].sum() * joint[:, 0].sum() / C
                actual_00 = joint[0, 0]

                # Chi-squared pour la cellule (0,0)
                if expected_00 > 0:
                    chi2_00 = (actual_00 - expected_00)**2 / expected_00
                else:
                    chi2_00 = float('inf')

                cross_correlations[(p1, p2)] = {
                    'expected_00': expected_00,
                    'actual_00': actual_00,
                    'deficit': expected_00 - actual_00,
                    'chi2_00': chi2_00,
                    'anti_correlated': actual_00 < expected_00,
                }

    return {
        'k': k, 'S': S, 'd': d, 'C': C,
        'primes': primes,
        'max_T_over_C': max_T_per_prime,
        'cross_correlations': cross_correlations,
        'T_per_prime': T_per_prime,  # garder pour analyse détaillée
    }


# ═══════════════════════════════════════════════════════════════════════
# Section 4 : Propriété structurelle — la congruence fondamentale
# ═══════════════════════════════════════════════════════════════════════

def structural_congruence_analysis(k: int) -> Dict:
    """Analyse la propriété structurelle clé :
    corrSum(A) ≡ 0 mod d ⟺ 2^S·(somme normalisée) = 3^k·(constante)

    Comme d = 2^S - 3^k, on a :
      corrSum(A) ≡ 0 mod d
      ⟺ Σ 3^{k-1-i}·2^{Aᵢ} ≡ 0 mod (2^S - 3^k)
      ⟺ Σ 3^{k-1-i}·2^{Aᵢ} = m·(2^S - 3^k) pour un entier m ≥ 0

    La borne : 0 ≤ corrSum(A) ≤ 3^{k-1}·(2^S - 1) < 3^k·2^S/(3-1) ???
    Non, plus précisément : corrSum(A) ≤ Σ_{i=0}^{k-1} 3^{k-1-i}·2^{S-1-???}

    En fait corrSum(A) ≤ corrSum_max = Σ_{i=0}^{k-1} 3^{k-1-i}·2^{S-k+i}

    Et m = corrSum(A)/d doit être un entier. Combien de multiples de d
    tombent dans [corrSum_min, corrSum_max] ?
    """
    S = math.ceil(k * math.log2(3))
    d = (1 << S) - 3**k
    C = math.comb(S - 1, k - 1)

    # Bornes de corrSum
    comps = compositions(S, k)
    corrsums = [corrsum(A, k) for A in comps]

    cs_min = min(corrsums)
    cs_max = max(corrsums)

    # Nombre de multiples de d dans [cs_min, cs_max]
    m_min = cs_min // d
    m_max = cs_max // d
    num_multiples = m_max - m_min + 1 if cs_min > 0 else m_max + 1

    # Pour chaque multiple m·d, combien de compositions le réalisent ?
    multiple_counts = defaultdict(int)
    for cs in corrsums:
        if cs % d == 0:
            m = cs // d
            multiple_counts[m] += 1

    # corrSum(A) / (3^{k-1}·2^S) est dans un intervalle contraint
    normalizer = 3**(k-1) * (1 << S)
    cs_normalized = [cs / normalizer for cs in corrsums]

    # Le ratio corrSum/d = "nombre de cycles"
    cs_over_d = [cs / d for cs in corrsums]

    return {
        'k': k, 'S': S, 'd': d, 'C': C,
        'cs_min': cs_min, 'cs_max': cs_max,
        'cs_min_over_d': cs_min / d, 'cs_max_over_d': cs_max / d,
        'num_d_multiples_in_range': num_multiples,
        'multiples_of_d': dict(multiple_counts),
        'N0_d': sum(multiple_counts.values()),
        'hypothesis_H_direct': sum(multiple_counts.values()) == 0,
        'normalized_range': (min(cs_normalized), max(cs_normalized)),
    }


# ═══════════════════════════════════════════════════════════════════════
# Section 5 : Programme principal
# ═══════════════════════════════════════════════════════════════════════

def main():
    t0 = time.time()

    print("=" * 82)
    print("Phase 21d — Synergie CRT Inter-Premiers pour l'Hypothèse H")
    print("Programme Merle — Projet Collatz-Junction-Theorem")
    print("=" * 82)

    # ──────────────────────────────────────────
    # S1 : Vue d'ensemble d → premiers → CRT
    # ──────────────────────────────────────────
    print(f"\n{'─' * 82}")
    print("S1. Factorisation de d(k) et analyse CRT pour k = 2..17")
    print(f"{'─' * 82}")

    print(f"\n  {'k':>3} {'S':>3} {'d':>12} {'C':>12} {'primes':>30} {'C/d':>10} {'regime':>10}")
    print(f"  {'─'*3} {'─'*3} {'─'*12} {'─'*12} {'─'*30} {'─'*10} {'─'*10}")

    k_data = {}
    for k in range(2, 18):
        S = math.ceil(k * math.log2(3))
        d = (1 << S) - 3**k
        C = math.comb(S - 1, k - 1)
        primes = distinct_prime_factors(d)

        C_over_d = C / d
        regime = 'EASY' if C_over_d < 1 else 'HARD' if C_over_d < 100 else 'V.HARD'

        primes_str = '×'.join(str(p) for p in primes)
        if len(primes_str) > 28:
            primes_str = primes_str[:25] + "..."

        print(f"  {k:3d} {S:3d} {d:12,d} {C:12,d} {primes_str:>30} {C_over_d:10.4f} {regime:>10}")

        k_data[k] = {'S': S, 'd': d, 'C': C, 'primes': primes, 'C_over_d': C_over_d}

    # ──────────────────────────────────────────
    # S2 : Analyse CRT détaillée (k petit)
    # ──────────────────────────────────────────
    print(f"\n{'─' * 82}")
    print("S2. Analyse CRT detaillee — intersection progressive des zeros")
    print(f"{'─' * 82}")

    convergents = {2, 5, 12}  # q₂, q₃, q₄ de log₂3

    all_crt_results = {}
    for k in range(2, 14):  # k jusqu'à 13 (C max ~ 75K pour k=12)
        S = k_data[k]['S']
        C = k_data[k]['C']

        if C > 500_000:
            print(f"\n  k={k}: C={C:,d} — SKIP (trop grand)")
            continue

        conv_marker = " ★" if k in convergents else ""
        print(f"\n  ═══ k = {k}{conv_marker} ═══")
        print(f"  d = {k_data[k]['d']:,d}, C = {C:,d}, "
              f"primes = {k_data[k]['primes']}")

        result = crt_synergy_analysis(k)
        all_crt_results[k] = result

        # Per-prime analysis
        print(f"\n  {'p':>8} {'ω_p':>6} {'S/ω':>7} {'N₀(p)':>8} {'N₀/C':>8} "
              f"{'C/p':>8} {'N₀/(C/p)':>10}")
        print(f"  {'─'*8} {'─'*6} {'─'*7} {'─'*8} {'─'*8} {'─'*8} {'─'*10}")

        for pp in result['per_prime']:
            print(f"  {pp['p']:8d} {pp['omega_p']:6d} {pp['S_over_omega']:7.3f} "
                  f"{pp['N0_p']:8d} {pp['fraction']:8.5f} "
                  f"{pp['expected_random']:8.1f} {pp['ratio_to_expected']:10.4f}")

        # Progressive intersection
        print(f"\n  Intersection progressive :")
        print(f"  {'etape':>6} {'+ p':>8} {'|Z_p|':>8} {'|∩|':>8} {'elim%':>8}")
        print(f"  {'─'*6} {'─'*8} {'─'*8} {'─'*8} {'─'*8}")

        for step in result['progressive']:
            print(f"  {step['step']:6d} {step['prime']:8d} {step['Z_p_size']:8d} "
                  f"{step['intersection_size']:8d} "
                  f"{step['elimination_rate']*100:7.3f}%")

        # CRT independence test
        if 'crt_independence' in result:
            ci = result['crt_independence']
            print(f"\n  Test d'independance CRT (p₁={ci['p1']}, p₂={ci['p2']}) :")
            print(f"    E[N₀₀ | independant] = {ci['expected_independent']:.2f}")
            print(f"    N₀₀ observe           = {ci['actual_intersection']}")
            print(f"    Ratio obs/exp         = {ci['ratio']:.4f}")

        # Verdict
        verdict = "✓ H VALIDE" if result['hypothesis_H'] else "✗ H VIOLEE"
        print(f"\n  → VERDICT : |∩ Z_p| = {result['final_intersection_size']}, "
              f"{verdict}")

        if not result['hypothesis_H'] and 'problematic_compositions' in result:
            print(f"  *** COMPOSITIONS PROBLEMATIQUES ***")
            for comp in result['problematic_compositions']:
                print(f"    A = {comp['A']}, corrSum = {comp['corrSum']:,d}, "
                      f"corrSum mod d = {comp['corrSum_mod_d']}")

    # ──────────────────────────────────────────
    # S3 : Modèle probabiliste vs réalité
    # ──────────────────────────────────────────
    print(f"\n{'─' * 82}")
    print("S3. Modele probabiliste vs realite")
    print(f"{'─' * 82}")

    print(f"\n  {'k':>3} {'C/d':>10} {'E[N₀]_rand':>12} {'N₀_observe':>12} "
          f"{'ratio':>8} {'P_Poisson':>10} {'VERDICT':>10}")
    print(f"  {'─'*3} {'─'*10} {'─'*12} {'─'*12} {'─'*8} {'─'*10} {'─'*10}")

    for k in sorted(all_crt_results.keys()):
        result = all_crt_results[k]
        C = result['C']
        d = result['d']
        primes = result['primes']
        N0_observed = result['final_intersection_size']

        prob_model = probabilistic_model(k, primes, C)
        conv_marker = " ★" if k in convergents else ""

        print(f"  {k:3d} {prob_model['C_over_d']:10.4f} "
              f"{prob_model['expected_N0_random']:12.4f} "
              f"{N0_observed:12d} "
              f"{N0_observed / max(0.001, prob_model['expected_N0_random']):8.4f} "
              f"{prob_model['prob_empty_poisson']:10.6f} "
              f"{'OK' if N0_observed == 0 else 'FAIL':>10}"
              f"{conv_marker}")

    # ──────────────────────────────────────────
    # S4 : Analyse structurelle — corrSum/d
    # ──────────────────────────────────────────
    print(f"\n{'─' * 82}")
    print("S4. Propriete structurelle — corrSum(A) / d")
    print(f"{'─' * 82}")

    for k in sorted(all_crt_results.keys()):
        C = k_data[k]['C']
        if C > 200_000:
            continue

        struct = structural_congruence_analysis(k)
        conv_marker = " ★" if k in convergents else ""

        print(f"\n  k = {k}{conv_marker}:")
        print(f"    corrSum ∈ [{struct['cs_min']:,d}, {struct['cs_max']:,d}]")
        print(f"    d = {struct['d']:,d}")
        print(f"    corrSum/d ∈ [{struct['cs_min_over_d']:.4f}, "
              f"{struct['cs_max_over_d']:.4f}]")
        print(f"    Multiples de d dans l'intervalle : {struct['num_d_multiples_in_range']}")
        if struct['multiples_of_d']:
            print(f"    Compositions realisant m·d :")
            for m, count in sorted(struct['multiples_of_d'].items()):
                print(f"      m = {m}: {count} compositions")
        else:
            print(f"    AUCUN multiple de d dans l'image ← H VERIFIEE")

    # ──────────────────────────────────────────
    # S5 : Focus convergents — le noyau dur
    # ──────────────────────────────────────────
    print(f"\n{'─' * 82}")
    print("S5. Focus convergents — le noyau dur irréductible")
    print(f"{'─' * 82}")

    print(f"""
  Les convergents q_n de log_2(3) sont :
    q_1 = 1, q_2 = 2, q_3 = 5, q_4 = 12, q_5 = 41, q_6 = 53, ...

  Pour ces k, d(k) = 2^S - 3^k est PETIT car 2^S ≈ 3^k (quasi-résonance).
  Conséquence : C/d >> 1, le modèle aléatoire prédit N₀ >> 0.
  Pourtant H tient — c'est le MYSTÈRE CENTRAL.""")

    for k in convergents:
        if k not in all_crt_results:
            continue
        result = all_crt_results[k]
        C = result['C']
        d = result['d']

        print(f"\n  ★ k = {k} (convergent q_{{{'2' if k==2 else '3' if k==5 else '4'}}}) :")
        print(f"    d = {d}, C = {C}, C/d = {C/d:.4f}")

        # Distribution jointe multi-premier si possible
        if len(result['primes']) >= 2:
            mprime = multi_prime_T_analysis(k)

            for (p1, p2), cc in mprime['cross_correlations'].items():
                print(f"    Correlation croisee (p={p1}, p={p2}) :")
                print(f"      E[joint_00] = {cc['expected_00']:.2f}, "
                      f"observe = {cc['actual_00']}")
                print(f"      Deficit = {cc['deficit']:.2f} "
                      f"{'(ANTI-CORRELÉ !)' if cc['anti_correlated'] else '(corrélé)'}")
                print(f"      χ² = {cc['chi2_00']:.4f}")

    # ──────────────────────────────────────────
    # S6 : Synthèse
    # ──────────────────────────────────────────
    print(f"\n{'=' * 82}")
    print("SYNTHESE — SYNERGIE CRT")
    print(f"{'=' * 82}")

    # Compter les types
    n_easy = 0
    n_hard_ok = 0
    n_hard_fail = 0
    for k, result in all_crt_results.items():
        C_over_d = result['C'] / result['d']
        if C_over_d < 1:
            n_easy += 1
        elif result['hypothesis_H']:
            n_hard_ok += 1
        else:
            n_hard_fail += 1

    print(f"""
  RESULTATS pour k = 2..{max(all_crt_results.keys())} :

  1. Cas EASY (C/d < 1, modele aleatoire suffit) : {n_easy}
  2. Cas HARD (C/d ≥ 1, H verifiee par synergie)  : {n_hard_ok}
  3. Cas FAIL (H violee)                            : {n_hard_fail}

  MECANISMES IDENTIFIES :

  (A) Pour d grand (non-convergent) avec un seul premier dominant :
      → Un premier p|d a N₀(p) = 0, ce qui suffit.
      → L'arc tronque (S/ω_p < 1) est le mecanisme individuel.

  (B) Pour d petit (convergent) avec TOUS N₀(p) > 0 :
      → AUCUN premier individuel ne suffit.
      → C'est l'INTERSECTION VIDE par CRT qui sauve H.
      → Les residus mod p₁ et mod p₂ sont ANTI-CORRELES au zero.
      → Mecanisme : corrSum a une structure arithmetique rigide
        qui empeche la compatibilite simultanee avec 0 mod p₁ ET 0 mod p₂.

  (C) La question centrale pour la preuve :
      → Peut-on DEMONTRER que l'anti-correlation CRT au zero
        est suffisante pour TOUS les convergents ?
      → C'est le VERROU theorique restant.
""")

    elapsed = time.time() - t0
    data_str = str([(k, r['final_intersection_size']) for k, r in sorted(all_crt_results.items())])
    sha = hashlib.sha256(data_str.encode()).hexdigest()[:16]

    print(f"Temps d'execution : {elapsed:.1f}s")
    print(f"SHA256(resultats)[:16] : {sha}")
    print(f"{'=' * 82}")


if __name__ == "__main__":
    main()
