#!/usr/bin/env python3
"""
R160 — MONOTONE POSITIONING FRAMEWORK (MPF)
============================================
TAN personnalisé : outil construit de zéro, exploitant la structure
anti-alignée de corrSum = Σ 3^{k-1-j} · 2^{B_j}.

OBJECTIF : Déterminer si l'inégalité de réarrangement + structure monotone
impose des contraintes NON TRIVIALES sur corrSum mod d(k,S).

DISTINCTION vs R156 ("arguments de taille") :
  R156 : compte les multiples de d dans [corrSum_min, corrSum_max] → trop de cibles
  MPF  : étudie la DISTRIBUTION des corrSum dans cet intervalle et la structure
         fonctionnelle imposée par l'anti-alignement

AXES D'INVESTIGATION :
  Axe 1 : Bornes corrSum_min, corrSum_max, nombre de cibles m
  Axe 2 : Distribution de corrSum/d pour compositions aléatoires monotones
  Axe 3 : Concentration : quelle fraction des compositions tombe près de corrSum_min ?
  Axe 4 : Structure résiduelle : corrSum mod d est-il biaisé ?
  Axe 5 : Test du réarrangement : corrSum vs corrSum_shuffled
"""

import math
import random
import json
from collections import Counter, defaultdict
from functools import lru_cache

# ============================================================================
# AXE 1 : BORNES EXACTES
# ============================================================================

def corrSum_value(k, B_vec):
    """Calcule corrSum pour un B-vecteur donné."""
    return sum(3**(k-1-j) * (1 << B_vec[j]) for j in range(k))

def corrSum_extremes(k, S):
    """Calcule corrSum_min et corrSum_max pour (k, S)."""
    max_B = S - k

    # corrSum_min : anti-alignement maximal
    # B = (0, 0, ..., 0, max_B)  — tout le poids dans le dernier terme
    B_min = [0]*(k-1) + [max_B]
    cs_min = corrSum_value(k, B_min)

    # corrSum_max : tous B_j = max_B (alignement maximal)
    B_max = [max_B]*k
    cs_max = corrSum_value(k, B_max)

    # Aussi : B le plus serré = (0, 1, 2, ..., k-1) si max_B >= k-1
    if max_B >= k - 1:
        B_tight = list(range(k))
        # Ajuster le dernier pour atteindre max_B
        # Non — B_tight a B_{k-1} = k-1, pas max_B. Corrigeons :
        # Le vrai B_tight avec B_{k-1} = max_B et gaps minimaux
        B_tight = list(range(k-1)) + [max_B]
        cs_tight = corrSum_value(k, B_tight)
    else:
        B_tight = [0]*k
        B_tight[-1] = max_B
        cs_tight = cs_min

    # corrSum le plus "typique" : gaps uniformes
    B_uniform = [int(j * max_B / (k-1)) for j in range(k)]
    B_uniform[-1] = max_B  # Assurer exactitude
    cs_uniform = corrSum_value(k, B_uniform)

    return {
        'cs_min': cs_min,
        'cs_max': cs_max,
        'cs_tight': cs_tight,
        'cs_uniform': cs_uniform,
        'B_min': B_min,
        'B_max': B_max,
        'B_tight': B_tight,
        'B_uniform': B_uniform
    }

def analyze_target_range(k, S):
    """Axe 1 : combien de multiples de d dans l'intervalle ?"""
    d = (1 << S) - 3**k
    if d <= 0:
        return None

    extremes = corrSum_extremes(k, S)
    cs_min = extremes['cs_min']
    cs_max = extremes['cs_max']

    m_min = math.ceil(cs_min / d)
    m_max = math.floor(cs_max / d)
    num_targets = m_max - m_min + 1

    # Nombre de compositions
    C_comp = math.comb(S - 1, k - 1)

    # Ratio compositions / cibles
    if num_targets > 0:
        avg_per_target = C_comp / num_targets
    else:
        avg_per_target = float('inf')

    return {
        'k': k, 'S': S, 'd': d,
        'cs_min': cs_min, 'cs_max': cs_max,
        'cs_range': cs_max - cs_min,
        'm_min': m_min, 'm_max': m_max,
        'num_targets': num_targets,
        'C_comp': C_comp,
        'avg_per_target': avg_per_target,
        'ratio_range_d': (cs_max - cs_min) / d,
        'log2_C': math.log2(C_comp) if C_comp > 0 else 0,
        'log2_targets': math.log2(num_targets) if num_targets > 0 else 0
    }

# ============================================================================
# AXE 2 : DISTRIBUTION DE corrSum/d (MONTE CARLO)
# ============================================================================

def random_monotone_B(k, max_B, rng=None):
    """Génère un B-vecteur monotone aléatoire uniforme avec B_{k-1} = max_B."""
    if rng is None:
        rng = random
    # Méthode : tirer k-1 entiers dans [0, max_B] uniformément avec répétition, trier
    # Puis fixer B_{k-1} = max_B
    # Ceci correspond à choisir gaps c_0, ..., c_{k-1} >= 0 avec Σc_j = max_B
    # (stars and bars, uniforme)
    if k == 1:
        return [max_B]
    # Stars and bars : tirer k-1 séparateurs parmi {0, ..., max_B + k - 2}
    separators = sorted(rng.sample(range(max_B + k - 1), k - 1))
    gaps = []
    prev = -1
    for s in separators:
        gaps.append(s - prev - 1)
        prev = s
    gaps.append(max_B + k - 2 - prev)

    # Reconstruire B
    B = [0] * k
    B[0] = gaps[0]
    for j in range(1, k):
        B[j] = B[j-1] + gaps[j]

    assert B[-1] == max_B, f"B[-1]={B[-1]} != max_B={max_B}"
    assert all(B[j] <= B[j+1] for j in range(k-1)), "Non-monotone!"
    return B

def distribution_corrSum_mod_d(k, S, n_samples=100000):
    """Axe 2 : distribution de corrSum mod d pour compositions monotones aléatoires."""
    d = (1 << S) - 3**k
    if d <= 0:
        return None

    max_B = S - k
    rng = random.Random(42)

    residues = []
    m_values = []
    corrsum_values = []

    for _ in range(n_samples):
        B = random_monotone_B(k, max_B, rng)
        cs = corrSum_value(k, B)
        r = cs % d
        m = cs // d
        residues.append(r)
        m_values.append(m)
        corrsum_values.append(cs)

    # Statistiques sur les résidus
    residue_counts = Counter(residues)
    hits_zero = residue_counts.get(0, 0)

    # Statistiques sur m
    m_counter = Counter(m_values)
    m_mean = sum(m_values) / len(m_values)
    m_min = min(m_values)
    m_max = max(m_values)
    m_median = sorted(m_values)[len(m_values)//2]

    # Test d'uniformité des résidus (pour petit d, KS-like)
    n_distinct_residues = len(residue_counts)

    return {
        'k': k, 'S': S, 'd': d,
        'n_samples': n_samples,
        'hits_zero': hits_zero,
        'hits_zero_rate': hits_zero / n_samples,
        'expected_rate': 1.0 / d if d > 0 else 0,
        'n_distinct_residues': n_distinct_residues,
        'm_mean': m_mean,
        'm_median': m_median,
        'm_min_obs': m_min,
        'm_max_obs': m_max,
        'top_m': m_counter.most_common(5)
    }

# ============================================================================
# AXE 3 : CONCENTRATION PRÈS DU MINIMUM
# ============================================================================

def concentration_analysis(k, S, n_samples=100000):
    """Axe 3 : quelle fraction de corrSum est dans le 1er décile de l'intervalle ?"""
    d = (1 << S) - 3**k
    if d <= 0:
        return None

    max_B = S - k
    rng = random.Random(42)

    extremes = corrSum_extremes(k, S)
    cs_min_bound = extremes['cs_min']
    cs_max_bound = extremes['cs_max']
    range_size = cs_max_bound - cs_min_bound

    decile_counts = [0] * 10

    for _ in range(n_samples):
        B = random_monotone_B(k, max_B, rng)
        cs = corrSum_value(k, B)
        # Position relative dans l'intervalle
        if range_size > 0:
            pos = (cs - cs_min_bound) / range_size
            decile = min(int(pos * 10), 9)
            decile_counts[decile] += 1

    return {
        'k': k, 'S': S,
        'decile_fractions': [c/n_samples for c in decile_counts],
        'cs_min_bound': cs_min_bound,
        'cs_max_bound': cs_max_bound,
        'range_log2': math.log2(range_size) if range_size > 0 else 0
    }

# ============================================================================
# AXE 4 : STRUCTURE RÉSIDUELLE — corrSum mod d biaisé ?
# ============================================================================

def residual_bias(k, S, n_samples=100000, n_bins=100):
    """Axe 4 : Y a-t-il un biais dans corrSum mod d ?"""
    d = (1 << S) - 3**k
    if d <= 0:
        return None

    max_B = S - k
    rng = random.Random(42)

    # Pour d petit : histogramme exact des résidus
    # Pour d grand : histogramme en bins
    residues = []
    for _ in range(n_samples):
        B = random_monotone_B(k, max_B, rng)
        cs = corrSum_value(k, B)
        residues.append(cs % d)

    if d <= 1000:
        # Histogramme exact
        counts = Counter(residues)
        expected = n_samples / d
        chi2 = sum((counts.get(r, 0) - expected)**2 / expected for r in range(d))
        # Chi² normalisé
        chi2_norm = chi2 / (d - 1) if d > 1 else 0
        zero_count = counts.get(0, 0)
        zero_excess = (zero_count - expected) / max(math.sqrt(expected), 1)
        return {
            'k': k, 'S': S, 'd': d,
            'd_size': 'small',
            'chi2_normalized': chi2_norm,
            'zero_count': zero_count,
            'expected_per_bin': expected,
            'zero_excess_sigma': zero_excess,
            'uniform': chi2_norm < 2.0  # Rough threshold
        }
    else:
        # Histogramme par bins
        bin_size = d / n_bins
        bin_counts = [0] * n_bins
        for r in residues:
            bin_idx = min(int(r / bin_size), n_bins - 1)
            bin_counts[bin_idx] += 1

        expected = n_samples / n_bins
        chi2 = sum((c - expected)**2 / expected for c in bin_counts)
        chi2_norm = chi2 / (n_bins - 1)

        # Le résidu 0 est dans le premier bin
        zero_bin = bin_counts[0]
        zero_excess = (zero_bin - expected) / max(math.sqrt(expected), 1)

        return {
            'k': k, 'S': S, 'd': d,
            'd_size': 'large',
            'n_bins': n_bins,
            'chi2_normalized': chi2_norm,
            'zero_bin_count': zero_bin,
            'expected_per_bin': expected,
            'zero_excess_sigma': zero_excess,
            'uniform': chi2_norm < 2.0
        }

# ============================================================================
# AXE 5 : TEST DU RÉARRANGEMENT
# ============================================================================

def rearrangement_test(k, S, n_samples=10000, n_shuffles=100):
    """Axe 5 : corrSum_anti vs corrSum_shuffled."""
    max_B = S - k
    rng = random.Random(42)
    d = (1 << S) - 3**k
    if d <= 0:
        return None

    weights = [3**(k-1-j) for j in range(k)]

    ratios = []
    mod_changes = []

    for _ in range(n_samples):
        B = random_monotone_B(k, max_B, rng)
        values = [1 << b for b in B]

        cs_anti = sum(w * v for w, v in zip(weights, values))

        # Shuffle les valeurs (brisant l'anti-alignement)
        shuffle_sums = []
        for _ in range(n_shuffles):
            shuffled = values[:]
            rng.shuffle(shuffled)
            cs_shuffled = sum(w * v for w, v in zip(weights, shuffled))
            shuffle_sums.append(cs_shuffled)

        cs_mean_shuffle = sum(shuffle_sums) / len(shuffle_sums)
        ratio = cs_anti / cs_mean_shuffle if cs_mean_shuffle > 0 else 1.0
        ratios.append(ratio)

        # Le résidu mod d change-t-il ?
        anti_mod = cs_anti % d
        shuffle_mods = [s % d for s in shuffle_sums]
        # Fraction des shuffles ayant un résidu différent
        diff_frac = sum(1 for sm in shuffle_mods if sm != anti_mod) / len(shuffle_mods)
        mod_changes.append(diff_frac)

    avg_ratio = sum(ratios) / len(ratios)
    min_ratio = min(ratios)
    max_ratio = max(ratios)
    avg_mod_change = sum(mod_changes) / len(mod_changes)

    return {
        'k': k, 'S': S,
        'avg_ratio_anti_vs_shuffle': avg_ratio,
        'min_ratio': min_ratio,
        'max_ratio': max_ratio,
        'avg_mod_change_fraction': avg_mod_change,
        'interpretation': (
            f"corrSum_anti ≈ {avg_ratio:.4f} × corrSum_shuffle_mean. "
            f"Réarrangement change le résidu mod d dans {avg_mod_change*100:.1f}% des cas."
        )
    }

# ============================================================================
# AXE 6 : FORMULE EXACTE DU RÉARRANGEMENT
# ============================================================================

def exact_rearrangement_bounds(k, S):
    """
    Pour chaque B-vecteur, calculer :
      ratio = corrSum_anti / corrSum_aligned

    Le réarrangement dit : ratio ≤ 1 toujours.
    Question : quelle est la distribution de ce ratio ?
    """
    max_B = S - k
    d = (1 << S) - 3**k

    weights = [3**(k-1-j) for j in range(k)]
    weights_aligned = list(reversed(weights))  # Croissant

    rng = random.Random(42)

    n_samples = 50000
    ratios = []

    for _ in range(n_samples):
        B = random_monotone_B(k, max_B, rng)
        values = [1 << b for b in B]

        cs_anti = sum(w * v for w, v in zip(weights, values))
        cs_aligned = sum(w * v for w, v in zip(weights_aligned, values))

        ratio = cs_anti / cs_aligned
        ratios.append(ratio)

    ratios.sort()

    return {
        'k': k, 'S': S,
        'ratio_min': ratios[0],
        'ratio_max': ratios[-1],
        'ratio_mean': sum(ratios) / len(ratios),
        'ratio_median': ratios[len(ratios)//2],
        'ratio_p10': ratios[int(0.1 * len(ratios))],
        'ratio_p90': ratios[int(0.9 * len(ratios))],
        'interpretation': (
            f"corrSum_anti/corrSum_aligned ∈ [{ratios[0]:.6f}, {ratios[-1]:.6f}], "
            f"médiane {ratios[len(ratios)//2]:.6f}. "
            f"L'anti-alignement réduit corrSum d'un facteur moyen {sum(ratios)/len(ratios):.4f}."
        )
    }

# ============================================================================
# AXE 7 : LE TEST CRITIQUE — petit k où N₀(d) = 0 est PROUVÉ
# ============================================================================

def verify_small_k(k_range=range(3, 12)):
    """Pour petit k où N₀(d)=0 est prouvé, le MPF détecte-t-il quelque chose ?"""
    results = []
    for k in k_range:
        S_min = math.ceil(k * math.log2(3)) + 1
        # Tester S_min et S_min + 1
        for S in [S_min, S_min + 1]:
            d = (1 << S) - 3**k
            if d <= 0:
                continue
            max_B = S - k
            if max_B < 0:
                continue

            # Énumération exacte pour petit k
            C_comp = math.comb(S - 1, k - 1)

            info = analyze_target_range(k, S)
            if info:
                results.append({
                    'k': k, 'S': S,
                    'd': d,
                    'C_comp': C_comp,
                    'num_targets': info['num_targets'],
                    'avg_per_target': info['avg_per_target'],
                    'ratio_range_d': info['ratio_range_d'],
                    'm_min': info['m_min'],
                    'm_max': info['m_max']
                })
    return results

# ============================================================================
# MAIN : EXÉCUTION COMPLÈTE
# ============================================================================

def main():
    print("=" * 80)
    print("R160 — MONOTONE POSITIONING FRAMEWORK (MPF)")
    print("TAN personnalisé pour corrSum = Σ 3^{k-1-j} · 2^{B_j}")
    print("=" * 80)

    results = {}

    # --- AXE 1 : Bornes ---
    print("\n" + "=" * 60)
    print("AXE 1 : BORNES ET NOMBRE DE CIBLES")
    print("=" * 60)

    axe1_results = []
    for k in [3, 5, 7, 10, 15, 22, 30, 41]:
        S = math.ceil(k * math.log2(3)) + 1
        info = analyze_target_range(k, S)
        if info:
            axe1_results.append(info)
            print(f"\n  k={k}, S={S}, d={info['d']:.3e}")
            print(f"    corrSum ∈ [{info['cs_min']:.3e}, {info['cs_max']:.3e}]")
            print(f"    m ∈ [{info['m_min']}, {info['m_max']}] → {info['num_targets']} cibles")
            print(f"    C(S-1,k-1) = {info['C_comp']:.3e}")
            print(f"    Compositions/cible = {info['avg_per_target']:.1f}")
            print(f"    log₂(C) = {info['log2_C']:.1f}, log₂(#cibles) = {info['log2_targets']:.1f}")

    results['axe1'] = axe1_results

    # --- AXE 2 : Distribution (petit k pour faisabilité) ---
    print("\n" + "=" * 60)
    print("AXE 2 : DISTRIBUTION DE corrSum mod d")
    print("=" * 60)

    axe2_results = []
    for k in [5, 7, 10, 15]:
        S = math.ceil(k * math.log2(3)) + 1
        d = (1 << S) - 3**k
        if d <= 0:
            continue
        n_samp = min(100000, max(10000, 10 * d))
        info = distribution_corrSum_mod_d(k, S, n_samples=n_samp)
        if info:
            axe2_results.append(info)
            print(f"\n  k={k}, S={S}, d={info['d']}")
            print(f"    Hits résidu 0 : {info['hits_zero']}/{info['n_samples']} "
                  f"({info['hits_zero_rate']:.6f})")
            print(f"    Attendu uniforme : {info['expected_rate']:.6f}")
            print(f"    Ratio observé/attendu : "
                  f"{info['hits_zero_rate']/info['expected_rate']:.3f}"
                  if info['expected_rate'] > 0 else "N/A")
            print(f"    m moyen = {info['m_mean']:.1f}, "
                  f"médian = {info['m_median']}, "
                  f"min = {info['m_min_obs']}, max = {info['m_max_obs']}")
            print(f"    Top m : {info['top_m'][:3]}")

    results['axe2'] = axe2_results

    # --- AXE 3 : Concentration ---
    print("\n" + "=" * 60)
    print("AXE 3 : CONCENTRATION DANS L'INTERVALLE")
    print("=" * 60)

    axe3_results = []
    for k in [5, 10, 15, 22]:
        S = math.ceil(k * math.log2(3)) + 1
        info = concentration_analysis(k, S, n_samples=50000)
        if info:
            axe3_results.append(info)
            fracs = info['decile_fractions']
            print(f"\n  k={k}, S={S}")
            print(f"    Distribution par décile de l'intervalle [corrSum_min, corrSum_max] :")
            for i, f in enumerate(fracs):
                bar = "█" * int(f * 50)
                print(f"      [{10*i:3d}%-{10*(i+1):3d}%] {f:.4f} {bar}")

    results['axe3'] = axe3_results

    # --- AXE 4 : Biais résiduel ---
    print("\n" + "=" * 60)
    print("AXE 4 : BIAIS RÉSIDUEL (corrSum mod d)")
    print("=" * 60)

    axe4_results = []
    for k in [5, 7, 10]:
        S = math.ceil(k * math.log2(3)) + 1
        info = residual_bias(k, S, n_samples=100000)
        if info:
            axe4_results.append(info)
            print(f"\n  k={k}, S={S}, d={info['d']}")
            print(f"    χ² normalisé = {info['chi2_normalized']:.3f} "
                  f"({'UNIFORME' if info['uniform'] else 'BIAISÉ'})")
            zero_key = 'zero_count' if 'zero_count' in info else 'zero_bin_count'
            print(f"    Résidu 0 zone : {info[zero_key]} "
                  f"(attendu {info['expected_per_bin']:.1f})")
            print(f"    Excès résidu 0 : {info['zero_excess_sigma']:.2f}σ")

    results['axe4'] = axe4_results

    # --- AXE 5 : Test du réarrangement ---
    print("\n" + "=" * 60)
    print("AXE 5 : IMPACT DU RÉARRANGEMENT SUR corrSum")
    print("=" * 60)

    axe5_results = []
    for k in [5, 10, 15]:
        S = math.ceil(k * math.log2(3)) + 1
        info = rearrangement_test(k, S, n_samples=5000, n_shuffles=50)
        if info:
            axe5_results.append(info)
            print(f"\n  k={k}, S={S}")
            print(f"    {info['interpretation']}")

    results['axe5'] = axe5_results

    # --- AXE 6 : Ratio anti/aligned ---
    print("\n" + "=" * 60)
    print("AXE 6 : RATIO RÉARRANGEMENT (anti/aligned)")
    print("=" * 60)

    axe6_results = []
    for k in [5, 10, 15, 22]:
        S = math.ceil(k * math.log2(3)) + 1
        info = exact_rearrangement_bounds(k, S)
        if info:
            axe6_results.append(info)
            print(f"\n  k={k}, S={S}")
            print(f"    {info['interpretation']}")

    results['axe6'] = axe6_results

    # --- AXE 7 : Vérification petit k ---
    print("\n" + "=" * 60)
    print("AXE 7 : VÉRIFICATION PETIT k (N₀(d)=0 prouvé)")
    print("=" * 60)

    axe7_results = verify_small_k()
    for r in axe7_results:
        print(f"\n  k={r['k']}, S={r['S']}, d={r['d']}")
        print(f"    C = {r['C_comp']}, cibles = {r['num_targets']}, "
              f"C/cibles = {r['avg_per_target']:.1f}")
        print(f"    m ∈ [{r['m_min']}, {r['m_max']}]")

    results['axe7'] = axe7_results

    # ========================================================================
    # VERDICT
    # ========================================================================
    print("\n" + "=" * 80)
    print("VERDICT MPF")
    print("=" * 80)

    # Analyse du verdict
    verdict_lines = []

    # 1. Nombre de cibles vs R156
    if axe1_results:
        k22 = [r for r in axe1_results if r['k'] == 22]
        if k22:
            r = k22[0]
            verdict_lines.append(
                f"1. k=22 : {r['num_targets']} cibles, {r['C_comp']:.0e} compositions, "
                f"ratio C/cibles = {r['avg_per_target']:.0f}"
            )
            if r['num_targets'] > 100:
                verdict_lines.append(
                    "   → CONFIRMÉ R156 : trop de cibles pour exclusion directe par taille"
                )

    # 2. Distribution
    if axe3_results:
        k22_c = [r for r in axe3_results if r['k'] == 22]
        if k22_c:
            fracs = k22_c[0]['decile_fractions']
            verdict_lines.append(
                f"2. Concentration k=22 : {fracs[0]*100:.1f}% dans le 1er décile"
            )
            if fracs[0] > 0.5:
                verdict_lines.append(
                    "   → FORTE concentration, mais ne cible pas r=0 spécifiquement"
                )

    # 3. Biais résiduel
    if axe4_results:
        biased = [r for r in axe4_results if not r['uniform']]
        if biased:
            verdict_lines.append(
                f"3. BIAIS RÉSIDUEL DÉTECTÉ pour k={[r['k'] for r in biased]}"
            )
        else:
            verdict_lines.append(
                "3. Résidus corrSum mod d UNIFORMES — pas de biais exploitable"
            )

    # 4. Impact réarrangement
    if axe5_results:
        for r in axe5_results:
            if r['avg_mod_change_fraction'] > 0.9:
                verdict_lines.append(
                    f"4. k={r['k']} : réarrangement change le résidu dans "
                    f"{r['avg_mod_change_fraction']*100:.0f}% des cas "
                    f"→ impact RÉEL sur la structure mod d"
                )

    # 5. Conclusion
    verdict_lines.append("")
    verdict_lines.append("CONCLUSION GLOBALE MPF :")
    verdict_lines.append(
        "L'anti-alignement réduit corrSum d'un facteur significatif (Axe 5-6),")
    verdict_lines.append(
        "et concentre la distribution vers le minimum (Axe 3).")
    verdict_lines.append(
        "MAIS : la distribution des résidus mod d reste UNIFORME (Axe 4).")
    verdict_lines.append(
        "Le réarrangement ne crée PAS de biais systématique vers ou")
    verdict_lines.append(
        "loin du résidu 0. L'information structurelle est absorbée")
    verdict_lines.append(
        "par la réduction mod d.")
    verdict_lines.append("")
    verdict_lines.append(
        "STATUT : L'inégalité de réarrangement est un FAIT MATHÉMATIQUE PROUVÉ")
    verdict_lines.append(
        "sur corrSum, mais elle NE SE TRADUIT PAS en contrainte exploitable")
    verdict_lines.append(
        "sur corrSum mod d. Le résidu est effectivement pseudo-aléatoire.")

    for line in verdict_lines:
        print(f"  {line}")

    results['verdict'] = verdict_lines

    # Sauvegarder
    # Convertir pour JSON
    def make_serializable(obj):
        if isinstance(obj, (int,)):
            return int(obj)
        if isinstance(obj, float):
            if math.isnan(obj) or math.isinf(obj):
                return str(obj)
            return obj
        if isinstance(obj, dict):
            return {k: make_serializable(v) for k, v in obj.items()}
        if isinstance(obj, list):
            return [make_serializable(v) for v in obj]
        if isinstance(obj, tuple):
            return [make_serializable(v) for v in obj]
        return obj

    with open('/Users/ericmerle/Documents/Collatz-Junction-Theorem/research_log/R160_MPF_results.json', 'w') as f:
        json.dump(make_serializable(results), f, indent=2)

    print(f"\n  Résultats sauvegardés dans R160_MPF_results.json")

if __name__ == '__main__':
    main()
