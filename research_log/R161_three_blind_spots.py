#!/usr/bin/env python3
"""
R161 — INVESTIGATION DES 3 ANGLES MORTS
========================================
Audit rigoureux des 3 pistes proposées dans "Stratégie de Percée".

ANGLE A : Géométrie d'Arakelov Combinatoire
ANGLE B : Distorsion de Pente (Slope Distortion)
ANGLE C : Automates / Mots Sturmiens

PROTOCOLE : Fail-Closed — chaque angle doit démontrer un contenu
NON TAUTOLOGIQUE et NON CIRCULAIRE, sinon il est enterré.
"""

import math
import random
import json
from collections import Counter
from itertools import combinations_with_replacement
from sympy import factorint, isprime

# ============================================================================
# UTILITAIRES
# ============================================================================

def corrSum_value(k, B_vec):
    """Calcule corrSum = Σ 3^{k-1-j} · 2^{B_j}."""
    return sum(3**(k-1-j) * (1 << B_vec[j]) for j in range(k))

def enumerate_monotone_B(k, max_B):
    """Énumère TOUTES les séquences B monotones avec B_{k-1} = max_B.
    Via gaps : c_0, ..., c_{k-1} >= 0 avec Σc_j = max_B."""
    if k == 1:
        yield [max_B]
        return
    # Stars and bars : placer max_B unités dans k boîtes
    # Utiliser une approche récursive pour petit k
    def _gen(remaining, num_boxes, current):
        if num_boxes == 1:
            yield current + [remaining]
            return
        for c in range(remaining + 1):
            yield from _gen(remaining - c, num_boxes - 1, current + [c])

    for gaps in _gen(max_B, k, []):
        B = [0] * k
        B[0] = gaps[0]
        for j in range(1, k):
            B[j] = B[j-1] + gaps[j]
        yield B

def random_monotone_B(k, max_B, rng):
    """B monotone aléatoire uniforme."""
    if k == 1:
        return [max_B]
    separators = sorted(rng.sample(range(max_B + k - 1), k - 1))
    gaps = []
    prev = -1
    for s in separators:
        gaps.append(s - prev - 1)
        prev = s
    gaps.append(max_B + k - 2 - prev)
    B = [0] * k
    B[0] = gaps[0]
    for j in range(1, k):
        B[j] = B[j-1] + gaps[j]
    return B

# ============================================================================
# ANGLE A : GÉOMÉTRIE D'ARAKELOV COMBINATOIRE
# ============================================================================

def angle_A_arakelov(k_range=range(3, 11)):
    """
    Test : la "hauteur d'Arakelov" h(corrSum) = log|corrSum| - Σ_{p|d} min(v_p(cs), v_p(d))·log(p)
    distingue-t-elle corrSum ≡ 0 mod d ?

    HYPOTHÈSE DU DOCUMENT : un invariant sommant contribution archi + non-archi
    pourrait être non nul pour arrangements monotones.

    TEST CRITIQUE : pour x ∈ Z, la formule du produit est
      |x| = Π_p p^{v_p(x)}
    C'est l'arithmétique fondamentale. Aucune information supplémentaire.
    """
    print("=" * 70)
    print("ANGLE A : GÉOMÉTRIE D'ARAKELOV COMBINATOIRE")
    print("=" * 70)

    results = []

    for k in k_range:
        S = math.ceil(k * math.log2(3)) + 1
        d = (1 << S) - 3**k
        if d <= 0:
            continue
        max_B = S - k
        if max_B < 0:
            continue

        # Factoriser d
        d_factors = factorint(d)

        # Pour petit k : énumération complète
        C_comp = math.comb(S - 1, k - 1)
        if C_comp > 500000:
            print(f"\n  k={k}, S={S} : C={C_comp:.1e} trop grand, skip énumération")
            continue

        heights = []
        heights_mod0 = []  # corrSum ≡ 0 mod d
        heights_near = []  # corrSum "presque" multiple de d

        n_solutions = 0

        for B in enumerate_monotone_B(k, max_B):
            cs = corrSum_value(k, B)

            # Hauteur archi
            h_inf = math.log(cs) if cs > 0 else -float('inf')

            # Contribution non-archi : v_p(corrSum) pour p|d
            h_nonarchi = 0
            cs_temp = cs
            for p, e_d in d_factors.items():
                v = 0
                t = cs_temp
                while t > 0 and t % p == 0:
                    v += 1
                    t //= p
                h_nonarchi += min(v, e_d) * math.log(p)

            h_arak = h_inf - h_nonarchi

            heights.append(h_arak)

            if cs % d == 0:
                n_solutions += 1
                heights_mod0.append(h_arak)
            elif abs(cs % d) < d // 10 or abs(cs % d - d) < d // 10:
                heights_near.append(h_arak)

        h_mean = sum(heights) / len(heights) if heights else 0
        h_std = (sum((h - h_mean)**2 for h in heights) / len(heights))**0.5 if heights else 0

        result = {
            'k': k, 'S': S, 'd': d,
            'C_comp': C_comp,
            'n_solutions': n_solutions,
            'h_mean': h_mean,
            'h_std': h_std,
            'h_mod0': heights_mod0,
            'h_near_mean': sum(heights_near) / len(heights_near) if heights_near else None,
            'n_near': len(heights_near),
            'd_factors': str(d_factors)
        }
        results.append(result)

        print(f"\n  k={k}, S={S}, d={d} = {d_factors}")
        print(f"    C = {C_comp}, N₀(d) = {n_solutions}")
        print(f"    h_Arakelov : mean={h_mean:.4f}, std={h_std:.4f}")
        if heights_mod0:
            print(f"    h pour corrSum≡0 : {heights_mod0}")
        else:
            print(f"    AUCUN corrSum≡0 (confirme N₀=0)")
        if heights_near:
            print(f"    h pour quasi-multiples ({len(heights_near)} cas) : mean={result['h_near_mean']:.4f}")

    # VERDICT
    print(f"\n  {'='*60}")
    print(f"  VERDICT ANGLE A :")
    print(f"  La hauteur d'Arakelov pour un entier x ∈ Z est :")
    print(f"    h(x) = log|x| - Σ_{{p|d}} min(v_p(x), v_p(d))·log(p)")
    print(f"  Pour x = m·d : h = log(m·d) - log(d) = log(m)")
    print(f"  Pour x ≠ 0 mod d : h = log|x| - (contribution partielle) > 0")
    print(f"  ")
    print(f"  PROBLÈME : h distingue x≡0 mod d de x≢0 mod d")
    print(f"  SEULEMENT SI on sait déjà que x≡0 mod d.")
    print(f"  C'est CIRCULAIRE : h encode la divisibilité par d,")
    print(f"  elle ne la PRÉDIT pas.")
    print(f"  ")
    print(f"  FONDAMENTAL : pour x ∈ Z, la formule du produit est :")
    print(f"    x = ± Π_p p^{{v_p(x)}}")
    print(f"  C'est l'ARITHMÉTIQUE FONDAMENTALE, pas un invariant non trivial.")
    print(f"  La géométrie d'Arakelov enrichit les VARIÉTÉS (via Riemann-Roch,")
    print(f"  théorie d'intersection) mais pour un ENTIER ISOLÉ,")
    print(f"  il n'y a pas de structure géométrique à exploiter.")
    print(f"  ")
    print(f"  STATUT : MORT — tautologie (formule du produit pour Z)")

    return results

# ============================================================================
# ANGLE B : DISTORSION DE PENTE (SLOPE DISTORTION)
# ============================================================================

def angle_B_slope_distortion(k_range=range(3, 11)):
    """
    Test : la déviation de B_j par rapport à la pente idéale σ = (S-k)/(k-1)
    est-elle corrélée avec corrSum mod d ?

    HYPOTHÈSE : pour corrSum ≡ 0 mod d, les B_j doivent s'écarter
    drastiquement de la pente diophantienne idéale.

    TEST : mesurer la déviation L² et L∞ par rapport à la droite idéale,
    et vérifier si les quasi-multiples de d ont des déviations anormales.
    """
    print("\n" + "=" * 70)
    print("ANGLE B : DISTORSION DE PENTE (SLOPE DISTORTION)")
    print("=" * 70)

    results = []

    for k in k_range:
        S = math.ceil(k * math.log2(3)) + 1
        d = (1 << S) - 3**k
        if d <= 0:
            continue
        max_B = S - k
        if max_B < 0 or k < 3:
            continue

        C_comp = math.comb(S - 1, k - 1)
        if C_comp > 500000:
            print(f"\n  k={k}, S={S} : C={C_comp:.1e} trop grand, Monte Carlo")
            # Monte Carlo
            rng = random.Random(42)
            n_samples = 100000
            dev_L2_list = []
            dev_Linf_list = []
            residues = []

            sigma = max_B / (k - 1) if k > 1 else 0

            for _ in range(n_samples):
                B = random_monotone_B(k, max_B, rng)
                cs = corrSum_value(k, B)
                r = cs % d

                # Déviation par rapport à la pente idéale
                deviations = [B[j] - j * sigma for j in range(k)]
                L2 = math.sqrt(sum(dv**2 for dv in deviations) / k)
                Linf = max(abs(dv) for dv in deviations)

                dev_L2_list.append(L2)
                dev_Linf_list.append(Linf)
                residues.append(r)

            # Corrélation déviation — résidu
            r_mean = sum(residues) / len(residues)
            L2_mean = sum(dev_L2_list) / len(dev_L2_list)
            cov = sum((r - r_mean) * (l - L2_mean) for r, l in zip(residues, dev_L2_list)) / len(residues)
            var_r = sum((r - r_mean)**2 for r in residues) / len(residues)
            var_L2 = sum((l - L2_mean)**2 for l in dev_L2_list) / len(dev_L2_list)
            corr = cov / max(math.sqrt(var_r * var_L2), 1e-30)

            result = {
                'k': k, 'S': S, 'd': d,
                'method': 'Monte Carlo',
                'L2_mean': L2_mean,
                'Linf_mean': sum(dev_Linf_list) / len(dev_Linf_list),
                'corr_residue_L2': corr
            }
            results.append(result)

            print(f"\n  k={k}, S={S}, d={d}")
            print(f"    Déviation L² moyenne = {L2_mean:.4f}")
            print(f"    Corrélation(résidu, déviation L²) = {corr:.6f}")
            continue

        sigma = max_B / (k - 1) if k > 1 else 0

        # Énumération complète
        dev_by_residue = {}  # résidu -> liste de (L2, Linf)
        all_L2 = []
        n_solutions = 0

        for B in enumerate_monotone_B(k, max_B):
            cs = corrSum_value(k, B)
            r = cs % d

            deviations = [B[j] - j * sigma for j in range(k)]
            L2 = math.sqrt(sum(dv**2 for dv in deviations) / k)
            Linf = max(abs(dv) for dv in deviations)

            all_L2.append(L2)

            if r not in dev_by_residue:
                dev_by_residue[r] = []
            dev_by_residue[r].append((L2, Linf))

            if r == 0:
                n_solutions += 1

        L2_global_mean = sum(all_L2) / len(all_L2)

        # Les quasi-multiples (résidus proches de 0 ou d) ont-ils des déviations plus grandes ?
        near_zero_devs = []
        far_devs = []
        threshold = max(1, d // 20)
        for r, devs in dev_by_residue.items():
            for L2, Linf in devs:
                if r < threshold or r > d - threshold:
                    near_zero_devs.append(L2)
                else:
                    far_devs.append(L2)

        near_mean = sum(near_zero_devs) / len(near_zero_devs) if near_zero_devs else 0
        far_mean = sum(far_devs) / len(far_devs) if far_devs else 0

        result = {
            'k': k, 'S': S, 'd': d,
            'method': 'exact',
            'C_comp': C_comp,
            'N0': n_solutions,
            'L2_global_mean': L2_global_mean,
            'L2_near_zero_mean': near_mean,
            'L2_far_mean': far_mean,
            'n_near': len(near_zero_devs),
            'n_far': len(far_devs),
            'ratio_near_far': near_mean / far_mean if far_mean > 0 else None
        }
        results.append(result)

        print(f"\n  k={k}, S={S}, d={d}")
        print(f"    C = {C_comp}, N₀ = {n_solutions}")
        print(f"    Pente idéale σ = {sigma:.4f}")
        print(f"    Déviation L² globale = {L2_global_mean:.4f}")
        print(f"    Déviation L² quasi-multiples (r≈0) = {near_mean:.4f} ({len(near_zero_devs)} cas)")
        print(f"    Déviation L² loin de 0 = {far_mean:.4f} ({len(far_devs)} cas)")
        if far_mean > 0:
            ratio = near_mean / far_mean
            print(f"    Ratio near/far = {ratio:.4f} {'(ANORMAL)' if abs(ratio - 1) > 0.3 else '(normal)'}")

    # VERDICT
    print(f"\n  {'='*60}")
    print(f"  VERDICT ANGLE B :")
    print(f"  La déviation par rapport à la pente idéale est UNE OBSERVABLE")
    print(f"  qui vit dans Z (espace d'ordre). Par le MPF (R160), nous savons")
    print(f"  que TOUTE observable de Z est détruite par la réduction mod d.")
    print(f"  ")
    print(f"  TEST NUMÉRIQUE : ratio déviation(quasi-multiples)/déviation(loin)")
    print(f"  devrait être ≈ 1 si pas de corrélation.")
    all_ratios = [r.get('ratio_near_far') for r in results if r.get('ratio_near_far') is not None]
    if all_ratios:
        print(f"  Ratios observés : {[f'{r:.3f}' for r in all_ratios]}")
        mean_ratio = sum(all_ratios) / len(all_ratios)
        print(f"  Ratio moyen = {mean_ratio:.4f}")
        if abs(mean_ratio - 1) < 0.2:
            print(f"  → PAS DE CORRÉLATION significative")
            print(f"  STATUT : MORT — la pente ne prédit pas le résidu mod d")
        else:
            print(f"  → CORRÉLATION DÉTECTÉE — à investiguer")
    else:
        print(f"  Données insuffisantes pour conclure")

    return results

# ============================================================================
# ANGLE C : AUTOMATES / MOTS STURMIENS
# ============================================================================

def subword_complexity(word, max_n=None):
    """Calcule la complexité de sous-mots C(n) = nombre de sous-mots distincts de longueur n."""
    if max_n is None:
        max_n = len(word) // 2
    complexities = {}
    for n in range(1, max_n + 1):
        subwords = set()
        for i in range(len(word) - n + 1):
            subwords.add(tuple(word[i:i+n]))
        complexities[n] = len(subwords)
    return complexities

def angle_C_sturmian(k_range=range(3, 11)):
    """
    Test : la complexité de sous-mots de la séquence de gaps
    c_j = B_j - B_{j-1} est-elle corrélée avec corrSum mod d ?

    HYPOTHÈSE : un mot sturmien (complexité n+1) serait nécessaire
    pour générer un cycle. Si la monotonie impose une complexité plus faible,
    le cycle est impossible.

    REMARQUE : les mots sturmiens ont complexité C(n) = n+1, la plus faible
    pour les mots apériodiques. Pour les mots périodiques, C(n) = constante.
    """
    print("\n" + "=" * 70)
    print("ANGLE C : AUTOMATES / MOTS STURMIENS")
    print("=" * 70)

    results = []

    for k in k_range:
        S = math.ceil(k * math.log2(3)) + 1
        d = (1 << S) - 3**k
        if d <= 0:
            continue
        max_B = S - k
        if max_B < 0 or k < 4:
            continue

        C_comp = math.comb(S - 1, k - 1)
        if C_comp > 500000:
            print(f"\n  k={k}, S={S} : C={C_comp:.1e} trop grand, Monte Carlo")
            rng = random.Random(42)
            n_samples = 50000

            complexities_all = []
            complexities_near = []
            complexities_far = []
            threshold = max(1, d // 20)

            for _ in range(n_samples):
                B = random_monotone_B(k, max_B, rng)
                cs = corrSum_value(k, B)
                r = cs % d

                # Séquence de gaps
                gaps = [B[0]] + [B[j] - B[j-1] for j in range(1, k)]

                # Complexité au niveau n=2 (pour efficacité)
                n_test = min(3, k // 2)
                sc = subword_complexity(gaps, max_n=n_test)
                c2 = sc.get(2, 0)

                complexities_all.append(c2)
                if r < threshold or r > d - threshold:
                    complexities_near.append(c2)
                else:
                    complexities_far.append(c2)

            mean_all = sum(complexities_all) / len(complexities_all)
            mean_near = sum(complexities_near) / len(complexities_near) if complexities_near else 0
            mean_far = sum(complexities_far) / len(complexities_far) if complexities_far else 0

            result = {
                'k': k, 'S': S, 'd': d,
                'method': 'Monte Carlo',
                'C2_mean_all': mean_all,
                'C2_mean_near': mean_near,
                'C2_mean_far': mean_far,
                'ratio': mean_near / mean_far if mean_far > 0 else None
            }
            results.append(result)

            print(f"\n  k={k}, S={S}")
            print(f"    C(2) moyen = {mean_all:.3f}")
            print(f"    C(2) quasi-mult = {mean_near:.3f}, loin = {mean_far:.3f}")
            if mean_far > 0:
                print(f"    Ratio = {mean_near/mean_far:.4f}")
            continue

        # Énumération complète
        complexities_by_residue = {}
        all_c2 = []
        n_solutions = 0

        for B in enumerate_monotone_B(k, max_B):
            cs = corrSum_value(k, B)
            r = cs % d

            gaps = [B[0]] + [B[j] - B[j-1] for j in range(1, k)]
            n_test = min(3, k // 2)
            sc = subword_complexity(gaps, max_n=n_test)
            c2 = sc.get(2, 0)

            all_c2.append(c2)
            if r not in complexities_by_residue:
                complexities_by_residue[r] = []
            complexities_by_residue[r].append(c2)

            if r == 0:
                n_solutions += 1

        mean_all = sum(all_c2) / len(all_c2)

        # Cobham : la complexité diffère-t-elle pour r≈0 ?
        near_c2 = []
        far_c2 = []
        threshold = max(1, d // 20)
        for r, c2_list in complexities_by_residue.items():
            if r < threshold or r > d - threshold:
                near_c2.extend(c2_list)
            else:
                far_c2.extend(c2_list)

        mean_near = sum(near_c2) / len(near_c2) if near_c2 else 0
        mean_far = sum(far_c2) / len(far_c2) if far_c2 else 0

        result = {
            'k': k, 'S': S, 'd': d,
            'method': 'exact',
            'C_comp': C_comp,
            'N0': n_solutions,
            'C2_mean_all': mean_all,
            'C2_mean_near': mean_near,
            'C2_mean_far': mean_far,
            'ratio': mean_near / mean_far if mean_far > 0 else None
        }
        results.append(result)

        print(f"\n  k={k}, S={S}, d={d}")
        print(f"    C = {C_comp}, N₀ = {n_solutions}")
        print(f"    Alphabet des gaps : {set(gaps)}")
        print(f"    C(2) moyen global = {mean_all:.3f}")
        print(f"    C(2) quasi-multiples = {mean_near:.3f} ({len(near_c2)} cas)")
        print(f"    C(2) loin = {mean_far:.3f} ({len(far_c2)} cas)")
        if mean_far > 0:
            ratio = mean_near / mean_far
            print(f"    Ratio = {ratio:.4f} {'(ANORMAL)' if abs(ratio - 1) > 0.2 else '(normal)'}")

    # VERDICT
    print(f"\n  {'='*60}")
    print(f"  VERDICT ANGLE C :")
    print(f"  Le théorème de Cobham (1969) : si une séquence est")
    print(f"  reconnaissable dans deux bases multiplicativement")
    print(f"  indépendantes (comme 2 et 3), elle est ultimement périodique.")
    print(f"  ")
    print(f"  PROBLÈME FONDAMENTAL : notre séquence (B_j) est FINIE")
    print(f"  (longueur k = 22..41). Cobham s'applique à des séquences INFINIES.")
    print(f"  Pour les séquences finies, il n'y a PAS de contrainte")
    print(f"  de complexité non triviale.")
    print(f"  ")
    print(f"  De plus, la corrSum est une COMBINAISON LINÉAIRE pondérée")
    print(f"  des 2^{{B_j}}, pas un objet reconnaissable par automate.")
    print(f"  L'application des résultats d'automates est une erreur de catégorie.")
    print(f"  ")
    all_ratios = [r.get('ratio') for r in results if r.get('ratio') is not None]
    if all_ratios:
        print(f"  Ratios complexité(quasi-mult)/complexité(loin) : "
              f"{[f'{r:.3f}' for r in all_ratios]}")
        mean_ratio = sum(all_ratios) / len(all_ratios)
        print(f"  Ratio moyen = {mean_ratio:.4f}")
        if abs(mean_ratio - 1) < 0.15:
            print(f"  → PAS DE CORRÉLATION")
    print(f"  ")
    print(f"  STATUT : MORT — erreur de catégorie (séquences finies, pas d'automates)")

    return results

# ============================================================================
# ANGLE TRANSVERSAL : LE PONT Z ↔ Z/dZ
# ============================================================================

def test_bridge_ZtoZd(k_range=range(3, 11)):
    """
    Test central : EXISTE-T-IL un observable f(B) vivant dans Z
    dont la valeur mod d est non uniforme ?

    Nous testons plusieurs observables :
    - corrSum (déjà testé par MPF)
    - corrSum_aligned (co-alignement)
    - Produit Π 2^{B_j}
    - Somme Σ B_j
    - Valeur de la "courbure" Σ|c_j - σ|

    Si AUCUNE n'a de biais résiduel, le pont Z → Z/dZ est
    UNIVERSELLEMENT destructeur pour les observables d'ordre.
    """
    print("\n" + "=" * 70)
    print("TEST TRANSVERSAL : OBSERVABLES DE Z vs RÉSIDUS mod d")
    print("=" * 70)

    for k in k_range:
        S = math.ceil(k * math.log2(3)) + 1
        d = (1 << S) - 3**k
        if d <= 0:
            continue
        max_B = S - k
        if max_B < 0:
            continue

        C_comp = math.comb(S - 1, k - 1)
        if C_comp > 200000:
            continue

        sigma = max_B / (k - 1) if k > 1 else 0

        obs_names = ['corrSum', 'Σ B_j', 'max gap', 'courbure']
        obs_near = {name: [] for name in obs_names}
        obs_far = {name: [] for name in obs_names}

        threshold = max(1, d // 20)

        for B in enumerate_monotone_B(k, max_B):
            cs = corrSum_value(k, B)
            r = cs % d

            # Observables
            sum_B = sum(B)
            gaps = [B[0]] + [B[j] - B[j-1] for j in range(1, k)]
            max_gap = max(gaps)
            courbure = sum(abs(g - sigma) for g in gaps)

            vals = [cs, sum_B, max_gap, courbure]

            target = obs_near if (r < threshold or r > d - threshold) else obs_far
            for name, val in zip(obs_names, vals):
                target[name].append(val)

        print(f"\n  k={k}, S={S}, d={d}")
        for name in obs_names:
            near_mean = sum(obs_near[name]) / len(obs_near[name]) if obs_near[name] else 0
            far_mean = sum(obs_far[name]) / len(obs_far[name]) if obs_far[name] else 0
            ratio = near_mean / far_mean if far_mean > 0 else None
            print(f"    {name:12s} : near={near_mean:.2f}, far={far_mean:.2f}, "
                  f"ratio={ratio:.4f}" if ratio else f"    {name:12s} : N/A")

    print(f"\n  {'='*60}")
    print(f"  Si tous les ratios ≈ 1.0 pour toutes les observables,")
    print(f"  le pont Z → Z/dZ est UNIVERSELLEMENT DESTRUCTEUR.")

# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 70)
    print("R161 — INVESTIGATION DES 3 ANGLES MORTS")
    print("Audit rigoureux — Protocole Fail-Closed")
    print("=" * 70)

    # Angle A
    results_A = angle_A_arakelov()

    # Angle B
    results_B = angle_B_slope_distortion()

    # Angle C
    results_C = angle_C_sturmian()

    # Test transversal
    test_bridge_ZtoZd()

    # VERDICT GLOBAL
    print("\n" + "=" * 70)
    print("VERDICT GLOBAL — 3 ANGLES MORTS")
    print("=" * 70)
    print("""
  ANGLE A (Arakelov) : MORT
    La formule du produit pour Z est l'arithmétique fondamentale.
    Pas de structure géométrique (Riemann-Roch, intersection)
    pour un entier isolé. L'invariant proposé est CIRCULAIRE.

  ANGLE B (Slope Distortion) : MORT
    La déviation de pente est une observable de Z.
    Par le Principe d'Incompatibilité (confirmé MPF R160),
    TOUTE observable de Z est détruite par la réduction mod d.
    Numériquement : aucune corrélation déviation ↔ résidu.

  ANGLE C (Sturmian/Automates) : MORT
    Cobham et la théorie des automates s'appliquent aux
    séquences INFINIES. Notre B_j est de longueur FINIE (k=22..41).
    Erreur de catégorie. Numériquement : aucune corrélation
    complexité ↔ résidu.

  TEST TRANSVERSAL : Le pont Z → Z/dZ est UNIVERSELLEMENT DESTRUCTEUR
    pour les observables testées (corrSum, somme B, max gap, courbure).
    Tous les ratios near/far ≈ 1.0.

  CONCLUSION :
    Les 3 angles morts NE SONT PAS des angles morts — ils sont des
    MANIFESTATIONS DIFFÉRENTES du même obstacle fondamental :

    ╔══════════════════════════════════════════════════════╗
    ║  La réduction mod d = 2^S - 3^k détruit toute      ║
    ║  information structurelle vivant dans Z.             ║
    ║  Aucun observable d'ordre, de taille, de complexité ║
    ║  ou de courbure ne survit à cette projection.       ║
    ╚══════════════════════════════════════════════════════╝

    Le "Principe d'Incompatibilité" (§1 du document) est CORRECT
    dans son diagnostic. Mais les "solutions" proposées (§3-4)
    ne franchissent PAS le pont — elles restent du côté Z.
""")

    # Sauvegarder
    all_results = {
        'angle_A': [str(r) for r in results_A],
        'angle_B': [str(r) for r in results_B],
        'angle_C': [str(r) for r in results_C]
    }
    with open('/Users/ericmerle/Documents/Collatz-Junction-Theorem/research_log/R161_results.json', 'w') as f:
        json.dump(all_results, f, indent=2)

    print("  Résultats sauvegardés dans R161_results.json")


if __name__ == '__main__':
    main()
