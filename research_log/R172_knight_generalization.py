#!/usr/bin/env python3
"""
R172 — GÉNÉRALISATION DE KNIGHT : EXPLORATION JEPA
====================================================

Knight (2025) prouve que le HIGH CYCLE ne peut être entier en montrant que
3·g(vh) - g(vh^R) = 3^x - 2^{k-1}, et que 2^{k-1}/(2^k - 3^x) n'est jamais entier.

La clé : vh et vh^R sont dans le MÊME cycle (vh^R est une rotation de vh
pour les mots de Christoffel).

QUESTION : Pour un vecteur de parité v QUELCONQUE, peut-on trouver une
combinaison linéaire de g-values de rotations qui produit une puissance de 2
(ou un nombre sans facteur premier de d) ?

EXPLORATION :
1. Pour chaque v de petits (k,x) :
   - Calculer g(v) pour toutes les rotations
   - Chercher des combinaisons linéaires a*g(rot_i) + b*g(rot_j) = 2^m
   - Si ça marche pour TOUT v, c'est la formule universelle

2. Exploiter la relation fondamentale :
   2*g(rot_1(v)) = 3*g(v) + d  si v[0] = 1
   2*g(rot_1(v)) = g(v)         si v[0] = 0
"""

import math
from itertools import combinations
from collections import defaultdict


def compute_g(v, x):
    """
    Calcule g(v) = Σ 2^{d_i} * 3^{x-1-i}
    où d_0 < d_1 < ... < d_{x-1} sont les positions des 1s dans v.
    """
    ones = [i for i, bit in enumerate(v) if bit == 1]
    assert len(ones) == x
    return sum(2**ones[i] * 3**(x-1-i) for i in range(x))


def rotate(v, j):
    """Rotation gauche de j positions."""
    k = len(v)
    return v[j:] + v[:j]


def all_parity_vectors(k, x):
    """Génère tous les vecteurs de parité aperiodiques de longueur k avec x uns."""
    for positions in combinations(range(k), x):
        v = [0] * k
        for p in positions:
            v[p] = 1
        v = tuple(v)
        # Vérifier apériodicité (pas de sous-période)
        is_aperiodic = True
        for period in range(1, k):
            if k % period == 0:
                if v == v[:period] * (k // period) and period < k:
                    is_aperiodic = False
                    break
        if is_aperiodic:
            yield v


def analyze_parity_vector(v, k, x, d):
    """
    Pour un vecteur v, cherche des combinaisons linéaires de g-values
    de rotations qui donnent une puissance de 2.
    """
    # Calculer g pour toutes les rotations
    rotations = []
    g_values = []
    seen = set()
    for j in range(k):
        vr = rotate(v, j)
        if vr not in seen:
            seen.add(vr)
            rotations.append((j, vr))
            g_values.append(compute_g(vr, x))

    n_rot = len(rotations)

    # Vérifier la relation fondamentale
    for idx, (j, vr) in enumerate(rotations):
        vr_next = rotate(v, (j + 1) % k)
        g_next = compute_g(vr_next, x)
        g_curr = g_values[idx]
        if vr[0] == 1:
            assert 2 * g_next == 3 * g_curr + d, f"Relation failed for rotation {j}"
        else:
            assert 2 * g_next == g_curr, f"Relation failed for rotation {j}"

    # Chercher des paires (i,j) telles que a*g_i + b*g_j = 2^m pour certains a,b,m
    results = []

    for i in range(n_rot):
        for j in range(i + 1, n_rot):
            gi, gj = g_values[i], g_values[j]

            # Essayer la combinaison de Knight : 3*gi - gj
            combo1 = 3 * gi - gj
            # Vérifier si c'est de la forme ±2^m ou ±2^m ± d
            if combo1 > 0 and combo1 & (combo1 - 1) == 0:  # power of 2
                results.append(('3g_i - g_j = 2^m', i, j, combo1,
                               math.log2(combo1)))

            combo2 = 3 * gj - gi
            if combo2 > 0 and combo2 & (combo2 - 1) == 0:
                results.append(('3g_j - g_i = 2^m', i, j, combo2,
                               math.log2(combo2)))

            # Aussi vérifier gi - gj
            diff = abs(gi - gj)
            if diff > 0 and diff & (diff - 1) == 0:
                results.append(('|g_i - g_j| = 2^m', i, j, diff,
                               math.log2(diff)))

            # 3*gi - gj + d
            combo3 = 3 * gi - gj + d
            if combo3 > 0 and combo3 & (combo3 - 1) == 0:
                results.append(('3g_i - g_j + d = 2^m', i, j, combo3,
                               math.log2(combo3)))

            # gi + gj
            total = gi + gj
            if total > 0 and total & (total - 1) == 0:
                results.append(('g_i + g_j = 2^m', i, j, total,
                               math.log2(total)))

    # Aussi chercher des combinaisons à un seul terme
    for i in range(n_rot):
        gi = g_values[i]
        # gi + d
        combo = gi + d
        if combo > 0 and combo & (combo - 1) == 0:
            results.append(('g_i + d = 2^m', i, -1, combo,
                           math.log2(combo)))

    return rotations, g_values, results


def is_power_of_2(n):
    return n > 0 and (n & (n - 1)) == 0


def gcd_with_d(val, d):
    """Compute gcd(val, d)."""
    return math.gcd(abs(val), d)


def main():
    print("=" * 72)
    print("R172 — GÉNÉRALISATION DE KNIGHT : EXPLORATION JEPA")
    print("=" * 72)
    print()

    # Pour chaque (k, x) petit :
    test_cases = [
        (5, 3),   # S=5, k=3 in our notation
        (7, 4),   # k=4 in our notation
        (8, 5),   # Knight's example
        (10, 6),
        (11, 7),
        (12, 7),
        (13, 8),
    ]

    for k, x in test_cases:
        d = 2**k - 3**x
        if d <= 0:
            continue

        print(f"\n{'='*60}")
        print(f"(k={k}, x={x}): d = 2^{k} - 3^{x} = {d}")
        print(f"{'='*60}")

        n_vectors = 0
        n_with_combo = 0
        n_without_combo = 0
        problematic = []

        for v in all_parity_vectors(k, x):
            n_vectors += 1
            rots, gvals, results = analyze_parity_vector(v, k, x, d)

            # Vérifier si g(v) ≡ 0 mod d (actual cycle candidate)
            g0 = gvals[0]
            is_cycle = (g0 % d == 0) and (g0 > 0)

            if results:
                n_with_combo += 1
                if n_vectors <= 3 or is_cycle:
                    v_str = ''.join(str(b) for b in v)
                    print(f"\n  v = {v_str}, g(v) = {g0}, "
                          f"g mod d = {g0 % d}, "
                          f"{'CYCLE CANDIDATE!' if is_cycle else ''}")
                    for combo_type, i, j, val, log2val in results[:3]:
                        ri = rots[i][0] if i >= 0 else -1
                        rj = rots[j][0] if j >= 0 else -1
                        print(f"    {combo_type}: rot({ri},{rj}) = {val} = 2^{log2val:.0f}")
            else:
                n_without_combo += 1
                # Est-ce un candidat de cycle ?
                if is_cycle:
                    v_str = ''.join(str(b) for b in v)
                    problematic.append((v_str, g0, g0 // d))
                    print(f"\n  ⚠️ v = {v_str}, g(v) = {g0}, n = {g0 // d} "
                          f"— NO power-of-2 combo found!")

        print(f"\n  BILAN: {n_vectors} vectors, "
              f"{n_with_combo} avec combo 2^m ({100*n_with_combo/max(1,n_vectors):.1f}%), "
              f"{n_without_combo} sans")
        if problematic:
            print(f"  ⚠️ PROBLÉMATIQUES (cycle candidates sans combo) : {problematic}")

    # Approche plus profonde : chercher des combinaisons linéaires générales
    print(f"\n\n{'='*72}")
    print("RECHERCHE DE COMBINAISONS LINÉAIRES GÉNÉRALES")
    print("=" * 72)

    k, x = 8, 5
    d = 2**k - 3**x
    print(f"\nCas d'étude détaillé : k={k}, x={x}, d={d}")

    for v in all_parity_vectors(k, x):
        v_str = ''.join(str(b) for b in v)
        rots, gvals, results = analyze_parity_vector(v, k, x, d)

        # Pour chaque paire de rotations, calculer gcd(combinaison, d)
        best_combo = None
        best_gcd_ratio = 0

        for i in range(len(gvals)):
            for j in range(len(gvals)):
                if i == j:
                    continue
                for a in range(-5, 6):
                    for b in range(-5, 6):
                        if a == 0 and b == 0:
                            continue
                        combo = a * gvals[i] + b * gvals[j]
                        if combo == 0:
                            continue
                        g = gcd_with_d(combo, d)
                        if g == d:
                            # combo is a multiple of d
                            # Check if combo/d is a power of 2
                            ratio = abs(combo) // d
                            if ratio > 0 and is_power_of_2(ratio):
                                if best_combo is None or ratio < best_gcd_ratio:
                                    best_combo = (a, b, i, j, combo, ratio)
                                    best_gcd_ratio = ratio
                        elif g == 1 and is_power_of_2(abs(combo)):
                            # combo is a pure power of 2
                            best_combo = (a, b, i, j, combo, 'pow2')
                            best_gcd_ratio = float('inf')

        g0 = gvals[0]
        is_cycle = (g0 % d == 0)
        if best_combo:
            a, b, i, j, combo, ratio = best_combo
            ri = rots[i][0]
            rj = rots[j][0]
            print(f"  {v_str}: {a}*g(rot{ri}) + {b}*g(rot{rj}) = {combo} "
                  f"(ratio={ratio}) {'CYCLE' if is_cycle else ''}")
        else:
            print(f"  {v_str}: no nice combo found {'CYCLE CANDIDATE!' if is_cycle else ''}")

    # Test de la stratégie "adjacente" : v et rotate(v, 1)
    # La relation est 2*g(v') = 3*g(v) + d ou 2*g(v') = g(v)
    # Que donne la chaîne sur k étapes ?
    print(f"\n\n{'='*72}")
    print("CHAÎNE DE RELATIONS SUR LE CYCLE COMPLET")
    print("=" * 72)

    k, x = 8, 5
    d = 2**k - 3**x
    print(f"\n(k={k}, x={x}), d={d}")

    for v in list(all_parity_vectors(k, x))[:5]:
        v_str = ''.join(str(b) for b in v)
        gvals = [compute_g(rotate(v, j), x) for j in range(k)]

        # Vérifier E - O = x * d
        O_sum = sum(gvals[j] for j in range(k) if v[j] == 1)
        E_sum = sum(gvals[j] for j in range(k) if v[j] == 0)
        assert E_sum - O_sum == x * d, f"E-O identity failed for {v_str}"

        # Chercher des identités structurelles
        # La somme totale :
        total = sum(gvals)
        print(f"\n  v = {v_str}")
        print(f"  g-values: {gvals}")
        print(f"  Σg = {total}, Σg/d = {total/d:.2f}")
        print(f"  E-O = {E_sum - O_sum} = {x}*{d} ✓")
        print(f"  gcd(Σg, d) = {math.gcd(total, d)}")

        # Le produit de tous les g-values mod d
        prod_mod_d = 1
        for g in gvals:
            prod_mod_d = (prod_mod_d * (g % d)) % d
        print(f"  Πg mod d = {prod_mod_d}")


if __name__ == '__main__':
    main()
