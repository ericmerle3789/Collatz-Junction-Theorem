#!/usr/bin/env python3
"""
POURQUOI c₀ = 1 EST-IL LE SEUL ÉTAT BLOQUÉ ?
==============================================
Session 5 — Attaque de la question clé identifiée en session 4.

DÉCOUVERTE (session 4) : L'état 0 est accessible depuis presque tous
les états initiaux SAUF c₀ = 1. Pourquoi ?

Ce script explore CINQ PISTES :

PISTE A : Bornes sur corrSum(A)
  corrSum(A) = Σ_{j=0}^{k-1} 3^{k-1-j} · 2^{A_j}
  Si max(corrSum) < 2d, alors n₀ = corrSum/d = 1 obligatoirement,
  ce qui impose corrSum = d exactement → contradiction possible.

PISTE B : Trajectoire typique depuis c₀ = 1
  Comment c_j évolue-t-il pas après pas ? Y a-t-il un "bassin"
  dont l'état 1 ne peut pas sortir pour atteindre 0 ?

PISTE C : Borne inférieure de corrSum
  corrSum(A) ≥ 3^{k-1} (car le terme j=0 vaut 3^{k-1} et les autres > 0)
  Si corrSum(A) ≥ d + 1 pour la composition minimale, et < 2d,
  alors n₀ = 1 et corrSum = d exactement est la SEULE possibilité.

PISTE D : "Énergie" de l'état 1
  Comparer le comportement de l'automate depuis c₀=1 vs c₀=c pour c ≠ 1.
  Quelle propriété QUANTITATIVE distingue c₀=1 ?

PISTE E : Double peeling
  Contraindre simultanément par le premier pas ET le dernier pas.
"""

import math
from collections import defaultdict
from itertools import combinations


def compute_params(k):
    """Calcule les paramètres de base."""
    S = math.ceil(k * math.log2(3))
    d = 2**S - 3**k
    C = math.comb(S - 1, k - 1)
    return S, d, C


def corrsum(A, k):
    """Calcule corrSum(A) = Σ 3^{k-1-j} · 2^{A_j}."""
    return sum(3**(k - 1 - j) * 2**A[j] for j in range(k))


# ============================================================
# PISTE A : Bornes sur corrSum
# ============================================================

def piste_A_bornes_corrsum(k_max=20):
    """Calcule min, max, moyenne de corrSum(A) et compare à d et 2d."""
    print("\n" + "=" * 80)
    print("PISTE A : BORNES SUR corrSum(A)")
    print("=" * 80)

    print(f"\n{'k':>3} {'S':>4} {'d':>12} {'min_cS':>14} {'max_cS':>14} "
          f"{'min/d':>8} {'max/d':>8} {'n0_min':>6} {'n0_max':>6}")
    print("-" * 90)

    results = []
    for k in range(3, k_max + 1):
        S, d, C = compute_params(k)
        if d <= 0:
            continue

        # Borne inférieure théorique : composition A = (0,1,2,...,k-1)
        # corrSum = Σ 3^{k-1-j} · 2^j = (3^k - 2^k) / (3-2) = 3^k - 2^k
        # (somme géométrique si A_j = j)
        A_min = list(range(k))  # 0, 1, 2, ..., k-1
        cs_min_theo = corrsum(A_min, k)

        # Borne supérieure théorique : A = (0, S-k+1, S-k+2, ..., S-1)
        A_max = [0] + list(range(S - k + 1, S))
        cs_max_theo = corrsum(A_max, k)

        # Si C est petit, on peut énumérer tout
        if C <= 500000:
            positions = list(range(1, S))
            min_cs = float('inf')
            max_cs = 0
            total = 0
            count = 0
            n0_counts = defaultdict(int)

            for combo in combinations(positions, k - 1):
                A = (0,) + combo
                cs = corrsum(A, k)
                min_cs = min(min_cs, cs)
                max_cs = max(max_cs, cs)
                total += cs
                count += 1
                n0 = cs // d  # n₀ potentiel (si cs ≡ 0 mod d, n₀ = cs/d)
                n0_counts[n0] += 1
        else:
            min_cs = cs_min_theo
            max_cs = cs_max_theo
            count = C
            n0_counts = {}

        n0_min = min_cs // d if d > 0 else 0
        n0_max = max_cs // d if d > 0 else 0

        # n₀ possibles si corrSum ≡ 0 mod d
        possible_n0 = list(range(max(1, n0_min), n0_max + 1))

        print(f"{k:3d} {S:4d} {d:12d} {min_cs:14d} {max_cs:14d} "
              f"{min_cs/d:8.3f} {max_cs/d:8.3f} {n0_min:6d} {n0_max:6d}")

        results.append({
            'k': k, 'S': S, 'd': d, 'C': C,
            'min_cs': min_cs, 'max_cs': max_cs,
            'min_ratio': min_cs / d, 'max_ratio': max_cs / d,
            'n0_min': n0_min, 'n0_max': n0_max,
            'possible_n0': possible_n0,
            'n0_distribution': dict(n0_counts) if n0_counts else None
        })

    # Analyse
    print(f"\n--- ANALYSE ---")
    for r in results:
        k = r['k']
        if r['n0_distribution']:
            dist = r['n0_distribution']
            print(f"\n  k={k}: n₀ distribution (si corrSum = n₀·d) :")
            for n0_val in sorted(dist.keys()):
                print(f"    n₀={n0_val} : {dist[n0_val]} compositions "
                      f"({100*dist[n0_val]/r['C']:.1f}%)")
        else:
            print(f"\n  k={k}: n₀ possibles = {r['possible_n0'][:10]}...")

    return results


# ============================================================
# PISTE B : Trajectoire depuis c₀ = 1
# ============================================================

def piste_B_trajectoire(k_val):
    """Analyse la trajectoire typique depuis c₀=1 dans l'automate."""
    S, d, C = compute_params(k_val)
    if d <= 0 or C > 200000:
        return None

    print(f"\n{'=' * 80}")
    print(f"PISTE B : TRAJECTOIRE DEPUIS c₀=1 (k={k_val}, d={d})")
    print(f"{'=' * 80}")

    # Construire les couches de l'automate depuis c₀=1
    layers = [{(1, 0): 1}]

    for step in range(1, k_val):
        current = layers[-1]
        next_layer = defaultdict(int)
        for (state, last_pos), count in current.items():
            for p in range(last_pos + 1, S):
                ns = (3 * state + pow(2, p, d)) % d
                next_layer[(ns, p)] += count
        layers.append(dict(next_layer))

    # Analyser chaque couche
    print(f"\n  Couche par couche (depuis c₀=1) :")
    for step, layer in enumerate(layers):
        states = defaultdict(int)
        for (s, p), c in layer.items():
            states[s] += c
        total = sum(states.values())
        has_zero = 0 in states
        zero_count = states.get(0, 0)
        min_state = min(states.keys())
        max_state = max(states.keys())
        unique_states = len(states)

        # Distribution dans Z/dZ : quelle fraction de {0,...,d-1} est couverte ?
        coverage = unique_states / d * 100

        print(f"  Couche {step}: {total} chemins, {unique_states} états "
              f"({coverage:.1f}% de Z/{d}Z), "
              f"0 {'PRESENT' if has_zero else 'absent'}"
              f"{f' ({zero_count} chemins)' if has_zero else ''}")

    # Comparer avec d'autres états initiaux
    print(f"\n  Comparaison : c₀ = 1 vs autres états initiaux")
    test_starts = [0, 1, 2, 3, d - 1, d // 2, d // 3]
    test_starts = [c for c in test_starts if 0 <= c < d]

    for c0 in sorted(set(test_starts)):
        layers_c0 = [{(c0, 0): 1}]
        for step in range(1, k_val):
            current = layers_c0[-1]
            next_layer = defaultdict(int)
            for (state, last_pos), count in current.items():
                for p in range(last_pos + 1, S):
                    ns = (3 * state + pow(2, p, d)) % d
                    next_layer[(ns, p)] += count
            layers_c0.append(dict(next_layer))

        final = layers_c0[-1]
        states_final = defaultdict(int)
        for (s, p), c in final.items():
            states_final[s] += c
        has_zero = 0 in states_final
        zero_count = states_final.get(0, 0)
        total = sum(states_final.values())

        print(f"    c₀={c0:4d} : 0 {'ATTEINT' if has_zero else 'ABSENT '} "
              f"({zero_count}/{total} chemins = "
              f"{100*zero_count/total:.2f}%)" if has_zero else
              f"    c₀={c0:4d} : 0 ABSENT  (0/{total} chemins)")

    return layers


# ============================================================
# PISTE C : Analyse fine de corrSum = n₀·d
# ============================================================

def piste_C_corrsum_exact(k_val):
    """Pour chaque n₀ possible, vérifie si corrSum = n₀·d est réalisable."""
    S, d, C = compute_params(k_val)
    if d <= 0 or C > 200000:
        return None

    print(f"\n{'=' * 80}")
    print(f"PISTE C : ANALYSE corrSum = n₀·d (k={k_val}, d={d}, S={S})")
    print(f"{'=' * 80}")

    # corrSum(A) = Σ 3^{k-1-j} · 2^{A_j} avec 0=A₀<A₁<...<A_{k-1}≤S-1
    # Terme j=0 : 3^{k-1} · 2^0 = 3^{k-1} (fixe)
    # Donc corrSum = 3^{k-1} + Σ_{j=1}^{k-1} 3^{k-1-j} · 2^{A_j}

    base = 3**(k_val - 1)  # Partie fixe

    # Borne inf de la partie variable : A_j = j pour j=1,...,k-1
    # Σ 3^{k-1-j} · 2^j = Σ (2/3)^j · 3^{k-1} = 3^{k-1} · ((2/3)^k - (2/3))/(2/3 - 1)
    var_min = sum(3**(k_val - 1 - j) * 2**j for j in range(1, k_val))
    var_max = sum(3**(k_val - 1 - j) * 2**(S - k_val + j) for j in range(1, k_val))

    cs_min = base + var_min
    cs_max = base + var_max

    print(f"  Partie fixe (3^{{k-1}}) = {base}")
    print(f"  Partie variable min = {var_min} (A_j = j)")
    print(f"  Partie variable max = {var_max} (A_j = S-k+j)")
    print(f"  corrSum min = {cs_min}")
    print(f"  corrSum max = {cs_max}")
    print(f"  d = {d}")
    print(f"  corrSum/d in [{cs_min/d:.4f}, {cs_max/d:.4f}]")

    n0_min = math.ceil(cs_min / d)
    n0_max = cs_max // d

    print(f"\n  n₀ possibles = {list(range(n0_min, n0_max + 1))}")

    # Pour chaque n₀, le "target" est corrSum = n₀·d
    # corrSum = 3^{k-1} + partie_variable = n₀·d
    # => partie_variable = n₀·d - 3^{k-1}
    for n0 in range(max(1, n0_min), n0_max + 1):
        target_cs = n0 * d
        target_var = target_cs - base

        if target_var < var_min or target_var > var_max:
            print(f"\n  n₀={n0} : target_var = {target_var} HORS BORNES "
                  f"[{var_min}, {var_max}]")
            continue

        print(f"\n  n₀={n0} : corrSum cible = {target_cs}")
        print(f"    Partie variable cible = {target_var}")

        # La partie variable = Σ_{j=1}^{k-1} 3^{k-1-j} · 2^{A_j}
        # C'est un nombre avec une structure très spécifique.
        # Vérifions si la cible est atteignable
        if C <= 200000:
            positions = list(range(1, S))
            found = False
            for combo in combinations(positions, k_val - 1):
                var = sum(3**(k_val - 1 - j) * 2**combo[j - 1]
                          for j in range(1, k_val))
                if var == target_var:
                    print(f"    TROUVÉ : A = (0, {combo})")
                    print(f"    corrSum = {target_cs} = {n0} × {d}")
                    found = True
                    break
            if not found:
                print(f"    NON TROUVÉ dans l'énumération complète !")
                print(f"    => corrSum = {n0}·d est IMPOSSIBLE.")

    return {'k': k_val, 'cs_min': cs_min, 'cs_max': cs_max,
            'n0_range': (n0_min, n0_max)}


# ============================================================
# PISTE D : Qu'est-ce qui distingue c₀=1 ?
# ============================================================

def piste_D_distinction_c0(k_val):
    """Analyse quantitative : qu'est-ce qui rend c₀=1 spécial ?"""
    S, d, C = compute_params(k_val)
    if d <= 0 or C > 200000:
        return None

    print(f"\n{'=' * 80}")
    print(f"PISTE D : QU'EST-CE QUI REND c₀=1 SPÉCIAL ? (k={k_val}, d={d})")
    print(f"{'=' * 80}")

    # Pour chaque c₀ possible, construire l'automate complet
    # et compter N₀(d, c₀) = nombre de chemins de c₀ à 0

    blocked_starts = []
    reaching_starts = []

    for c0 in range(d):
        layers = [{(c0, 0): 1}]
        for step in range(1, k_val):
            current = layers[-1]
            next_layer = defaultdict(int)
            for (state, last_pos), count in current.items():
                for p in range(last_pos + 1, S):
                    ns = (3 * state + pow(2, p, d)) % d
                    next_layer[(ns, p)] += count
            layers.append(dict(next_layer))

        final = layers[-1]
        states_final = defaultdict(int)
        for (s, p), c in final.items():
            states_final[s] += c
        n0_count = states_final.get(0, 0)

        if n0_count == 0:
            blocked_starts.append(c0)
        else:
            reaching_starts.append((c0, n0_count))

    print(f"\n  États initiaux BLOQUÉS (ne peuvent pas atteindre 0) :")
    print(f"    {blocked_starts}")
    print(f"    Nombre : {len(blocked_starts)}/{d}")

    if len(blocked_starts) <= 10:
        print(f"\n  Analyse des états bloqués :")
        for c0 in blocked_starts:
            # Propriétés arithmétiques
            is_power_of_2 = (c0 & (c0 - 1) == 0) if c0 > 0 else False
            mod3 = c0 % 3
            mod_d_inv = None
            # c₀ est-il dans ⟨2⟩ mod d ?
            in_2_orbit = False
            p2 = 1
            for i in range(S + 5):
                if p2 % d == c0:
                    in_2_orbit = True
                    break
                p2 = (p2 * 2) % d
            # c₀ est-il dans ⟨3⟩ mod d ?
            in_3_orbit = False
            p3 = 1
            for i in range(d):
                if p3 == c0:
                    in_3_orbit = True
                    break
                p3 = (p3 * 3) % d

            print(f"    c₀={c0}: 2^0={1 if c0==1 else 'non'}, "
                  f"in ⟨2⟩={'OUI' if in_2_orbit else 'non'}, "
                  f"in ⟨3⟩={'OUI' if in_3_orbit else 'non'}, "
                  f"mod 3={mod3}")

    # Y a-t-il un pattern parmi les états bloqués ?
    if blocked_starts:
        print(f"\n  Pattern des états bloqués :")
        # Sont-ils tous dans ⟨3⟩ ?
        orbits_3 = set()
        p3 = 1
        for _ in range(d):
            orbits_3.add(p3)
            p3 = (p3 * 3) % d
        blocked_in_3 = [c for c in blocked_starts if c in orbits_3]
        print(f"    Dans ⟨3⟩ mod d : {blocked_in_3}")

        # Sont-ils tous des puissances de 2 ?
        blocked_powers_2 = []
        p2 = 1
        for i in range(S + 5):
            if p2 % d in blocked_starts:
                blocked_powers_2.append((i, p2 % d))
            p2 = (p2 * 2) % d
        print(f"    Puissances de 2 mod d bloquées : {blocked_powers_2}")

    return {'blocked': blocked_starts, 'reaching_count': len(reaching_starts)}


# ============================================================
# PISTE E : Double Peeling (contraintes premier + dernier pas)
# ============================================================

def piste_E_double_peeling(k_val):
    """Attaque par les deux bouts : premier et dernier pas."""
    S, d, C = compute_params(k_val)
    if d <= 0 or C > 200000:
        return None

    print(f"\n{'=' * 80}")
    print(f"PISTE E : DOUBLE PEELING (k={k_val}, d={d}, S={S})")
    print(f"{'=' * 80}")

    # PREMIER PAS : c₀ = 1, c₁ = (3 + 2^{p₁}) mod d pour p₁ ∈ {1,...,S-1}
    print(f"\n  Premier pas (c₀=1 → c₁) :")
    first_step = {}
    for p1 in range(1, S):
        c1 = (3 + pow(2, p1, d)) % d
        first_step[p1] = c1
    print(f"    c₁ possibles : {sorted(set(first_step.values()))}")
    print(f"    Nombre : {len(set(first_step.values()))}/{d}")

    # DERNIER PAS : c_{k-2} → c_{k-1} = 0
    # c_{k-1} = (3·c_{k-2} + 2^{p_{k-1}}) mod d = 0
    # => 2^{p_{k-1}} = -3·c_{k-2} mod d
    # => c_{k-2} = -2^{p_{k-1}}/3 mod d = -2^{p_{k-1}} · 3^{-1} mod d
    print(f"\n  Dernier pas (c_{{k-2}} → 0) :")
    inv3 = pow(3, -1, d)  # inverse de 3 mod d
    last_step = {}  # p_{k-1} -> c_{k-2} nécessaire
    for pk in range(1, S):
        ck2_needed = (-pow(2, pk, d) * inv3) % d
        last_step[pk] = ck2_needed
    reachable_ck2 = set(last_step.values())
    print(f"    c_{{k-2}} nécessaires : {len(reachable_ck2)} valeurs distinctes")

    # INTERSECTION : quels c₁ mènent à des c_{k-2} qui permettent d'atteindre 0 ?
    # Pour k=3 : c₁ = c_{k-2} directement (un seul pas intermédiaire)
    if k_val == 3:
        print(f"\n  k=3 : c₁ = c_{{k-2}} directement (pas intermédiaire)")
        c1_set = set(first_step.values())
        ck2_set = reachable_ck2
        intersection = c1_set & ck2_set

        print(f"    c₁ possibles : {sorted(c1_set)}")
        print(f"    c_{{k-2}} nécessaires : {sorted(ck2_set)}")
        print(f"    Intersection : {sorted(intersection)}")

        # Pour chaque (p₁, p₂) compatible
        for p1 in range(1, S):
            c1 = first_step[p1]
            for p2 in range(p1 + 1, S):
                ck2 = last_step[p2]
                if c1 == ck2:
                    c_final = (3 * c1 + pow(2, p2, d)) % d
                    print(f"    p₁={p1}, p₂={p2}: c₁={c1}, "
                          f"c_final={(3*c1 + pow(2,p2,d)) % d} "
                          f"{'= 0 !!!' if c_final == 0 else ''}")

    # Pour k > 3 : analyser les étapes intermédiaires
    elif k_val <= 7:
        print(f"\n  k={k_val} : Analyse des contraintes croisées")

        # Forward : depuis c₀=1, quels états à l'étape j ?
        forward = [{(1, 0): 1}]
        for step in range(1, k_val - 1):
            current = forward[-1]
            nl = defaultdict(int)
            for (state, lp), cnt in current.items():
                for p in range(lp + 1, S):
                    ns = (3 * state + pow(2, p, d)) % d
                    nl[(ns, p)] += cnt
            forward.append(dict(nl))

        # Backward : depuis c_{k-1}=0, quels états à l'étape j (en arrière) ?
        # c_j = (c_{j+1} - 2^{p_{j+1}}) · 3^{-1} mod d
        backward = [{(0, S): 1}]  # position S comme "borne sup" fictive
        for step in range(1, k_val - 1):
            current = backward[-1]
            nl = defaultdict(int)
            for (state, first_pos), cnt in current.items():
                for p in range(1, first_pos):
                    prev_state = ((state - pow(2, p, d)) * inv3) % d
                    nl[(prev_state, p)] += cnt
            backward.append(dict(nl))

        # Point de rencontre : étape médiane
        mid = (k_val - 1) // 2
        fwd_mid = forward[mid]
        bwd_mid = backward[k_val - 1 - mid - 1] if k_val - 1 - mid - 1 < len(backward) else {}

        fwd_states = defaultdict(int)
        for (s, p), c in fwd_mid.items():
            fwd_states[s] += c

        bwd_states = defaultdict(int)
        for (s, p), c in bwd_mid.items():
            bwd_states[s] += c

        intersection_states = set(fwd_states.keys()) & set(bwd_states.keys())

        print(f"    Étape médiane {mid} :")
        print(f"      Forward : {len(fwd_states)} états distincts")
        print(f"      Backward : {len(bwd_states)} états distincts")
        print(f"      Intersection : {len(intersection_states)} états communs")
        print(f"      0 dans forward ? {'OUI' if 0 in fwd_states else 'NON'}")
        print(f"      1 dans backward ? {'OUI' if 1 in bwd_states else 'NON'}")

        # L'intersection est-elle VIDE (ce qui prouverait N₀=0) ?
        if not intersection_states:
            print(f"    ==> INTERSECTION VIDE ! Double peeling PROUVE N₀=0.")
        else:
            print(f"    ==> Intersection non vide. Le double peeling seul ne suffit pas.")
            # Mais on peut affiner avec les contraintes de position
            fwd_with_pos = fwd_mid
            bwd_with_pos = bwd_mid

            # Combien de paires (état, pos) sont compatibles ?
            matches = 0
            for (fs, fp), fc in fwd_with_pos.items():
                for (bs, bp), bc in bwd_with_pos.items():
                    if fs == bs and fp < bp:  # même état, positions compatibles
                        matches += fc * bc

            total_fwd = sum(fwd_with_pos.values())
            total_bwd = sum(bwd_with_pos.values())

            print(f"    Avec contraintes de position :")
            print(f"      Paires compatibles : {matches}")
            print(f"      (sur {total_fwd} × {total_bwd} = {total_fwd * total_bwd} possibles)")

    return {'first_step': first_step, 'last_step': last_step}


# ============================================================
# SYNTHÈSE : La piste la plus prometteuse
# ============================================================

def synthese():
    """Synthèse de toutes les pistes."""
    print("\n" + "*" * 80)
    print("SYNTHÈSE : POURQUOI c₀ = 1 EST-IL LE SEUL ÉTAT BLOQUÉ ?")
    print("*" * 80)

    # Exécuter toutes les pistes
    print("\n" + "#" * 80)
    print("# PISTE A : BORNES SUR corrSum")
    print("#" * 80)
    results_A = piste_A_bornes_corrsum(k_max=15)

    for k_val in [3, 4, 5, 6, 7]:
        S, d, C = compute_params(k_val)
        if d <= 0 or C > 200000:
            continue

        print(f"\n{'#' * 80}")
        print(f"# PISTES B+C+D+E POUR k={k_val}")
        print(f"{'#' * 80}")

        piste_B_trajectoire(k_val)
        piste_C_corrsum_exact(k_val)
        piste_D_distinction_c0(k_val)
        piste_E_double_peeling(k_val)


if __name__ == "__main__":
    synthese()
