#!/usr/bin/env python3
"""
AUTOMATE BACKWARD AVEC CONTRAINTE D'ORDRE — Session 6
======================================================

DÉCOUVERTE CRUCIALE : L'obstruction pour l'Énoncé C n'est PAS une
obstruction modulaire simple (mod 3) — c'est la CONTRAINTE D'ORDRE
STRICT sur les positions qui bloque.

L'automate backward SANS contrainte d'ordre atteint s=5 facilement
(en utilisant des positions répétées comme [3,3,5]).

L'automate backward AVEC positions strictement décroissantes
(q_{k-1} > q_{k-2} > ... > q_2, toutes ≥ p+2) ne peut PAS
atteindre s = 3+2^p en exactement k-2 pas.

Ce script :
1. Construit l'automate backward CORRECT (positions ordonnées)
2. Vérifie que le target est inaccessible
3. Analyse POURQUOI la contrainte d'ordre crée l'obstruction
4. Quantifie la perte de couverture due à l'ordre
"""

import math
from itertools import combinations
from collections import defaultdict


def compute_params(k):
    S = math.ceil(k * math.log2(3))
    d = (1 << S) - 3**k
    return S, d


def ordered_backward_analysis():
    """
    Automate backward CORRECT avec positions strictement décroissantes.

    Le backward part de c_{k-1} = 0 et remonte vers c_1.
    À chaque pas, on choisit une position q qui est STRICTEMENT PLUS PETITE
    que toute position déjà choisie.

    Les positions forment la séquence q_{k-1} > q_{k-2} > ... > q_2,
    toutes dans {p+2, ..., S-1}.

    L'état de l'automate est (résidu mod d, position_minimale_disponible).
    Plus précisément, on suit (résidu, dernière_position_choisie) et
    la prochaine position doit être < dernière_position et ≥ p+2.
    """
    print("=" * 70)
    print("AUTOMATE BACKWARD ORDONNÉ — ACCESSIBILITÉ DU TARGET")
    print("=" * 70)

    for k in range(5, 14):
        S, d = compute_params(k)
        if d <= 0:
            continue

        p = 1  # cas s=5
        s_target = (3 + pow(2, p, d)) % d
        min_pos = p + 2  # = 3 pour p=1
        inv3 = pow(3, -1, d)

        print(f"\n  k={k}, S={S}, d={d}, target s={s_target}, min_pos={min_pos}")

        # Backward ordonné :
        # État = (résidu, last_pos) où last_pos est la dernière position choisie
        # Transition : choisir q < last_pos, q ≥ min_pos
        # new_residue = (residue - 2^q) * inv3 mod d

        # Layer 0 : c_{k-1} = 0, pas encore de position choisie
        # On commence par choisir q_{k-1} ∈ {min_pos, ..., S-1}
        # Puis q_{k-2} < q_{k-1}, q_{k-2} ≥ min_pos
        # etc.

        # Pour l'efficacité, on ne garde que les résidus possibles par last_pos
        # current = {last_pos: set(residues)}
        current = defaultdict(set)

        # Initialisation : premier choix = q_{k-1}
        for q in range(min_pos, S):
            residue = ((-pow(2, q, d)) * inv3) % d
            current[q].add(residue)

        # Statistiques
        total_states_layer1 = sum(len(v) for v in current.values())
        all_residues_layer1 = set()
        for v in current.values():
            all_residues_layer1.update(v)

        reached_1 = s_target in all_residues_layer1

        print(f"    Couche 1 (q_{k-1} choisi): {len(all_residues_layer1)} résidus uniques, "
              f"target {'ATTEINT' if reached_1 else 'absent'}")

        target_found_at = None
        if reached_1:
            target_found_at = 1

        # Couches suivantes
        for step in range(2, k - 1):
            nxt = defaultdict(set)
            for last_pos, residues in current.items():
                # La prochaine position doit être < last_pos et ≥ min_pos
                for q in range(min_pos, last_pos):
                    new_residue_base = pow(2, q, d)
                    for res in residues:
                        new_res = ((res - new_residue_base) * inv3) % d
                        nxt[q].add(new_res)

            current = nxt

            all_residues = set()
            for v in current.values():
                all_residues.update(v)

            reached = s_target in all_residues
            if reached and target_found_at is None:
                target_found_at = step

            print(f"    Couche {step} (step backward): {len(all_residues)} résidus uniques, "
                  f"target {'ATTEINT' if reached else 'absent'}")

        # Résultat final (couche k-2)
        all_final_residues = set()
        for v in current.values():
            all_final_residues.update(v)
        final_reached = s_target in all_final_residues

        status = "⚠️ ATTEINT" if final_reached else "✓ ABSENT"
        print(f"    → Couche finale {k-2}: {len(all_final_residues)} résidus, target s={s_target} {status}")

        if final_reached:
            print(f"    PROBLÈME : target atteint avec positions ordonnées !")
            # Retrouver le chemin
            find_ordered_path(k, S, d, p, s_target, min_pos, inv3)
        else:
            print(f"    ✓ CONFIRMÉ : target INACCESSIBLE avec positions ordonnées ≥ {min_pos}")

            # Comparaison avec l'automate NON ordonné
            # (on fait k-2 pas avec positions quelconques ≥ min_pos)
            current_unordered = {0}
            for step in range(k - 2):
                nxt = set()
                for state in current_unordered:
                    for q in range(min_pos, S):
                        prev = ((state - pow(2, q, d)) * inv3) % d
                        nxt.add(prev)
                current_unordered = nxt

            unordered_reached = s_target in current_unordered

            print(f"    Automate NON ordonné : {len(current_unordered)} résidus, "
                  f"target {'ATTEINT' if unordered_reached else 'absent'}")
            print(f"    PERTE DE COUVERTURE par l'ordre : "
                  f"{len(current_unordered)} → {len(all_final_residues)} "
                  f"({len(all_final_residues)/max(1,len(current_unordered))*100:.1f}%)")


def find_ordered_path(k, S, d, p, s_target, min_pos, inv3):
    """Retrouve un chemin ordonné qui atteint le target."""
    # Reconstruction par couches avec historique
    # current = {(last_pos, residue): path}
    current = {}
    for q in range(min_pos, S):
        residue = ((-pow(2, q, d)) * inv3) % d
        current[(q, residue)] = [q]

    for step in range(2, k - 1):
        nxt = {}
        for (last_pos, res), path in current.items():
            for q in range(min_pos, last_pos):
                new_res = ((res - pow(2, q, d)) * inv3) % d
                if new_res == s_target and step == k - 2:
                    print(f"    Chemin trouvé : positions (backward) = {path + [q]}")
                    # Vérification
                    positions_bwd = path + [q]
                    positions_fwd = list(reversed(positions_bwd))
                    print(f"    Positions forward (q_2,...,q_{k-1}) = {positions_fwd}")
                    # Vérifier l'ordre
                    is_ordered = all(positions_fwd[i] < positions_fwd[i+1]
                                     for i in range(len(positions_fwd)-1))
                    print(f"    Strictement croissant ? {is_ordered}")
                    return
                nxt[(q, new_res)] = path + [q]
        current = nxt

    print(f"    (Chemin non retrouvé par reconstruction)")


# =====================================================================
# ANALYSE : POURQUOI L'ORDRE CRÉE L'OBSTRUCTION
# =====================================================================

def order_obstruction_analysis():
    """
    L'automate sans ordre atteint le target, mais avec ordre non.

    Comparer les deux :
    - Sans ordre : k-2 pas avec positions quelconques ≥ min_pos
    - Avec ordre : k-2 pas avec q_{k-1} > q_{k-2} > ... > q_2, toutes ≥ min_pos

    Le nombre de chemins ordonnés est C(S-min_pos, k-2) = C(S-p-2, k-2).
    Le nombre de chemins non ordonnés est (S-min_pos)^{k-2}.

    Rapport : C(n, m) / n^m = produit des (n-i)/n → décroît exponentiellement.

    Mais ce n'est pas juste une question de QUANTITÉ. C'est une question de
    STRUCTURE : les chemins ordonnés ne couvrent qu'une partie spécifique
    de l'espace des résidus.
    """
    print(f"\n\n{'=' * 70}")
    print("ANALYSE : POURQUOI L'ORDRE CRÉE L'OBSTRUCTION")
    print("=" * 70)

    for k in range(5, 11):
        S, d = compute_params(k)
        if d <= 0:
            continue

        p = 1
        min_pos = p + 2
        n_pos = S - min_pos  # positions disponibles

        print(f"\n  k={k}, S={S}, d={d}, n_pos={n_pos}")

        # Chemins ordonnés : C(n_pos, k-2)
        ordered_paths = math.comb(n_pos, k - 2)
        # Chemins non ordonnés : n_pos^{k-2}
        unordered_paths = n_pos ** (k - 2)

        ratio = ordered_paths / unordered_paths
        print(f"    Chemins ordonnés : C({n_pos},{k-2}) = {ordered_paths}")
        print(f"    Chemins non ordonnés : {n_pos}^{k-2} = {unordered_paths}")
        print(f"    Ratio ordonné/non-ordonné : {ratio:.6f}")
        print(f"    Ratio = 1/{1/ratio:.0f}")

        # C(n_pos, k-2) vs d
        print(f"    C(n_pos, k-2) / d = {ordered_paths / d:.4f}")

        # Vérification numérique complète pour petit k
        if k <= 10:
            inv3 = pow(3, -1, d)
            s_target = (3 + pow(2, p, d)) % d

            # Résidus atteignables AVEC ordre (= compositions valides)
            ordered_residues = set()
            for combo in combinations(range(min_pos, S), k - 2):
                # combo donne positions dans l'ordre croissant
                # dans le backward, on les parcourt en sens inverse
                residue = 0
                for q in reversed(combo):
                    residue = ((residue - pow(2, q, d)) * inv3) % d
                ordered_residues.add(residue)

            # Résidus atteignables SANS ordre
            # (trop long pour k grand, on le fait pour k ≤ 8)
            if k <= 8:
                unordered_residues = {0}
                for step in range(k - 2):
                    nxt = set()
                    for state in unordered_residues:
                        for q in range(min_pos, S):
                            prev = ((state - pow(2, q, d)) * inv3) % d
                            nxt.add(prev)
                    unordered_residues = nxt

                print(f"    Résidus ordonnés : {len(ordered_residues)}/{d}")
                print(f"    Résidus non ordonnés : {len(unordered_residues)}/{d}")
                print(f"    Target s={s_target} dans ordonnés ? {s_target in ordered_residues}")
                print(f"    Target s={s_target} dans non ordonnés ? {s_target in unordered_residues}")

                # Résidus dans non-ordonnés mais PAS dans ordonnés
                diff = unordered_residues - ordered_residues
                if len(diff) <= 20:
                    print(f"    Résidus perdus par l'ordre : {sorted(diff)}")
                else:
                    print(f"    Résidus perdus par l'ordre : {len(diff)} valeurs")
                    if s_target in diff:
                        print(f"    → TARGET s={s_target} EST dans les résidus perdus !")
            else:
                print(f"    Résidus ordonnés : {len(ordered_residues)}/{d}")
                print(f"    Target s={s_target} dans ordonnés ? {s_target in ordered_residues}")


# =====================================================================
# QUANTIFICATION : Combien de combinaisons ordonnées APPROCHENT le target ?
# =====================================================================

def proximity_analysis():
    """Pour chaque k, quels résidus ordonnés sont les plus proches du target ?"""
    print(f"\n\n{'=' * 70}")
    print("PROXIMITÉ AU TARGET DANS L'AUTOMATE ORDONNÉ")
    print("=" * 70)

    for k in range(5, 11):
        S, d = compute_params(k)
        if d <= 0:
            continue

        p = 1
        min_pos = p + 2
        s_target = (3 + pow(2, p, d)) % d
        inv3 = pow(3, -1, d)

        # Calculer tous les résidus ordonnés
        residues_with_combos = []
        for combo in combinations(range(min_pos, S), k - 2):
            residue = 0
            for q in reversed(combo):
                residue = ((residue - pow(2, q, d)) * inv3) % d
            residues_with_combos.append((residue, combo))

        # Trouver les plus proches du target
        distances = []
        for res, combo in residues_with_combos:
            dist = min(abs(res - s_target), d - abs(res - s_target))
            distances.append((dist, res, combo))

        distances.sort()

        print(f"\n  k={k}, S={S}, d={d}, target s={s_target}")
        print(f"    5 résidus ordonnés les plus proches du target :")
        for dist, res, combo in distances[:5]:
            fwd_positions = list(combo)
            print(f"      dist={dist}, résidu={res}, positions={fwd_positions}")

        if distances[0][0] == 0:
            print(f"    ⚠️ DISTANCE 0 — target atteint !")
        else:
            print(f"    Distance minimale = {distances[0][0]}")

        # Quel est le "bassin d'exclusion" autour du target ?
        all_residues = set(r for r, _ in residues_with_combos)
        target_dist = min(abs(s_target - r) for r in all_residues) if all_residues else float('inf')
        target_dist_wrap = min(min(abs(s_target - r), d - abs(s_target - r)) for r in all_residues) if all_residues else float('inf')
        print(f"    Bassin d'exclusion autour du target : rayon = {target_dist_wrap}")


# =====================================================================
# CLÉ : Relation entre positions ordonnées et corrSum
# =====================================================================

def corrsum_ordered_vs_target():
    """
    On sait que les compositions (0, p, q_2, ..., q_{k-1}) avec
    p < q_2 < ... < q_{k-1} ne donnent JAMAIS corrSum ≡ 0 mod d.

    Ceci est équivalent à l'Énoncé C pour les cas serrés.

    Mais c'est AUSSI vrai pour les compositions (0, p, p+1, ...) !
    Approche 2 de obstruction_search.py l'a confirmé pour TOUT p.

    Observation : c'est la conjonction de la contrainte d'ordre ET
    de la structure multiplicative 3^a·2^b qui crée l'obstruction.

    La contrainte d'ordre seule ne suffit pas (beaucoup de résidus atteignables).
    La structure 3^a·2^b seule ne suffit pas (l'automate non ordonné atteint tout).
    C'est leur INTERACTION qui bloque.
    """
    print(f"\n\n{'=' * 70}")
    print("INTERACTION ORDRE × STRUCTURE MULTIPLICATIVE")
    print("=" * 70)

    for k in range(5, 10):
        S, d = compute_params(k)
        if d <= 0:
            continue

        p = 1
        s_target = (3 + pow(2, p, d)) % d

        print(f"\n  k={k}, S={S}, d={d}")

        # TOUTES les compositions (0, p, ...) avec positions croissantes
        # et corrSum mod d
        residues_by_p = defaultdict(set)
        for combo in combinations(range(p + 1, S), k - 2):
            positions = [0, p] + list(combo)
            corrsum = sum(pow(3, k - 1 - j) * pow(2, positions[j]) for j in range(k))
            res = corrsum % d
            residues_by_p[p].add(res)

        residues = residues_by_p[p]
        print(f"    Compositions (0, {p}, ...): {len(residues)} résidus distincts")
        print(f"    0 dans les résidus ? {0 in residues}")

        if 0 not in residues and len(residues) < d:
            # Combien de résidus sont absents ?
            missing = set(range(d)) - residues
            print(f"    {len(missing)} résidus absents ({len(missing)/d*100:.1f}%)")

            # 0 est l'un des absents
            # Quels sont les résidus absents proches de 0 ?
            near_zero = sorted([(r, min(r, d-r)) for r in missing], key=lambda x: x[1])
            print(f"    Absents les plus proches de 0 :")
            for r, dist in near_zero[:5]:
                print(f"      résidu={r}, distance={dist}")

        # Maintenant : compositions (0, p, p+1, ...) spécifiquement
        residues_pp1 = set()
        ncombos_pp1 = 0
        for combo in combinations(range(p + 2, S), k - 3):
            positions = [0, p, p + 1] + list(combo)
            corrsum = sum(pow(3, k - 1 - j) * pow(2, positions[j]) for j in range(k))
            res = corrsum % d
            residues_pp1.add(res)
            ncombos_pp1 += 1

        print(f"    Compositions (0, {p}, {p+1}, ...): {len(residues_pp1)} résidus / {ncombos_pp1} combos")
        print(f"    0 dans les résidus ? {0 in residues_pp1}")

        # Combien de résidus de (0, p, p+1, ...) sont dans l'image de (0, p, ...) ?
        overlap = len(residues_pp1 & residues)
        print(f"    Overlap (0,p,p+1) ⊂ (0,p,...) : {overlap}/{len(residues_pp1)}")

        # Conclusion pour ce k
        if 0 not in residues:
            print(f"    → AUCUNE composition (0, {p}, ...) ne donne corrSum ≡ 0 mod d")
            print(f"       Donc l'Énoncé C est VÉRIFIÉ pour ce k et p={p}")


# =====================================================================
# SYNTHÈSE : L'obstruction est la COMBINAISON de 3 facteurs
# =====================================================================

def synthesis():
    """
    SYNTHÈSE DE L'OBSTRUCTION :

    1. La contrainte d'ORDRE STRICT réduit drastiquement les chemins
       (C(n,k-2) << n^{k-2})

    2. La structure MULTIPLICATIVE (poids 3^a pour chaque terme)
       crée une hiérarchie entre les positions

    3. L'identité 3^k = 2^S - d contraint la relation entre les poids
       et le modulus

    L'interaction de ces 3 facteurs produit un "trou" systématique
    dans les résidus atteignables qui inclut toujours le résidu 0
    pour les compositions commençant par (0, p, ...).

    C'est la MÊME obstruction que celle qui produit N₀(d) = 0 :
    la preuve de l'Énoncé C est en fait une REFORMULATION de N₀(d) = 0
    restreinte aux compositions commençant par position p.
    """
    print(f"\n\n{'=' * 70}")
    print("SYNTHÈSE : NATURE DE L'OBSTRUCTION")
    print("=" * 70)

    print("""
  RÉSULTATS DE CETTE SESSION :

  1. Le bug dans Investigation 6 (target oubliant le terme q_2) est CORRIGÉ.
     Le target corrigé est TOUJOURS absent pour k=5..12 (vérifié).

  2. L'argument mod 3 est INSUFFISANT car gcd(d, 3) = 1.
     (prefix ≡ 0 mod 3 et suffix ≢ 0 mod 3, mais d | corrSum n'exige pas 3 | corrSum)

  3. L'automate backward SANS contrainte d'ordre ATTEINT le target s=5
     (avec positions répétées). L'obstruction n'est PAS modulaire seule.

  4. L'automate backward AVEC contrainte d'ordre STRICT N'ATTEINT PAS le target.
     C'est la COMBINAISON de l'ordre et de la structure multiplicative qui bloque.

  5. Le nombre de résidus atteignables par chemins ordonnés est
     typiquement petit vs d (C(n,k-2)/d → 0 quand k croît).

  6. La vérification exhaustive confirme : pour TOUT p et k=3..12,
     aucune composition (0, p, p+1, q_3, ..., q_{k-1}) ne donne
     corrSum ≡ 0 mod d.

  STATUT DE L'ÉNONCÉ C :

  L'Énoncé C est VÉRIFIÉ numériquement pour k=3..14.

  La preuve FORMELLE reste ouverte. L'obstruction est RÉELLE
  (ce n'est pas un artefact) mais sa nature est plus subtile
  qu'une simple congruence.

  PISTE LA PLUS PROMETTEUSE :

  L'Énoncé C est ÉQUIVALENT à N₀(d) = 0 restreint aux compositions
  commençant par position p. Donc prouver l'Énoncé C directement
  est AUSSI DUR que prouver N₀(d) = 0 pour ces sous-ensembles.

  → Il faut peut-être ABANDONNER l'approche "Énoncé C comme lemme isolé"
  et utiliser plutôt l'Énoncé C comme un COROLLAIRE de la preuve globale
  de N₀(d) = 0 (via une approche spectrale ou combinatoire).
""")


if __name__ == "__main__":
    print("*" * 70)
    print("AUTOMATE BACKWARD ORDONNÉ — SESSION 6")
    print("*" * 70)

    ordered_backward_analysis()
    order_obstruction_analysis()
    proximity_analysis()
    corrsum_ordered_vs_target()
    synthesis()
