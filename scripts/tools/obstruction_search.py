#!/usr/bin/env python3
"""
RECHERCHE DE L'OBSTRUCTION RÉELLE — Session 6
==============================================

L'argument mod 3 est INSUFFISANT car gcd(d, 3) = 1.
Il faut trouver la VRAIE raison pour laquelle le target est toujours absent
de l'ensemble des résidus atteignables par le suffixe.

Approches :
1. Analyser la TAILLE du suffixe exact (pas mod d) vs la taille de d
2. Chercher des contraintes CUMULATIVES (mod 2, mod 3, mod 6, etc.)
3. Étudier la structure de l'automate backward restreint
4. Vérifier si l'obstruction est liée à l'Énoncé B (pigeonhole)
"""

import math
from itertools import combinations
from collections import defaultdict


def compute_params(k):
    S = math.ceil(k * math.log2(3))
    d = (1 << S) - 3**k
    return S, d


# =====================================================================
# APPROCHE 1 : Analyse de TAILLE — le corrSum est-il trop petit/grand pour être ≡ 0 mod d ?
# =====================================================================

def size_analysis():
    """
    L'Énoncé C est équivalent à : aucune composition (0, p, p+1, q_3, ..., q_{k-1})
    ne donne corrSum ≡ 0 mod d.

    corrSum exact = 3^{k-1} + 3^{k-2}·2^p + 3^{k-3}·2^{p+1} + Σ_{j=3}^{k-1} 3^{k-1-j}·2^{q_j}

    La question est : existe-t-il un entier n₀ ≥ 1 tel que corrSum = n₀·d ?

    Pour cela, corrSum doit être un MULTIPLE de d dans l'intervalle [corrSum_min, corrSum_max].
    """
    print("=" * 70)
    print("APPROCHE 1 : ANALYSE DE TAILLE (INTERVALLE)")
    print("=" * 70)

    for k in range(5, 15):
        S, d = compute_params(k)
        if d <= 0:
            continue

        for p in [1]:  # cas universel s=5
            # Prefix exact : 3^{k-1} + 3^{k-2}·2^p + 3^{k-3}·2^{p+1}
            prefix = 3**(k-1) + 3**(k-2) * 2**p + 3**(k-3) * 2**(p+1)

            # Suffix min : positions les plus PETITES (p+2, p+3, ..., p+k-2)
            suffix_min = sum(3**(k-1-(3+idx)) * 2**(p+2+idx) for idx in range(k-3))

            # Suffix max : positions les plus GRANDES (S-k+3, S-k+4, ..., S-1)
            top_positions = list(range(S - (k-3), S))
            if top_positions and top_positions[0] > p + 1:
                suffix_max = sum(3**(k-1-(3+idx)) * 2**top_positions[idx]
                                 for idx in range(k-3))
            else:
                suffix_max = suffix_min  # fallback

            corrsum_min = prefix + suffix_min
            corrsum_max = prefix + suffix_max

            # Multiples de d dans l'intervalle
            n_min = corrsum_min // d + (1 if corrsum_min % d != 0 else 0)
            n_max = corrsum_max // d

            num_multiples = max(0, n_max - n_min + 1)

            print(f"\n  k={k}, S={S}, d={d}, p={p}")
            print(f"    prefix = {prefix}")
            print(f"    suffix ∈ [{suffix_min}, {suffix_max}]")
            print(f"    corrSum ∈ [{corrsum_min}, {corrsum_max}]")
            print(f"    taille_intervalle = {corrsum_max - corrsum_min}")
            print(f"    d = {d}")
            print(f"    Ratio intervalle/d = {(corrsum_max - corrsum_min) / d:.2f}")
            print(f"    Multiples de d dans l'intervalle : n ∈ [{n_min}, {n_max}] → {num_multiples}")

            if num_multiples == 0:
                print(f"    ★ AUCUN multiple de d ! Obstruction par la TAILLE !")
            elif num_multiples == 1:
                n0 = n_min
                target_corrsum = n0 * d
                target_suffix = target_corrsum - prefix
                print(f"    Un seul multiple : n₀={n0}, corrSum={target_corrsum}")
                print(f"    Suffix requis = {target_suffix}")
                print(f"    = {target_suffix} mod d = {target_suffix % d}")

                # Ce suffix est-il réalisable ?
                # suffix = Σ 3^{k-4-idx}·2^{q_{3+idx}} avec q positifs distincts > p+1
                # suffix exact ∈ [suffix_min, suffix_max]
                if suffix_min <= target_suffix <= suffix_max:
                    print(f"    Suffix requis est dans l'intervalle ✓ (mais peut ne pas être atteignable)")
                else:
                    print(f"    ★ Suffix requis HORS de l'intervalle ! Obstruction par taille !")
            else:
                # Plusieurs multiples possibles
                targets = [n * d for n in range(n_min, min(n_max + 1, n_min + 5))]
                print(f"    Premiers multiples : {targets[:5]}")
                for n0 in range(n_min, min(n_max + 1, n_min + 5)):
                    target_suffix = n0 * d - prefix
                    print(f"      n₀={n0}: suffix requis = {target_suffix}, mod d = {target_suffix % d}")


# =====================================================================
# APPROCHE 2 : Vérification que TOUTES les compositions (0, p, p+1, ...) échouent
# =====================================================================

def verify_all_compositions_fail():
    """Pour petit k, vérifier EXHAUSTIVEMENT que corrSum ≠ 0 mod d pour (0, p, p+1, ...)."""
    print(f"\n\n{'=' * 70}")
    print("APPROCHE 2 : VÉRIFICATION EXHAUSTIVE (0, p, p+1, ...)")
    print("=" * 70)

    for k in range(3, 13):
        S, d = compute_params(k)
        if d <= 0:
            continue

        print(f"\n  k={k}, S={S}, d={d}")

        for p in range(1, S - 1):
            if p + 1 >= S:
                continue

            # Positions : (0, p, p+1, q_3, ..., q_{k-1}) avec q_3 > p+1
            num_extra = k - 3
            avail = list(range(p + 2, S))

            if len(avail) < num_extra:
                continue
            if num_extra < 0:
                continue

            if num_extra == 0:
                # Pas de suffix — corrSum = prefix seulement
                positions = [0, p, p + 1]
                if len(positions) == k:
                    corrsum = sum(3**(k-1-j) * 2**positions[j] for j in range(k))
                    if corrsum % d == 0:
                        print(f"    ⚠️ p={p}: corrSum={corrsum} ≡ 0 mod {d} ! VIOLATION !")
                continue

            ncombos = math.comb(len(avail), num_extra)
            if ncombos > 2_000_000:
                continue

            found = False
            for combo in combinations(avail, num_extra):
                positions = [0, p, p + 1] + list(combo)
                corrsum = sum(3**(k-1-j) * 2**positions[j] for j in range(k))
                if corrsum % d == 0:
                    print(f"    ⚠️ p={p}: positions={positions}, corrSum={corrsum} ≡ 0 ! VIOLATION !")
                    found = True
                    break

            if not found and ncombos <= 100000:
                s = (3 + pow(2, p, d)) % d
                print(f"    p={p} (s={s}): 0/{ncombos} compositions donnent corrSum ≡ 0 ✓")


# =====================================================================
# APPROCHE 3 : Quel est le n₀ le plus proche et pourquoi est-il évité ?
# =====================================================================

def closest_multiple_analysis():
    """Pour chaque k, trouver le multiple de d le plus proche du corrSum et analyser l'écart."""
    print(f"\n\n{'=' * 70}")
    print("APPROCHE 3 : MULTIPLES DE d LES PLUS PROCHES")
    print("=" * 70)

    for k in range(5, 13):
        S, d = compute_params(k)
        if d <= 0:
            continue

        p = 1  # cas s=5

        num_terms = k - 3
        avail = list(range(p + 2, S))

        if len(avail) < num_terms or num_terms <= 0:
            continue

        ncombos = math.comb(len(avail), num_terms)
        if ncombos > 500000:
            continue

        min_residue = d
        closest_combo = None
        all_residues = []

        for combo in combinations(avail, num_terms):
            positions = [0, p, p + 1] + list(combo)
            corrsum = sum(3**(k-1-j) * 2**positions[j] for j in range(k))
            residue = corrsum % d
            all_residues.append(residue)

            if residue != 0:
                dist = min(residue, d - residue)
                if dist < min_residue:
                    min_residue = dist
                    closest_combo = (positions, corrsum, residue)

        # Nombre de résidus distincts
        unique_residues = set(all_residues)

        print(f"\n  k={k}, S={S}, d={d}, p=1")
        print(f"    {ncombos} compositions, {len(unique_residues)} résidus distincts")
        print(f"    Distance minimale au multiple de d : {min_residue}")
        if closest_combo:
            pos, cs, res = closest_combo
            n0_below = cs // d
            print(f"    Plus proche : positions={pos}")
            print(f"      corrSum = {cs}, residue = {res}")
            print(f"      n₀ en dessous = {n0_below}, excès = {cs - n0_below * d}")
            print(f"      n₀ au dessus = {n0_below + 1}, déficit = {(n0_below + 1) * d - cs}")

        # La distribution des résidus est-elle "loin" de 0 ?
        # Calculer la distance moyenne à 0
        distances = [min(r, d - r) for r in all_residues if r != 0]
        avg_dist = sum(distances) / len(distances) if distances else 0
        expected_avg = d / 4  # distance moyenne attendue pour distribution uniforme

        print(f"    Distance moyenne à 0 : {avg_dist:.1f} (attendue si uniforme : {expected_avg:.1f})")
        print(f"    Ratio : {avg_dist / expected_avg:.2f}")


# =====================================================================
# APPROCHE 4 : Énoncé C direct via l'automate Horner restreint
# =====================================================================

def horner_automaton_analysis():
    """
    L'automate de Horner backward restreint aux positions ≥ p+2.

    Question : l'état s = 3+2^p est-il STRUCTURELLEMENT inaccessible
    depuis l'état 0 en k-2 pas avec positions toutes ≥ p+2 ?

    Approche : construire le graphe d'accessibilité restreint.
    """
    print(f"\n\n{'=' * 70}")
    print("APPROCHE 4 : AUTOMATE HORNER RESTREINT")
    print("=" * 70)

    for k in range(5, 13):
        S, d = compute_params(k)
        if d <= 0:
            continue

        p = 1  # cas s=5
        s_target = (3 + pow(2, p, d)) % d

        inv3 = pow(3, -1, d)

        # Backward restreint : positions ≥ p+2
        min_pos = p + 2

        # États atteignables à chaque couche
        current_states = {0}
        print(f"\n  k={k}, S={S}, d={d}, target s={s_target}")

        for step in range(1, k - 1):
            next_states = set()
            for state in current_states:
                for q in range(min_pos, S):
                    prev = ((state - pow(2, q, d)) * inv3) % d
                    next_states.add(prev)

            reached = s_target in next_states
            print(f"    Couche {step}: {len(next_states)} états "
                  f"(target {'ATTEINT' if reached else 'absent'})")
            current_states = next_states

            if reached:
                print(f"    ⚠️ Target atteint à la couche {step} !")
                # Mais on a besoin d'exactement k-2 couches
                break

        final_reached = s_target in current_states
        print(f"    Couche finale {k-2}: target s={s_target} {'⚠️ ATTEINT' if final_reached else '✓ ABSENT'}")

        if not final_reached:
            # L'état s n'est PAS atteignable — c'est l'obstruction !
            # Combien d'états sont atteignables vs total ?
            print(f"    États atteignables au final : {len(current_states)}/{d} ({len(current_states)/d*100:.1f}%)")

            # Les états NON atteignables forment un ensemble structuré ?
            unreachable = set(range(d)) - current_states
            if len(unreachable) <= 30:
                print(f"    États NON atteignables : {sorted(unreachable)}")

        else:
            # Retrouver le chemin
            print(f"    Backtracking pour trouver le chemin...")
            # Reconstruire
            layers = [{0}]
            for step in range(1, k - 1):
                nxt = set()
                for state in layers[-1]:
                    for q in range(min_pos, S):
                        prev = ((state - pow(2, q, d)) * inv3) % d
                        nxt.add(prev)
                layers.append(nxt)

            # Trouver un chemin qui atteint s_target
            path = [s_target]
            current = s_target
            for step in range(k - 2, 0, -1):
                found_q = None
                for q in range(min_pos, S):
                    nxt = (3 * current + pow(2, q, d)) % d
                    if nxt in layers[step - 1]:
                        found_q = q
                        current = nxt
                        break
                if found_q is not None:
                    path.append(found_q)

            path.reverse()
            print(f"    Chemin trouvé : {path}")


# =====================================================================
# APPROCHE 5 : Relation entre l'Énoncé C et la congruence 3^k ≡ 2^S mod d
# =====================================================================

def structural_relation():
    """
    L'identité fondamentale : 3^k = 2^S - d, donc 3^k ≡ 2^S mod d.

    Pour la composition (0, p, p+1, q_3, ..., q_{k-1}) :
    corrSum = Σ 3^{k-1-j}·2^{p_j}

    Utilisons la substitution 3^a = 3^{a-k}·2^S mod d (valide car 3^k ≡ 2^S) :

    Pour j ≤ k-1 : 3^{k-1-j} reste "positif" (pas de substitution nécessaire).
    Le terme j=0 : 3^{k-1}·2^0 = 3^{k-1}
    Le terme j=1 : 3^{k-2}·2^p
    Le terme j=2 : 3^{k-3}·2^{p+1}

    corrSum = 3^{k-1} + 3^{k-2}·2^p + 3^{k-3}·2^{p+1} + suffix

    Factorisons 3^{k-3} :
    corrSum = 3^{k-3}(9 + 3·2^p + 2^{p+1}) + suffix
            = 3^{k-3}(9 + 5·2^p) + suffix

    Pour corrSum ≡ 0 mod d :
    suffix ≡ -(9+5·2^p)·3^{k-3} mod d

    Utilisant 3^{k-3} = 3^{-3}·3^k = 3^{-3}·(2^S - d) ≡ (2^S)/27 mod d :

    target ≡ -(9+5·2^p)·2^S/27 mod d
           = -(9+5·2^p)/27 · 2^S mod d

    Or (9+5·2^p)/27... n'est pas un entier en général. Mais mod d :
    target = -(9+5·2^p) · inv(27) · 2^S mod d

    Le facteur 2^S mod d = 3^k mod d. Donc :
    target = -(9+5·2^p) · inv(27) · 3^k mod d
           = -(9+5·2^p) · 3^{k-3} mod d  (car inv(27)·3^k = 3^{k-3})

    C'est juste une reformulation circulaire. Essayons autre chose.
    """
    print(f"\n\n{'=' * 70}")
    print("APPROCHE 5 : STRUCTURE VIA 3^k ≡ 2^S mod d")
    print("=" * 70)

    for k in range(5, 13):
        S, d = compute_params(k)
        if d <= 0:
            continue

        p = 1

        inv3 = pow(3, -1, d)
        inv27 = pow(27, -1, d)

        target = (-(9 + 5 * pow(2, p, d)) * pow(3, k-3, d)) % d

        # Réécriture : target = -(9+5·2^p)·3^{k-3} mod d
        # = -(9+10)·3^{k-3} = -19·3^{k-3} mod d (pour p=1)

        # Le suffix = Σ_{j=3}^{k-1} 3^{k-1-j}·2^{q_j} avec q_j ≥ 3
        # Notons h_j = q_j - (p+2) ≥ 0, et h_j strictement croissant
        # Alors q_j = h_j + p + 2 = h_j + 3 (pour p=1)
        # suffix = Σ 3^{k-4-i}·2^{h_i+3} = 8·Σ 3^{k-4-i}·2^{h_i}
        # Avec h_0 ≥ 0, h_1 ≥ 1, ..., h_{k-4} ≥ k-4 (positions à translation)

        # Le suffix est donc 2^{p+2} · Σ 3^{k-4-i}·2^{h_i}
        # = 2^3 · (mini-corrSum avec k-3 termes et positions h_i ∈ {0,...,S-p-3})

        # DONC : suffix = 8 · miniCS
        # Et target = -19·3^{k-3} mod d

        # Pour suffix = target mod d : 8·miniCS ≡ -19·3^{k-3} mod d
        # miniCS ≡ -19·3^{k-3}·inv(8) mod d

        inv8 = pow(8, -1, d)
        mini_target = (-19 * pow(3, k-3, d) * inv8) % d

        # Nombre de positions disponibles pour mini
        num_terms = k - 3
        num_positions = S - (p + 2)  # positions 0,...,S-p-3

        print(f"\n  k={k}, S={S}, d={d}, p=1")
        print(f"    suffix = 8 · miniCS, miniCS = Σ 3^{{k-4-i}}·2^{{h_i}}")
        print(f"    h_i ∈ {{0,...,{num_positions-1}}}, {num_terms} termes")
        print(f"    mini_target = -19·3^{{k-3}}·8^{{-1}} mod d = {mini_target}")

        # Le miniCS a la MÊME structure que corrSum mais avec k-3 termes !
        # C'est un "sous-corrSum" de dimension k-3.

        # Observation : le miniCS est en fait corrSum pour un problème
        # de dimension k-3 dans un modulus d. La proportion de résidus
        # atteignables est C(n, k-3)/d avec n = S-p-2.

        ratio = math.comb(num_positions, num_terms) / d
        print(f"    C({num_positions}, {num_terms}) / d = {math.comb(num_positions, num_terms)} / {d} = {ratio:.4f}")

        if ratio < 1:
            print(f"    Ratio < 1 → la couverture est INCOMPLÈTE → normal que le target soit absent")
        else:
            print(f"    Ratio ≥ 1 → la couverture POURRAIT être complète")


# =====================================================================
# APPROCHE 6 : L'obstruction est-elle simplement que C(n, k-3)/d < 1 ?
# =====================================================================

def coverage_analysis():
    """
    Hypothèse : le target est absent simplement parce que le suffixe
    ne couvre qu'une fraction C(S-p-2, k-3)/d des résidus mod d,
    et cette fraction est si petite que les résidus évités sont "aléatoires"
    — mais le target est SYSTÉMATIQUEMENT parmi les évités.

    Ou bien : le nombre de combinaisons C est si petit que beaucoup de
    résidus sont absents, et le target est l'un d'entre eux par STRUCTURE,
    pas par hasard.

    Test : si on choisit un résidu ALÉATOIRE, quelle est la probabilité
    qu'il soit dans l'ensemble atteignable ?
    """
    print(f"\n\n{'=' * 70}")
    print("APPROCHE 6 : COUVERTURE vs TAILLE")
    print("=" * 70)

    for k in range(5, 15):
        S, d = compute_params(k)
        if d <= 0:
            continue

        p = 1  # cas s=5

        num_terms = k - 3
        num_positions = S - (p + 2)

        if num_terms <= 0 or num_positions < num_terms:
            continue

        C = math.comb(num_positions, num_terms)

        # Probabilité "aléatoire" qu'un résidu soit absent
        # Si les C combinaisons étaient indépendantes et uniformes :
        # P(résidu absent) ≈ (1 - 1/d)^C ≈ exp(-C/d)
        prob_absent = (1 - 1/d)**C if d > 1 else 0
        expected_absent = d * prob_absent

        print(f"\n  k={k}, S={S}, d={d}")
        print(f"    C({num_positions}, {num_terms}) = {C}")
        print(f"    C/d = {C/d:.4f}")
        print(f"    P(résidu absent, modèle aléatoire) ≈ {prob_absent:.4e}")
        print(f"    Nombre attendu de résidus absents ≈ {expected_absent:.1f}")

        # Vérification numérique pour petit k
        if k <= 10:
            avail = list(range(p + 2, S))
            suffix_vals = set()
            for combo in combinations(avail, num_terms):
                val = sum(pow(3, k - 1 - (3 + idx), d) * pow(2, combo[idx], d)
                          for idx in range(num_terms)) % d
                suffix_vals.add(val)

            actual_absent = d - len(suffix_vals)
            target = (-(9 + 5 * pow(2, p, d)) * pow(3, k-3, d)) % d

            print(f"    Résidus absents réels : {actual_absent}")
            print(f"    Target {target} absent : {target not in suffix_vals}")

            # Le target est-il "spécial" parmi les absents ?
            # Test : combien de fois le target apparaîtrait comme absent
            # si on tirait C résidus aléatoires ?
            if actual_absent > 0:
                print(f"    Fraction absente : {actual_absent}/{d} = {actual_absent/d*100:.1f}%")
                print(f"    Si uniforme, P(target absent) = {actual_absent/d:.4f}")

                # C'est bien plus qu'aléatoire !
                # L'absence est structurelle, pas aléatoire.


# =====================================================================
# APPROCHE 7 : L'obstruction par CORRSUM TOTAL
# =====================================================================

def corrsum_total_analysis():
    """
    Au lieu de regarder le suffixe séparément, regardons corrSum = prefix + suffix
    en tant qu'ENTIER. Pour corrSum ≡ 0 mod d, il faut corrSum = n₀·d.

    n₀ est l'élément minimal du cycle hypothétique.

    Contrainte : n₀ ≥ 1 (cycle non trivial).
    corrSum = prefix + suffix = n₀·d.
    Donc suffix = n₀·d - prefix.

    Le suffix est une somme de k-3 termes 3^{k-4-i}·2^{q_{3+i}}.
    Chaque terme est positif. Donc suffix > 0.
    Et suffix < 3^{k-4}·2^{S-1} + ... (borné).

    La question : existe-t-il n₀ ≥ 1 tel que n₀·d - prefix soit dans
    l'intervalle [suffix_min, suffix_max] ET soit réalisable comme somme ?
    """
    print(f"\n\n{'=' * 70}")
    print("APPROCHE 7 : ANALYSE PAR n₀ (ENTIER)")
    print("=" * 70)

    for k in range(5, 15):
        S, d = compute_params(k)
        if d <= 0:
            continue

        p = 1
        prefix = 3**(k-1) + 3**(k-2) * 2**p + 3**(k-3) * 2**(p+1)

        # Suffix bounds
        min_positions = list(range(p+2, p+2+(k-3)))
        max_positions = list(range(S-(k-3), S))

        if min_positions[-1] >= S or max_positions[0] <= p+1:
            continue

        suffix_min = sum(3**(k-1-(3+i)) * 2**min_positions[i] for i in range(k-3))
        suffix_max = sum(3**(k-1-(3+i)) * 2**max_positions[i] for i in range(k-3))

        corrsum_min = prefix + suffix_min
        corrsum_max = prefix + suffix_max

        n_min = math.ceil(corrsum_min / d)
        n_max = math.floor(corrsum_max / d)

        print(f"\n  k={k}, S={S}, d={d}, p=1")
        print(f"    prefix = {prefix} = 19·3^{k-3} = {19 * 3**(k-3)}")
        print(f"    suffix ∈ [{suffix_min}, {suffix_max}]")
        print(f"    corrSum ∈ [{corrsum_min}, {corrsum_max}]")
        print(f"    n₀ candidats : [{n_min}, {n_max}] → {n_max - n_min + 1} valeur(s)")

        for n0 in range(n_min, min(n_max + 1, n_min + 10)):
            required_suffix = n0 * d - prefix
            if required_suffix < suffix_min or required_suffix > suffix_max:
                print(f"      n₀={n0}: suffix={required_suffix} HORS intervalle")
                continue

            # Le suffix requis est dans l'intervalle. Est-il réalisable ?
            print(f"      n₀={n0}: suffix_requis={required_suffix}, dans [{suffix_min}, {suffix_max}]")

            # Vérification mod 3 de corrSum
            corrsum = n0 * d
            corrsum_mod3 = corrsum % 3

            # d mod 3 = (2^S - 3^k) mod 3 = ((-1)^S) mod 3 (car 3^k ≡ 0 mod 3)
            d_mod3 = pow(-1, S, 3)  # Actually: pow(2, S, 3)
            d_mod3 = pow(2, S, 3)

            print(f"        d mod 3 = {d_mod3}")
            print(f"        corrSum = n₀·d, corrSum mod 3 = {n0 % 3}·{d_mod3} mod 3 = {(n0 * d_mod3) % 3}")

            # corrSum mod 2 = 1 (Remark 2.5)
            # n₀·d mod 2 = ? d est impair. Donc n₀·d mod 2 = n₀ mod 2.
            # Pour corrSum impair : n₀ doit être IMPAIR.
            if n0 % 2 == 0:
                print(f"        n₀ est pair → corrSum serait pair → contradiction avec corrSum impair !")
                continue

            # corrSum mod 3 ∈ {1, 2} (Remark 2.5 — corrSum ≢ 0 mod 3)
            corrsum_mod3 = (n0 * d) % 3
            if corrsum_mod3 == 0:
                print(f"        corrSum ≡ 0 mod 3 → contradiction avec corrSum ≢ 0 mod 3 !")
                print(f"        ★ OBSTRUCTION : n₀·d ≡ 0 mod 3 pour ce n₀ !")
                continue

            print(f"        Contraintes mod 2 et mod 3 satisfaites, n₀ possible.")

            # Vérification numérique pour petit k
            if k <= 10:
                avail = list(range(p+2, S))
                num_terms = k - 3
                found = False
                for combo in combinations(avail, num_terms):
                    val = sum(3**(k-1-(3+i)) * 2**combo[i] for i in range(num_terms))
                    if val == required_suffix:
                        print(f"        RÉALISABLE : positions={combo}, suffix={val}")
                        found = True
                        # Mais corrSum = n₀·d, donc corrSum mod d = 0 — contradiction ?
                        full_cs = prefix + val
                        print(f"        corrSum = {full_cs}, mod d = {full_cs % d}")
                        print(f"        n₀ = {full_cs // d}, reste = {full_cs % d}")
                        break
                if not found:
                    print(f"        Non réalisable comme somme.")


if __name__ == "__main__":
    print("*" * 70)
    print("RECHERCHE DE L'OBSTRUCTION RÉELLE — SESSION 6")
    print("*" * 70)

    size_analysis()
    verify_all_compositions_fail()
    closest_multiple_analysis()
    horner_automaton_analysis()
    structural_relation()
    coverage_analysis()
    corrsum_total_analysis()
