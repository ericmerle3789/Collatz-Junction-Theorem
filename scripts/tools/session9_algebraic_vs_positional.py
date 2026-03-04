#!/usr/bin/env python3
"""
SESSION 9b — CONFLIT ALGÉBRIQUE vs POSITIONNEL
================================================
Le Prime Blocking vient d'un conflit entre :
  (A) L'ordre ALGÉBRIQUE : les résidus nécessaires pour atteindre 0
  (B) L'ordre POSITIONNEL : les positions A_j strictement croissantes

HYPOTHÈSE : Pour atteindre sum = 0, les résidus nécessaires imposent
des positions qui DÉCROISSENT quand l'ordre strict demande qu'elles CROISSENT.

INVESTIGATIONS :
  1. Pour chaque couche j, la "position inverse" p^{-1}(résidu) est-elle anti-corrélée avec j ?
  2. Structure du mapping position → résidu : monotone ? chaotique ?
  3. Conflit backward : quand on fixe la couche finale, quels résidus faut-il
     aux couches précédentes, et quelles positions y correspondent ?
  4. Preuve par induction partielle : si les premières positions sont "basses",
     les résidus cumulés sont "hauts", ce qui exige des positions "basses" en fin.
  5. Le "drift" de l'automate de Horner : la multiplication par 3 crée
     un drift systématique qui empêche le retour à 0.
  6. Analyse de la structure de 2^a mod p pour différents p premiers.
  7. Formalisation algébrique : utiliser la structure de Z/pZ pour prouver le conflit.
"""

from math import ceil, log2, gcd, comb
from itertools import combinations
from collections import defaultdict, Counter
import time


def compute_params(k):
    S = ceil(k * log2(3))
    d = 2**S - 3**k
    C = comb(S - 1, k - 1)
    return S, d, C


def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True


# ============================================================
# INVESTIGATION 1 : Pour atteindre sum = 0, quelles positions
# sont nécessaires à la DERNIÈRE couche ?
# Si on a une somme partielle s_{k-2} à la couche k-2,
# on a besoin de w^{k-1} · 2^{A_{k-1}} ≡ -s_{k-2} mod p
# Donc 2^{A_{k-1}} ≡ -s_{k-2} / w^{k-1} mod p
# La position A_{k-1} est déterminée par le log discret.
# ============================================================
def investigate_last_layer_positions():
    """Positions nécessaires à la dernière couche pour atteindre 0."""
    print("=" * 70)
    print("  INVESTIGATION 1 : Positions nécessaires à la dernière couche")
    print("=" * 70)

    for k in range(3, 9):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)
        wk1 = pow(w, k - 1, p)
        inv_wk1 = pow(wk1, -1, p)

        print(f"\n  k={k}, p={d}, S={S}, w^{{k-1}}={wk1}")

        # Construire le mapping résidu → position
        residue_to_pos = {}
        for a in range(1, S):
            r = pow(2, a, p)
            if r not in residue_to_pos:
                residue_to_pos[r] = a
            # (prend la première position = la plus petite)

        # Automate : propager depuis c_0=1 jusqu'à couche k-2
        layers = [set()]
        layers[0] = {(1, 0)}
        for j in range(1, k - 1):
            wj = pow(w, j, p)
            new_layer = set()
            for (s, last) in layers[-1]:
                for a in range(last + 1, S):
                    s_new = (s + wj * pow(2, a, p)) % p
                    new_layer.add((s_new, a))
            layers.append(new_layer)

        # Pour chaque état (s, last_pos) à la couche k-2,
        # quelle position A_{k-1} est nécessaire ?
        needed_positions = []
        for (s, last_pos) in layers[-1]:
            needed_residue = ((-s) * inv_wk1) % p
            # Chercher la position a telle que 2^a ≡ needed_residue mod p
            needed_pos = None
            for a in range(last_pos + 1, S):
                if pow(2, a, p) == needed_residue:
                    needed_pos = a
                    break

            if needed_pos is not None:
                needed_positions.append((s, last_pos, needed_pos, "FOUND"))
            else:
                # Position existe-t-elle en dehors de la plage ?
                all_pos = [a for a in range(1, S) if pow(2, a, p) == needed_residue]
                if all_pos:
                    needed_positions.append((s, last_pos, all_pos[0], "BLOCKED (pos too small)"))
                else:
                    needed_positions.append((s, last_pos, None, "BLOCKED (no pos exists)"))

        found = sum(1 for _, _, _, st in needed_positions if st == "FOUND")
        blocked_pos = sum(1 for _, _, _, st in needed_positions if "pos too small" in st)
        blocked_none = sum(1 for _, _, _, st in needed_positions if "no pos" in st)
        total = len(needed_positions)

        print(f"    États couche k-2 : {total}")
        print(f"    Position trouvée : {found} (devrait être 0 si N₀=0)")
        print(f"    Bloqué (pos trop petite) : {blocked_pos}")
        print(f"    Bloqué (résidu absent) : {blocked_none}")

        if found > 0:
            print(f"    ⚠️ ATTENTION : positions trouvées !")
            for s, lp, np, st in needed_positions:
                if st == "FOUND":
                    print(f"      s={s}, last_pos={lp}, needed_pos={np}")

        if total <= 30:
            for s, lp, np, st in needed_positions:
                print(f"      s={s}, last_pos={lp}, needed_A={np}: {st}")


# ============================================================
# INVESTIGATION 2 : Le "drift multiplicatif" de l'automate
# La transition c → 3c + 2^p crée un drift multiplicatif (×3)
# qui éloigne de 0. Peut-on quantifier ce drift ?
# ============================================================
def investigate_multiplicative_drift():
    """Drift multiplicatif : comment la multiplication par 3 éloigne de 0."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 2 : Drift multiplicatif de l'automate")
    print("=" * 70)

    for k in range(3, 9):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d

        print(f"\n  k={k}, p={d}, S={S}")

        # Depuis c_0 = 1, tracer la "distance à 0" couche par couche
        # Distance = min(c, p-c) (distance cyclique dans Z/pZ)
        layers = [set()]
        layers[0] = {(1, 0)}

        for j in range(1, k):
            new_layer = set()
            for (c, last) in layers[-1]:
                for a in range(last + 1, S):
                    c_new = (3 * c + pow(2, a, p)) % p
                    new_layer.add((c_new, a))
            layers.append(new_layer)

            # Distance stats
            dists = [min(c, p - c) for c, _ in new_layer]
            avg_dist = sum(dists) / len(dists) if dists else 0
            min_dist = min(dists) if dists else 0
            has_zero = 0 in set(c for c, _ in new_layer)
            print(f"    Couche {j}: |états|={len(new_layer)}, "
                  f"dist_avg={avg_dist:.1f}, dist_min={min_dist}, "
                  f"0 in image? {has_zero}")

        # Le drift moyen par couche
        # Après j pas depuis c_0=1 (pas d'ordre) :
        # c_j ≈ 3^j + Σ 3^{j-i} · 2^{a_i}
        # En moyenne sur les positions : E[2^a] = (2^S - 2) / (S-1)
        avg_2a = (2**S - 2) / (S - 1)
        print(f"    E[2^a] = {avg_2a:.1f}")
        print(f"    3^{{k-1}} = {3**(k-1)} vs p = {p}")
        print(f"    3^{{k-1}}/p = {3**(k-1)/p:.3f}")


# ============================================================
# INVESTIGATION 3 : Structure du mapping a → 2^a mod p
# L'ordre des résidus 2^1, 2^2, ..., 2^{S-1} mod p est-il
# "aléatoire" ou structuré ? Monotone par morceaux ?
# ============================================================
def investigate_power_of_2_structure():
    """Structure du mapping position → résidu 2^a mod p."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 3 : Structure de a → 2^a mod p")
    print("=" * 70)

    for k in range(3, 12):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d

        residues = [(a, pow(2, a, p)) for a in range(1, S)]
        print(f"\n  k={k}, p={d}, S={S}")
        print(f"    2^a mod p : {[r for _, r in residues]}")

        # Ordre discret : est-ce que 2^a mod p est "monotone" ?
        # Nombre d'inversions (a₁ < a₂ mais 2^a₁ > 2^a₂ mod p)
        inversions = 0
        total_pairs = 0
        for i in range(len(residues)):
            for j in range(i + 1, len(residues)):
                total_pairs += 1
                if residues[i][1] > residues[j][1]:
                    inversions += 1
        inv_ratio = inversions / total_pairs if total_pairs > 0 else 0
        print(f"    Inversions : {inversions}/{total_pairs} = {inv_ratio:.3f} "
              f"(0.5 = aléatoire)")

        # Le "retournement" : 2^{S-1} mod p est-il proche de 1 ?
        last_res = pow(2, S - 1, p)
        print(f"    2^{{S-1}} mod p = {last_res} "
              f"(distance à 1 : {min(abs(last_res - 1), p - abs(last_res - 1))})")


# ============================================================
# INVESTIGATION 4 : Conflit backward — backward analysis
# On part de la cible (sum = 0) et on remonte.
# À chaque couche j (de k-1 à 1), on retire w^j · 2^{A_j}.
# Les résidus nécessaires à la couche j-1 sont :
#   s_{j-1} = s_j - w^j · 2^{A_j}
# Pour s_j = 0 : s_{k-2} = -w^{k-1} · 2^{A_{k-1}}
# Pour chaque A_{k-1}, s_{k-2} est déterminé.
# Puis s_{k-3} = s_{k-2} - w^{k-2} · 2^{A_{k-2}}
# Avec A_{k-2} < A_{k-1}.
# ============================================================
def investigate_backward_analysis():
    """Analyse backward : de la cible vers l'état initial."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 4 : Analyse backward complète")
    print("=" * 70)

    for k in [3, 5]:
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)

        print(f"\n  k={k}, p={d}, S={S}, w={w}")
        print(f"  Target : sum = 0, donc s_{{k-1}} = 0")
        print(f"  Backward : s_{{j-1}} = (s_j - w^j · 2^{{A_j}}) mod p")

        # Backward depuis 0 : à chaque étape, on doit choisir A_j
        # avec A_j < A_{j+1} (puisqu'on remonte, les positions décroissent)
        # On commence avec "A_k = S" (fictif) et on remonte.

        # Arbre de backward
        # Layer 0 (cible) : s = 0, min_future_pos = S (fictif)
        backward = [{} for _ in range(k)]
        backward[0] = {(0, S): [()]}  # {(résidu, min_pos): [chemins]}

        for step in range(1, k):
            j = k - 1 - (step - 1)  # couche dans le forward
            wj = pow(w, j, p)
            for (s, min_pos), paths in backward[step - 1].items():
                for a in range(1, min_pos):
                    s_prev = (s - wj * pow(2, a, p)) % p
                    key = (s_prev, a)
                    if key not in backward[step]:
                        backward[step][key] = []
                    for path in paths:
                        backward[step][key].append((a,) + path)

            print(f"    Backward step {step} (couche {j}) : "
                  f"{len(backward[step])} états, "
                  f"résidus = {sorted(set(s for s, _ in backward[step]))[:10]}...")

        # À la fin du backward (step = k-1), on doit arriver à s = 1
        # (car c_0 = 1 dans le forward, correspondant à s_0 = w^0 · 2^0 = 1)
        final_layer = backward[k - 1]
        reaching_1 = {key: paths for key, paths in final_layer.items()
                      if key[0] == 1}

        print(f"\n  ★ Backward complet : {len(final_layer)} états finaux")
        print(f"  ★ Atteignent s=1 (c_0=1) ? {len(reaching_1) > 0}")
        if reaching_1:
            for (s, pos), paths in reaching_1.items():
                print(f"    s={s}, pos_min={pos}, chemins: {paths[:3]}")
        else:
            print(f"    AUCUN chemin backward n'atteint s=1 !")
            # Quels résidus SONT atteints ?
            reached = set(s for s, _ in final_layer)
            print(f"    Résidus atteints : {sorted(reached)}")
            print(f"    1 ∈ reached ? {1 in reached}")

            # Si 1 est atteint mais avec pos_min > 0 :
            reaching_1_any = {key: paths for key, paths in final_layer.items()
                              if key[0] == 1}
            if reaching_1_any:
                for (s, pos), paths in reaching_1_any.items():
                    print(f"    s=1 atteint avec pos_min={pos} "
                          f"(doit être > 0 = A_0)")
                    # Si pos_min > 0, c'est compatible !
                    # Si pos_min ≤ 0, c'est incompatible.
                    # MAIS A_0 = 0, donc on a besoin de pos_min > 0
                    # Or la contrainte backward exige pos < pos_précédent
                    # Donc pos_min est la plus petite position dans le chemin
                    # backward, qui doit être > 0 (car A_0 = 0 est déjà pris).
                    # WAIT: A_1 > A_0 = 0, donc A_1 ≥ 1.
                    # Le backward remonte A_{k-1}, A_{k-2}, ..., A_1
                    # et on a besoin de A_1 ≥ 1.
                    # Le pos dans notre backward est la dernière position
                    # choisie (la plus petite), qui correspond à A_1.
                    # Si pos ≥ 1, c'est compatible !
                    compatible = pos >= 1
                    print(f"    Compatible (pos≥1) ? {compatible}")
                    if compatible:
                        print(f"    ⚠️ SOLUTION TROUVÉE !")
                        for path in paths[:5]:
                            print(f"      Chemin (A_1,...,A_{{k-1}}): {path}")


# ============================================================
# INVESTIGATION 5 : Conflit structurel position-résidu
# Pour chaque couche j et résidu nécessaire r,
# la position p telle que 2^p ≡ r/w^j mod p donne p.
# On trace les "positions nécessaires" vs "positions disponibles".
# ============================================================
def investigate_position_residue_conflict():
    """Le conflit entre positions nécessaires et disponibles."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 5 : Conflit position-résidu")
    print("=" * 70)

    for k in [3, 5]:
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)

        print(f"\n  k={k}, p={d}, S={S}, w={w}")

        # Pour le chemin trivial backward depuis 0 :
        # s_{k-1} = 0
        # s_{k-2} = -w^{k-1} · 2^{A_{k-1}} (choisir A_{k-1} ∈ {1,...,S-1})
        # s_{k-3} = s_{k-2} - w^{k-2} · 2^{A_{k-2}} (A_{k-2} < A_{k-1})
        # ...
        # s_0 = ... doit être = 1

        # On trace pour CHAQUE chemin backward : les positions choisies
        # et les résidus intermédiaires.

        def trace_backward(target_s0=1):
            """Trace tous les chemins backward de 0 à target_s0."""
            paths = []

            def search(j, s, max_pos, positions):
                """j = prochaine couche forward à satisfaire (de k-1 vers 0)."""
                if j == 0:
                    # On a atteint la couche 0
                    if s == target_s0:
                        paths.append(list(positions))
                    return

                wj = pow(w, j, p)
                for a in range(1, max_pos):
                    s_new = (s - wj * pow(2, a, p)) % p
                    positions.append(a)
                    search(j - 1, s_new, a, positions)
                    positions.pop()

            search(k - 1, 0, S, [])
            return paths

        all_paths = trace_backward(1)
        print(f"  Chemins backward atteignant s_0=1 : {len(all_paths)}")

        if all_paths:
            for path in all_paths[:5]:
                # path[0] = A_{k-1}, path[1] = A_{k-2}, etc.
                # Convertir en A_1, ..., A_{k-1}
                A = list(reversed(path))
                # Vérifier l'ordre strict
                ordered = all(A[i] < A[i+1] for i in range(len(A)-1))
                # Vérifier que A_1 > 0 (car A_0 = 0)
                valid = A[0] >= 1 if A else True
                print(f"    A_1..A_{{k-1}} = {A}, ordered? {ordered}, "
                      f"A_1>0? {valid}")
        else:
            print(f"  ★ AUCUN chemin — confirme le prime blocking !")

            # Quels résidus sont atteints à s_0 ?
            reached_s0 = set()

            def search_s0(j, s, max_pos):
                if j == 0:
                    reached_s0.add(s)
                    return
                wj = pow(w, j, p)
                for a in range(1, max_pos):
                    s_new = (s - wj * pow(2, a, p)) % p
                    search_s0(j - 1, s_new, a)

            search_s0(k - 1, 0, S)
            print(f"  Résidus s_0 atteints (backward depuis 0) : "
                  f"{sorted(reached_s0)}")
            print(f"  1 ∈ reached ? {1 in reached_s0}")
            missing = set(range(p)) - reached_s0
            print(f"  Missing : {sorted(missing)}")


# ============================================================
# INVESTIGATION 6 : Le "théorème du drift" — tentative de preuve
# Dans l'automate de Horner, c_j = 3c_{j-1} + 2^{p_j}.
# Comme c_0 = 1 et les 2^{p_j} ≥ 2, on a :
#   c_j ≥ 3^j + Σ_{i=1}^j 3^{j-i} · 2 = 3^j + 2·(3^j - 1)/(3-1) = 3^j + 3^j - 1 = 2·3^j - 1
# NON, c'est faux car on travaille mod p.
# MAIS en valeur absolue (avant réduction mod p) :
#   corrSum = Σ 3^{k-1-j} · 2^{A_j} ≥ 3^{k-1} + 2·3^{k-2} + ... = 3^{k-1}(1 + 2/3 + ...)
# La borne inférieure de corrSum est strictement positive.
# ============================================================
def investigate_drift_theorem():
    """Le théorème du drift : corrSum est borné loin de n·d."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 6 : Théorème du drift — bornes de corrSum")
    print("=" * 70)

    for k in range(3, 12):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d

        # Borne inf de corrSum (en entiers)
        # corrSum = Σ 3^{k-1-j} · 2^{A_j} avec 0 = A_0 < A_1 < ... < A_{k-1} ≤ S-1
        # Min : choisir les plus petites positions : A_j = j
        cs_min = sum(3**(k-1-j) * 2**j for j in range(k))
        # Max : choisir les plus grandes positions : A_j = S - k + j
        cs_max = sum(3**(k-1-j) * 2**(S - k + j) for j in range(k))

        # Les multiples de d dans l'intervalle [cs_min, cs_max]
        first_mult = (cs_min // d + 1) * d if cs_min % d != 0 else cs_min
        last_mult = (cs_max // d) * d
        n_multiples = max(0, (last_mult - first_mult) // d + 1) if first_mult <= cs_max else 0
        n0_min = first_mult // d if first_mult <= cs_max else None
        n0_max = last_mult // d if first_mult <= cs_max else None

        print(f"\n  k={k}, p={d}, S={S}")
        print(f"    corrSum ∈ [{cs_min}, {cs_max}]")
        print(f"    d = {d}")
        print(f"    Multiples de d dans l'intervalle : {n_multiples}")
        if n0_min is not None:
            print(f"    n₀ ∈ [{n0_min}, {n0_max}]")
            print(f"    (d·n₀ doit être dans [{cs_min}, {cs_max}])")

        # Les multiples de d les plus proches de cs_min et cs_max
        dist_min = cs_min % d  # distance de cs_min au multiple précédent
        dist_max = d - (cs_max % d) if cs_max % d != 0 else 0  # dist au suivant
        print(f"    cs_min mod d = {cs_min % d}")
        print(f"    cs_max mod d = {cs_max % d}")

        # Combien de compositions donnent des valeurs proches de chaque multiple ?
        if C <= 5000:
            residues = Counter()
            for combo in combinations(range(1, S), k - 1):
                A = (0,) + combo
                cs = sum(3**(k-1-j) * 2**A[j] for j in range(k))
                residues[cs % d] += 1

            print(f"    Vérification : N₀(d) = {residues[0]}")
            # Distribution des résidus
            near_zero = sum(v for r, v in residues.items() if r <= 2 or r >= d - 2)
            print(f"    Compositions avec résidu dans [0,2]∪[d-2,d] : {near_zero}")


# ============================================================
# INVESTIGATION 7 : La preuve par substitution et groupes
# On utilise u = w·2 mod p et B_j = A_j - j.
# La somme devient : Σ u^j · 2^{B_j} avec B_0=0, B_j ≥ B_{j-1} (non-décroissant)
# et B_{k-1} ≤ S - k.
# ============================================================
def investigate_substitution_proof():
    """Preuve via la substitution B_j = A_j - j."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 7 : Substitution B_j = A_j - j")
    print("=" * 70)

    for k in range(3, 9):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)
        u = (w * 2) % p
        B_max = S - k

        print(f"\n  k={k}, p={d}, u=w·2={u}")
        print(f"    B_j ∈ [0, {B_max}], non-décroissant")
        print(f"    ord(u) = ", end="")
        o = 1
        x = u
        while x != 1:
            x = (x * u) % p
            o += 1
        print(f"{o}")
        print(f"    u^k mod p = {pow(u, k, p)}")

        # Les "atomes" : u^j · 2^b pour j=0..k-1, b=0..B_max
        print(f"    Atomes u^j · 2^b mod p :")
        for j in range(k):
            atoms = [(b, pow(u, j, p) * pow(2, b, p) % p) for b in range(B_max + 1)]
            print(f"      j={j}: u^{j}={pow(u,j,p)}, "
                  f"atomes = {[r for _, r in atoms]}")

        # Compter les sommes
        # Σ u^j · 2^{B_j} = 0, B_0=0, B_0 ≤ B_1 ≤ ... ≤ B_{k-1} ≤ B_max
        count_zero = 0
        count_total = 0

        def count_sums(j, last_B, partial_sum):
            nonlocal count_zero, count_total
            if j == k:
                count_total += 1
                if partial_sum == 0:
                    count_zero += 1
                return
            start_B = 0 if j == 0 else last_B  # B_j ≥ B_{j-1}
            if j == 0:
                # B_0 = 0 est fixé
                val = pow(u, 0, p) * pow(2, 0, p) % p  # = 1
                count_sums(1, 0, (partial_sum + val) % p)
            else:
                for b in range(start_B, B_max + 1):
                    val = pow(u, j, p) * pow(2, b, p) % p
                    count_sums(j + 1, b, (partial_sum + val) % p)

        count_sums(0, 0, 0)
        print(f"    Total B-compositions : {count_total} (= C = {C})")
        print(f"    N₀ (B-somme) = {count_zero}")

        # Distribution des résidus en B
        if C <= 5000:
            residues_B = Counter()
            def enum_B(j, last_B, ps):
                if j == k:
                    residues_B[ps] += 1
                    return
                if j == 0:
                    enum_B(1, 0, 1 % p)
                else:
                    for b in range(last_B, B_max + 1):
                        val = pow(u, j, p) * pow(2, b, p) % p
                        enum_B(j + 1, b, (ps + val) % p)

            enum_B(0, 0, 0)
            absent = [r for r in range(p) if residues_B[r] == 0]
            print(f"    Résidus absents : {absent}")
            if 0 in absent and len(absent) == 1:
                print(f"    ★ 0 est le SEUL résidu absent !")

        # OBSERVATION CLÉ : la somme Σ u^j · 2^{B_j} avec B non-décroissant
        # Quand B_j = B_{j+1} = b (même valeur) :
        # u^j · 2^b + u^{j+1} · 2^b = 2^b · u^j · (1 + u)
        # Le facteur (1+u) joue un rôle !
        one_plus_u = (1 + u) % p
        print(f"    1 + u = {one_plus_u}")
        if one_plus_u == 0:
            print(f"    ★★★ u = -1 mod p ! Des termes consécutifs s'annulent !")
        else:
            print(f"    (1+u) ≠ 0, pas d'annulation triviale")


# ============================================================
# MAIN
# ============================================================
if __name__ == "__main__":
    print("SESSION 9b — CONFLIT ALGÉBRIQUE vs POSITIONNEL")
    print("=" * 70)
    print()

    t0 = time.time()

    investigate_last_layer_positions()
    investigate_multiplicative_drift()
    investigate_power_of_2_structure()
    investigate_backward_analysis()
    investigate_position_residue_conflict()
    investigate_drift_theorem()
    investigate_substitution_proof()

    elapsed = time.time() - t0
    print(f"\n{'=' * 70}")
    print(f"  SESSION 9b TERMINÉE en {elapsed:.1f}s")
    print(f"{'=' * 70}")
