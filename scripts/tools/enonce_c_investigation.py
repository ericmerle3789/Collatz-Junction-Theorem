#!/usr/bin/env python3
"""
INVESTIGATION PROFONDE DE L'ENONCE C
=====================================
Session 6 — Attaque du coeur de la preuve

ENONCE C : Pour tout k >= 3 et tout etat s = 3 + 2^p (p >= 1) :
  Le backward ne peut PAS atteindre q_2 = p + 1.
  Equivalemment : max_bwd(s, 1) = p (pas p+1).

REFORMULATION ALGEBRIQUE :
  Le backward de k-2 etapes depuis c_{k-1}=0, utilisant des positions
  q_2 < q_3 < ... < q_{k-1} TOUTES dans {p+1, ..., S-1},
  NE PEUT PAS produire l'etat s = 3 + 2^p.

  Equivalence avec N_0(d) :
  Si max_bwd(s) >= p+1, alors la composition (0, p, q_2, ..., q_{k-1})
  avec 0 < p < q_2 < ... < q_{k-1} <= S-1 donnerait corrSum = 0 mod d.
  C'est-a-dire N_0(d) > 0 — contradiction !

APPROCHE :
  1. TRACER les chemins backward qui atteignent s = 3+2^p
  2. COMPRENDRE pourquoi q_2 = p est le max
  3. IDENTIFIER l'obstruction pour q_2 = p+1
  4. CHERCHER un argument algebrique general
"""

import math
from collections import defaultdict


def compute_params(k):
    S = math.ceil(k * math.log2(3))
    d = (1 << S) - 3**k
    return S, d


def build_forward_j1(k):
    """Forward au step j=1 : c_1 = (3 + 2^p) mod d pour p in {1,...,S-1}."""
    S, d = compute_params(k)
    fwd = {}
    for p in range(1, S):
        state = (3 + pow(2, p, d)) % d
        if state not in fwd or p < fwd[state]:
            fwd[state] = p
    return fwd, S, d


def build_backward_full(k, S, d):
    """Construit TOUTES les couches backward avec detail complet."""
    inv3 = pow(3, -1, d)
    layers = [{(0, S): 1}]
    for step in range(1, k):
        current = layers[-1]
        nl = defaultdict(int)
        for (state, first_pos), count in current.items():
            for p in range(1, first_pos):
                prev = ((state - pow(2, p, d)) * inv3) % d
                nl[(prev, p)] += count
        layers.append(dict(nl))
    return layers


def build_backward_by_state(k, S, d):
    """Backward layer k-2 : pour chaque etat, TOUTES les min_positions possibles."""
    inv3 = pow(3, -1, d)

    # Layer par layer, track toutes les positions par etat
    # layer[state] = set of min_positions achievable
    layers = [defaultdict(set)]
    layers[0][0].add(S)  # etat 0, position fictive S

    for step in range(1, k - 1):
        new_layer = defaultdict(set)
        for state, positions in layers[-1].items():
            for max_pos in positions:
                for p in range(1, max_pos):
                    prev = ((state - pow(2, p, d)) * inv3) % d
                    new_layer[prev].add(p)
        layers.append(new_layer)

    return layers[-1]  # layer k-2


def investigation_1_trace_backward_paths(k):
    """
    INVESTIGATION 1 : Tracer les chemins backward pour les cas serres.

    Pour chaque etat serre s = 3 + 2^p, montrer :
    - Quelles min_positions le backward atteint
    - Quels chemins menent a q_2 = p
    - Pourquoi q_2 = p+1 echoue
    """
    S, d = compute_params(k)
    if d <= 0:
        return

    print(f"\n{'='*70}")
    print(f"INVESTIGATION 1 : CHEMINS BACKWARD POUR k={k}, S={S}, d={d}")
    print(f"{'='*70}")

    fwd, _, _ = build_forward_j1(k)
    bwd_states = build_backward_by_state(k, S, d)

    # Trouver les cas serres (etats communs avec gap = 0)
    common = set(fwd.keys()) & set(bwd_states.keys())

    tight_cases = []
    for s in sorted(common):
        p_fwd = fwd[s]
        max_bwd = max(bwd_states[s])
        gap = p_fwd - max_bwd
        if gap == 0:
            tight_cases.append((s, p_fwd, max_bwd, bwd_states[s]))

    if not tight_cases:
        print(f"  Aucun cas serre pour k={k} (tous les gaps > 0)")
        return

    for s, p_fwd, max_bwd, bwd_positions in tight_cases:
        diff = (s - 3) % d
        is_pow2 = diff > 0 and (diff & (diff - 1)) == 0
        p_val = diff.bit_length() - 1 if is_pow2 else None

        print(f"\n  --- Etat s={s}, p_fwd={p_fwd}, max_bwd={max_bwd}, gap=0 ---")
        if is_pow2:
            print(f"      s = 3 + 2^{p_val} (mod d)")
        print(f"      Positions backward possibles : {sorted(bwd_positions)}")

        # Verifier que p+1 n'est PAS dans les positions backward
        if p_fwd + 1 in bwd_positions:
            print(f"      *** ALERTE : q_2 = p+1 = {p_fwd+1} EST atteignable ! ***")
        else:
            print(f"      q_2 = p+1 = {p_fwd+1} n'est PAS atteignable (confirme)")

        # Qu'est-ce que c_2 serait pour q_2 = p et q_2 = p+1 ?
        c2_at_p = (3 * s + pow(2, p_fwd, d)) % d
        c2_at_p1 = (3 * s + pow(2, p_fwd + 1, d)) % d if p_fwd + 1 < S else None

        print(f"\n      Si q_2 = p = {p_fwd} :  c_2 = 3*{s} + 2^{p_fwd} = {c2_at_p} (mod {d})")
        if c2_at_p1 is not None:
            print(f"      Si q_2 = p+1 = {p_fwd+1} :  c_2 = 3*{s} + 2^{p_fwd+1} = {c2_at_p1} (mod {d})")
        else:
            print(f"      q_2 = p+1 = {p_fwd+1} >= S={S}, position hors limites !")

        # Verifier si c_2 est atteignable depuis 0 en k-3 pas avec positions > q_2
        if k >= 5 and c2_at_p1 is not None:
            # Build backward k-3 layers from 0 with positions restricted to > p+1
            reachable = check_restricted_backward(k, S, d, p_fwd + 1, c2_at_p1)
            if reachable:
                print(f"      c_2={c2_at_p1} EST atteignable avec pos > {p_fwd+1} en {k-3} pas")
                print(f"      *** INVARIANT VIOLE ??? ***")
            else:
                print(f"      c_2={c2_at_p1} N'EST PAS atteignable avec pos > {p_fwd+1} en {k-3} pas")


def check_restricted_backward(k, S, d, min_pos, target_state):
    """
    Verifie si target_state est atteignable depuis 0 en exactement k-3 pas backward,
    avec TOUTES les positions dans {min_pos+1, ..., S-1}.

    Retourne True si atteignable, False sinon.
    """
    inv3 = pow(3, -1, d)

    # Backward depuis 0
    # Layer 0 : etat 0
    current = {0: set()}
    current[0].add(S)  # position fictive

    for step in range(1, k - 2):  # k-3 etapes
        new_states = defaultdict(set)
        for state, max_positions in current.items():
            for mp in max_positions:
                for p in range(min_pos + 1, mp):  # positions > min_pos
                    prev = ((state - pow(2, p, d)) * inv3) % d
                    new_states[prev].add(p)
        current = new_states
        if not current:
            break

    return target_state in current


def investigation_2_algebraic_obstruction(k):
    """
    INVESTIGATION 2 : Obstruction algebrique precise.

    Pour s = 3 + 2^p, analysons :
    - La valeur de c_2 = 3s + 2^{p+1} = 9 + 5*2^p mod d
    - Pourquoi cette valeur est inatteignable en k-3 pas depuis 0
    - Quel est le rapport avec d = 2^S - 3^k
    """
    S, d = compute_params(k)
    if d <= 0:
        return

    print(f"\n{'='*70}")
    print(f"INVESTIGATION 2 : OBSTRUCTION ALGEBRIQUE (k={k}, S={S}, d={d})")
    print(f"{'='*70}")

    fwd, _, _ = build_forward_j1(k)
    bwd_states = build_backward_by_state(k, S, d)
    common = set(fwd.keys()) & set(bwd_states.keys())

    for s in sorted(common):
        p = fwd[s]
        max_b = max(bwd_states[s])
        if p != max_b:
            continue  # pas un cas serre

        diff = (s - 3) % d
        if diff <= 0 or (diff & (diff - 1)) != 0:
            continue

        p_val = diff.bit_length() - 1
        print(f"\n  === s = {s} = 3 + 2^{p_val}, p_1 = {p} ===")

        # Analyse de c_2 pour differentes valeurs de q_2
        print(f"\n  Valeurs de c_2 = (3*s + 2^q) mod d pour q = {max(1,p-1)}..{min(S,p+4)} :")
        for q in range(max(1, p - 1), min(S, p + 4)):
            c2 = (3 * s + pow(2, q, d)) % d
            marker = ""
            if q == p:
                marker = " <-- q_2 = p (atteignable)"
            elif q == p + 1:
                marker = " <-- q_2 = p+1 (CRITIQUE)"
            print(f"    q={q}: c_2 = {c2}{marker}")

        # La difference entre c_2(p) et c_2(p+1)
        c2_p = (3 * s + pow(2, p, d)) % d
        c2_p1 = (3 * s + pow(2, p + 1, d)) % d if p + 1 < S else None

        if c2_p1 is not None:
            delta = (c2_p1 - c2_p) % d
            print(f"\n  delta = c_2(p+1) - c_2(p) = {delta} mod {d}")
            print(f"    = 2^{p+1} - 2^{p} = 2^{p} = {pow(2, p, d)} mod {d}")

            # c_2(p+1) decompose
            val_9 = 9 % d
            val_5_2p = (5 * pow(2, p, d)) % d
            val_total = (val_9 + val_5_2p) % d
            print(f"\n  c_2(p+1) = 9 + 5*2^{p} mod d = {val_9} + {val_5_2p} = {val_total} mod {d}")

            # Factorisation de c_2(p+1) en termes de puissances de 2 et 3
            # c_2(p+1) = 9 + 5*2^p = 3^2 + (4+1)*2^p = 3^2 + 2^{p+2} + 2^p
            c2_check = (9 + pow(2, p + 2, d) + pow(2, p, d)) % d
            print(f"  = 3^2 + 2^{p+2} + 2^{p} = {c2_check} mod {d} (verification)")

            # Analyse : dans Z/dZ, avec d = 2^S - 3^k, que vaut 3^2 ?
            print(f"\n  Dans Z/{d}Z :")
            print(f"    3^k = 2^S mod d = {pow(3, k, d)} = {pow(2, S, d)} (mod d)")
            print(f"    3^2 = {9 % d} (mod d)")
            print(f"    5 = {5 % d} (mod d)")
            print(f"    2^{p} = {pow(2, p, d)} (mod d)")


def investigation_3_corrsum_decomposition(k):
    """
    INVESTIGATION 3 : Decomposition de corrSum.

    Pour s = 3 + 2^p, une composition (0, p, q_2, ..., q_{k-1}) a :
      corrSum = 3^{k-1} + 3^{k-2}*2^p + 3^{k-3}*2^{q_2} + ... + 2^{q_{k-1}}

    Si q_2 = p+1, le debut de corrSum contient :
      3^{k-1} + 3^{k-2}*2^p + 3^{k-3}*2^{p+1}
      = 3^{k-1} + 3^{k-2}*2^p + 2*3^{k-3}*2^p
      = 3^{k-1} + (3 + 2)*3^{k-3}*2^p
      = 3^{k-1} + 5*3^{k-3}*2^p

    QUESTION : Cette expression specifique a-t-elle des proprietes
    mod d = 2^S - 3^k qui empechent corrSum = 0 mod d ?
    """
    S, d = compute_params(k)
    if d <= 0:
        return

    print(f"\n{'='*70}")
    print(f"INVESTIGATION 3 : DECOMPOSITION DE corrSum (k={k}, S={S}, d={d})")
    print(f"{'='*70}")

    fwd, _, _ = build_forward_j1(k)
    bwd_states = build_backward_by_state(k, S, d)
    common = set(fwd.keys()) & set(bwd_states.keys())

    for s in sorted(common):
        p = fwd[s]
        max_b = max(bwd_states[s])
        if p != max_b:
            continue
        diff = (s - 3) % d
        if diff <= 0 or (diff & (diff - 1)) != 0:
            continue
        p_val = diff.bit_length() - 1
        if p_val != p:
            continue

        print(f"\n  === s = 3 + 2^{p}, p = {p} ===")

        # Debut de corrSum pour q_2 = p+1
        term0 = pow(3, k - 1)
        term1 = pow(3, k - 2) * pow(2, p)
        term2_at_p = pow(3, k - 3) * pow(2, p) if k >= 4 else 0
        term2_at_p1 = pow(3, k - 3) * pow(2, p + 1) if k >= 4 else 0

        print(f"  corrSum commence par :")
        print(f"    T_0 = 3^{k-1} = {term0}")
        print(f"    T_1 = 3^{k-2} * 2^{p} = {term1}")
        if k >= 4:
            print(f"    T_2 (si q_2=p) = 3^{k-3} * 2^{p} = {term2_at_p}")
            print(f"    T_2 (si q_2=p+1) = 3^{k-3} * 2^{p+1} = {term2_at_p1}")

        # Les 3 premiers termes mod d
        prefix_p = (term0 + term1 + term2_at_p) % d
        prefix_p1 = (term0 + term1 + term2_at_p1) % d

        print(f"\n  Prefixe (T_0 + T_1 + T_2) mod d :")
        print(f"    Pour q_2=p   : {prefix_p} mod {d}")
        print(f"    Pour q_2=p+1 : {prefix_p1} mod {d}")

        # Ce qui reste a combler : suffix = corrSum - prefix = 0 mod d
        # Donc suffix = -prefix mod d
        target_suffix_p = (-prefix_p) % d
        target_suffix_p1 = (-prefix_p1) % d

        print(f"\n  Le suffixe (termes j=3...k-1) doit valoir :")
        print(f"    Pour q_2=p   : {target_suffix_p} mod {d}")
        print(f"    Pour q_2=p+1 : {target_suffix_p1} mod {d}")

        # Le suffixe est Sum_{j=3}^{k-1} 3^{k-1-j} * 2^{q_j}
        # avec q_j > q_2. Pour q_2=p : positions dans {p+1,...,S-1}
        # Pour q_2=p+1 : positions dans {p+2,...,S-1}
        # Nombre de termes : k-3

        if k >= 5:
            # Enumerer toutes les valeurs possibles du suffixe
            suffix_values_p = compute_suffix_range(k, S, d, p + 1)
            suffix_values_p1 = compute_suffix_range(k, S, d, p + 2)

            hit_p = target_suffix_p in suffix_values_p
            hit_p1 = target_suffix_p1 in suffix_values_p1

            print(f"\n  Suffixe atteignable ?")
            print(f"    Pour q_2=p   : {len(suffix_values_p)} valeurs, "
                  f"cible {target_suffix_p} {'TROUVEE' if hit_p else 'absente'}")
            print(f"    Pour q_2=p+1 : {len(suffix_values_p1)} valeurs, "
                  f"cible {target_suffix_p1} {'TROUVEE' if hit_p1 else 'ABSENTE'}")

            if not hit_p1 and len(suffix_values_p1) < 50:
                print(f"    Valeurs suffixe (q_2=p+1) : {sorted(suffix_values_p1)}")
                print(f"    Cible manquante : {target_suffix_p1}")


def compute_suffix_range(k, S, d, min_position):
    """
    Calcule l'ensemble des valeurs possibles pour
      suffix = Sum_{j=3}^{k-1} 3^{k-1-j} * 2^{q_j}
    avec min_position < q_3 < ... < q_{k-1} <= S-1
    et exactement k-3 termes.
    """
    from itertools import combinations

    num_terms = k - 3
    available = list(range(min_position, S))

    if num_terms <= 0:
        return {0}
    if len(available) < num_terms:
        return set()

    values = set()
    for combo in combinations(available, num_terms):
        val = 0
        for idx, q in enumerate(combo):
            j = 3 + idx  # j goes from 3 to k-1
            weight = pow(3, k - 1 - j)
            val += weight * pow(2, q)
        values.add(val % d)

    return values


def investigation_4_weight_ratio_analysis(k_max=12):
    """
    INVESTIGATION 4 : Analyse du ratio de poids.

    Au point j=1, le forward utilise le poids 3^{k-2} (pour position p_1).
    Le backward utilise le poids 3^{k-3} (pour position q_2).
    Ratio = 3 en faveur du forward.

    QUESTION PRECISE : Ce ratio de 3 est-il la RAISON pour laquelle
    le backward ne peut pas gagner une position supplementaire ?

    Si le backward avait le meme poids que le forward (ratio 1),
    pourrait-il atteindre q_2 = p+1 ?
    """
    print(f"\n{'='*70}")
    print(f"INVESTIGATION 4 : RATIO DE POIDS FORWARD/BACKWARD")
    print(f"{'='*70}")

    for k in range(3, k_max + 1):
        S, d = compute_params(k)
        if d <= 0:
            continue

        weight_fwd = pow(3, k - 2)  # poids du terme j=1 (forward)
        weight_bwd = pow(3, k - 3)  # poids du terme j=2 (backward)
        ratio = weight_fwd / weight_bwd if weight_bwd > 0 else float('inf')

        # Nombre de positions disponibles pour suffixe avec q_2=p vs q_2=p+1
        fwd, _, _ = build_forward_j1(k)
        bwd_states = build_backward_by_state(k, S, d)
        common = set(fwd.keys()) & set(bwd_states.keys())

        n_tight = 0
        for s in common:
            if fwd[s] == max(bwd_states[s]):
                n_tight += 1

        print(f"\n  k={k}: S={S}, d={d}")
        print(f"    Poids forward (j=1) : 3^{k-2} = {weight_fwd}")
        print(f"    Poids backward (j=2): 3^{k-3} = {weight_bwd}")
        print(f"    Ratio : {ratio:.1f}")
        print(f"    Cas serres : {n_tight} / {len(common)} etats communs")

        # Pour le cas serre principal s=5 (p=1) si applicable
        if 5 in fwd and 5 in bwd_states and k >= 5:
            p = fwd[5]
            positions_bwd = sorted(bwd_states[5])
            print(f"    Etat s=5 (3+2^1) : p_fwd={p}, bwd_positions={positions_bwd}")

            # Contribution du terme j=1 vs j=2 dans corrSum
            contrib_j1 = (weight_fwd * pow(2, p)) % d
            contrib_j2_p = (weight_bwd * pow(2, p)) % d
            contrib_j2_p1 = (weight_bwd * pow(2, p + 1)) % d
            print(f"    Contribution j=1 (p={p}): 3^{k-2}*2^{p} = {contrib_j1} mod {d}")
            print(f"    Contribution j=2 (q=p={p}): 3^{k-3}*2^{p} = {contrib_j2_p} mod {d}")
            print(f"    Contribution j=2 (q=p+1={p+1}): 3^{k-3}*2^{p+1} = {contrib_j2_p1} mod {d}")

            # En bits : combien de "bits" supplementaires le backward gagne-t-il ?
            # 2^{p+1} = 2 * 2^p, soit 1 bit de plus.
            # Mais le poids du backward est 3x plus petit.
            # Gain net = 2^{p+1} / 3 vs 2^p = 2/3 du forward
            # Donc le backward avec q_2=p+1 "vaut" 2/3 de ce que le forward
            # contribue avec p_1=p.
            print(f"    Ratio backward(p+1)/forward(p) = 2*3^{{k-3}} / 3^{{k-2}} = 2/3")


def investigation_5_modular_arithmetic(k):
    """
    INVESTIGATION 5 : Arithmetique modulaire de d = 2^S - 3^k.

    Pour s = 3 + 2^p, le forward fixe le residu :
      r_fwd = (s - 3) = 2^p (mod d)

    Le backward avec q_2 produit un residu :
      r_bwd = 2^{q_2} contribue au terme j=2

    QUESTION : La relation d = 2^S - 3^k cree-t-elle une
    obstruction arithmetique entre 2^p et 2^{p+1} dans le
    contexte de la recurrence de Horner ?

    IDEE CLE : corrSum pour composition (0, p, p+1, q_3, ...) contient
      3^{k-1} + 3^{k-2}*2^p + 3^{k-3}*2^{p+1} + ...
      = 3^{k-1} + 3^{k-3}*2^p*(3 + 2) + ...
      = 3^{k-1} + 5*3^{k-3}*2^p + ...

    Et d = 2^S - 3^k. Donc :
      3^k = 2^S mod d
      3^{k-1} = 2^S * 3^{-1} mod d
      3^{k-3} = 2^S * 3^{-3} mod d = 2^S / 27 mod d

    Substituons :
      corrSum = 2^S/3 + 5 * 2^{S+p}/27 + ...  (mod d)
    """
    S, d = compute_params(k)
    if d <= 0:
        return

    print(f"\n{'='*70}")
    print(f"INVESTIGATION 5 : ARITHMETIQUE MODULAIRE (k={k}, S={S}, d={d})")
    print(f"{'='*70}")

    inv3 = pow(3, -1, d)
    inv27 = pow(27, -1, d)

    print(f"\n  Relations fondamentales dans Z/{d}Z :")
    print(f"    3^{k} = 2^{S} mod d  (= {pow(3, k, d)} = {pow(2, S, d)})")
    print(f"    3^{{-1}} = {inv3} mod {d}")
    print(f"    3^{{-3}} = 27^{{-1}} = {inv27} mod {d}")

    fwd, _, _ = build_forward_j1(k)
    bwd_states = build_backward_by_state(k, S, d)
    common = set(fwd.keys()) & set(bwd_states.keys())

    for s in sorted(common):
        p = fwd[s]
        max_b = max(bwd_states[s])
        if p != max_b:
            continue
        diff = (s - 3) % d
        if diff <= 0 or (diff & (diff - 1)) != 0:
            continue
        p_val = diff.bit_length() - 1
        if p_val != p:
            continue

        print(f"\n  === s = 3 + 2^{p} ===")

        # Substituons 3^a = 3^{a-k} * 3^k = 3^{a-k} * 2^S mod d
        # Pour a < k : 3^a mod d directement
        # Pour le corrSum : 3^{k-1} = 3^{-1} * 3^k = inv3 * 2^S mod d
        val_3km1 = (inv3 * pow(2, S, d)) % d
        print(f"    3^{k-1} = 3^{{-1}} * 2^{S} = {val_3km1} mod {d}")
        print(f"    (verification : 3^{k-1} mod d = {pow(3, k-1, d)})")

        # corrSum debut pour (0, p, p+1, ...)
        # = 3^{k-1} + 3^{k-2}*2^p + 3^{k-3}*2^{p+1}
        # = 3^{-1}*2^S + 3^{-2}*2^{S+p} + 3^{-3}*2^{S+p+1}
        # En termes de 2^S :
        # = 2^S * (3^{-1} + 3^{-2}*2^p + 3^{-3}*2^{p+1})
        # = 2^S * 3^{-3} * (3^2 + 3*2^p + 2^{p+1})
        # = 2^S * 3^{-3} * (9 + 3*2^p + 2*2^p)
        # = 2^S * 3^{-3} * (9 + 5*2^p)

        factor = (9 + 5 * pow(2, p)) % d
        prefix_mod_d = (pow(2, S, d) * inv27 % d * factor) % d

        print(f"\n    Prefixe = 2^{S} * 27^{{-1}} * (9 + 5*2^{p})")
        print(f"           = {pow(2,S,d)} * {inv27} * {factor}")
        print(f"           = {prefix_mod_d} mod {d}")

        # Verification directe
        prefix_direct = (pow(3, k-1, d) + pow(3, k-2, d) * pow(2, p, d)
                         + pow(3, k-3, d) * pow(2, p+1, d)) % d
        print(f"    (verification directe : {prefix_direct})")

        # Rappel : 2^S = 0 + 3^k dans les entiers, donc 2^S mod d = 3^k mod d
        # Et 2^S = d + 3^k, donc 2^S mod d = 3^k mod d
        # Le prefixe contient le facteur 2^S mod d = 3^k mod d
        # Qui est un multiple de 3 dans les entiers

        print(f"\n    Observation : 2^{S} mod d = 3^{k} mod d = {pow(2, S, d)}")
        print(f"    Le prefixe contient le facteur 3^{k} / 27 = 3^{k-3}")
        print(f"    3^{k-3} = {pow(3, k-3, d)} mod {d}")

        # Quel est le residu cible pour le suffixe ?
        target = (-prefix_mod_d) % d
        print(f"\n    Suffixe doit valoir : -prefixe = {target} mod {d}")

        # Propriete de target dans Z/dZ
        # Est-ce un multiple de 3 ? De 2 ?
        print(f"    target mod 2 = {target % 2}")
        print(f"    target mod 3 = {target % 3}")
        if d > 5:
            for small_p in [2, 3, 5, 7]:
                if d % small_p == 0:
                    print(f"    target mod {small_p} = {target % small_p} (et d mod {small_p} = 0)")


def investigation_6_universal_s5(k_max=14):
    """
    INVESTIGATION 6 : Le cas universel s=5 (p=1).

    s = 5 = 3 + 2^1 est le cas serre le plus frequent.
    Il apparait pour k >= 5 (sauf k=6 ou c'est s=11 le cas critique).

    Pour s=5, p=1 :
      corrSum(0, 1, q_2, ..., q_{k-1}) = 3^{k-1} + 3^{k-2}*2 + ...
      = 3^{k-1} + 2*3^{k-2} + ...
      = 3^{k-2}*(3 + 2) + ...
      = 5*3^{k-2} + ...

    La question est : 5*3^{k-2} + Sum_{j>=3} 3^{k-1-j}*2^{q_j} = 0 mod d
    avec q_j >= 3 (car q_2 = p+1 = 2, donc q_3 >= 3).

    Equivalent a : Sum_{j>=3} 3^{k-1-j}*2^{q_j} = -5*3^{k-2} mod d

    Le cote droit est -5*3^{k-2} mod d. C'est un NOMBRE FIXE.
    Le cote gauche est une somme ponderee de k-3 puissances de 2.
    La question est : cette somme ponderee peut-elle atteindre ce nombre fixe ?
    """
    print(f"\n{'='*70}")
    print(f"INVESTIGATION 6 : CAS UNIVERSEL s=5 (p=1)")
    print(f"{'='*70}")

    for k in range(5, k_max + 1):
        S, d = compute_params(k)
        if d <= 0:
            continue

        # Cible : -5*3^{k-2} mod d
        target = (-5 * pow(3, k - 2, d)) % d
        # = -(5 * 3^{-2} * 3^k) mod d = -(5/9 * 2^S) mod d
        inv9 = pow(9, -1, d)
        target_alt = (-(5 * inv9 % d) * pow(2, S, d)) % d

        print(f"\n  k={k}, S={S}, d={d}")
        print(f"    Cible = -5*3^{k-2} mod d = {target}")
        print(f"    Cible = -(5/9)*2^{S} mod d = {target_alt} (verification)")

        # Le suffixe = Sum_{j=3}^{k-1} 3^{k-1-j} * 2^{q_j}
        # avec q_3 > q_2 = 2, donc q_3 >= 3
        # et q_3 < q_4 < ... < q_{k-1} <= S-1

        # Pour k petit, enumerer toutes les valeurs du suffixe
        if k <= 10:
            from itertools import combinations
            num_terms = k - 3
            avail = list(range(3, S))  # positions >= 3

            if len(avail) >= num_terms and num_terms > 0:
                suffix_vals = set()
                for combo in combinations(avail, num_terms):
                    val = sum(pow(3, k - 1 - (3 + idx), d) * pow(2, q, d)
                              for idx, q in enumerate(combo)) % d
                    suffix_vals.add(val)

                hit = target in suffix_vals
                coverage = len(suffix_vals) / d * 100

                print(f"    Suffixe : {len(suffix_vals)}/{d} valeurs ({coverage:.1f}%), "
                      f"cible {target} {'TROUVEE!' if hit else 'absente'}")

                if not hit:
                    # Distance minimale a la cible
                    min_dist = min(min(abs(v - target), d - abs(v - target))
                                   for v in suffix_vals)
                    print(f"    Distance min a la cible : {min_dist}")

                    # Quels residus sont proches de la cible ?
                    near = sorted([(v, (v - target) % d) for v in suffix_vals
                                   if min((v - target) % d, (target - v) % d) <= 3])
                    if near:
                        print(f"    Voisins : {near[:5]}")
            else:
                print(f"    Pas assez de positions : {len(avail)} < {num_terms}")
        else:
            # Pour k grand, compter les combinaisons
            from math import comb
            num_terms = k - 3
            avail = S - 3  # positions 3 a S-1
            n_combos = comb(avail, num_terms) if avail >= num_terms else 0
            print(f"    {n_combos} combinaisons pour {num_terms} termes dans {avail} positions")
            print(f"    Ratio combos/d = {n_combos/d:.4f}")


def investigation_7_valuation_analysis(k_max=12):
    """
    INVESTIGATION 7 : Analyse par valuations 2-adiques.

    Pour corrSum = 3^{k-1} + 3^{k-2}*2 + 3^{k-3}*2^{q_2} + ...
    avec q_2 = 2 (cas s=5, p=1, q_2=p+1) :

    v_2(corrSum) = v_2(3^{k-1} + 2*3^{k-2} + 4*3^{k-3} + ...)
                 = v_2(3^{k-3} * (9 + 6 + 4 + ...))
                 = v_2(3^{k-3}) + v_2(9 + 6 + 4 + ...)
                 = 0 + v_2(19 + ...)

    Pour corrSum = 0 mod d, il faut corrSum = n*d.
    Or d est IMPAIR (d = 2^S - 3^k, impair).
    Donc v_2(n*d) = v_2(n).
    Et v_2(corrSum) = ?

    Si v_2(corrSum) = 0 (corrSum impair), alors n doit etre impair.
    (On sait deja que corrSum est toujours impair.)

    Mais pour des compositions specifiques commencant par (0, p, p+1, ...),
    peut-on avoir une contrainte PLUS FORTE ?
    """
    print(f"\n{'='*70}")
    print(f"INVESTIGATION 7 : VALUATIONS 2-ADIQUES")
    print(f"{'='*70}")

    for k in range(5, k_max + 1):
        S, d = compute_params(k)
        if d <= 0:
            continue

        print(f"\n  k={k}, S={S}, d={d}")

        # Pour p=1 (s=5), corrSum prefix = 3^{k-1} + 3^{k-2}*2 + 3^{k-3}*4
        # = 3^{k-3} * (9 + 6 + 4) = 3^{k-3} * 19
        prefix_exact = 3**(k-1) + 3**(k-2) * 2 + 3**(k-3) * 4
        print(f"    Prefix (0,1,2) exact = {prefix_exact} = 3^{k-3} * {prefix_exact // 3**(k-3)}")
        print(f"    = 3^{k-3} * 19")
        print(f"    v_2(prefix) = {v2(prefix_exact)}")

        # Pour le corrSum total, le terme suivant a au minimum 2^3 = 8
        # corrSum = 19 * 3^{k-3} + sum(...) ou chaque terme a 2^{q_j} >= 2^3

        # Explorons les v_2 de corrSum pour TOUTES les compositions
        # commencant par (0, 1, 2, ...)
        if k <= 8:
            from itertools import combinations
            num_remaining = k - 3
            avail = list(range(3, S))
            if len(avail) >= num_remaining:
                v2_dist = defaultdict(int)
                for combo in combinations(avail, num_remaining):
                    cs = prefix_exact
                    for idx, q in enumerate(combo):
                        j = 3 + idx
                        cs += 3**(k-1-j) * 2**q
                    v = v2(cs)
                    v2_dist[v] += 1

                    # Verifier si divisible par d
                    if cs % d == 0:
                        print(f"    !!! corrSum = {cs} = {cs//d} * d (composition (0,1,2,{','.join(map(str,combo))}))")

                print(f"    Distribution v_2 : {dict(sorted(v2_dist.items()))}")
                total = sum(v2_dist.values())
                print(f"    Total : {total} compositions testees")

                # v_2 de d
                print(f"    v_2(d) = {v2(d)} (d impair, donc v_2=0)")

                # Pour corrSum = n*d : v_2(corrSum) = v_2(n) + 0 = v_2(n) >= 0
                # Pas de contradiction directe par v_2 car corrSum est toujours impair (v_2=0)
                # MAIS : le prefix 19*3^{k-3} est impair, et chaque terme supplémentaire
                # est pair (2^q >= 8), donc corrSum = impair + somme de pairs = impair.
                # => v_2(corrSum) = 0 toujours.


def v2(n):
    """Valuation 2-adique de n."""
    if n == 0:
        return float('inf')
    n = abs(n)
    v = 0
    while n % 2 == 0:
        v += 1
        n //= 2
    return v


def investigation_8_backward_tree(k):
    """
    INVESTIGATION 8 : Arbre backward detaille pour s=5.

    Construire l'arbre COMPLET des chemins backward qui atteignent s=5,
    et montrer EXACTEMENT ou le chemin avec q_2=2 echoue.
    """
    S, d = compute_params(k)
    if d <= 0 or k < 5:
        return

    if (3 + 2) % d != 5 % d:
        return

    s_target = (3 + 2) % d  # = 5 pour la plupart des k
    inv3 = pow(3, -1, d)

    print(f"\n{'='*70}")
    print(f"INVESTIGATION 8 : ARBRE BACKWARD VERS s={s_target} (k={k})")
    print(f"{'='*70}")

    # Construisons le backward PAS A PAS avec trace
    # Layer 0 : (etat=0, chemin vide)
    paths = [(0, S, [])]  # (state, max_allowed_pos, positions_used)

    for step in range(1, k - 1):
        new_paths = []
        for state, max_pos, positions in paths:
            for q in range(1, max_pos):
                new_state = ((state - pow(2, q, d)) * inv3) % d
                new_paths.append((new_state, q, positions + [q]))
        paths = new_paths

        # Filtrer uniquement les chemins qui menent a s_target
        target_paths = [(st, mp, pos) for st, mp, pos in paths if st == s_target]

        if step == k - 2 and target_paths:
            print(f"\n  Layer {step} (final) : {len(target_paths)} chemins atteignent s={s_target}")
            min_positions = [min(pos) for _, _, pos in target_paths]
            max_min_pos = max(min_positions)
            print(f"  Min positions = {sorted(set(min_positions))}")
            print(f"  MAX(min_pos) = {max_min_pos}")

            if max_min_pos <= 1:
                print(f"  => max_bwd = {max_min_pos} = p = 1, CONFIRME")
            else:
                print(f"  => max_bwd = {max_min_pos}")

            # Afficher les quelques meilleurs chemins
            best = sorted(target_paths, key=lambda x: -min(x[2]))[:5]
            print(f"\n  Top 5 chemins (par min_pos decroissant) :")
            for st, mp, pos in best:
                print(f"    positions = {pos}, min = {min(pos)}")

    # Maintenant, essayons avec q_2 >= 2 (restriction)
    print(f"\n  --- Tentative avec positions >= 2 uniquement ---")
    paths = [(0, S, [])]
    for step in range(1, k - 1):
        new_paths = []
        for state, max_pos, positions in paths:
            for q in range(2, max_pos):  # positions >= 2
                new_state = ((state - pow(2, q, d)) * inv3) % d
                new_paths.append((new_state, q, positions + [q]))
        paths = new_paths

    target_restricted = [(st, mp, pos) for st, mp, pos in paths if st == s_target]
    print(f"  Chemins atteignant s={s_target} avec pos >= 2 : {len(target_restricted)}")

    if target_restricted:
        print(f"  !!! INVARIANT VIOLE !!!")
        for st, mp, pos in target_restricted[:3]:
            print(f"    positions = {pos}")
    else:
        print(f"  AUCUN — confirme que q_2=2 est impossible")

        # Quels etats sont atteignables avec pos >= 2 ?
        reachable_states = set(st for st, _, _ in paths)
        print(f"  Etats atteignables avec pos >= 2 : {len(reachable_states)} / {d}")
        if s_target in reachable_states:
            print(f"  s={s_target} EST dans les etats (contradiction?)")
        else:
            print(f"  s={s_target} N'EST PAS dans les etats atteignables")

        # Les etats les plus proches ?
        if len(reachable_states) < 50:
            print(f"  Etats atteignables : {sorted(reachable_states)}")


if __name__ == "__main__":
    print("*" * 70)
    print("INVESTIGATION PROFONDE DE L'ENONCE C")
    print("*" * 70)

    # Investigation 1 : Chemins backward pour les cas serres
    for k in [5, 6, 7, 8]:
        investigation_1_trace_backward_paths(k)

    # Investigation 2 : Obstruction algebrique
    for k in [5, 6]:
        investigation_2_algebraic_obstruction(k)

    # Investigation 3 : Decomposition de corrSum
    for k in [5, 6, 7]:
        investigation_3_corrsum_decomposition(k)

    # Investigation 4 : Ratio de poids
    investigation_4_weight_ratio_analysis(k_max=10)

    # Investigation 5 : Arithmetique modulaire
    for k in [5, 6]:
        investigation_5_modular_arithmetic(k)

    # Investigation 6 : Cas universel s=5
    investigation_6_universal_s5(k_max=12)

    # Investigation 7 : Valuations 2-adiques
    investigation_7_valuation_analysis(k_max=8)

    # Investigation 8 : Arbre backward detaille
    for k in [5, 6]:
        investigation_8_backward_tree(k)
