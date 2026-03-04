#!/usr/bin/env python3
"""
PREUVE DE L'ASYMETRIE DE POIDS — Attaque sur l'invariant fort
==============================================================
Session 5 — Vers un theoreme

STRATEGIE : Prouver l'invariant fort au point de RDV j=1 (le plus simple).

Au point j=1 :
  - Forward : c_1 = (3 + 2^{p_1}) mod d, UN SEUL pas.
    Pour chaque etat s, p_1(s) est l'UNIQUE solution de 2^{p_1} = s - 3 mod d
    dans {0,...,S-1} (unicite car ord_d(2) > S-1 pour k >= 4).

  - Backward : k-2 pas depuis c_{k-1} = 0.
    Pour chaque etat s atteignable, q_2(s) = min position du backward.
    max(q_2(s)) = maximum de la plus petite position backward pour etat s.

  L'invariant fort dit : p_1(s) >= max(q_2(s)) pour tout s commun.

QUESTION CLE : Pourquoi le forward utilise-t-il des positions >= celles du backward,
meme si les positions vont de 0 a S-1 pour les deux ?

HYPOTHESE : C'est lie a la TAILLE ENTIERE des puissances de 2.
  Forward : 2^{p_1} = s - 3 mod d. En entier : 2^{p_1} = s - 3 + m*d pour m >= 0.
  Backward : utilise positions q_2 < q_3 < ... < q_{k-1}. Les plus grandes positions
  sont prises en premier (q_{k-1} est la plus grande), laissant q_2 petit.
"""

import math
from collections import defaultdict


def compute_params(k):
    S = math.ceil(k * math.log2(3))
    d = (1 << S) - 3**k
    C = math.comb(S - 1, k - 1)
    return S, d, C


def build_forward_j1(k):
    """
    Forward au point j=1 : c_1 = (3 + 2^p) mod d
    Retourne {state: position} (unique car ord > S-1)
    """
    S, d, C = compute_params(k)
    if d <= 0:
        return {}, S, d

    fwd = {}
    for p in range(1, S):  # positions 1..S-1 (a_0=0 est deja consomme)
        state = (3 + pow(2, p, d)) % d
        if state not in fwd or p < fwd[state]:
            fwd[state] = p  # on garde la plus petite position
    return fwd, S, d


def build_backward_to_j1(k):
    """
    Backward : k-2 pas depuis c_{k-1}=0 vers c_1.
    Retourne {state: max_min_pos} ou max_min_pos est le maximum
    de la plus petite position utilisee par un backward path.
    """
    S, d, C = compute_params(k)
    if d <= 0:
        return {}, S, d

    inv3 = pow(3, -1, d)

    # Couche backward : (state, min_pos_used)
    # On traque la position MINIMALE utilisee par chaque chemin backward.
    # Pour chaque etat, on veut le MAX de min_pos parmi tous les chemins.
    # Representation : {state: max_over_paths(min_pos_of_path)}
    # Plus precisement : {state: set_of_min_positions}

    # Couche 0 : c_{k-1} = 0, pas de position encore
    # Step 1 : c_{k-2} = (0 - 2^{q_{k-1}}) * inv3 mod d, q_{k-1} in {0..S-1}
    #   min_pos = q_{k-1} (seule position utilisee)
    # Step 2 : c_{k-3} = (c_{k-2} - 2^{q_{k-2}}) * inv3 mod d, q_{k-2} < q_{k-1}
    #   min_pos = q_{k-2} (plus petite des deux)
    # ...
    # After m = k-2 steps : on est a c_1, et min_pos = q_2

    # Representation : layers[step] = dict{(state, min_pos): count}
    # Mais on veut juste max(min_pos) par etat.

    # Optimisation : pour chaque (state, min_pos), on ne garde que le meilleur.
    # Representation : {state: max_min_pos}

    # Start : no state yet
    # Step 1 from end: c_{k-2} = -2^{q_{k-1}} * inv3 mod d
    layer = {}  # {state: max_min_pos}
    for q in range(1, S):  # positions 1..S-1 (pas 0, a_0 est reserve)
        state = ((-pow(2, q, d)) * inv3) % d
        if state not in layer or q > layer[state]:
            layer[state] = q  # min_pos = q (only pos), maximize it

    # Steps 2..k-2 from end
    for step in range(2, k - 1):
        new_layer = {}
        for state, current_max_min in layer.items():
            # layer tracks (state, max_min_pos_so_far).
            # Add a new position q < current_max_min, with q >= 1.
            # The new min_pos becomes q.
            for q in range(1, current_max_min):  # q >= 1, q < current min pos
                new_state = ((state - pow(2, q, d)) * inv3) % d
                if new_state not in new_layer or q > new_layer[new_state]:
                    new_layer[new_state] = q
        layer = new_layer

    return layer, S, d


def analyze_j1_invariant(k, verbose=True):
    """
    Test detaille de l'invariant fort au point j=1.
    Montre pourquoi p_1(s) >= max(q_2(s)) pour chaque etat commun.
    """
    S, d, C = compute_params(k)
    if d <= 0:
        if verbose:
            print(f"  k={k} : d <= 0, skip")
        return None

    fwd, _, _ = build_forward_j1(k)
    bwd, _, _ = build_backward_to_j1(k)

    common = sorted(set(fwd.keys()) & set(bwd.keys()))

    if verbose:
        print(f"\n{'='*80}")
        print(f"INVARIANT FORT AU POINT j=1 — k={k}, S={S}, d={d}")
        print(f"{'='*80}")
        print(f"  Etats forward : {len(fwd)}, backward : {len(bwd)}, communs : {len(common)}")

        if len(common) > 0:
            print(f"\n  {'state':>8} {'p1_fwd':>7} {'q2_bwd':>7} {'gap':>5} "
                  f"{'2^p1':>12} {'s-3':>10} {'s-3 mod d':>10} {'integer_m':>10}")
            print(f"  " + "-" * 80)

            all_gaps = []
            for s in common:
                p1 = fwd[s]
                q2 = bwd[s]
                gap = p1 - q2
                all_gaps.append(gap)
                two_p1 = 2 ** p1
                s_minus_3 = (s - 3) % d
                # Quelle est la valeur ENTIERE ? 2^{p1} = s - 3 + m*d
                m = (two_p1 - s_minus_3) // d if s_minus_3 != two_p1 % d else 0
                if s_minus_3 == 0 and two_p1 % d == 0:
                    m = two_p1 // d
                else:
                    m = (two_p1 - (s - 3)) // d

                if len(common) <= 30:
                    print(f"  {s:8d} {p1:7d} {q2:7d} {gap:5d} "
                          f"{two_p1:12d} {s-3:10d} {s_minus_3:10d} {m:10d}")

            min_gap = min(all_gaps)
            avg_gap = sum(all_gaps) / len(all_gaps)
            print(f"\n  Gap min = {min_gap}, Gap moyen = {avg_gap:.2f}")
            print(f"  INVARIANT {'OUI' if min_gap >= 0 else 'NON'}")

    return common


def integer_analysis_j1(k, verbose=True):
    """
    ANALYSE ENTIERE : Quelle est la structure de 2^{p_1} en ENTIERS (pas mod d) ?

    Forward : 2^{p_1} = (s - 3) mod d => 2^{p_1} = s - 3 + m*d pour un m >= 0
      - Si s >= 4 : m = 0, donc p_1 = log_2(s-3). PETIT pour les petits s.
      - Si s <= 2 : 2^{p_1} = s - 3 + d (car s-3 < 0). GRAND car d est grand.
      - s = 3 : 2^{p_1} = 0 mod d => p_1 = ? (seulement si d | 2^{p_1}, rare)

    Backward : Apres k-2 pas, la plus petite position q_2 est contrainte
    par le fait que k-2 positions doivent s'emboiter dans {0,...,S-1}.
    Par pigeonhole : q_2 <= S - (k-2) = S - k + 2.

    PREDICTION : Pour les etats s avec p_1(s) petit (s proche de 3),
    le backward ne peut pas produire q_2(s) aussi petit => gap > 0.
    Pour les etats s avec p_1(s) grand (s loin de 3),
    le backward pourrait atteindre un q_2(s) grand aussi, MAIS
    le forward prend deja les grandes positions => gap >= 0.
    """
    S, d, C = compute_params(k)
    if d <= 0:
        return None

    fwd, _, _ = build_forward_j1(k)
    bwd, _, _ = build_backward_to_j1(k)
    common = sorted(set(fwd.keys()) & set(bwd.keys()))

    if verbose:
        print(f"\n{'='*80}")
        print(f"ANALYSE ENTIERE j=1 — k={k}, S={S}, d={d}")
        print(f"{'='*80}")

    # Classifions les etats par la "distance a 3"
    close_to_3 = []  # s - 3 petit (0 < s-3 < d/2)
    far_from_3 = []  # s - 3 grand (s-3 < 0 ou s-3 > d/2)
    for s in common:
        diff = (s - 3) % d
        if 0 < diff < d // 2:
            close_to_3.append(s)
        else:
            far_from_3.append(s)

    if verbose:
        print(f"  Etats proches de 3 (mod d) : {len(close_to_3)}")
        print(f"  Etats loin de 3 (mod d) : {len(far_from_3)}")

        if close_to_3:
            print(f"\n  PROCHES DE 3 :")
            for s in close_to_3[:10]:
                p1 = fwd[s]
                q2 = bwd[s]
                print(f"    s={s}, s-3={s-3}, p1={p1} (2^p1={2**p1}), "
                      f"q2={q2}, gap={p1-q2}")

        if far_from_3:
            print(f"\n  LOIN DE 3 :")
            for s in far_from_3[:10]:
                p1 = fwd[s]
                q2 = bwd[s]
                diff = (s - 3) % d
                print(f"    s={s}, (s-3)%d={diff}, p1={p1} (2^p1={2**p1}), "
                      f"q2={q2}, gap={p1-q2}")

    return close_to_3, far_from_3


def pigeonhole_bound(k, verbose=True):
    """
    BORNE PAR PIGEONHOLE : Le backward utilise k-2 positions strictement croissantes
    dans {0,...,S-1}. Donc la plus petite position q_2 satisfait :
      q_2 <= S - 1 - (k - 3) = S - k + 2

    Si l'etat n'est PAS atteignable avec q_2 = S-k+2, alors q_2 est encore plus petit.

    Compare cette borne avec p_1(s) pour chaque etat.
    """
    S, d, C = compute_params(k)
    if d <= 0:
        return None

    fwd, _, _ = build_forward_j1(k)
    bwd, _, _ = build_backward_to_j1(k)
    common = sorted(set(fwd.keys()) & set(bwd.keys()))

    pigeonhole = S - k + 2

    if verbose:
        print(f"\n{'='*80}")
        print(f"BORNE PIGEONHOLE — k={k}, S={S}, d={d}")
        print(f"{'='*80}")
        print(f"  Borne pigeonhole : q_2 <= S - k + 2 = {pigeonhole}")
        print(f"  Nombre d'etats communs : {len(common)}")

    # Combien d'etats forward ont p_1 >= pigeonhole ?
    above_pigeonhole = sum(1 for s in common if fwd[s] >= pigeonhole)
    below_pigeonhole = len(common) - above_pigeonhole

    if verbose:
        print(f"  Etats avec p_1 >= borne : {above_pigeonhole}/{len(common)} "
              f"=> bloques par pigeonhole seul")
        print(f"  Etats avec p_1 < borne : {below_pigeonhole}/{len(common)} "
              f"=> necessitent argument plus fin")

        if below_pigeonhole > 0:
            print(f"\n  Etats CRITIQUES (p_1 < borne pigeonhole) :")
            for s in common:
                p1 = fwd[s]
                q2 = bwd[s]
                if p1 < pigeonhole:
                    print(f"    s={s}, p1={p1}, q2_max={q2}, gap={p1-q2}")

    return above_pigeonhole, below_pigeonhole


def backward_position_distribution(k, verbose=True):
    """
    Analyse DETAILLEE de la distribution des positions backward.

    Pour chaque etat s accessible par backward en k-2 pas :
    - Quels sont TOUS les q_2 possibles ?
    - Quelle est la distribution ?
    - Y a-t-il une borne SUPERIEURE plus fine que pigeonhole ?
    """
    S, d, C = compute_params(k)
    if d <= 0:
        return None

    inv3 = pow(3, -1, d)

    # Couches backward avec TOUTES les min_pos pour chaque etat
    # Layer = {state: set_of_min_positions}

    layer = defaultdict(set)  # {state: set of min_pos}

    # Step 1 from end
    for q in range(1, S):  # positions >= 1
        state = ((-pow(2, q, d)) * inv3) % d
        layer[state].add(q)

    # Steps 2..k-2 from end
    for step in range(2, k - 1):
        new_layer = defaultdict(set)
        for state, min_pos_set in layer.items():
            max_min = max(min_pos_set)
            for q in range(1, max_min):  # q >= 1
                new_state = ((state - pow(2, q, d)) * inv3) % d
                new_layer[new_state].add(q)
        layer = new_layer

    # Comparer avec forward
    fwd, _, _ = build_forward_j1(k)
    common = sorted(set(fwd.keys()) & set(layer.keys()))

    if verbose:
        print(f"\n{'='*80}")
        print(f"DISTRIBUTION BACKWARD DETAILLEE — k={k}, S={S}, d={d}")
        print(f"{'='*80}")
        print(f"  Etats communs : {len(common)}")

        if len(common) <= 30:
            for s in common:
                p1 = fwd[s]
                bwd_positions = sorted(layer[s])
                max_q2 = max(bwd_positions)
                gap = p1 - max_q2
                n_bwd = len(bwd_positions)
                pos_str = str(bwd_positions) if n_bwd <= 10 else f"[{bwd_positions[0]}..{bwd_positions[-1]}] ({n_bwd} vals)"
                print(f"    s={s}: p1={p1}, bwd_q2={pos_str}, max_q2={max_q2}, gap={gap}")
        else:
            # Stats
            gaps = []
            for s in common:
                p1 = fwd[s]
                max_q2 = max(layer[s])
                gaps.append(p1 - max_q2)
            print(f"  Gap min = {min(gaps)}, max = {max(gaps)}, moy = {sum(gaps)/len(gaps):.2f}")

            # Show worst cases
            worst = [(g, s) for g, s in zip(gaps, common)]
            worst.sort()
            print(f"\n  5 pires cas :")
            for g, s in worst[:5]:
                p1 = fwd[s]
                max_q2 = max(layer[s])
                bwd_count = len(layer[s])
                print(f"    s={s}: p1={p1}, max_q2={max_q2}, gap={g}, "
                      f"#bwd_options={bwd_count}")

    return layer


def critical_question_why_invariant(k, verbose=True):
    """
    LA QUESTION CRITIQUE : Pourquoi min(p_1(s)) >= max(q_2(s)) pour tout s ?

    TENTATIVE DE REPONSE ANALYTIQUE :

    Forward : c_1 = 3 + 2^{p_1} mod d
    => 2^{p_1} = c_1 - 3 mod d

    Backward (dernier pas avant le meeting point) :
    c_1 = (c_2 - 2^{q_2}) * inv3 mod d
    => c_2 = 3*c_1 + 2^{q_2} mod d
    => 2^{q_2} = c_2 - 3*c_1 mod d

    Donc pour un etat commun s :
    Forward : 2^{p_1} = s - 3 mod d
    Backward : 2^{q_2} = c_2 - 3*s mod d

    Les 'residus' sont s - 3 (forward) et c_2 - 3*s (backward).
    Le backward a un FACTEUR 3 devant s !

    Si s est petit : s - 3 est petit, mais 3*s est 3x plus grand.
    Si c_2 ~ 0 : backward residu ~ -3*s mod d = d - 3*s (si 3*s < d).
    Ceci est GRAND quand s est petit (car d - 3*s ~ d).

    Hmm... c'est subtil. Analysons numeriquement.
    """
    S, d, C = compute_params(k)
    if d <= 0:
        return None

    inv3 = pow(3, -1, d)
    fwd, _, _ = build_forward_j1(k)

    if verbose:
        print(f"\n{'='*80}")
        print(f"QUESTION CRITIQUE — k={k}, S={S}, d={d}")
        print(f"{'='*80}")

    # Forward : residu = s - 3 mod d
    # Backward : residu_q2 = c_2 - 3*s mod d (depend de c_2)

    # Au lieu de fixer c_2, construisons le backward complet
    # et pour chaque (s, q_2) backward, calculons le residu
    bwd_data = defaultdict(list)  # s -> [(q_2, c_2, residue)]

    # Build backward k-2 steps
    # We need to track (state, min_pos, predecessor_state)
    # Actually, let's build the backward paths that lead to each state s at j=1
    # The last backward step: c_1 = (c_2 - 2^{q_2}) * inv3 mod d
    # So c_2 = 3*c_1 + 2^{q_2} mod d

    # We need the backward layer at j=2 (one step before meeting point)
    # Build backward from c_{k-1}=0, taking k-3 steps to reach c_2

    if k <= 3:
        # For k=3: backward has 1 step. c_2 is directly computed.
        # k-2 = 1 step backward from c_2=0 to c_1
        # c_1 = (0 - 2^{q_2}) * inv3 mod d = -2^{q_2} * inv3 mod d
        for q2 in range(1, S):
            s = ((-pow(2, q2, d)) * inv3) % d
            residue = pow(2, q2, d)  # 2^{q_2} mod d
            bwd_data[s].append((q2, 0, residue))

    else:
        # Build backward layers from c_{k-1}=0 to c_2 (k-3 steps)
        # Then the final step from c_2 to c_1 gives us q_2 and the residue
        layer_c2 = defaultdict(set)  # c_2 -> set of (min_pos_so_far,)
        # Step 1: c_{k-2} from c_{k-1}=0
        for q in range(1, S):
            c_km2 = ((-pow(2, q, d)) * inv3) % d
            layer_c2[c_km2].add(q)

        # Steps 2..k-3 from end (to reach c_2)
        for step in range(2, k - 2):
            new_layer = defaultdict(set)
            for state, min_pos_set in layer_c2.items():
                for current_min in min_pos_set:
                    for q in range(1, current_min):
                        new_state = ((state - pow(2, q, d)) * inv3) % d
                        new_layer[new_state].add(q)
            layer_c2 = new_layer

        # Now layer_c2 contains c_2 states with their min_pos from the end
        # Final step: c_1 = (c_2 - 2^{q_2}) * inv3, with q_2 < min_pos_of_c2_path
        for c2, min_pos_set in layer_c2.items():
            max_min = max(min_pos_set)
            for q2 in range(1, max_min):
                c1 = ((c2 - pow(2, q2, d)) * inv3) % d
                residue_q2 = pow(2, q2, d)
                bwd_data[c1].append((q2, c2, residue_q2))

    # Compare forward and backward residues
    common = sorted(set(fwd.keys()) & set(bwd_data.keys()))

    if verbose and len(common) <= 20:
        print(f"\n  {'s':>6} {'p1':>4} {'fwd_res':>10} {'q2_max':>6} "
              f"{'bwd_res':>10} {'c2':>8} {'3s%d':>10}")
        print(f"  " + "-" * 70)
        for s in common:
            p1 = fwd[s]
            fwd_residue = (s - 3) % d
            # Backward : find the path with max q2
            best = max(bwd_data[s], key=lambda x: x[0])
            q2_max, c2_best, bwd_residue = best
            three_s = (3 * s) % d

            print(f"  {s:6d} {p1:4d} {fwd_residue:10d} {q2_max:6d} "
                  f"{bwd_residue:10d} {c2_best:8d} {three_s:10d}")

        # Key question: what's the relationship between fwd_residue and bwd_residue?
        print(f"\n  Forward residue: 2^p1 = s - 3 mod d")
        print(f"  Backward residue: 2^q2 = c2 - 3*s mod d")
        print(f"  Note: forward a 's' dans le residue, backward a '3*s'")
        print(f"  Le facteur 3 est LA CLE de l'asymetrie!")

    return common, bwd_data


def multiplicative_shift_analysis(k, verbose=True):
    """
    ANALYSE DU DECALAGE MULTIPLICATIF

    Pour comprendre pourquoi p_1 >= q_2, comparons les residus :
    Forward : 2^{p_1} = s - 3 mod d
    Backward (dernier pas) : 2^{q_2} = c_2 - 3*s mod d

    Si on pouvait relier c_2 a s, on aurait :
    2^{q_2} / 2^{p_1} ~ (c_2 - 3*s) / (s - 3) mod d

    Le facteur 3 dans '3*s' fait que le backward 'consomme' 3x plus de
    la valeur de s. Cela signifie que pour atteindre le meme etat s,
    le backward doit 'compenser' avec une PLUS PETITE puissance de 2
    (donc q_2 plus petit).

    FORMALISATION :
    Definissons R_fwd(s) = dlog_2(s - 3 mod d) et R_bwd(s) = max_{c_2} dlog_2(c_2 - 3s mod d)
    ou dlog_2 est le log discret en base 2 mod d.

    L'invariant dit R_fwd(s) >= R_bwd(s).
    """
    S, d, C = compute_params(k)
    if d <= 0:
        return None

    inv3 = pow(3, -1, d)
    fwd, _, _ = build_forward_j1(k)

    if verbose:
        print(f"\n{'='*80}")
        print(f"DECALAGE MULTIPLICATIF — k={k}, S={S}, d={d}")
        print(f"{'='*80}")

    # Pour chaque etat forward s, calculons :
    # 1. Le residu forward : r_fwd = (s - 3) % d
    # 2. Le "range" de residus backward possibles : r_bwd = (c_2 - 3*s) % d
    #    pour differents c_2 atteignables par backward en k-3 pas
    # 3. Les dlogs correspondants

    # D'abord, construisons le log discret base 2 mod d
    dlog = {}
    val = 1
    for i in range(S):
        dlog[val] = i
        val = (val * 2) % d

    # Etats atteignables par backward en k-3 pas (= couche c_2)
    if k <= 3:
        c2_states = {0}  # c_2 = c_{k-1} = 0 directly
    else:
        c2_layer = {0: S}  # {state: max_min_pos}
        for step in range(1, k - 2):
            new_layer = {}
            for state, mmp in c2_layer.items():
                for q in range(1, mmp):  # q >= 1
                    new_state = ((state - pow(2, q, d)) * inv3) % d
                    if new_state not in new_layer or q > new_layer[new_state]:
                        new_layer[new_state] = q
            c2_layer = new_layer
        c2_states = set(c2_layer.keys())

    if verbose:
        print(f"  Etats c_2 atteignables : {len(c2_states)}")

    # Pour chaque etat forward s, calculons les residus
    results = []
    for s in sorted(fwd.keys()):
        p1 = fwd[s]
        r_fwd = (s - 3) % d

        # Residus backward possibles
        best_q2 = -1
        best_c2 = -1
        for c2 in c2_states:
            r_bwd = (c2 - 3 * s) % d
            if r_bwd in dlog:
                q2 = dlog[r_bwd]
                if q2 > best_q2:
                    best_q2 = q2
                    best_c2 = c2

        if best_q2 >= 0:
            results.append((s, p1, best_q2, p1 - best_q2, best_c2))

    if verbose and results:
        if len(results) <= 30:
            print(f"\n  {'s':>6} {'p1':>4} {'best_q2':>8} {'gap':>5} {'c2':>8} "
                  f"{'(s-3)%d':>10} {'(c2-3s)%d':>12}")
            print(f"  " + "-" * 65)
            for s, p1, bq2, gap, c2 in results:
                r_fwd = (s - 3) % d
                r_bwd = (c2 - 3 * s) % d
                print(f"  {s:6d} {p1:4d} {bq2:8d} {gap:5d} {c2:8d} "
                      f"{r_fwd:10d} {r_bwd:12d}")

        gaps = [r[3] for r in results]
        print(f"\n  Gap min = {min(gaps)}, Gap moyen = {sum(gaps)/len(gaps):.2f}")
        print(f"  INVARIANT au j=1 (dlog) : {'OUI' if min(gaps) >= 0 else 'NON'}")

        # Le facteur multiplicatif clé
        print(f"\n  === ANALYSE DU FACTEUR 3 ===")
        # Si c_2 = 0 (cas le plus simple pour backward) :
        # r_bwd = (-3*s) mod d = d - 3*s (si 3*s < d)
        # r_fwd = s - 3 (si s > 3)
        # Ratio r_bwd / r_fwd = (d - 3*s) / (s - 3) pour 4 <= s << d
        # ~ d/s pour s petit, >> 1
        # ~ -3 pour s grand (quand s -> d/3)
        # Donc r_bwd >> r_fwd quand s est petit => q2 >> p1 ?? NON !
        # Attendons... r_bwd GRAND signifie que le backward a besoin d'un
        # GRAND 2^{q2}, donc q2 GRAND. Mais le backward veut q2 PETIT !

        # AH ! Voilà l'inversion :
        # Forward : r_fwd petit => 2^{p1} petit => p1 petit (BIEN pour forward)
        # Backward : veut q2 petit, donc r_bwd = 2^{q2} petit
        # MAIS r_bwd = c_2 - 3s mod d. Quand c_2 ~ 0 et s > 0 :
        #   r_bwd = -3s mod d = d - 3s (GRAND quand s petit)
        # Donc backward est FORCE d'avoir un GRAND residu quand s est petit
        # => GRAND q2, ce qui est MAUVAIS pour le backward !

        print(f"  Pour s petit (s > 3, c_2 ~ 0) :")
        print(f"    r_fwd = s - 3 (PETIT) => p1 petit")
        print(f"    r_bwd = d - 3s (GRAND) => q2 GRAND")
        print(f"  Le backward est FORCE d'utiliser une grande position !")
        print(f"  Mais il a besoin de petites positions (il construit de haut en bas).")
        print(f"  => Le backward ne peut PAS offrir q2 <= p1.")
        print(f"\n  Pour s grand (s ~ d/3, c_2 ~ 0) :")
        print(f"    r_fwd = s - 3 (GRAND) => p1 grand")
        print(f"    r_bwd = d - 3s (PETIT car 3s ~ d) => q2 petit")
        print(f"  Forward a besoin d'une grande position (p1 grand)")
        print(f"  Backward offre une petite position (q2 petit)")
        print(f"  => gap = p1 - q2 >> 0. Invariant largement satisfait.")

    return results


def the_key_theorem(verbose=True):
    """
    SYNTHESE : Le theoreme du decalage multiplicatif.

    Pour tout etat commun s au point j=1 :
    - Forward residu : 2^{p_1} ≡ s - 3 (mod d)
    - Backward residu (cas c_2=0) : 2^{q_2} ≡ -3s (mod d) = d - 3s (mod d)

    Le RATIO des residus est :
      (d - 3s) / (s - 3) ~ d/s pour s petit
                          ~ 3 pour s ~ d/4
                          ~ 0 pour s ~ d/3

    En termes de positions (logarithmes discrets) :
      q_2 - p_1 ~ log_2(ratio) = log_2((d-3s)/(s-3))

    Pour s petit : ratio >> 1, donc q_2 >> p_1 => gap = p_1 - q_2 < 0 ???

    ATTENTION : c'est le CONTRAIRE de ce qu'on veut !

    RESOLUTION : le backward ne se limite PAS a c_2 = 0.
    Les etats c_2 atteignables ont leurs propres contraintes.
    De plus, le backward doit satisfaire q_2 < min_pos(chemin_vers_c_2).
    C'est cette contrainte d'EMBOITEMENT qui limite q_2.

    Le vrai argument est que :
    1. Le backward DOIT utiliser k-2 positions strictement croissantes
    2. Les k-3 positions superieures (q_3,...,q_{k-1}) consomment les positions hautes
    3. La position residuelle q_2 est FORCEE d'etre petite
    4. Independamment du residu mod d, q_2 ne peut pas etre grand
    """
    if verbose:
        print(f"\n{'*'*80}")
        print(f"SYNTHESE : POURQUOI L'INVARIANT TIENT")
        print(f"{'*'*80}")

        print(f"""
  L'invariant fort tient par la CONJONCTION de deux forces :

  FORCE 1 : CONTRAINTE D'EMBOITEMENT (backward)
    Le backward utilise k-2 positions dans {{0,...,S-1}}.
    Les k-3 positions superieures 'mangent' les hautes valeurs.
    La position residuelle q_2 <= S - k + 2 (pigeonhole),
    mais en pratique souvent beaucoup moins.

  FORCE 2 : LOG DISCRET (forward)
    Le forward a p_1 = dlog_2(s - 3 mod d).
    Pour la plupart des etats s, (s - 3) mod d est 'aleatoire' dans Z/dZ,
    donc p_1 est 'aleatoire' dans {{0,...,ord_d(2)-1}}.
    Puisque ord_d(2) > S-1, p_1 est bien reparti dans {{0,...,S-1}}.

  MECANISME COMBINE :
    - Pour les etats avec p_1 PETIT (s ~ 3+2^p avec p petit) :
      Ce sont les etats 'faciles' pour le forward.
      Le backward ne peut atteindre ces etats qu'avec q_2 encore plus petit,
      car le residu backward est r_bwd ~ d - 3s (GRAND), forcant le
      chemin backward a 'epuiser' ses positions hautes rapidement.

    - Pour les etats avec p_1 GRAND (s loin de 3) :
      Le forward utilise une grande position.
      Le backward pourrait theoriquement atteindre ces etats,
      mais ses k-3 positions superieures sont deja consommees,
      laissant q_2 << p_1.

  CONCLUSION :
    Le facteur multiplicatif 3 dans la recurrence de Horner (c = 3*c_prev + 2^p)
    cree une ASYMETRIE entre forward et backward :
    - Forward ADDITIONNE 2^p (faible poids relatif)
    - Backward DIVISE par 3 (multiplicateur du poids)
    Cette asymetrie fait que pour atteindre un meme etat,
    forward et backward consomment les positions de facon INCOMPATIBLE.
""")

    # Verification numerique
    print(f"  VERIFICATION NUMERIQUE :")
    for k in range(3, 15):
        S, d, C = compute_params(k)
        if d <= 0:
            continue
        fwd, _, _ = build_forward_j1(k)
        bwd, _, _ = build_backward_to_j1(k)
        common = sorted(set(fwd.keys()) & set(bwd.keys()))
        if common:
            min_gap = min(fwd[s] - bwd[s] for s in common)
        else:
            min_gap = float('inf')
        pigeonhole = S - k + 2
        status = "OUI" if min_gap >= 0 else "NON"
        print(f"    k={k:2d} S={S:2d} d={d:8d} |common|={len(common):4d} "
              f"min_gap={min_gap:3d} pigeonhole={pigeonhole:2d} => {status}")


def ultimate_investigation(k, verbose=True):
    """
    Pour les cas SERRÉS (gap=0), analysons EXACTEMENT ce qui se passe.
    """
    S, d, C = compute_params(k)
    if d <= 0:
        return None

    fwd, _, _ = build_forward_j1(k)
    bwd, _, _ = build_backward_to_j1(k)
    common = sorted(set(fwd.keys()) & set(bwd.keys()))

    tight = [(s, fwd[s], bwd[s]) for s in common if fwd[s] - bwd[s] == 0]

    if verbose and tight:
        print(f"\n{'='*80}")
        print(f"CAS SERRES (gap=0) — k={k}, S={S}, d={d}")
        print(f"{'='*80}")
        for s, p1, q2 in tight:
            print(f"  s={s}: p1=q2={p1}")
            # Forward : 2^{p1} = (s - 3) % d
            r_fwd = (s - 3) % d
            print(f"    Forward: 2^{p1} = {2**p1}, (s-3)%d = {r_fwd}")
            # Backward : quel c_2 mene ici avec q_2 = p1 ?
            inv3 = pow(3, -1, d)
            # c_1 = (c_2 - 2^{q_2}) * inv3 => c_2 = 3*s + 2^{q_2}
            c_2 = (3 * s + pow(2, p1, d)) % d
            print(f"    Backward: c_2 = (3*{s} + 2^{p1}) % d = {c_2}")
            r_bwd = pow(2, p1, d)
            print(f"    2^q2 = {2**p1}, (c_2 - 3*s)%d = {(c_2 - 3*s) % d}")
            print(f"    Forward et backward utilisent la MEME puissance 2^{p1} !")
            print(f"    Mais avec des sens differents :")
            print(f"      Forward: s = 3 + 2^{p1} mod d (additif)")
            print(f"      Backward: s = (c_2 - 2^{p1}) * 3^-1 mod d (divisif)")

    return tight


if __name__ == "__main__":
    print("*" * 80)
    print("PREUVE DE L'ASYMETRIE DE POIDS")
    print("*" * 80)

    # Analyse de l'invariant au point j=1 pour petits k
    for k in [5, 6, 7]:
        analyze_j1_invariant(k)

    # Analyse entiere
    for k in [5, 6]:
        integer_analysis_j1(k)

    # Borne pigeonhole
    for k in [5, 6, 7, 8, 10]:
        pigeonhole_bound(k)

    # Distribution backward
    for k in [5, 6]:
        backward_position_distribution(k)

    # Question critique
    for k in [5, 6]:
        critical_question_why_invariant(k)

    # Decalage multiplicatif
    for k in [5, 6]:
        multiplicative_shift_analysis(k)

    # Cas serres
    for k in range(3, 11):
        S, d, C = compute_params(k)
        if d <= 0:
            continue
        tight = ultimate_investigation(k, verbose=False)
        if tight:
            print(f"\n  k={k}: {len(tight)} cas serres")
            ultimate_investigation(k)

    # Synthese
    the_key_theorem()
