#!/usr/bin/env python3
"""
DOUBLE PEELING : PREUVE PAR INCOMPATIBILITE FORWARD/BACKWARD
==============================================================
Session 5 — Exploitation de la Piste E

IDÉE CLÉ : Construire l'automate depuis les DEUX bouts :
  - Forward : depuis c₀=1 vers l'avant
  - Backward : depuis c_{k-1}=0 vers l'arrière

Si les deux ensembles ne se rencontrent JAMAIS (avec contraintes de
position), alors N₀(d) = 0 est PROUVÉ.

RÉSULTAT k=6 (session 5) : 0 paires compatibles !
Le double peeling SUFFIT à prouver N₀(d)=0 pour k=6.

Testons systématiquement pour k=3..15.
"""

import math
from collections import defaultdict


def compute_params(k):
    S = math.ceil(k * math.log2(3))
    d = 2**S - 3**k
    C = math.comb(S - 1, k - 1)
    return S, d, C


def double_peeling_analysis(k_val, verbose=True):
    """
    Double peeling complet pour un k donné.

    Forward : couches depuis c₀=1
    Backward : couches depuis c_{k-1}=0

    Pour chaque profondeur de "rendez-vous" j (0 ≤ j ≤ k-1) :
      Forward donne les (état, position_max) après j pas depuis c₀=1
      Backward donne les (état, position_min) après (k-1-j) pas depuis 0

    Un chemin complet existe ssi ∃ j, (s,p_max) forward et (s,p_min) backward
    tels que p_max < p_min (les positions ne se chevauchent pas).
    """
    S, d, C = compute_params(k_val)
    if d <= 0:
        return None

    inv3 = pow(3, -1, d)

    # === FORWARD : depuis c₀=1, couche par couche ===
    # Chaque entrée : (état, dernière_position) -> nombre de chemins
    forward_layers = [{(1, 0): 1}]

    for step in range(1, k_val):
        current = forward_layers[-1]
        next_layer = defaultdict(int)
        for (state, last_pos), count in current.items():
            for p in range(last_pos + 1, S):
                ns = (3 * state + pow(2, p, d)) % d
                next_layer[(ns, p)] += count
        forward_layers.append(dict(next_layer))

    # === BACKWARD : depuis c_{k-1}=0, couche par couche (en arrière) ===
    # Transition inverse : si c_{j+1} = (3·c_j + 2^p) mod d
    #   alors c_j = (c_{j+1} - 2^p) · 3^{-1} mod d
    # Chaque entrée : (état, première_position) -> nombre de chemins
    # "première_position" = la plus petite position utilisée dans le segment backward
    backward_layers = [{(0, S): 1}]  # S = position fictive (au-delà de la borne)

    for step in range(1, k_val):
        current = backward_layers[-1]
        next_layer = defaultdict(int)
        for (state, first_pos), count in current.items():
            for p in range(1, first_pos):
                prev_state = ((state - pow(2, p, d)) * inv3) % d
                next_layer[(prev_state, p)] += count
        backward_layers.append(dict(next_layer))

    # === ANALYSE : pour chaque point de rendez-vous j ===
    if verbose:
        print(f"\n{'='*80}")
        print(f"DOUBLE PEELING : k={k_val}, d={d}, S={S}, C={C}, C/d={C/d:.3f}")
        print(f"{'='*80}")

    total_compatible = 0
    best_meeting = None

    for j in range(0, k_val):
        fwd = forward_layers[j]  # j pas forward
        bwd_idx = k_val - 1 - j  # (k-1-j) pas backward

        if bwd_idx >= len(backward_layers):
            continue
        bwd = backward_layers[bwd_idx]

        # États accessibles
        fwd_states = defaultdict(list)  # état -> [(pos_max, count)]
        for (s, p), c in fwd.items():
            fwd_states[s].append((p, c))

        bwd_states = defaultdict(list)  # état -> [(pos_min, count)]
        for (s, p), c in bwd.items():
            bwd_states[s].append((p, c))

        # Intersection des états
        common_states = set(fwd_states.keys()) & set(bwd_states.keys())

        # Paires compatibles (pos_max_forward < pos_min_backward)
        compatible = 0
        compatible_paths = 0
        for s in common_states:
            for (fp, fc) in fwd_states[s]:
                for (bp, bc) in bwd_states[s]:
                    if fp < bp:  # Positions ne se chevauchent pas
                        compatible += 1
                        compatible_paths += fc * bc

        total_fwd = sum(c for _, c in fwd.items())
        total_bwd = sum(c for _, c in bwd.items())

        if verbose:
            print(f"\n  RDV étape j={j} (fwd {j} pas, bwd {k_val-1-j} pas) :")
            print(f"    Forward : {total_fwd} chemins, {len(fwd_states)} états")
            print(f"    Backward : {total_bwd} chemins, {len(bwd_states)} états")
            print(f"    États communs : {len(common_states)}")
            print(f"    Paires (état,pos) compatibles : {compatible}")
            print(f"    Chemins compatibles : {compatible_paths}")

        total_compatible += compatible_paths

        if compatible_paths > 0 and best_meeting is None:
            best_meeting = j

    if verbose:
        print(f"\n  === RÉSULTAT ===")
        print(f"  Total chemins compatibles toutes étapes : {total_compatible}")
        if total_compatible == 0:
            print(f"  *** DOUBLE PEELING PROUVE N₀(d) = 0 POUR k={k_val} ***")
        else:
            print(f"  Double peeling ne suffit pas seul. "
                  f"Meilleur point de RDV : j={best_meeting}")

    return {
        'k': k_val, 'd': d, 'S': S, 'C': C,
        'total_compatible': total_compatible,
        'proven': total_compatible == 0
    }


def systematic_test(k_max=17):
    """Test systématique du double peeling pour k=3..k_max."""
    print("*" * 80)
    print("DOUBLE PEELING : TEST SYSTÉMATIQUE")
    print("*" * 80)

    results = []
    for k in range(3, k_max + 1):
        S, d, C = compute_params(k)
        if d <= 0:
            continue
        if C > 500000:
            print(f"\nk={k}: SKIP (C={C} trop grand)")
            continue

        r = double_peeling_analysis(k, verbose=True)
        if r:
            results.append(r)

    # Synthèse
    print(f"\n\n{'='*80}")
    print(f"SYNTHÈSE DOUBLE PEELING")
    print(f"{'='*80}")

    print(f"\n{'k':>3} {'d':>10} {'S':>4} {'C':>10} {'C/d':>8} "
          f"{'compatible':>11} {'PROUVE?':>8}")
    print("-" * 60)

    for r in results:
        proven_str = "OUI !!!" if r['proven'] else "non"
        print(f"{r['k']:3d} {r['d']:10d} {r['S']:4d} {r['C']:10d} "
              f"{r['C']/r['d']:8.3f} {r['total_compatible']:11d} {proven_str:>8}")

    proven_count = sum(1 for r in results if r['proven'])
    total = len(results)

    print(f"\n  Double peeling prouve N₀=0 pour {proven_count}/{total} valeurs de k testées.")

    if proven_count == total:
        print(f"\n  *** DOUBLE PEELING SUFFIT POUR TOUS LES k TESTÉS ! ***")
        print(f"  Si formalisable, c'est potentiellement la CLÉ de la preuve.")
    else:
        failing = [r['k'] for r in results if not r['proven']]
        print(f"\n  k non prouvés par double peeling : {failing}")
        print(f"  Pour ces k, il faut un argument complémentaire.")

    return results


if __name__ == "__main__":
    systematic_test(k_max=15)
