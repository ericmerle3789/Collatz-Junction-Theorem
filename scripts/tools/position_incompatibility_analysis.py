#!/usr/bin/env python3
"""
ANALYSE DE L'INCOMPATIBILITE DES POSITIONS FORWARD/BACKWARD
=============================================================
Session 5 — Formalisation du Double Peeling

QUESTION CLE : Pourquoi p_fwd >= p_bwd TOUJOURS ?

PISTES D'INVESTIGATION :
  (A) Position moyenne : quelle est la position moyenne dans chaque couche ?
      Si <p_fwd>_j > (S-1)/2 et <p_bwd>_{k-1-j} < (S-1)/2, incompatibilite.
  (B) Position min/max : le min de p_fwd est-il >= max de p_bwd ?
      C'est plus fort que la moyenne.
  (C) Entropie positionnelle : les positions sont-elles "concentrees" ?
  (D) Drift de Horner : la multiplication par 3 pousse-t-elle les positions
      dans une direction specifique ?
  (E) Argument de comptage : combien de positions chaque couche "consomme" ?
      Si forward consomme > S/2 et backward aussi, c'est impossible.
"""

import math
from collections import defaultdict
import statistics


def compute_params(k):
    S = math.ceil(k * math.log2(3))
    d = 2**S - 3**k
    C = math.comb(S - 1, k - 1)
    return S, d, C


def build_forward_layers(k_val, S, d):
    """Construit les couches forward avec statistiques de positions."""
    layers = [{(1, 0): 1}]
    for step in range(1, k_val):
        current = layers[-1]
        next_layer = defaultdict(int)
        for (state, last_pos), count in current.items():
            for p in range(last_pos + 1, S):
                ns = (3 * state + pow(2, p, d)) % d
                next_layer[(ns, p)] += count
        layers.append(dict(next_layer))
    return layers


def build_backward_layers(k_val, S, d):
    """Construit les couches backward avec statistiques de positions."""
    inv3 = pow(3, -1, d)
    layers = [{(0, S): 1}]
    for step in range(1, k_val):
        current = layers[-1]
        next_layer = defaultdict(int)
        for (state, first_pos), count in current.items():
            for p in range(1, first_pos):
                prev_state = ((state - pow(2, p, d)) * inv3) % d
                next_layer[(prev_state, p)] += count
        layers.append(dict(next_layer))
    return layers


def position_statistics(layer, label=""):
    """Statistiques sur les positions dans une couche."""
    positions = []
    for (state, pos), count in layer.items():
        positions.extend([pos] * count)

    if not positions:
        return None

    return {
        'count': len(positions),
        'min': min(positions),
        'max': max(positions),
        'mean': statistics.mean(positions),
        'median': statistics.median(positions),
        'stdev': statistics.stdev(positions) if len(positions) > 1 else 0,
        'states': len(set(s for (s, p) in layer.keys())),
    }


def piste_A_position_moyennes(k_val, verbose=True):
    """
    Piste A : Comparer les positions moyennes forward et backward
    au point de rendez-vous.
    """
    S, d, C = compute_params(k_val)
    if d <= 0:
        return None

    fwd = build_forward_layers(k_val, S, d)
    bwd = build_backward_layers(k_val, S, d)

    if verbose:
        print(f"\n{'='*80}")
        print(f"PISTE A : POSITIONS MOYENNES — k={k_val}, S={S}, d={d}")
        print(f"{'='*80}")

    results = []
    for j in range(0, k_val):
        bwd_idx = k_val - 1 - j
        if bwd_idx >= len(bwd):
            continue

        fwd_stats = position_statistics(fwd[j])
        bwd_stats = position_statistics(bwd[bwd_idx])

        if fwd_stats and bwd_stats:
            gap = bwd_stats['min'] - fwd_stats['max']
            mean_gap = bwd_stats['mean'] - fwd_stats['mean']

            result = {
                'j': j,
                'fwd_mean': fwd_stats['mean'],
                'fwd_max': fwd_stats['max'],
                'fwd_min': fwd_stats['min'],
                'bwd_mean': bwd_stats['mean'],
                'bwd_min': bwd_stats['min'],
                'bwd_max': bwd_stats['max'],
                'gap_minmax': gap,  # bwd_min - fwd_max (doit etre > 0 pour compatibilite)
                'gap_mean': mean_gap,
                'S_half': (S - 1) / 2,
            }
            results.append(result)

            if verbose:
                print(f"\n  RDV j={j} (fwd {j} pas, bwd {k_val-1-j} pas):")
                print(f"    Forward  : pos in [{fwd_stats['min']}, {fwd_stats['max']}], "
                      f"moy={fwd_stats['mean']:.1f}, med={fwd_stats['median']:.1f}")
                print(f"    Backward : pos in [{bwd_stats['min']}, {bwd_stats['max']}], "
                      f"moy={bwd_stats['mean']:.1f}, med={bwd_stats['median']:.1f}")
                print(f"    S/2 = {(S-1)/2:.1f}")
                print(f"    Gap (bwd_min - fwd_max) = {gap}")
                print(f"    Gap (bwd_moy - fwd_moy) = {mean_gap:.1f}")
                if gap > 0:
                    print(f"    !!! GAP POSITIF => positions POURRAIENT etre compatibles !!!")
                else:
                    print(f"    Gap <= 0 => positions incompatibles (fwd_max >= bwd_min)")

    return results


def piste_B_position_ranges(k_val, verbose=True):
    """
    Piste B : Pour chaque etat commun, comparer la plage de positions
    forward vs backward.
    """
    S, d, C = compute_params(k_val)
    if d <= 0:
        return None

    fwd = build_forward_layers(k_val, S, d)
    bwd = build_backward_layers(k_val, S, d)
    inv3 = pow(3, -1, d)

    if verbose:
        print(f"\n{'='*80}")
        print(f"PISTE B : PLAGES DE POSITIONS PAR ETAT — k={k_val}, S={S}, d={d}")
        print(f"{'='*80}")

    results = []
    for j in range(1, k_val - 1):  # Points de RDV intermediaires
        bwd_idx = k_val - 1 - j
        if bwd_idx >= len(bwd):
            continue

        # Grouper par etat
        fwd_by_state = defaultdict(list)
        for (s, p), c in fwd[j].items():
            fwd_by_state[s].append(p)

        bwd_by_state = defaultdict(list)
        for (s, p), c in bwd[bwd_idx].items():
            bwd_by_state[s].append(p)

        common = set(fwd_by_state.keys()) & set(bwd_by_state.keys())

        closest_gap = float('inf')
        closest_detail = None

        for s in common:
            fwd_positions = sorted(fwd_by_state[s])
            bwd_positions = sorted(bwd_by_state[s])

            # Le meilleur cas : min(bwd) - max(fwd)
            best_gap = min(bwd_positions) - max(fwd_positions)

            if best_gap < closest_gap:
                closest_gap = best_gap
                closest_detail = {
                    'state': s,
                    'fwd_range': (min(fwd_positions), max(fwd_positions)),
                    'bwd_range': (min(bwd_positions), max(bwd_positions)),
                    'gap': best_gap,
                }

        result = {
            'j': j,
            'common_states': len(common),
            'closest_gap': closest_gap,
            'detail': closest_detail,
        }
        results.append(result)

        if verbose:
            print(f"\n  RDV j={j} : {len(common)} etats communs")
            if closest_detail:
                d_info = closest_detail
                print(f"    Plus proche gap = {d_info['gap']}")
                print(f"    Etat s={d_info['state']}: "
                      f"fwd=[{d_info['fwd_range'][0]},{d_info['fwd_range'][1]}], "
                      f"bwd=[{d_info['bwd_range'][0]},{d_info['bwd_range'][1]}]")
                if d_info['gap'] <= 0:
                    print(f"    => OVERLAP de {-d_info['gap']} positions")

    return results


def piste_C_position_consumption(k_val, verbose=True):
    """
    Piste C : Combien de positions distinctes chaque couche "consomme" ?
    Si forward a j pas consomme >= j positions minimales,
    et backward a (k-1-j) pas consomme >= (k-1-j) positions,
    et j + (k-1-j) = k-1 >= S-1, alors c'est impossible.

    Mais k-1 < S-1 en general, donc cet argument simple ne marche pas.
    Regardons les positions EFFECTIVES (non pas minimales).
    """
    S, d, C = compute_params(k_val)
    if d <= 0:
        return None

    fwd = build_forward_layers(k_val, S, d)
    bwd = build_backward_layers(k_val, S, d)

    if verbose:
        print(f"\n{'='*80}")
        print(f"PISTE C : CONSOMMATION DE POSITIONS — k={k_val}, S={S}, d={d}")
        print(f"{'='*80}")
        print(f"  k-1 = {k_val-1} pas au total, S-1 = {S-1} positions disponibles")
        print(f"  Ratio : (k-1)/(S-1) = {(k_val-1)/(S-1):.3f}")

    # Pour chaque couche forward, quel est le range de positions ?
    if verbose:
        print(f"\n  Couches FORWARD :")
    fwd_ranges = []
    for j in range(len(fwd)):
        positions = [p for (s, p) in fwd[j].keys()]
        if positions:
            r = (min(positions), max(positions))
            fwd_ranges.append(r)
            if verbose:
                print(f"    j={j}: positions in [{r[0]}, {r[1]}], "
                      f"span={r[1]-r[0]}, distinct={len(set(positions))}/{S-1}")

    if verbose:
        print(f"\n  Couches BACKWARD :")
    bwd_ranges = []
    for m in range(len(bwd)):
        positions = [p for (s, p) in bwd[m].keys()]
        if positions:
            r = (min(positions), max(positions))
            bwd_ranges.append(r)
            if verbose:
                j_equiv = k_val - 1 - m  # etape equivalente dans le chemin complet
                print(f"    m={m} (<==> j={j_equiv}): positions in [{r[0]}, {r[1]}], "
                      f"span={r[1]-r[0]}, distinct={len(set(positions))}/{S-1}")

    # ANALYSE : au point de rendez-vous central j = (k-1)//2
    j_mid = (k_val - 1) // 2
    if j_mid < len(fwd_ranges) and (k_val - 1 - j_mid) < len(bwd_ranges):
        fwd_r = fwd_ranges[j_mid]
        bwd_r = bwd_ranges[k_val - 1 - j_mid]

        # Les forward utilisent des positions dans [fwd_r[0], fwd_r[1]]
        # Les backward utilisent des positions dans [bwd_r[0], bwd_r[1]]
        overlap = min(fwd_r[1], bwd_r[1]) - max(fwd_r[0], bwd_r[0])

        if verbose:
            print(f"\n  POINT CENTRAL j={j_mid}:")
            print(f"    Forward range:  [{fwd_r[0]}, {fwd_r[1]}]")
            print(f"    Backward range: [{bwd_r[0]}, {bwd_r[1]}]")
            print(f"    Overlap = {max(0, overlap + 1)} positions")
            if overlap >= 0:
                print(f"    => Les ranges se CHEVAUCHENT massivement")
            else:
                print(f"    => Les ranges sont SEPAREES (gap = {-overlap - 1})")

    return {'S': S, 'k': k_val, 'fwd_ranges': fwd_ranges, 'bwd_ranges': bwd_ranges}


def piste_D_horner_drift(k_val, verbose=True):
    """
    Piste D : Le "drift" de Horner.

    La transition c -> (3c + 2^p) mod d multiplie par 3.
    Si c est "petit" (c << d), alors 3c + 2^p est aussi relativement petit,
    sauf si 2^p est grand. Mais les petites positions donnent des petits 2^p.

    Hypothese : depuis c_0=1 (tres petit), le forward doit utiliser des
    positions de PLUS EN PLUS grandes pour "atteindre" des etats arbitraires.
    De meme, depuis c_{k-1}=0 (nul), le backward doit utiliser des
    positions de PLUS EN PLUS petites.

    Testons : position moyenne a chaque etape.
    """
    S, d, C = compute_params(k_val)
    if d <= 0:
        return None

    fwd = build_forward_layers(k_val, S, d)
    bwd = build_backward_layers(k_val, S, d)

    if verbose:
        print(f"\n{'='*80}")
        print(f"PISTE D : DRIFT DE HORNER — k={k_val}, S={S}, d={d}")
        print(f"{'='*80}")

    # Position moyenne ponderee a chaque etape forward
    if verbose:
        print(f"\n  FORWARD (depuis c_0=1) :")
        print(f"  {'etape':>6} {'pos_moy':>8} {'pos_med':>8} {'pos_min':>8} {'pos_max':>8} {'nb_chemins':>11}")

    for j in range(len(fwd)):
        positions = []
        for (s, p), c in fwd[j].items():
            positions.extend([p] * c)
        if positions:
            if verbose:
                print(f"  {j:6d} {statistics.mean(positions):8.1f} "
                      f"{statistics.median(positions):8.1f} "
                      f"{min(positions):8d} {max(positions):8d} "
                      f"{len(positions):11d}")

    # Position moyenne ponderee a chaque etape backward
    if verbose:
        print(f"\n  BACKWARD (depuis c_{k_val-1}=0) :")
        print(f"  {'etape_bwd':>9} {'pos_moy':>8} {'pos_med':>8} {'pos_min':>8} {'pos_max':>8} {'nb_chemins':>11}")

    for m in range(len(bwd)):
        positions = []
        for (s, p), c in bwd[m].items():
            positions.extend([p] * c)
        if positions:
            if verbose:
                print(f"  {m:9d} {statistics.mean(positions):8.1f} "
                      f"{statistics.median(positions):8.1f} "
                      f"{min(positions):8d} {max(positions):8d} "
                      f"{len(positions):11d}")

    return True


def piste_E_overlap_fraction(k_max=14, verbose=True):
    """
    Piste E : Pour chaque k, calculer la fraction de recouvrement
    au point de rendez-vous central.

    Definissons :
      fwd_max(j) = max position dans Forward_j
      bwd_min(k-1-j) = min position dans Backward_{k-1-j}
      overlap(j) = fwd_max(j) - bwd_min(k-1-j) + 1  (si > 0)

    Cherchons le j qui MINIMISE l'overlap (le "meilleur" point de RDV).
    """
    if verbose:
        print(f"\n{'='*80}")
        print(f"PISTE E : FRACTION DE RECOUVREMENT AU MEILLEUR RDV")
        print(f"{'='*80}")
        print(f"\n{'k':>3} {'S':>4} {'d':>10} {'best_j':>7} {'fwd_max':>8} "
              f"{'bwd_min':>8} {'overlap':>8} {'S-1':>5} {'overlap/(S-1)':>14}")
        print("-" * 80)

    results = []
    for k in range(3, k_max + 1):
        S, d, C = compute_params(k)
        if d <= 0 or C > 500000:
            continue

        fwd = build_forward_layers(k, S, d)
        bwd = build_backward_layers(k, S, d)

        best_j = None
        best_overlap = float('inf')
        best_fwd_max = None
        best_bwd_min = None

        for j in range(0, k):
            bwd_idx = k - 1 - j
            if bwd_idx >= len(bwd):
                continue

            fwd_positions = [p for (s, p) in fwd[j].keys()]
            bwd_positions = [p for (s, p) in bwd[bwd_idx].keys()]

            if not fwd_positions or not bwd_positions:
                continue

            fm = max(fwd_positions)
            bm = min(bwd_positions)
            ov = fm - bm + 1  # overlap (peut etre negatif = gap)

            if ov < best_overlap:
                best_overlap = ov
                best_j = j
                best_fwd_max = fm
                best_bwd_min = bm

        if best_j is not None:
            result = {
                'k': k, 'S': S, 'd': d,
                'best_j': best_j,
                'fwd_max': best_fwd_max,
                'bwd_min': best_bwd_min,
                'overlap': best_overlap,
                'overlap_frac': best_overlap / (S - 1) if S > 1 else 0,
            }
            results.append(result)

            if verbose:
                print(f"{k:3d} {S:4d} {d:10d} {best_j:7d} {best_fwd_max:8d} "
                      f"{best_bwd_min:8d} {best_overlap:8d} {S-1:5d} "
                      f"{best_overlap/(S-1):14.3f}")

    if verbose:
        print(f"\nSi overlap > 0 pour TOUS les k, les positions sont TOUJOURS incompatibles.")
        all_positive = all(r['overlap'] > 0 for r in results)
        print(f"Resultat : {'OUI !!!' if all_positive else 'NON (des gaps existent)'}")

        if all_positive:
            min_frac = min(r['overlap_frac'] for r in results)
            max_frac = max(r['overlap_frac'] for r in results)
            print(f"Overlap/(S-1) in [{min_frac:.3f}, {max_frac:.3f}]")
            print(f"L'overlap est toujours une fraction SIGNIFICATIVE de S-1.")

    return results


def piste_F_state_position_correlation(k_val, verbose=True):
    """
    Piste F : Y a-t-il une CORRELATION entre l'etat et la position ?

    Hypothese : pour atteindre un etat donne s via forward, il faut des
    positions "hautes" (proches de S). Pour atteindre le meme etat via
    backward, il faut des positions "basses" (proches de 1).

    Si cette correlation existe, elle expliquerait l'incompatibilite.
    """
    S, d, C = compute_params(k_val)
    if d <= 0:
        return None

    fwd = build_forward_layers(k_val, S, d)
    bwd = build_backward_layers(k_val, S, d)

    j_mid = (k_val - 1) // 2
    bwd_idx = k_val - 1 - j_mid

    if j_mid >= len(fwd) or bwd_idx >= len(bwd):
        return None

    if verbose:
        print(f"\n{'='*80}")
        print(f"PISTE F : CORRELATION ETAT-POSITION au RDV central j={j_mid}")
        print(f"k={k_val}, S={S}, d={d}")
        print(f"{'='*80}")

    # Pour chaque etat commun, position moyenne forward vs backward
    fwd_by_state = defaultdict(list)
    for (s, p), c in fwd[j_mid].items():
        fwd_by_state[s].extend([p] * c)

    bwd_by_state = defaultdict(list)
    for (s, p), c in bwd[bwd_idx].items():
        bwd_by_state[s].extend([p] * c)

    common = sorted(set(fwd_by_state.keys()) & set(bwd_by_state.keys()))

    if verbose and len(common) <= 30:
        print(f"\n  {'etat':>8} {'fwd_moy':>8} {'bwd_moy':>8} {'gap_moy':>8}")
        print(f"  " + "-" * 36)
        for s in common[:30]:
            fm = statistics.mean(fwd_by_state[s])
            bm = statistics.mean(bwd_by_state[s])
            print(f"  {s:8d} {fm:8.1f} {bm:8.1f} {bm - fm:8.1f}")

    if common:
        all_gaps = []
        for s in common:
            fm = statistics.mean(fwd_by_state[s])
            bm = statistics.mean(bwd_by_state[s])
            all_gaps.append(bm - fm)

        if verbose:
            print(f"\n  Nombre d'etats communs : {len(common)}")
            print(f"  Gap moyen (bwd_moy - fwd_moy) : {statistics.mean(all_gaps):.2f}")
            print(f"  Gap min : {min(all_gaps):.2f}")
            print(f"  Gap max : {max(all_gaps):.2f}")
            print(f"  Gap > 0 pour TOUS les etats ? "
                  f"{'OUI' if all(g > 0 for g in all_gaps) else 'NON'}")
            print(f"  Gap > 0 dans {sum(1 for g in all_gaps if g > 0)}/{len(all_gaps)} etats")

    return common


# ============================================================
# EXECUTION
# ============================================================

if __name__ == "__main__":
    print("*" * 80)
    print("ANALYSE DE L'INCOMPATIBILITE DES POSITIONS")
    print("*" * 80)

    # Piste E d'abord (vue d'ensemble)
    print("\n\n" + "=" * 80)
    print("PISTE E : VUE D'ENSEMBLE (k=3..14)")
    print("=" * 80)
    piste_E_overlap_fraction(k_max=14)

    # Piste A pour quelques k representatifs
    for k in [5, 6, 8, 10]:
        piste_A_position_moyennes(k)

    # Piste D (drift de Horner) pour k=6
    piste_D_horner_drift(6)

    # Piste C (consommation de positions) pour k=6
    piste_C_position_consumption(6)

    # Piste F (correlation etat-position) pour k=5 et k=6
    piste_F_state_position_correlation(5)
    piste_F_state_position_correlation(6)
