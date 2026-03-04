#!/usr/bin/env python3
"""
TEST DE L'HYPOTHESE DE LA POSITION FANTOME
==========================================
Section 6.2 du BLOCKING_MECHANISM_PROOF_SKETCH.md

HYPOTHESE : L'etat (-3^{k-1} mod d) est toujours atteignable
a l'etape k-2 de l'automate de Horner.

Si cette hypothese est vraie, alors :
  - En ajoutant la position fantome p=S, on pourrait transiter
    de (-3^{k-1} mod d) vers 0 via : 3*(-3^{k-1}) + 2^S = -3^k + 3^k = 0 mod d
  - La SEULE raison pour laquelle 0 n'est pas atteint est
    l'exclusion de p=S.

On teste aussi une version plus forte :
  Pour CHAQUE etat (c, p) dans la couche k-2 avec c = (-3^{k-1} mod d),
  la position p est-elle >= S-1 ? (ce qui signifie qu'il n'y a plus
  de position disponible au-dela de p, sauf S qui est interdit)
"""

from itertools import combinations
from collections import defaultdict
import math


def test_phantom_position(k_val):
    """Teste l'hypothese de la position fantome pour un k donne."""
    S = math.ceil(k_val * math.log2(3))
    d = 2**S - 3**k_val
    C = math.comb(S - 1, k_val - 1)

    if d <= 0:
        return None

    # L'etat cible : -3^{k-1} mod d
    target_state = (-pow(3, k_val - 1, d)) % d

    # Verification : depuis target_state avec p=S, on atteint 0 ?
    check = (3 * target_state + pow(2, S, d)) % d
    assert check == 0, f"Erreur : 3*{target_state} + 2^{S} != 0 mod {d}, got {check}"

    # Construire l'automate couche par couche
    # Layer = dict de (state, last_pos) -> count
    layers = [{(1 % d, 0): 1}]  # Etat initial = 1, position initiale = 0

    for step in range(1, k_val):
        current = layers[-1]
        next_layer = defaultdict(int)
        for (state, last_pos), count in current.items():
            for p in range(last_pos + 1, S):
                next_state = (3 * state + pow(2, p, d)) % d
                next_layer[(next_state, p)] += count
        layers.append(dict(next_layer))

    # Verifier si target_state est dans la couche k-2
    # (couche k-2 = layers[k_val - 2] car layers[0] = etape 0)
    if k_val - 2 < 0:
        # k=2 n'est pas traite (k >= 3)
        return None

    penultimate = layers[k_val - 2]  # Avant-derniere couche (etape k-2)
    final = layers[k_val - 1]  # Derniere couche (etape k-1)

    # Etats dans la couche k-2
    states_penult = defaultdict(int)
    positions_for_target = []
    for (s, p), c in penultimate.items():
        states_penult[s] += c
        if s == target_state:
            positions_for_target.append((p, c))

    target_reachable = target_state in states_penult
    target_count = states_penult.get(target_state, 0)
    total_penult = sum(states_penult.values())

    # Verifier aussi la couche finale
    states_final = defaultdict(int)
    for (s, p), c in final.items():
        states_final[s] += c
    N0 = states_final.get(0, 0)

    # Pour les positions du target dans la couche k-2 :
    # La transition vers 0 necessite 2^q = (-3 * target_state) mod d avec q > p
    # Or (-3 * target_state) mod d = 3^k mod d = 2^S mod d
    # Donc on a besoin de 2^q = 2^S mod d, c'est-a-dire q = S mod ord_d(2)
    # La plus petite solution est q = S (si ord_d(2) > S-1, alors S est
    # la seule solution dans {p+1, ..., S})

    need_residue = pow(2, S, d)  # = 3^k mod d

    # Chercher les positions q dans {1,...,S-1} qui donnent 2^q = need_residue mod d
    valid_positions_for_zero = []
    for q in range(1, S):
        if pow(2, q, d) == need_residue:
            valid_positions_for_zero.append(q)

    # Si valid_positions_for_zero est vide, cela signifie que
    # la SEULE position qui donne le bon residu est q = S (interdit!)
    phantom_is_only_option = len(valid_positions_for_zero) == 0

    # Meme si des positions alternatives existent, sont-elles utilisables
    # depuis les etats (target_state, p) dans la couche k-2 ?
    usable_alternatives = []
    for q in valid_positions_for_zero:
        for (p, c) in positions_for_target:
            if q > p:
                usable_alternatives.append((q, p, c))

    print(f"\n{'='*80}")
    print(f"k={k_val}, S={S}, d={d}, C={C}, C/d={C/d:.4f}")
    print(f"{'='*80}")
    print(f"  Etat fantome : -3^{k_val-1} mod {d} = {target_state}")
    print(f"  Verification : 3*{target_state} + 2^{S} mod {d} = {check} (doit etre 0)")
    print(f"  N_0(d) = {N0} (doit etre 0)")
    print(f"\n  Couche k-2 (etape {k_val-2}) :")
    print(f"    {total_penult} chemins, {len(states_penult)} etats distincts")
    print(f"    Etat {target_state} atteignable ? {'OUI' if target_reachable else 'NON'}")
    if target_reachable:
        print(f"    Nombre de chemins vers etat {target_state} : {target_count}")
        print(f"    Positions depuis lesquelles : {sorted(positions_for_target)}")

    print(f"\n  Analyse du dernier pas (vers 0 depuis etat {target_state}) :")
    print(f"    Besoin : 2^q = {need_residue} mod {d} (= 2^S mod d = 3^k mod d)")
    if valid_positions_for_zero:
        print(f"    Positions q in {{1,...,{S-1}}} avec 2^q = {need_residue} : {valid_positions_for_zero}")
    else:
        print(f"    AUCUNE position q in {{1,...,{S-1}}} avec 2^q = {need_residue} mod {d}")
        print(f"    ==> La position fantome q={S} est la SEULE option !")

    print(f"    Position fantome q={S} necessaire seule ? {'OUI' if phantom_is_only_option else 'NON'}")

    if not phantom_is_only_option and target_reachable:
        if usable_alternatives:
            print(f"    Alternatives UTILISABLES (q > p_last) : {usable_alternatives}")
            print(f"    ATTENTION : des alternatives existent et sont utilisables !")
            print(f"    ==> L'hypothese de la position fantome est INSUFFISANTE pour ce k")
        else:
            print(f"    Alternatives INUTILISABLES (toutes q <= p_last) :")
            for q in valid_positions_for_zero:
                for (p, c) in positions_for_target:
                    print(f"      q={q} <= p={p} (bloque par contrainte d'ordre)")
            print(f"    ==> La position fantome reste NECESSAIRE (alternatives consommees)")

    return {
        'k': k_val, 'S': S, 'd': d, 'C': C,
        'target_state': target_state,
        'target_reachable': target_reachable,
        'target_count': target_count,
        'phantom_only': phantom_is_only_option,
        'valid_alt_positions': valid_positions_for_zero,
        'usable_alternatives': usable_alternatives,
        'N0': N0
    }


# ============================================================
# Executer pour k = 3..17
# ============================================================

print("*" * 80)
print("TEST DE L'HYPOTHESE DE LA POSITION FANTOME")
print("*" * 80)

results = []
for k in range(3, 18):
    S = math.ceil(k * math.log2(3))
    d = 2**S - 3**k
    C = math.comb(S - 1, k - 1)
    if d <= 0 or C > 2_000_000:  # Limiter la complexite
        print(f"\nk={k}: SKIP (C={C} trop grand ou d={d} <= 0)")
        continue
    r = test_phantom_position(k)
    if r:
        results.append(r)


# ============================================================
# Synthese
# ============================================================

print(f"\n\n{'='*80}")
print(f"SYNTHESE : HYPOTHESE DE LA POSITION FANTOME")
print(f"{'='*80}")

print(f"\n{'k':>3} {'d':>10} {'target':>8} {'reach?':>7} {'count':>6} "
      f"{'phantom_only':>13} {'alt_pos':>8} {'usable':>7} {'N0':>4}")
print("-" * 80)

for r in results:
    reach_str = "OUI" if r['target_reachable'] else "NON"
    phantom_str = "OUI" if r['phantom_only'] else "non"
    alt_str = str(r['valid_alt_positions']) if r['valid_alt_positions'] else "[]"
    usable_str = str(len(r['usable_alternatives'])) if r['usable_alternatives'] else "0"
    print(f"{r['k']:3d} {r['d']:10d} {r['target_state']:8d} {reach_str:>7} "
          f"{r['target_count']:6d} {phantom_str:>13} {alt_str:>8} {usable_str:>7} {r['N0']:4d}")

# Conclusion
all_reachable = all(r['target_reachable'] for r in results)
all_phantom_only = all(r['phantom_only'] for r in results)
no_usable_alt = all(len(r['usable_alternatives']) == 0 for r in results)

print(f"\n--- VERDICTS ---")
print(f"  Etat fantome toujours atteignable a l'etape k-2 ? "
      f"{'OUI !!!' if all_reachable else 'NON'}")
print(f"  Position fantome p=S toujours seule option ?      "
      f"{'OUI !!!' if all_phantom_only else 'NON'}")
print(f"  Aucune alternative utilisable ?                    "
      f"{'OUI !!!' if no_usable_alt else 'NON'}")

if all_reachable and no_usable_alt:
    print(f"\n  ==> HYPOTHESE CONFIRMEE : Pour tout k teste,")
    print(f"      l'etat -3^{{k-1}} mod d EST atteignable a l'etape k-2,")
    print(f"      ET la seule facon de transiter vers 0 est via p=S (interdit).")
    print(f"      C'est la CLE du mecanisme de blocage !")
elif all_reachable and not no_usable_alt:
    print(f"\n  ==> HYPOTHESE PARTIELLEMENT CONFIRMEE :")
    print(f"      L'etat fantome est toujours atteignable,")
    print(f"      MAIS pour certains k, des positions alternatives existent")
    print(f"      et sont utilisables. L'hypothese simple est INSUFFISANTE.")
elif not all_reachable:
    print(f"\n  ==> HYPOTHESE REFUTEE pour certains k :")
    print(f"      L'etat fantome n'est PAS toujours atteignable.")
    for r in results:
        if not r['target_reachable']:
            print(f"      k={r['k']} : etat {r['target_state']} NON ATTEIGNABLE")
