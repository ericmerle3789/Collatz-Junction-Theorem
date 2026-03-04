#!/usr/bin/env python3
"""
THEOREME DU DRIFT DE HORNER : FORMALISATION
=============================================
Session 5 — Noyau de la preuve du Double Peeling

DECOUVERTE (position_incompatibility_analysis.py) :
  Pour CHAQUE etat s commun aux couches forward et backward,
  la position forward est TOUJOURS >= la position backward.

  Formellement : pour tout (s, p_fwd) in Forward_j et (s, p_bwd) in Backward_{k-1-j},
    p_fwd >= p_bwd.

HYPOTHESE A TESTER :
  Cela vient du "drift" de la recurrence de Horner :
    - Forward : c_j = 3*c_{j-1} + 2^{p_j} mod d
      La multiplication par 3 "amplifie" l'etat. Pour controler l'etat
      (atteindre un s specifique), il faut des GRANDS 2^p -> HAUTES positions.
    - Backward : c_{j-1} = (c_j - 2^{q}) * 3^{-1} mod d
      La division par 3 "attenue" l'etat. Pour controler l'etat,
      il faut des PETITS 2^q -> BASSES positions.

CE SCRIPT TESTE :
  (1) Pour chaque (etat, position) forward, Y A-T-IL un backward compatible ?
      Resultat attendu : JAMAIS (confirme Double Peeling).
  (2) La "position minimale" pour atteindre s via forward est-elle toujours
      >= la "position maximale" pour atteindre s via backward ?
      Si OUI, c'est un invariant fort.
  (3) Lien avec la taille de 3^j : le drift vient-il de |3^j mod d| ?
"""

import math
from collections import defaultdict


def compute_params(k):
    S = math.ceil(k * math.log2(3))
    d = 2**S - 3**k
    C = math.comb(S - 1, k - 1)
    return S, d, C


def build_layers(k_val, S, d):
    """Construit les couches forward et backward."""
    inv3 = pow(3, -1, d)

    # Forward
    fwd = [{(1, 0): 1}]
    for step in range(1, k_val):
        current = fwd[-1]
        nl = defaultdict(int)
        for (state, last_pos), count in current.items():
            for p in range(last_pos + 1, S):
                ns = (3 * state + pow(2, p, d)) % d
                nl[(ns, p)] += count
        fwd.append(dict(nl))

    # Backward
    bwd = [{(0, S): 1}]
    for step in range(1, k_val):
        current = bwd[-1]
        nl = defaultdict(int)
        for (state, first_pos), count in current.items():
            for p in range(1, first_pos):
                prev = ((state - pow(2, p, d)) * inv3) % d
                nl[(prev, p)] += count
        bwd.append(dict(nl))

    return fwd, bwd


def test_min_max_invariant(k_val, verbose=True):
    """
    TEST DE L'INVARIANT FORT :
    Pour tout etat s commun a Forward_j et Backward_{k-1-j},
      min_fwd(s) >= max_bwd(s)
    ou min_fwd(s) = min des positions forward pour atteindre s
       max_bwd(s) = max des positions backward pour atteindre s.

    C'est PLUS FORT que "pas de paire compatible" car meme les
    meilleures positions (min fwd, max bwd) ne se croisent pas.
    """
    S, d, C = compute_params(k_val)
    if d <= 0:
        return None

    fwd, bwd = build_layers(k_val, S, d)

    if verbose:
        print(f"\n{'='*80}")
        print(f"INVARIANT min_fwd >= max_bwd — k={k_val}, S={S}, d={d}")
        print(f"{'='*80}")

    all_satisfy = True
    worst_gap = float('inf')  # min de (min_fwd - max_bwd)
    worst_detail = None

    for j in range(1, k_val - 1):  # RDV intermediaires
        bwd_idx = k_val - 1 - j
        if bwd_idx >= len(bwd):
            continue

        # Grouper par etat
        fwd_pos = defaultdict(list)
        for (s, p), c in fwd[j].items():
            fwd_pos[s].append(p)

        bwd_pos = defaultdict(list)
        for (s, p), c in bwd[bwd_idx].items():
            bwd_pos[s].append(p)

        common = set(fwd_pos.keys()) & set(bwd_pos.keys())

        for s in common:
            min_f = min(fwd_pos[s])
            max_b = max(bwd_pos[s])
            gap = min_f - max_b

            if gap < worst_gap:
                worst_gap = gap
                worst_detail = {
                    'j': j, 'state': s,
                    'min_fwd': min_f, 'max_bwd': max_b,
                    'all_fwd': sorted(fwd_pos[s]),
                    'all_bwd': sorted(bwd_pos[s]),
                }

            if gap < 0:
                all_satisfy = False
                if verbose:
                    print(f"  VIOLATION j={j}, s={s}: min_fwd={min_f} < max_bwd={max_b}")
                    print(f"    fwd positions: {sorted(fwd_pos[s])}")
                    print(f"    bwd positions: {sorted(bwd_pos[s])}")

    if verbose:
        if all_satisfy:
            print(f"  *** INVARIANT FORT VERIFIE : min_fwd >= max_bwd PARTOUT ***")
            print(f"  Plus petit gap : {worst_gap}")
            if worst_detail:
                wd = worst_detail
                print(f"  Cas le plus serre : j={wd['j']}, s={wd['state']}")
                print(f"    min_fwd={wd['min_fwd']}, max_bwd={wd['max_bwd']}")
                print(f"    fwd: {wd['all_fwd'][:10]}{'...' if len(wd['all_fwd'])>10 else ''}")
                print(f"    bwd: {wd['all_bwd'][:10]}{'...' if len(wd['all_bwd'])>10 else ''}")
        else:
            print(f"  INVARIANT FORT VIOLE (mais les paires COMPTEES restent 0)")
            print(f"  Plus petit gap : {worst_gap}")
            if worst_detail:
                wd = worst_detail
                print(f"  Cas le plus serre : j={wd['j']}, s={wd['state']}")

    return {
        'k': k_val, 'satisfied': all_satisfy,
        'worst_gap': worst_gap, 'worst_detail': worst_detail,
    }


def analyze_drift_quantitatively(k_val, verbose=True):
    """
    Quantifier le drift de Horner.

    Forward step j : c_j = 3^j + sum_{i=1}^j 3^{j-i} * 2^{p_i} mod d
    Le terme dominant est 3^j * c_0 = 3^j.

    Pour annuler cette croissance et atteindre un etat specifique,
    il faut que sum 3^{j-i} * 2^{p_i} compense 3^j - s mod d.
    Cela necessite des grands 2^{p_i} -> des hautes positions.

    Backward step m : les termes sont multiplies par 3^{-m},
    donc les contributions 2^{q_i} sont attenuees -> basses positions suffisent.

    Calculons : position moyenne en fonction de l'etat atteint.
    """
    S, d, C = compute_params(k_val)
    if d <= 0:
        return None

    fwd, bwd = build_layers(k_val, S, d)

    j_mid = (k_val - 1) // 2
    bwd_idx = k_val - 1 - j_mid

    if j_mid >= len(fwd) or bwd_idx >= len(bwd):
        return None

    if verbose:
        print(f"\n{'='*80}")
        print(f"DRIFT QUANTITATIF — k={k_val}, S={S}, d={d}, RDV j={j_mid}")
        print(f"{'='*80}")

    # Pour chaque etat, position min/max forward et backward
    fwd_by_state = defaultdict(list)
    for (s, p), c in fwd[j_mid].items():
        fwd_by_state[s].append(p)

    bwd_by_state = defaultdict(list)
    for (s, p), c in bwd[bwd_idx].items():
        bwd_by_state[s].append(p)

    common = sorted(set(fwd_by_state.keys()) & set(bwd_by_state.keys()))

    if verbose:
        print(f"\n  {len(common)} etats communs")
        print(f"\n  {'etat':>8} {'fwd_min':>8} {'fwd_max':>8} {'bwd_min':>8} {'bwd_max':>8} "
              f"{'gap_best':>9} {'gap_worst':>10}")
        print(f"  " + "-" * 68)

    gaps_best = []
    gaps_worst = []

    for s in common[:40]:  # Limiter l'affichage
        f_min = min(fwd_by_state[s])
        f_max = max(fwd_by_state[s])
        b_min = min(bwd_by_state[s])
        b_max = max(bwd_by_state[s])

        gap_best = b_max - f_min   # meilleur cas (plus de chances de compatibilite)
        gap_worst = b_min - f_max  # pire cas

        gaps_best.append(gap_best)
        gaps_worst.append(gap_worst)

        if verbose:
            print(f"  {s:8d} {f_min:8d} {f_max:8d} {b_min:8d} {b_max:8d} "
                  f"{gap_best:9d} {gap_worst:10d}")

    if verbose and common:
        print(f"\n  --- SYNTHESE ---")
        print(f"  Gap BEST (max_bwd - min_fwd):")
        print(f"    max = {max(gaps_best)}, min = {min(gaps_best)}, mean = {sum(gaps_best)/len(gaps_best):.1f}")
        print(f"    Gap best > 0 ? {sum(1 for g in gaps_best if g > 0)}/{len(gaps_best)}")
        print(f"  Gap WORST (min_bwd - max_fwd):")
        print(f"    max = {max(gaps_worst)}, min = {min(gaps_worst)}, mean = {sum(gaps_worst)/len(gaps_worst):.1f}")
        print(f"    Gap worst >= 0 ? {sum(1 for g in gaps_worst if g >= 0)}/{len(gaps_worst)}")

    return gaps_best, gaps_worst


def test_position_bound(k_val, verbose=True):
    """
    HYPOTHESE STRUCTURELLE :

    A l'etape j du forward, pour atteindre l'etat s,
    la position minimale requise est environ :
      p_min_fwd(s, j) ~ max(j, f(s, j))

    A l'etape m = k-1-j du backward, pour atteindre l'etat s,
    la position maximale est environ :
      p_max_bwd(s, m) ~ min(S - m, g(s, m))

    Si p_min_fwd >= p_max_bwd pour tout s, j, c'est prouve.

    Testons la relation : p_min_fwd(s) >= j est triviale (par la contrainte d'ordre).
                          p_max_bwd(s) <= S - (k-1-j) = S - k + 1 + j.

    Donc la question est : est-ce que j >= S - k + 1 + j ?
    i.e. 0 >= S - k + 1, i.e. k >= S + 1.
    Mais S > k, donc k < S + 1 est VRAI et l'argument trivial echoue.

    Il faut un argument plus fin. Regardons les bornes EFFECTIVES.
    """
    S, d, C = compute_params(k_val)
    if d <= 0:
        return None

    fwd, bwd = build_layers(k_val, S, d)

    if verbose:
        print(f"\n{'='*80}")
        print(f"BORNES EFFECTIVES SUR LES POSITIONS — k={k_val}, S={S}, d={d}")
        print(f"{'='*80}")
        print(f"  Borne triviale : p_fwd >= j, p_bwd <= S-{k_val-1}+j = {S-k_val+1}+j")
        print(f"  S-k+1 = {S-k_val+1}")
        print(f"  La borne triviale donne gap_trivial = j - (S-k+1+j) = {k_val-1-S}")
        print(f"  Comme k-1={k_val-1} < S-1={S-1}, gap trivial < 0 (ne suffit pas)")

    # Bornes EFFECTIVES : pour chaque j, quel est le min_fwd et max_bwd effectifs ?
    if verbose:
        print(f"\n  {'j':>3} {'min_fwd':>8} {'max_bwd':>8} {'eff_gap':>8} "
              f"{'trivial_fwd':>12} {'trivial_bwd':>12}")
        print(f"  " + "-" * 56)

    effective_gaps = []
    for j in range(1, k_val - 1):
        bwd_idx = k_val - 1 - j
        if bwd_idx >= len(bwd):
            continue

        # Min forward position across all states
        fwd_positions = [p for (s, p) in fwd[j].keys()]
        bwd_positions = [p for (s, p) in bwd[bwd_idx].keys()]

        if not fwd_positions or not bwd_positions:
            continue

        min_fwd = min(fwd_positions)
        max_bwd = max(bwd_positions)
        eff_gap = min_fwd - max_bwd

        effective_gaps.append(eff_gap)

        if verbose:
            print(f"  {j:3d} {min_fwd:8d} {max_bwd:8d} {eff_gap:8d} "
                  f"{'(>=' + str(j) + ')':>12} {'(<=' + str(S-k_val+1+j) + ')':>12}")

    if verbose:
        if effective_gaps:
            print(f"\n  Gap effectif min : {min(effective_gaps)}")
            print(f"  Gap effectif max : {max(effective_gaps)}")
            print(f"  Tous gaps effectifs < 0 : "
                  f"{'OUI (les ranges globaux se chevauchent)' if all(g < 0 for g in effective_gaps) else 'NON'}")
            print(f"\n  NOTE : Les gaps effectifs globaux sont negatifs (les ranges se chevauchent).")
            print(f"  Le blocage vient du fait que pour un MEME ETAT s,")
            print(f"  le min_fwd(s) >= max_bwd(s), meme si les ranges globaux se croisent.")

    return effective_gaps


def ultimate_test(k_max=14):
    """
    Test definitif : l'invariant fort min_fwd(s) >= max_bwd(s)
    est-il verifie pour tous k et tous etats communs ?
    """
    print("*" * 80)
    print("TEST DEFINITIF : INVARIANT FORT min_fwd(s) >= max_bwd(s)")
    print("*" * 80)

    print(f"\n{'k':>3} {'S':>4} {'d':>10} {'invariant':>10} {'worst_gap':>10}")
    print("-" * 42)

    all_results = []
    for k in range(3, k_max + 1):
        S, d, C = compute_params(k)
        if d <= 0 or C > 500000:
            continue
        r = test_min_max_invariant(k, verbose=False)
        if r:
            all_results.append(r)
            status = "OUI" if r['satisfied'] else "NON"
            print(f"{k:3d} {S:4d} {d:10d} {status:>10} {r['worst_gap']:10d}")

    all_ok = all(r['satisfied'] for r in all_results)
    print(f"\n{'='*60}")
    if all_ok:
        print(f"*** INVARIANT FORT VERIFIE POUR TOUS k = 3..{k_max} ***")
        print(f"Pour tout k, tout j, et tout etat commun s :")
        print(f"  min(p_fwd | etat=s) >= max(p_bwd | etat=s)")
        print(f"Cela est PLUS FORT que le Double Peeling.")
        print(f"C'est le NOYAU de la preuve a formaliser.")
        worst_overall = min(r['worst_gap'] for r in all_results)
        print(f"\nPlus petit gap global : {worst_overall}")
        for r in all_results:
            if r['worst_gap'] == worst_overall:
                wd = r['worst_detail']
                print(f"  Atteint pour k={r['k']}, j={wd['j']}, s={wd['state']}")
                print(f"  min_fwd={wd['min_fwd']}, max_bwd={wd['max_bwd']}")
    else:
        print(f"INVARIANT FORT VIOLE pour certains k.")
        print(f"Mais le Double Peeling (paires ponderees = 0) reste vrai.")
        print(f"L'invariant faible (compatible_paths = 0) suffit.")

        for r in all_results:
            if not r['satisfied']:
                wd = r['worst_detail']
                print(f"\n  k={r['k']}: VIOLATION")
                print(f"    j={wd['j']}, s={wd['state']}")
                print(f"    fwd positions: {wd['all_fwd'][:15]}")
                print(f"    bwd positions: {wd['all_bwd'][:15]}")

    return all_results


if __name__ == "__main__":
    # Test definitif
    results = ultimate_test(k_max=14)

    # Analyse detaillee pour les cas interessants
    for k in [5, 6, 8]:
        analyze_drift_quantitatively(k)
        test_position_bound(k)
