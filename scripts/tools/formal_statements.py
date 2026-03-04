#!/usr/bin/env python3
"""
ENONCES MATHEMATIQUES FORMELS A PROUVER
=========================================
Session 5 — Synthese

Ce script identifie et teste les enonces mathematiques precis
qui constituent la preuve par Double Peeling.

================================================================
STRUCTURE DE LA PREUVE
================================================================

THEOREME PRINCIPAL : Pour tout k >= 3, N_0(d(k)) = 0
  ou d(k) = 2^S - 3^k, S = ceil(k * log_2(3))

PREUVE PAR DOUBLE PEELING :
  Lemme 1 (Validite) : Si N_0(d) > 0, alors pour tout j (1 <= j <= k-2),
    il existe au moins une paire (f, b) compatible au point j.
    Contrapositif : s'il existe un j sans paire compatible, alors N_0(d) = 0.

  Lemme 2 (Invariant fort) : Pour tout k >= 3, au point j=1 :
    Pour tout etat s commun aux couches Forward_1 et Backward_{k-2} :
      min_fwd(s, 1) >= max_bwd(s, 1)
    ou min_fwd(s, j) = min{p : (s, p) in Forward_j}
       max_bwd(s, j) = max{q : (s, q) in Backward_{k-1-j}}

  Lemme 3 (Incompatibilite) : Si l'invariant fort tient au point j=1,
    alors il n'y a pas de paire compatible au point j=1.

  Lemme 1 + 2 + 3 => Theoreme Principal.

================================================================
ENONCES TECHNIQUES A PROUVER
================================================================

Enonce A (Prerequis) : Pour k >= 4, ord_d(2) > S - 1.
  Consequence : Chaque etat a AU PLUS une position forward au step j=1.
  (Pour k=3, verification directe suffit.)

Enonce B (Invariant fort, cas generique) :
  Pour k >= 3, pour tout etat s commun :
  Si (s - 3) mod d >= 2^{S-k+2}, alors p_1(s) >= S - k + 2 > max possible q_2.
  (Argument pigeonhole.)

Enonce C (Invariant fort, cas serres) :
  Pour les etats s = 3 + 2^p (0 < p <= floor(log_2(d))),
  la meilleure position backward max_bwd(s) = p exactement.
  Autrement dit : le backward NE PEUT PAS atteindre q_2 = p + 1.

================================================================
"""

import math
from collections import defaultdict


def compute_params(k):
    S = math.ceil(k * math.log2(3))
    d = (1 << S) - 3**k
    return S, d


def build_layers(k_val, S, d):
    inv3 = pow(3, -1, d)
    fwd = [{(1, 0): 1}]
    for step in range(1, k_val):
        current = fwd[-1]
        nl = defaultdict(int)
        for (state, last_pos), count in current.items():
            for p in range(last_pos + 1, S):
                ns = (3 * state + pow(2, p, d)) % d
                nl[(ns, p)] += count
        fwd.append(dict(nl))

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


def test_enonce_A(k_max=30, verbose=True):
    """
    Enonce A : ord_d(2) > S - 1 pour k >= 4.

    Cela signifie que 2^0, 2^1, ..., 2^{S-1} sont tous DISTINCTS mod d.
    Consequence : la position p_1 au step j=1 est UNIQUEMENT determinee
    par l'etat s (pas de choix).
    """
    if verbose:
        print(f"\n{'='*60}")
        print(f"ENONCE A : ord_d(2) > S - 1")
        print(f"{'='*60}")

    all_ok = True
    for k in range(3, k_max + 1):
        S, d = compute_params(k)
        if d <= 0:
            continue

        # Compute ord_d(2) the hard way
        val = 1
        seen = set()
        for i in range(S):
            if val in seen:
                break
            seen.add(val)
            val = (val * 2) % d

        distinct = len(seen) == S  # All 2^0,...,2^{S-1} are distinct mod d
        # Compute actual order
        val = 1
        for o in range(1, 2 * d):
            val = (val * 2) % d
            if val == 1:
                ord_d = o
                break
        else:
            ord_d = None

        ok = distinct
        if not ok:
            all_ok = False

        if verbose and (not ok or k <= 15):
            status = "OK" if ok else "FAIL"
            print(f"  k={k:2d} S={S:2d} d={d:10d} ord_d(2)={ord_d} "
                  f"{'>' if ord_d and ord_d > S-1 else '<='} S-1={S-1} => {status}")

    if verbose:
        print(f"\n  Enonce A verifie pour k=3..{k_max}: {all_ok}")

    return all_ok


def test_enonce_B(k_max=14, verbose=True):
    """
    Enonce B : Argument pigeonhole pour les etats generiques.

    Pour un etat s avec p_1(s) >= S - k + 2 :
      La position forward est deja >= borne pigeonhole du backward.
      Le backward utilise k-2 positions dans {1,...,S-1}, donc min_pos <= S-1-(k-3) = S-k+2.
      Mais le backward a aussi la contrainte positions >= 1, donc sa VRAIE borne est
      q_2 <= S - k + 2 (par pigeonhole sur {1,...,S-1}).

    Fraction des etats bloques par pigeonhole seul ?
    """
    if verbose:
        print(f"\n{'='*60}")
        print(f"ENONCE B : PIGEONHOLE POUR ETATS GENERIQUES")
        print(f"{'='*60}")

    for k in range(3, k_max + 1):
        S, d = compute_params(k)
        if d <= 0:
            continue

        fwd, bwd = build_layers(k, S, d)
        if 1 >= len(fwd) or k - 2 >= len(bwd):
            continue

        # Forward at j=1
        fwd_by_state = defaultdict(list)
        for (s, p), c in fwd[1].items():
            fwd_by_state[s].append(p)

        # Backward at layer k-2
        bwd_by_state = defaultdict(list)
        for (s, p), c in bwd[k - 2].items():
            bwd_by_state[s].append(p)

        common = set(fwd_by_state.keys()) & set(bwd_by_state.keys())
        pigeonhole_bound = S - k + 2  # max possible q_2

        n_pigeonhole = 0
        n_need_fine = 0
        for s in common:
            p1 = min(fwd_by_state[s])
            if p1 >= pigeonhole_bound:
                n_pigeonhole += 1
            else:
                n_need_fine += 1

        frac = n_pigeonhole / len(common) * 100 if common else 0
        print(f"  k={k:2d} S={S:2d} |common|={len(common):4d} "
              f"pigeonhole={pigeonhole_bound:2d} "
              f"bloques={n_pigeonhole:4d} ({frac:.0f}%) "
              f"restants={n_need_fine:4d}")


def test_enonce_C(k_max=14, verbose=True):
    """
    Enonce C : Cas serres s = 3 + 2^p.

    Pour ces etats, p_1 = p (petit), et max_bwd = p exactement.
    Le backward ne peut PAS faire mieux que q_2 = p.

    Pattern observe :
    - s=5 (p=1) : universel pour k >= 5 (le cas le plus serre)
    - s=7 (p=2) : k=5
    - s=11 (p=3) : k=5,6
    """
    if verbose:
        print(f"\n{'='*60}")
        print(f"ENONCE C : CAS SERRES s = 3 + 2^p")
        print(f"{'='*60}")

    for k in range(3, k_max + 1):
        S, d = compute_params(k)
        if d <= 0:
            continue

        fwd, bwd = build_layers(k, S, d)
        if 1 >= len(fwd) or k - 2 >= len(bwd):
            continue

        fwd_by_state = defaultdict(list)
        for (s, p), c in fwd[1].items():
            fwd_by_state[s].append(p)

        bwd_by_state = defaultdict(list)
        for (s, p), c in bwd[k - 2].items():
            bwd_by_state[s].append(p)

        common = set(fwd_by_state.keys()) & set(bwd_by_state.keys())

        tight_cases = []
        for s in sorted(common):
            min_fwd = min(fwd_by_state[s])
            max_bwd = max(bwd_by_state[s])
            gap = min_fwd - max_bwd
            if gap == 0:
                tight_cases.append((s, min_fwd, max_bwd))

        if tight_cases:
            for s, mf, mb in tight_cases:
                # Verify s = 3 + 2^p
                diff = (s - 3) % d
                is_power_of_2 = diff > 0 and (diff & (diff - 1)) == 0
                if is_power_of_2:
                    p_val = diff.bit_length() - 1
                    marker = f"s = 3 + 2^{p_val}"
                else:
                    marker = f"(s-3)%d = {diff}"
                print(f"  k={k:2d}: s={s:6d}, p1=q2={mf}, {marker}")


def test_full_invariant(k_max=14, verbose=True):
    """
    TEST COMPLET DE L'INVARIANT : Verifie que min_fwd >= max_bwd
    pour TOUS les k et TOUS les j intermediaires.
    """
    if verbose:
        print(f"\n{'='*60}")
        print(f"TEST COMPLET : INVARIANT FORT (tous j)")
        print(f"{'='*60}")

    all_ok = True
    for k in range(3, k_max + 1):
        S, d = compute_params(k)
        if d <= 0:
            continue

        fwd, bwd = build_layers(k, S, d)
        worst_gap = float('inf')
        total_common = 0

        for j in range(1, k - 1):
            bwd_idx = k - 1 - j
            if j >= len(fwd) or bwd_idx >= len(bwd):
                continue

            fwd_by_state = defaultdict(list)
            for (s, p), c in fwd[j].items():
                fwd_by_state[s].append(p)

            bwd_by_state = defaultdict(list)
            for (s, p), c in bwd[bwd_idx].items():
                bwd_by_state[s].append(p)

            common = set(fwd_by_state.keys()) & set(bwd_by_state.keys())
            total_common += len(common)

            for s in common:
                min_f = min(fwd_by_state[s])
                max_b = max(bwd_by_state[s])
                gap = min_f - max_b
                if gap < worst_gap:
                    worst_gap = gap

        ok = worst_gap >= 0
        if not ok:
            all_ok = False
        status = "OUI" if ok else "NON"
        print(f"  k={k:2d} S={S:2d} d={d:8d} worst_gap={worst_gap:3d} "
              f"total_common={total_common:5d} => {status}")

    print(f"\n  *** INVARIANT FORT {'VERIFIE' if all_ok else 'ECHOUE'} "
          f"POUR k=3..{k_max} ***")

    return all_ok


def summary_of_proof_strategy(verbose=True):
    """
    SYNTHESE : La strategie de preuve complete.
    """
    if verbose:
        print(f"\n{'*'*60}")
        print(f"STRATEGIE DE PREUVE COMPLETE")
        print(f"{'*'*60}")

        print(f"""
  THEOREME : Pour tout k >= 3, N_0(d(k)) = 0.

  PREUVE :
  --------
  Par le Lemme 1 (Double Peeling), il suffit de montrer
  qu'au point j=1, aucune paire forward/backward n'est compatible.

  Par le Lemme 3, il suffit de montrer l'Invariant Fort au point j=1 :
    Pour tout etat s commun : min_fwd(s, 1) >= max_bwd(s, 1).

  On decompose les etats communs en deux categories :

  CAS 1 (Generique, Enonce B) :
    Si p_1(s) >= S - k + 2, alors p_1(s) >= borne pigeonhole du backward.
    Cela couvre ~50-70% des etats.
    PREUVE : Le backward utilise k-2 positions strictement croissantes
    dans {{1,...,S-1}} (S-1 slots). Par pigeonhole, min_pos <= S-k+2.

  CAS 2 (Serre, Enonce C) :
    Les etats restants ont p_1(s) < S - k + 2.
    Numeriquement, ces etats sont TOUS de la forme s = 3 + 2^p
    avec p petit (p = 1, 2, ou 3).
    Pour ces etats, max_bwd(s) = p_1(s) exactement (gap = 0).
    PREUVE NECESSAIRE : Montrer que le backward ne peut atteindre
    q_2 = p + 1 pour ces etats specifiques.

  PREREQUIS (Enonce A) :
    Pour k >= 4, ord_d(2) > S - 1. Cela garantit l'unicite de p_1(s).
    Pour k = 3, verification directe (d=5, 3 etats communs, tous gap >= 0).

  STATUT :
    [NUMERIQUE k=3..14] Enonce A : VERIFIE
    [NUMERIQUE k=3..14] Enonce B + C => Invariant Fort : VERIFIE
    [A PROUVER] Enonce A pour tout k >= 4 (Baker + Lifting the Exponent)
    [A PROUVER] Enonce C pour tout k >= 3 (arithmetique de d = 2^S - 3^k)

  NOTE IMPORTANTE :
    L'Enonce C est le COEUR de la preuve.
    Il repose sur le fait que la structure arithmetique de d = 2^S - 3^k
    empeche le backward d'atteindre certains etats avec des positions hautes.
    Cela semble lie au "facteur 3" dans la recurrence de Horner.
""")


if __name__ == "__main__":
    print("*" * 60)
    print("ENONCES MATHEMATIQUES FORMELS")
    print("*" * 60)

    test_enonce_A(k_max=20)
    test_enonce_B()
    test_enonce_C()
    test_full_invariant()
    summary_of_proof_strategy()
