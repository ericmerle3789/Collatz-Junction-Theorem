#!/usr/bin/env python3
"""
R171 — MITM OPTIMISE pour prouver N_0(d(k)) = 0
=================================================

Version optimisee : utilise la programmation dynamique au lieu de
l'enumeration explicite des compositions. Pour chaque cote (L/R),
on construit l'ENSEMBLE des sommes partielles possibles mod d
incrementalement via DP.

Complexite memoire : O(d) par bitset (pour stocker les sommes possibles)
Complexite temps : O(k * top * |S_prev|) ou |S_prev| est la taille du set

Pour k=22, d ~ 3*10^9. Un set Python de ~1M entiers = ~40 MB. Faisable.
"""

import time
import math
import json


def compute_params(k):
    """Calcule S, d, top pour un k donne."""
    S = math.ceil(k * math.log2(3)) + 1
    while 2**S <= 3**k:
        S += 1
    d = 2**S - 3**k
    top = S - k
    return S, d, top


def factor_trial(n):
    """Factorisation par division trial."""
    factors = {}
    d_val = 2
    while d_val * d_val <= abs(n):
        while n % d_val == 0:
            factors[d_val] = factors.get(d_val, 0) + 1
            n //= d_val
        d_val += 1
    if abs(n) > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


def dp_forward_sums(coeff_list, d, top, min_start=0):
    """
    Calcule l'ensemble de toutes les sommes partielles possibles mod d
    pour des compositions monotones.

    coeff_list[j] = coefficient du j-eme terme (deja reduit mod d)
    Pour le j-eme terme, la valeur est coeff_list[j] * 2^{B_j} mod d
    avec B_j >= B_{j-1} (monotone) et B_j in [min_start, top].

    Retourne un set de toutes les sommes possibles.

    DP : states[b] = ensemble des sommes partielles quand le dernier B = b
    """
    n_terms = len(coeff_list)
    if n_terms == 0:
        return {0}

    # Precalculer 2^b mod d
    pow2 = [pow(2, b, d) for b in range(top + 1)]

    # Initialisation : premier terme, B_0 peut aller de min_start a top
    # states[b] = set des sommes quand B_0 = b
    states = {}
    for b in range(min_start, top + 1):
        val = (coeff_list[0] * pow2[b]) % d
        if b not in states:
            states[b] = set()
        states[b].add(val)

    # Pour chaque terme suivant
    for j in range(1, n_terms):
        new_states = {}

        # Cumuler : pour B_j = b, on peut venir de tout B_{j-1} <= b
        # Optimisation : construire le set cumule incrementalement
        cumul_set = set()

        for b in range(min_start, top + 1):
            # Ajouter les etats du B_{j-1} = b au cumul
            if b in states:
                cumul_set = cumul_set | states[b]

            # Pour B_j = b : ajouter coeff_list[j] * 2^b a chaque somme du cumul
            addition = (coeff_list[j] * pow2[b]) % d
            new_set = set()
            for s in cumul_set:
                new_set.add((s + addition) % d)

            if new_set:
                new_states[b] = new_set

        states = new_states

    # Fusionner tous les etats finaux
    result = set()
    for b, s_set in states.items():
        result |= s_set

    return result


def dp_forward_sums_optimized(coeff_list, d, top, min_start=0):
    """
    Version encore plus optimisee : au lieu de stocker par b,
    on stocke un seul set et on le fait evoluer.

    Approche : set_at_or_before[b] = union de tous les states[0..b]
    On construit incrementalement.

    En fait, pour le DP, a chaque etape j on a besoin de :
      pour chaque b : {sommes possibles quand on a pose j termes et le dernier = b}

    Simplification : on n'a PAS besoin de distinguer par b si on stocke
    les paires (sum_so_far, last_b). Mais ca peut etre gros.

    Alternative : stockage compact.
    Pour chaque etape j :
      cumulative_sums_up_to_b = union des sums pour last_b <= b
      Pour b : new_sums_with_last_b = {s + coeff[j]*2^b mod d : s in cumulative_up_to_b}

    Puis cumulative pour l'etape suivante est reconstruit.

    La taille du set est bornee par min(C(compositions vues), d).
    Pour k=22 : C ~ 928M, d ~ 3*10^9. Mais en pratique le set peut etre << d.
    """
    n_terms = len(coeff_list)
    if n_terms == 0:
        return {0}

    pow2 = [pow(2, b, d) for b in range(top + 1)]

    # states_le_b[b] = cumulative set of sums with last_B <= b after j terms
    # We only need the current and build the next step

    # Init: j=0
    # After placing first term with B_0 = b:
    # sums_with_last_exactly_b = {coeff[0] * 2^b}
    # cumul_le_b = union of sums_exactly for all b' <= b

    # We store: for each b, the set of NEW sums (exactly at b, not cumulated)
    exact_at_b = {}
    for b in range(min_start, top + 1):
        val = (coeff_list[0] * pow2[b]) % d
        exact_at_b[b] = {val}

    for j in range(1, n_terms):
        # Build cumulative set incrementally
        cumul = set()
        new_exact_at_b = {}

        for b in range(min_start, top + 1):
            # Add sums ending at b from previous step to cumulative
            if b in exact_at_b:
                cumul |= exact_at_b[b]

            # New sums at step j with B_j = b
            if cumul:
                addition = (coeff_list[j] * pow2[b]) % d
                new_set = set()
                for s in cumul:
                    new_set.add((s + addition) % d)
                new_exact_at_b[b] = new_set

        exact_at_b = new_exact_at_b

    # Final: collect all sums
    result = set()
    for s_set in exact_at_b.values():
        result |= s_set
    return result


def mitm_dp_prove(k, verbose=True):
    """
    MITM avec DP pour prouver N_0(d(k)) = 0.

    Split : left = j=0..half, right = j=half+1..k-1
    Le lien est B_{half} <= B_{half+1}.

    Pour chaque valeur frontiere m (B_{half} <= m, B_{half+1} >= m) :
      Left : sommes pour j=0..half avec tous B dans [0, m]
      Right : sommes pour j=half+1..k-1 avec B_{k-1}=top et tous B dans [m, top]

    On verifie si (d - right_sum) mod d est dans left_sums.

    Optimisation : au lieu de recalculer pour chaque m, on peut etre
    plus malin. Mais pour commencer, on fait simplement.
    """
    S, d, top = compute_params(k)

    if verbose:
        print(f"\n{'='*60}")
        print(f"MITM-DP pour k={k}")
        print(f"  S={S}, d={d:,}, top={top}")
        print(f"  d = {factor_trial(d)}")
        print(f"  C = {math.comb(S-1, k-1):,}")
        print(f"{'='*60}")

    # Coefficients
    coeff = [pow(3, k - 1 - j, d) for j in range(k)]
    pow2 = [pow(2, b, d) for b in range(top + 1)]

    # Split
    half = k // 2
    left_indices = list(range(half))         # j = 0..half-1
    right_indices = list(range(half, k))     # j = half..k-1

    left_coeff = [coeff[j] for j in left_indices]
    right_coeff = [coeff[j] for j in right_indices]

    if verbose:
        print(f"  Left: j={left_indices[0]}..{left_indices[-1]} ({len(left_indices)} terms)")
        print(f"  Right: j={right_indices[0]}..{right_indices[-1]} ({len(right_indices)} terms)")
        print(f"  Boundary: B_{left_indices[-1]} <= B_{right_indices[0]}")

    t_start = time.time()

    # Strategie : pour chaque frontiere m
    # Left: B values in [0, m], all <= m
    # Right: B values in [m, top], B_{k-1} = top
    # Right has len(right_indices) terms, last one fixed = top

    collision_found = False
    collision_detail = None

    for m in range(top + 1):
        t_m = time.time()

        # LEFT: terms j=0..half-1, B values in [0, m]
        left_sums = dp_forward_sums_optimized(left_coeff, d, m, min_start=0)

        # RIGHT: terms j=half..k-1, B values in [m, top], last B = top
        # We need to handle the constraint B_{k-1} = top
        # Split right into: j=half..k-2 (free, in [m, top]) + j=k-1 (fixed = top)
        right_free_coeff = right_coeff[:-1]  # j=half..k-2
        right_fixed_val = (coeff[k-1] * pow2[top]) % d  # j=k-1, B=top

        if len(right_free_coeff) > 0:
            # Compute sums of free right terms with B in [m, top]
            right_free_sums = dp_forward_sums_optimized(right_free_coeff, d, top, min_start=m)
            # Add fixed term
            right_sums = set()
            for s in right_free_sums:
                right_sums.add((s + right_fixed_val) % d)
        else:
            # Only the fixed term
            right_sums = {right_fixed_val}

        # Check collision : L + R = 0 mod d  =>  L = (-R) mod d = (d - R) mod d
        for r_val in right_sums:
            target = (d - r_val) % d
            if target in left_sums:
                collision_found = True
                collision_detail = {"m": m, "left": target, "right": r_val}
                break

        elapsed_m = time.time() - t_m

        if verbose:
            print(f"  m={m:>3d}/{top} : |L|={len(left_sums):>10,}, |R|={len(right_sums):>10,}, "
                  f"t={elapsed_m:.2f}s, collision={'*** OUI ***' if collision_found else 'non'}")

        if collision_found:
            break

    elapsed_total = time.time() - t_start

    result = {
        "k": k,
        "S": S,
        "d": d,
        "d_factored": str(factor_trial(d)),
        "top": top,
        "C_total": math.comb(S - 1, k - 1),
        "elapsed_s": round(elapsed_total, 3),
        "collision_found": collision_found,
        "collision_detail": collision_detail,
        "N0_equals_zero": not collision_found,
    }

    if verbose:
        print(f"\n  RESULTAT k={k} :")
        print(f"  Temps : {elapsed_total:.3f}s")
        if collision_found:
            print(f"  *** COLLISION *** : {collision_detail}")
        else:
            print(f"  *** N_0(d({k})) = 0 PROUVE ***")

    return result


def run_campaign():
    """Campagne complete."""
    print("=" * 72)
    print("R171 — CAMPAGNE MITM-DP")
    print("Objectif : Prouver N_0(d(k)) = 0 pour k=22+")
    print("=" * 72)

    results = {}

    # Validation sur petits k
    print("\n--- VALIDATION k=3..10 ---")
    for k in range(3, 11):
        res = mitm_dp_prove(k, verbose=False)
        S, d, top = compute_params(k)
        status = "N0=0 OK" if res["N0_equals_zero"] else "COLLISION!"
        print(f"  k={k:>2d} : d={d:>12,}, C={math.comb(S-1,k-1):>10,}, "
              f"t={res['elapsed_s']:.3f}s -> {status}")
        results[f"k={k}_validation"] = res
        if not res["N0_equals_zero"]:
            print(f"  !!! ERREUR : k={k} devrait donner N0=0 !!!")
            return results

    print("\n  Validation OK pour k=3..10")

    # Test principal : k=22
    print("\n" + "=" * 72)
    print("*** k=22 : LE TEST ***")
    print("=" * 72)
    res22 = mitm_dp_prove(22, verbose=True)
    results["k=22"] = res22

    if res22["N0_equals_zero"]:
        print(f"\n{'*'*72}")
        print(f"*** k=22 FERME : N_0(d(22)) = 0 PROUVE ***")
        print(f"{'*'*72}")

        # Etendre
        for k_ext in range(23, 42):
            S_ext, d_ext, top_ext = compute_params(k_ext)
            C_ext = math.comb(S_ext - 1, k_ext - 1)
            print(f"\n--- k={k_ext} : S={S_ext}, d={d_ext:,}, C={C_ext:,} ---")

            # Estimation memoire : le set peut grandir jusqu'a min(C, d)
            # Pour des grands k, le set va saturer a d, ce qui peut etre trop gros
            if d_ext > 5_000_000_000:
                print(f"  d={d_ext:,} trop grand pour un set Python. SKIP.")
                results[f"k={k_ext}"] = {"status": "SKIPPED", "reason": "d too large for set"}
                continue

            try:
                res_ext = mitm_dp_prove(k_ext, verbose=True)
                results[f"k={k_ext}"] = res_ext
                if not res_ext["N0_equals_zero"]:
                    print(f"  !!! COLLISION pour k={k_ext} !!!")
                    break
            except MemoryError:
                print(f"  MEMOIRE INSUFFISANTE pour k={k_ext}")
                results[f"k={k_ext}"] = {"status": "OOM"}
                break

    # Sauvegarder
    with open("R171_MITM_results.json", "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nResultats sauvegardes dans R171_MITM_results.json")

    # Resume
    print("\n" + "=" * 72)
    print("RESUME")
    print("=" * 72)
    for key, val in results.items():
        if isinstance(val, dict) and "N0_equals_zero" in val:
            status = "N0=0 PROUVE" if val["N0_equals_zero"] else "COLLISION"
            print(f"  {key} : {status} (t={val.get('elapsed_s', '?')}s)")

    return results


if __name__ == "__main__":
    run_campaign()
