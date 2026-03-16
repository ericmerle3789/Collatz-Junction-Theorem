#!/usr/bin/env python3
"""
R171 — MITM pour TOUS les S valides d'un k donne
==================================================

Pour un k-cycle de Collatz, S (nombre de divisions par 2) peut varier.
La condition est : 2^S > 3^k (pour que d = 2^S - 3^k > 0).

Pour prouver l'absence de k-cycles, on doit montrer N_0(d(k,S)) = 0
pour TOUS les S valides : S = S_min, S_min+1, ..., S_max.

S_max est borne par le fait que le plus petit element du cycle satisfait
n_min = corrSum / d >= 1, donc corrSum >= d.

corrSum_max = (3^k - 1) * 2^{S-k-1} (quand tous les B_j = S-k)
Condition : corrSum_max >= d = 2^S - 3^k
=> (3^k - 1) * 2^{S-k-1} >= 2^S - 3^k
=> (3^k - 1) / 2^{k+1} >= 1 - 3^k / 2^S
Pour S grand : LHS ~ (3/2)^k / 2, RHS ~ 1
Donc S_max est le plus grand S tel que (3^k - 1) * 2^{S-k-1} >= 2^S - 3^k

Reorganisons : (3^k - 1) * 2^{S-k-1} >= 2^S - 3^k
=> 3^k * 2^{S-k-1} - 2^{S-k-1} >= 2^S - 3^k
=> 3^k * 2^{S-k-1} + 3^k >= 2^S + 2^{S-k-1}
=> 3^k * (2^{S-k-1} + 1) >= 2^{S-k-1} * (2^{k+1} + 1)
C'est complique. Plus simple : calculer numeriquement.
"""

import time
import math
import json
import sys


def dp_forward_sums(coeff_list, d, top, min_start=0):
    """
    DP pour calculer toutes les sommes mod d possibles
    pour des compositions monotones.
    """
    n_terms = len(coeff_list)
    if n_terms == 0:
        return {0}

    pow2 = [pow(2, b, d) for b in range(top + 1)]

    exact_at_b = {}
    for b in range(min_start, top + 1):
        val = (coeff_list[0] * pow2[b]) % d
        if b not in exact_at_b:
            exact_at_b[b] = set()
        exact_at_b[b].add(val)

    for j in range(1, n_terms):
        cumul = set()
        new_exact_at_b = {}

        for b in range(min_start, top + 1):
            if b in exact_at_b:
                cumul |= exact_at_b[b]

            if cumul:
                addition = (coeff_list[j] * pow2[b]) % d
                new_set = set()
                for s in cumul:
                    new_set.add((s + addition) % d)
                new_exact_at_b[b] = new_set

        exact_at_b = new_exact_at_b

    result = set()
    for s_set in exact_at_b.values():
        result |= s_set
    return result


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


def mitm_prove(k, S, verbose=True):
    """
    MITM-DP pour un (k, S) specifique.
    """
    d = 2**S - 3**k
    if d <= 0:
        return {"k": k, "S": S, "d": d, "status": "INVALID (d<=0)"}

    top = S - k
    C = math.comb(S - 1, k - 1)

    # Verifier que corrSum_max >= d (sinon aucun cycle n'est possible)
    # corrSum_max = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{top} = 2^{top} * (3^k - 1) / 2
    corrsum_max = (pow(3, k) - 1) * pow(2, top) // 2
    if corrsum_max < d:
        if verbose:
            print(f"  S={S}: d={d:,}, corrSum_max={corrsum_max:,} < d => AUCUN CYCLE POSSIBLE (trivial)")
        return {
            "k": k, "S": S, "d": d, "top": top, "C": C,
            "N0_equals_zero": True,
            "reason": "corrSum_max < d",
            "elapsed_s": 0,
        }

    if verbose:
        print(f"\n  --- k={k}, S={S} ---")
        print(f"  d = {d:,} = {factor_trial(d)}")
        print(f"  top = {top}, C = {C:,}")
        print(f"  corrSum_max = {corrsum_max:,}, corrSum_max/d = {corrsum_max/d:.2f}")

    # Limiter la taille du set
    if d > 100_000_000_000:  # 100 milliards : trop pour un set Python
        if verbose:
            print(f"  d trop grand pour MITM direct. Essai CRT...")
        return mitm_crt(k, S, d, top, verbose)

    coeff = [pow(3, k - 1 - j, d) for j in range(k)]
    pow2 = [pow(2, b, d) for b in range(top + 1)]

    half = k // 2
    left_coeff = [coeff[j] for j in range(half)]
    right_coeff = [coeff[j] for j in range(half, k)]

    t_start = time.time()
    collision_found = False

    for m in range(top + 1):
        # LEFT
        left_sums = dp_forward_sums(left_coeff, d, m, min_start=0)

        # RIGHT with B_{k-1} = top fixed
        right_free_coeff = right_coeff[:-1]
        right_fixed_val = (coeff[k - 1] * pow2[top]) % d

        if len(right_free_coeff) > 0:
            right_free_sums = dp_forward_sums(right_free_coeff, d, top, min_start=m)
            right_sums = set()
            for s in right_free_sums:
                right_sums.add((s + right_fixed_val) % d)
        else:
            right_sums = {right_fixed_val}

        for r_val in right_sums:
            target = (d - r_val) % d
            if target in left_sums:
                collision_found = True
                break

        if collision_found:
            break

    elapsed = time.time() - t_start

    if verbose:
        status = "COLLISION!" if collision_found else "N_0 = 0 PROUVE"
        print(f"  => {status} (t={elapsed:.3f}s)")

    return {
        "k": k, "S": S, "d": d, "d_factored": str(factor_trial(d)),
        "top": top, "C": C,
        "N0_equals_zero": not collision_found,
        "elapsed_s": round(elapsed, 3),
    }


def mitm_crt(k, S, d, top, verbose=True):
    """
    Pour les grands d : utiliser CRT.
    Factoriser d = p1 * p2 * ... et verifier mod chaque facteur.
    Si AUCUN premier ne bloque, verifier les survivants par CRT.
    """
    factors = factor_trial(d)
    prime_factors = list(factors.keys())

    if verbose:
        print(f"  CRT avec facteurs : {factors}")

    # Pour chaque facteur premier, calculer le nombre de corrSum = 0 mod p
    survivors = None  # Will hold the surviving (left_sum, right_sum) pairs or count

    # Strategie simple : verifier mod chaque premier, compter les survivants
    survivor_fraction = 1.0
    blocking_prime = None

    for p in prime_factors:
        # Calculer toutes les corrSum mod p
        coeff_p = [pow(3, k - 1 - j, p) for j in range(k)]
        pow2_p = [pow(2, b, p) for b in range(top + 1)]

        # DP complete pour mod p (p est petit ou modere)
        if p > 10_000_000_000:
            if verbose:
                print(f"    p={p} trop grand, skip")
            continue

        all_sums = dp_all_sums_mod_p(k, S, p, top)
        n_zero = all_sums.get(0, 0)
        total = sum(all_sums.values())
        frac = n_zero / total if total > 0 else 0

        if verbose:
            print(f"    p={p}: {n_zero}/{total} compositions avec corrSum=0 mod p "
                  f"({frac*100:.2f}%)")

        survivor_fraction *= frac

        if n_zero == 0:
            blocking_prime = p
            break

    C = math.comb(S - 1, k - 1)
    expected_survivors = C * survivor_fraction

    if blocking_prime is not None:
        if verbose:
            print(f"  => PREMIER BLOQUANT p={blocking_prime} : N_0(d) = 0 PROUVE")
        return {
            "k": k, "S": S, "d": d, "d_factored": str(factors),
            "top": top, "C": C,
            "N0_equals_zero": True,
            "reason": f"blocking prime p={blocking_prime}",
            "elapsed_s": 0,
        }

    if verbose:
        print(f"  Survivants attendus (CRT) : {expected_survivors:.2f}")
        if expected_survivors < 1:
            print(f"  Heuristiquement < 1, mais PAS une preuve.")

    return {
        "k": k, "S": S, "d": d, "d_factored": str(factors),
        "top": top, "C": C,
        "N0_equals_zero": None,  # Cannot prove
        "reason": "CRT incomplete",
        "expected_survivors": round(expected_survivors, 4),
        "elapsed_s": 0,
    }


def dp_all_sums_mod_p(k, S, p, top):
    """
    DP complete : calcule le nombre de compositions donnant chaque
    residue mod p. Retourne un Counter.
    """
    from collections import Counter

    coeff = [pow(3, k - 1 - j, p) for j in range(k)]
    pow2 = [pow(2, b, p) for b in range(top + 1)]

    # DP : count[last_b][residue] = nombre de compositions
    # Pour chaque etape j, pour chaque last_b et residue
    # Optimisation : utiliser des arrays

    # Etape 0 : placer B_0 = b pour b = 0..top
    # count_at_b[b] = Counter des residus
    count_at_b = {}
    for b in range(top + 1):
        val = (coeff[0] * pow2[b]) % p
        count_at_b[b] = Counter({val: 1})

    # B_{k-1} n'est PAS fixe a top dans cette version (on compte TOUTES les compositions)
    # Attends, dans le Junction Theorem, B_{k-1} = S - k = top. C'est fixe.
    # Donc le dernier terme est toujours coeff[k-1] * 2^{top}.

    # Reformulons : on a k-1 termes libres (j=0..k-2) avec B_0 <= ... <= B_{k-2} <= top
    # Plus un terme fixe : coeff[k-1] * 2^{top}

    fixed_term = (coeff[k - 1] * pow2[top]) % p

    # DP sur les k-1 premiers termes
    # Re-init pour j=0
    count_at_b = {}
    for b in range(top + 1):
        val = (coeff[0] * pow2[b]) % p
        if b not in count_at_b:
            count_at_b[b] = Counter()
        count_at_b[b][val] += 1

    for j in range(1, k - 1):  # j=1..k-2
        # Construire le cumul
        cumul = Counter()
        new_count_at_b = {}

        for b in range(top + 1):
            if b in count_at_b:
                cumul += count_at_b[b]

            if cumul:
                addition = (coeff[j] * pow2[b]) % p
                new_counter = Counter()
                for res, cnt in cumul.items():
                    new_res = (res + addition) % p
                    new_counter[new_res] += cnt
                new_count_at_b[b] = new_counter

        count_at_b = new_count_at_b

    # Fusionner tous les B finaux et ajouter le terme fixe
    total = Counter()
    for b_counter in count_at_b.values():
        total += b_counter

    # Ajouter le terme fixe
    final = Counter()
    for res, cnt in total.items():
        new_res = (res + fixed_term) % p
        final[new_res] += cnt

    return final


def compute_S_range(k):
    """
    Calcule la plage de S valides pour un k-cycle.
    S_min : plus petit S tel que 2^S > 3^k
    S_max : plus grand S tel que corrSum_max >= d (au moins 1 cycle possible)
    """
    # S_min
    S_min = math.ceil(k * math.log2(3))
    if 2**S_min <= 3**k:
        S_min += 1

    # S_max : corrSum_max = (3^k - 1) * 2^{S-k} // 2 >= d = 2^S - 3^k
    # (3^k - 1) * 2^{S-k-1} >= 2^S - 3^k
    S_max = S_min
    for S in range(S_min, 3 * k + 1):  # Borne large
        d = 2**S - 3**k
        corrsum_max = (pow(3, k) - 1) * pow(2, S - k) // 2
        if corrsum_max >= d:
            S_max = S
        else:
            break

    return S_min, S_max


def prove_k_complete(k, verbose=True):
    """
    Prouve N_0(d(k,S)) = 0 pour TOUS les S valides.
    """
    S_min, S_max = compute_S_range(k)

    if verbose:
        print(f"\n{'='*72}")
        print(f"PREUVE COMPLETE pour k={k}")
        print(f"  S range : [{S_min}, {S_max}]")
        print(f"  {S_max - S_min + 1} valeurs de S a verifier")
        print(f"{'='*72}")

    all_results = {}
    all_proven = True

    for S in range(S_min, S_max + 1):
        res = mitm_prove(k, S, verbose=verbose)
        all_results[f"S={S}"] = res

        if res.get("N0_equals_zero") is True:
            continue
        elif res.get("N0_equals_zero") is False:
            if verbose:
                print(f"\n  !!! COLLISION TROUVEE pour k={k}, S={S} !!!")
            all_proven = False
            break
        else:
            # Indeterminate (CRT incomplete)
            if verbose:
                print(f"\n  ??? INDETERMINE pour k={k}, S={S} ???")
            all_proven = False

    if verbose:
        print(f"\n{'='*72}")
        if all_proven:
            print(f"*** k={k} COMPLETEMENT PROUVE : N_0 = 0 pour TOUS S dans [{S_min}, {S_max}] ***")
        else:
            print(f"k={k} : preuve INCOMPLETE")
        print(f"{'='*72}")

    return {
        "k": k,
        "S_range": [S_min, S_max],
        "all_proven": all_proven,
        "details": all_results,
    }


def main():
    print("=" * 72)
    print("R171 — CAMPAGNE MITM COMPLETE : TOUS LES S POUR CHAQUE k")
    print("=" * 72)

    all_results = {}

    # Validation k=3..10
    print("\n--- VALIDATION k=3..10 ---")
    for k in range(3, 11):
        S_min, S_max = compute_S_range(k)
        res = prove_k_complete(k, verbose=False)
        status = "PROUVE" if res["all_proven"] else "ECHEC"
        print(f"  k={k:>2d} : S=[{S_min},{S_max}], {status}")
        all_results[f"k={k}_val"] = res

    # k=22 : le test principal
    print("\n" + "=" * 72)
    print("*** TEST PRINCIPAL : k=22 ***")
    print("=" * 72)

    res22 = prove_k_complete(22, verbose=True)
    all_results["k=22"] = res22

    # Si k=22 reussit, continuer avec k=23, 24, ...
    if res22["all_proven"]:
        for k_ext in range(23, 42):
            print(f"\n{'='*72}")
            print(f"*** k={k_ext} ***")
            print(f"{'='*72}")

            S_min, S_max = compute_S_range(k_ext)
            print(f"  S range : [{S_min}, {S_max}]")

            # Estimation rapide
            d_min = 2**S_min - 3**k_ext
            if d_min > 100_000_000_000:
                print(f"  d_min = {d_min:,} > 100B : au-dela du MITM direct")
                print(f"  Tentative CRT...")

            res_ext = prove_k_complete(k_ext, verbose=True)
            all_results[f"k={k_ext}"] = res_ext

            if not res_ext["all_proven"]:
                print(f"  k={k_ext} : preuve INCOMPLETE")
                # Continue quand meme pour les autres k

    # Sauvegarder
    with open("R171_MITM_allS_results.json", "w") as f:
        json.dump(all_results, f, indent=2, default=str)
    print(f"\nResultats sauvegardes dans R171_MITM_allS_results.json")

    # Resume final
    print("\n" + "=" * 72)
    print("RESUME FINAL")
    print("=" * 72)
    for key, val in sorted(all_results.items()):
        if isinstance(val, dict) and "all_proven" in val:
            status = "PROUVE" if val["all_proven"] else "INCOMPLET"
            S_range = val.get("S_range", "?")
            print(f"  {key:>12s} : S={S_range}, {status}")

    proven_k = [k for k, v in all_results.items() if isinstance(v, dict) and v.get("all_proven")]
    print(f"\n  k completement prouves : {proven_k}")

    return all_results


if __name__ == "__main__":
    main()
