#!/usr/bin/env python3
"""
R171 — MITM rapide pour k=22, tous les S valides
=================================================

FAIT CLES :
- Pour k=22, S_min = 35 (2^35 > 3^22)
- Pour S > S_max, corrSum_max < d => aucun cycle (trivial)
- On doit verifier CHAQUE S de S_min a S_max

Optimisation : utiliser le MITM avec sets (pas DP complet)
L'approche DP precedente stocke TOUTES les sommes intermediaires.
L'approche MITM ne stocke que les sommes finales d'une MOITIE.
"""

import time
import math
import json
import sys


def compute_S_range(k):
    """Plage de S valides."""
    S_min = math.ceil(k * math.log2(3))
    if 2**S_min <= 3**k:
        S_min += 1
    S_max = S_min
    for S in range(S_min, 3 * k + 1):
        d = 2**S - 3**k
        corrsum_max = (pow(3, k) - 1) * pow(2, S - k) // 2
        if corrsum_max >= d:
            S_max = S
        else:
            break
    return S_min, S_max


def gen_monotone(length, max_val, min_val=0):
    """Genere les sequences monotones de 'length' elements dans [min_val, max_val]."""
    if length == 0:
        yield ()
        return
    if length == 1:
        for v in range(min_val, max_val + 1):
            yield (v,)
        return
    for v in range(min_val, max_val + 1):
        for rest in gen_monotone(length - 1, max_val, v):
            yield (v,) + rest


def mitm_check(k, S):
    """
    MITM pour un (k, S) specifique.
    Retourne True si N_0 = 0 (pas de collision).
    """
    d = 2**S - 3**k
    if d <= 0:
        return True, {"reason": "d <= 0", "d": d}

    top = S - k
    corrsum_max = (pow(3, k) - 1) * pow(2, top) // 2
    if corrsum_max < d:
        return True, {"reason": "corrSum_max < d (trivial)", "d": d}

    # Precalcul
    coeff = [pow(3, k - 1 - j, d) for j in range(k)]
    pow2 = [pow(2, b, d) for b in range(top + 1)]

    # Split en deux moities
    # Left: j=0..half-1, Right: j=half..k-1 (avec B_{k-1}=top fixe)
    half = k // 2  # 11 pour k=22

    t0 = time.time()

    # Pour chaque frontiere m = valeur max du cote gauche / min du cote droit
    for m in range(top + 1):
        # GAUCHE : B_0 <= ... <= B_{half-1} <= m
        # Calculer toutes les sommes gauches
        left_sums = set()
        for seq in gen_monotone(half, m):
            s = 0
            for j, b in enumerate(seq):
                s = (s + coeff[j] * pow2[b]) % d
            left_sums.add(s)

        # DROITE : m <= B_{half} <= ... <= B_{k-2} <= top, B_{k-1} = top
        # k-1-half termes libres + 1 fixe
        right_free = k - 1 - half  # nombre de termes libres a droite
        fixed_val = (coeff[k - 1] * pow2[top]) % d

        for seq in gen_monotone(right_free, top, m):
            s = fixed_val
            for j_offset, b in enumerate(seq):
                j_actual = half + j_offset
                s = (s + coeff[j_actual] * pow2[b]) % d

            target = (d - s) % d
            if target in left_sums:
                elapsed = time.time() - t0
                return False, {
                    "reason": "COLLISION",
                    "d": d,
                    "m": m,
                    "left": target,
                    "right": s,
                    "elapsed_s": round(elapsed, 3),
                }

    elapsed = time.time() - t0
    return True, {"reason": "N0=0 (exhaustif)", "d": d, "elapsed_s": round(elapsed, 3)}


def main():
    k = 22
    S_min, S_max = compute_S_range(k)

    print(f"k={k} : S range = [{S_min}, {S_max}]", flush=True)
    print(f"Nombre de S a verifier : {S_max - S_min + 1}", flush=True)

    results = {}
    all_proven = True

    for S in range(S_min, S_max + 1):
        d = 2**S - 3**k
        top = S - k
        C = math.comb(S - 1, k - 1)
        corrsum_max = (pow(3, k) - 1) * pow(2, top) // 2

        print(f"\n  S={S} : d={d:,}, top={top}, C={C:,}, corrSum_max/d={corrsum_max/d:.2f}", flush=True)

        proven, detail = mitm_check(k, S)
        results[S] = {"proven": proven, **detail}

        if proven:
            print(f"    => N_0 = 0 ({detail['reason']}) "
                  f"[t={detail.get('elapsed_s', 0):.3f}s]", flush=True)
        else:
            print(f"    => !!! COLLISION !!! {detail}", flush=True)
            all_proven = False
            break

    print(f"\n{'='*60}", flush=True)
    if all_proven:
        print(f"*** k={k} : N_0(d) = 0 PROUVE POUR TOUS S dans [{S_min}, {S_max}] ***", flush=True)
        print(f"*** AUCUN {k}-CYCLE DE COLLATZ N'EXISTE ***", flush=True)
    else:
        print(f"k={k} : COLLISION TROUVEE", flush=True)
    print(f"{'='*60}", flush=True)

    # Sauvegarder
    with open("R171_k22_allS.json", "w") as f:
        json.dump({"k": k, "S_range": [S_min, S_max],
                    "all_proven": all_proven, "results": results},
                  f, indent=2, default=str)

    return all_proven


if __name__ == "__main__":
    main()
