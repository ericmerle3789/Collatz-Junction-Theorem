#!/usr/bin/env python3
"""
R171 — Auto-vérification Collatz pour le Bloc 3
=================================================

Vérifie que TOUS les entiers de 1 à n_max (pire cas du Bloc 3)
atteignent 1 par itérations de Collatz.

Pour le Bloc 3 (k=22-41) : n_max ≈ 727,618,686 (k=41, S=65).

Optimisation : on ne vérifie que les IMPAIRS (les pairs convergent
trivialement si leur moitié converge). On utilise aussi un cache :
si on atteint un nombre déjà vérifié, on s'arrête.
"""

import time
import math
import sys


def verify_collatz_optimized(n_max):
    """
    Vérifie que tous les impairs de 1 à n_max atteignent 1.
    Utilise le fait que si on descend en-dessous de n, c'est déjà vérifié.
    """
    count = 0
    max_steps = 0

    for n in range(3, n_max + 1, 2):  # Impairs seulement
        x = n
        steps = 0
        while x >= n:  # Dès qu'on descend sous n, on sait que ça converge
            if x % 2 == 0:
                x //= 2
            else:
                x = 3 * x + 1
            steps += 1

            if steps > 100000:  # Safety
                print(f"ALERTE : {n} ne converge pas après 100000 étapes !")
                return False, n, count

        count += 1
        if steps > max_steps:
            max_steps = steps

        # Progress
        if count % 10_000_000 == 0:
            pct = 100 * n / n_max
            print(f"  {n:>12,} / {n_max:,} ({pct:.1f}%) — max_steps={max_steps}",
                  flush=True)

    return True, None, count


def compute_bloc3_nmin():
    """Calcule le pire n_min pour le Bloc 3."""
    worst_n = 0
    worst_k = 0
    for k in range(22, 42):
        S_min = math.ceil(k * math.log2(3))
        if 2**S_min <= 3**k:
            S_min += 1
        d = 2**S_min - 3**k
        corrsum_max = (3**k - 1) * 2**(S_min - k) // 2
        nmin = corrsum_max / d
        if nmin > worst_n:
            worst_n = nmin
            worst_k = k
    return math.ceil(worst_n), worst_k


def main():
    n_max, worst_k = compute_bloc3_nmin()

    print("=" * 72)
    print("R171 — AUTO-VÉRIFICATION COLLATZ POUR LE BLOC 3")
    print("=" * 72)
    print(f"\n  Pire cas Bloc 3 : k={worst_k}, n_min ≤ {n_max:,}")
    print(f"  Vérification de tous les impairs de 1 à {n_max:,}")
    print(f"  Nombre d'impairs à vérifier : ~{n_max // 2:,}")
    print()

    t0 = time.time()
    ok, bad_n, count = verify_collatz_optimized(n_max)
    elapsed = time.time() - t0

    print(f"\n{'='*72}")
    if ok:
        print(f"  ✓ VÉRIFIÉ : tous les {count:,} impairs de 1 à {n_max:,}")
        print(f"    atteignent 1 par itérations de Collatz.")
        print(f"    Temps : {elapsed:.1f}s")
        print(f"\n  ★★★ PREUVE AUTO-CONTENUE POUR LE BLOC 3 (k=22-41) ★★★")
        print(f"  Aucune dépendance externe (pas besoin de Barina 2021).")
    else:
        print(f"  ✗ ERREUR : {bad_n} ne converge pas !")
    print(f"{'='*72}")

    # Sauvegarder
    import json
    result = {
        "verified_up_to": n_max,
        "worst_k": worst_k,
        "all_converge": ok,
        "n_impairs_verified": count,
        "elapsed_s": round(elapsed, 1),
        "bloc3_proven": ok,
    }
    with open("R171_self_verify_bloc3.json", "w") as f:
        json.dump(result, f, indent=2)
    print(f"Résultat sauvegardé dans R171_self_verify_bloc3.json")


if __name__ == "__main__":
    main()
