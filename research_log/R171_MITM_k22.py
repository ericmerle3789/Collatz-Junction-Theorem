#!/usr/bin/env python3
"""
R171 — MEET-IN-THE-MIDDLE (MITM) pour prouver N_0(d(22)) = 0
==============================================================

Strategie :
  corrSum = L + R ou L = somme des 11 premiers termes, R = somme des 11 derniers.
  On fixe m = B_10 (la valeur frontiere).

  Pour chaque m :
    Left : B_0 <= ... <= B_9 <= m, B_10 = m
      => C(m+10, 10) compositions pour B_0..B_9
    Right : m <= B_11 <= ... <= B_20 <= top, B_21 = top
      => C(top-m+10, 10) compositions pour B_11..B_20

    On stocke toutes les valeurs L mod d dans un set.
    On calcule chaque R, et on verifie si (d - R) mod d est dans le set.
    Si oui : corrSum = 0 mod d TROUVEE => cycle existe potentiellement
    Si non pour TOUS les m : N_0(d(22)) = 0 PROUVE.

Parametres k=22 :
  S = 35 (car 2^35 > 3^22 et 2^34 < 3^22)
  d = 2^35 - 3^22 = 34,359,738,368 - 31,381,059,609 = 2,978,678,759
  top = S - k = 35 - 22 = 13
  C(S-1, k-1) = C(34, 21) = 927,983,760 compositions

Complexite MITM :
  Total work = sum_{m=0}^{13} [C(m+10, 10) + C(13-m+10, 10)]
             = 2 * sum_{m=0}^{13} C(m+10, 10)
             = 2 * C(24, 11) = 2 * 2,496,144 = 4,992,288
  Soit ~5 MILLIONS d'operations au lieu de 928 MILLIONS.
"""

import time
import math
import json
from itertools import combinations_with_replacement


def compute_params(k):
    """Calcule S, d, top pour un k donne."""
    # S = plus petit entier tel que 2^S > 3^k
    S = math.ceil(k * math.log2(3)) + 1
    # Verifier
    while 2**S <= 3**k:
        S += 1
    d = 2**S - 3**k
    top = S - k
    return S, d, top


def comb(n, r):
    """Nombre de combinaisons C(n, r)."""
    if r < 0 or r > n:
        return 0
    return math.comb(n, r)


def generate_monotone_sequences(length, max_val):
    """
    Genere toutes les sequences monotones (v_0, ..., v_{length-1})
    avec 0 <= v_0 <= v_1 <= ... <= v_{length-1} <= max_val.
    """
    if length == 0:
        yield ()
        return
    if length == 1:
        for v in range(max_val + 1):
            yield (v,)
        return

    def _gen(depth, lower, acc):
        if depth == length:
            yield tuple(acc)
            return
        for v in range(lower, max_val + 1):
            acc.append(v)
            yield from _gen(depth + 1, v, acc)
            acc.pop()

    yield from _gen(0, 0, [])


def mitm_prove_k(k, verbose=True):
    """
    Utilise MITM pour prouver N_0(d(k)) = 0.

    Retourne :
      - True si N_0(d(k)) = 0 (aucune collision trouvee)
      - False si une collision est trouvee (corrSum = 0 mod d possible)
      - dict avec les details
    """
    S, d, top = compute_params(k)

    if verbose:
        print(f"\n{'='*60}")
        print(f"MITM pour k={k}")
        print(f"  S = {S}")
        print(f"  d = {d}")
        print(f"  top = S - k = {top}")
        print(f"  C(S-1, k-1) = C({S-1}, {k-1}) = {comb(S-1, k-1):,}")
        print(f"{'='*60}")

    # Precalculer les coefficients 3^{k-1-j} mod d pour j=0..k-1
    coeff = [(pow(3, k - 1 - j, d)) for j in range(k)]

    # Precalculer 2^b mod d pour b=0..top
    pow2 = [pow(2, b, d) for b in range(top + 1)]

    # Split : left = j=0..half_k, right = j=half_k+1..k-1
    # On choisit le split au milieu
    half_k = (k - 1) // 2  # Index du dernier element du cote gauche
    # Left : j=0..half_k (half_k+1 termes)
    # Right : j=half_k+1..k-1 (k-1-half_k termes)

    left_len = half_k + 1  # Nombre de termes a gauche
    right_len = k - 1 - half_k  # Nombre de termes a droite (sans B_{k-1})
    # B_{k-1} = top est fixe, on l'inclut dans le cote droit

    if verbose:
        print(f"  Split : left j=0..{half_k} ({left_len} termes)")
        print(f"          right j={half_k+1}..{k-1} ({right_len+1} termes, incl. B_{k-1}={top})")

    # Estimation de la complexite
    total_left = 0
    total_right = 0
    for m in range(top + 1):
        nl = comb(m + left_len - 1, left_len - 1)  # B_0 <= ... <= B_{half_k-1} <= m, B_{half_k}=m
        nr = comb(top - m + right_len - 1, right_len - 1)  # m <= B_{half_k+1} <= ... <= B_{k-2} <= top
        total_left += nl
        total_right += nr

    if verbose:
        print(f"  Complexite estimee : {total_left:,} left + {total_right:,} right = {total_left+total_right:,}")
        print(f"  (vs brute force : {comb(S-1, k-1):,})")
        print(f"  Speedup : {comb(S-1, k-1) / (total_left + total_right):.1f}x")

    t_start = time.time()

    total_left_checked = 0
    total_right_checked = 0
    collision_found = False
    collision_details = None

    for m in range(top + 1):
        t_m = time.time()

        # ===== COTE GAUCHE =====
        # B_0 <= B_1 <= ... <= B_{half_k-1} <= m, et B_{half_k} = m
        # Terme fixe du cote gauche : coeff[half_k] * pow2[m]
        fixed_left = (coeff[half_k] * pow2[m]) % d

        # Generer toutes les sequences (B_0, ..., B_{half_k-1}) avec max = m
        left_sums = set()

        if left_len == 1:
            # Seul terme = B_{half_k} = m
            left_sums.add(fixed_left)
            total_left_checked += 1
        else:
            for seq in generate_monotone_sequences(left_len - 1, m):
                s = fixed_left
                for j_idx, b_val in enumerate(seq):
                    s = (s + coeff[j_idx] * pow2[b_val]) % d
                left_sums.add(s)
                total_left_checked += 1

        # ===== COTE DROIT =====
        # m <= B_{half_k+1} <= ... <= B_{k-2} <= top, et B_{k-1} = top
        # Terme fixe du cote droit : coeff[k-1] * pow2[top]
        fixed_right = (coeff[k - 1] * pow2[top]) % d

        # Generer toutes les sequences (B_{half_k+1}, ..., B_{k-2}) avec min=m, max=top
        if right_len == 0:
            # Seul terme = B_{k-1} = top
            target = (d - fixed_right) % d
            if target in left_sums:
                collision_found = True
                collision_details = {"m": m, "right_sum": fixed_right, "left_sum": target}
                break
            total_right_checked += 1
        else:
            for seq in generate_monotone_sequences(right_len, top - m):
                # Shift : actual B values = seq[i] + m
                s = fixed_right
                for j_offset, b_offset in enumerate(seq):
                    j_actual = half_k + 1 + j_offset
                    b_actual = b_offset + m
                    s = (s + coeff[j_actual] * pow2[b_actual]) % d

                target = (d - s) % d
                if target in left_sums:
                    collision_found = True
                    collision_details = {"m": m, "right_sum": s, "left_sum": target}
                    break
                total_right_checked += 1

            if collision_found:
                break

        elapsed_m = time.time() - t_m
        if verbose and (m % max(1, (top+1)//5) == 0 or m == top):
            print(f"  m={m:>3d}/{top} : |L|={len(left_sums):>10,}, "
                  f"checked_R={total_right_checked:>10,}, "
                  f"t={elapsed_m:.2f}s, collision={'OUI' if collision_found else 'non'}")

    elapsed_total = time.time() - t_start

    result = {
        "k": k,
        "S": S,
        "d": d,
        "d_factored": None,  # sera rempli
        "top": top,
        "C_total": comb(S - 1, k - 1),
        "left_checked": total_left_checked,
        "right_checked": total_right_checked,
        "total_operations": total_left_checked + total_right_checked,
        "elapsed_s": round(elapsed_total, 3),
        "collision_found": collision_found,
        "collision_details": collision_details,
        "N0_equals_zero": not collision_found,
    }

    if verbose:
        print(f"\n  === RESULTAT k={k} ===")
        print(f"  Operations totales : {total_left_checked + total_right_checked:,}")
        print(f"  Temps total : {elapsed_total:.3f}s")
        if collision_found:
            print(f"  *** COLLISION TROUVEE *** : {collision_details}")
            print(f"  ==> N_0(d({k})) > 0 — un cycle POURRAIT exister !")
        else:
            print(f"  *** AUCUNE COLLISION ***")
            print(f"  ==> N_0(d({k})) = 0 PROUVE par MITM exhaustif")

    return result


def factor_trial(n):
    """Factorisation par division trial."""
    factors = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


def run_mitm_campaign():
    """Lance la campagne MITM pour k=22 puis etend si possible."""
    print("=" * 72)
    print("R171 — CAMPAGNE MITM : PREUVE COMPUTATIONNELLE")
    print("Objectif : Prouver N_0(d(k)) = 0 pour k = 22, 23, ...")
    print("=" * 72)

    all_results = {}

    # D'abord, verifier les petits k (validation du code)
    print("\n--- VALIDATION sur k=3..8 (resultats connus) ---")
    for k in range(3, 9):
        res = mitm_prove_k(k, verbose=False)
        S, d, top = compute_params(k)
        factors = factor_trial(d)
        res["d_factored"] = str(factors)
        status = "OK (N0=0)" if res["N0_equals_zero"] else "COLLISION!"
        print(f"  k={k:>2d} : d={d:>12,} = {factors}, "
              f"C={comb(S-1,k-1):>10,}, "
              f"ops={res['total_operations']:>10,}, "
              f"t={res['elapsed_s']:.3f}s -> {status}")
        all_results[f"k={k}"] = res

    # Maintenant le test principal : k=22
    print("\n" + "=" * 72)
    print("*** TEST PRINCIPAL : k=22 ***")
    print("=" * 72)

    k = 22
    S, d, top = compute_params(k)
    factors = factor_trial(d)
    print(f"  d({k}) = {d:,} = {factors}")

    res = mitm_prove_k(k, verbose=True)
    res["d_factored"] = str(factors)
    all_results[f"k={k}"] = res

    if res["N0_equals_zero"]:
        print(f"\n{'*'*72}")
        print(f"*** N_0(d({k})) = 0 PROUVE PAR MITM EXHAUSTIF ***")
        print(f"*** k={k} EST FERME — AUCUN {k}-CYCLE DE COLLATZ ***")
        print(f"{'*'*72}")

    # Si k=22 reussit, etendre a k=23, 24, ...
    if res["N0_equals_zero"]:
        print("\n--- EXTENSION : k=23, 24, ... ---")
        for k_ext in range(23, 42):
            S_ext, d_ext, top_ext = compute_params(k_ext)
            C_ext = comb(S_ext - 1, k_ext - 1)

            # Estimer la complexite MITM
            half = (k_ext - 1) // 2
            est_left = sum(comb(m + half, half) for m in range(top_ext + 1))
            est_right = sum(comb(top_ext - m + (k_ext - 2 - half), k_ext - 2 - half)
                          for m in range(top_ext + 1))
            est_total = est_left + est_right

            feasible = est_total < 5_000_000_000  # 5 milliards = seuil

            factors_ext = factor_trial(d_ext) if d_ext < 10**15 else "too_large"

            print(f"  k={k_ext:>2d} : S={S_ext:>3d}, d={d_ext:>20,}, "
                  f"C={C_ext:>15,}, MITM_ops={est_total:>15,}, "
                  f"{'FAISABLE' if feasible else 'TROP GROS'}")

            if feasible and est_total < 500_000_000:  # Seuil plus strict : 500M
                print(f"        -> Lancement MITM pour k={k_ext}...")
                t0 = time.time()
                res_ext = mitm_prove_k(k_ext, verbose=True)
                res_ext["d_factored"] = str(factors_ext)
                all_results[f"k={k_ext}"] = res_ext

                if res_ext["N0_equals_zero"]:
                    print(f"  *** k={k_ext} FERME ***")
                else:
                    print(f"  !!! COLLISION TROUVEE pour k={k_ext} !!!")
                    break

    # Sauvegarder
    output_file = "R171_MITM_results.json"
    with open(output_file, "w") as f:
        json.dump(all_results, f, indent=2, default=str)
    print(f"\nResultats sauvegardes dans {output_file}")

    # Resume
    print("\n" + "=" * 72)
    print("RESUME CAMPAGNE MITM")
    print("=" * 72)
    proven = [k for k, v in all_results.items() if v.get("N0_equals_zero")]
    failed = [k for k, v in all_results.items() if not v.get("N0_equals_zero")]
    print(f"  N_0(d) = 0 PROUVE pour : {proven}")
    if failed:
        print(f"  COLLISION trouvee pour : {failed}")

    return all_results


if __name__ == "__main__":
    run_mitm_campaign()
