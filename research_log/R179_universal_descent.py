#!/usr/bin/env python3
"""
R179b — DESCENTE 2-ADIQUE : EXTENSION x=3..30 + ANALYSE THÉORIQUE

R179a a montré : 2284/2284 cas exclus pour x=3..10, 0 survivants.

Ce script :
1. Étend à x=3..30 (couvrant tout le gap Bloc 3)
2. Analyse le MÉCANISME d'exclusion : pourquoi la descente réussit-elle toujours ?
3. Cherche un théorème universel : "la descente exclut TOUT k impair pour TOUT x"
"""

from math import gcd


def v2(n):
    """Valuation 2-adique de n."""
    if n == 0:
        return float('inf')
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


def g_max(S, x):
    """Maximum de g(v)."""
    return sum(3**(x-1-j) * 2**(S-x+j) for j in range(x))


def k_max_for_Sx(S, x):
    d = 2**S - 3**x
    if d <= 0:
        return 0
    gm = g_max(S, x)
    return gm // d


def two_adic_descent(S, x, k):
    """
    Descente 2-adique pour g = k·d avec e₀=0.
    Retourne (excluded, Ds, reason, failure_type).
    failure_type: 'periodic', 'v2_contradiction', 'overflow', 'underflow',
                  'remainder_nonzero', 'position_out_of_range', 'SOLUTION'
    """
    d = 2**S - 3**x
    if d <= 0:
        return True, [], "d ≤ 0", "trivial"

    target = k * d

    Ds = [0]
    remainder = target - 3**(x-1)

    if remainder <= 0:
        return True, Ds, f"R₀ = {remainder} ≤ 0", "underflow"
    if remainder == 0:
        return True, Ds, "R₀ = 0 prématuré", "premature_zero"

    for m in range(1, x):
        coeff = 3**(x-1-m)

        if remainder == 0:
            return True, Ds, f"R_{m-1} = 0 prématuré", "premature_zero"

        v2_rem = v2(remainder)
        D_m = v2_rem

        if D_m <= Ds[-1]:
            return True, Ds + [D_m], f"D_{m}={D_m} ≤ D_{m-1}={Ds[-1]}", "v2_contradiction"

        if D_m >= S:
            return True, Ds + [D_m], f"D_{m}={D_m} ≥ S={S}", "position_out_of_range"

        Ds.append(D_m)
        remainder -= coeff * 2**D_m

        if remainder < 0:
            return True, Ds, f"R_{m} < 0", "overflow"

    if remainder != 0:
        return True, Ds, f"Reste final = {remainder}", "remainder_nonzero"

    # Check periodicity
    positions = tuple(Ds)
    v = tuple(1 if i in positions else 0 for i in range(S))
    for period in range(1, S):
        if S % period == 0 and period < S:
            if v == v[:period] * (S // period):
                return True, Ds, f"PÉRIODIQUE (période {period})", "periodic"

    return False, Ds, f"⚠️ SOLUTION D={Ds}", "SOLUTION"


def main():
    print("=" * 80)
    print("R179b — DESCENTE 2-ADIQUE UNIVERSELLE : x = 3..30")
    print("=" * 80)

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 1 : Extension systématique x=3..30
    # ═══════════════════════════════════════════════════════════════════════
    print("\n" + "═" * 70)
    print("PARTIE 1 : DESCENTE SYSTÉMATIQUE x = 3..30")
    print("═" * 70)

    grand_total = 0
    grand_excluded = 0
    grand_survivors = []
    failure_types = {}

    for x in range(3, 31):
        S_min = int(x * 1.585) + 1
        while 2**S_min <= 3**x:
            S_min += 1

        x_total = 0
        x_excluded = 0
        x_max_k = 0

        for S in range(S_min, S_min + 25):
            d = 2**S - 3**x
            if d <= 0:
                continue
            km = k_max_for_Sx(S, x)
            if km == 0:
                continue

            for k in range(1, min(km + 1, 500)):
                if k % 2 == 0:
                    continue

                x_total += 1
                grand_total += 1
                x_max_k = max(x_max_k, k)

                success, Ds, reason, ftype = two_adic_descent(S, x, k)

                failure_types[ftype] = failure_types.get(ftype, 0) + 1

                if success:
                    x_excluded += 1
                    grand_excluded += 1
                else:
                    grand_survivors.append((S, x, k, Ds, reason))

        status = "✅" if x_total == x_excluded else "⚠️"
        print(f"  {status} x={x:2d}: {x_excluded}/{x_total} exclus, "
              f"k_max testé={x_max_k}")

    print(f"\n  GRAND TOTAL : {grand_excluded}/{grand_total} exclus, "
          f"{len(grand_survivors)} survivants")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 2 : Distribution des types d'exclusion
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 2 : TYPES D'EXCLUSION")
    print("═" * 70)

    for ftype, count in sorted(failure_types.items(), key=lambda x: -x[1]):
        pct = 100 * count / grand_total if grand_total > 0 else 0
        print(f"  {ftype:30s}: {count:6d} ({pct:5.1f}%)")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 3 : Analyse du pattern pour k=3
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 3 : PATTERN k=3 — POURQUOI LE RESTE FINAL EST-IL TOUJOURS NON NUL ?")
    print("═" * 70)

    print("\nPour k=3, la descente force certains D_j. Le reste final suit-il un pattern ?\n")

    for x in range(3, 12):
        S_min = int(x * 1.585) + 1
        while 2**S_min <= 3**x:
            S_min += 1

        print(f"\n  x = {x}:")
        for S in range(S_min, S_min + 8):
            d = 2**S - 3**x
            if d <= 0:
                continue
            km = k_max_for_Sx(S, x)
            if km < 3:
                continue

            success, Ds, reason, ftype = two_adic_descent(S, x, 3)

            # Compute the actual D values found
            print(f"    S={S:3d}: D={Ds}, type={ftype}, raison={reason}")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 4 : La formule du reste pour k général
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 4 : FORMULE DU RESTE POUR k IMPAIR")
    print("═" * 70)
    print("""
Pour k impair, la descente commence par :
  R₀ = k·d - 3^{x-1} = k·(2^S - 3^x) - 3^{x-1}
     = k·2^S - (3k+1)·3^{x-1}

Pour k=1 : R₀ = 2^S - 4·3^{x-1}, v₂(R₀) = v₂(2^S - 4·3^{x-1}) = 2
           (car 4·3^{x-1} ≡ 4 mod 8, et 2^S ≡ 0 mod 8 pour S≥3)

Pour k=3 : R₀ = 3·2^S - 10·3^{x-1}
           v₂(R₀) = v₂(3·2^S - 10·3^{x-1}) = v₂(2(3·2^{S-1} - 5·3^{x-1})) = 1
           (car 3·2^{S-1} est pair pour S≥2, et 5·3^{x-1} est impair
            → 3·2^{S-1} - 5·3^{x-1} est impair → v₂ = 1)
""")

    # Verify v₂(R₀) pattern for various k
    print("  v₂(R₀) pour différents k impairs :\n")
    for x in [5, 7, 10, 15]:
        S = int(x * 1.585) + 3
        while 2**S <= 3**x:
            S += 1
        d = 2**S - 3**x
        print(f"  x={x}, S={S}, d={d}:")
        for k in [1, 3, 5, 7, 9, 11, 13, 15]:
            R0 = k * d - 3**(x-1)
            if R0 <= 0:
                print(f"    k={k:3d}: R₀ = {R0} ≤ 0")
                continue
            v = v2(R0)
            # Also compute k·2^S and (3k+1)·3^{x-1}
            term1 = k * 2**S
            term2 = (3*k + 1) * 3**(x-1)
            print(f"    k={k:3d}: R₀ = {R0:>15d}, v₂(R₀) = {v:2d}, "
                  f"k·2^S = {term1}, (3k+1)·3^{{x-1}} = {term2}, "
                  f"v₂(3k+1) = {v2(3*k+1)}")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 5 : Le théorème de structure — pourquoi v₂ force D_j
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 5 : STRUCTURE THÉORIQUE DE LA DESCENTE")
    print("═" * 70)
    print("""
OBSERVATION CLÉ :

Pour k impair :
  R₀ = k·2^S - (3k+1)·3^{x-1}

  v₂(R₀) = v₂(3k+1)  (car 3k+1 ≡ 4 mod 8 si k impair, donc v₂(3k+1) ≥ 2)

  Wait... vérifions :
  k=1 : 3k+1 = 4 = 2², v₂ = 2
  k=3 : 3k+1 = 10 = 2·5, v₂ = 1
  k=5 : 3k+1 = 16 = 2⁴, v₂ = 4
  k=7 : 3k+1 = 22 = 2·11, v₂ = 1
  k=9 : 3k+1 = 28 = 4·7, v₂ = 2
  k=11: 3k+1 = 34 = 2·17, v₂ = 1
  k=13: 3k+1 = 40 = 8·5, v₂ = 3
  k=15: 3k+1 = 46 = 2·23, v₂ = 1

  Pattern : v₂(3k+1) est irrégulier.

  Pour k=1 : D₁ = v₂(R₀) = 2, puis récurrence force D_j = 2j.
  Pour k=3 : D₁ = v₂(R₀) = 1 (car v₂(3·3+1) = v₂(10) = 1).
             Puis R₁ = R₀ - 3^{x-2}·2^1 = ... et la suite diffère.

  La question est : pourquoi le RESTE FINAL n'est-il JAMAIS 0 ?
""")

    # For each k, trace the complete descent and observe the final remainder
    print("  Descente complète pour x=5, quelques k :\n")
    x = 5
    S_min = int(x * 1.585) + 1
    while 2**S_min <= 3**x:
        S_min += 1
    S = S_min + 3  # Choose a nice S

    d = 2**S - 3**x
    print(f"  x={x}, S={S}, d={d}\n")

    for k in [1, 3, 5, 7, 9, 11, 13, 15]:
        target = k * d
        if target <= 3**(x-1):
            continue
        print(f"    k={k}: target = {target}")

        remainder = target - 3**(x-1)
        Ds = [0]
        for m in range(1, x):
            if remainder <= 0:
                print(f"      Step {m}: remainder = {remainder} ≤ 0 → STOP")
                break
            v = v2(remainder)
            D_m = v
            coeff = 3**(x-1-m)
            subtracted = coeff * 2**D_m
            new_rem = remainder - subtracted
            print(f"      Step {m}: R={remainder}, v₂={v}, D_{m}={D_m}, "
                  f"subtract {coeff}·2^{D_m}={subtracted}, new_R={new_rem}")
            Ds.append(D_m)
            remainder = new_rem
        print(f"      Final: D={Ds}, remainder={remainder}")
        print()

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 6 : Hypothèse — le reste final a un facteur 2^{2(x-1)} ?
    # ═══════════════════════════════════════════════════════════════════════
    print("\n" + "═" * 70)
    print("PARTIE 6 : PATTERN DU RESTE FINAL")
    print("═" * 70)
    print("Pour k=3, le reste final est-il toujours = k·2^S - C pour une constante C ?\n")

    for x in range(3, 12):
        S_min = int(x * 1.585) + 1
        while 2**S_min <= 3**x:
            S_min += 1

        print(f"  x = {x}:")
        for S in range(S_min + 2, S_min + 6):
            d = 2**S - 3**x
            if d <= 0:
                continue
            km = k_max_for_Sx(S, x)

            for k in [3, 5, 7]:
                if k > km:
                    continue
                success, Ds, reason, ftype = two_adic_descent(S, x, k)
                if ftype == "remainder_nonzero":
                    # Extract the remainder from the reason
                    rem = int(reason.split("= ")[1])
                    v2_rem = v2(rem)
                    odd_part = rem >> v2_rem
                    print(f"    S={S:3d}, k={k}: D={Ds}, reste={rem} = 2^{v2_rem}·{odd_part}")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 7 : Le reste final comme fonction de k et S
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 7 : FORMULE FERMÉE DU RESTE FINAL (k=3)")
    print("═" * 70)
    print("""
Pour k=3, x fixé :
  Après la descente, le reste final dépend de S.
  Observons le pattern reste_final(S) :
""")

    for x in [4, 5, 6, 7]:
        S_min = int(x * 1.585) + 1
        while 2**S_min <= 3**x:
            S_min += 1

        print(f"\n  x = {x}:")
        rems = []
        for S in range(S_min, S_min + 12):
            d = 2**S - 3**x
            if d <= 0:
                continue
            km = k_max_for_Sx(S, x)
            if km < 3:
                continue

            success, Ds, reason, ftype = two_adic_descent(S, x, 3)
            if ftype == "remainder_nonzero":
                rem = int(reason.split("= ")[1])
                rems.append((S, rem))
                if len(rems) >= 2:
                    ratio = rems[-1][1] / rems[-2][1]
                else:
                    ratio = 0
                print(f"    S={S:3d}: reste = {rem:>12d}, ratio = {ratio:.4f}")

        if len(rems) >= 3:
            # Check if ratio stabilizes
            ratios = [rems[i+1][1]/rems[i][1] for i in range(len(rems)-1)]
            if all(abs(r - 2.0) < 0.1 for r in ratios[-3:]):
                print(f"    → Ratio stabilise à ~2 : reste ∝ 2^S")
            elif all(abs(r - 4.0) < 0.1 for r in ratios[-3:]):
                print(f"    → Ratio stabilise à ~4 : reste ∝ 4^S")


if __name__ == '__main__':
    main()
