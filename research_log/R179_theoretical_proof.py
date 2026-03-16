#!/usr/bin/env python3
"""
R179c — VERS LA PREUVE THÉORIQUE DE LA DESCENTE UNIVERSELLE

ACQUIS R179a+b :
- 111215/111215 cas exclus pour x=3..30, k impair ≤ 499
- 0 survivants
- k=3: D=[0,1,5,7,9,...,2x-3], reste = 2^{2x-2}·(2^{S-2x+2}-5·3^{x-1}/2^{2x-3}) ∝ 2^S

OBJECTIF : Prouver théoriquement que la descente EXCLUT TOUJOURS tout k impair ≥ 3.

STRATÉGIE :
Pour chaque k impair, la descente produit une suite D_0=0, D_1, D_2, ..., D_{x-1}
et un reste R_{x-1}. On veut montrer que R_{x-1} ≠ 0 TOUJOURS.

Si on peut exprimer R_{x-1} en forme fermée en fonction de k, S, x,
et montrer que R_{x-1} > 0 pour S suffisamment grand, c'est gagné.
"""

from math import gcd


def v2(n):
    if n == 0:
        return float('inf')
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


def full_descent(S, x, k):
    """
    Descente complète. Retourne (Ds, remainders, success).
    """
    d = 2**S - 3**x
    if d <= 0:
        return [0], [0], True

    target = k * d
    Ds = [0]
    remainders = [target - 3**(x-1)]

    if remainders[0] <= 0:
        return Ds, remainders, True

    for m in range(1, x):
        rem = remainders[-1]
        if rem == 0:
            return Ds, remainders, True
        if rem < 0:
            return Ds, remainders, True

        v = v2(rem)
        D_m = v
        coeff = 3**(x-1-m)
        new_rem = rem - coeff * 2**D_m

        Ds.append(D_m)
        remainders.append(new_rem)

    return Ds, remainders, remainders[-1] != 0


def main():
    print("=" * 80)
    print("R179c — VERS LA PREUVE THÉORIQUE : FORMULE DU RESTE")
    print("=" * 80)

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 1 : Pour k=3, calculer D et le reste en forme fermée
    # ═══════════════════════════════════════════════════════════════════════
    print("\n" + "═" * 70)
    print("PARTIE 1 : DESCENTE k=3 — POSITIONS FORCÉES")
    print("═" * 70)
    print("""
Pour k=3 :
  R₀ = 3·2^S - 10·3^{x-1}
  v₂(R₀) = 1 (car 10 = 2·5, et 3·2^S a v₂ = S, 10·3^{x-1} a v₂ = 1, donc min = 1)

  D₁ = 1
  R₁ = R₀ - 3^{x-2}·2¹ = 3·2^S - 10·3^{x-1} - 2·3^{x-2}
     = 3·2^S - (10·3 + 2)·3^{x-2} = 3·2^S - 32·3^{x-2}

  v₂(R₁) = v₂(3·2^S - 32·3^{x-2}) = 5
  (car 32 = 2^5, et 3·2^S a v₂ = S ≥ 5 pour S ≥ 5)

  D₂ = 5
  R₂ = R₁ - 3^{x-3}·2^5 = 3·2^S - 32·3^{x-2} - 32·3^{x-3}
     = 3·2^S - 32·3^{x-3}·(3+1) = 3·2^S - 128·3^{x-3}

  v₂(R₂) = 7 (car 128 = 2^7)

  D₃ = 7
  R₃ = R₂ - 3^{x-4}·2^7 = 3·2^S - 128·3^{x-3} - 128·3^{x-4}
     = 3·2^S - 128·3^{x-4}·4 = 3·2^S - 512·3^{x-4}

  Pattern émergent : R_m = 3·2^S - 2^{2m+1}·3^{x-1-m} pour m ≥ 1
""")

    # Vérifier cette formule
    print("  Vérification de R_m = 3·2^S - 2^{2m+1}·3^{x-1-m} :\n")

    for x in [5, 7, 10]:
        S_min = int(x * 1.585) + 3
        while 2**S_min <= 3**x:
            S_min += 1
        S = S_min + 5

        Ds, remainders, _ = full_descent(S, x, 3)
        print(f"  x={x}, S={S}:")
        for m in range(min(len(remainders), x)):
            actual = remainders[m]
            if m == 0:
                predicted = 3 * 2**S - 10 * 3**(x-1)
            else:
                predicted = 3 * 2**S - 2**(2*m+1) * 3**(x-1-m)
            match = actual == predicted
            print(f"    m={m}: actual={actual}, predicted={predicted}, "
                  f"match={'✅' if match else '❌'}")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 2 : Formule générale pour k quelconque
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 2 : PATTERN POUR k QUELCONQUE")
    print("═" * 70)
    print("""
HYPOTHÈSE : Pour tout k impair, la descente produit :
  R_m = k·2^S - C_m(k)·3^{x-1-m}

où C_m(k) est une constante dépendant de k et m (pas de S).

Si c'est vrai, alors le reste final R_{x-1} = k·2^S - C_{x-1}(k)
est ≠ 0 dès que C_{x-1}(k) ≠ k·2^S, ce qui est vrai pour S assez grand
(car C_{x-1} est une constante).

Vérifions cette structure...
""")

    for k in [1, 3, 5, 7, 9, 11, 13, 15]:
        print(f"\n  k = {k}:")
        for x in [5, 7]:
            S_min = int(x * 1.585) + 3
            while 2**S_min <= 3**x:
                S_min += 1

            # Compute for two different S values to check S-independence of C_m
            results = {}
            for S in [S_min + 5, S_min + 10]:
                Ds, remainders, _ = full_descent(S, x, k)
                results[S] = (Ds, remainders)

            S1, S2 = S_min + 5, S_min + 10
            Ds1, rem1 = results[S1]
            Ds2, rem2 = results[S2]

            print(f"    x={x}: D(S={S1}) = {Ds1}, D(S={S2}) = {Ds2}")

            # Check if D sequences are the same
            if Ds1 == Ds2:
                print(f"    → D indépendant de S ✅")
                # Extract C_m : R_m = k·2^S - C_m·3^{x-1-m}
                # C_m = (k·2^S - R_m) / 3^{x-1-m}
                for m in range(min(len(rem1), x)):
                    if x-1-m >= 0 and 3**(x-1-m) > 0:
                        C_m_1 = (k * 2**S1 - rem1[m]) / 3**(x-1-m) if m < len(rem1) else None
                        C_m_2 = (k * 2**S2 - rem2[m]) / 3**(x-1-m) if m < len(rem2) else None
                        if C_m_1 is not None and C_m_2 is not None:
                            match = abs(C_m_1 - C_m_2) < 0.5
                            if not match and m < x-1:
                                # Check alternative: R_m = k·2^S - C_m (no 3 factor for last step)
                                pass
                            if m <= 3:
                                print(f"      C_{m} = {C_m_1:.1f} (S={S1}), "
                                      f"{C_m_2:.1f} (S={S2}), "
                                      f"{'CONSTANT ✅' if match else 'NOT constant ❌'}")
            else:
                print(f"    → D DÉPEND de S (problème)")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 3 : Le reste final pour k=3 — formule exacte
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 3 : RESTE FINAL k=3 — FORMULE EXACTE")
    print("═" * 70)
    print("""
Si R_m = 3·2^S - 2^{2m+1}·3^{x-1-m}, alors pour m = x-1 :

  R_{x-1} = 3·2^S - 2^{2(x-1)+1}·3^0 = 3·2^S - 2^{2x-1}

Ce n'est JAMAIS 0 car 3·2^S est divisible par 3 mais 2^{2x-1} ne l'est pas.
Mieux : R_{x-1} = 3·2^S - 2^{2x-1} > 0 pour S > 2x-1 (toujours vrai car S > 2x typiquement).

MAIS ATTENTION : R_{x-1} = 0 signifie g = k·d, on veut R_{x-1} ≠ 0.
Vérifions la formule :
""")

    for x in [4, 5, 6, 7, 8, 9, 10]:
        S_min = int(x * 1.585) + 3
        while 2**S_min <= 3**x:
            S_min += 1

        for S in [S_min + 5]:
            Ds, remainders, _ = full_descent(S, x, 3)
            actual = remainders[-1] if len(remainders) >= x else "N/A"
            predicted = 3 * 2**S - 2**(2*x-1)
            match = actual == predicted
            print(f"  x={x:2d}, S={S:3d}: actual={actual:>15}, "
                  f"predicted={predicted:>15}, {'✅' if match else '❌'}")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 4 : Formule du reste pour k=5, k=7, etc.
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 4 : RESTE FINAL POUR CHAQUE k IMPAIR")
    print("═" * 70)
    print("Extracting C(k) from R_{x-1} = k·2^S - C(k)\n")

    for k in [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21]:
        x = 7
        S_min = int(x * 1.585) + 3
        while 2**S_min <= 3**x:
            S_min += 1

        Ck_values = []
        for S in [S_min + 5, S_min + 10, S_min + 15]:
            d = 2**S - 3**x
            if d <= 0:
                continue
            km = d * k  # This is k*d not k_max
            Ds, remainders, _ = full_descent(S, x, k)
            if len(remainders) >= x:
                R_final = remainders[-1]
                if R_final > 0:
                    Ck = k * 2**S - R_final
                    Ck_values.append(Ck)

        if len(Ck_values) >= 2:
            all_same = all(c == Ck_values[0] for c in Ck_values)
            print(f"  k={k:3d}: C(k) = {Ck_values[0]:>15d} "
                  f"{'(constant across S) ✅' if all_same else '(VARIES!) ❌'}"
                  f"  v₂(C(k)) = {v2(Ck_values[0])}")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 5 : C(k) comme fonction de k — pattern ?
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 5 : C(k) COMME FONCTION DE k")
    print("═" * 70)

    for x in [5, 7, 10]:
        print(f"\n  x = {x}:")
        S_min = int(x * 1.585) + 3
        while 2**S_min <= 3**x:
            S_min += 1
        S = S_min + 10

        for k in range(1, 40, 2):
            d = 2**S - 3**x
            if k * d > sum(3**(x-1-j) * 2**(S-1) for j in range(x)):
                break

            Ds, remainders, _ = full_descent(S, x, k)
            if len(remainders) >= x and remainders[-1] > 0:
                Ck = k * 2**S - remainders[-1]
                print(f"    k={k:3d}: C(k) = {Ck:>15d}, C(k)/k = {Ck/k:>12.1f}, "
                      f"C(k) mod 3 = {Ck % 3}, v₂(C(k)) = {v2(Ck)}")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 6 : Le théorème — R_{x-1} ≠ 0 car 3 | R mais 3 ∤ 2^{2x-1}
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 6 : ARGUMENT DE DIVISIBILITÉ PAR 3")
    print("═" * 70)
    print("""
OBSERVATION CRUCIALE pour k=3 :
  R_{x-1} = 3·2^S - 2^{2x-1}

  Si R_{x-1} = 0 : 3·2^S = 2^{2x-1}, i.e., 3 = 2^{2x-1-S}.
  Mais 3 n'est PAS une puissance de 2. DONC R_{x-1} ≠ 0. ∎

  Pour k=1 (rappel T191) :
  R_{x-1} = 2^S - 3·4^{x-1} = 2^S - 3·2^{2(x-1)}
  Si = 0 : 2^{S-2(x-1)} = 3 → impossible.
  Si S = 2(x-1) : R = 1 - 3 = -2 < 0 → exclu aussi.
  Donc le seul cas = 0 est S = 2x avec vecteur périodique (déjà traité).

  Pour k=5 :
  Le C(k) doit être vérifié... est-il de la forme 5·2^a - b avec 3|b ?

  L'argument mod 3 est : si C(k) ≡ 0 mod 3, alors R_{x-1} = k·2^S - C(k).
  Pour R_{x-1} = 0 : k·2^S = C(k), donc k·2^S ≡ 0 mod 3.
  Mais k est impair et 2^S n'est jamais ≡ 0 mod 3, donc k·2^S ≢ 0 mod 3
  sauf si 3|k.

  Cas k ≡ 0 mod 3 (k=3,9,15,21,...) :
  Si C(k) ≡ 0 mod 3 et k ≡ 0 mod 3 : k·2^S ≡ 0 mod 3, OK.
  Mais on a besoin que C(k) = k·2^S pour R=0.
  C(k) est une constante (indépendante de S), et k·2^S croît → pas égaux.

  Cas k ≢ 0 mod 3 (k=1,5,7,11,13,...) :
  k·2^S ≢ 0 mod 3, donc si C(k) ≡ 0 mod 3 : R ≢ 0 mod 3 ≠ 0. ∎
""")

    # Check C(k) mod 3
    print("  C(k) mod 3 pour différents k :\n")
    x = 7
    S = 25
    for k in range(1, 30, 2):
        d = 2**S - 3**x
        if k > d * 2:  # rough bound
            break
        Ds, remainders, _ = full_descent(S, x, k)
        if len(remainders) >= x and remainders[-1] != 0:
            R = remainders[-1]
            Ck = k * 2**S - R
            print(f"    k={k:3d}: C(k) mod 3 = {Ck % 3}, "
                  f"k mod 3 = {k % 3}, "
                  f"k·2^S mod 3 = {(k * 2**S) % 3}, "
                  f"R mod 3 = {R % 3}"
                  f"  {'→ 3∤k et 3|C → R≢0 mod 3 ✅' if k%3 != 0 and Ck%3 == 0 else ''}"
                  f"  {'→ 3|k, need other argument' if k%3 == 0 else ''}")


if __name__ == '__main__':
    main()
