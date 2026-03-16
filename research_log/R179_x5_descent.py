#!/usr/bin/env python3
"""
R179 — EXTENSION DE LA DESCENTE 2-ADIQUE À x=5..10

ACQUIS R178 :
- k=1 EXCLU universellement (force vecteur périodique)
- k=2 EXCLU universellement (contradiction v₂ immédiate)
- x=3 PROUVÉ : seul k=1 possible pour S≥7, et k=1 échoue
- x=4 PROUVÉ : k=1 échoue, k=2 contradiction v₂

OBJECTIF R179 :
Pour x=5..10, montrer que TOUT k≥3 impair échoue aussi.
Méthode : pour chaque x, calculer k_max(S) = floor(g_max/d),
puis pour chaque k = 1..k_max, appliquer la descente 2-adique.

QUESTION CLÉ : Existe-t-il des k ≥ 3 impairs survivants ?
"""

from itertools import combinations
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


def compute_g(positions, x):
    """g(v) = Σ 3^{x-1-j} · 2^{e_j}"""
    return sum(3**(x-1-j) * 2**positions[j] for j in range(x))


def g_max(S, x):
    """Maximum de g(v) pour vecteurs apériodiques (positions S-x,...,S-1)."""
    return sum(3**(x-1-j) * 2**(S-x+j) for j in range(x))


def k_max_for_Sx(S, x):
    """k_max = floor(g_max / d)."""
    d = 2**S - 3**x
    if d <= 0:
        return 0
    gm = g_max(S, x)
    return gm // d


def two_adic_descent(S, x, k, verbose=False):
    """
    Tente la descente 2-adique pour g = k·d avec e₀=0.
    h = 3^{x-1} + 3^{x-2}·2^{D₁} + ... + 2^{D_{x-1}} = k·d

    Retourne (success, D_sequence, reason) :
    - success=True si la descente prouve l'impossibilité
    - D_sequence = les D_j forcés
    - reason = explication
    """
    d = 2**S - 3**x
    if d <= 0:
        return True, [], "d ≤ 0"

    target = k * d
    # h = Σ_{j=0}^{x-1} 3^{x-1-j} · 2^{D_j}, D_0=0
    # R_0 = target - 3^{x-1} = k·d - 3^{x-1}
    # Each step: R_m = R_{m-1} - 3^{x-1-(m)} · 2^{D_m}
    # v₂(R_{m-1}) determines D_m

    Ds = [0]  # D_0 = 0
    remainder = target - 3**(x-1)

    if remainder <= 0:
        return True, Ds, f"R₀ = {remainder} ≤ 0 après premier terme"

    for m in range(1, x):
        coeff = 3**(x-1-m)  # coefficient = 3^{x-1-m}

        if remainder == 0:
            return True, Ds, f"R_{m-1} = 0 prématurément (termes restants non nuls)"

        # v₂(remainder) doit être ≥ D_m, et D_m est déterminé par v₂
        v2_rem = v2(remainder)

        # v₂(coeff · 2^{D_m}) = v₂(3^{x-1-m}) + D_m = 0 + D_m = D_m
        # (car 3^anything est impair)
        # Pour que la soustraction fonctionne : D_m = v₂(remainder)
        D_m = v2_rem

        # D_m doit être > D_{m-1} (positions strictement croissantes)
        if D_m <= Ds[-1]:
            return True, Ds + [D_m], f"D_{m} = {D_m} ≤ D_{m-1} = {Ds[-1]} : positions non croissantes"

        # D_m doit être < S (position dans {0,...,S-1})
        if D_m >= S:
            return True, Ds + [D_m], f"D_{m} = {D_m} ≥ S = {S} : position hors bornes"

        Ds.append(D_m)
        remainder -= coeff * 2**D_m

        if remainder < 0:
            return True, Ds, f"R_{m} = {remainder} < 0 : dépassement"

    # Après x-1 étapes, remainder devrait être 0
    if remainder != 0:
        return True, Ds, f"Reste final = {remainder} ≠ 0"

    # Vérifier si le vecteur est périodique
    positions = tuple(Ds)
    v = tuple(1 if i in positions else 0 for i in range(S))
    for period in range(1, S):
        if S % period == 0 and period < S:
            if v == v[:period] * (S // period):
                return True, Ds, f"Vecteur {Ds} PÉRIODIQUE (période {period})"

    # La descente a trouvé un vecteur apériodique valide !
    return False, Ds, f"⚠️ SOLUTION TROUVÉE : D={Ds}, g={target}, k={k}"


def main():
    print("=" * 80)
    print("R179 — EXTENSION DESCENTE 2-ADIQUE : x = 5..10")
    print("=" * 80)

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 1 : Pour chaque (x, S), lister les k possibles
    # ═══════════════════════════════════════════════════════════════════════
    print("\n" + "═" * 70)
    print("PARTIE 1 : k_max PAR (x, S)")
    print("═" * 70)
    print("Pour chaque x, les k possibles décroissent avec S.\n")

    for x in range(3, 11):
        S_min = int(x * 1.585) + 1
        while 2**S_min <= 3**x:
            S_min += 1

        print(f"\n  x = {x}:")
        for S in range(S_min, min(S_min + 20, 50)):
            d = 2**S - 3**x
            if d <= 0:
                continue
            km = k_max_for_Sx(S, x)
            if km > 0:
                # List odd k values
                odd_ks = [k for k in range(1, km+1) if k % 2 == 1]
                print(f"    S={S:3d}: d={d:>15d}, k_max={km:>6d}, "
                      f"k impairs ≤ k_max : {odd_ks[:10]}"
                      f"{'...' if len(odd_ks) > 10 else ''}")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 2 : Descente 2-adique pour chaque (x, S, k)
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 2 : DESCENTE 2-ADIQUE SYSTÉMATIQUE")
    print("═" * 70)

    survivors = []
    total_tested = 0
    total_excluded = 0

    for x in range(3, 11):
        S_min = int(x * 1.585) + 1
        while 2**S_min <= 3**x:
            S_min += 1

        x_survivors = []

        for S in range(S_min, min(S_min + 25, 60)):
            d = 2**S - 3**x
            if d <= 0:
                continue
            km = k_max_for_Sx(S, x)

            for k in range(1, min(km + 1, 200)):
                if k % 2 == 0:
                    continue  # k pair exclu par parité (d est impair, g impair structure)

                total_tested += 1
                success, Ds, reason = two_adic_descent(S, x, k)

                if success:
                    total_excluded += 1
                else:
                    x_survivors.append((S, x, k, Ds, reason))

        if x_survivors:
            print(f"\n  ⚠️ x={x}: {len(x_survivors)} SURVIVANTS :")
            for S, x_, k, Ds, reason in x_survivors[:10]:
                print(f"    S={S}, k={k}: {reason}")
            survivors.extend(x_survivors)
        else:
            print(f"\n  ✅ x={x}: TOUS les (S,k) exclus par descente 2-adique")

    print(f"\n\n  BILAN : {total_excluded}/{total_tested} cas exclus, "
          f"{len(survivors)} survivants")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 3 : Analyse détaillée des survivants
    # ═══════════════════════════════════════════════════════════════════════
    if survivors:
        print("\n\n" + "═" * 70)
        print("PARTIE 3 : ANALYSE DES SURVIVANTS")
        print("═" * 70)

        for S, x, k, Ds, reason in survivors[:30]:
            d = 2**S - 3**x
            g = k * d
            print(f"\n  S={S}, x={x}, k={k}: d={d}, g={g}")
            print(f"    Positions D = {Ds}")
            print(f"    Raison : {reason}")

            # Vérifier avec g(v) direct
            g_check = compute_g(tuple(Ds), x)
            print(f"    Vérification : g(D) = {g_check}, k·d = {k*d}, "
                  f"match = {g_check == k*d}")

            # Ce vecteur est-il dans l'ensemble des solutions réelles ?
            # Vérifions tous les vecteurs apériodiques
            found_any = False
            for positions in combinations(range(S), x):
                v = tuple(1 if i in positions else 0 for i in range(S))
                is_periodic = False
                for period in range(1, S):
                    if S % period == 0 and period < S:
                        if v == v[:period] * (S // period):
                            is_periodic = True
                            break
                if is_periodic:
                    continue

                g_val = compute_g(positions, x)
                if g_val % d == 0:
                    found_any = True
                    print(f"    ❌ VRAI d|g : positions={positions}, "
                          f"g={g_val}, k={g_val//d}")
                    break

            if not found_any:
                print(f"    ✅ Confirmation : aucun vecteur apériodique avec d|g(v)")
                print(f"    → Le survivant est un ARTEFACT de la descente naive")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 4 : Pourquoi la descente échoue-t-elle parfois ?
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 4 : DIAGNOSTIC DES SURVIVANTS")
    print("═" * 70)
    print("""
La descente 2-adique force D_m = v₂(R_{m-1}).
Cela suppose que le terme 3^{x-1-m}·2^{D_m} est le SEUL terme
contribuant à la valuation 2-adique du reste.

Si PLUSIEURS termes restants contribuent à la même puissance de 2,
la descente peut construire un "faux" vecteur (apériodique mais
correspondant à un g qui n'est PAS un multiple de d).

Ou bien : la descente trouve une solution qui EST valide mais qui
correspond à un vecteur APÉRIODIQUE — ce qui serait une vraie menace.

Distinguons ces deux cas pour chaque survivant.
""")

    # Additional analysis for k even (reminder)
    print("\n  RAPPEL : k pairs")
    print("  k=2 exclu universellement (T192) :")
    print("  R₀ = 2d - 3^{x-1} = 2^{S+1} - 7·3^{x-1} — impair → v₂ contradiction")

    # Check : est-ce que k=4,6,8,... sont aussi exclus ?
    print("\n  Test k pairs (k=4,6,8,...) :")
    for x in range(3, 8):
        S_min = int(x * 1.585) + 1
        while 2**S_min <= 3**x:
            S_min += 1

        for S in range(S_min, S_min + 10):
            d = 2**S - 3**x
            if d <= 0:
                continue
            km = k_max_for_Sx(S, x)

            for k in range(2, min(km+1, 50), 2):  # k pair
                success, Ds, reason = two_adic_descent(S, x, k)
                if not success:
                    print(f"    ⚠️ SURVIVANT PAIR : S={S}, x={x}, k={k}: {reason}")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 5 : Pattern dans les valeurs finales de la descente k=1
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 5 : FACTEUR IMPAIR DANS LA VALEUR FINALE (k=1)")
    print("═" * 70)
    print("Pour k=1, la descente force D_j=2j. La valeur finale est :")
    print("  R_{x-1} = 2^S - 3·4^{x-1}")
    print("  = 4^{x-1}·(2^{S-2(x-1)} - 3)")
    print("Pour S > 2x : 2^{S-2(x-1)} - 3 est IMPAIR et > 1 → pas une puissance de 2\n")

    for x in range(2, 15):
        for S in [2*x, 2*x+1, 2*x+2, 2*x+5, 2*x+10]:
            d = 2**S - 3**x
            if d <= 0:
                continue
            val = 2**S - 3 * 4**(x-1)
            if val <= 0:
                continue
            odd_part = val >> v2(val)
            print(f"  x={x:2d}, S={S:3d}: 2^S - 3·4^{{x-1}} = {val:>15d} = "
                  f"2^{v2(val)} · {odd_part}"
                  f"  {'← IMPAIR>1 ✓' if odd_part > 1 else '← PUISSANCE DE 2 ⚠️'}")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 6 : La descente pour k=3 (premier k impair non trivial)
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 6 : DESCENTE k=3 SYSTÉMATIQUE")
    print("═" * 70)

    for x in range(3, 9):
        S_min = int(x * 1.585) + 1
        while 2**S_min <= 3**x:
            S_min += 1

        print(f"\n  x = {x}:")
        for S in range(S_min, S_min + 15):
            d = 2**S - 3**x
            if d <= 0:
                continue
            km = k_max_for_Sx(S, x)
            if km < 3:
                continue

            success, Ds, reason = two_adic_descent(S, x, 3)
            status = "EXCLU" if success else "SURVIVANT"
            print(f"    S={S:3d}: k=3, d={d:>12d}, {status}: {reason}")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 7 : Vérification exhaustive d ∤ g pour x=5..8
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 7 : VÉRIFICATION EXHAUSTIVE d ∤ g(v)")
    print("═" * 70)
    print("Confirme que AUCUN vecteur apériodique ne donne d|g, même si la descente a des survivants\n")

    for x in range(3, 9):
        S_min = int(x * 1.585) + 1
        while 2**S_min <= 3**x:
            S_min += 1

        any_found = False
        cases_checked = 0

        for S in range(S_min, min(S_min + 12, 25)):
            d = 2**S - 3**x
            if d <= 0:
                continue

            cases_checked += 1
            for positions in combinations(range(S), x):
                v = tuple(1 if i in positions else 0 for i in range(S))
                is_periodic = False
                for period in range(1, S):
                    if S % period == 0 and period < S:
                        if v == v[:period] * (S // period):
                            is_periodic = True
                            break
                if is_periodic:
                    continue

                g_val = compute_g(positions, x)
                if g_val % d == 0:
                    print(f"  ❌ x={x}, S={S}: d|g ! pos={positions}, g={g_val}")
                    any_found = True
                    break

            if any_found:
                break

        if not any_found:
            print(f"  ✅ x={x}: CONFIRMÉ d ∤ g(v) pour {cases_checked} valeurs de S")
        else:
            print(f"  ❌ x={x}: TROUVÉ d|g ! Analyser en détail.")

    # ═══════════════════════════════════════════════════════════════════════
    # SYNTHÈSE
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("SYNTHÈSE R179")
    print("═" * 70)
    print(f"""
  Cas testés par descente 2-adique : {total_tested}
  Exclus par descente : {total_excluded}
  Survivants : {len(survivors)}

  Si survivants = 0 : la descente 2-adique suffit pour x=3..10 !
  Si survivants > 0 : analyser si ce sont des artefacts ou de vrais dangers.
  Dans tous les cas : vérification exhaustive confirme d ∤ g(v) pour S petit.
""")


if __name__ == '__main__':
    main()
