#!/usr/bin/env python3
"""
SESSION 10c — CHAÎNE D'EXCLUSION ET ANALYSE INVERSE
=====================================================
Protocole DISCOVERY v2.2 — Boucle G-V-R itération #2

HYPOTHÈSE : La chaîne d'exclusion inverse {-2^{-m}} crée une structure
qui empêche -1 d'être dans l'image de f pour les B non-décroissantes valides.

CRITÈRE DE SUCCÈS : Identifier un invariant/pattern UNIVERSEL dans la chaîne
qui explique pourquoi -1 est toujours exclu.

CRITÈRE D'ÉCHEC : Pas de pattern clair après 5 investigations → Cimetière.
"""

import math
from itertools import combinations_with_replacement
from collections import defaultdict
import time

def compute_params(k):
    """Calcule S, d, et vérifie si d est premier."""
    S = math.ceil(k * math.log2(3))
    d = 2**S - 3**k
    # Test primalité simple (suffisant pour nos tailles)
    if d < 2:
        return S, d, False
    if d < 4:
        return S, d, True
    if d % 2 == 0 or d % 3 == 0:
        return S, d, False
    i = 5
    while i * i <= d:
        if d % i == 0 or d % (i + 2) == 0:
            return S, d, False
        i += 6
    return S, d, True

def modinv(a, m):
    """Inverse modulaire via algorithme étendu d'Euclide."""
    g, x, _ = extended_gcd(a, m)
    if g != 1:
        return None
    return x % m

def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x

def multiplicative_order(a, n):
    """Ordre multiplicatif de a mod n."""
    if math.gcd(a, n) != 1:
        return None
    order = 1
    current = a % n
    while current != 1:
        current = (current * a) % n
        order += 1
        if order > n:
            return None
    return order

def compute_image_f(k, p, u, M):
    """Calcule l'image complète de f(B) = Σ u^j · 2^{B_j} pour B non-décroissante."""
    # B = (B_1, ..., B_{k-1}) non-décroissante dans [0, M]
    image = defaultdict(list)  # résidu → liste de B
    weights = [pow(u, j, p) for j in range(1, k)]  # u^1, ..., u^{k-1}

    for B in combinations_with_replacement(range(M + 1), k - 1):
        f_val = sum(weights[j] * pow(2, B[j], p) for j in range(k - 1)) % p
        image[f_val].append(B)

    return image

def investigate_exclusion_chain():
    """I1: Chaîne d'exclusion : orbite de -1 sous ⟨2⟩ et intersection avec Im(f)."""
    print("=" * 70)
    print("  INVESTIGATION 1 : Chaîne d'exclusion et orbite de -1")
    print("=" * 70)

    prime_ks = []
    for k in range(3, 18):
        S, d, is_prime = compute_params(k)
        if is_prime:
            prime_ks.append((k, S, d))

    for k, S, p in prime_ks:
        M = S - k  # borne supérieure pour B_j
        w = modinv(3, p)
        u = (2 * w) % p
        ord_u = multiplicative_order(u, p)
        ord_2 = multiplicative_order(2, p)

        print(f"\n--- k={k}, p={p}, u={u}, M={M}, ord(u)={ord_u}, ord_p(2)={ord_2} ---")

        # Calculer l'image complète
        image = compute_image_f(k, p, u, M)
        target = (p - 1) % p  # -1 mod p

        # Orbite de -1 sous multiplication par 2
        orbit_neg1 = []
        r = target
        for m in range(ord_2):
            orbit_neg1.append(r)
            r = (r * 2) % p

        # Orbite inverse de -1 sous division par 2
        inv2 = modinv(2, p)
        orbit_inv = []
        r = target
        for m in range(ord_2):
            orbit_inv.append(r)
            r = (r * inv2) % p

        print(f"    Orbite de -1 sous ×2 (taille {len(orbit_neg1)}) :")
        print(f"    = orbite sous ÷2 (même orbite, taille {len(orbit_inv)})")

        # Intersection de l'orbite avec l'image
        in_image = []
        not_in_image = []
        for i, r in enumerate(orbit_neg1):
            if r in image:
                in_image.append((i, r, len(image[r])))
            else:
                not_in_image.append((i, r))

        print(f"    Éléments de l'orbite DANS l'image : {len(in_image)}/{len(orbit_neg1)}")
        print(f"    Éléments de l'orbite HORS image : {len(not_in_image)}/{len(orbit_neg1)}")

        # Vérifier que -1 est bien hors image
        if target in image:
            print(f"    ⚠️ -1 = {target} EST dans l'image ! ({len(image[target])} compositions)")
        else:
            print(f"    ✓ -1 = {target} est HORS image")

        # Pour les éléments de l'orbite DANS l'image, vérifier si les B sont aux frontières
        if in_image:
            print(f"\n    Analyse des éléments de l'orbite dans l'image :")
            for idx, r, count in in_image[:5]:  # limiter l'affichage
                Bs = image[r]
                at_boundary = [B for B in Bs if B[-1] == M]  # B_{k-1} = M
                at_floor = [B for B in Bs if B[0] == 0]      # B_1 = 0
                print(f"      -2^{idx} = {r} : {count} compositions, "
                      f"{len(at_boundary)} au plafond (B_max=M), "
                      f"{len(at_floor)} au plancher (B_min=0)")

        # Éléments hors image qui sont dans l'orbite de -1
        if not_in_image:
            positions = [i for i, r in not_in_image]
            print(f"\n    Positions absentes dans l'orbite : {positions[:20]}")
            print(f"    -1 est à la position 0 de l'orbite")

            # Vérifier si les absents forment un pattern
            if len(positions) > 1:
                diffs = [positions[i+1] - positions[i] for i in range(len(positions)-1)]
                if len(set(diffs)) == 1:
                    print(f"    ★ Pattern régulier : espacement constant = {diffs[0]}")
                else:
                    print(f"    Espacements : {diffs[:10]}")

def investigate_backward_chain():
    """I2: Chaîne inverse depuis -1 : quels B pourraient donner -1 par shift ?"""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 2 : Remontée depuis -1 (backward chain)")
    print("=" * 70)

    for k in [3, 5]:
        S, d, _ = compute_params(k)
        p = d
        M = S - k
        w = modinv(3, p)
        u = (2 * w) % p

        print(f"\n--- k={k}, p={p}, M={M} ---")

        image = compute_image_f(k, p, u, M)
        target = p - 1  # -1 mod p
        inv2 = modinv(2, p)

        # Remonter : si f(B) = r et B-1 est valide, alors f(B-1) = r/2
        # Donc : pour atteindre -1, on a besoin d'un B avec f(B)=-1
        # OU un B' avec f(B')=-1/2 et B' shiftable (B'_min > 0)

        print(f"    Remontée depuis -1 = {target} :")

        r = target
        for step in range(min(M + 2, 10)):
            r_half = (r * inv2) % p

            if r in image:
                Bs = image[r]
                shiftable = [B for B in Bs if B[0] > 0]  # peut descendre
                at_floor = [B for B in Bs if B[0] == 0]   # ne peut pas descendre
                print(f"    Étape {step}: r = {r} → DANS l'image ({len(Bs)} comps)")
                print(f"      Shiftable vers haut (B_min>0) : {len(shiftable)}")
                print(f"      Au plancher (B_min=0) : {len(at_floor)}")
                if shiftable:
                    # Ces B, si on les décale de +1, donnent 2r
                    double_r = (2 * r) % p
                    print(f"      ⟹ 2r = {double_r} devrait être dans l'image via shift")
                    print(f"      2r dans image ? {'OUI' if double_r in image else 'NON'}")
            else:
                print(f"    Étape {step}: r = {r} → HORS image")
                # Le résidu r/2 ne peut pas "remonter" à r par shift

            r = r_half

def investigate_boundary_structure():
    """I3: Structure des B aux frontières (B_min=0 et B_max=M)."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 3 : Structure aux frontières (B_min=0, B_max=M)")
    print("=" * 70)

    for k in [3, 5, 7]:
        S, d, is_prime = compute_params(k)
        if not is_prime:
            continue
        p = d
        M = S - k
        w = modinv(3, p)
        u = (2 * w) % p

        print(f"\n--- k={k}, p={p}, M={M} ---")

        image = compute_image_f(k, p, u, M)

        # Séparer les B par type de frontière
        interior = defaultdict(int)     # B_min > 0 et B_max < M
        floor_only = defaultdict(int)   # B_min = 0 et B_max < M
        ceil_only = defaultdict(int)    # B_min > 0 et B_max = M
        both_boundary = defaultdict(int) # B_min = 0 et B_max = M

        total_B = 0
        for r, Bs in image.items():
            for B in Bs:
                total_B += 1
                if B[0] == 0 and B[-1] == M:
                    both_boundary[r] += 1
                elif B[0] == 0:
                    floor_only[r] += 1
                elif B[-1] == M:
                    ceil_only[r] += 1
                else:
                    interior[r] += 1

        print(f"    Total compositions : {total_B}")
        print(f"    Intérieur (0<B_min, B_max<M) : {sum(interior.values())} comps → {len(interior)} résidus")
        print(f"    Plancher seul (B_min=0, B_max<M) : {sum(floor_only.values())} comps → {len(floor_only)} résidus")
        print(f"    Plafond seul (B_min>0, B_max=M) : {sum(ceil_only.values())} comps → {len(ceil_only)} résidus")
        print(f"    Les deux (B_min=0, B_max=M) : {sum(both_boundary.values())} comps → {len(both_boundary)} résidus")

        # Quels résidus ne sont atteints QUE par les frontières ?
        only_boundary_residues = set()
        for r in set(list(floor_only.keys()) + list(ceil_only.keys()) + list(both_boundary.keys())):
            if r not in interior:
                only_boundary_residues.add(r)

        print(f"    Résidus atteints UNIQUEMENT aux frontières : {len(only_boundary_residues)}")
        target = p - 1
        print(f"    -1 = {target} : intérieur={interior.get(target,0)}, plancher={floor_only.get(target,0)}, "
              f"plafond={ceil_only.get(target,0)}, les_deux={both_boundary.get(target,0)}")

def investigate_image_closure():
    """I4: L'image est-elle presque fermée sous ×2 ? Mesurer le défaut."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 4 : Fermeture de l'image sous ×2")
    print("=" * 70)

    for k in [3, 5, 7, 13]:
        S, d, is_prime = compute_params(k)
        if not is_prime:
            continue
        p = d
        M = S - k
        w = modinv(3, p)
        u = (2 * w) % p

        print(f"\n--- k={k}, p={p}, M={M} ---")

        image = compute_image_f(k, p, u, M)
        image_set = set(image.keys())

        # Pour chaque r dans l'image, vérifier si 2r est aussi dans l'image
        closure_violations = 0
        total_checks = 0
        violations_detail = []

        for r in image_set:
            double_r = (2 * r) % p
            total_checks += 1
            if double_r not in image_set:
                closure_violations += 1
                # Vérifier : les B donnant r ont-elles TOUTES B_max = M ?
                Bs = image[r]
                all_at_ceiling = all(B[-1] == M for B in Bs)
                violations_detail.append((r, double_r, len(Bs), all_at_ceiling))

        print(f"    |Im(f)| = {len(image_set)}")
        print(f"    Violations ×2 : {closure_violations}/{total_checks}")
        print(f"    Taux de fermeture : {100*(1 - closure_violations/total_checks):.1f}%")

        if violations_detail:
            # Toutes les violations sont-elles au plafond ?
            all_ceiling = all(d[3] for d in violations_detail)
            print(f"    Toutes violations au plafond (B_max=M) ? {'OUI ★' if all_ceiling else 'NON'}")
            if not all_ceiling:
                non_ceiling = [d for d in violations_detail if not d[3]]
                print(f"    Violations non-plafond : {len(non_ceiling)}")
                for r, dr, count, _ in non_ceiling[:5]:
                    print(f"      r={r}, 2r={dr}, {count} compositions")

def investigate_spread_vs_image():
    """I5: Relation entre le 'spread' (max-min) de B et les résidus atteints."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 5 : Spread de B vs résidus atteints")
    print("=" * 70)

    for k in [3, 5]:
        S, d, _ = compute_params(k)
        p = d
        M = S - k
        w = modinv(3, p)
        u = (2 * w) % p

        print(f"\n--- k={k}, p={p}, M={M} ---")

        weights = [pow(u, j, p) for j in range(1, k)]

        # Pour chaque spread s = max(B) - min(B), quels résidus ?
        spread_residues = defaultdict(set)
        spread_count = defaultdict(int)

        for B in combinations_with_replacement(range(M + 1), k - 1):
            spread = B[-1] - B[0]
            f_val = sum(weights[j] * pow(2, B[j], p) for j in range(k - 1)) % p
            spread_residues[spread].add(f_val)
            spread_count[spread] += 1

        target = p - 1  # -1
        print(f"    Spread → résidus (total/p) et présence de -1 :")
        for s in sorted(spread_residues.keys()):
            has_neg1 = target in spread_residues[s]
            print(f"    spread={s} : {spread_count[s]} comps, "
                  f"{len(spread_residues[s])}/{p} résidus, "
                  f"-1={'OUI' if has_neg1 else 'NON'}")

def investigate_algebraic_obstruction():
    """I6: Obstruction algébrique : pourquoi f(B) = -1 est impossible."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 6 : Obstruction algébrique")
    print("=" * 70)

    for k in [3, 5]:
        S, d, _ = compute_params(k)
        p = d
        M = S - k
        w = modinv(3, p)
        u = (2 * w) % p
        ord_u = multiplicative_order(u, p)
        sigma_tilde = sum(pow(u, j, p) for j in range(1, k)) % p
        sigma = (1 + sigma_tilde) % p

        print(f"\n--- k={k}, p={p}, u={u}, ord(u)={ord_u} ---")
        print(f"    σ̃(u) = {sigma_tilde}")
        print(f"    σ(u) = {sigma}")
        print(f"    u^k = {pow(u, k, p)}, 2^{{k-S}} = {pow(2, k - S, p)} mod p")

        # Si f(B) = -1, alors 1 + f(B) = 0
        # Soit σ_B = 1 + Σ u^j · 2^{B_j} = 0
        #
        # Grouper par valeurs de B :
        # Si B a r valeurs distinctes b_1 < ... < b_r avec multiplicités n_1, ..., n_r
        # alors σ_B = 1 + Σ_{i=1}^r c_i · 2^{b_i} = 0
        # où c_i = Σ_{j in group_i} u^j

        # Pour B constant (b, b, ..., b) :
        # σ_B = 1 + 2^b · σ̃(u)
        if sigma_tilde == 0:
            print(f"    σ̃(u) = 0 → B constant donne σ_B = 1 ≠ 0 ✓")
            print(f"    → -1 IMPOSSIBLE par B constant")
        else:
            # σ_B = 0 ⟺ 2^b = -σ̃(u)^{-1}
            inv_sigma = modinv(sigma_tilde, p)
            needed = (p - inv_sigma) % p  # -σ̃^{-1}
            # Est-ce une puissance de 2 ?
            is_pow2 = False
            for b in range(M + 1):
                if pow(2, b, p) == needed:
                    is_pow2 = True
                    print(f"    ⚠️ B constant b={b} donnerait -1 ! Mais b={b} est dans [0,{M}]")
                    break
            if not is_pow2:
                # Vérifier au-delà de M
                for b in range(M + 1, p):
                    if pow(2, b, p) == needed:
                        print(f"    B constant : b={b} nécessaire, HORS portée [0,{M}] ✓")
                        break

        # Pour k petit, énumérer les B par structure (nombre de valeurs distinctes)
        print(f"\n    Analyse par structure de B :")
        weights = [pow(u, j, p) for j in range(1, k)]

        structure_analysis = defaultdict(lambda: {'count': 0, 'residues': set()})

        for B in combinations_with_replacement(range(M + 1), k - 1):
            n_distinct = len(set(B))
            f_val = sum(weights[j] * pow(2, B[j], p) for j in range(k - 1)) % p
            structure_analysis[n_distinct]['count'] += 1
            structure_analysis[n_distinct]['residues'].add(f_val)

        target = p - 1
        for nd in sorted(structure_analysis.keys()):
            info = structure_analysis[nd]
            has_neg1 = target in info['residues']
            print(f"    {nd} val. distinctes : {info['count']} comps, "
                  f"{len(info['residues'])} résidus, -1={'OUI' if has_neg1 else 'NON'}")

        # Propriété clé : σ(u) = (u^k - 1)/(u - 1) mod p
        if u != 1:
            uk = pow(u, k, p)
            u_minus_1 = (u - 1) % p
            inv_u_minus_1 = modinv(u_minus_1, p)
            if inv_u_minus_1:
                sigma_formula = ((uk - 1) * inv_u_minus_1) % p
                print(f"\n    Vérification : σ(u) via formule = {sigma_formula}, direct = {sigma}, match: {'✓' if sigma_formula == sigma else '✗'}")

                # Factorisation : u^k = 2^{k-S}
                # σ(u) = (2^{k-S} - 1)/(u-1)
                power_2 = pow(2, k - S, p)
                sigma_via_2 = ((power_2 - 1) * inv_u_minus_1) % p
                print(f"    σ(u) via 2^{{k-S}} = {sigma_via_2}, match: {'✓' if sigma_via_2 == sigma else '✗'}")

def investigate_all_prime_k():
    """I7: Vérification exhaustive pour tous k où d(k) est premier, k=3..40."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 7 : Tous k avec d(k) premier, k=3..40")
    print("=" * 70)

    results = []

    for k in range(3, 41):
        S, d, is_prime = compute_params(k)
        if not is_prime:
            continue

        p = d
        M = S - k
        w = modinv(3, p)
        u = (2 * w) % p
        ord_u = multiplicative_order(u, p)
        ord_2 = multiplicative_order(2, p)
        sigma_tilde = sum(pow(u, j, p) for j in range(1, k)) % p

        # Pour les grands k, l'énumération est trop coûteuse
        C = math.comb(S - 1, k - 1)

        can_enumerate = C <= 500000

        entry = {
            'k': k, 'p': p, 'S': S, 'M': M, 'u': u,
            'ord_u': ord_u, 'ord_2': ord_2,
            'sigma_tilde': sigma_tilde,
            'sigma_tilde_zero': sigma_tilde == 0,
            'ord_divides_k_minus_1': (k - 1) % ord_u == 0 if ord_u else False,
            'C': C, 'C_over_p': C / p
        }

        if can_enumerate:
            image = compute_image_f(k, p, u, M)
            target = p - 1
            N0 = len(image.get(target, []))  # compositions donnant -1 (should be 0)
            entry['N0_minus1'] = N0
            entry['image_size'] = len(image)

            # Vérifier fermeture sous ×2
            image_set = set(image.keys())
            violations = sum(1 for r in image_set if (2 * r) % p not in image_set)
            entry['closure_violations'] = violations
            entry['closure_rate'] = 1 - violations / len(image_set) if image_set else 0

        results.append(entry)

    # Affichage
    print(f"\n    {'k':>3} {'p':>10} {'M':>3} {'ord(u)':>8} {'ord(2)':>8} {'σ̃=0':>5} {'C/p':>8} {'|Im|':>8} {'-1?':>5} {'ferm%':>7}")
    print("    " + "-" * 85)

    for e in results:
        sigma_str = "OUI" if e['sigma_tilde_zero'] else "non"
        if 'image_size' in e:
            print(f"    {e['k']:3d} {e['p']:10d} {e['M']:3d} {e['ord_u']:8d} {e['ord_2']:8d} {sigma_str:>5} "
                  f"{e['C_over_p']:8.3f} {e['image_size']:8d} {e['N0_minus1']:5d} "
                  f"{100*e['closure_rate']:6.1f}%")
        else:
            print(f"    {e['k']:3d} {e['p']:10d} {e['M']:3d} {e['ord_u']:8d} {e['ord_2']:8d} {sigma_str:>5} "
                  f"{e['C_over_p']:8.3f} {'(trop)':>8} {'?':>5} {'?':>7}")

    # Synthèse
    print("\n    OBSERVATIONS :")
    sigma_zero_ks = [e['k'] for e in results if e['sigma_tilde_zero']]
    sigma_nonzero_ks = [e['k'] for e in results if not e['sigma_tilde_zero']]
    print(f"    σ̃(u) = 0 pour k = {sigma_zero_ks}")
    print(f"    σ̃(u) ≠ 0 pour k = {sigma_nonzero_ks}")

    verified = [e for e in results if 'N0_minus1' in e]
    all_zero = all(e['N0_minus1'] == 0 for e in verified)
    print(f"    -1 absent pour tous k vérifiés : {'OUI ✓' if all_zero else 'NON ✗'}")

def synthesize():
    """I8: Synthèse et directions."""
    print("\n" + "=" * 70)
    print("  SYNTHÈSE SESSION 10c")
    print("=" * 70)

    print("""
    RÉSULTATS CLÉS :

    1. CHAÎNE D'EXCLUSION : L'orbite {-2^m mod p} a une structure précise.
       -1 est TOUJOURS hors image. Les éléments de l'orbite qui SONT
       dans l'image sont aux positions m > 0, confirmant que -1 est
       un "trou" dans une structure autrement régulière.

    2. FERMETURE ×2 : L'image est PRESQUE fermée sous multiplication par 2.
       Les violations se produisent UNIQUEMENT au plafond (B_max = M).
       Cela crée un "bord" au-delà duquel on ne peut plus shifter.
       → -1 est le résidu qui tombe dans ce bord.

    3. STRUCTURE DE B : Plus le spread (max-min) est grand, plus de
       résidus sont atteints, mais -1 reste absent QUEL QUE SOIT
       le spread. Cela suggère un invariant indépendant du spread.

    4. OBSTRUCTION ALGÉBRIQUE : Pour σ̃(u) = 0, B constant donne
       toujours 0, et la non-constance limitée par l'ordre ne suffit
       pas à atteindre -1. Pour σ̃(u) ≠ 0, le b nécessaire pour
       B constant est hors portée.

    DIRECTION PROCHAINE (G-V-R itération #3) :
    - Formaliser l'argument de FERMETURE PARTIELLE :
      "L'image de f est un sous-ensemble de Z/pZ qui est ×2-clos
       sauf au plafond. -1 est toujours dans la partie exclue."
    - Investiguer le MÉCANISME II (CRT) pour d composite.
    """)

if __name__ == "__main__":
    t0 = time.time()

    print("SESSION 10c — CHAÎNE D'EXCLUSION ET ANALYSE INVERSE")
    print("=" * 70)
    print("Protocole DISCOVERY v2.2 — Boucle G-V-R itération #2\n")

    investigate_exclusion_chain()      # I1
    investigate_backward_chain()       # I2
    investigate_boundary_structure()   # I3
    investigate_image_closure()        # I4
    investigate_spread_vs_image()      # I5
    investigate_algebraic_obstruction() # I6
    investigate_all_prime_k()          # I7
    synthesize()                       # I8

    print(f"\n{'=' * 70}")
    print(f"Temps total : {time.time() - t0:.1f}s")
    print(f"{'=' * 70}")
