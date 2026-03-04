#!/usr/bin/env python3
"""
SESSION 10e — FILTRATION Im_0 ⊂ Im_1 ⊂ ... ⊂ Im_M
=====================================================
Protocole DISCOVERY v2.2 — Boucle G-V-R itération #4

HYPOTHÈSE : L'image de f grandit couche par couche (Im_m := image avec B_j ∈ [0,m]).
À chaque couche, -1 reste exclu. Le mécanisme est :
  - Im_{m+1} ⊇ 2 · Im_m (par shift)
  - Les NOUVEAUX éléments de Im_{m+1} \ 2·Im_m sont structurellement contraints
  - -1 ne peut jamais entrer car il faudrait -1/2 dans la couche précédente
    SANS être au plafond, mais c'est impossible.

CRITÈRE DE SUCCÈS : Trouver un invariant qui se préserve à chaque couche
et qui implique -1 ∉ Im_m pour tout m.
"""

import math
from itertools import combinations_with_replacement
from collections import defaultdict
import time

def compute_params(k):
    S = math.ceil(k * math.log2(3))
    d = 2**S - 3**k
    return S, d

def modinv(a, m):
    g, x, _ = extended_gcd(a % m, m)
    if g != 1:
        return None
    return x % m

def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x

def multiplicative_order(a, n):
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

def compute_image_by_layer(k, p, u, M):
    """Calcule Im_m pour chaque m de 0 à M."""
    weights = [pow(u, j, p) for j in range(1, k)]

    layers = {}  # m → set of residues in Im_m
    layer_new = {}  # m → NEW residues added at layer m (not in Im_{m-1})

    for m in range(M + 1):
        im_m = set()
        for B in combinations_with_replacement(range(m + 1), k - 1):
            f_val = sum(weights[j] * pow(2, B[j], p) for j in range(k - 1)) % p
            im_m.add(f_val)

        layers[m] = im_m
        if m == 0:
            layer_new[m] = im_m.copy()
        else:
            layer_new[m] = im_m - layers[m - 1]

    return layers, layer_new

def investigate_filtration_growth():
    """I1: Croissance de la filtration couche par couche."""
    print("=" * 70)
    print("  INVESTIGATION 1 : Croissance Im_0 ⊂ Im_1 ⊂ ... ⊂ Im_M")
    print("=" * 70)

    for k in [3, 5, 4, 13]:
        S, d = compute_params(k)
        if d < 2:
            continue
        # Vérifier primalité simplement
        p = d
        M = S - k
        w = modinv(3, p)
        if w is None:
            continue
        u = (2 * w) % p
        ord_u = multiplicative_order(u, p)
        sigma_tilde = sum(pow(u, j, p) for j in range(1, k)) % p

        print(f"\n--- k={k}, p={p}, u={u}, M={M}, σ̃(u)={sigma_tilde} ---")

        layers, layer_new = compute_image_by_layer(k, p, u, M)
        target = p - 1  # -1

        print(f"    {'m':>3} | {'|Im_m|':>8} | {'Nouveaux':>8} | {'via ×2':>8} | {'Vrais nouveaux':>14} | {'-1 ?':>5}")
        print(f"    {'---':>3}-+-{'--------':>8}-+-{'--------':>8}-+-{'--------':>8}-+-{'--------------':>14}-+-{'-----':>5}")

        for m in range(M + 1):
            size = len(layers[m])
            new = len(layer_new[m])

            # Combien de nouveaux viennent du shift ×2 de Im_{m-1} ?
            if m > 0:
                shifted = {(2 * r) % p for r in layers[m - 1]}
                from_shift = len(layer_new[m] & shifted)
                truly_new = len(layer_new[m] - shifted)
            else:
                from_shift = 0
                truly_new = new

            has_neg1 = target in layers[m]
            print(f"    {m:3d} | {size:8d} | {new:8d} | {from_shift:8d} | {truly_new:14d} | {'OUI' if has_neg1 else 'NON':>5}")

        # Vérifier l'inclusion ×2
        print(f"\n    Vérification 2·Im_m ⊂ Im_{m+1} :")
        for m in range(M):
            shifted = {(2 * r) % p for r in layers[m]}
            contained = shifted.issubset(layers[m + 1])
            missing = shifted - layers[m + 1]
            print(f"    2·Im_{m} ⊂ Im_{m+1} : {'✓' if contained else f'✗ ({len(missing)} manquants)'}")

def investigate_neg1_orbit_in_filtration():
    """I2: Position de -1 et son orbite dans la filtration."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 2 : Orbite de -1 dans la filtration")
    print("=" * 70)

    for k in [3, 5]:
        S, d = compute_params(k)
        p = d
        M = S - k
        w = modinv(3, p)
        u = (2 * w) % p
        inv2 = modinv(2, p)

        print(f"\n--- k={k}, p={p}, M={M} ---")

        layers, layer_new = compute_image_by_layer(k, p, u, M)
        target = p - 1  # -1

        # Backward chain : -1, -1/2, -1/4, ...
        print(f"    Backward chain -2^{{-m}} et première apparition dans la filtration :")
        r = target
        for step in range(M + 3):
            # Chercher la première couche m où r apparaît
            first_layer = None
            for m in range(M + 1):
                if r in layers[m]:
                    first_layer = m
                    break

            if first_layer is not None:
                print(f"    -2^{{-{step}}} = {r:>6} : première apparition à m={first_layer}")
            else:
                print(f"    -2^{{-{step}}} = {r:>6} : JAMAIS dans Im_M ★")

            r = (r * inv2) % p

def investigate_sigma_tilde_chain():
    """I3: La chaîne σ̃(u)·2^m et sa relation avec l'exclusion de -1."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 3 : Chaîne σ̃(u)·2^m dans la filtration")
    print("=" * 70)

    for k in [3, 5, 4]:
        S, d = compute_params(k)
        p = d
        M = S - k
        w = modinv(3, p)
        u = (2 * w) % p
        sigma_tilde = sum(pow(u, j, p) for j in range(1, k)) % p

        print(f"\n--- k={k}, p={p}, M={M}, σ̃(u)={sigma_tilde} ---")

        layers, _ = compute_image_by_layer(k, p, u, M)
        target = p - 1

        # Les séquences constantes B=(b,...,b) donnent f = 2^b · σ̃(u)
        print(f"    Valeurs f(b,...,b) = 2^b · σ̃(u) :")
        constant_values = []
        for b in range(M + 1):
            val = (pow(2, b, p) * sigma_tilde) % p
            constant_values.append(val)
            print(f"    b={b}: f = {val} (dans Im_{b})")

        # La chaîne des constantes : σ̃, 2σ̃, 4σ̃, ..., 2^M·σ̃
        # Quand σ̃ = 0 : toutes les constantes donnent 0
        # Quand σ̃ ≠ 0 : chaîne de M+1 éléments dans l'orbite de σ̃ sous ×2

        # Condition nécessaire pour -1 dans Im
        # Si -1 ∈ Im_M, par backward chain : -2^{-M} ∈ Im_0
        # Im_0 = {f(b,...,b) : b∈{0}} = {σ̃(u)}
        # Donc condition nécessaire : σ̃(u) = -2^{-M} = -(2^M)^{-1} mod p

        needed = (p - modinv(pow(2, M, p), p)) % p if sigma_tilde != 0 else None
        print(f"\n    Condition backward : σ̃(u) devrait être {needed} pour que -1 puisse être dans Im")
        print(f"    σ̃(u) = {sigma_tilde}")
        print(f"    Match ? {'OUI ⚠️' if sigma_tilde == needed else 'NON ✓'}")

        # MAIS attention : la backward chain est nécessaire SEULEMENT si l'exclusion
        # se propage parfaitement. En réalité, les "vrais nouveaux" à chaque couche
        # peuvent introduire des résidus qui ne viennent pas du shift.

        # Vérification directe : à chaque couche m, -1 est-il dans
        # l'ensemble des "vrais nouveaux" (pas du shift) ?
        print(f"\n    -1 dans les 'vrais nouveaux' de chaque couche :")
        for m in range(M + 1):
            if m == 0:
                truly_new = layers[0]
            else:
                shifted = {(2 * r) % p for r in layers[m - 1]}
                truly_new = layers[m] - layers[m - 1] - shifted
                # Attention: c'est layer_new - shifted
                layer_new_m = layers[m] - layers[m - 1]
                truly_new = layer_new_m - shifted

            has_neg1 = target in truly_new
            print(f"    m={m}: {len(truly_new)} vrais nouveaux, -1 présent ? {'OUI ⚠️' if has_neg1 else 'NON ✓'}")

def investigate_minimal_B_for_residue():
    """I4: Pour chaque résidu, quel est le B minimal (en spread) qui l'atteint ?"""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 4 : Couche minimale pour chaque résidu")
    print("=" * 70)

    for k in [3, 5]:
        S, d = compute_params(k)
        p = d
        M = S - k
        w = modinv(3, p)
        u = (2 * w) % p

        print(f"\n--- k={k}, p={p}, M={M} ---")

        layers, _ = compute_image_by_layer(k, p, u, M)
        target = p - 1

        # Pour chaque résidu, trouver la première couche
        first_appearance = {}
        for m in range(M + 1):
            for r in layers[m]:
                if r not in first_appearance:
                    first_appearance[r] = m

        print(f"    Distribution des premières apparitions :")
        by_layer = defaultdict(list)
        for r, m in first_appearance.items():
            by_layer[m].append(r)

        for m in sorted(by_layer.keys()):
            residues = sorted(by_layer[m])
            print(f"    Couche {m}: {len(residues)} résidus")
            # -1 est-il parmi eux ?
            if target in residues:
                print(f"      ★ -1 = {target} apparaît ici !")

        if target not in first_appearance:
            print(f"    ★★★ -1 = {target} n'apparaît dans AUCUNE couche !")

        # Vérification : résidus qui n'apparaissent jamais
        never = set(range(p)) - set(first_appearance.keys())
        print(f"    Résidus JAMAIS atteints : {sorted(never)}")

def investigate_inductive_argument():
    """I5: Tentative d'argument inductif sur les couches."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 5 : Argument inductif sur les couches")
    print("=" * 70)

    for k in [3, 5]:
        S, d = compute_params(k)
        p = d
        M = S - k
        w = modinv(3, p)
        u = (2 * w) % p
        sigma_tilde = sum(pow(u, j, p) for j in range(1, k)) % p
        inv2 = modinv(2, p)

        print(f"\n--- k={k}, p={p}, M={M}, σ̃={sigma_tilde} ---")

        layers, layer_new = compute_image_by_layer(k, p, u, M)
        target = p - 1

        # L'argument inductif :
        # Base : Im_0 = {σ̃(u)}, -1 ∉ Im_0 car σ̃(u) ≠ -1
        # Étape : Si -1 ∉ Im_m, montrer -1 ∉ Im_{m+1}
        #
        # Im_{m+1} = Im_m ∪ {f(B) : B dans [0,m+1], max(B) = m+1}
        #          = Im_m ∪ (2·Im_m) ∪ {vrais nouveaux}
        #
        # Pour -1 ∈ Im_{m+1} \ Im_m, il faudrait :
        #   (a) -1 ∈ 2·Im_m, i.e., -1/2 ∈ Im_m
        #       MAIS par hypothèse d'induction, on ne sait pas si -1/2 ∈ Im_m
        #   (b) -1 est un "vrai nouveau" (pas du shift)

        # Le problème : on ne peut pas juste traquer -1, il faut aussi traquer -1/2, -1/4, etc.

        # Définir EXCLU_m = orbite de -1 sous ÷2 qui doit être hors Im_m
        # Pour que l'induction marche :
        # Exclu_0 = {-1, -1/2, -1/4, ..., -2^{-M}} (toute la backward chain)
        # À chaque couche, on "libère" le plus grand élément de la chaîne

        print(f"\n    Backward chain et couches critiques :")
        chain = []
        r = target
        for step in range(M + 1):
            chain.append(r)
            r = (r * inv2) % p

        # La chaîne est : -1, -1/2, -1/4, ..., -2^{-M}
        # Pour que -1 ∉ Im_M, il faut (par backward chain) :
        #   -2^{-m} ∉ Im_{M-m} pour m = 0, 1, ..., M
        # En particulier :
        #   -2^{-M} ∉ Im_0

        print(f"    Chaîne backward : {chain}")
        print(f"    Im_0 = {layers[0]}")
        print(f"    -2^{{-M}} = {chain[M]} ∈ Im_0 ? {'OUI ⚠️' if chain[M] in layers[0] else 'NON ✓'}")

        # Vérifier toute la chaîne
        all_excluded = True
        for m in range(M + 1):
            residue = chain[m]
            layer = M - m
            in_layer = residue in layers[layer]
            print(f"    -2^{{-{m}}} = {residue:>6} ∉ Im_{layer} ? {'OUI (exclu) ✓' if not in_layer else 'NON (présent) ⚠️'}")
            if in_layer:
                all_excluded = False

        if all_excluded:
            print(f"    ★★★ Toute la backward chain est exclue ! Argument inductif POSSIBLE.")
        else:
            print(f"    ⚠️ La backward chain n'est PAS entièrement exclue → besoin d'analyse plus fine.")

def investigate_truly_new_structure():
    """I6: Structure des 'vrais nouveaux' à chaque couche."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 6 : D'où viennent les 'vrais nouveaux' ?")
    print("=" * 70)

    for k in [3, 5]:
        S, d = compute_params(k)
        p = d
        M = S - k
        w = modinv(3, p)
        u = (2 * w) % p
        weights = [pow(u, j, p) for j in range(1, k)]

        print(f"\n--- k={k}, p={p}, M={M} ---")

        # Pour chaque couche, les "vrais nouveaux" = B avec max(B) = m+1
        # et f(B) pas dans {2·Im_m}
        # Ces B ont au moins un composant = m+1, les autres dans [0, m+1]

        for m in range(M + 1):
            # Compositions avec max(B) = m (au moins un B_j = m)
            comps_with_max_m = []
            for B in combinations_with_replacement(range(m + 1), k - 1):
                if B[-1] == m:  # max(B) = m
                    f_val = sum(weights[j] * pow(2, B[j], p) for j in range(k - 1)) % p
                    comps_with_max_m.append((B, f_val))

            # Parmi ceux-ci, lesquels sont des "vrais nouveaux" (pas du shift) ?
            # Un comp est un shift si B' = (B_1-1, ..., B_{k-1}-1) est valide et max(B') = m-1
            truly_new_comps = []
            from_shift_comps = []
            for B, f_val in comps_with_max_m:
                if B[0] > 0:
                    # B-1 est valide, f(B) = 2·f(B-1), c'est un shift
                    from_shift_comps.append((B, f_val))
                else:
                    # B[0] = 0, ce n'est PAS un shift (car B-1 aurait B[0]=-1)
                    truly_new_comps.append((B, f_val))

            target = p - 1
            new_residues = set(f for B, f in truly_new_comps)
            has_neg1 = target in new_residues

            if truly_new_comps:
                print(f"    Couche m={m}: {len(truly_new_comps)} vrais nouveaux, "
                      f"{len(from_shift_comps)} shifts, -1 ? {'OUI ⚠️' if has_neg1 else 'NON ✓'}")
                if k <= 5 and len(truly_new_comps) <= 10:
                    for B, f_val in truly_new_comps:
                        print(f"      B={B}, f={f_val}")

def synthesize():
    """I7: Synthèse."""
    print("\n" + "=" * 70)
    print("  SYNTHÈSE SESSION 10e — FILTRATION")
    print("=" * 70)

    print("""
    STRUCTURE DE LA FILTRATION :

    Im_0 ⊂ Im_1 ⊂ ... ⊂ Im_M  où Im_m = {f(B) : B non-décr. dans [0,m]}

    1. Im_{m+1} ⊇ 2·Im_m (par shift B → B+1)
    2. Im_{m+1} = Im_m ∪ (shift) ∪ (vrais nouveaux)
    3. Les "vrais nouveaux" à couche m ont B_min = 0 et B_max = m
       (ne viennent pas d'un shift car B_min = 0)

    BACKWARD CHAIN :
    -1 ∉ Im_M nécessite -2^{-m} ∉ Im_{M-m} pour tout m = 0, ..., M
    En particulier : -2^{-M} ∉ Im_0 = {σ̃(u)}

    QUESTIONS OUVERTES :
    1. La backward chain est-elle entièrement exclue ? (Vérifié pour k=3,5)
    2. Pourquoi les "vrais nouveaux" n'incluent-ils jamais -1 ?
    3. Peut-on formuler un invariant inductif ?

    PISTE POUR L'INVARIANT :
    Hypothèse : E_m := {r ∈ Z/pZ : r ∉ Im_m ET 2r ∉ Im_m}
    Si -1 ∈ E_0 et E_m se propage correctement...
    Mais les vrais nouveaux compliquent cette propagation.

    LE PROBLÈME FONDAMENTAL : Les "vrais nouveaux" ne sont pas contrôlés
    par le shift. Ils viennent de compositions avec B_min = 0, et leur
    structure dépend des poids u^j de façon non triviale.
    """)

if __name__ == "__main__":
    t0 = time.time()

    print("SESSION 10e — FILTRATION Im_0 ⊂ Im_1 ⊂ ... ⊂ Im_M")
    print("=" * 70)
    print("Protocole DISCOVERY v2.2 — Boucle G-V-R itération #4\n")

    investigate_filtration_growth()         # I1
    investigate_neg1_orbit_in_filtration()  # I2
    investigate_sigma_tilde_chain()         # I3
    investigate_minimal_B_for_residue()     # I4
    investigate_inductive_argument()        # I5
    investigate_truly_new_structure()       # I6
    synthesize()                           # I7

    print(f"\n{'=' * 70}")
    print(f"Temps total : {time.time() - t0:.1f}s")
    print(f"{'=' * 70}")
