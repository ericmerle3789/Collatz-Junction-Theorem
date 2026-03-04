#!/usr/bin/env python3
"""
SESSION 10e4 — VERS LA PREUVE UNIVERSELLE (cas σ̃=0)
=====================================================
Protocole DISCOVERY v2.2 — Boucle G-V-R itération #5

THÉORÈMES PROUVÉS :
  T1 : u^k = 2^{-M} mod p (identité universelle)
  T2 : σ̃(u) = 0 ⟹ u = 2^{-M} mod p
  T3 : σ̃(u) = 0 ⟹ (k-1)M ≡ 0 mod ord_2(p)

OBJECTIF : Prouver que f(B) ≠ -1 pour B ∈ [0,M]^{k-1} non-décr,
en utilisant T2, pour le cas σ̃=0.

f(B) = Σ_{j=1}^{k-1} 2^{B_j - jM} mod p

STRATÉGIE : Montrer que la somme Σ 2^{E_j} (E_j dans bandes disjointes)
ne peut pas atteindre -1 mod p pour les contraintes données.
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

def is_prime(n):
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True

def investigate_all_sigma0_cases():
    """I1: Trouver TOUS les k avec σ̃(u) = 0 et d premier."""
    print("=" * 70)
    print("  INVESTIGATION 1 : Tous les k avec σ̃(u) = 0 et d premier")
    print("=" * 70)

    sigma0_cases = []
    for k in range(2, 50):
        S, d = compute_params(k)
        if d < 2 or not is_prime(d):
            continue
        w = modinv(3, d)
        if w is None:
            continue
        u = (2 * w) % d
        sigma_tilde = sum(pow(u, j, d) for j in range(1, k)) % d
        ord_u = multiplicative_order(u, d)
        ord_2 = multiplicative_order(2, d)
        M = S - k

        if sigma_tilde == 0:
            sigma0_cases.append(k)
            print(f"  k={k:>3}: p={d:>12}, M={M:>3}, ord(u)={ord_u:>8}, ord(2)={ord_2:>8}, "
                  f"u=2^{{-M}}={modinv(pow(2, M, d), d)}, u={u}, "
                  f"MATCH={'✓' if u == modinv(pow(2, M, d), d) else '✗'}, "
                  f"(k-1)M={((k-1)*M)}, ord₂|? {'✓' if ((k-1)*M) % ord_2 == 0 else '✗'}")
        else:
            # Non-σ̃=0 mais d premier
            print(f"  k={k:>3}: p={d:>12}, M={M:>3}, σ̃={sigma_tilde:>8} ≠ 0")

    print(f"\n  Cas σ̃=0 avec d premier : k = {sigma0_cases}")

def investigate_integer_lift():
    """I2: Relèvement dans Z — la somme Σ 2^{E_j} dans Z, pas juste mod p."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 2 : Relèvement dans Z")
    print("=" * 70)

    # L'idée : f(B) = Σ 2^{B_j - jM} mod p
    # Dans Z (pas mod p) : F(B) = Σ 2^{B_j} / 2^{jM} = (1/2^M) Σ (2^{B_j} / 2^{(j-1)M})
    # Ou plus simplement : Σ u^j · 2^{B_j} dans Z est un entier
    # dont le résidu mod p est f(B)
    #
    # Dans Z, le corrSum = Σ 3^{k-1-j} · 2^{A_j}
    # avec A_j = B_j + j, le corrSum est un entier positif
    # corrSum ≡ 0 mod d ⟺ corrSum = n₀ · d pour un entier n₀
    #
    # La somme corrSum = Σ 3^{k-1-j} · 2^{B_j+j} est POSITIVE
    # et bornée : corrSum ≤ k · 3^{k-1} · 2^{S-1}
    # corrSum ≥ k · 2^0 · 3^0 = k (minimum quand tous B_j = 0, j minimal)
    #
    # Pour corrSum ≡ 0 mod d, on a besoin corrSum = n₀ · d
    # Le plus petit multiple positif de d est d lui-même
    # Donc corrSum ≥ d

    for k in [3, 5]:
        S, d = compute_params(k)
        p = d
        M = S - k

        # Bornes exactes sur corrSum
        # B_j ∈ [0, M], A_j = B_j + j ∈ [j, j+M]
        # corrSum = Σ_{j=0}^{k-1} 3^{k-1-j} · 2^{A_j}
        # Minimum : A_j = j pour tout j (B_j = 0)
        corrSum_min = sum(pow(3, k-1-j) * pow(2, j) for j in range(k))
        # Maximum : A_j = j + M pour tout j (B_j = M)
        corrSum_max = sum(pow(3, k-1-j) * pow(2, j + M) for j in range(k))

        print(f"\n--- k={k}, d={d}, M={M} ---")
        print(f"  corrSum min (B=0) = {corrSum_min}")
        print(f"  corrSum max (B=M) = {corrSum_max}")
        print(f"  d = {d}")
        print(f"  corrSum_min / d = {corrSum_min / d:.4f}")
        print(f"  corrSum_max / d = {corrSum_max / d:.4f}")

        # Multiples de d dans [corrSum_min, corrSum_max]
        n_min = corrSum_min // d + (1 if corrSum_min % d != 0 else 0)
        n_max = corrSum_max // d
        print(f"  Multiples de d dans [min, max] : n ∈ [{n_min}, {n_max}]")
        print(f"  Nombre de multiples : {n_max - n_min + 1}")

        # Le corrSum pour B constant = (b,...,b)
        for b in range(M + 1):
            cs = sum(pow(3, k-1-j) * pow(2, b+j) for j in range(k))
            n0 = cs / d
            print(f"  B={b}: corrSum={cs}, corrSum/d={n0:.6f}, ≡ {cs % d} mod d")

        # La valeur critique : corrSum = 0 mod d
        # i.e., corrSum = n · d pour un entier n
        # La question est : existe-t-il un B valide tel que corrSum divise d ?

        # Vérifions : corrSum mod d pour TOUS les B valides
        print(f"\n  Distribution corrSum mod d :")
        weights_A = [pow(3, k-1-j) for j in range(k)]
        residues = defaultdict(int)
        for B in combinations_with_replacement(range(M + 1), k):
            cs_mod = sum(weights_A[j] * pow(2, B[j] + j) for j in range(k)) % d
            residues[cs_mod] += 1

        print(f"  {len(residues)} résidus distincts sur {d}")
        print(f"  résidu 0 : {residues.get(0, 0)} compositions")
        if residues.get(0, 0) == 0:
            print(f"  ★★★ N₀(d) = 0 CONFIRMÉ par calcul direct dans Z")

        # La valeur de corrSum_min mod d
        print(f"  corrSum_min mod d = {corrSum_min % d}")
        # Si corrSum_min > d et corrSum_min mod d ≠ 0, le plus petit
        # corrSum divisible par d est ceil(corrSum_min/d) * d

        # INSIGHT : corrSum = 3^k (la valeur du cycle de Collatz)
        # Pour n₀ ≠ 0, il faudrait corrSum = n₀ · d + 3^k ... non
        # Actually: corrSum = n₀ · d + 3^k est l'équation de Steiner
        # n₀ · d = corrSum - 3^k
        print(f"\n  Équation de Steiner : n₀ · d = corrSum - 3^k")
        print(f"  3^k = {3**k}")
        print(f"  corrSum_min - 3^k = {corrSum_min - 3**k}")
        print(f"  (corrSum_min - 3^k) / d = {(corrSum_min - 3**k) / d:.6f}")
        print(f"  (corrSum_max - 3^k) / d = {(corrSum_max - 3**k) / d:.6f}")

def investigate_gauss_sum_approach():
    """I3: Approche par sommes de Gauss."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 3 : Sommes de Gauss et comptage de solutions")
    print("=" * 70)

    # Le nombre de solutions de f(B) = r mod p pour r donné est :
    # N_r = (1/p) Σ_{t=0}^{p-1} ω^{-tr} Π_{j=1}^{k-1} Σ_{b=0}^{M} ω^{t·u^j·2^b}
    #
    # où ω = e^{2πi/p} est une racine primitive p-ème
    #
    # Pour r = -1 : N_{-1} = (1/p) Σ_t ω^t Π_j Σ_b ω^{t·u^j·2^b}
    #
    # Le terme t=0 contribue (M+1)^{k-1} / p (la contribution "aléatoire")
    # Les termes t≠0 sont des oscillations liées aux sommes de Gauss
    #
    # Si les sommes sont "petites" (bornées par √p ou similaire),
    # alors N_{-1} ≈ (M+1)^{k-1} / p + O(erreur)
    # et N_{-1} = 0 signifie que l'erreur domine

    for k in [3, 5, 4]:
        S, d = compute_params(k)
        p = d
        if not is_prime(p):
            continue
        M = S - k
        w = modinv(3, p)
        u = (2 * w) % p
        ord_2 = multiplicative_order(2, p)

        # Le nombre total de compositions non-décr dans [0,M]^{k-1}
        # = C(M+k-1, k-1) (étoiles et barres)
        from math import comb
        total_comps = comb(M + k - 1, k - 1)

        # Le "terme moyen" = total_comps / p
        mean = total_comps / p

        print(f"\n--- k={k}, p={p}, M={M} ---")
        print(f"  Total compositions non-décr : C({M}+{k-1},{k-1}) = {total_comps}")
        print(f"  Terme moyen par résidu : {total_comps}/{p} = {mean:.4f}")

        # N_{-1} = 0 signifie un écart de -mean par rapport à la moyenne
        # L'écart relatif = mean / sqrt(mean) = sqrt(mean)
        # Si mean < 1, il est "facile" d'avoir N_{-1} = 0
        print(f"  mean < 1 ? {'OUI (N₀=0 naturel)' if mean < 1 else f'NON ({mean:.2f} > 1)'}")

        # Calculons les sommes exponentielles partielles pour t=1
        # S_j(t) = Σ_{b=0}^M ω^{t·u^j·2^b} (somme de Gauss partielle)
        # En fait, calculons juste |S_j(1)| pour voir si les sommes sont petites

        # Approximation : pour u^j·2^b parcourant les résidus mod p,
        # la somme est essentiellement une somme de Gauss tronquée
        # |S_j(t)| ≤ min(M+1, √p · log p) typiquement

        print(f"  √p = {math.sqrt(p):.2f}")
        print(f"  M+1 = {M+1}")
        print(f"  M+1 < √p ? {'OUI' if M+1 < math.sqrt(p) else 'NON'}")

        # Pour k=3 : M+1=3, √5≈2.2, M+1 > √p. Mais p est petit.
        # Pour k=5 : M+1=4, √13≈3.6, M+1 > √p. Similaire.
        # Pour k=4 : M+1=4, √47≈6.9, M+1 < √p.

def investigate_recentered_sum():
    """I4: Analyse de la somme recentrée Σ 2^{E_j} = -1 (cas σ̃=0)."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 4 : Somme recentrée (σ̃=0 uniquement)")
    print("=" * 70)

    for k in [3, 5]:
        S, d = compute_params(k)
        p = d
        M = S - k
        ord_2 = multiplicative_order(2, p)

        print(f"\n--- k={k}, p={p}, M={M}, ord₂={ord_2} ---")
        print(f"  (k-1)·M = {(k-1)*M}, ord₂ = {ord_2}")
        print(f"  (k-1)·M / ord₂ = {(k-1)*M / ord_2}")

        # L'équation recentrée : Σ_{j=1}^{k-1} 2^{E_j} = -1 mod p
        # avec E_j ∈ [-jM, -(j-1)M], non-décroissant
        # Wait, actually E_j = B_j - jM, and B is non-decreasing,
        # but the non-decreasing constraint on B gives:
        # B_j ≤ B_{j+1} ⟹ E_j + jM ≤ E_{j+1} + (j+1)M ⟹ E_{j+1} ≥ E_j - M

        # Dans Z/ord₂Z, les exposants E_j sont bien définis mod ord₂
        # Chaque E_j parcourt M+1 valeurs consécutives (mod ord₂)
        # La bande j couvre [(-jM) mod ord₂, (-(j-1)M) mod ord₂]

        # Puisque (k-1)M = ord₂, les bandes couvrent EXACTEMENT une période complète
        # Bande 1 : [-M, 0] ≡ [ord₂-M, ord₂] ≡ [ord₂-M, 0]
        # Bande 2 : [-2M, -M] ≡ [ord₂-2M, ord₂-M]
        # ...
        # Bande k-1 : [-(k-1)M, -(k-2)M] ≡ [0, M]

        bands = []
        for j in range(1, k):
            lo = (-j * M) % ord_2
            hi = (-(j-1) * M) % ord_2
            values = set()
            for b in range(M + 1):
                e = (b - j * M) % ord_2
                values.add(e)
            bands.append(values)
            print(f"  Bande j={j}: E_j ∈ [{-j*M}, {-(j-1)*M}] ≡ mod {ord_2}: {sorted(values)}")

        # Les bandes partitionnent {0, 1, ..., ord₂-1} !
        all_values = set()
        for band in bands:
            all_values |= band
        print(f"  Union des bandes : {sorted(all_values)}")
        print(f"  Partition de [0,{ord_2-1}] ? {'OUI ★★★' if all_values == set(range(ord_2)) else 'NON'}")

        # Chaque bande a M+1 éléments sauf possiblement aux frontières
        # Avec (k-1)(M+1) = (k-1)M + k-1 = ord₂ + k-1 > ord₂
        # Donc il y a des chevauchements aux frontières !
        print(f"  Nombre total de valeurs dans les bandes : {sum(len(b) for b in bands)}")
        print(f"  Avec chevauchement : {sum(len(b) for b in bands) - ord_2}")

        # Les valeurs 2^{E_j} pour chaque bande
        band_images = []
        for j, band in enumerate(bands, 1):
            img = set()
            for e in band:
                img.add(pow(2, e, p))
            band_images.append(img)
            print(f"  Im(2^{{E_{j}}}) = {sorted(img)}")

        # Le produit cartésien des band_images donne toutes les sommes possibles
        # Pour k=3, c'est 2 bandes → somme de 2 éléments
        if k == 3:
            sums = set()
            for a in band_images[0]:
                for b in band_images[1]:
                    sums.add((a + b) % p)
            print(f"\n  Toutes les sommes possibles : {sorted(sums)}")
            print(f"  -1 = {p-1} dans les sommes ? {'OUI ⚠️' if p-1 in sums else 'NON ✓'}")
            # ATTENTION : cette approche IGNORE la contrainte de non-décroissance
            # Sans contrainte, -1 PEUT être atteint !

        # Maintenant avec la contrainte B non-décr (i.e., E_{j+1} ≥ E_j - M)
        if k == 3:
            constrained_sums = set()
            for e1 in range(-M, 1):  # E_1 ∈ [-M, 0]
                for e2 in range(-2*M, -M + 1):  # E_2 ∈ [-2M, -M]
                    if e2 >= e1 - M:  # Contrainte de non-décr
                        s = (pow(2, e1 % ord_2, p) + pow(2, e2 % ord_2, p)) % p
                        constrained_sums.add(s)
            print(f"  Sommes avec contrainte non-décr : {sorted(constrained_sums)}")
            print(f"  -1 dans les sommes contraintes ? {'OUI ⚠️' if p-1 in constrained_sums else 'NON ✓'}")

        if k == 5:
            constrained_sums = set()
            count = 0
            for e1 in range(-M, 1):
                for e2 in range(-2*M, -M + 1):
                    if e2 < e1 - M:
                        continue
                    for e3 in range(-3*M, -2*M + 1):
                        if e3 < e2 - M:
                            continue
                        for e4 in range(-4*M, -3*M + 1):
                            if e4 < e3 - M:
                                continue
                            s = (pow(2, e1 % ord_2, p) + pow(2, e2 % ord_2, p) +
                                 pow(2, e3 % ord_2, p) + pow(2, e4 % ord_2, p)) % p
                            constrained_sums.add(s)
                            count += 1
            print(f"  Sommes contraintes ({count} combinaisons) : {sorted(constrained_sums)}")
            print(f"  -1 dans les sommes contraintes ? {'OUI ⚠️' if p-1 in constrained_sums else 'NON ✓'}")

def investigate_boundary_analysis():
    """I5: Analyse des frontières de bandes — pourquoi -1 est bloqué."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 5 : Frontières de bandes et blocage")
    print("=" * 70)

    # Pour k=3, p=5, ord₂=4, M=2 :
    # Bande 1 : E_1 ∈ {-2,-1,0} ≡ {2,3,0} mod 4, images 2^E₁ = {4,3,1}
    # Bande 2 : E_2 ∈ {-4,-3,-2} ≡ {0,1,2} mod 4, images 2^E₂ = {1,2,4}
    # Contrainte : E_2 ≥ E_1 - M = E_1 - 2

    k = 3
    S, d = compute_params(k)
    p = d
    M = S - k
    ord_2 = multiplicative_order(2, p)

    print(f"\n--- k=3, p=5, M=2, ord₂=4 ---")
    print(f"  Table complète des sommes 2^E₁ + 2^E₂ avec contrainte :")
    print(f"  {'E₁':>4} | {'E₂':>4} | {'E₁ mod 4':>8} | {'E₂ mod 4':>8} | {'2^E₁':>5} | {'2^E₂':>5} | {'Σ':>3} | {'=-1?':>5} | {'E₂≥E₁-M?':>9}")

    for e1 in range(-M, 1):
        for e2 in range(-2*M, -M + 1):
            e1_mod = e1 % ord_2
            e2_mod = e2 % ord_2
            val1 = pow(2, e1_mod, p)
            val2 = pow(2, e2_mod, p)
            s = (val1 + val2) % p
            constraint = e2 >= e1 - M
            is_target = s == p - 1
            marker = "★" if is_target else ""
            c_marker = "✓" if constraint else "✗"
            print(f"  {e1:4d} | {e2:4d} | {e1_mod:8d} | {e2_mod:8d} | {val1:5d} | {val2:5d} | {s:3d} | {'OUI '+marker if is_target else 'NON':>5} | {c_marker:>9}")

    # La clé : les combinaisons donnant -1=4 sont celles avec contrainte VIOLÉE
    print(f"\n  ★ Combinaisons donnant somme = -1 = 4 mod 5 :")
    for e1 in range(-M, 1):
        for e2 in range(-2*M, -M + 1):
            val1 = pow(2, e1 % ord_2, p)
            val2 = pow(2, e2 % ord_2, p)
            s = (val1 + val2) % p
            if s == p - 1:
                constraint = e2 >= e1 - M
                print(f"    E₁={e1}, E₂={e2}: 2^{e1%ord_2}+2^{e2%ord_2} = {val1}+{val2} = {s}")
                print(f"    Contrainte E₂ ≥ E₁-M = {e1-M} : {'SATISFAITE' if constraint else 'VIOLÉE ← BLOQUÉE!'}")

    # Pour k=5 aussi
    print(f"\n--- k=5, p=13, M=3, ord₂=12 ---")
    k = 5
    S, d = compute_params(k)
    p = d
    M = S - k
    ord_2 = multiplicative_order(2, p)

    count_target = 0
    count_target_valid = 0
    for e1 in range(-M, 1):
        for e2 in range(-2*M, -M + 1):
            if e2 < e1 - M:
                continue
            for e3 in range(-3*M, -2*M + 1):
                if e3 < e2 - M:
                    continue
                for e4 in range(-4*M, -3*M + 1):
                    if e4 < e3 - M:
                        continue
                    s = sum(pow(2, e % ord_2, p) for e in [e1,e2,e3,e4]) % p
                    if s == p - 1:
                        count_target += 1
                        # Correspondance avec B :
                        B = [e1+M, e2+2*M, e3+3*M, e4+4*M]
                        valid = all(0 <= b <= M for b in B) and all(B[i] <= B[i+1] for i in range(3))
                        if valid:
                            count_target_valid += 1
                            print(f"  ⚠️ VALIDE : E=({e1},{e2},{e3},{e4}), B={B}")

    print(f"  Solutions f=-1 avec contrainte non-décr : {count_target}")
    print(f"  Solutions f=-1 valides dans [0,M] : {count_target_valid}")
    if count_target_valid == 0 and count_target == 0:
        print(f"  ★★★ AUCUNE solution même sans restriction de range ! (dans la vue recentrée)")

def investigate_non_sigma0():
    """I6: Cas σ̃(u) ≠ 0 — structure différente."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 6 : Cas σ̃(u) ≠ 0 (k=4, p=47)")
    print("=" * 70)

    k = 4
    S, d = compute_params(k)
    p = d
    M = S - k
    w = modinv(3, p)
    u = (2 * w) % p
    ord_u = multiplicative_order(u, p)
    ord_2 = multiplicative_order(2, p)
    sigma_tilde = sum(pow(u, j, p) for j in range(1, k)) % p

    print(f"  k={k}, p={p}, M={M}, u={u}, ord(u)={ord_u}, ord(2)={ord_2}")
    print(f"  σ̃(u) = {sigma_tilde}")
    print(f"  u^{{k-1}} = {pow(u, k-1, p)} (≠ 1 car σ̃ ≠ 0)")

    # Pour σ̃ ≠ 0, u N'EST PAS 2^{-M}
    u_check = modinv(pow(2, M, p), p)
    print(f"  u = {u} vs 2^{{-M}} = {u_check} : u ≠ 2^{{-M}}")

    # Mais u^k = 2^{-M} est toujours vrai
    print(f"  u^k = {pow(u, k, p)}, 2^{{-M}} = {modinv(pow(2, M, p), p)}")
    print(f"  u^k = 2^{{-M}} : {'✓' if pow(u, k, p) == modinv(pow(2, M, p), p) else '✗'}")

    # La différence : u^{k-1} ≠ 1 signifie que les poids u^j ne sont PAS
    # des racines de l'unité. Ils parcourent un sous-groupe plus grand.

    # Les poids u, u², ..., u^{k-1} génèrent un sous-groupe de (Z/pZ)*
    # de taille = ord(u)
    weights = [pow(u, j, p) for j in range(1, k)]
    print(f"  Poids u^j : {weights}")
    print(f"  Sous-groupe ⟨u⟩ : taille {ord_u}")

    # Image de f dans [0,M]
    image_f = set()
    for B in combinations_with_replacement(range(M + 1), k - 1):
        fv = sum(weights[j] * pow(2, B[j], p) for j in range(k - 1)) % p
        image_f.add(fv)
    print(f"  |Im(f)| = {len(image_f)} sur {p}")
    print(f"  Ratio : {len(image_f)/p:.3f}")
    print(f"  -1 ∈ Im(f) ? {'OUI ⚠️' if p-1 in image_f else 'NON ✓'}")

    # Pour σ̃ ≠ 0, l'argument de débordement est PLUS FORT
    # (overflow = 4 au lieu de 1)
    # Intuition : u a un grand ordre multiplicatif, les poids u^j
    # "dispersent" les valeurs plus largement, et le nombre de
    # compositions dans [0,M] est trop petit pour couvrir les cibles

    # Nombre de compositions : C(M+k-2, k-2) = C(5,2) = 10 (non-décr avec max(B)=M possible)
    from math import comb
    n_comps = comb(M + k - 1, k - 1)
    print(f"  Compositions totales : C({M+k-1},{k-1}) = {n_comps}")
    print(f"  Ratio comps/p : {n_comps/p:.4f}")

    # Pour k=4 : 20 compositions, p=47. Environ 20/47 ≈ 0.43 du résidu.
    # En réalité |Im(f)| = 18 < 20 (certaines compositions donnent le même résidu)

def synthesize():
    """I7: Synthèse et état de la preuve."""
    print("\n" + "=" * 70)
    print("  SYNTHÈSE SESSION 10e4")
    print("=" * 70)

    print("""
    ARCHITECTURE DE LA PREUVE UNIVERSELLE :

    ═══════════════════════════════════════════════════════════
    CAS 1 : d(k) est PREMIER et σ̃(u) = 0
    ═══════════════════════════════════════════════════════════

    THÉORÈMES PROUVÉS :
    T1: u = 2^{-M} mod p
    T2: u^{k-1} = 1 mod p
    T3: (k-1)·M ≡ 0 mod ord₂(p)
    T4: f(B) = Σ 2^{B_j - jM} mod p

    CONJECTURE À PROUVER :
    C1: La somme Σ 2^{E_j} ≠ -1 mod p pour E_j dans les bandes
        disjointes [-jM, -(j-1)M] avec contrainte de non-décr.

    NOTE : Pour k=3 et k=5, les bandes couvrent EXACTEMENT
    une période de 2 mod p. La preuve devrait utiliser cette
    structure cyclotomique.

    ═══════════════════════════════════════════════════════════
    CAS 2 : d(k) est PREMIER et σ̃(u) ≠ 0
    ═══════════════════════════════════════════════════════════

    THÉORÈME : u^k = 2^{-M} mod p (toujours)
    OBSERVATION : |Im(f)| ≪ p (image très creuse)
    OBSERVATION : overflow ≥ 4 (vs 1 pour σ̃=0)

    L'image est creuse car :
    - M+1 ≪ ord₂(p) (peu de valeurs de 2^B distinctes)
    - Les poids u^j parcourent un grand sous-groupe
    - Résultat : les compositions ne couvrent qu'une fraction de Z/pZ

    PISTE : Borne combinatoire. Montrer |Im(f)| ≤ p - (M+1).
    Plus précisément : |Im(f)| ≤ C(M+k-1, k-1) < p pour tout k.

    ═══════════════════════════════════════════════════════════
    CAS 3 : d(k) est COMPOSITE
    ═══════════════════════════════════════════════════════════

    Mécanisme II : Anti-corrélation CRT.
    Vérifié computationnellement pour k=6,...,12.
    GAP : preuve formelle.

    ═══════════════════════════════════════════════════════════
    GAP PRINCIPAL : Prouver C1 (σ̃=0) et la borne combinatoire (σ̃≠0)
    pour TOUT k, sans énumération.
    ═══════════════════════════════════════════════════════════
    """)

if __name__ == "__main__":
    t0 = time.time()

    print("SESSION 10e4 — VERS LA PREUVE UNIVERSELLE")
    print("=" * 70)
    print("Protocole DISCOVERY v2.2 — Boucle G-V-R itération #5\n")

    investigate_all_sigma0_cases()     # I1
    investigate_integer_lift()          # I2
    investigate_gauss_sum_approach()    # I3
    investigate_recentered_sum()        # I4
    investigate_boundary_analysis()     # I5
    investigate_non_sigma0()            # I6
    synthesize()                        # I7

    print(f"\n{'=' * 70}")
    print(f"Temps total : {time.time() - t0:.1f}s")
    print(f"{'=' * 70}")
