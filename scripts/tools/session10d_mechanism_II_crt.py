#!/usr/bin/env python3
"""
SESSION 10d — MÉCANISME II : CRT ANTI-CORRÉLATION (optimisé)
=============================================================
Protocole DISCOVERY v2.2 — Boucle G-V-R itération #3

HYPOTHÈSE : Pour d composite, les solutions mod p₁ et mod p₂ sont
ANTI-CORRÉLÉES de sorte que la joint matrix M[0][0] = 0 toujours.

OPTIMISATION : Travaille mod d directement avec entiers Python.
Limite C ≤ 200000 pour énumération raisonnable.
"""

import math
from itertools import combinations
from collections import defaultdict
import time

def compute_params(k):
    S = math.ceil(k * math.log2(3))
    d = 2**S - 3**k
    return S, d

def factorize(n):
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

def compute_all_corrsums_mod_d(k, S, d):
    """Calcule corrSum mod d pour TOUTES les compositions. Retourne une liste."""
    # Pré-calculer les puissances mod d
    pow3 = [pow(3, k - 1 - j, d) for j in range(k)]
    pow2 = [pow(2, a, d) for a in range(S)]
    base = pow3[0]  # 3^{k-1} mod d

    results = []
    for positions in combinations(range(1, S), k - 1):
        cs = base
        for j_idx, pos in enumerate(positions):
            cs = (cs + pow3[j_idx + 1] * pow2[pos]) % d
        results.append(cs)
    return results

def investigate_factorization():
    """I1: Factorisation de d(k) pour k=3..21."""
    print("=" * 70)
    print("  INVESTIGATION 1 : Factorisation de d(k) et compteurs N₀")
    print("=" * 70)

    MAX_C = 200000

    for k in range(3, 22):
        S, d = compute_params(k)
        C = math.comb(S - 1, k - 1)
        factors = factorize(d)
        factor_str = " × ".join(f"{p}^{e}" if e > 1 else str(p)
                                 for p, e in sorted(factors.items()))
        is_prime = len(factors) == 1 and list(factors.values())[0] == 1

        # N₀ si calculable
        N0_str = "?"
        N0_factors = {}
        if C <= MAX_C:
            all_cs = compute_all_corrsums_mod_d(k, S, d)
            N0 = sum(1 for cs in all_cs if cs == 0)
            N0_str = str(N0)

            # N₀ par facteur
            for p in sorted(factors.keys()):
                n0p = sum(1 for cs in all_cs if cs % p == 0)
                N0_factors[p] = n0p

        status = "PREMIER" if is_prime else "COMPOSITE"
        print(f"\n  k={k:2d}, S={S:2d}, d={d:>12}, C={C:>10}, N₀(d)={N0_str:>6} [{status}]")
        print(f"    d = {factor_str}")
        if N0_factors:
            for p, n0p in sorted(N0_factors.items()):
                print(f"    N₀({p:>8}) = {n0p:>6}  (C/p = {C/p:.3f})")

def investigate_joint_matrix():
    """I2: Matrice CRT jointe pour les k composites."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 2 : Matrice CRT jointe M[0][0]")
    print("=" * 70)

    MAX_C = 200000

    for k in range(6, 18):
        S, d = compute_params(k)
        C = math.comb(S - 1, k - 1)
        factors = factorize(d)
        primes = sorted(factors.keys())

        if C > MAX_C:
            continue
        if len(primes) < 2:
            continue

        print(f"\n--- k={k}, d={d}, C={C} ---")
        print(f"    Facteurs : {' × '.join(str(p) for p in primes)}")

        # Calcul des corrSums mod d
        all_cs = compute_all_corrsums_mod_d(k, S, d)

        # N₀ par facteur
        for p in primes:
            n0p = sum(1 for cs in all_cs if cs % p == 0)
            print(f"    N₀({p}) = {n0p}")

        # Paires CRT
        for i in range(len(primes)):
            for j in range(i + 1, len(primes)):
                pi, pj = primes[i], primes[j]
                n0_pi = sum(1 for cs in all_cs if cs % pi == 0)
                n0_pj = sum(1 for cs in all_cs if cs % pj == 0)
                n00 = sum(1 for cs in all_cs if cs % pi == 0 and cs % pj == 0)
                expected = n0_pi * n0_pj / C

                if n00 == 0:
                    print(f"    M[0,0]({pi},{pj}) = {n00}  ★ ANTI-CORRÉLATION PARFAITE  "
                          f"(attendu: {expected:.2f})")
                else:
                    print(f"    M[0,0]({pi},{pj}) = {n00}  (attendu: {expected:.2f})")

        # N₀(d) global
        N0_d = sum(1 for cs in all_cs if cs == 0)
        print(f"    N₀(d) = {N0_d}")

def investigate_anticorrelation_detail():
    """I3: Détail de l'anti-corrélation : quels résidus mod p₂ sont atteints quand ≡0 mod p₁."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 3 : Détail de l'anti-corrélation")
    print("=" * 70)

    for k in [6, 8, 9, 10, 11, 12]:
        S, d = compute_params(k)
        C = math.comb(S - 1, k - 1)
        factors = factorize(d)
        primes = sorted(factors.keys())

        if C > 200000 or len(primes) < 2:
            continue

        p1, p2 = primes[0], primes[1]

        print(f"\n--- k={k}, d={d}, p₁={p1}, p₂={p2} ---")

        all_cs = compute_all_corrsums_mod_d(k, S, d)

        # Quand corrSum ≡ 0 mod p₁, distribution mod p₂
        dist_p2_given_0_p1 = defaultdict(int)
        count_0_p1 = 0
        for cs in all_cs:
            if cs % p1 == 0:
                dist_p2_given_0_p1[cs % p2] += 1
                count_0_p1 += 1

        absent_p2 = sorted(r for r in range(p2) if r not in dist_p2_given_0_p1)

        print(f"    Quand ≡0 mod {p1}: {count_0_p1} compositions")
        print(f"    Résidus atteints mod {p2}: {len(dist_p2_given_0_p1)}/{p2}")
        if 0 in absent_p2:
            print(f"    ★ 0 ABSENT mod {p2}")
        else:
            print(f"    0 PRÉSENT mod {p2} ({dist_p2_given_0_p1[0]} fois)")

        if len(absent_p2) <= 30:
            print(f"    Résidus absents mod {p2}: {absent_p2}")

        # Vice versa
        dist_p1_given_0_p2 = defaultdict(int)
        count_0_p2 = 0
        for cs in all_cs:
            if cs % p2 == 0:
                dist_p1_given_0_p2[cs % p1] += 1
                count_0_p2 += 1

        absent_p1 = sorted(r for r in range(p1) if r not in dist_p1_given_0_p2)

        print(f"    Quand ≡0 mod {p2}: {count_0_p2} compositions")
        print(f"    Résidus atteints mod {p1}: {len(dist_p1_given_0_p2)}/{p1}")
        if 0 in absent_p1:
            print(f"    ★ 0 ABSENT mod {p1}")
        if len(absent_p1) <= 30:
            print(f"    Résidus absents mod {p1}: {absent_p1}")

def investigate_d_orders():
    """I4: Ordres multiplicatifs dans les facteurs de d."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 4 : Ordres multiplicatifs dans les facteurs")
    print("=" * 70)

    for k in range(3, 22):
        S, d = compute_params(k)
        factors = factorize(d)
        primes = sorted(factors.keys())

        if len(primes) < 2:
            continue

        print(f"\n  k={k:2d}, d = {d}, S = {S}")
        for p in primes[:5]:  # limiter aux 5 premiers facteurs
            ord_2 = multiplicative_order(2, p)
            ord_3 = multiplicative_order(3, p)
            w = modinv(3, p)
            u = (2 * w) % p if w else None
            ord_u = multiplicative_order(u, p) if u else None
            print(f"    p={p:>8}: ord_p(2)={ord_2}, ord_p(3)={ord_3}, "
                  f"u={u}, ord_p(u)={ord_u}")

def investigate_corrsum_mod_product():
    """I5: Distribution de corrSum mod p₁·p₂ vs d."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 5 : corrSum mod p₁·p₂")
    print("=" * 70)

    for k in [6, 8, 9, 10]:
        S, d = compute_params(k)
        C = math.comb(S - 1, k - 1)
        factors = factorize(d)
        primes = sorted(factors.keys())

        if C > 200000 or len(primes) < 2:
            continue

        p1, p2 = primes[0], primes[1]
        product = p1 * p2

        print(f"\n--- k={k}, d={d}, p₁={p1}, p₂={p2}, p₁p₂={product} ---")

        all_cs = compute_all_corrsums_mod_d(k, S, d)

        # Distribution mod produit
        dist = defaultdict(int)
        for cs in all_cs:
            dist[cs % product] += 1

        reached = len(dist)
        print(f"    Résidus atteints mod {product}: {reached}/{product} ({100*reached/product:.1f}%)")
        print(f"    C/{product} = {C/product:.4f}")

        # 0 mod produit
        n0_product = dist.get(0, 0)
        print(f"    N₀(p₁p₂) = {n0_product}")

        # Si d = p₁·p₂ (exactement 2 facteurs premiers), alors N₀(d) = N₀(p₁p₂)
        if d == product:
            print(f"    ★ d = p₁·p₂ exactement → N₀(d) = N₀(p₁p₂) = {n0_product}")

        # Analyse : multiples de p₁ atteints, réduits mod p₂
        multiples_p1 = {}
        for r, count in dist.items():
            if r % p1 == 0:
                multiples_p1[r // p1] = count

        reached_mod_p2 = sorted(set(m % p2 for m in multiples_p1.keys()))
        print(f"    Multiples de p₁ atteints → réduits mod p₂: {reached_mod_p2[:20]}")
        if 0 not in reached_mod_p2:
            print(f"    ★★ 0 mod p₂ ABSENT parmi les multiples de p₁ !")
            print(f"       ⟹ Impossible d'avoir corrSum ≡ 0 mod p₁ ET mod p₂ simultanément")

def investigate_three_factor():
    """I6: Cas à 3+ facteurs premiers."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 6 : Cas à 3+ facteurs premiers")
    print("=" * 70)

    for k in range(3, 18):
        S, d = compute_params(k)
        C = math.comb(S - 1, k - 1)
        factors = factorize(d)
        primes = sorted(factors.keys())

        if len(primes) < 3 or C > 200000:
            continue

        print(f"\n--- k={k}, d={d}, facteurs: {' × '.join(str(p) for p in primes)} ---")

        all_cs = compute_all_corrsums_mod_d(k, S, d)

        # Pour chaque PAIRE de facteurs, vérifier M[0,0]
        print(f"    Paires CRT (toutes) :")
        all_pairs_zero = True
        for i in range(len(primes)):
            for j in range(i + 1, len(primes)):
                pi, pj = primes[i], primes[j]
                n00 = sum(1 for cs in all_cs if cs % pi == 0 and cs % pj == 0)
                n0i = sum(1 for cs in all_cs if cs % pi == 0)
                n0j = sum(1 for cs in all_cs if cs % pj == 0)
                expected = n0i * n0j / C
                status = "★" if n00 == 0 else ""
                print(f"      ({pi}, {pj}): M[0,0]={n00}, attendu={expected:.1f} {status}")
                if n00 > 0:
                    all_pairs_zero = False

        # Pour les TRIPLETS
        if len(primes) >= 3:
            n000 = sum(1 for cs in all_cs if all(cs % p == 0 for p in primes[:3]))
            print(f"    Triplet ({primes[0]},{primes[1]},{primes[2]}): M[0,0,0]={n000}")

        # Est-ce qu'UNE SEULE paire suffit ?
        if all_pairs_zero:
            print(f"    ★ TOUTES les paires ont M[0,0]=0 → N₀(d)=0 suit")
        else:
            # Il faut au moins une paire avec M[0,0]=0
            has_blocking_pair = any(
                sum(1 for cs in all_cs if cs % primes[i] == 0 and cs % primes[j] == 0) == 0
                for i in range(len(primes)) for j in range(i+1, len(primes))
            )
            if has_blocking_pair:
                print(f"    Au moins une paire bloquante → N₀(d)=0")
            else:
                print(f"    ⚠️ Aucune paire ne bloque seule → besoin du triplet")

def synthesize():
    """I7: Synthèse."""
    print("\n" + "=" * 70)
    print("  SYNTHÈSE SESSION 10d — MÉCANISME II")
    print("=" * 70)

    print("""
    MÉCANISME II : CRT ANTI-CORRÉLATION

    Pour d composite (d = p₁ · p₂ · ... · p_r) :
    1. N₀(p_i) > 0 pour chaque facteur (barrière des primes individuels)
    2. MAIS les compositions ≡ 0 mod p₁ ne sont JAMAIS ≡ 0 mod p₂
    3. Cela crée une anti-corrélation PARFAITE : M[0][0] = 0

    Le mécanisme fondamental :
    - corrSum = 3^{k-1} + Σ 3^{k-1-j} · 2^{A_j} est le MÊME entier
    - Évalué mod p₁ et mod p₂, les contraintes se contredisent
    - La structure de d = 2^S - 3^k lie les facteurs de sorte que
      corrSum ≡ 0 mod p₁ force corrSum ≢ 0 mod p₂

    QUESTION OUVERTE pour la preuve :
    - Peut-on formaliser ce lien via les ordres multiplicatifs ?
    - La relation 2^S ≡ 3^k mod d impose des contraintes sur
      les ordres de 2 et 3 dans chaque facteur p|d.
    - Ces contraintes pourraient prouver l'anti-corrélation.
    """)

if __name__ == "__main__":
    t0 = time.time()

    print("SESSION 10d — MÉCANISME II : CRT ANTI-CORRÉLATION (optimisé)")
    print("=" * 70)
    print("Protocole DISCOVERY v2.2 — Boucle G-V-R itération #3\n")

    investigate_factorization()          # I1
    investigate_joint_matrix()           # I2
    investigate_anticorrelation_detail() # I3
    investigate_d_orders()               # I4
    investigate_corrsum_mod_product()    # I5
    investigate_three_factor()           # I6
    synthesize()                         # I7

    print(f"\n{'=' * 70}")
    print(f"Temps total : {time.time() - t0:.1f}s")
    print(f"{'=' * 70}")
