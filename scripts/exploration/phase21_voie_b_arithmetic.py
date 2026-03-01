#!/usr/bin/env python3
"""phase21_voie_b_arithmetic.py — Voie B : Structure arithmétique exacte.

Objectif : Prouver l'Hypothèse H en exploitant les relations algébriques
fondamentales entre corrSum, d, et les puissances de 2 et 3.

IDEE CENTRALE :
  d = 2^S - 3^k  et  corrSum(A) = Σ 3^{k-1-i} · 2^{A_i}

  Posons ω = 2/3 dans Z/d. On a :
    3^k ≡ 2^S (mod d)
    ⟹ (2/3)^S ≡ 3^{S-k}/3^S = 3^{-k} (mod d)... non, plus direct :
    ⟹ 2 ≡ 3·ω (mod d) avec ω = 2·(3^{-1} mod d)

  corrSum(A) = 3^{k-1} · Σ (2/3)^{A_i - ... } ?

  Plus précisément, factorisons :
    corrSum(A) = 3^{k-1} · [2^{A_0} + (2/3)·2^{A_1} + ... + (2/3)^{k-1}·2^{A_{k-1}}]
              = 3^{k-1} · Σ_{j=0}^{k-1} (2/3)^j · 2^{A_j}
              = Σ 3^{k-1-j} · 2^{A_j}

  Posons r = 2 mod d (représentant dans Z/dZ).
  corrSum(A) mod d = Σ 3^{k-1-j} · r^{A_j} mod d

  La contrainte 2^S ≡ 3^k (mod d) donne r^S ≡ 3^k (mod d).

SECTIONS :
  S1. Ordre multiplicatif de 2 et 3 modulo d et ses facteurs
  S2. Structure du sous-groupe <2> dans (Z/dZ)*
  S3. Résidus interdits : structure de corrSum mod p pour chaque p|d
  S4. Borne de lacunarité : espacement minimal des puissances de 2
  S5. Argument d'imparité + valuation 2-adique
  S6. Analyse mod p pour petits p — borne de Weil empirique
  S7. Argument de counting : densité vs exclusion
  S8. Synthèse et construction formelle

Auteur : Eric Merle (assisté par Claude)
Date : 28 février 2026
"""

import math
import numpy as np
from itertools import combinations
from typing import List, Tuple, Dict, Set
from collections import Counter, defaultdict
import time

def compositions(S: int, k: int):
    """Génère toutes les compositions ordonnées A = (0, a₁, ..., a_{k-1})."""
    if k == 1:
        return [(0,)]
    return [(0,) + rest for rest in combinations(range(1, S), k - 1)]

def corrsum(A, k):
    return sum((3 ** (k - 1 - i)) * (2 ** a) for i, a in enumerate(A))

def corrsum_mod(A, k, m):
    """corrSum(A) mod m, calcul modular pour éviter les grands entiers."""
    result = 0
    for i, a in enumerate(A):
        result = (result + pow(3, k - 1 - i, m) * pow(2, a, m)) % m
    return result

def multiplicative_order(a, n):
    """Ordre de a dans (Z/nZ)*."""
    if math.gcd(a, n) > 1:
        return 0
    order, current = 1, a % n
    while current != 1:
        current = (current * a) % n
        order += 1
        if order > n:
            return 0
    return order

def distinct_prime_factors(n):
    factors = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            factors.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors

def full_factorization(n):
    """Retourne la factorisation complète [(p, e), ...]."""
    factors = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0:
                e += 1
                n //= d
            factors.append((d, e))
        d += 1
    if n > 1:
        factors.append((n, 1))
    return factors


# ═══════════════════════════════════════════════════════════════════════
# Section 1 : Ordres multiplicatifs de 2 et 3 modulo d
# ═══════════════════════════════════════════════════════════════════════

def orders_analysis():
    """Analyse les ordres multiplicatifs de 2 et 3 modulo d et chaque p|d.

    INTUITION : Si ord_d(2) est grand par rapport à k, les puissances 2^{A_j}
    sont "bien réparties" dans (Z/dZ)*, ce qui rend l'annulation accidentelle
    de corrSum mod d très improbable.
    """
    print(f"\n  {'k':>3} {'S':>3} {'d':>12} {'facteurs':>25} "
          f"{'ord_d(2)':>10} {'ord_d(3)':>10} {'S/ord':>8} {'k/ord3':>8}")
    print(f"  {'─'*3} {'─'*3} {'─'*12} {'─'*25} {'─'*10} {'─'*10} {'─'*8} {'─'*8}")

    results = []
    for k in range(3, 21):
        S = math.ceil(k * math.log2(3))
        d = (1 << S) - 3**k
        if d <= 0:
            continue

        facts = full_factorization(d)
        facts_str = '·'.join(f"{p}^{e}" if e > 1 else str(p) for p, e in facts)

        ord2 = multiplicative_order(2, d) if math.gcd(2, d) == 1 else 0
        ord3 = multiplicative_order(3, d) if math.gcd(3, d) == 1 else 0

        ratio_S = f"{S/ord2:.3f}" if ord2 > 0 else "∞"
        ratio_k = f"{k/ord3:.3f}" if ord3 > 0 else "∞"

        print(f"  {k:3d} {S:3d} {d:12,d} {facts_str:>25} "
              f"{ord2:10d} {ord3:10d} {ratio_S:>8} {ratio_k:>8}")

        results.append({
            'k': k, 'S': S, 'd': d,
            'ord2': ord2, 'ord3': ord3,
            'factors': facts
        })

    # Analyse des ordres modulo chaque premier
    print(f"\n  Ordres de 2 et 3 modulo chaque facteur premier p de d :")
    print(f"  {'k':>3} {'p':>8} {'ord_p(2)':>10} {'ord_p(3)':>10} {'S mod ord_p(2)':>16} {'k mod ord_p(3)':>16}")
    print(f"  {'─'*3} {'─'*8} {'─'*10} {'─'*10} {'─'*16} {'─'*16}")

    for r in results:
        k, S = r['k'], r['S']
        for p, e in r['factors']:
            o2 = multiplicative_order(2, p)
            o3 = multiplicative_order(3, p)
            Smod = S % o2 if o2 > 0 else "—"
            kmod = k % o3 if o3 > 0 else "—"
            print(f"  {k:3d} {p:8d} {o2:10d} {o3:10d} {str(Smod):>16} {str(kmod):>16}")

    return results


# ═══════════════════════════════════════════════════════════════════════
# Section 2 : Structure du sous-groupe engendré par les puissances de 2
# ═══════════════════════════════════════════════════════════════════════

def subgroup_structure(max_k=13):
    """Étudie le sous-groupe <2^0, 2^1, ..., 2^{S-1}> dans Z/pZ pour p|d.

    Les exposants A_j ∈ {0, 1, ..., S-1}. On regarde la structure de
    {2^a mod p : 0 ≤ a < S} dans Z/pZ.

    Si ord_p(2) | S, alors 2^S ≡ 1 mod p et les puissances cyclent exactement.
    Sinon, on n'a qu'un sous-ensemble strict du groupe cyclique <2>.
    """
    print(f"\n  Sous-groupes <2^a mod p> pour p|d(k), a ∈ [0, S-1] :")
    print(f"  {'k':>3} {'p':>8} {'ord_p(2)':>10} {'S':>4} "
          f"{'#pow2':>6} {'cosets':>8} {'covers_all':>12}")
    print(f"  {'─'*3} {'─'*8} {'─'*10} {'─'*4} {'─'*6} {'─'*8} {'─'*12}")

    for k in range(3, max_k + 1):
        S = math.ceil(k * math.log2(3))
        d = (1 << S) - 3**k
        if d <= 0:
            continue

        primes = distinct_prime_factors(d)
        for p in primes:
            if p > 100000:
                continue  # sauter les très grands premiers

            o2 = multiplicative_order(2, p)
            powers_mod_p = set(pow(2, a, p) for a in range(S))
            n_powers = len(powers_mod_p)
            n_cosets = S // o2 if o2 > 0 else 0
            remainder = S % o2 if o2 > 0 else S
            covers_all = (n_powers == min(o2, p - 1))

            print(f"  {k:3d} {p:8d} {o2:10d} {S:4d} "
                  f"{n_powers:6d} {n_cosets:8d}+{remainder} {str(covers_all):>12}")


# ═══════════════════════════════════════════════════════════════════════
# Section 3 : Distribution de corrSum mod p — résidus exclus
# ═══════════════════════════════════════════════════════════════════════

def residue_exclusion_analysis(max_k=13):
    """Pour chaque p|d(k), calcule la distribution exacte de corrSum mod p.

    Question clé : le résidu 0 est-il exclu ? Et si oui, quel est le "gap"
    entre la densité observée et la densité uniforme 1/p ?
    """
    print(f"\n  Distribution corrSum mod p — test d'exclusion du résidu 0 :")
    print(f"  {'k':>3} {'p':>8} {'C':>8} {'N₀(p)':>8} {'E[N₀]':>8} "
          f"{'T(0)/C':>10} {'max|T|/C':>10} {'0_EXCLU':>8}")
    print(f"  {'─'*3} {'─'*8} {'─'*8} {'─'*8} {'─'*8} {'─'*10} {'─'*10} {'─'*8}")

    all_results = []
    for k in range(3, max_k + 1):
        S = math.ceil(k * math.log2(3))
        d = (1 << S) - 3**k
        C = math.comb(S - 1, k - 1)

        if C > 200_000:
            continue

        comps = compositions(S, k)
        primes = distinct_prime_factors(d)

        for p in primes:
            if p > 100000:
                continue

            residues = [corrsum_mod(A, k, p) for A in comps]
            counter = Counter(residues)

            N0 = counter.get(0, 0)
            expected = C / p
            max_T = max(abs(counter.get(r, 0) - expected) for r in range(p))

            # Fourier-based max|T|/C
            T_values = {}
            for t in range(p):
                Tt = sum(1 for r in residues if r == t) - expected
                T_values[t] = Tt

            max_Tt_over_C = max(abs(v) for v in T_values.values()) / C

            print(f"  {k:3d} {p:8d} {C:8d} {N0:8d} {expected:8.1f} "
                  f"{T_values.get(0, 0)/C:10.6f} {max_Tt_over_C:10.6f} "
                  f"{'OUI' if N0 == 0 else 'NON':>8}")

            all_results.append({
                'k': k, 'p': p, 'C': C, 'N0': N0,
                'expected': expected, 'max_Tt_over_C': max_Tt_over_C,
                'T0_over_C': T_values.get(0, 0) / C
            })

    return all_results


# ═══════════════════════════════════════════════════════════════════════
# Section 4 : Borne de lacunarité — exploitation de la sparsité
# ═══════════════════════════════════════════════════════════════════════

def lacunarity_analysis(max_k=15):
    """Étudie la LACUNARITE de corrSum comme somme exponentielle.

    corrSum(A) = Σ 3^{k-1-j} · 2^{A_j} avec A_0 < A_1 < ... < A_{k-1}

    C'est une somme de k termes dans un espace de taille 2^S.
    Les termes sont EXPONENTIELLEMENT ESPACES (en puissances de 2).
    C'est une "somme lacunaire" au sens de Kac-Salem-Zygmund.

    Borne type Kac : pour une somme de k termes exponentiellement espacés,
    la fluctuation est d'ordre √k / √(S/k) ≈ k / √S.

    On compare avec la borne |T(t)|/C < 1/(p-1) nécessaire pour N₀ = 0.
    """
    print(f"\n  Analyse de lacunarité : comparaison des bornes :")
    print(f"  {'k':>3} {'S':>4} {'C':>10} {'d':>12} {'k/√S':>8} {'√k':>8} "
          f"{'C/d':>10} {'1/(p_min-1)':>12}")
    print(f"  {'─'*3} {'─'*4} {'─'*10} {'─'*12} {'─'*8} {'─'*8} {'─'*10} {'─'*12}")

    for k in range(3, max_k + 1):
        S = math.ceil(k * math.log2(3))
        d = (1 << S) - 3**k
        C = math.comb(S - 1, k - 1)

        primes = distinct_prime_factors(d)
        p_min = min(primes) if primes else d

        lacunarity_ratio = k / math.sqrt(S)
        sqrt_k = math.sqrt(k)
        C_over_d = C / d

        bound = 1 / (p_min - 1) if p_min > 1 else float('inf')

        print(f"  {k:3d} {S:4d} {C:10,d} {d:12,d} {lacunarity_ratio:8.4f} "
              f"{sqrt_k:8.4f} {C_over_d:10.6f} {bound:12.6f}")


# ═══════════════════════════════════════════════════════════════════════
# Section 5 : Argument d'imparité + congruences modulo petits nombres
# ═══════════════════════════════════════════════════════════════════════

def parity_and_small_moduli(max_k=13):
    """corrSum(A) est TOUJOURS impair (prouvé en S5 du script précédent).

    Conséquences :
    1. Si d est pair, corrSum ≢ 0 mod d (car d pair, corrSum impair)
       → Mais d = 2^S - 3^k est TOUJOURS IMPAIR (car 3^k est impair, 2^S est pair)
       → d est impair, donc l'argument d'imparité de corrSum ne suffit pas seul.

    2. Vérifions corrSum mod 2, 3, 4, 8, ... pour des exclusions structurelles.
    """
    print(f"\n  corrSum mod petits nombres — recherche de congruences structurelles :")

    for k in range(3, max_k + 1):
        S = math.ceil(k * math.log2(3))
        d = (1 << S) - 3**k
        C = math.comb(S - 1, k - 1)

        if C > 200_000:
            continue

        comps = compositions(S, k)

        print(f"\n  k = {k}, S = {S}, d = {d}")
        print(f"  d mod 2 = {d % 2}, d mod 3 = {d % 3}, d mod 4 = {d % 4}, "
              f"d mod 8 = {d % 8}, d mod 6 = {d % 6}")

        for m in [2, 3, 4, 6, 8, 12, 24]:
            residues = set(corrsum_mod(A, k, m) for A in comps)
            d_mod_m = d % m
            zero_possible = (0 in residues) if d_mod_m == 0 else (d_mod_m in residues or 0 in residues)

            # Ce qui nous intéresse : corrSum(A) ≡ 0 mod d
            # ⟹ corrSum(A) ≡ 0 mod gcd(d, m)
            g = math.gcd(d, m)
            residues_modg = set(corrsum_mod(A, k, g) for A in comps) if g > 1 else {0}
            excludes_0_modg = (0 not in residues_modg) if g > 1 else False

            print(f"    mod {m:2d}: résidus atteints = {sorted(residues)[:20]}{'...' if len(residues) > 20 else ''} "
                  f"| gcd(d,{m})={g}, 0 ∈ Im(mod {g}) : {'NON ★' if excludes_0_modg else 'oui'}")


# ═══════════════════════════════════════════════════════════════════════
# Section 6 : Borne de Weil empirique — max|T(t)|/(C/p) pour p|d
# ═══════════════════════════════════════════════════════════════════════

def weil_bound_empirical(max_k=13):
    """Calcule max_{t≠0} |T(t)|/√C pour chaque p|d et compare à √p.

    Borne de Weil standard pour les sommes exponentielles :
      |S(f, χ)| ≤ (deg f - 1) · √p

    Pour corrSum mod p, on a une somme de k termes. La "borne de Weil
    lacunaire" prédirait max|T(t)| ≈ √(k) · √(C/p).

    On vérifie si max|T(t)|/√C croît comme √p ou plus lentement.
    """
    print(f"\n  Borne de Weil empirique : max|T(t)|/√C vs √p :")
    print(f"  {'k':>3} {'p':>8} {'C':>8} {'max|T|':>10} {'max|T|/√C':>12} "
          f"{'√p':>8} {'ratio':>8} {'N₀':>5}")
    print(f"  {'─'*3} {'─'*8} {'─'*8} {'─'*10} {'─'*12} {'─'*8} {'─'*8} {'─'*5}")

    for k in range(3, max_k + 1):
        S = math.ceil(k * math.log2(3))
        d = (1 << S) - 3**k
        C = math.comb(S - 1, k - 1)

        if C > 200_000:
            continue

        comps = compositions(S, k)
        primes = distinct_prime_factors(d)

        for p in primes:
            if p > 50000:
                continue

            residues = [corrsum_mod(A, k, p) for A in comps]
            counter = Counter(residues)
            expected = C / p

            # T(t) = #{A : corrSum(A) ≡ t mod p} - C/p
            max_T = 0
            for t in range(p):
                Tt = abs(counter.get(t, 0) - expected)
                if Tt > max_T:
                    max_T = Tt

            N0 = counter.get(0, 0)
            sqrt_C = math.sqrt(C)
            sqrt_p = math.sqrt(p)
            ratio = (max_T / sqrt_C) / sqrt_p if sqrt_p > 0 else 0

            print(f"  {k:3d} {p:8d} {C:8d} {max_T:10.2f} "
                  f"{max_T/sqrt_C:12.4f} {sqrt_p:8.4f} {ratio:8.4f} {N0:5d}")


# ═══════════════════════════════════════════════════════════════════════
# Section 7 : Argument STRUCTURAL — la congruence 2^S ≡ 3^k mod d
# ═══════════════════════════════════════════════════════════════════════

def structural_congruence_argument(max_k=13):
    """Exploite la relation fondamentale 2^S = 3^k + d.

    CONSEQUENCE DIRECTE :
      corrSum(A) mod d = Σ 3^{k-1-j} · 2^{A_j} mod d

      Considérons la composition minimale A_min = (0, 1, ..., k-1).
      corrSum(A_min) = Σ 3^{k-1-j} · 2^j = (3^k - 2^k) / (3-2) = 3^k - 2^k

      Or d = 2^S - 3^k, donc :
      corrSum(A_min) mod d = (3^k - 2^k) mod (2^S - 3^k)
                           = (3^k - 2^k) mod d

      Puisque cs_min = 3^k - 2^k et on a montré cs_min > d pour k ≥ 3 :
      corrSum(A_min) mod d = (3^k - 2^k) - m·d pour un certain m ≥ 1.

      Plus précisément : m = ⌊(3^k - 2^k) / d⌋ et le résidu est cs_min - m·d.

    QUESTION : ce résidu est-il TOUJOURS > 0 ? Et pour toutes les autres
    compositions ?
    """
    print(f"\n  Résidu de corrSum(A_min) mod d — test de positivité stricte :")
    print(f"  {'k':>3} {'cs_min':>15} {'d':>15} {'m':>4} {'résidu':>12} "
          f"{'résidu/d':>10}")
    print(f"  {'─'*3} {'─'*15} {'─'*15} {'─'*4} {'─'*12} {'─'*10}")

    for k in range(3, 25):
        S = math.ceil(k * math.log2(3))
        d = (1 << S) - 3**k
        cs_min = 3**k - 2**k

        m = cs_min // d
        residue = cs_min % d

        print(f"  {k:3d} {cs_min:15,d} {d:15,d} {m:4d} {residue:12,d} "
              f"{residue/d:10.6f}")

    # Analyse plus fine : distribution de corrSum mod d
    print(f"\n  Distribution complète corrSum mod d pour petits k :")
    print(f"  {'k':>3} {'d':>10} {'min_res':>10} {'max_res':>10} {'#distinct':>10} "
          f"{'gap_near_0':>12} {'gap_near_d':>12}")
    print(f"  {'─'*3} {'─'*10} {'─'*10} {'─'*10} {'─'*10} {'─'*12} {'─'*12}")

    for k in range(3, 14):
        S = math.ceil(k * math.log2(3))
        d = (1 << S) - 3**k
        C = math.comb(S - 1, k - 1)

        if C > 200_000:
            comps = None
            continue
        else:
            comps = compositions(S, k)
            residues_mod_d = sorted(set(corrsum(A, k) % d for A in comps))

            min_res = residues_mod_d[0]
            max_res = residues_mod_d[-1]
            n_distinct = len(residues_mod_d)

            # Gap autour de 0 (et de d)
            gap_near_0 = min_res  # distance du plus petit résidu à 0
            gap_near_d = d - max_res  # distance du plus grand résidu à d

            print(f"  {k:3d} {d:10,d} {min_res:10,d} {max_res:10,d} {n_distinct:10,d} "
                  f"{gap_near_0:12,d} {gap_near_d:12,d}")


# ═══════════════════════════════════════════════════════════════════════
# Section 8 : Argument de LIFTING — pourquoi 0 est exclu de Im(corrSum mod d)
# ═══════════════════════════════════════════════════════════════════════

def lifting_argument(max_k=13):
    """L'argument central pour la preuve.

    THÈSE : corrSum(A) ≡ 0 mod d est impossible pour k ≥ 3 car :

    1. corrSum(A) = Σ 3^{k-1-j} · 2^{A_j} avec A strictement croissant
    2. Le plus petit terme est 3^{k-1} (quand A_0 = 0)
    3. Chaque terme supplémentaire ajoute au moins 3^{k-2}·2 = 2·3^{k-2}

    4. Posons f(A) = corrSum(A) / 3^{k-1} = Σ (2/3)^j · 2^{A_j-j} · (2/3)^{-A_j+j}
       ... Non, plus simplement :
       corrSum(A) = 3^{k-1} · [1 + Σ_{j=1}^{k-1} (2/3)^j · 2^{A_j}]

    5. OBSERVATION CLEE :
       corrSum(A) = 0 mod d  ⟹  corrSum(A) = m·d pour un entier m ≥ 1
       ⟹ Σ 3^{k-1-j}·2^{A_j} = m·(2^S - 3^k)
       ⟹ Σ 3^{k-1-j}·2^{A_j} + m·3^k = m·2^S
       ⟹ 3^{k-1}·(Σ (2/3)^{-j}·2^{A_j}/3^{k-1} + m·3) = m·2^S
       ... Reformulons :
       ⟹ Σ 3^{k-1-j}·2^{A_j} = m·2^S - m·3^k

    APPROCHE MODULAIRE :
    On étudie corrSum(A) mod p pour chaque p|d et on montre l'exclusion.
    """
    print(f"\n  Analyse de lifting : corrSum(A) = m·d ⟹ contraintes sur A :")

    for k in range(3, 14):
        S = math.ceil(k * math.log2(3))
        d = (1 << S) - 3**k
        C = math.comb(S - 1, k - 1)

        if C > 200_000:
            continue

        comps = compositions(S, k)

        # Pour chaque composition, calculer corrSum et le quotient m = corrSum / d
        # (arrondi si non divisible)
        m_values = []
        fractional_parts = []
        for A in comps:
            cs = corrsum(A, k)
            m = cs // d
            frac = (cs % d) / d
            m_values.append(m)
            fractional_parts.append(frac)

        m_min, m_max = min(m_values), max(m_values)
        frac_min = min(fractional_parts)
        frac_max = max(fractional_parts)

        # Le résidu 0 mod d correspond à frac = 0
        has_zero = 0.0 in fractional_parts
        # Plus précisément, vérifions exactement
        exact_zero = any(corrsum(A, k) % d == 0 for A in comps)

        print(f"\n  k={k}, S={S}, d={d:,d}, C={C:,d}")
        print(f"    m ∈ [{m_min}, {m_max}], #m_values = {m_max - m_min + 1}")
        print(f"    frac(corrSum/d) ∈ [{frac_min:.6f}, {frac_max:.6f}]")
        print(f"    corrSum ≡ 0 mod d : {'OUI ✗' if exact_zero else 'NON ✓ (H vérifié)'}")

        # Histogramme des parties fractionnaires
        if C <= 1000:
            hist, _ = np.histogram(fractional_parts, bins=20, range=(0, 1))
            density_str = ' '.join(f"{h:3d}" for h in hist)
            print(f"    Histogramme frac(corrSum/d) [20 bins] : {density_str}")
            # La densité autour de 0
            near_zero = sum(1 for f in fractional_parts if f < 0.05 or f > 0.95)
            print(f"    Résidus proches de 0 (|frac| < 0.05) : {near_zero} / {C} = {near_zero/C:.4f}")


# ═══════════════════════════════════════════════════════════════════════
# Section 9 : La piste des CHIFFRES EN BASE MIXTE
# ═══════════════════════════════════════════════════════════════════════

def mixed_base_analysis(max_k=13):
    """OBSERVATION CLEF : corrSum(A) peut être vu comme un nombre en base mixte.

    corrSum(A) = Σ_{j=0}^{k-1} 3^{k-1-j} · 2^{A_j}
              = 3^{k-1}·2^{A_0} + 3^{k-2}·2^{A_1} + ... + 3^0·2^{A_{k-1}}

    C'est un nombre avec des "chiffres" c_j = 2^{A_j} en "base" décroissante
    en puissances de 3.

    Pour corrSum(A) ≡ 0 mod d, on a besoin que :
    Σ 3^{k-1-j} · 2^{A_j} ≡ 0 mod (2^S - 3^k)

    Or 3^k ≡ 2^S mod d, donc 3 ≡ 2^{S/k} "approximativement" mod d.

    En fait, posons ρ = 2^S · 3^{-k} mod d. Alors ρ ≡ 1 mod d (par définition).
    Donc 2^S ≡ 3^k mod d.

    Conséquence :
    3 ≡ 2^S · 3^{-(k-1)} · 3^{-1} ... non, plus directement :
    3^{k-1-j} = 3^k · 3^{-(j+1)} ≡ 2^S · 3^{-(j+1)} mod d

    Donc corrSum(A) ≡ 2^S · Σ 3^{-(j+1)} · 2^{A_j} mod d
                     ≡ 2^S · Σ (2/3)^{A_j} · 3^{A_j-(j+1)} ... compliqué.

    Approche plus directe : écrire tout en puissances de 2 mod d.
    """
    print(f"\n  Analyse en puissances de 2 modulo d :")

    for k in range(3, min(max_k + 1, 14)):
        S = math.ceil(k * math.log2(3))
        d = (1 << S) - 3**k
        C = math.comb(S - 1, k - 1)

        if C > 200_000:
            continue

        # 3^j mod d en termes de puissances de 2 mod d
        # Comme 3^k ≡ 2^S mod d, on a 3 ≡ 2^S · (3^{k-1})^{-1} mod d
        # Mais c'est circulaire. Calculons directement.

        three_mod_d = 3 % d
        inv3 = pow(3, -1, d) if math.gcd(3, d) == 1 else None

        if inv3 is None:
            print(f"  k={k}: 3|d, skip")
            continue

        # Représentation : 3^{k-1-j} · 2^{A_j} mod d
        # = pow(3, k-1-j, d) * pow(2, A_j, d) mod d
        # On cherche quand Σ = 0 mod d.

        # Clé : la somme est une combinaison linéaire de pow(2, A_j, d)
        # avec des coefficients pow(3, k-1-j, d).
        # Les coefficients sont FIXES (dépendent de j, pas de A_j).
        # Les "variables" sont pow(2, A_j, d) pour A_j ∈ {j, j+1, ..., S-1}
        # (car A_0 = 0 et A strictement croissant, donc A_j ≥ j).

        print(f"\n  k={k}, S={S}, d={d:,d}, C={C:,d}")

        # Coefficients w_j = 3^{k-1-j} mod d
        coeffs = [pow(3, k - 1 - j, d) for j in range(k)]
        print(f"    Coefficients w_j = 3^(k-1-j) mod d : {coeffs}")

        # La somme est Σ w_j · 2^{A_j} mod d = 0
        # C'est un "subset-sum" pondéré dans Z/dZ !

        # Vérifions l'écart entre les puissances de 2 consécutives
        n_show = min(S, 20)
        pow2_diffs = [(pow(2, a+1, d) - pow(2, a, d)) % d for a in range(n_show)]
        print(f"    Diff 2^(a+1)-2^a mod d (a=0..{n_show-1}): {pow2_diffs}")

        # La structure clé : changer A_j → A_j + 1 modifie corrSum de
        # w_j · (2^{A_j+1} - 2^{A_j}) = w_j · 2^{A_j} mod d
        # C'est un DOUBLEMENT du terme j.


# ═══════════════════════════════════════════════════════════════════════
# Section 10 : SYNTHÈSE — Le véritable argument
# ═══════════════════════════════════════════════════════════════════════

def synthesis(max_k=13):
    """Synthèse de tous les arguments pour la preuve de H.

    ARCHITECTURE DE LA PREUVE (candidate) :

    Théorème (Hypothèse H) : Pour tout k ≥ 3, 0 ∉ Im(corrSum mod d(k)).

    Preuve :
    CAS 1 (k ≤ 68) : Vérification computationnelle directe (déjà fait).

    CAS 2 (k ≥ 69) : Argument asymptotique.

    Étape 1 : C/d < 0.024 pour k ≥ 69 (prouvé par borne Stirling).

    Étape 2 : Les résidus corrSum(A) mod d sont dans une bande
              [cs_min mod d, cs_max mod d] qui ne contient qu'une fraction
              C/d des classes de résidus de Z/dZ.

    Étape 3 (GAP) : Montrer que les résidus forment des "clusters" qui
              évitent systématiquement le voisinage de 0 mod d.

    On vérifie cette structure pour k ≤ 13 et on cherche le patron
    asymptotique.
    """
    print(f"\n  SYNTHÈSE — Structure des résidus corrSum mod d :")
    print(f"  {'='*70}")

    for k in range(3, max_k + 1):
        S = math.ceil(k * math.log2(3))
        d = (1 << S) - 3**k
        C = math.comb(S - 1, k - 1)

        if C > 200_000:
            continue

        comps = compositions(S, k)
        cs_values = [corrsum(A, k) for A in comps]
        residues = sorted([cs % d for cs in cs_values])
        n_distinct = len(set(residues))

        # Analyse des gaps
        gaps = []
        for i in range(len(residues) - 1):
            gaps.append(residues[i + 1] - residues[i])

        # Gap spécial : de max_res à d + min_res (gap circulaire passant par 0)
        circular_gap = (d - residues[-1]) + residues[0]
        gaps.append(circular_gap)

        avg_gap = d / n_distinct
        max_gap = max(gaps) if gaps else 0
        circular_rank = sorted(gaps, reverse=True).index(circular_gap) + 1 if gaps else 0

        # Le gap contenant 0 est toujours le gap circulaire
        gap_at_zero = circular_gap

        primes = distinct_prime_factors(d)
        facts_str = '×'.join(str(p) for p in primes)

        print(f"\n  k={k}, S={S}, d={d:,d} = {facts_str}")
        print(f"    C = {C:,d}, |Im| = {n_distinct:,d}, C/d = {C/d:.6f}")
        print(f"    Gap moyen = {avg_gap:.1f}, Max gap = {max_gap:,d}")
        print(f"    Gap contenant 0 = {gap_at_zero:,d} (rang {circular_rank}/{len(gaps)})")
        print(f"    Ratio gap_0 / gap_moyen = {gap_at_zero / avg_gap:.4f}")

        # Le gap circulaire est-il le plus grand ?
        is_max = (circular_gap == max_gap)
        print(f"    Gap_0 est le plus grand ? {'OUI ★' if is_max else 'NON'}")

        # Distribution des résidus dans les "déciles" de Z/dZ
        deciles = [0] * 10
        for r in residues:
            bucket = min(int(10 * r / d), 9)
            deciles[bucket] += 1
        decile_str = ' '.join(f"{x:4d}" for x in deciles)
        print(f"    Déciles (0-10% ... 90-100%) : {decile_str}")


# ═══════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════

def main():
    t0 = time.time()

    print("=" * 82)
    print("Phase 21g — Voie B : Structure Arithmétique Exacte")
    print("Programme Merle — Projet Collatz-Junction-Theorem")
    print("=" * 82)

    # S1 : Ordres multiplicatifs
    print(f"\n{'─'*82}")
    print(f"S1. Ordres multiplicatifs de 2 et 3 modulo d et ses facteurs")
    print(f"{'─'*82}")
    orders_analysis()

    # S2 : Sous-groupes
    print(f"\n{'─'*82}")
    print(f"S2. Structure du sous-groupe des puissances de 2 dans Z/pZ")
    print(f"{'─'*82}")
    subgroup_structure()

    # S3 : Distribution des résidus
    print(f"\n{'─'*82}")
    print(f"S3. Distribution de corrSum mod p — résidus exclus")
    print(f"{'─'*82}")
    residue_exclusion_analysis()

    # S4 : Lacunarité
    print(f"\n{'─'*82}")
    print(f"S4. Bornes de lacunarité")
    print(f"{'─'*82}")
    lacunarity_analysis()

    # S5 : Imparité et petits moduli
    print(f"\n{'─'*82}")
    print(f"S5. Argument d'imparité et congruences modulo petits nombres")
    print(f"{'─'*82}")
    parity_and_small_moduli()

    # S6 : Borne de Weil empirique
    print(f"\n{'─'*82}")
    print(f"S6. Borne de Weil empirique")
    print(f"{'─'*82}")
    weil_bound_empirical()

    # S7 : Congruence structurelle
    print(f"\n{'─'*82}")
    print(f"S7. Argument structurel — congruence 2^S ≡ 3^k mod d")
    print(f"{'─'*82}")
    structural_congruence_argument()

    # S8 : Lifting
    print(f"\n{'─'*82}")
    print(f"S8. Argument de lifting — corrSum(A) = m·d")
    print(f"{'─'*82}")
    lifting_argument()

    # S9 : Base mixte
    print(f"\n{'─'*82}")
    print(f"S9. Analyse en base mixte (puissances de 2 modulo d)")
    print(f"{'─'*82}")
    mixed_base_analysis()

    # S10 : Synthèse
    print(f"\n{'─'*82}")
    print(f"S10. SYNTHÈSE — Structure des résidus et architecture de la preuve")
    print(f"{'─'*82}")
    synthesis()

    elapsed = time.time() - t0
    print(f"\nTemps d'execution : {elapsed:.1f}s")
    print("=" * 82)

if __name__ == '__main__':
    main()
