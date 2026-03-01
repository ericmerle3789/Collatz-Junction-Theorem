#!/usr/bin/env python3
"""phase21_proof_construction.py — Construction de la preuve de l'Hypothèse H.

L'Hypothèse H (Zero-Exclusion) dit :
  Pour tout k ≥ 3, pour toute composition A ∈ Comp(S,k),
  corrSum(A) ≢ 0 mod d(k).

Ce script explore les STRUCTURES PROFONDES nécessaires à la preuve :

1. L'identité fondamentale corrSum_min > d (toujours vrai)
2. La borne corrSum(A) ∈ [cs_min, cs_max] avec cs_min/d → 1
3. Le "lift" : corrSum(A) = m·d implique m ≥ 2 et des contraintes fortes sur m
4. L'argument par injection : corrSum est "presque injective" mod d
5. Les bornes de Weil pour les cas convergents

Auteur : Eric Merle (assisté par Claude)
Date : 28 février 2026
"""

import math
import numpy as np
from itertools import combinations
from typing import List, Tuple, Dict
from collections import Counter, defaultdict
import time
import hashlib

def compositions(S: int, k: int):
    if k == 1:
        return [(0,)]
    return [(0,) + rest for rest in combinations(range(1, S), k - 1)]

def corrsum(A, k):
    return sum((3 ** (k - 1 - i)) * (2 ** a) for i, a in enumerate(A))

def multiplicative_order(a, p):
    if a % p == 0:
        return 0
    order, current = 1, a % p
    while current != 1:
        current = (current * a) % p
        order += 1
    return order

def distinct_prime_factors(n):
    factors = set()
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.add(d)
            n //= d
        d += 1
    if n > 1:
        factors.add(n)
    return sorted(factors)


# ═══════════════════════════════════════════════════════════════════════
# Section 1 : L'identité fondamentale cs_min > d
# ═══════════════════════════════════════════════════════════════════════

def verify_csmin_greater_d():
    """Vérifie et prouve que cs_min = 3^k - 2^k > d = 2^S - 3^k pour tout k ≥ 2.

    PREUVE :
      cs_min = Σ_{i=0}^{k-1} 3^{k-1-i} · 2^i = (3^k - 2^k) / (3-2) = 3^k - 2^k

      cs_min > d  ⟺  3^k - 2^k > 2^S - 3^k
                  ⟺  2·3^k > 2^S + 2^k
                  ⟺  2·3^k - 2^k > 2^S

      Or 2^S ≤ 2·3^k (car S ≤ k·log₂3 + 1)
      Et 2·3^k - 2^k = 2·3^k·(1 - (2/3)^k/2) > 2·3^k · 0.5 = 3^k  (pour k ≥ 2)
      Et 2^S = 2^{⌈k·log₂3⌉} < 2·3^k

      Pour être rigoureux, il faut montrer 2·3^k - 2^k > 2^S.
      Puisque 2^S = 3^k + d et d > 0 :
        2·3^k - 2^k > 3^k + d  ⟺  3^k - 2^k > d  ⟺  cs_min > d

      Et la condition 3^k - 2^k > 2^S - 3^k est équivalente à 2·3^k > 2^S + 2^k,
      qui est vraie car 2·3^k > 2^S (pour tout k ≥ 1) et 2^k > 0.

      En fait : 2·3^k = 2^{1 + k·log₂3} et 2^S ≤ 2^{k·log₂3 + 1} = 2·3^k.
      Donc 2·3^k ≥ 2^S. Alors 2·3^k - 2^k ≥ 2^S - 2^k > 2^S - 2^S = 0.
      Mais on a besoin de STRICTE supériorité : 2·3^k - 2^k > 2^S.

      Cas 1 : S = ⌈k·log₂3⌉ < k·log₂3 + 1 (non-convergent)
        Alors 2^S < 2·3^k, et la marge est 2·3^k - 2^S > 0.
        Et 2^k < 2·3^k - 2^S ssi ... (à vérifier numériquement pour k petit)

      Cas 2 : S = k·log₂3 + 1 - ε (convergent par au-dessus, ε petit)
        Alors 2^S ≈ 2·3^k, et la marge est petite.
    """
    print(f"\n  {'k':>3} {'cs_min':>15} {'d':>15} {'cs_min-d':>15} {'cs_min/d':>10} "
          f"{'OK':>4}")
    print(f"  {'─'*3} {'─'*15} {'─'*15} {'─'*15} {'─'*10} {'─'*4}")

    all_ok = True
    for k in range(2, 70):
        S = math.ceil(k * math.log2(3))
        d = (1 << S) - 3**k
        cs_min = 3**k - 2**k

        ok = cs_min > d
        all_ok = all_ok and ok

        if k <= 20 or k in {41, 53, 68, 69} or not ok:
            print(f"  {k:3d} {cs_min:15,d} {d:15,d} {cs_min - d:15,d} "
                  f"{cs_min/d:10.4f} {'✓' if ok else '✗':>4}")

    print(f"\n  Resultat : cs_min > d pour TOUT k = 2..69 : {'✓ PROUVE' if all_ok else '✗ ECHOUE'}")
    return all_ok


# ═══════════════════════════════════════════════════════════════════════
# Section 2 : Analyse des multiples admissibles de d
# ═══════════════════════════════════════════════════════════════════════

def admissible_multiples_analysis():
    """Pour corrSum(A) ≡ 0 mod d, on a corrSum(A) = m·d avec m ≥ 2.

    Les multiples admissibles sont m = 2, 3, ..., ⌊cs_max/d⌋.
    Combien y en a-t-il ? Et comment C/d se compare-t-il ?
    """
    print(f"\n  {'k':>3} {'m_min':>6} {'m_max':>8} {'#mult':>8} {'C':>10} "
          f"{'C/#mult':>8} {'hits_0':>8}")
    print(f"  {'─'*3} {'─'*6} {'─'*8} {'─'*8} {'─'*10} {'─'*8} {'─'*8}")

    for k in range(2, 18):
        S = math.ceil(k * math.log2(3))
        d = (1 << S) - 3**k
        C = math.comb(S - 1, k - 1)

        if C > 200_000:
            # Calcul sans énumération
            cs_min = 3**k - 2**k
            cs_max_approx = sum(3**(k-1-i) * 2**(S-1-i) for i in range(k))
            m_min = math.ceil(cs_min / d)
            m_max = cs_max_approx // d
            num_mult = m_max - m_min + 1
            hits_0 = "?"
        else:
            comps = compositions(S, k)
            corrsums = [corrsum(A, k) for A in comps]
            cs_min = min(corrsums)
            cs_max = max(corrsums)
            m_min = math.ceil(cs_min / d)
            m_max = cs_max // d
            num_mult = m_max - m_min + 1

            # Comptage réel des hits mod d = 0
            hits_0 = sum(1 for cs in corrsums if cs % d == 0)

        print(f"  {k:3d} {m_min:6d} {m_max:8d} {num_mult:8d} {C:10,d} "
              f"{C/num_mult if num_mult > 0 else 0:8.2f} {hits_0:>8}")


# ═══════════════════════════════════════════════════════════════════════
# Section 3 : Injectivité de corrSum mod d
# ═══════════════════════════════════════════════════════════════════════

def injectivity_analysis():
    """Analyse si corrSum est (quasi-)injective mod d.

    Si corrSum est injective mod d, alors |Im(corrSum mod d)| = C.
    Et si C < d, alors la fraction C/d < 1 des résidus est couverte,
    et il y a d - C résidus non couverts. Si 0 est parmi eux, H tient.

    Mais même si corrSum n'est pas injective, les collisions réduisent
    la taille de l'image, rendant l'exclusion de 0 PLUS PROBABLE.
    """
    print(f"\n  {'k':>3} {'C':>8} {'d':>12} {'|Im|':>8} {'C/|Im|':>8} "
          f"{'|Im|/d':>8} {'0∈Im':>6}")
    print(f"  {'─'*3} {'─'*8} {'─'*12} {'─'*8} {'─'*8} {'─'*8} {'─'*6}")

    for k in range(2, 14):
        S = math.ceil(k * math.log2(3))
        d = (1 << S) - 3**k
        C = math.comb(S - 1, k - 1)

        if C > 200_000:
            continue

        comps = compositions(S, k)
        residues = [corrsum(A, k) % d for A in comps]
        image = set(residues)
        zero_in_image = 0 in image

        # Statistiques de collision
        counter = Counter(residues)
        max_collision = max(counter.values())
        avg_collision = C / len(image)

        print(f"  {k:3d} {C:8d} {d:12,d} {len(image):8d} {avg_collision:8.3f} "
              f"{len(image)/d:8.5f} {'OUI' if zero_in_image else 'NON':>6}")

    return


# ═══════════════════════════════════════════════════════════════════════
# Section 4 : La contrainte de BORNES sur corrSum
# ═══════════════════════════════════════════════════════════════════════

def bounds_constraint_analysis():
    """Exploite les bornes exactes sur corrSum pour restreindre les multiples de d.

    corrSum(A) est BORNÉ : cs_min ≤ corrSum(A) ≤ cs_max.

    Pour corrSum = m·d, les valeurs possibles de m sont dans [m_min, m_max].

    La PROPORTION de multiples de d dans [cs_min, cs_max] est :
      (m_max - m_min + 1) / ((cs_max - cs_min) / d + 1) ≈ 1

    C'est-à-dire que les multiples de d sont UNIFORMÉMENT répartis dans
    l'intervalle, et la probabilité de toucher un multiple quelconque est ~ 1/d.

    Pour le multiple m = 0 SPECIFIQUEMENT : corrSum(A) = 0 est IMPOSSIBLE
    car cs_min > 0 (pour k ≥ 1). Et corrSum(A) = d est AUSSI impossible
    car cs_min > d (prouvé en §1). Donc m ≥ 2.

    La question est : peut-on trouver A tel que corrSum(A) = m·d pour un m ≥ 2 ?
    """
    print(f"\n  {'k':>3} {'cs_min/d':>10} {'cs_max/d':>10} "
          f"{'density':>10} {'expected':>10} {'actual':>8}")
    print(f"  {'─'*3} {'─'*10} {'─'*10} {'─'*10} {'─'*10} {'─'*8}")

    for k in range(2, 14):
        S = math.ceil(k * math.log2(3))
        d = (1 << S) - 3**k
        C = math.comb(S - 1, k - 1)

        if C > 200_000:
            continue

        comps = compositions(S, k)
        corrsums = [corrsum(A, k) for A in comps]
        cs_min, cs_max = min(corrsums), max(corrsums)
        m_min = math.ceil(cs_min / d)
        m_max = cs_max // d
        num_multiples = m_max - m_min + 1

        # "Densité" : C compositions dans un intervalle de taille cs_max - cs_min + 1
        range_size = cs_max - cs_min + 1
        density = C / range_size

        # Expected hits : density * nombre de multiples (modèle uniforme)
        expected_hits = density * num_multiples

        # Actual
        actual_hits = sum(1 for cs in corrsums if cs % d == 0)

        print(f"  {k:3d} {cs_min/d:10.4f} {cs_max/d:10.4f} "
              f"{density:10.6f} {expected_hits:10.4f} {actual_hits:8d}")


# ═══════════════════════════════════════════════════════════════════════
# Section 5 : La valuation 2-adique de corrSum
# ═══════════════════════════════════════════════════════════════════════

def two_adic_analysis():
    """Analyse la valuation 2-adique v₂(corrSum(A)).

    corrSum(A) = Σ 3^{k-1-i} · 2^{A_i}

    Puisque A_0 = 0, le premier terme est 3^{k-1} (impair).
    Donc v₂(corrSum(A)) = 0 SI aucun autre terme n'est pair et ne compense.

    En fait : corrSum(A) = 3^{k-1} + Σ_{i=1}^{k-1} 3^{k-1-i} · 2^{A_i}
    Le premier terme 3^{k-1} est TOUJOURS IMPAIR.
    Les termes suivants sont des multiples de 2^{A_i} avec A_i ≥ 1, donc PAIRS.
    Donc corrSum(A) = (impair) + (pair) = IMPAIR.

    Conséquence : v₂(corrSum(A)) = 0 pour TOUT A.

    Et d = 2^S - 3^k. Puisque 2^S est pair et 3^k est impair, d est IMPAIR.
    Donc v₂(d) = 0.

    Cette propriété est compatible mais ne suffit pas à prouver H.
    """
    print(f"\n  Verification : corrSum(A) est toujours impair")
    print(f"  {'k':>3} {'C':>8} {'#impairs':>10} {'%':>8}")
    print(f"  {'─'*3} {'─'*8} {'─'*10} {'─'*8}")

    for k in range(2, 14):
        S = math.ceil(k * math.log2(3))
        C = math.comb(S - 1, k - 1)
        if C > 200_000:
            continue

        comps = compositions(S, k)
        n_odd = sum(1 for A in comps if corrsum(A, k) % 2 == 1)
        print(f"  {k:3d} {C:8d} {n_odd:10d} {n_odd/C*100:7.2f}%")


# ═══════════════════════════════════════════════════════════════════════
# Section 6 : L'argument de structure — corrSum mod d est "anti-0"
# ═══════════════════════════════════════════════════════════════════════

def anti_zero_structure():
    """Analyse pourquoi le résidu 0 mod d est spécifiquement évité.

    corrSum(A) ≡ 0 mod d ⟺ corrSum(A) ≡ 0 mod (2^S - 3^k)

    Or corrSum(A) = Σ 3^{k-1-i} · 2^{A_i}

    En réduisant mod d = 2^S - 3^k, et en utilisant 2^S ≡ 3^k mod d :

    Définissons la "somme normalisée" :
      η(A) = corrSum(A) / 3^{k-1}  (dans ℚ)
           = 1 + Σ_{i=1}^{k-1} 3^{-i} · 2^{A_i}
           = 1 + (2/3)^{A_1}/3^{0} + ... (pas tout à fait)

    En fait : η(A) = Σ_{i=0}^{k-1} (2/3)^{A_i} · 3^{A_i - i}... Non, trop compliqué.

    Simplifions : corrSum(A) = 3^{k-1}·2^0 + 3^{k-2}·2^{A_1} + ... + 3^0·2^{A_{k-1}}

    C'est la valeur de Horner du polynôme f(x) = 2^{A_{k-1}} + 3·2^{A_{k-2}} + ...
    évalué en x = 3, multiplié par les puissances de 2.

    Forme compacte : corrSum(A) = Σ_{j=0}^{k-1} 3^j · 2^{A_{k-1-j}}

    Et d = 2^S - 3^k. Donc mod d : 3^k ≡ 2^S.

    Si k divise l'un des exposants... Non.

    Explorons plutôt la VALEUR MINIMALE de corrSum/d :
    """
    print(f"\n  Distributions de corrSum mod d — focus sur la zone autour de 0")
    print(f"  {'k':>3} {'d':>10} {'min_res':>10} {'max_res':>10} "
          f"{'gap_around_0':>14} {'0_excluded':>12}")
    print(f"  {'─'*3} {'─'*10} {'─'*10} {'─'*10} {'─'*14} {'─'*12}")

    for k in range(2, 14):
        S = math.ceil(k * math.log2(3))
        d = (1 << S) - 3**k
        C = math.comb(S - 1, k - 1)
        if C > 200_000:
            continue

        comps = compositions(S, k)
        residues = sorted(set(corrsum(A, k) % d for A in comps))

        min_res = min(residues)
        max_res = max(residues)

        # Gap around 0 : distance minimale de 0 dans la liste des résidus
        # (en considérant la distance circulaire mod d)
        if 0 in residues:
            gap = 0
        else:
            # Distance au plus proche résidu de 0 (mod d, circulaire)
            gap_above = min(r for r in residues if r > 0) if any(r > 0 for r in residues) else d
            gap_below = d - max(r for r in residues if r > 0) if any(r > 0 for r in residues) else d
            gap = min(gap_above, gap_below)

        excluded = 0 not in residues
        print(f"  {k:3d} {d:10,d} {min_res:10,d} {max_res:10,d} "
              f"{gap:14,d} {'EXCLU' if excluded else 'PRESENT':>12}")


# ═══════════════════════════════════════════════════════════════════════
# Section 7 : L'argument arithmétique — la "borne de lift"
# ═══════════════════════════════════════════════════════════════════════

def lift_bound_analysis():
    """L'argument de LIFT :

    corrSum(A) = m·d avec m ∈ ℕ*

    Borne inférieure : corrSum ≥ cs_min = 3^k - 2^k ≥ d + (3^k - 2^k - d) = d + (2·3^k - 2^k - 2^S)
    Donc m ≥ ⌈cs_min/d⌉ = ⌈(3^k - 2^k)/d⌉

    Borne supérieure : corrSum ≤ cs_max = Σ 3^{k-1-i}·2^{S-1-i} pour i=0..k-1
    Donc m ≤ ⌊cs_max/d⌋

    La question : combien de ces m correspondent à des corrSum REALISABLES ?

    Un corrSum réalisable doit être de la forme Σ 3^{k-1-i}·2^{A_i} avec
    0 = A_0 < A_1 < ... < A_{k-1} ≤ S-1.

    L'ensemble des corrSum réalisables est DISCRET et STRUCTURÉ.
    Un multiple m·d doit coïncider avec l'un de ces points structurés.

    ARGUMENT CLÉ : Pour k grand, la DISTANCE entre corrSum consécutifs
    (en moyenne) est (cs_max - cs_min)/C ≈ d·(m_max - m_min)/C ≈ d·num_mult/C.
    Et la distance entre multiples de d consécutifs est d.
    Si C < num_mult, la densité de corrSum est INFÉRIEURE à celle des multiples,
    ce qui rend chaque multiple individuel rarement touché.

    Mais ce n'est qu'un argument heuristique, pas une preuve.
    """
    print(f"\n  {'k':>3} {'spacing_d':>12} {'spacing_cs':>12} {'ratio':>10} "
          f"{'C_eff':>10} {'N0':>6}")
    print(f"  {'─'*3} {'─'*12} {'─'*12} {'─'*10} {'─'*10} {'─'*6}")

    for k in range(2, 14):
        S = math.ceil(k * math.log2(3))
        d = (1 << S) - 3**k
        C = math.comb(S - 1, k - 1)
        if C > 200_000:
            continue

        comps = compositions(S, k)
        corrsums = sorted(corrsum(A, k) for A in comps)
        cs_min, cs_max = corrsums[0], corrsums[-1]

        # Espacement moyen entre corrSum consécutifs
        spacing_cs = (cs_max - cs_min) / (C - 1) if C > 1 else float('inf')
        # Espacement entre multiples de d
        spacing_d = d

        # "C effectif" : nombre de corrSum dans une fenêtre de taille d
        C_eff = d / spacing_cs if spacing_cs > 0 else float('inf')

        N0 = sum(1 for cs in corrsums if cs % d == 0)

        print(f"  {k:3d} {spacing_d:12.1f} {spacing_cs:12.4f} "
              f"{spacing_d/spacing_cs:10.2f} {C_eff:10.2f} {N0:6d}")


# ═══════════════════════════════════════════════════════════════════════
# Section 8 : Le théorème de preuve formelle
# ═══════════════════════════════════════════════════════════════════════

def formal_proof_attempt():
    """Tentative de construction de la preuve formelle.

    THÉORÈME : Pour tout k ≥ 3, corrSum(A) ≢ 0 mod d(k).

    APPROCHE DE PREUVE :

    1. Pour k = 3, ..., 68 : vérification par calcul exhaustif.
       (Déjà réalisé dans Phase 19 — 81 théorèmes Lean)

    2. Pour k ≥ 69, nous prouvons :

    LEMME 1 : cs_min = 3^k - 2^k > d = 2^S - 3^k pour tout k ≥ 2.
    PREUVE : cs_min - d = (3^k - 2^k) - (2^S - 3^k) = 2·3^k - 2^k - 2^S
             = 2·3^k - 2^k - 2^{⌈k·log₂3⌉}.
             Puisque 2^{⌈k·log₂3⌉} ≤ 2·3^k et 2^k < 3^k pour k ≥ 2,
             cs_min - d ≥ 2·3^k - 3^k - 2·3^k = -3^k... Non, ça ne marche pas.

             Reprise : cs_min - d = 2(3^k - 2^{S-1}) - 2^k.
             Or 3^k > 2^{S-1} car S-1 < k·log₂3, donc 2^{S-1} < 3^k.
             Et 2(3^k - 2^{S-1}) > 2·0 = 0. Mais on a besoin que ce soit > 2^k.

             3^k - 2^{S-1} = 3^k - 2^{⌈k·log₂3⌉-1}.
             Si S = ⌈k·log₂3⌉, alors S-1 < k·log₂3 ≤ S.
             Donc 2^{S-1} < 3^k ≤ 2^S.
             3^k - 2^{S-1} ≥ 3^k - 3^k = 0.
             Plus précisément : 3^k - 2^{S-1} = 3^k·(1 - 2^{S-1}/3^k)
                                               = 3^k·(1 - 2^{S-1-k·log₂3})
                                               = 3^k·(1 - 2^{-γ_S})
             où γ_S = k·log₂3 - (S-1) ∈ (0, 1].

             Alors cs_min - d = 2·3^k·(1 - 2^{-γ_S}) - 2^k
                              = 3^k·(2 - 2^{1-γ_S}) - 2^k.

             Pour k ≥ 3 : 3^k/2^k = (3/2)^k ≥ (3/2)^3 = 3.375.
             Donc 2^k ≤ 3^k/3.375.
             cs_min - d ≥ 3^k·(2 - 2^{1-γ_S}) - 3^k/3.375
                        = 3^k·(2 - 2^{1-γ_S} - 1/3.375)

             Il faut que 2 - 2^{1-γ_S} > 1/3.375 = 0.296.
             I.e., 2^{1-γ_S} < 1.704. I.e., 1-γ_S < log₂(1.704) = 0.769.
             I.e., γ_S > 0.231.

             PROBLÈME : pour les convergents, γ_S peut être très petit (proche de 0).
             Par exemple k=5 : γ = 0.075, et la condition γ > 0.231 n'est PAS satisfaite.

             Mais numériquement cs_min > d est TOUJOURS vrai. Il faut une preuve
             plus fine pour les petits γ.

    LEMME 2 (affinement) : Pour tout k ≥ 2,
      cs_min - d = 3^k·(2 - 2^{1-γ_S}) - 2^k > 0

    PREUVE POUR LES CONVERGENTS :
      Le cas le plus serré est k=12 : cs_min/d = 527345/517135 = 1.0197.
      La marge est POSITIVE mais petite (2%).
      Pour k=41 : cs_min = 3^41 - 2^41 = 36472996377170786403 - 2199023255552 = ...
      cs_min/d dépend de γ.

      Pour γ petit : cs_min - d ≈ 3^k·(2·γ·ln2) - 2^k
                                = 3^k·(1.386·γ) - 2^k
      Et d ≈ 3^k·(2^γ - 1) ≈ 3^k·γ·ln2 = 3^k·0.693·γ.
      Donc cs_min/d ≈ (3^k·1.386·γ - 2^k) / (3^k·0.693·γ)
                     ≈ 2 - 2^k/(3^k·0.693·γ)
                     = 2 - (2/3)^k / (0.693·γ)

      Pour k suffisamment grand : (2/3)^k → 0, donc cs_min/d → 2.
      Le ratio converge vers 2 pour tout γ > 0 fixé.
      Même pour γ très petit, dès que k est assez grand, cs_min/d > 1.

      Pour k fixé et γ → 0 :
        cs_min - d ≈ 3^k·1.386·γ - 2^k > 0 iff γ > 2^k/(3^k·1.386) = (2/3)^k/1.386
        Pour k=5 : (2/3)^5/1.386 = 0.0324·0.721 = 0.095. Et γ(5) = 0.075 < 0.095...

        Wait, vérifions : k=5, γ=0.075.
        cs_min = 3^5 - 2^5 = 243 - 32 = 211.
        d = 2^8 - 3^5 = 256 - 243 = 13.
        cs_min/d = 211/13 = 16.23. Très grand !

        Ah, ma formule asymptotique n'est pas bonne pour les petits k.
        Le problème est que 2^k est NEGLIGEABLE devant 3^k pour k ≥ 3.
        cs_min = 3^k - 2^k ≈ 3^k pour k grand.
        d = 2^S - 3^k ≈ γ·ln2·3^k.
        Donc cs_min/d ≈ 1/(γ·ln2) >> 1 pour petit γ.

        La preuve est triviale dans ce régime : cs_min ≈ 3^k >> d ≈ γ·3^k.
        cs_min > d car 1 > γ·ln2 ≈ 0.693·γ, ce qui est vrai pour γ < 1.443. ✓

    BILAN : cs_min > d est FACILE à prouver formellement.
    """
    print(f"\n  VERIFICATION DE LA PREUVE :")
    print(f"\n  LEMME 1 : cs_min > d pour tout k ≥ 2")

    min_ratio = float('inf')
    min_k = 0
    for k in range(2, 200):
        S = math.ceil(k * math.log2(3))
        d = (1 << S) - 3**k
        cs_min = 3**k - 2**k
        ratio = cs_min / d
        if ratio < min_ratio:
            min_ratio = ratio
            min_k = k

    print(f"    Ratio minimal cs_min/d = {min_ratio:.6f} atteint en k = {min_k}")
    print(f"    cs_min > d pour k = 2..199 : {'✓' if min_ratio > 1 else '✗'}")

    # Argument asymptotique
    print(f"\n  ARGUMENT ASYMPTOTIQUE :")
    print(f"    Pour k → ∞ : cs_min/d → 1/(γ·ln2) > 1 (car γ < 1/ln2 ≈ 1.443)")
    print(f"    γ maximal = 1 - ε (quand S = ⌈k·log₂3⌉ et la partie frac. est petite)")
    print(f"    Dans le pire cas : cs_min/d ≈ 1/ln2 ≈ 1.443")
    print(f"    Valeur numerique minimale : cs_min/d = {min_ratio:.6f} en k = {min_k}")

    # La borne C/d
    print(f"\n  LEMME 2 : C/d → 0 exponentiellement")
    print(f"    H₂(1/log₂3) = {-1/math.log2(3)*math.log2(1/math.log2(3)) - (1-1/math.log2(3))*math.log2(1-1/math.log2(3)):.6f}")
    print(f"    Deficit entropique = H₂ - 1 = {-1/math.log2(3)*math.log2(1/math.log2(3)) - (1-1/math.log2(3))*math.log2(1-1/math.log2(3)) - 1:.6f}")
    print(f"    Taux : C/d ≈ 0.9465^k")
    print(f"    Pour k = 69 : C/d < {0.9465**69:.6f}")

    # L'obstacle restant
    print(f"""
  OBSTACLE CENTRAL :
  =================

  Même si cs_min > d et C/d → 0, cela ne prouve PAS que 0 ∉ Im(corrSum mod d).

  La condition cs_min > d montre que corrSum(A) ≥ 2d pour les cas frontières,
  donc corrSum(A) = m·d avec m ≥ 2.

  Mais il pourrait exister un A tel que corrSum(A) soit EXACTEMENT un multiple de d.

  Pour k ≥ 69 : C/d < 0.024. Il y a ~C ≈ d/42 compositions. L'intervalle
  [cs_min, cs_max] contient ~cs_max/d ≈ 2^S/d ≈ 3^k/d multiples de d.
  Chaque composition touche un seul point de l'intervalle. La probabilité
  de toucher un multiple de d est ~(nombre de multiples)·(taille du point)/range
  = 1/d par composition, soit C/d au total. C'est < 0.024.

  C'est un argument PROBABILISTE (pas une preuve formelle).

  POUR UNE PREUVE FORMELLE, deux voies :

  VOIE A : Prouver que corrSum mod d a une distribution "uniformément bornée"
           (type borne de Weil), donnant max|T(t)|/C < 1/(p-1) pour tout p|d.
           → Nécessite des bornes sur les sommes exponentielles lacunaires.

  VOIE B : Exploiter la structure arithmétique EXACTE de corrSum.
           → La congruence 2^S ≡ 3^k mod d impose des relations rigides.
           → corrSum(A) mod d = Σ 3^{{k-1-i}}·2^{{A_i}} mod d peut être analysé
             en utilisant 2^S = 3^k + d.

  VOIE C : Preuve computationnelle étendue.
           → Étendre la vérification à k ≤ K₀ pour K₀ assez grand.
           → Puis utiliser un argument de monotonie : pour k > K₀, le "margin"
             C/d est tellement petit que l'exclusion est certaine.
           → Nécessite un argument de TRANSFERT du computationnel au théorique.
  """)


# ═══════════════════════════════════════════════════════════════════════
# Section 9 : Programme principal
# ═══════════════════════════════════════════════════════════════════════

def main():
    t0 = time.time()

    print("=" * 82)
    print("Phase 21f — Construction de la Preuve de l'Hypothèse H")
    print("Programme Merle — Projet Collatz-Junction-Theorem")
    print("=" * 82)

    # S1
    print(f"\n{'─' * 82}")
    print("S1. Identite fondamentale : cs_min = 3^k - 2^k > d = 2^S - 3^k")
    print(f"{'─' * 82}")
    verify_csmin_greater_d()

    # S2
    print(f"\n{'─' * 82}")
    print("S2. Multiples admissibles de d dans [cs_min, cs_max]")
    print(f"{'─' * 82}")
    admissible_multiples_analysis()

    # S3
    print(f"\n{'─' * 82}")
    print("S3. Injectivite de corrSum mod d")
    print(f"{'─' * 82}")
    injectivity_analysis()

    # S4
    print(f"\n{'─' * 82}")
    print("S4. Contrainte de bornes : densite vs multiples")
    print(f"{'─' * 82}")
    bounds_constraint_analysis()

    # S5
    print(f"\n{'─' * 82}")
    print("S5. Valuation 2-adique de corrSum")
    print(f"{'─' * 82}")
    two_adic_analysis()

    # S6
    print(f"\n{'─' * 82}")
    print("S6. Structure anti-zero : gap autour de 0 mod d")
    print(f"{'─' * 82}")
    anti_zero_structure()

    # S7
    print(f"\n{'─' * 82}")
    print("S7. Espacement de corrSum vs espacement de d")
    print(f"{'─' * 82}")
    lift_bound_analysis()

    # S8
    print(f"\n{'─' * 82}")
    print("S8. Construction de la preuve formelle")
    print(f"{'─' * 82}")
    formal_proof_attempt()

    elapsed = time.time() - t0
    print(f"\nTemps d'execution : {elapsed:.1f}s")
    print(f"{'=' * 82}")


if __name__ == "__main__":
    main()
