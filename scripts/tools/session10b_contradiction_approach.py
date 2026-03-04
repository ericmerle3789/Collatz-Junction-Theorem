#!/usr/bin/env python3
"""
SESSION 10b — APPROCHE PAR CONTRADICTION
==========================================
Protocole DISCOVERY v2.2, Boucle G-V-R #1.

PRÉ-ENGAGEMENT :
  Hypothèse : Si f(B) = Σ_{j=1}^{k-1} u^j · 2^{B_j} = -1 mod p
              avec B non-décroissante, alors on peut dériver une contradiction
              en utilisant l'identité u^k = 2^{k-S} et σ̃(u) = Σ u^j.
  Critère de succès : Trouver une identité/inégalité UNIVERSELLE qui exclut -1.
  Critère d'échec : Si l'approche ne donne rien après 5 itérations → Cimetière.

INVESTIGATIONS :
  I1  : σ̃(u) = Σ_{j=1}^{k-1} u^j pour tous les k premiers
        Quand σ̃(u) = 0 vs ≠ 0 ? Y a-t-il un pattern ?
  I2  : Multiplication par u : si f(B)=-1, que vaut u·f(B) ?
        Explorer la récurrence f → u·f + correction
  I3  : Identité de clôture : f(B) + 1 = 0 → f(B) + u^0·2^{B_0} = ?
        Relier à la somme COMPLÈTE (k termes incluant j=0)
  I4  : Approche par les SOMMES PARTIELLES : montrer que la trajectoire
        cumulative ne peut pas terminer en -1
  I5  : La structure de l'image pour k=13 (p=502829, grand premier)
        Test de passage à l'échelle
  I6  : Analyse de la DISTANCE à -1 : quelle est la valeur la plus proche ?
  I7  : Synthèse : direction de la preuve générale
"""

from math import ceil, log2, gcd, comb
from itertools import combinations
from collections import Counter, defaultdict
import time

def compute_params(k):
    S = ceil(k * log2(3))
    d = 2**S - 3**k
    C = comb(S - 1, k - 1)
    return S, d, C

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i+2) == 0: return False
        i += 6
    return True

def multiplicative_order(a, n):
    if gcd(a, n) != 1:
        return None
    order = 1
    current = a % n
    while current != 1:
        current = (current * a) % n
        order += 1
        if order > n:
            return None
    return order

# ============================================================
# INVESTIGATION 1 : σ̃(u) pour tous les k premiers
# ============================================================
def investigate_sigma_tilde():
    """
    σ̃(u) = Σ_{j=1}^{k-1} u^j mod p
    σ(u) = Σ_{j=0}^{k-1} u^j = 1 + σ̃(u) mod p

    Si u ≠ 1 mod p : σ(u) = (u^k - 1)/(u - 1) mod p
    Et σ̃(u) = σ(u) - 1

    u^k = 2^{k-S} mod p → σ(u) = (2^{k-S} - 1)/(u - 1) mod p
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 1 : σ̃(u) = Σ u^j (j=1..k-1) pour k premiers")
    print("=" * 70)

    results = []
    for k in range(3, 22):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)
        u = (w * 2) % p
        ord_u = multiplicative_order(u, p)

        # σ(u) = Σ_{j=0}^{k-1} u^j
        sigma_full = sum(pow(u, j, p) for j in range(k)) % p
        # σ̃(u) = Σ_{j=1}^{k-1} u^j = σ(u) - 1
        sigma_tilde = (sigma_full - 1) % p

        # Formule fermée : si u ≠ 1
        if u != 1:
            uk = pow(u, k, p)
            u_minus_1_inv = pow(u - 1, -1, p)
            sigma_formula = ((uk - 1) * u_minus_1_inv) % p
        else:
            sigma_formula = k % p

        # Vérifier l'identité u^k = 2^{k-S}
        uk_actual = pow(u, k, p)
        two_kS = pow(2, k - S, p) if k >= S else pow(pow(2, S - k, p), -1, p)

        results.append({
            'k': k, 'p': p, 'u': u, 'ord_u': ord_u,
            'sigma_full': sigma_full, 'sigma_tilde': sigma_tilde,
            'sigma_formula': sigma_formula,
            'uk': uk_actual, 'two_kS': two_kS,
            'C_over_p': C / p
        })

        print(f"\n  k={k:2d}, p={p:>10d}, u={u:>10d}, ord(u)={ord_u}")
        print(f"    σ(u)  = {sigma_full:>10d} (formule: {sigma_formula})")
        print(f"    σ̃(u)  = {sigma_tilde:>10d}")
        print(f"    u^k   = {uk_actual:>10d}, 2^(k-S) = {two_kS:>10d}, "
              f"match: {'✓' if uk_actual == two_kS else '✗'}")
        print(f"    C/p   = {C/p:.4f}")

        # Quand σ̃(u) = 0 ?
        if sigma_tilde == 0:
            print(f"    ★★★ σ̃(u) = 0 ! Les séquences constantes B donnent toutes f=0.")
            # Cela signifie que la somme Σ_{j=1}^{k-1} u^j = 0
            # Donc (u^k - u)/(u-1) = 0
            # Donc u^k = u, i.e., u^{k-1} = 1
            # Donc ord(u) | (k-1)
            print(f"    Vérification : ord(u)={ord_u}, k-1={k-1}, "
                  f"ord(u) | (k-1) ? {'OUI' if (k-1) % ord_u == 0 else 'NON'}")

    # Résumé
    print(f"\n{'=' * 70}")
    print(f"  RÉSUMÉ σ̃(u) :")
    for r in results:
        zero_marker = " ★ σ̃=0" if r['sigma_tilde'] == 0 else ""
        print(f"    k={r['k']:2d}: σ̃(u) = {r['sigma_tilde']:>10d} mod {r['p']:>10d}{zero_marker}")

# ============================================================
# INVESTIGATION 2 : Multiplication par u
# ============================================================
def investigate_u_multiplication():
    """
    Si f(B) = Σ_{j=1}^{k-1} u^j · 2^{B_j} = -1 mod p
    Alors u · f(B) = Σ_{j=1}^{k-1} u^{j+1} · 2^{B_j}
                   = Σ_{j=2}^{k} u^j · 2^{B_{j-1}}
                   = -u mod p

    La somme complète (k termes, j=0..k-1) est :
    F(B) = u^0·2^{B_0} + f(B) = 2^{B_0} + f(B)

    Si f(B) = -1 :
    F(B) = 2^{B_0} - 1 mod p

    Mais F(B) correspond à l'automate de Horner !
    F(B) = Σ_{j=0}^{k-1} u^j · 2^{B_j} = 0 ⟺ corrSum ≡ 0 mod p
    Donc f(B) = -1 ⟺ F(B) = 2^{B_0} - 1

    Or B_0 correspond à A_0 = 0 + 0 = 0 (puisque B_0 = A_0 - 0 = 0).
    Donc 2^{B_0} = 1.
    Donc F(B) = 1 - 1 = 0 mod p.
    Donc f(B) = -1 ⟺ corrSum ≡ 0 mod p. C'est tautologique !

    MAIS : attendons. B_0 est FIXÉ à 0 (car A_0 = 0 toujours).
    f(B) ne considère que j=1..k-1, pas j=0.
    Le terme j=0 est u^0 · 2^{B_0} = 1 · 2^0 = 1.
    Donc F(B) = 1 + f(B).
    Et F(B) = 0 ⟺ f(B) = -1. Tautologie confirmée.

    Cherchons une AUTRE relation.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 2 : Multiplication par u et récurrence")
    print("=" * 70)

    for k in [3, 5]:
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)
        u = (w * 2) % p

        print(f"\n--- k={k}, p={p}, u={u} ---")

        # La tautologie est confirmée : f(B) = -1 ⟺ F(B) = 0 ⟺ corrSum ≡ 0
        print(f"    Tautologie confirmée : f(B)=-1 ⟺ corrSum≡0 mod p")

        # Cherchons une relation NON-tautologique.
        # Idée : u · f(B) = Σ u^{j+1} · 2^{B_j} pour j=1..k-1
        #       = u^2·2^{B_1} + ... + u^k·2^{B_{k-1}}
        #       = f_shifted(B) + u^k·2^{B_{k-1}} - u·2^{B_1}
        # Non, c'est plus subtil. Écrivons :
        # u·f(B) = Σ_{j=1}^{k-1} u^{j+1}·2^{B_j}
        #        = Σ_{i=2}^{k} u^i·2^{B_{i-1}}
        # Donc u·f(B) = f_shifted(B) où B_shifted a B_{j-1} au rang j pour j=2..k
        #             + le terme u^k·2^{B_{k-1}}
        #             - le terme u·2^{B_1} (qui est dans f mais pas dans u·f de façon simple)

        # Plutôt : u·f(B) + u = u·(f(B) + 1) = u·F(B) = u·0 = 0 si f(B)=-1

        # OK, essayons autrement : relation entre f(B) et f(B')
        # où B' est une modification de B.
        # Si on "décale" B de 1 : B'_j = B_j + 1 (quand possible)
        # f(B') = Σ u^j · 2^{B_j+1} = 2 · Σ u^j · 2^{B_j} = 2 · f(B)
        # Donc f(B') = 2f(B) mod p.
        # Si f(B) = -1, alors f(B') = -2 mod p.
        # Mais B' doit encore satisfaire B'_j ≤ S-k, i.e., B_j ≤ S-k-1.
        print(f"\n    Relation de décalage : f(B+1) = 2·f(B) mod p")
        print(f"    Si f(B)=-1 → f(B+1)=-2 → f(B+2)=-4 → ... → f(B+m)=-2^m")
        print(f"    Cela crée une CHAÎNE de valeurs interdites si -1 est interdit.")

        # Les puissances de -2 mod p
        neg_two_powers = set()
        val = (-1) % p
        for m in range(S - k + 1):
            neg_two_powers.add(val)
            val = (val * 2) % p
        print(f"    Chaîne -2^m mod {p} : {sorted(neg_two_powers)}")
        print(f"    Taille de la chaîne : {len(neg_two_powers)}")

        # Si l'un de ces résidus est ABSENT de l'image ordonnée,
        # alors TOUTE la chaîne est absente.
        positions = list(range(1, S))
        weights_u = [pow(u, j, p) for j in range(1, k)]

        image_ordered = set()
        for combo in combinations(positions, k - 1):
            # Convertir en B : B_j = combo[j] - (j+1)
            B = tuple(combo[j] - (j + 1) for j in range(k - 1))
            if all(b >= 0 for b in B):  # doit être non-négatif
                val = sum(weights_u[j] * pow(2, B[j], p) % p for j in range(k - 1)) % p
                image_ordered.add(val)

        # Vérifier quels éléments de la chaîne sont absents
        absent_in_chain = neg_two_powers - image_ordered
        print(f"    Éléments de la chaîne ABSENTS de l'image : {sorted(absent_in_chain)}")
        print(f"    → Taille : {len(absent_in_chain)} / {len(neg_two_powers)}")

        if (-1) % p in absent_in_chain:
            print(f"    ★ -1 fait partie de la chaîne absente !")

# ============================================================
# INVESTIGATION 3 : Somme complète et B_0 = 0
# ============================================================
def investigate_full_sum():
    """
    F(A) = Σ_{j=0}^{k-1} w^j · 2^{A_j} mod p
    avec A_0 = 0 (fixé) → w^0 · 2^0 = 1.
    Donc F(A) = 1 + f(A).
    N₀(p) = 0 ⟺ F(A) ≠ 0 pour toute composition ordonnée
                ⟺ f(A) ≠ -1.

    La question clé : pourquoi F(A) ≠ 0 ?
    F(A) = Σ w^j · 2^{A_j} avec A_0=0 < A_1 < ... < A_{k-1} ≤ S-1.

    Multiplions par w^{-0} = 1 : pas utile.
    Multiplions par 3^{k-1} : corrSum = 3^{k-1} · F(A) mod ... non.

    En fait, F(A) = 0 mod p ⟺ corrSum = 0 mod p.
    Et corrSum = Σ 3^{k-1-j} · 2^{A_j}.

    L'identité clé est 2^S = 3^k mod p.
    Donc 2^S · corrSum = 3^k · corrSum = 3^k · Σ 3^{k-1-j} · 2^{A_j}
                       = Σ 3^{2k-1-j} · 2^{A_j}.
    Et 3^{2k-1-j} = 3^{k-1} · 3^{k-j}.

    Hmm, essayons plutôt l'approche par MONOÏDE.
    F(A) est une somme de k termes de la forme w^j · 2^{A_j}.
    Le premier terme est w^0 · 2^0 = 1.
    Les termes suivants sont dans le sous-groupe <u> = <w·2> fois {1, 2, 4, ...}.

    En fait, w^j · 2^{A_j} = u^j · 2^{A_j - j} = u^j · 2^{B_j}.
    Le premier terme (j=0) est u^0 · 2^{B_0} = 1 · 1 = 1.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 3 : Propriétés de la somme complète F(A)")
    print("=" * 70)

    for k in [3, 5, 13]:
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)
        u = (w * 2) % p

        print(f"\n--- k={k}, p={p}, u={u}, ord(u)={multiplicative_order(u, p)} ---")

        # u^k = 2^{k-S} mod p
        uk = pow(u, k, p)
        # σ(u) = Σ_{j=0}^{k-1} u^j
        sigma = sum(pow(u, j, p) for j in range(k)) % p

        print(f"    u^k = {uk}")
        print(f"    σ(u) = {sigma}")

        # Si F(B) = Σ_{j=0}^{k-1} u^j · 2^{B_j} = 0 avec B_0=0, B non-décroissante
        # Alors 1 + Σ_{j=1}^{k-1} u^j · 2^{B_j} = 0

        # Multiplions par u : u·F(B) = Σ u^{j+1} · 2^{B_j}
        #                            = Σ_{i=1}^{k} u^i · 2^{B_{i-1}}
        # u·F(B) = u·2^{B_0} + u²·2^{B_1} + ... + u^k·2^{B_{k-1}}
        #        = u + u²·2^{B_1} + ... + u^k·2^{B_{k-1}}
        # (car B_0 = 0)

        # Aussi : F(B) = 1 + u·2^{B_1} + u²·2^{B_2} + ... + u^{k-1}·2^{B_{k-1}}

        # Soustrayons : u·F(B) - F(B) = (u-1)·F(B)
        #             = u - 1 + (u²-u)·2^{B_1} + ... + (u^k - u^{k-1})·2^{B_{k-1}}
        #             = (u-1) · (1 + u·2^{B_1} + u²·2^{B_2} + ... + u^{k-1}·2^{B_{k-1}})
        # C'est tautologique : (u-1)·F = (u-1)·F.

        # Essayons une AUTRE manipulation.
        # F(B) = 0 → 1 = -Σ_{j=1}^{k-1} u^j · 2^{B_j}
        # Prenons la somme sur TOUS les B non-décroissants possibles de chaque côté.
        # Σ_B F(B) = Σ_B (1 + Σ_{j=1}^{k-1} u^j · 2^{B_j})
        #          = #B + Σ_{j=1}^{k-1} u^j · Σ_B 2^{B_j}

        # Calculons #B (nombre de suites non-décroissantes de longueur k-1 dans [0, S-k])
        # C'est binom(S-k + k-2, k-2) = binom(S-2, k-2) (stars and bars)
        num_B = comb(S - 2, k - 2) if S >= k else 0
        print(f"    #B (suites non-décroissantes) = {num_B}")
        print(f"    C (compositions ordonnées)     = {C}")
        print(f"    Correspondance : #B = C ? {'OUI ✓' if num_B == C else 'NON'}")

        # En fait, Comp(S,k) = {0 < A_1 < ... < A_{k-1} ≤ S-1}
        # B_j = A_j - j → B_0 = 0 ≤ B_1 ≤ ... ≤ B_{k-1} ≤ S-k
        # #B = binom(S-k + (k-1) - 1, k-1 - 1) = binom(S-2, k-2)
        # Et C = binom(S-1, k-1). En général #B ≠ C.
        # Wait, compositions with k parts summing to S vs ordered positions.
        # Actually the bijection is: (A_1,...,A_{k-1}) strict in [1,S-1]
        # ↔ (B_1,...,B_{k-1}) non-decreasing in [0,S-k]
        # where B_j = A_j - j.
        # The number of strict sequences of k-1 elements in {1,...,S-1}
        # = C(S-1, k-1) = C.
        # The number of non-decreasing sequences of k-1 elements in {0,...,S-k}
        # = C(S-k + k-2, k-2) = C(S-2, k-2).
        # These should be equal by a combinatorial identity...
        # C(S-1, k-1) = (S-1)! / ((k-1)! (S-k)!)
        # C(S-2, k-2) = (S-2)! / ((k-2)! (S-k)!)
        # These are NOT equal in general.
        # Wait, there's a subtlety. The bijection gives a MAP from strict to non-decreasing.
        # Strict: choose k-1 elements from {1,...,S-1} → C(S-1,k-1) choices
        # Non-decreasing: choose k-1 elements with repetition from {0,...,S-k} → C(S-k+k-2, k-2) = C(S-2, k-2)
        # Hmm, these should be equal because it's a bijection.
        # C(S-1, k-1) = C(S-1, S-k). And C(S-2, k-2) = C(S-2, S-k).
        # These are only equal if S-1 = S-2, which is never. So there's an error.

        # Actually the bijection between strict increasing and non-decreasing:
        # strict in {1,...,S-1} of length k-1 → C(S-1, k-1)
        # But the B_j = A_j - j are non-decreasing in {0,...,S-k}
        # This is a BIJECTION between combinations (subsets) of {1,...,S-1}
        # of size k-1 and non-decreasing sequences in {0,...,S-k} of length k-1.
        # The number of non-decreasing sequences of length k-1 from {0,...,S-k}
        # is C(S-k + k-1, k-1) = C(S-1, k-1) = C!
        # (multiset coefficient with n=S-k+1 types, k-1 elements = C(S-k+k-1, k-1) = C(S-1,k-1))
        # OK so they ARE equal.

        num_B_correct = comb(S - 1, k - 1)
        print(f"    (corrigé) #B = C({S-1},{k-1}) = {num_B_correct} = C ✓")

# ============================================================
# INVESTIGATION 4 : Approche par les sommes de Newton
# ============================================================
def investigate_newton_sums():
    """
    Les "poids" u^j (j=1..k-1) sont les puissances d'une seule racine u.
    Ils satisfont la relation de récurrence : power sums.

    Σ u^j = σ̃(u) = (u^k - u)/(u - 1) si u ≠ 1

    Si on définit x_j = 2^{B_j} (les "amplitudes"), alors
    f(B) = Σ_{j=1}^{k-1} u^j · x_j avec 1 ≤ x_1 ≤ x_2 ≤ ... ≤ x_{k-1} ≤ 2^{S-k}

    C'est une somme pondérée avec poids FIXES u^j et amplitudes ORDONNÉES.

    Propriété clé : les poids u^j sont des puissances d'un SEUL élément.
    Donc le "polynôme de poids" est P(X) = uX + u²X² + ... + u^{k-1}X^{k-1}
    évalué en X = 1 (pour x constant).

    → Explorer les sommes de Newton / fonctions symétriques élémentaires
    des amplitudes et leur interaction avec les poids.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 4 : Structure des poids comme puissances de u")
    print("=" * 70)

    for k in [3, 5]:
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)
        u = (w * 2) % p
        ord_u = multiplicative_order(u, p)

        print(f"\n--- k={k}, p={p}, u={u}, ord(u)={ord_u} ---")

        # La propriété clé : le polynôme P(X) = Σ_{j=1}^{k-1} u^j · X^j
        # évalué en X = 2^b donne les contributions
        print(f"    Polynôme P(X) = Σ u^j · X^j (j=1..{k-1})")

        # Évaluation de P aux points 2^b pour b=0..S-k
        for b in range(S - k + 1):
            x = pow(2, b, p)
            P_val = sum(pow(u, j, p) * pow(x, j, p) % p for j in range(1, k)) % p
            # Formule fermée : P(x) = ux · (1 - (ux)^{k-1}) / (1 - ux) si ux ≠ 1
            ux = (u * x) % p
            if ux != 1:
                P_closed = (ux * (1 - pow(ux, k - 1, p)) * pow(1 - ux, -1, p)) % p
            else:
                P_closed = ((k - 1) * ux) % p  # Not exactly but ux = 1 case
            print(f"    P(2^{b}) = P({x}) = {P_val} (fermé: {P_closed})")

        # Maintenant, f(B) = Σ u^j · 2^{B_j} ≠ P évalué en un seul point
        # SAUF si tous les B_j sont égaux (séquence constante)
        # Pour B constante (B_j = b pour tout j) : f(b,...,b) = σ̃(u) · 2^b
        sigma_tilde = sum(pow(u, j, p) for j in range(1, k)) % p
        print(f"\n    σ̃(u) = {sigma_tilde}")
        if sigma_tilde == 0:
            print(f"    ★ σ̃(u) = 0 → f(b,...,b) = 0 pour tout b")
            print(f"      Les séquences constantes donnent TOUJOURS 0")
            print(f"      La somme ne peut valoir -1 que si les B_j sont NON-CONSTANTS")
            print(f"      Mais la contrainte d'ORDRE (non-décroissant) force une certaine homogénéité")
        else:
            print(f"    σ̃(u) ≠ 0 → f(b,...,b) = {sigma_tilde}·2^b parcourt {sigma_tilde}·<2>")
            # Quel ensemble ?
            const_image = set()
            for b in range(S - k + 1):
                val = (sigma_tilde * pow(2, b, p)) % p
                const_image.add(val)
            print(f"    Image des séquences constantes : {sorted(const_image)}")
            print(f"    -1 dans cette image ? {'OUI' if (-1) % p in const_image else 'NON'}")

# ============================================================
# INVESTIGATION 5 : Test de passage à l'échelle (k=13, p=502829)
# ============================================================
def investigate_large_k():
    """
    Pour k=13, p=502829, C=125970.
    C/p ≈ 0.25, donc beaucoup de résidus absents.
    Vérifier que -1 est toujours absent.
    Aussi : calculer σ̃(u) pour voir si le pattern continue.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 5 : k=13 (p=502829) — passage à l'échelle")
    print("=" * 70)

    k = 13
    S, d, C = compute_params(k)
    p = d
    w = pow(3, -1, p)
    u = (w * 2) % p
    ord_u = multiplicative_order(u, p)

    print(f"    k={k}, p={p}, C={C}, C/p={C/p:.4f}")
    print(f"    u={u}, ord(u)={ord_u}")

    sigma_tilde = sum(pow(u, j, p) for j in range(1, k)) % p
    sigma_full = (1 + sigma_tilde) % p
    print(f"    σ̃(u) = {sigma_tilde}")
    print(f"    σ(u) = {sigma_full}")

    # Vérification u^k = 2^{k-S}
    uk = pow(u, k, p)
    two_kS = pow(2, k - S, p) if k >= S else pow(pow(2, S - k, p), -1, p)
    print(f"    u^k = {uk}, 2^(k-S) = {two_kS}, match: {'✓' if uk == two_kS else '✗'}")

    # Pour k=13, l'énumération exhaustive est trop coûteuse (C=125970)
    # Mais on peut calculer la distribution par force brute
    target = (-1) % p

    # Calculer l'image en échantillonnant
    print(f"\n    Énumération exhaustive des {C} compositions...")
    t0 = time.time()
    positions = list(range(1, S))
    weights = [pow(w, j, p) for j in range(1, k)]

    count_target = 0
    residues_seen = set()
    total = 0
    for combo in combinations(positions, k - 1):
        val = sum(weights[j] * pow(2, combo[j], p) % p for j in range(k - 1)) % p
        residues_seen.add(val)
        if val == target:
            count_target += 1
        total += 1

    elapsed = time.time() - t0
    print(f"    Temps : {elapsed:.1f}s, compositions : {total}")
    print(f"    Résidus atteints : {len(residues_seen)}/{p}")
    print(f"    -1 ({target}) : {count_target} compositions")
    print(f"    ★ -1 absent ? {'OUI ✓' if count_target == 0 else 'NON ✗'}")

    # Distance minimale à -1
    min_dist = p
    for r in residues_seen:
        dist = min((r - target) % p, (target - r) % p)
        min_dist = min(min_dist, dist)
    print(f"    Distance minimale à -1 : {min_dist} (sur Z/pZ)")

# ============================================================
# INVESTIGATION 6 : σ̃(u) = 0 ⟺ ord(u) | (k-1)
# ============================================================
def investigate_sigma_zero_condition():
    """
    σ̃(u) = Σ_{j=1}^{k-1} u^j = u·(u^{k-1} - 1)/(u - 1) mod p (si u ≠ 1)

    σ̃(u) = 0 ⟺ u·(u^{k-1} - 1) = 0 mod p
             ⟺ u^{k-1} = 1 mod p (car u ≠ 0 mod p)
             ⟺ ord(u) | (k-1)

    C'est une condition ARITHMÉTIQUE sur u et k.
    Quand est-elle satisfaite ? Pour quels k premiers ?
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 6 : Condition σ̃(u) = 0 ⟺ ord(u) | (k-1)")
    print("=" * 70)

    for k in range(3, 30):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)
        u = (w * 2) % p
        ord_u = multiplicative_order(u, p)

        sigma_tilde = sum(pow(u, j, p) for j in range(1, k)) % p
        divides = (k - 1) % ord_u == 0

        marker = " ★ σ̃=0" if sigma_tilde == 0 else ""
        print(f"    k={k:2d}, p={p:>10d}, u={u:>10d}, ord(u)={ord_u:>8d}, "
              f"k-1={k-1:2d}, ord|k-1: {'OUI' if divides else 'non':>3s}, "
              f"σ̃(u)={sigma_tilde:>10d}{marker}")

        if (sigma_tilde == 0) != divides:
            print(f"    ⚠️ INCOHÉRENCE : σ̃=0 mais ord(u) ∤ (k-1) ou vice versa !")

# ============================================================
# INVESTIGATION 7 : Synthèse
# ============================================================
def synthesize():
    print("\n" + "=" * 70)
    print("  INVESTIGATION 7 : SYNTHÈSE")
    print("=" * 70)

    print("""
    RÉSUMÉ SESSION 10b :

    ★ σ̃(u) = Σ u^j (j=1..k-1) : peut être 0 ou non-nul.
      σ̃(u) = 0 ⟺ ord(u) | (k-1).
      Quand σ̃(u) = 0 : toutes les séquences constantes donnent f=0.
      → La seule façon d'obtenir -1 serait via des séquences non-constantes.
      → Mais la contrainte d'ordre force l'homogénéité.

    ★ Tautologie confirmée : f(B) = -1 ⟺ corrSum ≡ 0 mod p.
      La reformulation TARGET -1 est EXACTEMENT le problème original.
      Son utilité est dans la DÉCOMPOSITION : on sépare le terme j=0 (fixé à 1)
      des k-1 termes variables.

    ★ Relation de décalage : f(B+1) = 2·f(B) mod p.
      Si -1 est exclu, alors -2, -4, -8, ... sont aussi exclus
      (tant que les B décalées restent valides).
      → Chaîne d'exclusion exponentielle !

    ★ L'identité u^k = 2^{k-S} crée une relation de PÉRIODICITÉ partielle
      des poids. Les poids u^j "bouclent" après k étapes.
      Combiné avec la borne B_j ≤ S-k, cela crée une TENSION :
      les amplitudes sont bornées mais les poids sont cycliques.

    PROCHAINE DIRECTION (G-V-R itération 2) :
    - Explorer la CHAÎNE D'EXCLUSION : si -1 est exclu,
      quels autres résidus sont automatiquement exclus ?
    - La chaîne -2^m mod p pourrait expliquer POURQUOI
      l'image ordonnée est si régulière (p-1 résidus pour k=3,5).
    """)

# ============================================================
# MAIN
# ============================================================
if __name__ == "__main__":
    print("SESSION 10b — APPROCHE PAR CONTRADICTION")
    print("=" * 70)
    print("Protocole DISCOVERY v2.2 — Boucle G-V-R #1")
    print()

    t0 = time.time()

    investigate_sigma_tilde()
    investigate_u_multiplication()
    investigate_full_sum()
    investigate_newton_sums()
    investigate_large_k()
    investigate_sigma_zero_condition()
    synthesize()

    elapsed = time.time() - t0
    print(f"\n{'=' * 70}")
    print(f"Temps total : {elapsed:.1f}s")
    print(f"{'=' * 70}")
