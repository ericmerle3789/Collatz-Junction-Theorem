#!/usr/bin/env python3
"""
R165 - TEST DU LEVIER WRONSKIEN ET POLYNOME QUOTIENT
======================================================
Le R165 propose :
  1. Polynome quotient Q(x) = P_B(x) / (x^S - 3^k) dans Z_p
  2. Wronskien W(P_B, x^S-3^k) evalue en x=2
  3. Structure de signe de Q (coefficients negatifs en haut degre)
  4. "Verrouillage differentiel" via W(2) negatif

TESTS :
  A. Le polynome quotient EXISTE-T-IL ? (deg P_B < deg(x^S-3^k))
  B. Le Wronskien W(2) est-il informatif ?
  C. W(2) mod d : contraint-il corrSum ?
  D. La structure de signe de Q contraint-elle quelque chose ?
  E. Application a k=22

PREDICTION : Meme cadre p-adique que R163-R164, memes blocages.
"""

import math
import json
import time
from sympy import factorint


def corrSum_value(k, B_vec):
    return sum(3**(k-1-j) * (1 << B_vec[j]) for j in range(k))

def P_B_deriv_at_2(k, B_vec):
    """P_B'(2) = Sum B_j * 3^{k-1-j} * 2^{B_j - 1} (entier exact)."""
    total = 0
    for j in range(k):
        if B_vec[j] > 0:
            total += B_vec[j] * 3**(k-1-j) * (1 << (B_vec[j] - 1))
    return total

def enumerate_monotone_B(k, max_B):
    if k == 1:
        yield [max_B]
        return
    def _gen(remaining, num_boxes, current):
        if num_boxes == 1:
            yield current + [remaining]
            return
        for c in range(remaining + 1):
            yield from _gen(remaining - c, num_boxes - 1, current + [c])
    for gaps in _gen(max_B, k, []):
        B = [0] * k
        B[0] = gaps[0]
        for j in range(1, k):
            B[j] = B[j-1] + gaps[j]
        yield B


def test_A_quotient_exists(k_range=range(3, 11)):
    """
    Le polynome quotient Q(x) = P_B(x) / (x^S - 3^k) existe-t-il ?

    P_B(x) = Sum 3^{k-1-j} * x^{B_j}, degre = max(B_j) = S-k
    x^S - 3^k, degre = S

    Division euclidienne : deg(P_B) = S-k < S = deg(x^S - 3^k)
    -> Q(x) = 0, R(x) = P_B(x)
    -> Le quotient est TRIVIAL (zero !)
    """
    print("=" * 70)
    print("TEST A : LE POLYNOME QUOTIENT EXISTE-T-IL ?")
    print("=" * 70)

    for k in k_range:
        S = math.ceil(k * math.log2(3)) + 1
        d = (1 << S) - 3**k
        if d <= 0:
            continue
        max_B = S - k

        print(f"\n  k={k}, S={S}, max_B={max_B}")
        print(f"    deg(P_B) = max(B_j) = S-k = {max_B}")
        print(f"    deg(x^S - 3^k) = S = {S}")
        print(f"    Division euclidienne : {max_B} < {S}")
        print(f"    -> Q(x) = 0, R(x) = P_B(x)")
        print(f"    -> Le 'polynome quotient' est ZERO")

    print(f"\n  {'='*60}")
    print(f"  VERDICT TEST A :")
    print(f"  deg(P_B) = S-k < S = deg(x^S - 3^k) pour TOUTE composition monotone.")
    print(f"  La division euclidienne de P_B par x^S-3^k donne Q=0, R=P_B.")
    print(f"  Le 'polynome quotient' du R165 est ZERO.")
    print(f"  ")
    print(f"  Le R165 semble definir Q autrement (dans Z_d ou en utilisant")
    print(f"  la relation 3^k = x^S mod d). Mais cela revient a remplacer")
    print(f"  3^k par x^S dans P_B, ce qui donne des puissances NEGATIVES")
    print(f"  de x (car B_j < S). C'est une serie de Laurent, pas un polynome.")


def test_B_wronskian(k_range=range(3, 11)):
    """
    Wronskien W(f,g) = f*g' - f'*g evalue en x=2.

    f = P_B(x), g = x^S - 3^k
    g'(x) = S*x^{S-1}

    W(2) = P_B(2) * S * 2^{S-1} - P_B'(2) * (2^S - 3^k)
         = corrSum * S * 2^{S-1} - P_B'(2) * d

    Si corrSum = m*d (cycle existe) :
    W(2) = m*d * S * 2^{S-1} - P_B'(2) * d
         = d * (m * S * 2^{S-1} - P_B'(2))

    -> W(2) est TOUJOURS divisible par d quand corrSum = 0 mod d.
    -> Le Wronskien est une COMBINAISON LINEAIRE de corrSum et d.
    -> Il ne contraint PAS corrSum.
    """
    print("\n" + "=" * 70)
    print("TEST B : LE WRONSKIEN W(P_B, x^S - 3^k)(2)")
    print("=" * 70)

    for k in k_range:
        S = math.ceil(k * math.log2(3)) + 1
        d = (1 << S) - 3**k
        if d <= 0:
            continue
        max_B = S - k
        C_comp = math.comb(S-1, k-1)
        if C_comp > 10000:
            continue

        # Calculer W(2) pour quelques compositions
        n_tested = 0
        n_W_neg = 0
        n_W_pos = 0
        n_W_zero_mod_d = 0
        n_cs_zero = 0

        for B in enumerate_monotone_B(k, max_B):
            n_tested += 1
            cs = corrSum_value(k, B)
            deriv = P_B_deriv_at_2(k, B)

            # W(2) = cs * S * 2^{S-1} - deriv * d
            W = cs * S * (1 << (S-1)) - deriv * d

            if W < 0:
                n_W_neg += 1
            elif W > 0:
                n_W_pos += 1

            if cs % d == 0:
                n_cs_zero += 1
                # Verifier W(2) mod d
                W_mod_d = W % d
                if W_mod_d == 0:
                    n_W_zero_mod_d += 1

            if n_tested <= 3:
                print(f"\n  k={k}, B={B}")
                print(f"    corrSum = {cs}")
                print(f"    P_B'(2) = {deriv}")
                print(f"    W(2) = {cs}*{S}*2^{S-1} - {deriv}*{d}")
                print(f"    W(2) = {W}")
                print(f"    W(2) {'< 0' if W < 0 else '>= 0'}")
                if cs % d == 0:
                    m = cs // d
                    inner = m * S * (1 << (S-1)) - deriv
                    print(f"    corrSum = {m} * d")
                    print(f"    W(2)/d = {inner}")

        print(f"\n  k={k}: {n_tested} compositions")
        print(f"    W(2) < 0 : {n_W_neg} ({100*n_W_neg/n_tested:.1f}%)")
        print(f"    W(2) > 0 : {n_W_pos} ({100*n_W_pos/n_tested:.1f}%)")
        print(f"    corrSum = 0 mod d : {n_cs_zero}")
        if n_cs_zero > 0:
            print(f"    W(2) = 0 mod d quand cs=0 mod d : {n_W_zero_mod_d}/{n_cs_zero}")

    print(f"\n  {'='*60}")
    print(f"  VERDICT TEST B :")
    print(f"  W(2) = corrSum * S * 2^{{S-1}} - P_B'(2) * d")
    print(f"  ")
    print(f"  FAIT 1 : W(2) est une combinaison lineaire de corrSum et d.")
    print(f"  FAIT 2 : Si corrSum = 0 mod d, alors W(2) = 0 mod d AUTOMATIQUEMENT.")
    print(f"  FAIT 3 : Le signe de W(2) ne contraint PAS corrSum mod d.")
    print(f"  ")
    print(f"  Le Wronskien est DERIVATIF de la condition corrSum = 0 mod d.")
    print(f"  Il ne contient AUCUNE information supplementaire.")


def test_C_sign_structure(k_range=range(3, 10)):
    """
    Le R165 affirme que Q(x) a des coefficients negatifs en haut degre
    et positifs en bas degre (heritage du MPF/anti-alignement).

    Mais Q(x) = 0 (test A). Si on interprete Q comme la fraction
    P_B(x)/(x^S - 3^k), c'est une fraction rationnelle, pas un polynome.

    Meme en forceant une definition differente, la structure de signe
    ne contraint PAS la divisibilite mod d (Principe d'Incompatibilite).
    """
    print("\n" + "=" * 70)
    print("TEST C : STRUCTURE DE SIGNE ET CONTRAINTE SUR corrSum")
    print("=" * 70)

    for k in k_range:
        S = math.ceil(k * math.log2(3)) + 1
        d = (1 << S) - 3**k
        if d <= 0:
            continue
        max_B = S - k
        C_comp = math.comb(S-1, k-1)
        if C_comp > 5000:
            continue

        # Le R165 dit : les coefficients de P_B sont decroissants (3^{k-1-j})
        # et les exposants sont croissants (B_j). C'est le MPF.
        # Mais cela a DEJA ETE TESTE en R160 : anti-alignement ne contraint pas mod d.

        # Test supplementaire : le Wronskien normalise W(2)/d
        # a-t-il une structure speciale quand corrSum = 0 mod p ?

        factors = factorint(d)
        for p in factors:
            if p > 200:
                continue

            W_over_p_when_cs_zero = []
            W_over_p_all = []

            for B in enumerate_monotone_B(k, max_B):
                cs = corrSum_value(k, B)
                deriv = P_B_deriv_at_2(k, B)
                W = cs * S * (1 << (S-1)) - deriv * d

                W_mod_p = W % p
                W_over_p_all.append(W_mod_p)

                if cs % p == 0:
                    W_over_p_when_cs_zero.append(W_mod_p)

            # Distribution de W mod p conditionnee a cs=0 mod p
            if W_over_p_when_cs_zero:
                n_zero = sum(1 for w in W_over_p_when_cs_zero if w == 0)
                print(f"\n  k={k}, p={p}")
                print(f"    #(cs=0 mod p) = {len(W_over_p_when_cs_zero)}")
                print(f"    #(W=0 mod p | cs=0) = {n_zero} ({100*n_zero/len(W_over_p_when_cs_zero):.1f}%)")
                print(f"    -> W=0 mod p AUTOMATIQUE quand cs=0 mod p ({100*n_zero/len(W_over_p_when_cs_zero):.0f}%)")
            break

    print(f"\n  {'='*60}")
    print(f"  VERDICT TEST C :")
    print(f"  W(2) = 0 mod p AUTOMATIQUEMENT quand corrSum = 0 mod p.")
    print(f"  La structure de signe du Wronskien/quotient ne contraint PAS la divisibilite.")
    print(f"  Le signe est une observable de Z -> Principe d'Incompatibilite.")


def test_D_comparison():
    """Comparaison avec pistes anterieures."""
    print("\n" + "=" * 70)
    print("TEST D : COMPARAISON AVEC PISTES ANTERIEURES")
    print("=" * 70)

    print("""
  INVENTAIRE :

  R141-R145 : Lifting p-adique ELIMINE
  R162/Voie B : Corps de fonctions / rebranding PRO
  R162/Voie C : Weierstrass / polygone plat
  R162/TPE : Uniformisateur / resultant plus faible
  R163 : Hensel direction inversee / E-K inexistant
  R164 : Taylor P_B(2+h) = Hensel / double relevement = erreur Z_p vs Z/dZ

  R165 (NOUVEAU) :
  1. Polynome quotient Q = P_B/(x^S-3^k)
     -> Q = 0 car deg(P_B) < deg(x^S-3^k)
     -> OBJET INEXISTANT

  2. Wronskien W(f,g)(2)
     -> W(2) = corrSum * S*2^{S-1} - P_B'(2)*d
     -> Combinaison lineaire de corrSum et d
     -> W(2) = 0 mod d quand corrSum = 0 mod d : AUTOMATIQUE
     -> Aucune info supplementaire

  3. Structure de signe
     -> Observable de Z -> Principe d'Incompatibilite
     -> DEJA TESTE R160 (MPF) : anti-alignement non exploitable

  4. Verrouillage differentiel
     -> W(2)/d est un entier quand corrSum = 0 mod d : trivial
     -> Le signe de cet entier ne contraint rien

  CONCLUSION : R165 = R164 + Wronskien (combinaison lineaire triviale)
  Le Wronskien n'apporte AUCUNE information au-dela de corrSum et d.

  CLASSIFICATION : Cadre p-adique recycle (R141-R145) +
                   structure de signe non exploitable (R160 MPF) +
                   Wronskien = combinaison lineaire triviale (NOUVEAU mais MORT)
""")


def test_E_k22():
    """Application a k=22."""
    print("\n" + "=" * 70)
    print("TEST E : APPLICATION A k=22")
    print("=" * 70)

    k = 22
    S = 35
    d = (1 << S) - 3**k
    factors = factorint(d)
    C_comp = math.comb(S-1, k-1)

    print(f"\n  k={k}, S={S}, d={d}")
    print(f"  d = {factors}")
    print(f"  C = {C_comp}")
    print(f"  deg(P_B) = S-k = {S-k} < S = {S}")
    print(f"  -> Polynome quotient Q = 0")
    print(f"  -> Wronskien W(2) = corrSum * {S} * 2^{S-1} - P_B'(2) * {d}")
    print(f"  -> Combinaison lineaire : rien de nouveau")
    print(f"  -> {C_comp} compositions : probleme intact")

    print(f"\n  {'='*60}")
    print(f"  VERDICT k=22 :")
    print(f"  Le R165 ne fournit rien d'exploitable.")
    print(f"  Polynome quotient = 0, Wronskien = combinaison lineaire triviale.")


def main():
    print("=" * 70)
    print("R165 - TEST DU LEVIER WRONSKIEN ET POLYNOME QUOTIENT")
    print("Protocole Fail-Closed")
    print("=" * 70)

    t0 = time.time()

    test_A_quotient_exists()
    test_B_wronskian()
    test_C_sign_structure()
    test_D_comparison()
    test_E_k22()

    elapsed = time.time() - t0

    print("\n" + "=" * 70)
    print("VERDICT GLOBAL - R165 WRONSKIEN ET QUOTIENT")
    print("=" * 70)
    print(f"""
  +================================================================+
  |  R165 = CADRE p-ADIQUE RECYCLE + OBJETS TRIVIAUX               |
  +================================================================+
  |                                                                  |
  |  A. Polynome quotient Q = P_B/(x^S-3^k)                        |
  |     deg(P_B) = S-k < S = deg(x^S-3^k)                          |
  |     -> Q = 0 (division euclidienne triviale)                     |
  |     -> L'objet central du R165 N'EXISTE PAS                     |
  |                                                                  |
  |  B. Wronskien W(P_B, x^S-3^k)(2)                               |
  |     = corrSum * S*2^{{S-1}} - P_B'(2) * d                        |
  |     -> COMBINAISON LINEAIRE de corrSum et d                      |
  |     -> W(2) = 0 mod d AUTOMATIQUEMENT quand corrSum = 0 mod d   |
  |     -> Aucune information supplementaire                         |
  |                                                                  |
  |  C. Structure de signe (MPF)                                     |
  |     -> Observable de Z, deja testee R160                         |
  |     -> Principe d'Incompatibilite : non exploitable              |
  |                                                                  |
  |  D. Verrouillage differentiel                                    |
  |     -> W(2)/d entier quand corrSum=0 : trivial (lineaire)       |
  |     -> Le signe ne contraint pas la divisibilite                 |
  |                                                                  |
  |  CLASSIFICATION : Cadre p-adique R141-R145 +                    |
  |                   MPF R160 + Wronskien trivial                   |
  |  NUMERO D'ECHEC : 252e piste fermee                             |
  +================================================================+

  Temps : {elapsed:.1f}s
""")

    results = {
        'verdict': 'MORT - Wronskien = combinaison lineaire triviale',
        'classification': 'Cadre p-adique R141-R145 + MPF R160 + objet trivial',
        'test_A': 'Polynome quotient Q = 0 (deg P_B < deg diviseur)',
        'test_B': 'Wronskien = combinaison lineaire de corrSum et d',
        'test_C': 'W=0 mod d automatique quand corrSum=0 mod d',
        'test_D': 'Recyclage R141-R145 + R160',
        'test_E': 'k=22 : rien d exploitable'
    }
    with open('/Users/ericmerle/Documents/Collatz-Junction-Theorem/research_log/R165_results.json', 'w') as f:
        json.dump(results, f, indent=2, ensure_ascii=False)

    print("  Resultats sauvegardes dans R165_results.json")


if __name__ == '__main__':
    main()
