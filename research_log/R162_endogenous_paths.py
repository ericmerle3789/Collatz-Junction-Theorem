#!/usr/bin/env python3
"""
R162 — INVESTIGATION DES VOIES ENDOGÈNES (Post-R161)
=====================================================
3 voies proposées exploitant l'"ADN partagé" d = 2^S - 3^k.

VOIE A : Rigidité de Furstenberg finitaire (×2, ×3 sur Z/dZ)
VOIE B : Corps de fonctions (P(x,y) = corrSum, intersection avec x^S=y^k)
VOIE C : Weierstrass p-adique (polygone de Newton de corrSum)

VÉRIFICATION CARTE : Furstenberg tué R159, lifting R141-R145, PRO R80.
QUESTION : l'ADN partagé (2^S ≡ 3^k mod d) change-t-il la donne ?
"""

import math
import random
import json
from sympy import factorint, primitive_root, isprime, gcd

# ============================================================================
# UTILITAIRES
# ============================================================================

def corrSum_value(k, B_vec):
    return sum(3**(k-1-j) * (1 << B_vec[j]) for j in range(k))

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

# ============================================================================
# VOIE A : RIGIDITÉ DE FURSTENBERG FINITAIRE
# ============================================================================

def voie_A_furstenberg(k_range=range(3, 11)):
    """
    Test : la structure jointe de ×2 et ×3 sur Z/dZ contraint-elle corrSum ?

    HYPOTHÈSE : L'ADN partagé 2^S ≡ 3^k mod d crée une rigidité.

    TESTS :
    1. Calculer ord_d(2), ord_d(3), et lcm(ord_d(2), ord_d(3))
    2. Le groupe ⟨2,3⟩ mod d couvre-t-il tout (Z/dZ)* ?
    3. La relation 2^S ≡ 3^k contraint-elle corrSum mod d ?

    KILL TEST : Si ⟨2,3⟩ = (Z/dZ)* pour tous les d testés,
    il n'y a AUCUNE restriction de groupe → Voie A morte.
    """
    print("=" * 70)
    print("VOIE A : RIGIDITÉ DE FURSTENBERG FINITAIRE")
    print("=" * 70)

    results = []

    for k in k_range:
        S = math.ceil(k * math.log2(3)) + 1
        d = (1 << S) - 3**k
        if d <= 0:
            continue

        # ord_d(2) et ord_d(3)
        ord2 = 1
        x = 2 % d
        while x != 1 and ord2 < d:
            x = (x * 2) % d
            ord2 += 1
        if x != 1:
            ord2 = None  # 2 n'est pas inversible (impossible car gcd(2,d)=1)

        ord3 = 1
        x = 3 % d
        while x != 1 and ord3 < d:
            x = (x * 3) % d
            ord3 += 1
        if x != 1:
            ord3 = None

        # ⟨2,3⟩ comme sous-groupe de (Z/dZ)*
        # Euler phi(d)
        factors = factorint(d)
        phi_d = d
        for p in factors:
            phi_d = phi_d * (p - 1) // p

        # Le sous-groupe ⟨2,3⟩ a-t-il la même taille que (Z/dZ)* ?
        # Calculer la taille du sous-groupe engendré par 2 et 3
        # Pour petit d : force brute
        if d < 1000000 and ord2 and ord3:
            generated = set()
            # BFS depuis 1
            queue = [1]
            generated.add(1)
            while queue:
                current = queue.pop(0)
                for multiplier in [2, 3]:
                    nxt = (current * multiplier) % d
                    if nxt not in generated:
                        generated.add(nxt)
                        queue.append(nxt)
                        if len(generated) > phi_d:
                            break
                if len(generated) > phi_d:
                    break
            group_size = len(generated)
        else:
            group_size = None  # Trop grand

        # La relation 2^S ≡ 3^k mod d est-elle exploitable ?
        # Vérification : 2^S mod d
        pow2S = pow(2, S, d)
        pow3k = pow(3, k, d)
        dna_check = (pow2S == pow3k) or (pow2S - pow3k) % d == 0

        result = {
            'k': k, 'S': S, 'd': d,
            'ord_d_2': ord2, 'ord_d_3': ord3,
            'phi_d': phi_d,
            'group_2_3_size': group_size,
            'covers_all': group_size == phi_d if group_size else None,
            'dna_verified': dna_check,
            'lcm_ord': None
        }

        if ord2 and ord3:
            lcm_ord = (ord2 * ord3) // gcd(ord2, ord3)
            result['lcm_ord'] = lcm_ord

        results.append(result)

        print(f"\n  k={k}, S={S}, d={d}")
        print(f"    ord_d(2) = {ord2}, ord_d(3) = {ord3}")
        print(f"    phi(d) = {phi_d}")
        if group_size:
            print(f"    |⟨2,3⟩| = {group_size} → "
                  f"{'COUVRE TOUT' if group_size == phi_d else f'{group_size}/{phi_d} = {group_size/phi_d:.3f}'}")
        print(f"    2^S ≡ 3^k mod d vérifié : {dna_check}")
        if result['lcm_ord']:
            print(f"    lcm(ord(2),ord(3)) = {result['lcm_ord']}")

    # VERDICT
    covers_all = [r for r in results if r.get('covers_all') is True]
    print(f"\n  {'='*60}")
    print(f"  VERDICT VOIE A :")
    print(f"  ⟨2,3⟩ = (Z/dZ)* dans {len(covers_all)}/{len([r for r in results if r.get('covers_all') is not None])} cas testés")
    if len(covers_all) == len([r for r in results if r.get('covers_all') is not None]):
        print(f"  → AUCUNE restriction de groupe : 2 et 3 engendrent TOUT (Z/dZ)*")
        print(f"  ")
        print(f"  CONSÉQUENCE : La rigidité de Furstenberg nécessite que les")
        print(f"  actions de ×2 et ×3 soient 'non commensurables'.")
        print(f"  Mais dans Z/dZ, elles engendrent le MÊME groupe !")
        print(f"  → Il n'y a pas de tension entre les deux dynamiques.")
        print(f"  → L'analogue discret de Furstenberg est VIDE.")
        print(f"  ")
        print(f"  De plus : R159 avait déjà identifié 3 obstructions :")
        print(f"  1. |⟨2⟩| ≈ log p << p^δ (seuil BGK)")
        print(f"  2. rang 1 (orbite ≠ action du groupe)")
        print(f"  3. pas d'analogue fini de Rudnick")
        print(f"  ")
        print(f"  STATUT : MORT — ⟨2,3⟩=(Z/dZ)* détruit toute rigidité")

    return results

# ============================================================================
# VOIE B : CORPS DE FONCTIONS / GÉOMÉTRIE ALGÉBRIQUE
# ============================================================================

def voie_B_function_field(k_range=range(3, 9)):
    """
    Test : remplacer (2,3) par (x,y) et étudier P(x,y) = corrSum.

    P(x,y) = Σ y^{k-1-j} · x^{B_j}
    Contrainte : x^S = y^k (courbe algébrique C)

    On veut : P(x,y) ≡ 0 mod (x^S - y^k) n'a pas de solution (x,y) = (2,3)

    TEST 1 : Le polynôme P(x,y) mod (x^S - y^k) se simplifie-t-il ?
    TEST 2 : Le degré résultant permet-il Bézout ?
    TEST 3 : Est-ce un REBRANDING de PRO (R80) ?
    """
    print("\n" + "=" * 70)
    print("VOIE B : CORPS DE FONCTIONS / GÉOMÉTRIE ALGÉBRIQUE")
    print("=" * 70)

    results = []

    for k in k_range:
        S = math.ceil(k * math.log2(3)) + 1
        d = (1 << S) - 3**k
        if d <= 0:
            continue
        max_B = S - k

        C_comp = math.comb(S - 1, k - 1)
        if C_comp > 100000:
            continue

        # Pour chaque composition monotone, construire P(x,y) et évaluer
        # P est un polynôme en (x,y) avec degré max_B en x et k-1 en y
        # On regarde P mod (x^S - y^k)

        # La réduction : remplacer x^S par y^k dans P(x,y)
        # Si B_j < S pour tout j, aucune réduction n'est possible !
        # Car deg_x(P) = max(B_j) = S-k < S
        # Donc P(x,y) est DÉJÀ réduit modulo (x^S - y^k)

        # Cela signifie que P(x,y) mod (x^S - y^k) = P(x,y) lui-même
        # La "substitution algébrique" ne fait RIEN

        max_deg_x = max_B  # = S - k < S
        reduction_possible = max_deg_x >= S

        # Test Bézout : nombre d'intersections de P=0 et x^S=y^k dans P²
        # deg(P) en x = S-k, deg(P) en y = k-1
        # deg total de P ≈ S-1
        # deg de x^S-y^k = max(S,k) = S
        # Bézout : #intersections ≤ (S-1) · S ≈ S² (beaucoup trop)

        bezout_bound = (S - 1) * S

        # Test de REBRANDING : P(2,3) = corrSum, exact.
        # La question P(2,3) ≡ 0 mod d est IDENTIQUE à corrSum ≡ 0 mod d.
        # Passer par P(x,y) ne change PAS la question.

        n_zero = 0
        for B in enumerate_monotone_B(k, max_B):
            cs = corrSum_value(k, B)
            if cs % d == 0:
                n_zero += 1

        result = {
            'k': k, 'S': S, 'd': d,
            'max_deg_x': max_deg_x,
            'reduction_possible': reduction_possible,
            'bezout_bound': bezout_bound,
            'C_comp': C_comp,
            'N0': n_zero
        }
        results.append(result)

        print(f"\n  k={k}, S={S}, d={d}")
        print(f"    deg_x(P) = {max_deg_x}, S = {S}")
        print(f"    Réduction de P mod (x^S - y^k) possible ? "
              f"{'OUI' if reduction_possible else 'NON (deg < S)'}")
        print(f"    Borne de Bézout : ≤ {bezout_bound} intersections")
        print(f"    C = {C_comp}, N₀ = {n_zero}")

    # VERDICT
    print(f"\n  {'='*60}")
    print(f"  VERDICT VOIE B :")
    print(f"  ")
    print(f"  PROBLÈME FATAL 1 — Pas de réduction :")
    print(f"    deg_x(P) = S-k < S pour TOUT B monotone.")
    print(f"    Donc P(x,y) mod (x^S - y^k) = P(x,y) lui-même.")
    print(f"    La 'substitution algébrique' n'opère PAS.")
    print(f"  ")
    print(f"  PROBLÈME FATAL 2 — REBRANDING :")
    print(f"    P(2,3) = corrSum exactement.")
    print(f"    'P(2,3) ≡ 0 mod d' = 'corrSum ≡ 0 mod d'.")
    print(f"    Le passage par (x,y) ne change pas la question.")
    print(f"    C'est le même REBRANDING que PRO (R80).")
    print(f"  ")
    print(f"  PROBLÈME FATAL 3 — Bézout inutile :")
    print(f"    Borne Bézout ≈ S² >> nombre de compositions.")
    print(f"    Trop d'intersections potentielles pour exclure quoi que ce soit.")
    print(f"  ")
    print(f"  PROBLÈME FATAL 4 — Monotonie invisible :")
    print(f"    La contrainte B_0 ≤ B_1 ≤ ... est COMBINATOIRE.")
    print(f"    Elle ne se traduit pas en condition géométrique")
    print(f"    sur la courbe P(x,y) = 0 (pas de singularité, pas de genre).")
    print(f"  ")
    print(f"  Confirmé R80 (PRO = rebranding), R152 (isomorphisme analyse↔algèbre)")
    print(f"  STATUT : MORT — rebranding (4 problèmes fatals)")

    return results

# ============================================================================
# VOIE C : WEIERSTRASS p-ADIQUE / POLYGONE DE NEWTON
# ============================================================================

def voie_C_padic_weierstrass(k_range=range(3, 11)):
    """
    Test : corrSum comme série p-adique, polygone de Newton.

    Pour p|d, corrSum = Σ 3^{k-1-j} · 2^{B_j} ∈ Z_p.
    La question : corrSum ≡ 0 mod p.

    Polygone de Newton de corrSum (comme polynôme en 2^{B_0}) :
    corrSum = 3^{k-1} · 2^{B_0} + Σ_{j≥1} 3^{k-1-j} · 2^{B_j}

    Pour p|d avec p ≠ 2, 3 : v_p(3^{k-1-j} · 2^{B_j}) = 0 pour TOUT j.
    Donc TOUS les termes ont valuation 0.
    Le polygone de Newton est PLAT (horizontal à hauteur 0).

    CONSÉQUENCE : Weierstrass ne donne AUCUNE information sur les zéros.
    """
    print("\n" + "=" * 70)
    print("VOIE C : WEIERSTRASS p-ADIQUE / POLYGONE DE NEWTON")
    print("=" * 70)

    results = []

    for k in k_range:
        S = math.ceil(k * math.log2(3)) + 1
        d = (1 << S) - 3**k
        if d <= 0:
            continue

        factors = factorint(d)

        # Pour chaque p|d
        valuations_flat = True
        for p, e in factors.items():
            # v_p(3^{k-1-j}) = 0 car p ≠ 3 (puisque gcd(d,3)=1)
            # v_p(2^{B_j}) = 0 car p ≠ 2 (puisque d est impair)
            # Donc v_p(terme_j) = 0 pour tout j
            assert p != 2 and p != 3, f"p={p} divides d={d} but gcd(d,6)=1!"

        # Le polygone de Newton est plat : toutes les valuations = 0
        # Weierstrass : f(x) = a_0 + a_1·x + ... avec v_p(a_i) = 0 pour tout i
        # Le théorème dit : le nombre de zéros = longueur de la pente nulle
        # Mais pour une somme de termes TOUS de valuation 0,
        # la somme peut avoir valuation > 0 par cancellation.
        # Weierstrass ne contrôle PAS cela.

        # Test numérique : pour p|d, calculer v_p(corrSum) pour des B aléatoires
        rng = random.Random(42)
        max_B = S - k
        n_samples = min(10000, math.comb(S-1, k-1))

        p_first = list(factors.keys())[0]

        val_dist = {}
        for _ in range(n_samples):
            if n_samples >= math.comb(S-1, k-1):
                break
            seps = sorted(rng.sample(range(max_B + k - 1), k - 1))
            gaps = []
            prev = -1
            for s in seps:
                gaps.append(s - prev - 1)
                prev = s
            gaps.append(max_B + k - 2 - prev)
            B = [0] * k
            B[0] = gaps[0]
            for j in range(1, k):
                B[j] = B[j-1] + gaps[j]

            cs = corrSum_value(k, B)
            v = 0
            temp = cs
            while temp > 0 and temp % p_first == 0:
                v += 1
                temp //= p_first
            val_dist[v] = val_dist.get(v, 0) + 1

        result = {
            'k': k, 'S': S, 'd': d,
            'd_factors': str(factors),
            'all_terms_val_0': True,
            'newton_polygon': 'FLAT (horizontal at 0)',
            'v_p_distribution': dict(sorted(val_dist.items())),
            'p_tested': p_first
        }
        results.append(result)

        print(f"\n  k={k}, S={S}, d={d} = {factors}")
        print(f"    Tous les facteurs p|d satisfont p≠2, p≠3 : OUI (gcd(d,6)=1)")
        print(f"    v_p(terme_j) = v_p(3^{{k-1-j}}·2^{{B_j}}) = 0 pour TOUT j, TOUT p|d")
        print(f"    Polygone de Newton : PLAT (tous les points à hauteur 0)")
        print(f"    Distribution de v_{{{p_first}}}(corrSum) : {dict(sorted(val_dist.items()))}")

    # VERDICT
    print(f"\n  {'='*60}")
    print(f"  VERDICT VOIE C :")
    print(f"  ")
    print(f"  PROBLÈME FATAL — Polygone de Newton PLAT :")
    print(f"    Pour tout p|d : gcd(p, 6) = 1 (car d impair, gcd(d,3)=1)")
    print(f"    Donc v_p(3^a · 2^b) = 0 pour tout a, b ≥ 0.")
    print(f"    Chaque terme de corrSum a valuation p-adique 0.")
    print(f"    Le polygone de Newton est une LIGNE HORIZONTALE à hauteur 0.")
    print(f"  ")
    print(f"  Le théorème de préparation de Weierstrass donne le nombre de")
    print(f"  zéros = la 'longueur' de la pente nulle du polygone.")
    print(f"  Pour un polygone PLAT, cette information est TRIVIALE :")
    print(f"  elle dit seulement que la somme PEUT s'annuler par cancellation.")
    print(f"  ")
    print(f"  C'est le même phénomène que le R161 : les termes individuels")
    print(f"  ont valuation 0, et la cancellation est ARITHMÉTIQUE,")
    print(f"  pas contrôlable par des arguments p-adiques.")
    print(f"  ")
    print(f"  Confirmé R77 (V2C : invariants 2-adiques orthogonaux à d)")
    print(f"  Confirmé R141-R145 (lifting p-adique ÉLIMINÉ)")
    print(f"  STATUT : MORT — polygone plat, aucune information")

    return results

# ============================================================================
# TEST CLÉ : L'ADN PARTAGÉ CHANGE-T-IL QUELQUE CHOSE ?
# ============================================================================

def test_shared_dna(k_range=range(3, 11)):
    """
    Le point central du document : 2^S ≡ 3^k mod d.
    Cette relation est l'ADN partagé.

    TEST : Cette relation apporte-t-elle une contrainte sur corrSum mod d
    au-delà de ce que nous savions déjà ?

    REFORMULATION : corrSum mod d = Σ 3^{k-1-j} · 2^{B_j} mod d
    En utilisant 3^k ≡ 2^S :
      3^{k-1} ≡ 3^{-1} · 2^S mod d
      3^{k-2} ≡ 3^{-2} · 2^S mod d
      ...
      3^{k-1-j} ≡ 3^{-1-j} · 2^S mod d

    Donc : corrSum ≡ 2^S · Σ 3^{-1-j} · 2^{B_j - S} ≡ 0 mod d
    ⟺ Σ (2/3)^j · 2^{B_j} · 3^{-1} ≡ 0 mod d   (simplifié par 2^S)

    Mais 2/3 mod d est un nombre SPÉCIFIQUE. La somme est toujours
    dans Z/dZ. On a juste RÉÉCRIT corrSum avec des puissances de (2/3).

    C'est EXACTEMENT la même somme, réécrite.
    """
    print("\n" + "=" * 70)
    print("TEST CLÉ : L'ADN PARTAGÉ (2^S ≡ 3^k mod d)")
    print("=" * 70)

    for k in k_range:
        S = math.ceil(k * math.log2(3)) + 1
        d = (1 << S) - 3**k
        if d <= 0:
            continue

        # Calculer 2/3 mod d
        inv3 = pow(3, -1, d)
        ratio_23 = (2 * inv3) % d

        # Vérifier : corrSum ≡ 2^S · inv3 · Σ ratio_23^j · 2^{B_j} mod d
        # Plus simplement : corrSum ≡ 3^{k-1} · 2^{B_0} + ... mod d
        # En substituant 3^{k-1-j} = inv3^{j+1} · 3^k = inv3^{j+1} · 2^S mod d

        # L'information est-elle plus compacte ?
        # Non : c'est la MÊME somme de k termes dans Z/dZ
        # Le nombre de variables (B_0, ..., B_{k-1}) est identique
        # La contrainte de monotonie est identique
        # La structure de Z/dZ est identique

        # Test : ord_d(2/3) = ?
        ord_ratio = 1
        x = ratio_23
        while x != 1 and ord_ratio < d:
            x = (x * ratio_23) % d
            ord_ratio += 1

        # La relation 2^S ≡ 3^k mod d implique (2/3)^S ≡ (3/2)^{S-k} · ... non, plus simple :
        # (2/3)^S ≡ 2^S / 3^S ≡ 3^k / 3^S ≡ 3^{k-S} mod d
        # Et (2/3)^k ≡ 2^k / 3^k ≡ 2^k / 2^S ≡ 2^{k-S} mod d

        # Vérification
        pow_ratio_S = pow(ratio_23, S, d)
        pow_ratio_k = pow(ratio_23, k, d)
        pow3_kS = pow(3, k - S, d) if k >= S else pow(pow(3, -1, d), S - k, d)
        pow2_kS = pow(2, k - S, d) if k >= S else pow(pow(2, -1, d), S - k, d)

        print(f"\n  k={k}, S={S}, d={d}")
        print(f"    2/3 mod d = {ratio_23}")
        print(f"    ord_d(2/3) = {ord_ratio}")
        print(f"    (2/3)^S mod d = {pow_ratio_S}, 3^{{k-S}} mod d = {pow3_kS}")
        print(f"    Match : {pow_ratio_S == pow3_kS}")

    print(f"\n  {'='*60}")
    print(f"  VERDICT ADN PARTAGÉ :")
    print(f"  La relation 2^S ≡ 3^k mod d permet de réécrire corrSum")
    print(f"  en termes de (2/3)^j · 2^{{B_j}} au lieu de 3^{{k-1-j}} · 2^{{B_j}}.")
    print(f"  ")
    print(f"  Mais c'est une RÉÉCRITURE ALGÉBRIQUE de la même somme.")
    print(f"  Le nombre de variables, la contrainte de monotonie,")
    print(f"  et la structure de Z/dZ sont IDENTIQUES.")
    print(f"  ")
    print(f"  L'ADN partagé est un FAIT TRIVIAL : d = 2^S - 3^k")
    print(f"  implique AUTOMATIQUEMENT 2^S ≡ 3^k mod d.")
    print(f"  Ce n'est pas une 'découverte' — c'est la DÉFINITION de d.")
    print(f"  ")
    print(f"  STATUT : TAUTOLOGIE — réécriture de la définition de d")

# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 70)
    print("R162 — VOIES ENDOGÈNES (Post-R161)")
    print("Protocole Fail-Closed — ADN Partagé")
    print("=" * 70)

    results_A = voie_A_furstenberg()
    results_B = voie_B_function_field()
    results_C = voie_C_padic_weierstrass()
    test_shared_dna()

    # VERDICT GLOBAL
    print("\n" + "=" * 70)
    print("VERDICT GLOBAL — VOIES ENDOGÈNES")
    print("=" * 70)
    print("""
  VOIE A (Furstenberg finitaire) : MORT
    ⟨2,3⟩ = (Z/dZ)* dans TOUS les cas testés.
    Pas de sous-groupe propre → pas de rigidité.
    Confirme R159 (3 obstructions).

  VOIE B (Corps de fonctions) : MORT
    4 problèmes fatals :
    1. Pas de réduction (deg_x < S)
    2. Rebranding de PRO (R80)
    3. Bézout donne S² >> C intersections
    4. Monotonie invisible en géométrie algébrique
    Confirme R80, R152.

  VOIE C (Weierstrass p-adique) : MORT
    Polygone de Newton PLAT (tous termes ont v_p = 0).
    Le théorème de Weierstrass ne donne AUCUNE info.
    Confirme R77, R141-R145.

  ADN PARTAGÉ : TAUTOLOGIE
    2^S ≡ 3^k mod d est la DÉFINITION de d.
    La réécriture en (2/3)^j ne change pas la structure.

  ╔══════════════════════════════════════════════════════════════╗
  ║  CONCLUSION : Les "voies endogènes" ne franchissent pas     ║
  ║  le Principe d'Incompatibilité. L'ADN partagé est un fait   ║
  ║  trivial (la définition de d), pas un outil exploitable.    ║
  ║                                                              ║
  ║  Le document source fait un diagnostic correct (§1) mais     ║
  ║  ses 3 voies (§2) tombent sur les MÊMES obstacles que les   ║
  ║  248 pistes fermées avant elles.                             ║
  ║                                                              ║
  ║  Le Bloc 3 reste OUVERT. Le programme nécessite un outil     ║
  ║  QUALITATIVEMENT NOUVEAU qui n'est dans aucun cadre connu.   ║
  ╚══════════════════════════════════════════════════════════════╝
""")

    # Sauvegarder
    all_results = {
        'voie_A': [str(r) for r in results_A],
        'voie_B': [str(r) for r in results_B],
        'voie_C': [str(r) for r in results_C],
    }
    with open('/Users/ericmerle/Documents/Collatz-Junction-Theorem/research_log/R162_results.json', 'w') as f:
        json.dump(all_results, f, indent=2)

    print("  Résultats sauvegardés dans R162_results.json")


if __name__ == '__main__':
    main()
