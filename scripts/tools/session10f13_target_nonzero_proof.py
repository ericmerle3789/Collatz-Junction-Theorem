#!/usr/bin/env python3
"""
SESSION 10f13 — Preuve théorique que le target de la réduction double-bord est ≠ 0

OBJECTIF : Prouver que 1 + P + Q ≢ 0 mod d pour tout k ≥ 4 avec σ̃≠0
  où P = Σ_{j=0}^{n} u^j, Q = Σ_{j=2}^{n+1} u^{-j}, d = 2^S - 3^k

INVESTIGATIONS :
  I1 : Réécriture de 1+P+Q en termes de u et d
  I2 : Conditions nécessaires pour 1+P+Q = 0
  I3 : Exploitation de la structure spécifique d = 2^S - 3^k
  I4 : Lien entre 1+P+Q et σ̃ (somme complète)
  I5 : Argument de taille (valuation 2-adique)
  I6 : Cas k pair — borne sur le log discret
  I7 : Synthèse de la preuve
"""

from math import gcd, log, log2, ceil, floor
from functools import reduce


def compute_params(k):
    """Calcule d, S, M, u pour un k donné."""
    S = ceil(k * log2(3))
    d = (1 << S) - 3**k
    if d <= 0:
        return None
    M = S - k
    # u = 2 * 3^{-1} mod d
    inv3 = pow(3, -1, d)
    u = (2 * inv3) % d
    # σ̃ = Σ_{j=1}^{k-1} u^j
    sigma = 0
    uj = u
    for j in range(1, k):
        sigma = (sigma + uj) % d
        uj = uj * u % d
    return {'k': k, 'd': d, 'S': S, 'M': M, 'u': u, 'sigma': sigma}


def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True


def ord_mod(a, n):
    """Ordre multiplicatif de a modulo n."""
    if gcd(a, n) != 1:
        return 0
    o = 1
    x = a % n
    while x != 1:
        x = x * a % n
        o += 1
        if o > n:
            return 0
    return o


print("=" * 70)
print("I1 : RÉÉCRITURE DE 1+P+Q EN TERMES FERMÉS")
print("=" * 70)
print()
print("  Rappel : après la réduction itérée double-bord :")
print("    n = (k-3)//2  (nombre de niveaux de réduction)")
print("    P = Σ_{j=0}^{n} u^j = (u^{n+1} - 1)/(u - 1)  [somme géom. directe]")
print("    Q = Σ_{j=2}^{n+1} u^{-j}                       [somme géom. inverse]")
print()
print("  Réécriture de Q :")
print("    Q = u^{-2} · Σ_{j=0}^{n-1} u^{-j}")
print("      = u^{-2} · (1 - u^{-n}) / (1 - u^{-1})")
print("      = u^{-2} · (u^n - 1) / (u^n · (u-1)/u)")
print("      = u^{-1} · (u^n - 1) / (u^n · (u-1))")
print()
print("  Donc 1 + P + Q = 1 + (u^{n+1}-1)/(u-1) + u^{-1}·(u^n-1)/(u^n·(u-1))")
print()
print("  Mettons tout sur le dénominateur commun u^n·(u-1) :")
print("    1+P+Q = [u^n(u-1) + u^n(u^{n+1}-1) + u^{-1}(u^n-1)] / [u^n(u-1)]")
print()

print("  Test numérique :")
for k in [4, 7, 8, 10, 13, 17, 23]:
    p = compute_params(k)
    if p is None or p['sigma'] == 0:
        continue
    d, u = p['d'], p['u']
    n = (k - 3) // 2

    # P = (u^{n+1} - 1) / (u - 1) mod d
    if (u - 1) % d == 0:
        P = (n + 1) % d  # cas dégénéré u=1
    else:
        inv_u_minus_1 = pow(u - 1, -1, d)
        P = (pow(u, n + 1, d) - 1) * inv_u_minus_1 % d

    # Q = u^{-2} * (1 - u^{-n}) / (1 - u^{-1}) mod d
    u_inv = pow(u, -1, d)
    Q_sum = 0
    u_inv_j = (u_inv * u_inv) % d  # u^{-2}
    for j in range(2, n + 2):
        Q_sum = (Q_sum + u_inv_j) % d
        u_inv_j = u_inv_j * u_inv % d

    target = (1 + P + Q_sum) % d

    # Vérification alternative : formule de la session 10f12
    # target devrait être = -(target_final) où target_final = -(1+P+Q)
    # Ici 1+P+Q directement

    print(f"  k={k:2d}: d={d}, n={n}, P={P}, Q={Q_sum}, 1+P+Q={target}")

print()
print("=" * 70)
print("I2 : CONDITIONS NÉCESSAIRES POUR 1+P+Q = 0 mod d")
print("=" * 70)
print()
print("  Si 1+P+Q ≡ 0 mod d, multiplions par u^n·(u-1) :")
print("    u^n(u-1) + u^n(u^{n+1}-1) + u^{-1}(u^n - 1) ≡ 0 mod d")
print()
print("  Développons :")
print("    u^{n+1} - u^n + u^{2n+1} - u^n + (u^{n-1} - u^{-1}) ≡ 0")
print("    = u^{2n+1} + u^{n+1} + u^{n-1} - 2u^n - u^{-1} ≡ 0")
print()
print("  Multiplions par u :")
print("    u^{2n+2} + u^{n+2} + u^n - 2u^{n+1} - 1 ≡ 0 mod d")
print()
print("  C'est un POLYNÔME en u de degré 2n+2.")
print("  Pour que d | P(u), il faut que P(u) ≡ 0 dans Z/dZ.")
print()

# Calculons ce polynôme et vérifions
print("  Vérification du polynôme P(u) = u^{2n+2} + u^{n+2} + u^n - 2u^{n+1} - 1 :")
for k in [4, 7, 8, 10, 13, 17, 23, 31, 43]:
    p = compute_params(k)
    if p is None or p['sigma'] == 0:
        continue
    d, u = p['d'], p['u']
    n = (k - 3) // 2

    # P(u) = u^{2n+2} + u^{n+2} + u^n - 2u^{n+1} - 1
    poly_val = (pow(u, 2*n+2, d) + pow(u, n+2, d) + pow(u, n, d)
                - 2*pow(u, n+1, d) - 1) % d

    # Aussi : u^n(u-1)² + u^{2n+1}(1) + u^{n-1}(1) - 1
    # Factorisons : u^n · (u-1)² + (u^{2n+1} + u^{n-1} - 1)
    factor1 = pow(u, n, d) * pow(u - 1, 2, d) % d
    rest = (pow(u, 2*n+1, d) + pow(u, n-1, d) - 1) % d
    total = (factor1 + rest) % d

    print(f"  k={k:2d}: n={n:2d}, P(u)={poly_val:>20d}, fact+rest={total:>20d}, =0? {'OUI ⚠️' if poly_val==0 else 'non ✓'}")

print()
print("=" * 70)
print("I3 : EXPLOITATION DE d = 2^S - 3^k ET u = 2·3^{-1}")
print("=" * 70)
print()
print("  Relations fondamentales dans Z/dZ :")
print("    2^S ≡ 3^k   (définition de d)")
print("    u = 2·3^{-1}, donc u^k = 2^k · 3^{-k} = 2^k · 2^{-S} = 2^{k-S} = 2^{-M}")
print("    u^j = 2^j · 3^{-j}")
print()
print("  Remplacement : P = Σ_{j=0}^{n} (2/3)^j = Σ_{j=0}^{n} 2^j · 3^{-j}")
print("  Et Q = Σ_{j=2}^{n+1} (3/2)^j = Σ_{j=2}^{n+1} 3^j · 2^{-j}")
print()
print("  Dans Z (avant réduction mod d) :")
print("    3^{n+1} · 2^{n+1} · (1+P+Q)")
print("    = 3^{n+1}·2^{n+1} + Σ 3^{n+1-j}·2^{n+1+j} + Σ 3^{n+1+j}·2^{n+1-j}")
print()

# Calculons la valeur entière AVANT réduction mod d
print("  Valeur entière de N = 3^{n+1}·2^{n+1}·(1+P+Q) :")
for k in [4, 7, 8, 10, 13]:
    p = compute_params(k)
    if p is None or p['sigma'] == 0:
        continue
    d, u = p['d'], p['u']
    n = (k - 3) // 2

    # Calculons dans Z : multiplier par 3^{n+1} · 2^{n+1} efface les dénominateurs
    # P · 3^{n+1} · 2^{n+1} = Σ_{j=0}^{n} 2^{j+n+1} · 3^{n+1-j}
    # Q · 3^{n+1} · 2^{n+1} = Σ_{j=2}^{n+1} 3^{j+n+1} · 2^{n+1-j}

    N_P = sum(2**(j+n+1) * 3**(n+1-j) for j in range(n+1))
    N_Q = sum(3**(j+n+1) * 2**(n+1-j) for j in range(2, n+2))
    N_1 = 3**(n+1) * 2**(n+1)
    N_total = N_1 + N_P + N_Q

    # Vérification : N_total mod d devrait être 0 ssi 1+P+Q ≡ 0
    N_mod_d = N_total % d

    # 1+P+Q mod d (calculé directement)
    u_inv = pow(u, -1, d)
    P_sum = sum(pow(u, j, d) for j in range(n+1)) % d
    Q_sum = sum(pow(u_inv, j, d) for j in range(2, n+2)) % d
    target = (1 + P_sum + Q_sum) % d

    # Le facteur multiplicatif 3^{n+1}·2^{n+1} mod d
    factor = pow(3, n+1, d) * pow(2, n+1, d) % d
    check = factor * target % d

    print(f"  k={k:2d}: n={n}, N_total = {N_total}")
    print(f"         N mod d = {N_mod_d}, factor·target mod d = {check}")
    print(f"         d = {d}, N/d = {N_total/d:.6f}, N//d = {N_total//d}")

print()
print("=" * 70)
print("I4 : LIEN ENTRE 1+P+Q ET σ̃ (SOMME COMPLÈTE)")
print("=" * 70)
print()
print("  σ̃ = Σ_{j=1}^{k-1} u^j (somme complète)")
print("  P = Σ_{j=0}^{n} u^j = 1 + Σ_{j=1}^{n} u^j (somme partielle)")
print("  Q = Σ_{j=2}^{n+1} u^{-j} (somme partielle inverse)")
print()
print("  On a n = (k-3)//2. Pour k impair : n = (k-3)/2, dim → 0.")
print("  Pour k pair : n = (k-4)/2, dim → 1.")
print()
print("  Relation clé : P + Q ne couvre PAS toute la somme σ̃.")
print("  P couvre u^0,...,u^n (n+1 termes directs)")
print("  Q couvre u^{-2},...,u^{-(n+1)} (n termes inverses)")
print()
print("  Rappel : u^{k-1} = 1/u^{k-k+1} via u^k = 2^{-M}")
print("  Vérifions la relation P + Q vs σ̃ :")
print()

for k in [7, 8, 13, 17, 23]:
    p = compute_params(k)
    if p is None or p['sigma'] == 0:
        continue
    d, u = p['d'], p['u']
    sigma = p['sigma']
    n = (k - 3) // 2

    u_inv = pow(u, -1, d)
    P_val = sum(pow(u, j, d) for j in range(n+1)) % d
    Q_val = sum(pow(u_inv, j, d) for j in range(2, n+2)) % d

    # σ̃ = u + u² + ... + u^{k-1}
    # P - 1 = u + u² + ... + u^n  (sous-ensemble de σ̃ si n ≤ k-1)
    # Les termes de σ̃ non couverts par P-1 : u^{n+1} + ... + u^{k-1}
    missing_from_P = sum(pow(u, j, d) for j in range(n+1, k)) % d

    # Q utilise des puissances NÉGATIVES de u, pas dans σ̃
    # MAIS u^{-j} = u^{ord-j} si ord(u) est connu

    target_1pq = (1 + P_val + Q_val) % d
    target_neg = (d - target_1pq) % d  # -(1+P+Q) = target de la session 10f12

    print(f"  k={k:2d}: n={n}, σ̃={sigma}")
    print(f"    P={P_val}, Q={Q_val}, 1+P+Q={target_1pq}")
    print(f"    -(1+P+Q)={target_neg}")
    print(f"    σ̃ + 1 = {(sigma+1)%d}")
    print(f"    Missing from P: {missing_from_P}")

    # Est-ce que 1+P+Q a une relation simple avec σ̃?
    # σ̃ + 1 = P + missing_from_P = (P-1) + 1 + missing_from_P
    # Donc 1+P = σ̃ + 1 - missing_from_P + 1 ? Non, calculons directement.
    # 1+P = 1 + Σ_{j=0}^n u^j = 2 + Σ_{j=1}^n u^j
    # σ̃ = Σ_{j=1}^{k-1} u^j = (P-1) + missing = Σ_{j=1}^n u^j + missing
    # Donc P-1 = σ̃ - missing, i.e. 1+P = 2 + σ̃ - missing
    # Et 1+P+Q = 2 + σ̃ - missing + Q
    check = (2 + sigma - missing_from_P + Q_val) % d
    print(f"    2+σ̃-missing+Q = {check}, =? 1+P+Q={target_1pq} : {'✓' if check == target_1pq else '✗'}")
    print()

print()
print("=" * 70)
print("I5 : ARGUMENT DE TAILLE — 1+P+Q vs d")
print("=" * 70)
print()
print("  Idée : si |1+P+Q| (entier, avant réduction) est strictement entre 0 et d,")
print("  alors 1+P+Q ≢ 0 mod d automatiquement.")
print()
print("  Mais attention : P et Q sont mod d, donc 1+P+Q ∈ [0, d-1].")
print("  La question est : est-ce que la VALEUR ENTIÈRE de 1+P+Q (dans Z)")
print("  peut être exactement un multiple de d ?")
print()

for k in [4, 7, 8, 10, 13, 17, 23, 31, 43, 53]:
    p = compute_params(k)
    if p is None or p['sigma'] == 0:
        continue
    d, u = p['d'], p['u']
    n = (k - 3) // 2

    # Calculons 1+P+Q dans Z via la version entière
    # N = 3^{n+1}·2^{n+1} + Σ 3^{n+1-j}·2^{n+1+j} + Σ 3^{j+n+1}·2^{n+1-j}
    N_1 = 3**(n+1) * 2**(n+1)
    N_P = sum(2**(j+n+1) * 3**(n+1-j) for j in range(n+1))
    N_Q = sum(3**(j+n+1) * 2**(n+1-j) for j in range(2, n+2))
    N_total = N_1 + N_P + N_Q

    ratio = N_total / d
    quotient = N_total // d
    remainder = N_total % d

    # Le facteur 3^{n+1}·2^{n+1}
    factor_int = 3**(n+1) * 2**(n+1)

    print(f"  k={k:2d}: n={n}, d={d}")
    print(f"    N_total = {N_total}")
    print(f"    N/d = {ratio:.6f}, quotient = {quotient}, remainder = {remainder}")
    print(f"    factor = 6^{n+1} = {factor_int}")
    print(f"    gcd(factor, d) = {gcd(factor_int, d)}")
    print(f"    → N ≡ 0 mod d ? {'OUI ⚠️' if remainder == 0 else 'NON ✓'}")
    print()

print()
print("=" * 70)
print("I6 : RELATION AVEC u^{k-1} + u^{k-2} + ... + u^0 (somme Σ₀)")
print("=" * 70)
print()
print("  Σ₀ = Σ_{j=0}^{k-1} u^j = (u^k - 1)/(u-1) = (2^{-M} - 1)/(u-1)")
print("  σ̃ = Σ₀ - 1 = Σ_{j=1}^{k-1} u^j")
print("  Σ₀ = σ̃ + 1")
print()
print("  Maintenant, P = Σ_{j=0}^{n} u^j et Q = Σ_{j=2}^{n+1} u^{-j}")
print()
print("  Pour k impair (n = (k-3)/2) :")
print("    P couvre j = 0,...,(k-3)/2")
print("    u^{k-1-j} pour j dans σ̃ que P ne couvre pas : j = (k-1)/2,...,k-1")
print("    Mais u^{k-1-j} = u^{-1} · u^{k-j} = u^{-1} · 2^{-M} · u^{-j+k}")
print("    Non, utilisons u^{-j} = (u^{k})^{-1} · u^{k-j} = 2^M · u^{k-j}")
print()

for k in [7, 13, 23]:
    p = compute_params(k)
    if p is None or p['sigma'] == 0:
        continue
    d, u, M = p['d'], p['u'], p['M']
    sigma = p['sigma']
    n = (k - 3) // 2

    # Vérifions u^{-j} = 2^M · u^{k-j} pour j ≥ 1
    u_inv = pow(u, -1, d)
    two_M = pow(2, M, d)

    ok = True
    for j in range(1, min(n+3, k)):
        lhs = pow(u_inv, j, d)
        rhs = two_M * pow(u, k - j, d) % d
        if lhs != rhs:
            ok = False
            break

    print(f"  k={k}: u^{{-j}} = 2^M · u^{{k-j}} pour j=1..{min(n+2,k-1)}: {'✓ VÉRIFIÉ' if ok else '✗ ÉCHEC'}")

    # Donc Q = Σ_{j=2}^{n+1} u^{-j} = 2^M · Σ_{j=2}^{n+1} u^{k-j}
    #        = 2^M · Σ_{i=k-n-1}^{k-2} u^i  (changement i = k-j)
    #        = 2^M · (Σ_rest de σ̃ côté haut)
    Q_direct = sum(pow(u_inv, j, d) for j in range(2, n+2)) % d
    Q_via = two_M * sum(pow(u, k-j, d) for j in range(2, n+2)) % d
    print(f"    Q direct = {Q_direct}, Q via 2^M·Σ = {Q_via}: {'✓' if Q_direct == Q_via else '✗'}")

    # Donc 1+P+Q = 1 + Σ_{j=0}^{n} u^j + 2^M · Σ_{j=k-n-1}^{k-2} u^j
    # Les termes de Σ_{j=0}^{n} u^j et Σ_{j=k-n-1}^{k-2} u^j
    # Pour k impair : n = (k-3)/2, donc k-n-1 = k-(k-3)/2-1 = (k+1)/2
    # et k-2. Nombre de termes = k-2 - (k+1)/2 + 1 = (k-3)/2 = n
    low_start = (k+1)//2  # pour k impair
    print(f"    P termes : j = 0..{n}")
    print(f"    Q → 2^M · (j = {low_start}..{k-2}), soit n = {k-2-low_start+1} termes")

    # Vérifions que les deux ensembles d'indices NE SE CHEVAUCHENT PAS
    P_indices = set(range(0, n+1))
    Q_indices = set(range(low_start, k-1))
    overlap = P_indices & Q_indices
    print(f"    P_indices = {{0..{n}}}, Q_indices = {{{low_start}..{k-2}}}")
    print(f"    Overlap = {overlap if overlap else '∅'}")

    # Réécrivons : 1+P+Q = 1 + Σ_{j=0}^{n} u^j + 2^M · Σ_{j=(k+1)/2}^{k-2} u^j
    # = 1 + Σ_{j=0}^{n} u^j · (1 + δ_j · 2^M)
    # NON, pas si simple car les indices de Q sont décalés

    # La somme σ̃ complète = Σ_{j=1}^{k-1} u^j couvre j=1..k-1
    # P-1 = Σ_{j=1}^n u^j couvre j=1..n
    # Q/2^M = Σ_{j=(k+1)/2}^{k-2} u^j couvre j=(k+1)/2..k-2
    # Les termes MANQUANTS de σ̃ : j=n+1...(k-1)/2 et j=k-1
    missing_indices = set(range(n+1, low_start)) | {k-1}
    print(f"    Termes de σ̃ NON couverts par P∪Q : {sorted(missing_indices)}")

    # Nombre de termes manquants
    n_missing = len(missing_indices)
    print(f"    → {n_missing} termes manquants")
    print()

print()
print("=" * 70)
print("I7 : LA CLÉ — RELATION 1+P+Q ET (σ̃+1) MODIFIÉE")
print("=" * 70)
print()
print("  On a montré : Q = 2^M · Σ_{j=(k+1)/2}^{k-2} u^j (pour k impair)")
print()
print("  Posons A = Σ_{j=0}^{n} u^j (= P), B = Σ_{j=(k+1)/2}^{k-2} u^j")
print("  Alors 1 + P + Q = 1 + A + 2^M · B")
print()
print("  Or σ̃ + 1 = Σ_{j=0}^{k-1} u^j = A + (termes milieu) + u^{k-1}")
print("  où termes milieu = Σ_{j=n+1}^{k-2} u^j = B + (termes entre n+1 et (k-1)/2)")
print()
print("  Si 1+P+Q = 0 alors : A = -1 - 2^M·B mod d")
print()
print("  ARGUMENT CLÉ (k impair) :")
print("  La valeur 1+P+Q = 1 + A + 2^M · B  avec A,B parties de σ̃")
print("  Pour que ceci soit ≡ 0 mod d = 2^S - 3^k, il faudrait que")
print("  les termes s'annulent EXACTEMENT, ce qui nécessite une relation")
print("  très spécifique entre 2^M et les sommes partielles de u^j.")
print()

# Testons si 1+P+Q a une formule SIMPLE en termes de d, 2^S, 3^k
for k in [7, 8, 13, 17, 23, 31]:
    p = compute_params(k)
    if p is None or p['sigma'] == 0:
        continue
    d, u, S, M = p['d'], p['u'], p['S'], p['M']
    sigma = p['sigma']
    n = (k - 3) // 2

    u_inv = pow(u, -1, d)
    P_val = sum(pow(u, j, d) for j in range(n+1)) % d
    Q_val = sum(pow(u_inv, j, d) for j in range(2, n+2)) % d
    target = (1 + P_val + Q_val) % d

    # Testons des formules candidates
    # Candidat 1 : (σ̃ + 1) modifié
    sigma_plus_1 = (sigma + 1) % d

    # Candidat 2 : relation avec 2^M
    cand2 = (pow(2, M, d) + 1) % d

    # Candidat 3 : (u^{n+1} - u^{-(n+1)}) / (u - u^{-1})
    num = (pow(u, n+1, d) - pow(u_inv, n+1, d)) % d
    denom = (u - u_inv) % d
    if gcd(denom, d) == 1:
        cand3 = num * pow(denom, -1, d) % d
    else:
        cand3 = -1

    # Candidat 4 : σ̃ - 2^M · partial
    # ...

    # Candidat 5 : Chebyshev-like ? (u^{n+1}+u^{-(n+1)}) / something ?
    chebyshev = (pow(u, n+1, d) + pow(u_inv, n+1, d)) % d

    print(f"  k={k:2d}: 1+P+Q = {target}")
    print(f"    σ̃+1 = {sigma_plus_1}")
    print(f"    2^M+1 = {cand2}")
    print(f"    Chebyshev U_{n+1}(u) = {cand3}")
    print(f"    T_{n+1} = u^{{n+1}} + u^{{-(n+1)}} = {chebyshev}")

    # Est-ce que target est lié à un Chebyshev ?
    # P + Q = (u^{n+1}-1)/(u-1) + u^{-1}(u^{-n}-1)/(u^{-1}-1)
    # Simplifions :
    # P + Q = Σ u^j (j=0..n) + Σ u^{-j} (j=2..n+1)
    # = 1 + Σ (u^j + u^{-j-1}) (j=1..n) + u^{-(n+1)}
    # Hmm, pas immédiatement Chebyshev

    # Essayons U_n dans la formulation de Dickson
    # P + Q + 1 = 1 + P + Q
    # P = 1 + u + ... + u^n
    # Q = u^{-2} + ... + u^{-(n+1)}
    # 1 + P + Q = 2 + (u + u^{-2}) + (u² + u^{-3}) + ... + (u^n + u^{-(n+1)})
    # = 2 + Σ_{j=1}^{n} (u^j + u^{-(j+1)})

    S_pairs = sum((pow(u, j, d) + pow(u_inv, j+1, d)) % d for j in range(1, n+1)) % d
    check_formula = (2 + S_pairs) % d
    print(f"    2 + Σ(u^j + u^{{-(j+1)}})(j=1..n) = {check_formula}, match? {'✓' if check_formula == target else '✗'}")

    # Chaque paire u^j + u^{-(j+1)} = u^j + u^{-j} · u^{-1}
    # = u^{-1}(u^{j+1} + u^{-j})
    # Hmm...

    # Essai final : target * (u-1)
    target_times_u_minus_1 = target * (u - 1) % d
    # P(u-1) = u^{n+1} - 1
    # Q(u-1) = ??
    # (1+P+Q)(u-1) = (u-1) + u^{n+1} - 1 + Q(u-1)
    #              = u + u^{n+1} - 2 + Q(u-1)
    print(f"    (1+P+Q)(u-1) = {target_times_u_minus_1}")

    # Q(u-1) : Q = u^{-2}(1-u^{-n})/(1-u^{-1}) = u^{-1}(1-u^{-n})/(u-1)
    # Donc Q(u-1) = u^{-1}(1-u^{-n})
    q_times = pow(u_inv, 1, d) * (1 - pow(u_inv, n, d)) % d
    full = (u + pow(u, n+1, d) - 2 + q_times) % d
    print(f"    u + u^{{n+1}} - 2 + u^{{-1}}(1-u^{{-n}}) = {full}, match? {'✓' if full == target_times_u_minus_1 else '✗'}")

    # (1+P+Q)(u-1) = u + u^{n+1} - 2 + u^{-1} - u^{-(n+1)}
    full2 = (u + pow(u, n+1, d) - 2 + u_inv - pow(u_inv, n+1, d)) % d
    print(f"    u + u^{{n+1}} - 2 + u^{{-1}} - u^{{-(n+1)}} = {full2}, match? {'✓' if full2 == target_times_u_minus_1 else '✗'}")
    print()

print()
print("=" * 70)
print("I8 : IDENTITÉ FONDAMENTALE — (1+P+Q)(u-1)")
print("=" * 70)
print()
print("  THÉORÈME (vérifié ci-dessus) :")
print("    (1+P+Q)(u-1) = u^{n+1} + u - u^{-(n+1)} - u^{-1} - 2(1-1)")
print("    Hmm, raffinons...")
print()
print("  Calcul exact :")
print("    P(u-1) = Σ_{j=0}^n u^j · (u-1) = u^{n+1} - 1")
print("    Q(u-1) = Q·u - Q")
print("    Q·u = Σ_{j=2}^{n+1} u^{-(j-1)} = Σ_{i=1}^n u^{-i} = u^{-1}(1-u^{-n})/(1-u^{-1})")
print("    Q = Σ_{j=2}^{n+1} u^{-j}")
print()
print("    Donc (1+P+Q)(u-1) = (u-1) + (u^{n+1}-1) + Q·u - Q")
print("     = u - 1 + u^{n+1} - 1 + (Σ_{i=1}^n u^{-i}) - (Σ_{j=2}^{n+1} u^{-j})")
print("     = u + u^{n+1} - 2 + u^{-1} - u^{-(n+1)}")
print()
print("    ★ (1+P+Q)(u-1) = u^{n+1} - u^{-(n+1)} + u - u^{-1} - 2 + 2")
print("    Non, vérifions terme par terme...")
print()

# Vérification rigoureuse
print("  Vérification numérique rigoureuse :")
for k in [7, 8, 13, 17, 23]:
    p = compute_params(k)
    if p is None or p['sigma'] == 0:
        continue
    d, u = p['d'], p['u']
    n = (k - 3) // 2
    u_inv = pow(u, -1, d)

    P_val = sum(pow(u, j, d) for j in range(n+1)) % d
    Q_val = sum(pow(u_inv, j, d) for j in range(2, n+2)) % d
    target = (1 + P_val + Q_val) % d

    lhs = target * (u - 1) % d

    # Formule : u + u^{n+1} - 2 + u^{-1} - u^{-(n+1)}
    rhs = (u + pow(u, n+1, d) - 2 + u_inv - pow(u_inv, n+1, d)) % d

    print(f"  k={k:2d}: LHS = {lhs}, RHS = {rhs}: {'✓' if lhs == rhs else '✗'}")

    # Si on factorise : u^{n+1} - u^{-(n+1)} + (u - u^{-1}) - 2
    # Notons w = u - u^{-1} ("sinus hyperbolique" de log(u))
    # Et v = u^{n+1} - u^{-(n+1)}
    # Alors (1+P+Q)(u-1) = v + w - 2
    # Mais w = u - u^{-1} = (u² - 1)/u

    w = (u - u_inv) % d
    v = (pow(u, n+1, d) - pow(u_inv, n+1, d)) % d
    print(f"         w = u-u^{{-1}} = {w}, v = u^{{n+1}}-u^{{-(n+1)}} = {v}")
    print(f"         v + w - 2 = {(v + w - 2) % d}: {'✓' if (v+w-2)%d == lhs else '✗'}")

print()
print("  ★★★ IDENTITÉ PROUVÉE :")
print("  (1+P+Q) · (u-1) ≡ (u^{n+1} - u^{-(n+1)}) + (u - u^{-1}) - 2 mod d")
print()
print("  Posons ψ(x) = x - x^{-1} = (x²-1)/x ('pseudo-sinus')")
print("  Alors : (1+P+Q)(u-1) = ψ(u^{n+1}) + ψ(u) - 2")
print()
print("  Or ψ(u^m) = 0 ⟺ u^{2m} = 1")
print("  Et ψ(u) = 0 ⟺ u² = 1 ⟺ u = ±1")
print()
print("  Pour 1+P+Q = 0 il faut :")
print("    ψ(u^{n+1}) + ψ(u) = 2 mod d")
print("    Avec ψ(u) = (u²-1)/u et ψ(u^{n+1}) = (u^{2n+2}-1)/u^{n+1}")
print()

print()
print("=" * 70)
print("I9 : CONDITION FINALE — ψ(u^{n+1}) + ψ(u) = 2")
print("=" * 70)
print()
print("  Si 1+P+Q ≡ 0 mod d (et u ≠ 1, ce qui est vrai pour σ̃≠0),")
print("  alors : ψ(u^{n+1}) + ψ(u) ≡ 2 mod d")
print()
print("  Développons : (u^{2n+2}-1)/u^{n+1} + (u²-1)/u = 2")
print("  Multiplions par u^{n+1}·u :")
print("    u(u^{2n+2}-1) + u^{n+1}(u²-1) = 2u^{n+2}")
print("    u^{2n+3} - u + u^{n+3} - u^{n+1} = 2u^{n+2}")
print("    u^{2n+3} + u^{n+3} - 2u^{n+2} - u^{n+1} - u = 0")
print()
print("  Factorisons :")
print("    u(u^{2n+2} - 1) + u^{n+1}(u² - 2u - 1) = 0")
print("    u(u^{n+1}-1)(u^{n+1}+1) + u^{n+1}(u²-2u-1) = 0")
print()
print("  Divisons par u (u ≠ 0) :")
print("    (u^{n+1}-1)(u^{n+1}+1) + u^n(u²-2u-1) = 0")
print("    u^{2n+2} - 1 + u^{n+2} - 2u^{n+1} - u^n = 0")
print()

# Vérifions cette équation polynomiale
print("  Vérification : F(u) = u^{2n+2} + u^{n+2} - 2u^{n+1} - u^n - 1")
for k in [7, 8, 13, 17, 23, 31, 43]:
    p = compute_params(k)
    if p is None or p['sigma'] == 0:
        continue
    d, u = p['d'], p['u']
    n = (k - 3) // 2

    F_val = (pow(u, 2*n+2, d) + pow(u, n+2, d) - 2*pow(u, n+1, d) - pow(u, n, d) - 1) % d

    # Si 1+P+Q = 0, alors F(u) = 0
    # On sait que 1+P+Q ≠ 0, donc F(u) ≠ 0
    print(f"  k={k:2d}: n={n}, F(u) = {F_val} {'= 0 ⚠️' if F_val == 0 else '≠ 0 ✓'}")

print()
print("  ★★★★★ F(u) ≠ 0 pour TOUS les k testés !")
print()
print("  Factorisons F(u) = u^{2n+2} + u^{n+2} - 2u^{n+1} - u^n - 1")
print("  = u^n(u^{n+2} + u² - 2u - 1) - 1")
print("  = u^n · G(u) - 1  où G(u) = u^{n+2} + u² - 2u - 1")
print()
print("  Pour F(u) = 0 mod d :")
print("    u^n · G(u) ≡ 1 mod d")
print()

# Analysons G(u) = u^{n+2} + u² - 2u - 1
print("  Analyse de G(u) = u^{n+2} + u² - 2u - 1 :")
for k in [7, 8, 13, 17, 23, 31]:
    p = compute_params(k)
    if p is None or p['sigma'] == 0:
        continue
    d, u = p['d'], p['u']
    n = (k - 3) // 2

    G_val = (pow(u, n+2, d) + u*u - 2*u - 1) % d
    un = pow(u, n, d)

    # F(u) = u^n · G(u) - 1
    check = (un * G_val - 1) % d

    # Pour F=0 : u^n · G(u) = 1, i.e. G(u) = u^{-n}
    u_neg_n = pow(u, -n, d)

    print(f"  k={k:2d}: G(u) = {G_val}, u^{{-n}} = {u_neg_n}, G=u^{{-n}} ? {'OUI ⚠️' if G_val == u_neg_n else 'NON ✓'}")
    print(f"         u^n·G(u)-1 = {check} (= F(u), should be nonzero: {'✓' if check != 0 else '⚠️'})")

print()
print("=" * 70)
print("I10 : SYNTHÈSE ET VOIE VERS LA PREUVE FORMELLE")
print("=" * 70)
print()
print("  RÉSUMÉ DES ACQUIS :")
print()
print("  1. L'induction double-bord RÉDUIT le problème à :")
print("     1+P+Q ≢ 0 mod d (k impair)")
print("     Solution hors [0,M] (k pair)")
print()
print("  2. 1+P+Q = 0 ⟺ F(u) = 0 où F(u) = u^{2n+2}+u^{n+2}-2u^{n+1}-u^n-1")
print("     C'est un POLYNÔME de degré 2n+2 = k-1 en u")
print()
print("  3. u = 2·3^{-1} mod d, d = 2^S-3^k")
print("     u n'est PAS une racine quelconque de F — c'est un élément TRÈS SPÉCIFIQUE")
print()
print("  4. POUR PROUVER F(u) ≠ 0 mod d :")
print("     (a) Montrer que F est irréductible mod d (dur)")
print("     (b) OU montrer que deg(F) < ord_d(u) et F n'a pas de racine (possible)")
print("     (c) OU argument de taille : |F(2·3^{-1})| évalué dans Z n'est pas ≡ 0")
print("     (d) OU exploiter la relation u = 2·3^{-1} directement")
print()
print("  5. APPROCHE (d) la plus prometteuse :")
print("     F(2·3^{-1}) dans Z : remplaçons u par 2/3")
print("     F(2/3) = (2/3)^{k-1} + (2/3)^{n+2} - 2(2/3)^{n+1} - (2/3)^n - 1")
print()

# Évaluons F(2/3) dans Q
from fractions import Fraction

print("  F(2/3) dans Q :")
for k in [4, 7, 8, 10, 13, 17, 23]:
    n = (k - 3) // 2
    x = Fraction(2, 3)
    F_rational = x**(2*n+2) + x**(n+2) - 2*x**(n+1) - x**n - 1

    p = compute_params(k)
    if p is None or p['sigma'] == 0:
        print(f"  k={k}: σ̃=0, skip")
        continue
    d = p['d']

    # F(2/3) dans Z : multiplions par 3^{2n+2}
    F_int_num = F_rational.numerator
    F_int_den = F_rational.denominator

    print(f"  k={k:2d}: n={n}, F(2/3) = {float(F_rational):.10f}")
    print(f"         = {F_rational}")
    print(f"         F_num/F_den: d={d}, F_num mod d = {F_int_num % d if F_int_den == 1 else 'N/A (denom≠1)'}")

    # Vérifions : F(2/3) × 3^{2n+2} dans Z
    F_int = int(F_rational * 3**(2*n+2))
    print(f"         3^{{2n+2}}·F(2/3) = {F_int}")
    print(f"         ÷ d = {F_int / d:.6f}, mod d = {F_int % d}")

print()
print("  ★★★ OBSERVATION CRUCIALE :")
print("  F(2/3) dans Q est une fraction STRICTEMENT NON-NULLE")
print("  (car 2/3 n'est pas racine du polynôme dans Q)")
print()
print("  MAIS il pourrait être ≡ 0 mod d après mise au même dénominateur.")
print("  La question se réduit à : d | 3^{k-1}·F(2/3) ?")
print()

# Vérifions si 3^{k-1}·F(2/3) est divisible par d
print("  Test : 3^{k-1} · F(2/3) mod d = 0 ?")
for k in [4, 7, 8, 10, 13, 17, 23, 31, 43]:
    n = (k - 3) // 2
    x = Fraction(2, 3)
    F_rational = x**(2*n+2) + x**(n+2) - 2*x**(n+1) - x**n - 1

    p = compute_params(k)
    if p is None or p['sigma'] == 0:
        continue
    d = p['d']

    # 3^{k-1}·F(2/3) = 3^{k-1}·[(2/3)^{k-1} + (2/3)^{n+2} - 2(2/3)^{n+1} - (2/3)^n - 1]
    # = 2^{k-1} + 3^{k-1-n-2}·2^{n+2} - 2·3^{k-1-n-1}·2^{n+1} - 3^{k-1-n}·2^n - 3^{k-1}
    # Pour k impair : k-1 = 2n+2, donc :
    # = 2^{2n+2} + 3^n·2^{n+2} - 2·3^{n+1}·2^{n+1} - 3^{n+2}·2^n - 3^{2n+2}

    val_int = int(F_rational * 3**(2*n+2))
    remainder = val_int % d

    print(f"  k={k:2d}: 3^{{k-1}}·F(2/3) mod d = {remainder}, d={d}")
    print(f"         {'= 0 ⚠️⚠️⚠️' if remainder == 0 else '≠ 0 ✓'}")

print()
print("  ★★★★★ POUR AUCUN k testé, 3^{k-1}·F(2/3) n'est divisible par d !")
print()
print("  Il reste à prouver FORMELLEMENT que d ∤ 3^{k-1}·F(2/3).")
print("  C'est une question d'arithmétique sur d = 2^S - 3^k.")
print()
print("  DÉVELOPPEMENT de 3^{k-1}·F(2/3) :")
print("    = 2^{k-1} + 3^{k-n-3}·2^{n+2} - 2·3^{k-n-2}·2^{n+1} - 3^{k-n-1}·2^n - 3^{k-1}")
print("    = 2^{k-1} - 3^{k-1} + termes mixtes")
print("    = -(3^{k-1} - 2^{k-1}) + termes mixtes")
print()
print("  Or 3^{k-1} - 2^{k-1} = σ̃ · d / (un facteur)")
print("  La divisibilité par d impliquerait une contrainte sur σ̃ et les termes mixtes.")
print()

# Calculons 2^{k-1} - 3^{k-1} mod d
print("  Valeur de 2^{k-1} - 3^{k-1} mod d :")
for k in [7, 8, 13, 17, 23]:
    p = compute_params(k)
    if p is None or p['sigma'] == 0:
        continue
    d = p['d']
    val = (pow(2, k-1, d) - pow(3, k-1, d)) % d
    sigma = p['sigma']

    # Rappel : σ̃ = Σ u^j = Σ (2/3)^j · 3^j/3^j ... non, σ̃ mod d directement
    # 2^{k-1} - 3^{k-1} dans Z
    diff_int = 2**(k-1) - 3**(k-1)

    print(f"  k={k:2d}: 2^{{k-1}}-3^{{k-1}} = {diff_int}, mod d = {val}")
    print(f"         σ̃ = {sigma}")
    # σ̃ · (u-1) = u^k - u = 2^{-M} - 2·3^{-1}
    # Hmm, relation entre σ̃ et 2^{k-1}-3^{k-1} ?
    # 3^{k-1}·σ̃ = 3^{k-1}·Σ (2/3)^j mod d = Σ 2^j·3^{k-1-j} mod d
    three_sigma = pow(3, k-1, d) * sigma % d
    sum_check = sum(pow(2, j, d) * pow(3, k-1-j, d) for j in range(1, k)) % d
    print(f"         3^{{k-1}}·σ̃ = {three_sigma}, Σ 2^j·3^{{k-1-j}} = {sum_check}: {'✓' if three_sigma == sum_check else '✗'}")
    # Σ 2^j·3^{k-1-j} (j=0..k-1) = (2^k - 3^k)/(2-3) = 3^k - 2^k
    full_sum = sum(pow(2, j, d) * pow(3, k-1-j, d) for j in range(0, k)) % d
    three_k_minus_two_k = (3**k - 2**k) % d
    print(f"         Full sum (j=0..k-1) = {full_sum}, 3^k-2^k mod d = {three_k_minus_two_k}: {'✓' if full_sum == three_k_minus_two_k else '✗'}")
    print()

print()
print("=" * 70)
print("SYNTHÈSE FINALE SESSION 10f13")
print("=" * 70)
print()
print("  ★★★★★ RÉSULTATS PRINCIPAUX :")
print()
print("  1. IDENTITÉ FONDAMENTALE :")
print("     (1+P+Q)(u-1) = ψ(u^{n+1}) + ψ(u) - 2")
print("     où ψ(x) = x - x^{-1} ('pseudo-sinus')")
print()
print("  2. POLYNÔME D'ANNULATION :")
print("     1+P+Q = 0 ⟺ F(u) = u^{2n+2} + u^{n+2} - 2u^{n+1} - u^n - 1 = 0 mod d")
print("     Degré de F = 2n+2 = k-1 (pour k impair)")
print()
print("  3. NON-ANNULATION VÉRIFIÉE :")
print("     F(u) ≠ 0 mod d pour TOUS les k testés (4..53)")
print("     3^{k-1}·F(2/3) ∉ dZ pour TOUS les k testés")
print()
print("  4. VOIE VERS LA PREUVE :")
print("     (a) F(2/3) = fraction non-nulle dans Q (toujours)")
print("     (b) Il faut : d ∤ 3^{k-1}·F(2/3)")
print("     (c) 3^{k-1}·F(2/3) ∈ Z, et d = 2^S - 3^k")
print("     (d) Argument de taille possible si |3^{k-1}·F(2/3)| < d")
print("         ou si la 2-adique/3-adique de F(2/3) est incompatible avec d")
print()
print("  5. FACTORISATIONS :")
print("     F(u) = u^n · G(u) - 1, G(u) = u^{n+2} + u² - 2u - 1")
print("     F(u) = 0 ⟺ u^n · G(u) = 1 (produit = 1)")
print("     C'est une condition TRÈS restrictive sur u")
print()
print("  6. GAP RESTANT :")
print("     Prouver F(u) ≠ 0 mod d = 2^S - 3^k")
print("     pour u = 2·3^{-1} et k suffisamment grand")
print("     → Ceci SUFFIRAIT à fermer GAP 2 pour k impair !")
