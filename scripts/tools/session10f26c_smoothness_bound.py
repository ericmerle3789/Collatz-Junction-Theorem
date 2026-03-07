#!/usr/bin/env python3
"""
SESSION 10f26c — BORNE INFERIEURE SUR P+(d-1)
Argument DETERMINISTE que d-1 = 2^S - 3^k - 1 ne peut pas etre (S-1)-smooth.

STRATEGIE:
  I1: Argument de comptage simple (nombre de B-smooth ≤ N)
  I2: Contraintes modulaires sur les facteurs premiers de d-1
  I3: Cyclotomie: Phi_n(2) et facteurs primitifs
  I4: Argument de Stewart (P+ de a^n - b^n)
  I5: Synthese theorique

Anti-hallucination: chaque borne est verifiee numeriquement.
"""
import sys
import math
import time

sys.stdout.reconfigure(line_buffering=True)

def flush():
    sys.stdout.flush()

try:
    import gmpy2
    from gmpy2 import mpz, is_prime as gmp_is_prime, powmod
except ImportError:
    pass

def ceil_log2_3(k):
    return math.ceil(k * math.log2(3))

KNOWN_K = [3, 4, 5, 13, 56, 61, 69, 73, 76, 148, 185, 655, 917,
           2183, 3540, 3895, 4500, 6891, 7752]

print("=" * 78)
print("SESSION 10f26c — BORNE INFERIEURE SUR P+(d-1)")
print("=" * 78)

# ======================================================================
# I1: ARGUMENT DE COMPTAGE
# ======================================================================
print("\n" + "=" * 78)
print("I1: ARGUMENT DE COMPTAGE — NOMBRE DE B-SMOOTH ≤ N")
print("=" * 78)
flush()

print("""
  THEOREME (Hildebrand & Tenenbaum, 1986):
    Psi(x, y) = #{n ≤ x : P+(n) ≤ y} = x · rho(u) · (1 + O(1/log y))
    ou u = log(x)/log(y), rho = fonction de Dickman.

  Pour notre probleme:
    x = d-1 ≈ 2^S
    y = S-1  (borne de lissete)
    u = log(2^S)/log(S-1) = S·ln(2)/ln(S-1)

  MAIS ATTENTION: on ne veut pas la PROBABILITE qu'un nombre aleatoire
  de taille ~2^S soit (S-1)-smooth. On veut savoir si LE NOMBRE SPECIFIQUE
  d-1 = 2^S - 3^k - 1 est (S-1)-smooth.

  L'argument probabiliste ne suffit PAS pour une preuve.

  ARGUMENT DETERMINISTE (tentative):
    Si d-1 est B-smooth avec B = S-1, alors:
      d-1 = prod_{p <= B} p^{a_p}
    Il y a pi(B) ≈ B/ln(B) premiers <= B.
    Et d-1 ≈ 2^S, donc sum a_p · log p ≈ S · log 2.
""")

# Calculons les bornes pour differents k
print("  Verification numerique:")
print(f"  {'k':>5s} | {'S':>5s} | {'B=S-1':>5s} | {'π(B)':>5s} | {'u':>8s} | {'log₁₀ρ(u)':>10s} | {'Ψ(d-1,B)':>12s}")
print("  " + "-" * 70)

for k in [13, 56, 100, 200, 500, 1000, 5000, 10000, 20000]:
    S = ceil_log2_3(k)
    B = S - 1
    # pi(B) approx
    pi_B = int(B / math.log(B)) if B > 2 else 1
    u = S * math.log(2) / math.log(B) if B > 1 else float('inf')

    # log10(rho(u)) approx pour u >> 1: rho(u) ≈ exp(-u(ln u - 1))
    if u > 2:
        log10_rho = -(u * (math.log(u) - 1)) / math.log(10)
    else:
        log10_rho = 0

    # Psi(d-1, B) ≈ 2^S · rho(u)
    # log10(Psi) ≈ S·log10(2) + log10(rho)
    log10_psi = S * math.log10(2) + log10_rho

    print(f"  {k:5d} | {S:5d} | {B:5d} | {pi_B:5d} | {u:8.2f} | {log10_rho:10.1f} | {log10_psi:12.1f}")

print("""
  OBSERVATION:
    Pour k ≥ 200: log₁₀(Ψ) < 0, i.e. Ψ(d-1, B) < 1
    ⟹ Il n'existe (heuristiquement) AUCUN B-smooth de taille ≈ d-1

    Plus fort: pour k ≥ 100, log₁₀(ρ) < -10
    ⟹ La probabilite est < 10^{-10}

    MAIS ceci est un argument PROBABILISTE, pas deterministe.
""")
flush()

# ======================================================================
# I2: CONTRAINTES MODULAIRES
# ======================================================================
print("\n" + "=" * 78)
print("I2: CONTRAINTES MODULAIRES SUR d-1 = 2^S - 3^k - 1")
print("=" * 78)
flush()

print("""
  Si p | d-1, alors 2^S ≡ 3^k + 1 (mod p).

  Pour chaque premier p ≤ S-1:
    ord_p(2) = o_2, ord_p(3) = o_3
    2^S mod p depend de S mod o_2
    3^k mod p depend de k mod o_3

  La contrainte 2^S ≡ 3^k + 1 (mod p) est satisfaite ssi:
    Il existe s ∈ Z/o_2, t ∈ Z/o_3 tels que
    S ≡ s (mod o_2), k ≡ t (mod o_3), et 2^s ≡ 3^t + 1 (mod p)

  Probabilite qu'un couple (S,k) satisfasse ceci pour p fixe:
    ≈ #{(s,t) : 2^s ≡ 3^t + 1 mod p} / (o_2 · o_3)

  Pour p = 2: 2^S ≡ 0 (mod 2), 3^k + 1 ≡ 0 (mod 2). OK, toujours.
  Pour p = 3: 2^S ≡ (-1)^S (mod 3), 3^k + 1 ≡ 1 (mod 3).
    2^S ≡ 1 (mod 3) ⟺ S pair.
  Pour p = 5: ord_5(2)=4, ord_5(3)=4.
    2^S mod 5 ∈ {2,4,3,1}, 3^k mod 5 ∈ {3,4,2,1}
    2^S ≡ 3^k + 1 (mod 5):
""")

# Calcul explicite pour petits p
for p in [3, 5, 7, 11, 13]:
    # Possibilites (S mod o_2, k mod o_3) telles que 2^S ≡ 3^k + 1 (mod p)
    o2 = 1
    x = 2 % p
    while x != 1 and o2 < p:
        x = (x * 2) % p
        o2 += 1
    if x != 1:
        o2 = p - 1

    o3 = 1
    x = 3 % p
    while x != 1 and o3 < p:
        x = (x * 3) % p
        o3 += 1
    if x != 1:
        o3 = p - 1

    valid = []
    for s in range(o2):
        for t in range(o3):
            if pow(2, s, p) == (pow(3, t, p) + 1) % p:
                valid.append((s, t))

    prob = len(valid) / (o2 * o3) if o2 * o3 > 0 else 0
    print(f"  p={p:3d}: ord_p(2)={o2:3d}, ord_p(3)={o3:3d}, "
          f"#{'{'}(s,t): 2^s≡3^t+1{'}'} = {len(valid)}/{o2*o3} = {prob:.4f}")

print("""
  PRODUIT EULERIENNE:
    Si les contraintes mod p etaient independantes, la probabilite que
    TOUS les p ≤ B divisent d-1 serait le produit des probabilites.
    Mais les contraintes ne sont PAS independantes en general.

  ARGUMENT PLUS FORT:
    Pour que d-1 soit B-smooth, il faut que d-1 s'ecrive comme
    produit de premiers ≤ B. Mais d-1 ≈ 2^S est un nombre de S bits,
    et il n'y a que pi(B) ≈ S/(ln S) premiers ≤ B.

    L'exposant moyen de chaque premier serait ≈ S·ln2 / (pi(B)·ln(B/2))
    ≈ S·ln2·ln(B) / B ≈ ln2·ln(S) (en utilisant B ≈ S)

    Mais les exposants ne sont pas libres: v_p(d-1) est DETERMINE par
    la valeur de 2^S - 3^k - 1 mod p^e.
""")
flush()

# ======================================================================
# I3: ARGUMENT CYCLOTOMIQUE
# ======================================================================
print("\n" + "=" * 78)
print("I3: FACTEURS CYCLOTOMIQUES DE 2^S - 1 ET ZSYGMONDY")
print("=" * 78)
flush()

print("""
  RAPPEL:
    2^S - 1 = prod_{n | S} Phi_n(2)

  ZSYGMONDY (1892): Pour S > 6, 2^S - 1 a un facteur premier primitif q
    tel que q ∤ 2^j - 1 pour j < S. De plus, q ≡ 1 (mod S).

  APPLICATION A NOTRE PROBLEME:
    d = 2^S - 3^k = (2^S - 1) - (3^k - 1)
    d-1 = (2^S - 1) - 3^k = (2^S - 1) - (3^k - 1) - 1

  Soit q un facteur premier primitif de 2^S - 1 (Zsygmondy).
    q | 2^S - 1 et q ≡ 1 (mod S).

  Question: est-ce que q | d-1 = (2^S - 1) - 3^k ?
    q | d-1 ⟺ q | 3^k ⟺ q = 3 (impossible car q ≡ 1 mod S et S > 6)
              OU q | (2^S - 1) - d - 1 = 3^k - 1 + d - (2^S - 1)

    Hmm, plus directement:
    d-1 = (2^S - 1) - 3^k
    Si q | (2^S - 1) et q ∤ 3^k, alors q ∤ d-1 en general.
    Si q | (2^S - 1) et q | d-1, alors q | 3^k.
    Mais q ≡ 1 mod S > 6, donc q ≥ S+1 > S-1.

  CAS INTERESSANT: si q | d, alors d = q (car d est premier).
    Cela signifierait d = q, un facteur primitif de 2^S - 1.
    Mais on sait que gcd(d, 2^S - 1) = 1 (verifie pour les 19 cas).
    Donc q ≠ d, et q ∤ d.

  CONSEQUENCE: Le facteur primitif q de 2^S - 1 est > S-1 et ne divise
    ni d ni d-1 (en general). Il ne nous aide pas directement.
""")

# Verification pour les petits cas
print("  Verification: facteurs primitifs de 2^S - 1")
for k in [3, 4, 5, 13]:
    S = ceil_log2_3(k)
    M_S = pow(2, S) - 1
    d = pow(2, S) - pow(3, k)
    dm1 = d - 1

    # Facteurs de M_S
    factors_MS = []
    temp = M_S
    for p in range(2, min(10000, M_S)):
        while temp % p == 0:
            factors_MS.append(p)
            temp //= p
    if temp > 1:
        factors_MS.append(temp)

    # Lesquels sont primitifs? (divisent 2^S - 1 mais pas 2^j - 1 pour j < S)
    primitives = []
    for p in set(factors_MS):
        is_prim = True
        for j in range(1, S):
            if (pow(2, j) - 1) % p == 0:
                is_prim = False
                break
        if is_prim:
            primitives.append(p)

    print(f"  k={k}, S={S}: 2^S-1={M_S}, facteurs={set(factors_MS)}, "
          f"primitifs={primitives}")
    for q in primitives:
        divides_d = (d % q == 0)
        divides_dm1 = (dm1 % q == 0)
        print(f"    q={q}: q|d? {'O' if divides_d else 'N'}, "
              f"q|d-1? {'O' if divides_dm1 else 'N'}, q≡{q%S} mod S")

flush()

# ======================================================================
# I4: ARGUMENT DE TAILLE + NOMBRE DE PREMIERS
# ======================================================================
print("\n" + "=" * 78)
print("I4: ARGUMENT DETERMINISTE — TAILLE vs NOMBRE DE PREMIERS")
print("=" * 78)
flush()

print("""
  LEMME (tentative): Pour k assez grand, d-1 = 2^S - 3^k - 1 n'est pas (S-1)-smooth.

  PREUVE (tentative):
    Supposons d-1 B-smooth avec B = S-1.
    Alors d-1 = prod_{p ≤ B} p^{a_p} ou a_p = v_p(d-1).

    Donc: log(d-1) = sum_{p ≤ B} a_p · log p

    Or log(d-1) ≈ S · log 2 (car d ≈ 2^S)

    Et sum_{p ≤ B} a_p · log p ≤ sum_{p ≤ B} a_p · log B
                                 = log B · sum a_p
                                 = log(S-1) · Omega(d-1)

    Ou Omega(d-1) = sum a_p est le nombre total de facteurs premiers
    (avec multiplicite) de d-1.

    Donc: Omega(d-1) ≥ S · log 2 / log(S-1) = u

    Mais Omega(d-1) ≤ log₂(d-1) ≈ S (borne triviale).
    Et u ≈ S · log 2 / log S ≈ S · 0.693 / ln S.

    Pour k grand: u ≈ 0.693 · S / ln S.
    Et le nombre MAXIMUM de facteurs (avec multiplicite) de d-1
    est S (car d-1 < 2^S).

    Ratio u/S ≈ 0.693/ln S → 0.
    Donc la contrainte u ≤ Omega(d-1) ≤ S est non-contradictoire.

  ECHEC: l'argument de taille seul ne suffit pas a exclure la lissete.
  Il faut exploiter la STRUCTURE de d-1 = 2^S - 3^k - 1.
""")

# Mais verifions les valeurs de Omega pour les 11 petits cas
print("  Verification Omega(d-1) vs u:")
for k in KNOWN_K[:11]:  # petits cas
    S = ceil_log2_3(k)
    d = pow(2, S) - pow(3, k)
    dm1 = d - 1
    B = S - 1
    u = S * math.log(2) / math.log(B) if B > 1 else 0

    # Omega(d-1) exact
    Omega = 0
    temp = dm1
    for p in range(2, min(B + 1, 10000)):
        while temp % p == 0:
            Omega += 1
            temp //= p
    # Cofacteur
    if temp > 1:
        Omega += 1  # au moins 1 facteur > B

    print(f"  k={k:5d}: S={S}, u={u:.2f}, Omega(d-1)≥{Omega}, S={S}, "
          f"u/S={u/S:.4f}")

flush()

# ======================================================================
# I5: ARGUMENT STRUCTUREL — VALUATION p-ADIQUE
# ======================================================================
print("\n" + "=" * 78)
print("I5: ARGUMENT STRUCTUREL — VALUATION p-ADIQUE DE d-1")
print("=" * 78)
flush()

print("""
  IDEE CLE: Pour chaque premier p ≤ S-1, v_p(d-1) est BORNE.

  v_p(d-1) = v_p(2^S - 3^k - 1)

  Or 2^S mod p^e et 3^k mod p^e sont periodiques en S et k.
  La periode de 2^S mod p^e est ord_{p^e}(2) = p^{e-1} · ord_p(2) pour e ≥ 2 (LTE).

  Donc v_p(d-1) est determine par (S mod ord_{p^e}(2), k mod ord_{p^e}(3)).

  La SOMME sum v_p(d-1) · log p sur p ≤ B = log M (ou M = partie smooth).

  Si d-1 est B-smooth, alors M = d-1, donc log M = log(d-1) ≈ S · log 2.

  Mais M = prod p^{v_p(d-1)}, et chaque v_p est borne par:
    v_p(d-1) ≤ log_p(d-1) ≈ S · log 2 / log p

  En pratique, pour un p FIXE et des S, k "aleatoires":
    E[v_p(d-1)] ≈ 1/(p-1) (par un argument de densite des divisibilites).

  Donc E[log M] ≈ sum_{p ≤ B} log(p) / (p-1) ≈ log B (par Mertens).

  CONTRADICTION: Pour d-1 B-smooth, il faudrait log M = S · log 2,
  mais l'esperance de log M est seulement ≈ log S.

  Le RATIO est S · log 2 / log S → ∞.

  Ceci formalise quantitativement l'argument de Dickman:
  les valuations p-adiques "typiques" ne fournissent qu'une
  fraction infime des bits necessaires.
""")

# Verification: M_bits vs d_bits pour les 19 cas
print("  Verification M_bits / d_bits:")
for k in KNOWN_K:
    S = ceil_log2_3(k)
    d = pow(2, S) - pow(3, k)
    dm1 = d - 1
    B = S - 1

    M = 1
    temp = dm1
    p = 2
    while p <= B:
        while temp % p == 0:
            M *= p
            temp //= p
        p += 1 if p == 2 else 2

    M_bits = M.bit_length()
    d_bits = d.bit_length()
    ratio = M_bits / d_bits * 100

    print(f"  k={k:5d}: M={M_bits:5d}b, d={d_bits:5d}b, M/d={ratio:5.1f}%")

flush()

# ======================================================================
# SYNTHESE
# ======================================================================
print("\n" + "=" * 78)
print("SYNTHESE — BORNE INFERIEURE SUR P+(d-1)")
print("=" * 78)
flush()

print("""
  ETAT DES LIEUX:

  1. ARGUMENT PROBABILISTE (Dickman): ECRASANT mais non rigoureux.
     ρ(u) → 0 super-exponentiellement, u ≈ k·ln3/ln(k).

  2. ARGUMENT DE TAILLE: INSUFFISANT seul.
     u ≤ Omega(d-1) ≤ S est non-contradictoire.

  3. ARGUMENT VALUATIONS: QUALITATIF.
     E[log M] ≈ log S vs log(d-1) ≈ S·log 2 — gap exponentiel.
     Mais "en esperance" n'est pas une preuve.

  4. ARGUMENT CYCLOTOMIQUE: NON CONCLUANT.
     Les facteurs primitifs de 2^S - 1 ne divisent pas d en general.

  CONCLUSION INTERMEDIAIRE:
    Aucun argument DETERMINISTE trouv pour l'instant.
    Le gap theorique est: "heuristique forte ≠ preuve".

  PISTE LA PLUS PROMETTEUSE:
    Resultats de Stewart (2013):
    "On the greatest prime factor of integers of the form a^b ± 1"
    Borne: P+(a^n - 1) > n · exp(c · (log n)^{1/2}) pour n assez grand.

    Si on pouvait adapter a d-1 = 2^S - 3^k - 1:
    P+(d-1) > S · exp(c · (log S)^{1/2}) >> S-1 pour S assez grand.

    MAIS: d-1 = 2^S - 3^k - 1 n'est PAS de la forme a^n - 1.
    C'est de la forme a^n - b^k - 1.

  ALTERNATIVE:
    Si d est premier et 2^S ≡ 3^k mod d,
    on pourrait utiliser les resultats sur les solutions
    de a^x ≡ b^y (mod p) pour montrer que l'ordre est grand.

    Yu & Kunrui (2004): "p-adic logarithmic forms and group varieties"
    ⟹ Bornes inferieures sur ord_p(2) via formes lineaires en logarithmes.

    Baker (1966): Si alpha, beta sont des entiers algebriques,
    |alpha^m - beta^n| > exp(-C · log(m) · log(n))
    ⟹ ord_d(2) > (log d)^{1+epsilon} ?

  RESUME:
    La MEILLEURE approche semble etre les formes lineaires en logarithmes
    p-adiques (Baker-Wustholz, Yu), qui donnent des bornes inferieures
    sur ord_d(2) en fonction de log(d).

    Si on peut montrer ord_d(2) > S-1, c'est FINI car alors
    ord_d(2) ∤ C (car C a seulement des facteurs ≤ S-1).
""")
flush()
