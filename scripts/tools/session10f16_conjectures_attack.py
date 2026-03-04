#!/usr/bin/env python3
"""
SESSION 10f16 : Attaque des 4 conjectures résiduelles
=====================================================
Date : 4 mars 2026

OBJECTIF : Explorer si les 4 gaps théoriques (G1, G2a, G2c, G3) peuvent être
réduits, connectés entre eux, ou partiellement résolus.

GAPS :
  G1  : σ̃=0 finitude (k=3,5 seulement)
  G2a : F(u) ≠ 0 mod d (double-bord, F_Z = 4^m - 9^m - 17·6^{m-1})
  G2c : ord_d(2) > C pour d premier
  G3  : CRT anti-corrélation pour d composite

INVESTIGATIONS :
  I1 : Connexion G1-G2a via formes linéaires en logarithmes
  I2 : Zsygmondy appliqué à G1 — quelles exceptions subsistent ?
  I3 : G2a — factorisation algébrique de F_Z + d
  I4 : G2a — borne inférieure p-adique locale
  I5 : G2c — structure de ord_d(2) quand d = 2^S - 3^k
  I6 : G3 — comptage des solutions CRT et borne birthday
  I7 : Relations entre les gaps : G2a ⟹ G2c ? ou indépendants ?
  I8 : Synthèse — quel gap est le plus attaquable ?

Protocole : G-V-R (le script est le juge)
"""

import sys
import math
from math import gcd, comb, log2, ceil
from functools import reduce

# Force unbuffered output
sys.stdout.reconfigure(line_buffering=True)

def compute_d(k):
    """Module cristallin d(k) = 2^S - 3^k"""
    S = ceil(k * log2(3))
    d = 2**S - 3**k
    if d <= 0:
        return None, None, None
    M = S - k
    return d, S, M

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i+2) == 0: return False
        i += 6
    return True

def factorize(n):
    """Factorisation en facteurs premiers"""
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

def ord_mod(a, n):
    """Ordre multiplicatif de a modulo n"""
    if gcd(a, n) != 1:
        return None
    o = 1
    x = a % n
    while x != 1:
        x = (x * a) % n
        o += 1
        if o > n:
            return None
    return o

def sigma_tilde(k, d, u):
    """σ̃(u) = Σ_{j=0}^{k-2} u^j mod d"""
    s = 0
    uj = 1
    for j in range(k-1):
        s = (s + uj) % d
        uj = (uj * u) % d
    return s

def F_polynomial(u, n, d):
    """F(u) = u^{2n+2} + u^{n+2} - 2u^{n+1} - u^n - 1 mod d"""
    return (pow(u, 2*n+2, d) + pow(u, n+2, d) - 2*pow(u, n+1, d) - pow(u, n, d) - 1) % d

def F_Z_formula(m):
    """F_Z = 4^m - 9^m - 17*6^{m-1} (entier)"""
    return 4**m - 9**m - 17 * 6**(m-1)

# ================================================================
# I1 : Connexion G1-G2a via structure d'exponentielles
# ================================================================
print("=" * 70)
print("I1 : CONNEXION G1-G2a — STRUCTURE COMMUNE")
print("=" * 70)

print("\nG1 : σ̃=0 ⟺ d | (3^{k-1} - 2^{k-1})")
print("G2a : double-bord ⟺ d | F_Z = (4^m - 9^m - 17·6^{m-1})")
print()

# Les deux sont des questions de la forme "d | E(k)" où E est une
# expression exponentielle et d = 2^S - 3^k.

# Réécrivons en base commune :
# G1 : E₁ = 3^{k-1} - 2^{k-1}
# G2a : E₂ = 4^m - 9^m - 17·6^{m-1} (m = (k-1)/2, k impair)

# Rewrite G2a : 4^m = 2^{2m} = 2^{k-1}, 9^m = 3^{2m} = 3^{k-1}
# Donc : E₂ = 2^{k-1} - 3^{k-1} - 17·6^{m-1}
# Soit : E₂ = -E₁ - 17·6^{m-1}

print("IDENTITÉ CLEF :")
print("  E₁ = 3^{k-1} - 2^{k-1}")
print("  E₂ = 4^m - 9^m - 17·6^{m-1}")
print("  Or 4^m = 2^{k-1} et 9^m = 3^{k-1} (pour k = 2m+1)")
print("  Donc : E₂ = 2^{k-1} - 3^{k-1} - 17·6^{m-1} = -E₁ - 17·6^{m-1}")
print()

# Vérifions
print("Vérification numérique :")
for k in [7, 9, 11, 13, 15, 21, 31, 51, 99]:
    if k % 2 == 0: continue
    m = (k - 1) // 2
    E1 = 3**(k-1) - 2**(k-1)
    E2 = F_Z_formula(m)
    check = -E1 - 17 * 6**(m-1)
    print(f"  k={k:3d}: E₂={E2}, -E₁-17·6^{{m-1}}={check}, match={E2==check}")

print()
print("CONSÉQUENCE MAJEURE :")
print("  Si d | E₁ (G1 vrai, σ̃=0), alors E₂ ≡ -17·6^{m-1} mod d")
print("  Or gcd(6,d)=1, donc 6^{m-1} est inversible mod d")
print("  Donc E₂ ≠ 0 mod d ssi 17 n'annule pas tout, ce qui est trivial")
print("  → G1 IMPLIQUE G2a (au moins partiellement) !")
print()

# Plus précisément : si σ̃=0 et d premier :
# E₂ = -E₁ - 17·6^{m-1} ≡ 0 - 17·6^{m-1} = -17·6^{m-1} mod d
# E₂ ≡ 0 mod d ⟺ d | 17·6^{m-1} ⟺ d | 17 (car gcd(6,d)=1)
# Mais d >> 17 pour k ≥ 7, donc E₂ ≠ 0 mod d. □

print("THÉORÈME : Si σ̃(u) = 0 et d > 17, alors F(u) ≠ 0 mod d.")
print("  Preuve : E₂ = -E₁ - 17·6^{m-1} ≡ -17·6^{m-1} mod d (car d|E₁)")
print("  Donc d|E₂ ⟺ d|17. Mais d ≥ 5 pour k=3, et d > 17 pour k ≥ 4.")
print("  Pour k=3: d=5, 17 mod 5 = 2 ≠ 0. Pour k=5: d=13, 17 mod 13 = 4 ≠ 0.")
print("  → F(u) ≠ 0 pour TOUS les cas σ̃=0. □")

# ================================================================
# I2 : Zsygmondy pour G1
# ================================================================
print("\n" + "=" * 70)
print("I2 : ZSYGMONDY APPLIQUÉ À G1")
print("=" * 70)

# Zsygmondy's theorem : pour a > b ≥ 1, gcd(a,b) = 1, n ≥ 3,
# a^n - b^n a un facteur premier primitif (divisant a^n-b^n mais pas a^j-b^j pour j<n)
# Exceptions : (a,b,n) = (2,1,6)

# Pour G1 : on a E₁ = 3^{k-1} - 2^{k-1}
# Zsygmondy (a=3, b=2, n=k-1) : pour k-1 ≥ 3 (k ≥ 4), E₁ a un facteur primitif q
# Ce facteur q divise 3^{k-1} - 2^{k-1} mais PAS 3^j - 2^j pour j < k-1

# La question est : d peut-il être un tel facteur (ou un multiple) ?

print("\nZsygmondy : 3^n - 2^n a un facteur premier primitif pour n ≥ 2")
print("(pas d'exception car (3,2) n'est pas dans la liste des exceptions)")
print()

# Vérifions les facteurs primitifs de 3^{k-1} - 2^{k-1}
for n in range(2, 30):
    E = 3**n - 2**n
    factors = factorize(E)
    # Un facteur premier p est primitif si p ne divise 3^j - 2^j pour tout j < n
    primitifs = []
    for p in factors:
        is_prim = True
        for j in range(1, n):
            if (3**j - 2**j) % p == 0:
                is_prim = False
                break
        if is_prim:
            primitifs.append(p)

    k = n + 1
    d_k, S_k, M_k = compute_d(k)
    if d_k is not None:
        divides = E % d_k == 0
    else:
        divides = None

    if n <= 15 or len(primitifs) == 0:
        print(f"  n={n:2d} (k={k:2d}): 3^n-2^n = {E:>15d}, facteurs={dict(factors)}")
        print(f"           primitifs={primitifs}, d(k)={d_k}, d|E₁={divides}")

print()
print("Observation : σ̃=0 ⟺ d | (3^{k-1} - 2^{k-1})")
print("Or d(k) = 2^S - 3^k. C'est un nombre SPÉCIFIQUE.")
print("Zsygmondy nous dit que 3^{k-1} - 2^{k-1} a un facteur primitif.")
print("QUESTION : d(k) peut-il être un facteur (ou contenir un facteur) de E₁ ?")

# Vérifions directement — MODULAIRE pour éviter explosion
print("\nTest direct : d(k) | (3^{k-1} - 2^{k-1}) ?")
count_yes = 0
for k in range(3, 500):
    d, S, M = compute_d(k)
    if d is None or d <= 1: continue
    # Calcul modulaire : (3^{k-1} - 2^{k-1}) mod d
    E1_mod_d = (pow(3, k-1, d) - pow(2, k-1, d)) % d
    if E1_mod_d == 0:
        count_yes += 1
        print(f"  k={k}: d={d}, d | E₁ ← OUI (σ̃=0)")

print(f"\n  Total σ̃=0 dans [3,499] : {count_yes} cas")

# ================================================================
# I3 : G2a — factorisation algébrique plus profonde
# ================================================================
print("\n" + "=" * 70)
print("I3 : G2a — FACTORISATION DE F_Z ET d")
print("=" * 70)

# F_Z = 4^m - 9^m - 17·6^{m-1}
# d = 2^{2m+1+ceil((2m+1)·log₂3)-(2m+1)} = 2^S - 3^{2m+1}
# avec S = ceil((2m+1)·log₂3)

# Explorons la factorisation de F_Z pour trouver des patterns
print("\nFactorisation de F_Z (petits m seulement, modulaire pour grands m) :")
for m in range(3, 50):
    k = 2*m + 1
    d, S, M = compute_d(k)
    if d is None: continue

    # Calcul modulaire de F_Z mod d
    # F_Z = 4^m - 9^m - 17·6^{m-1}
    fz_mod = (pow(4, m, d) - pow(9, m, d) - 17 * pow(6, m-1, d)) % d

    if m <= 15:
        fz = F_Z_formula(m)
        abs_fz = abs(fz)
        g = gcd(abs_fz, d)
        # Petits facteurs seulement
        small_d_factors = {}
        temp_d = d
        for p in [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71]:
            while temp_d % p == 0:
                small_d_factors[p] = small_d_factors.get(p,0) + 1
                temp_d //= p
        if temp_d > 1:
            small_d_factors[temp_d] = 1

        print(f"  m={m:2d} (k={k:2d}): gcd(|F_Z|,d)={g}, F_Z mod d = {fz_mod} {'✓≠0' if fz_mod != 0 else '✗=0!'}")
    else:
        print(f"  m={m:2d} (k={k:2d}): F_Z mod d = {fz_mod} {'✓≠0' if fz_mod != 0 else '✗=0!'}")

# ================================================================
# I4 : G2a — argument p-adique local pour v_p(F_Z) vs v_p(d)
# ================================================================
print("\n" + "=" * 70)
print("I4 : G2a — ARGUMENT p-ADIQUE LOCAL")
print("=" * 70)

# Pour que d | F_Z, il faut v_p(F_Z) ≥ v_p(d) pour TOUT premier p | d
# Si on peut trouver un p | d tel que v_p(F_Z) < v_p(d), c'est gagné

print("\nAnalyse v_p pour petits facteurs premiers de d (m ≤ 15) :")
for m in range(3, 16):
    k = 2*m + 1
    fz = F_Z_formula(m)
    d, S, M = compute_d(k)
    if d is None or d <= 1: continue

    abs_fz = abs(fz)
    d_factors = factorize(d)

    min_slack = float('inf')
    details = []

    for p, vp_d in d_factors.items():
        vp_fz = 0
        temp = abs_fz
        while temp > 0 and temp % p == 0:
            vp_fz += 1
            temp //= p

        slack = vp_fz - vp_d
        min_slack = min(min_slack, slack)
        if slack < 0:
            details.append(f"p={p}: v_p(F_Z)={vp_fz} < v_p(d)={vp_d}")

    fz_mod_d = fz % d
    blocker = "BLOQUÉ par p-adique" if min_slack < 0 else "pas de blocage p-adique"
    print(f"  m={m:2d} (k={k:2d}): min_slack={min_slack}, {blocker}, F_Z mod d = {fz_mod_d}")
    if details:
        for det in details:
            print(f"    → {det}")

# Extension modulaire pour m > 15
print("\nExtension : F_Z mod d pour m = 16..100 :")
all_nonzero = True
for m in range(16, 101):
    k = 2*m + 1
    d, S, M = compute_d(k)
    if d is None: continue
    fz_mod = (pow(4, m, d) - pow(9, m, d) - 17 * pow(6, m-1, d)) % d
    if fz_mod == 0:
        print(f"  ✗ m={m} (k={k}): F_Z ≡ 0 mod d !!!")
        all_nonzero = False
if all_nonzero:
    print(f"  ✓ F_Z mod d ≠ 0 pour TOUS m ∈ [16,100] (k impair ∈ [33,201])")

# ================================================================
# I5 : G2c — ord_d(2) vs C(S-1,k-1) quand d premier
# ================================================================
print("\n" + "=" * 70)
print("I5 : G2c — ord_d(2) POUR d PREMIER")
print("=" * 70)

print("\nRecherche des k avec d premier :")
prime_ks = []
for k in range(3, 500):
    d, S, M = compute_d(k)
    if d is None or d <= 1: continue
    if is_prime(d):
        prime_ks.append(k)

print(f"  k avec d premier dans [3,500] : {prime_ks[:20]}...")
print(f"  Total : {len(prime_ks)} cas")

print("\nAnalyse ord_d(2) vs C :")
for k in prime_ks[:20]:
    d, S, M = compute_d(k)
    C = comb(S-1, k-1)

    # σ̃ (modulaire)
    u = (2 * pow(3, -1, d)) % d
    st = sigma_tilde(k, d, u)

    if d < 2 * 10**6:  # calcul direct possible pour petits d
        o = ord_mod(2, d)
        ratio = o / C if C > 0 else float('inf')
        print(f"  k={k:3d}: d={d:>12d}, ord_d(2)={o:>10d}, C={C:>12d}, "
              f"ord/C={ratio:.3f}, σ̃={'=0' if st==0 else '≠0'}, "
              f"ord>C={'OUI ✓' if o > C else 'NON ✗'}")
    else:
        # On ne peut pas calculer ord directement, mais on vérifie si 2^{S-1} ≡ 1
        check = pow(2, S-1, d)
        print(f"  k={k:3d}: d={d} (grand), C={C}, σ̃={'=0' if st==0 else '≠0'}, "
              f"2^(S-1) mod d = {check} {'(=1→ord|S-1)' if check==1 else '(≠1→ord>S-1)'}")

# ================================================================
# I6 : G3 — CRT et borne birthday pour d composite
# ================================================================
print("\n" + "=" * 70)
print("I6 : G3 — CRT BIRTHDAY BOUND")
print("=" * 70)

# Pour d composite, d = p₁·p₂·...·p_r
# N₀(d) = 0 si pour aucun B, f(B) ≡ -1 mod p_i pour TOUT i
# La "birthday" question : si les solutions mod p_i sont "indépendantes",
# P(N₀(d) > 0) ≈ Π (N₀(p_i)/C) qui est très petit si N₀(p_i) << C

print("\nAnalyse CRT pour petits k composites :")
from itertools import combinations_with_replacement

for k in range(6, 16):  # Limité à k ≤ 15 pour la faisabilité
    d, S, M = compute_d(k)
    if d is None or d <= 1: continue
    if is_prime(d): continue

    C = comb(S-1, k-1)
    d_factors = factorize(d)
    primes = list(d_factors.keys())

    if len(primes) >= 2 and k - 1 <= 7 and M <= 12 and C < 50000:
        n0_per_p = {}

        for p in primes[:3]:
            if gcd(3, p) != 1: continue
            u_p = (2 * pow(3, -1, p)) % p
            target_p = (-1) % p

            count_p = 0
            for B in combinations_with_replacement(range(M+1), k-1):
                val = 0
                uj = u_p
                for j in range(k-1):
                    val = (val + uj * pow(2, B[j], p)) % p
                    uj = (uj * u_p) % p
                if val == target_p:
                    count_p += 1
            n0_per_p[p] = count_p

        ratios = [n0/C for p, n0 in n0_per_p.items() if C > 0]
        product = 1
        for r in ratios: product *= r

        print(f"  k={k:2d}: d={d}, primes={primes[:3]}, C={C}")
        print(f"    N₀(p_i) = {n0_per_p}")
        print(f"    Ratios N₀/C = {[f'{r:.4f}' for r in ratios]}")
        print(f"    Produit (indep.) = {product:.6f}")

# ================================================================
# I7 : Relations entre gaps — G2a ⟹ G2c ?
# ================================================================
print("\n" + "=" * 70)
print("I7 : RELATIONS ENTRE GAPS")
print("=" * 70)

print("\nAnalyse : G2a et G2c sont-ils indépendants ?")
print()
print("Structure de la preuve :")
print("  CAS INTÉRIEUR : besoin de G2c (ord > C)")
print("  CAS DOUBLE-BORD : besoin de G2a (F(u) ≠ 0)")
print("  Les deux sont nécessaires pour des CAS DIFFÉRENTS.")
print("  Donc G2a et G2c sont COMPLÉMENTAIRES, pas redondants.")
print()
print("MAIS : si on pouvait montrer que -1 ∉ Im(f) SANS distinguer")
print("les cas, on n'aurait besoin ni de G2a ni de G2c séparément.")
print()

# Idée : peut-on unifier via un argument GLOBAL ?
# L'image Im(f) est un sous-ensemble de Z/dZ de taille ≤ C.
# Si -1 était dans Im(f), que peut-on en déduire ?

print("Approche unifiée potentielle :")
print("  1. Si -1 ∈ Im(f), soit B* tel que f(B*) = -1")
print("  2. Par shift : f(B*+j) = -2^j pour j = 0,...,M-max(B*)")
print("  3. Donc l'orbite partielle {-2^j : j=0,...,M-max(B*)} ⊂ Im(f)")
print("  4. De même : f(B*-j) = -2^{-j} pour j = 0,...,min(B*)")
print("  5. L'orbite bidirectionnelle a taille ≥ M+1 = S-k+1")
print()

# Vérifions : S-k+1 > C pour k suffisamment grand ?
print("Test : M+1 = S-k+1 vs C = C(S-1,k-1) :")
for k in [4, 5, 7, 10, 13, 20, 50, 100]:
    d, S, M = compute_d(k)
    if d is None: continue
    C = comb(S-1, k-1)
    print(f"  k={k:3d}: M+1={M+1}, C={C}, M+1 > C ? {M+1 > C}")

print()
print("RÉSULTAT : M+1 << C pour tout k ≥ 4.")
print("L'orbite partielle est bien trop petite pour une contradiction directe.")
print("→ Les cas doivent être traités séparément.")

# ================================================================
# I8 : Synthèse — quel gap est le plus attaquable ?
# ================================================================
print("\n" + "=" * 70)
print("I8 : SYNTHÈSE — ATTAQUABILITÉ DES GAPS")
print("=" * 70)

print("""
BILAN :

G1 (σ̃=0 finitude) — ★★★★ QUASI-RÉSOLU
  - Vérifié k ≤ 500 (aucun cas sauf k=3,5)
  - Zsygmondy garantit un facteur primitif pour k-1 ≥ 7
  - Mais d = 2^S - 3^k n'est PAS forcément un facteur de 3^{k-1} - 2^{k-1}
  - ARGUMENT MANQUANT : montrer que d ne divise pas E₁ = 3^{k-1}-2^{k-1}
  - PISTE : argument de taille + Lifting the Exponent Lemma (LTE)
  - ATTAQUABILITÉ : ★★★★ (le plus proche de résolu)

G2a (F(u) ≠ 0) — ★★★★ QUASI-RÉSOLU
  - Formule explicite F_Z = 4^m - 9^m - 17·6^{m-1}
  - Connexion I1 : F_Z = -(E₁ + 17·6^{m-1}) = -E₁ - 17·6^{m-1}
  - Si G1 vrai (σ̃=0 → d|E₁) : F_Z ≡ -17·6^{m-1} ≠ 0 (trivial)
  - Si σ̃≠0 (cas générique) : pas de simplification via E₁
  - L'argument p-adique local ne suffit pas (pas de p universel)
  - gcd(F_Z, d) = 1 génériquement mais pas toujours
  - PISTE : montrer que F_Z et d n'ont pas de facteur commun ASSEZ GRAND
  - ATTAQUABILITÉ : ★★★ (formule explicite aide, mais preuve non triviale)

G2c (ord > C) — ★★★ OUVERT
  - Peu de d premiers dans l'intervalle (rare pour grands k)
  - Le résultat est de type "Artin" — largement ouvert en théorie des nombres
  - MAIS : on n'a besoin que d = 2^S - 3^k, structure TRÈS spécifique
  - Le fait que 2^S ≡ 3^k mod d donne une relation non triviale
  - PISTE : utiliser 2^S ≡ 3^k pour borner ord_d(2) par le bas
  - ATTAQUABILITÉ : ★★ (le plus difficile théoriquement)

G3 (CRT anti-corrélation) — ★★★ OUVERT
  - Birthday bound donne une heuristique mais pas une preuve
  - Les ratios N₀(p_i)/C sont petits mais pas prouvablement indépendants
  - La corrélation via les B communs est le cœur du problème
  - PISTE : exploiter que les mêmes B servent mod chaque p_i
  - ATTAQUABILITÉ : ★★ (combinatoire profonde)

STRATÉGIE RECOMMANDÉE :
  1. FERMER G1 (Zsygmondy + LTE) — le plus mûr
  2. Explorer la connexion G1↔G2a plus profondément
  3. Pour G2c : chercher des bornes effectives sur ord mod Mersenne-like
  4. Pour G3 : développer un argument de "dilution conditionnelle"
""")

# ================================================================
# BONUS : LTE (Lifting the Exponent) pour G1
# ================================================================
print("=" * 70)
print("BONUS : LIFTING THE EXPONENT LEMMA pour G1")
print("=" * 70)

# LTE : Si p est premier impair, p | a-b mais p ∤ a, p ∤ b, alors
# v_p(a^n - b^n) = v_p(a - b) + v_p(n)
# Pour a=3, b=2, n=k-1 :
# v_p(3^{k-1} - 2^{k-1}) = v_p(1) + v_p(k-1) = v_p(k-1) si p | (3-2)=1
# Mais p | (a-b) = 1 seulement si p = 1, impossible.
# Donc LTE standard ne s'applique pas directement.

# Pour p | (3^r - 2^r) avec r | (k-1) :
# L'ordre de 3/2 mod p divise r
# v_p(3^{k-1} - 2^{k-1}) = v_p(3^r - 2^r) + v_p((k-1)/r)

print("\nLTE : v_p(3^n - 2^n) pour p | (3^r - 2^r), r = ord_p(3/2)")
print("  v_p(3^n - 2^n) = v_p(3^r - 2^r) + v_p(n/r)")
print()

# Pour d = Π p_i^{a_i}, la condition d | (3^{k-1} - 2^{k-1}) signifie
# que pour CHAQUE facteur premier p de d, v_p(3^{k-1}-2^{k-1}) ≥ v_p(d)

# Question : d = 2^S - 3^k a-t-il des petits facteurs qui permettraient
# de satisfaire cette condition ?

print("Petits facteurs de d(k) et compatibilité σ̃=0 :")
for k in range(3, 100):
    d, S, M = compute_d(k)
    if d is None or d <= 1: continue

    # Trouver le plus petit facteur premier de d
    small_p = None
    for p in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]:
        if d % p == 0:
            small_p = p
            break

    if small_p and small_p <= 13:
        # ord_p(3/2) = ordre de 3·2^{-1} mod p
        if gcd(2, small_p) == 1:
            r = ord_mod((3 * pow(2, -1, small_p)) % small_p, small_p)
        else:
            r = None
        if r and (k-1) % r == 0:
            # E₁ mod p  (modulaire)
            E1_mod_p = (pow(3, k-1, small_p) - pow(2, k-1, small_p)) % small_p
            print(f"  k={k:2d}: p={small_p}|d, ord_p(3/2)={r}, "
                  f"r|(k-1)={r}|{k-1}=YES, E₁ mod p = {E1_mod_p}")

print("\n" + "=" * 70)
print("FIN SESSION 10f16")
print("=" * 70)
