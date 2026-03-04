#!/usr/bin/env python3
"""
SESSION 10f17c : F_Z mod p — argument algébrique
==================================================
OBSERVATION : F_Z mod 5 = 3 pour TOUT m (k impair).

PREUVE pour p=5 :
  F_Z = 4^m - 9^m - 17·6^{m-1}
  mod 5 : 9 ≡ 4, donc 4^m - 9^m ≡ 0
          17 ≡ 2, 6 ≡ 1, donc 17·6^{m-1} ≡ 2
          F_Z ≡ -2 ≡ 3 mod 5  ✓

QUESTION : Peut-on montrer F_Z mod p ≠ 0 pour TOUT p ≥ 5 ?
  F_Z mod p = (4^m - 9^m - 17·6^{m-1}) mod p

  Cas 1 : 4 ≡ 9 mod p ⟺ p | 5 → p = 5 (traité ci-dessus)
  Cas 2 : 4 ≢ 9 mod p → 4^m - 9^m mod p oscille, dépend de m

  L'objectif est de montrer que QUEL QUE SOIT m, F_Z ≠ 0 mod p.
  C'est-à-dire : 4^m - 9^m ≠ 17·6^{m-1} mod p pour tout m ≥ 3.
"""

import sys
import math
sys.stdout.reconfigure(line_buffering=True)

# ================================================================
# I1. Vérifier F_Z mod p pour TOUS les premiers p ≤ 1000
#     et TOUS les m = 3..500 (k = 7..1001 impair)
# ================================================================
print("=" * 70)
print("I1. F_Z mod p : recherche de p tel que p | F_Z pour un m ∈ [3,500]")
print("=" * 70)

def sieve(n):
    """Crible d'Ératosthène"""
    is_p = [True] * (n + 1)
    is_p[0] = is_p[1] = False
    for i in range(2, int(n**0.5) + 1):
        if is_p[i]:
            for j in range(i*i, n+1, i):
                is_p[j] = False
    return [i for i in range(2, n+1) if is_p[i]]

PRIMES = sieve(1000)

# Pour chaque premier p ≥ 5, trouver les m tels que p | F_Z
print("\nRecherche des p avec F_Z ≡ 0 mod p pour un m ∈ [3,500]:")

p_divides_fz = {}  # p -> list of m
for p in PRIMES:
    if p < 5:
        continue

    dividing_m = []
    for m in range(3, 501):
        fz_mod_p = (pow(4, m, p) - pow(9, m, p) - 17 * pow(6, m-1, p)) % p
        if fz_mod_p == 0:
            dividing_m.append(m)

    if dividing_m:
        p_divides_fz[p] = dividing_m

if p_divides_fz:
    print(f"\n  {len(p_divides_fz)} premiers p ∈ [5, 997] avec p | F_Z pour un m:")
    for p in sorted(p_divides_fz.keys())[:30]:
        ms = p_divides_fz[p]
        print(f"    p={p}: {len(ms)} valeurs de m : {ms[:15]}{'...' if len(ms)>15 else ''}")
else:
    print(f"\n  ★★★★★ AUCUN p ∈ [5, 997] ne divise F_Z pour m ∈ [3, 500]")

# ================================================================
# I2. Analyse des p qui divisent F_Z : est-ce aussi un facteur de d ?
# ================================================================
print("\n" + "=" * 70)
print("I2. CROISEMENT : p | F_Z ET p | d ?")
print("=" * 70)

def ceil_log2_3(k):
    return math.ceil(k * math.log2(3))

# Pour chaque p qui divise F_Z, vérifier si p | d(k) aussi
print("\nPour chaque p | F_Z, existe-t-il un k impair tel que p | d(k) aussi ?")

shared_primes = {}
for p, ms in sorted(p_divides_fz.items()):
    for m in ms:
        k = 2 * m + 1  # k impair
        S = ceil_log2_3(k)
        d_mod_p = (pow(2, S, p) - pow(3, k, p)) % p
        if d_mod_p == 0:
            if p not in shared_primes:
                shared_primes[p] = []
            shared_primes[p].append((k, m))

if shared_primes:
    print(f"\n  {len(shared_primes)} premiers p avec p | gcd(F_Z, d) :")
    for p in sorted(shared_primes.keys()):
        kms = shared_primes[p]
        print(f"    p={p}: k = {[k for k,m in kms[:10]]}{'...' if len(kms)>10 else ''}")
else:
    print(f"\n  ★★★★★ AUCUN p ∈ [5, 997] ne divise simultanément F_Z et d !")

# ================================================================
# I3. Argument algébrique : F_Z mod p comme fonction de m
# ================================================================
print("\n" + "=" * 70)
print("I3. STRUCTURE ALGÉBRIQUE : F_Z mod p en fonction de m")
print("=" * 70)

# F_Z = 4^m - 9^m - 17·6^{m-1} mod p
# = (2²)^m - (3²)^m - 17·(2·3)^{m-1} mod p
# Posons a = 4 mod p, b = 9 mod p, c = 6 mod p
# F_Z ≡ a^m - b^m - 17·c^{m-1} mod p
#      = a^m - b^m - (17/c)·c^m mod p
#      = a^m - b^m - (17·c⁻¹)·c^m mod p  (si c ≢ 0, i.e. p ≠ 2,3)

# Analyser pour quelques petits p
for p in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]:
    a = 4 % p
    b = 9 % p
    c = 6 % p

    # Calculer l'orbite de (a^m, b^m, c^m) mod p
    # Période = lcm(ord_p(4), ord_p(9), ord_p(6))
    ord_a = 1
    x = a
    while x % p != 1:
        x = (x * a) % p
        ord_a += 1
        if ord_a > p:
            ord_a = None
            break

    ord_b = 1
    x = b
    while x % p != 1:
        x = (x * b) % p
        ord_b += 1
        if ord_b > p:
            ord_b = None
            break

    ord_c = 1
    x = c
    while x % p != 1:
        x = (x * c) % p
        ord_c += 1
        if ord_c > p:
            ord_c = None
            break

    period = None
    if ord_a and ord_b and ord_c:
        period = math.lcm(ord_a, ord_b, ord_c)

    # Calculer F_Z mod p pour m = 0..period (si period existe)
    if period and period <= 200:
        fz_values = set()
        for m in range(1, period + 1):
            fz = (pow(a, m, p) - pow(b, m, p) - 17 * pow(c, m-1, p)) % p
            fz_values.add(fz)

        has_zero = 0 in fz_values
        print(f"  p={p}: 4≡{a}, 9≡{b}, 6≡{c}, ord(4)={ord_a}, ord(9)={ord_b}, "
              f"ord(6)={ord_c}, période={period}")
        print(f"    F_Z mod {p} prend {len(fz_values)} valeurs: {sorted(fz_values)}")
        if a == b:
            print(f"    → 4 ≡ 9 mod {p}, donc 4^m - 9^m ≡ 0, "
                  f"F_Z ≡ -17·6^{{m-1}} mod {p}")
            val = (-17 * pow(c, 0, p)) % p  # m=1 test
            print(f"    → Si 6^{{m-1}} est constant mod {p} : F_Z ≡ {(-17 % p)} mod {p}")
        if not has_zero:
            print(f"    ★ F_Z mod {p} ≠ 0 pour TOUT m (prouvé par exhaustion sur la période)")
        else:
            print(f"    ⚠ F_Z ≡ 0 mod {p} possible (mais p | d aussi ?)")
    else:
        # Calculer directement pour m = 3..100
        fz_values = set()
        for m in range(3, 101):
            fz = (pow(a, m, p) - pow(b, m, p) - 17 * pow(c, m-1, p)) % p
            fz_values.add(fz)
        has_zero = 0 in fz_values
        print(f"  p={p}: ord(4)={ord_a}, ord(9)={ord_b}, ord(6)={ord_c}, "
              f"période={'trop grande' if not period else period}")
        print(f"    F_Z mod {p} pour m=3..100 : {len(fz_values)} valeurs, "
              f"contient 0: {has_zero}")

# ================================================================
# I4. Argument clé : quand 4 ≡ 9 mod p (i.e. p | 5)
# ================================================================
print("\n" + "=" * 70)
print("I4. CAS SPÉCIAL : p | 5 → F_Z mod 5 = 3 TOUJOURS")
print("=" * 70)

print("""
PREUVE COMPLÈTE pour p = 5 :
  F_Z = 4^m - 9^m - 17·6^{m-1}

  mod 5 : 4 ≡ 4, 9 ≡ 4, donc 4^m - 9^m ≡ 0 mod 5  (∀m)
          17 ≡ 2, 6 ≡ 1, donc 17·6^{m-1} ≡ 2·1 = 2 mod 5
          F_Z ≡ 0 - 2 ≡ -2 ≡ 3 mod 5

  Donc 5 ∤ F_Z pour TOUT m. QED.

  Cet argument fonctionne car 4 ≡ 9 mod 5 (les deux sont ≡ -1 mod 5).
  Autrement dit : 2² ≡ 3² mod 5, qui vient de 2+3 = 5 ≡ 0 mod 5.
""")

# ================================================================
# I5. Généralisation : pour quels p a-t-on 4 ≡ 9 mod p ?
# ================================================================
print("=" * 70)
print("I5. POUR QUELS p : 4 ≡ 9 mod p ?")
print("=" * 70)

print("  4 ≡ 9 mod p ⟺ p | (9-4) = 5 ⟺ p = 5")
print("  C'est le SEUL cas. Pour p ≠ 5, 4^m - 9^m ≢ 0 mod p en général.")
print()

# ================================================================
# I6. Approche alternative : F_Z comme récurrence linéaire
# ================================================================
print("=" * 70)
print("I6. F_Z COMME RÉCURRENCE LINÉAIRE MOD p")
print("=" * 70)

print("""
F_Z(m) = 4^m - 9^m - 17·6^{m-1}

C'est une combinaison linéaire de 3 exponentielles : 4^m, 9^m, 6^m.
Les zéros de F_Z mod p sont les m tels que :
  4^m - 9^m ≡ 17·6^{m-1} mod p

Posons x = m mod T où T = lcm(ord_p(4), ord_p(9), ord_p(6)).
F_Z(m) mod p = F_Z(m mod T) mod p.

Donc p | F_Z(m) pour un m ⟺ p | F_Z(x) pour un x ∈ {0, ..., T-1}.
Le nombre de solutions est au plus T (nombre fini).

THÉORÈME : Pour chaque p ≥ 5, l'ensemble des m tels que p | F_Z(m)
est une union d'au plus T classes de résidus modulo T.
Si cet ensemble est VIDE (pas de solution), alors p ∤ F_Z pour TOUT m.
""")

# Vérifier : pour chaque p, le nombre de m ∈ [0, T-1] avec p | F_Z
print("Résultats exhaustifs par premier p :")
critical_primes = []  # p qui peut diviser F_Z

for p in sieve(200):
    if p < 5:
        continue

    a, b, c = 4 % p, 9 % p, 6 % p

    # Ordres
    def order(base, mod):
        if base % mod == 0:
            return None
        o, x = 1, base % mod
        while x != 1:
            x = (x * base) % mod
            o += 1
            if o > mod:
                return mod  # fallback
        return o

    oa, ob, oc = order(4, p), order(9, p), order(6, p)
    if oa is None or ob is None or oc is None:
        continue

    T = math.lcm(oa, ob, oc)

    # Chercher les m ∈ [0, T-1] avec p | F_Z
    zeros = []
    for m in range(T):
        if m == 0:
            # F_Z(0) = 1 - 1 - 17·6^{-1} → pas défini pour m=0
            continue
        fz = (pow(a, m, p) - pow(b, m, p) - 17 * pow(c, m-1, p)) % p
        if fz == 0:
            zeros.append(m)

    if zeros:
        critical_primes.append((p, T, zeros))
        print(f"  p={p}: T={T}, {len(zeros)} zéros mod T: {zeros[:10]}{'...' if len(zeros)>10 else ''}")

if not critical_primes:
    print(f"\n  ★★★★★ AUCUN p ∈ [5, 199] ne donne F_Z ≡ 0 mod p pour AUCUN m !")
    print(f"  → F_Z est copremier à TOUT premier p ∈ [5, 199] pour TOUT m ≥ 1")
else:
    print(f"\n  {len(critical_primes)} premiers p avec au moins un zéro de F_Z mod p")

    # Pour chaque tel p, vérifier si ces m correspondent à des k avec p | d
    print("\n  Croisement avec d(k) :")
    for p, T, zeros in critical_primes:
        # Les m dangereux : est-ce que k = 2m+1 donne p | d ?
        dangerous = []
        for m0 in zeros:
            # Tester m = m0, m0+T, m0+2T, ... jusqu'à m = 500
            for shift in range(0, 501, T):
                m = m0 + shift
                if m < 3 or m > 500:
                    continue
                k = 2 * m + 1
                S = ceil_log2_3(k)
                d_mod_p = (pow(2, S, p) - pow(3, k, p)) % p
                if d_mod_p == 0:
                    dangerous.append((m, k))

        if dangerous:
            print(f"    p={p}: {len(dangerous)} cas avec p | gcd(F_Z, d) !")
            print(f"      (m, k) = {dangerous[:10]}")
        else:
            print(f"    p={p}: AUCUN croisement (les zéros de F_Z ne tombent pas sur d)")

# ================================================================
# I7. THÉORÈME VISÉ : gcd(F_Z, d) contrôlé
# ================================================================
print("\n" + "=" * 70)
print("I7. THÉORÈME VISÉ : gcd(F_Z, d) est borné")
print("=" * 70)

# Calculer gcd(F_Z, d) pour k impair 7..501
print("\ngcd(F_Z, d) pour k impair 7..501:")
gcd_values = {}
for k in range(7, 502, 2):
    m = (k - 1) // 2
    S = ceil_log2_3(k)
    d = pow(2, S) - pow(3, k)
    if d <= 0:
        continue
    fz_mod_d = (pow(4, m, d) - pow(9, m, d) - 17 * pow(6, m-1, d)) % d
    if fz_mod_d == 0:
        g = d  # F_Z ≡ 0 mod d
    else:
        # gcd(fz_mod_d, d) = gcd(F_Z, d)
        g = math.gcd(fz_mod_d, d)

    if g > 1:
        gcd_values[k] = g

if gcd_values:
    print(f"\n  k avec gcd(F_Z, d) > 1:")
    for k, g in sorted(gcd_values.items()):
        # Factoriser g si petit
        print(f"    k={k}: gcd = {g}")
else:
    print(f"\n  ★★★★★ gcd(F_Z, d) = 1 pour TOUS les k impairs ∈ [7, 501] !")

# ================================================================
# I8. SYNTHÈSE
# ================================================================
print("\n" + "=" * 70)
print("I8. SYNTHÈSE SESSION 10f17c")
print("=" * 70)

print(f"""
RÉSULTAT CLÉ 1 : F_Z mod 5 = 3 TOUJOURS (PROUVÉ algébriquement)
  Car 4 ≡ 9 mod 5, donc 4^m - 9^m ≡ 0, et 17·6^{{m-1}} ≡ 2 mod 5.

RÉSULTAT CLÉ 2 : Pour p ∈ [5, 199], F_Z mod p est PÉRIODIQUE en m.
  Les zéros (s'ils existent) forment un sous-ensemble fini de Z/TZ.
  {"Pas de zéros trouvés pour p ∈ [5, 199]" if not critical_primes else f"{len(critical_primes)} premiers avec zéros"}

RÉSULTAT CLÉ 3 : gcd(F_Z, d) pour k impair 7..501
  {f"Toujours 1 !" if not gcd_values else f"Exceptions: {gcd_values}"}

STRATÉGIE POUR PROUVER G2a :
  Option A : Montrer gcd(F_Z, d) = 1 pour tout k ≥ 7 impair.
    Sous-cas : montrer que pour tout p | d, p ne divise pas F_Z.
    Utiliser la périodicité de F_Z mod p et le fait que les k avec p|d
    forment un ensemble différent de ceux avec p|F_Z.

  Option B : Montrer d ∤ F_Z par argument de TAILLE + coprimité partielle.
    |F_Z| ~ 9^m, d ~ 2^S ~ 3^k ≈ 9^m.
    Le ratio |F_Z|/d oscille mais d ∤ F_Z car gcd(F_Z, d) << d.
""")

print("=" * 70)
print("FIN SESSION 10f17c")
print("=" * 70)
