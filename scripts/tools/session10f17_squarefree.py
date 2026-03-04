#!/usr/bin/env python3
"""
SESSION 10f17 : d = 2^S - 3^k est-il squarefree ?
=====================================================
Question : Pour k >= 3, d(k) = 2^ceil(k*log2(3)) - 3^k.
           d(k) est-il toujours squarefree (sans facteur carré) ?

Enjeu : Si oui, l'argument p-adique (R59) prouverait G2a directement.

Investigations :
  I1. Test squarefree pour k = 3..500
  I2. Si exceptions, les analyser (quel p², quel k)
  I3. Relation entre facteurs de d et structure 2^S - 3^k
  I4. Implications pour G2a quand d n'est PAS squarefree
  I5. Lien avec nombres de Wieferich et théorie ABC
  I6. Extension : d squarefree pour k pair (via k pairs → k impairs?)
  I7. Synthèse et prochaine action
"""

import sys
import math
sys.stdout.reconfigure(line_buffering=True)

try:
    from sympy import factorint, isprime, sqrt as sym_sqrt
    HAS_SYMPY = True
except ImportError:
    HAS_SYMPY = False
    print("WARNING: sympy non disponible, utilisation de factorisation basique")

def ceil_log2_3(k):
    """S = ceil(k * log2(3))"""
    return math.ceil(k * math.log2(3))

def d_of_k(k):
    """d(k) = 2^S - 3^k"""
    S = ceil_log2_3(k)
    return 2**S - 3**k

def is_squarefree_basic(n):
    """Test squarefree par factorisation."""
    if n <= 1:
        return True, {}
    n = abs(n)
    if HAS_SYMPY:
        factors = factorint(n)
    else:
        factors = {}
        temp = n
        d = 2
        while d * d <= temp:
            while temp % d == 0:
                factors[d] = factors.get(d, 0) + 1
                temp //= d
            d += 1
        if temp > 1:
            factors[temp] = 1
    sqfree = all(v == 1 for v in factors.values())
    return sqfree, factors

# ================================================================
# I1. Test squarefree pour k = 3..500
# ================================================================
print("=" * 70)
print("I1. TEST SQUAREFREE : d(k) = 2^S - 3^k pour k = 3..500")
print("=" * 70)

non_squarefree = []
squarefree_count = 0
total = 0

# Phase 1 : k = 3..200 (factorisation complète faisable)
print("\nPhase 1 : k = 3..200 (factorisation complète)")
for k in range(3, 201):
    S = ceil_log2_3(k)
    d = d_of_k(k)
    if d <= 0:
        continue
    total += 1
    sqfree, factors = is_squarefree_basic(d)
    if not sqfree:
        squared_primes = {p: v for p, v in factors.items() if v >= 2}
        non_squarefree.append((k, S, d, squared_primes))
        print(f"  ⚠ k={k}: d = 2^{S} - 3^{k} = {d}")
        print(f"    NON squarefree! Facteurs carrés: {squared_primes}")
    else:
        squarefree_count += 1

print(f"\n  Résultat Phase 1: {squarefree_count}/{total} squarefree, "
      f"{len(non_squarefree)} exceptions")

# Phase 2 : k = 201..500 (factorisation par petits premiers)
print("\nPhase 2 : k = 201..500 (test par petits p²)")
SMALL_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
                53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109,
                113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
                181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241,
                251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313,
                317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389,
                397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461,
                463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547,
                557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617,
                619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691,
                701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773,
                787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859,
                863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947,
                953, 967, 971, 977, 983, 991, 997]

phase2_non_sqfree = []
phase2_total = 0
for k in range(201, 501):
    S = ceil_log2_3(k)
    # Utiliser arithmétique modulaire : d mod p² = (2^S - 3^k) mod p²
    phase2_total += 1
    for p in SMALL_PRIMES:
        p2 = p * p
        d_mod_p2 = (pow(2, S, p2) - pow(3, k, p2)) % p2
        if d_mod_p2 == 0:
            phase2_non_sqfree.append((k, S, p))
            print(f"  ⚠ k={k}: p²={p}² | d (d mod {p2} = 0)")
            break

print(f"\n  Résultat Phase 2: {phase2_total - len(phase2_non_sqfree)}/{phase2_total} "
      f"squarefree mod petits p², {len(phase2_non_sqfree)} exceptions")

# ================================================================
# I2. Analyse détaillée des exceptions
# ================================================================
print("\n" + "=" * 70)
print("I2. ANALYSE DÉTAILLÉE DES EXCEPTIONS")
print("=" * 70)

all_exceptions = non_squarefree + [(k, S, None, {p: '?'})
                                     for k, S, p in phase2_non_sqfree]

if not all_exceptions and not phase2_non_sqfree:
    print("\n  AUCUNE exception ! d est squarefree pour TOUS les k ∈ [3,500]")
    print("  → L'argument p-adique (R59) prouverait G2a DIRECTEMENT !")
else:
    print(f"\n  {len(non_squarefree) + len(phase2_non_sqfree)} exceptions trouvées:")
    for item in non_squarefree:
        k, S, d, sp = item
        print(f"    k={k}: S={S}, d={d}, facteurs carrés: {sp}")
    for k, S, p in phase2_non_sqfree:
        print(f"    k={k}: S={S}, p²={p}² | d")

# ================================================================
# I3. Analyse structurelle : pourquoi d est (ou n'est pas) squarefree
# ================================================================
print("\n" + "=" * 70)
print("I3. ANALYSE STRUCTURELLE : d = 2^S - 3^k")
print("=" * 70)

# Pour chaque exception, analyser si p² | 2^S - 3^k a une structure
if non_squarefree:
    print("\nAnalyse des p² divisant d:")
    p_counts = {}
    for k, S, d, sp in non_squarefree:
        for p, v in sp.items():
            p_counts[p] = p_counts.get(p, []) + [(k, v)]
    for p, klist in sorted(p_counts.items()):
        print(f"  p={p}: apparaît pour k = {[k for k,v in klist]}")
        # Vérifier si p² | 2^S - 3^k a un pattern mod
        # p² | 2^S - 3^k  ⟺  2^S ≡ 3^k mod p²
        # Chercher la période de cette congruence
        print(f"    Condition: 2^S ≡ 3^k mod {p*p}")
        ord2 = 1
        x = 2
        while x % (p*p) != 1:
            x = (x * 2) % (p*p)
            ord2 += 1
            if ord2 > p*p:
                break
        ord3 = 1
        x = 3
        while x % (p*p) != 1:
            x = (x * 3) % (p*p)
            ord3 += 1
            if ord3 > p*p:
                break
        print(f"    ord_{p*p}(2) = {ord2}, ord_{p*p}(3) = {ord3}")
else:
    print("\n  Aucune exception → analyse non nécessaire.")

# ================================================================
# I4. Si d n'est pas squarefree : implications pour G2a
# ================================================================
print("\n" + "=" * 70)
print("I4. IMPLICATIONS POUR G2a (cas d non squarefree)")
print("=" * 70)

if non_squarefree:
    print("\nPour chaque exception, vérifions si F_Z mod d ≠ 0 :")
    for k, S, d, sp in non_squarefree:
        if k % 2 == 1 and k >= 7:
            m = (k - 1) // 2
            F_Z = 4**m - 9**m - 17 * 6**(m-1)
            r = F_Z % d
            gcd_val = math.gcd(abs(F_Z), d)
            print(f"  k={k}: F_Z mod d = {r}, gcd(F_Z,d) = {gcd_val}")
            for p, v in sp.items():
                fz_mod_p2 = F_Z % (p**2)
                print(f"    F_Z mod {p}² = {fz_mod_p2}", end="")
                if fz_mod_p2 == 0:
                    print(" ← PROBLÈME : p² divise aussi F_Z !")
                else:
                    print(f" ← OK : p² ne divise PAS F_Z (seulement p¹ max)")
else:
    print("\n  Pas d'exceptions → G2a prouvable par argument p-adique direct.")

# ================================================================
# I5. Lien théorique : nombres de Wieferich et abc
# ================================================================
print("\n" + "=" * 70)
print("I5. CONNEXIONS THÉORIQUES")
print("=" * 70)

print("""
CONNEXION 1 : Nombres de Wieferich
-----------------------------------
p est un premier de Wieferich si 2^{p-1} ≡ 1 mod p².
Seuls deux connus : p = 1093, p = 3511.
Si p² | d = 2^S - 3^k, alors 2^S ≡ 3^k mod p².
Cela NE signifie PAS que p est de Wieferich (car S ≠ p-1 en général),
mais c'est une condition similaire de "presque divisibilité".

CONNEXION 2 : Conjecture abc
-----------------------------
abc dit que pour a + b = c avec gcd(a,b)=1,
le radical rad(abc) > c^{1-ε} pour tout ε > 0.
Ici : 3^k + d = 2^S, gcd(3^k, d) = gcd(3^k, 2^S - 3^k).
Si d n'est pas squarefree, rad(d) < d, réduisant rad(3^k · d · 2^S).
La conjecture abc impliquerait que d ne peut pas avoir de "gros" facteurs carrés.

CONNEXION 3 : Catalan-Mihailescu (résolu 2002)
-----------------------------------------------
2^S - 3^k = d, pour d petit ⟹ 2^S ≈ 3^k (puissances parfaites proches).
Catalan : les seules puissances parfaites consécutives sont 8=2³ et 9=3².
Pour d = 1 : impossible sauf k=2, S=4 (16-9=7, non).
""")

# ================================================================
# I6. Test étendu k = 3..1000 avec petits p²
# ================================================================
print("=" * 70)
print("I6. TEST ÉTENDU : k = 3..1000 avec p² pour p ≤ 997")
print("=" * 70)

extended_non_sqfree = []
for k in range(3, 1001):
    S = ceil_log2_3(k)
    found = False
    for p in SMALL_PRIMES:
        p2 = p * p
        d_mod_p2 = (pow(2, S, p2) - pow(3, k, p2)) % p2
        if d_mod_p2 == 0:
            extended_non_sqfree.append((k, p))
            found = True
            break

if extended_non_sqfree:
    print(f"\n  Exceptions trouvées (k, p tel que p²|d):")
    for k, p in extended_non_sqfree:
        print(f"    k={k}: {p}² | d")
    print(f"\n  Total: {len(extended_non_sqfree)} exceptions sur {998} valeurs de k")

    # Analyser les p qui apparaissent
    p_set = {}
    for k, p in extended_non_sqfree:
        p_set[p] = p_set.get(p, []) + [k]
    print("\n  Distribution par premier p:")
    for p, ks in sorted(p_set.items()):
        print(f"    p={p}: k = {ks[:20]}{'...' if len(ks)>20 else ''} ({len(ks)} valeurs)")
else:
    print(f"\n  ★★★★★ AUCUNE exception pour k = 3..1000 !")
    print(f"  d est squarefree mod p² (p ≤ 997) pour les 998 valeurs de k testées")

# ================================================================
# I7. Recherche systématique : grands p²
# ================================================================
print("\n" + "=" * 70)
print("I7. RECHERCHE AVEC PLUS GRANDS PREMIERS")
print("=" * 70)

# Pour k = 3..200, on a la factorisation complète (Phase 1)
# Vérifier si un grand p² (p > 997) divise d
if not non_squarefree:
    print("\n  Phase 1 (k=3..200) déjà montrée squarefree par factorisation complète.")
    print("  → Aucun p > 997 ne donne p² | d pour k ≤ 200")
else:
    print("\n  Grands facteurs carrés trouvés en Phase 1:")
    for k, S, d, sp in non_squarefree:
        for p, v in sp.items():
            if p > 997:
                print(f"    k={k}: p={p}^{v} | d")

# Pour k = 201..500, vérifier avec factorisation complète (si sympy)
if HAS_SYMPY:
    print("\n  Phase 2+ : Factorisation complète pour k = 201..300 (sympy)")
    phase2plus_non_sqfree = []
    for k in range(201, 301):
        S = ceil_log2_3(k)
        d = d_of_k(k)
        if d <= 0:
            continue
        # Utiliser sympy pour factoriser
        try:
            factors = factorint(d, limit=10**6)
            # Vérifier si squarefree parmi les facteurs trouvés
            for p, v in factors.items():
                if v >= 2:
                    phase2plus_non_sqfree.append((k, p, v))
                    print(f"    ⚠ k={k}: {p}^{v} | d")
        except Exception as e:
            pass  # Factorisation trop lente, skip

    if not phase2plus_non_sqfree:
        print("    Aucun facteur carré trouvé (facteurs ≤ 10^6)")

# ================================================================
# I8. Argument heuristique : probabilité de non-squarefree
# ================================================================
print("\n" + "=" * 70)
print("I8. ARGUMENT HEURISTIQUE")
print("=" * 70)

print("""
La probabilité qu'un entier aléatoire n soit squarefree est 6/π² ≈ 0.6079.
Mais d n'est PAS un entier aléatoire : d = 2^S - 3^k a une structure spéciale.

Argument 1 : d n'est divisible ni par 2 ni par 3
  d = 2^S - 3^k ≡ -3^k ≡ 0 mod ? Non : gcd(d, 6) = 1 (car d impair et d mod 3 ≠ 0)
  En fait d mod 2 = 2^S mod 2 - 3^k mod 2 = 0 - 1 = -1 ≡ 1 mod 2 → d impair ✓
  d mod 3 = 2^S mod 3 - 0 = 2^S mod 3 ∈ {1, 2} → d ≢ 0 mod 3 ✓

  Donc 4 ∤ d et 9 ∤ d par définition.
  La proba heuristique de squarefree sachant d impair et d ≢ 0 mod 3 est :
  P = ∏_{p≥5} (1 - 1/p²) = (6/π²) / ((1-1/4)(1-1/9)) = 0.6079 / (3/4 · 8/9)
    = 0.6079 / (2/3) = 0.9119

  Donc ~91% des k devraient donner d squarefree, et ~9% donner d non-squarefree.
""")

# Calcul numérique
prob = 1.0
for p in SMALL_PRIMES:
    if p >= 5:
        prob *= (1 - 1.0 / (p * p))
print(f"  Estimation numérique (p jusqu'à 997): P(sqfree | d impair, d≢0 mod3) ≈ {prob:.6f}")
print(f"  Pour 998 valeurs de k : on attendrait ~{998*(1-prob):.1f} exceptions")

# ================================================================
# I9. Test final : vérification avec Möbius
# ================================================================
print("\n" + "=" * 70)
print("I9. VÉRIFICATION CROISÉE AVEC CORE SQUAREFREE")
print("=" * 70)

# Pour les k de Phase 1, calculer le radical et le core squarefree
if HAS_SYMPY:
    sqfree_part_ratios = []
    for k in range(3, 101):
        d = d_of_k(k)
        if d <= 0:
            continue
        factors = factorint(d)
        # rad(d) = produit des p | d
        rad = 1
        for p in factors:
            rad *= p
        # sqfree core = d / (partie carrée)
        sq_part = 1
        for p, v in factors.items():
            if v >= 2:
                sq_part *= p ** (v - 1)
        sqfree_core = d // sq_part
        ratio = rad / d
        sqfree_part_ratios.append((k, d, rad, ratio, len(factors)))

    print(f"\n  Statistiques sur k=3..100 ({len(sqfree_part_ratios)} valeurs):")
    ratios = [r for _, _, _, r, _ in sqfree_part_ratios]
    num_factors = [n for _, _, _, _, n in sqfree_part_ratios]
    if ratios:
        print(f"    rad(d)/d : min = {min(ratios):.6f}, max = {max(ratios):.6f}, "
              f"moy = {sum(ratios)/len(ratios):.6f}")
        all_one = sum(1 for r in ratios if abs(r - 1.0) < 1e-10)
        print(f"    d squarefree (rad/d = 1): {all_one}/{len(ratios)}")
        print(f"    Nb facteurs premiers de d : min={min(num_factors)}, "
              f"max={max(num_factors)}, moy={sum(num_factors)/len(num_factors):.1f}")

# ================================================================
# I10. SYNTHÈSE
# ================================================================
print("\n" + "=" * 70)
print("I10. SYNTHÈSE SESSION 10f17")
print("=" * 70)

total_exceptions = len(non_squarefree) + len(phase2_non_sqfree) + len(extended_non_sqfree)

if total_exceptions == 0:
    print("""
★★★★★ RÉSULTAT PRINCIPAL :
  d(k) = 2^S - 3^k est squarefree pour TOUS les k ∈ [3, 200]
  (factorisation complète vérifiée)

  ET aucun petit p² (p ≤ 997) ne divise d pour k ∈ [3, 1000]

★★★★★ IMPLICATION POUR G2a :
  L'argument p-adique (R59) montre v_p(F_Z) = 0 pour tout p | d.
  Si d est squarefree (tous v_p(d) = 1), alors d ∤ F_Z est PROUVÉ
  car il existe p | d avec p ∤ F_Z (en fait TOUS les p | d ne divisent pas F_Z).

  MAIS : l'heuristique prédit ~9% d'exceptions squarefree.
  Le fait qu'on n'en trouve AUCUNE est REMARQUABLE et suggère
  une propriété structurelle profonde de d = 2^S - 3^k.

  DIRECTION :
  1. Prouver que d est squarefree → G2a résolu
  2. OU : renforcer l'argument p-adique pour couvrir d non-squarefree
  3. OU : montrer que même si p² | d, on a p² ∤ F_Z

  PROCHAINE ACTION :
  - Tester k jusqu'à 5000 avec factorisation partielle
  - Chercher un argument théorique pour la squarefree-ness
  - Investiguer si rad(d) divise F_Z (condition plus faible)
""")
else:
    print(f"""
  EXCEPTIONS TROUVÉES : {total_exceptions}

  L'argument p-adique simple ne suffit PAS pour tous les k.
  MAIS : vérifier si d ∤ F_Z reste vrai même pour d non-squarefree.

  DIRECTION :
  1. Pour les exceptions, vérifier directement F_Z mod d ≠ 0
  2. Chercher un argument p-adique RENFORCÉ : v_p(F_Z) < v_p(d)
  3. Ou : argument par la taille |F_Z/d| combiné avec non-divisibilité
""")

print("\n" + "=" * 70)
print("FIN SESSION 10f17")
print("=" * 70)
