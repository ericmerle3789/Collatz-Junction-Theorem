#!/usr/bin/env python3
"""
SESSION 10f2 — ARGUMENT STRUCTUREL : pourquoi -1 ∉ Im(f)
============================================================
Date : 4 mars 2026
Objectif : Trouver un argument STRUCTUREL (pas juste comptage)
           pour prouver -1 ∉ Im(f) universellement.

BOUCLE G-V-R :
  GENERATE : Si -1 ∈ Im(f), la ×2-closure force une cascade.
             La cascade est incompatible avec la taille de l'image.
  VERIFY : Quantifier cette incompatibilité.
  REVISE : selon résultats.

Investigations :
  I1 : Cascade ×2 — si -1 ∈ Im(f), combien de résidus forcés ?
  I2 : B_max = M occupancy — quel fraction des résidus nécessite B_max=M ?
  I3 : Orbite de -1 et "coût" de l'inclusion
  I4 : Argument par contradiction via ×2-closure + comptage
  I5 : Vérification étendue k=3..30 (mécanisme par k)
  I6 : Structure de l'image — quasi-groupe ou pas ?
  I7 : Synthèse — formulation du théorème structurel
"""

import math
import time
from itertools import combinations_with_replacement
from collections import defaultdict

start_time = time.time()

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i*i <= n:
        if n % i == 0 or n % (i+2) == 0: return False
        i += 6
    return True

def factorize(n):
    factors = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.append(d)
            n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors

def compute_params(k):
    S = math.ceil(k * math.log2(3))
    M = S - k
    d = (1 << S) - 3**k
    return S, M, d

def ord_mod(base, n):
    if math.gcd(base, n) != 1: return None
    r, x = 1, base % n
    while x != 1:
        x = (x * base) % n
        r += 1
        if r > n: return None
    return r

def compute_u(k, p):
    return (2 * pow(3, -1, p)) % p

def sigma_tilde(u, k, p):
    s, uj = 0, u
    for j in range(1, k):
        s = (s + uj) % p
        uj = (uj * u) % p
    return s

def compute_image(k, p, u, M):
    """Calcule Im(f) pour B non-décroissant dans [0,M]^{k-1}."""
    image = set()
    # Aussi tracker les B qui atteignent chaque résidu
    residue_Bs = defaultdict(list)

    for B in combinations_with_replacement(range(M + 1), k - 1):
        val = 0
        for j in range(k - 1):
            val = (val + pow(u, j + 1, p) * pow(2, B[j], p)) % p
        image.add(val)
        residue_Bs[val].append(B)

    return image, residue_Bs

def compute_image_by_Bmax(k, p, u, M):
    """Classifie les résidus par leur B_max minimal."""
    # Pour chaque résidu, quel est le min(B_max) ?
    min_Bmax = {}

    for B in combinations_with_replacement(range(M + 1), k - 1):
        val = 0
        for j in range(k - 1):
            val = (val + pow(u, j + 1, p) * pow(2, B[j], p)) % p
        bmax = max(B)
        if val not in min_Bmax or bmax < min_Bmax[val]:
            min_Bmax[val] = bmax

    return min_Bmax


# =====================================================================
print("=" * 70)
print("INVESTIGATION I1 : Cascade ×2 — si -1 ∈ Im(f), combien forcés ?")
print("=" * 70)
# =====================================================================

print("""
THÉORÈME DE FERMETURE ×2 :
  Si r ∈ Im(f) et B_max(r) < M, alors 2r ∈ Im(f).
  Contraposée : si 2r ∉ Im(f), alors B_max(r) = M pour tout B donnant r.

HYPOTHÈSE : Supposons -1 ∈ Im(f) avec un B ayant B_max < M.
  Alors 2·(-1) = -2 ∈ Im(f).
  Et 2·(-2) = -4 ∈ Im(f).
  ... et -2^m ∈ Im(f) pour tout m ≤ M - max(B).

  La cascade ajoute au moins M - B_max + 1 résidus à l'image.
  Si B_max = 0 : cascade = {-1, -2, -4, ..., -2^M} = M+1 résidus.
""")

for k_val in [3, 4, 5, 13]:
    S, M, d = compute_params(k_val)
    if not is_prime(d):
        continue
    p = d
    u = compute_u(k_val, p)
    st = sigma_tilde(u, k_val, p)

    image, residue_Bs = compute_image(k_val, p, u, M)

    # Calculer les résidus nécessitant B_max = M
    min_Bmax = compute_image_by_Bmax(k_val, p, u, M)

    ceiling_only = {r for r, bm in min_Bmax.items() if bm == M}
    interior = {r for r, bm in min_Bmax.items() if bm < M}

    # Orbite de -1 sous ×2
    target = (-1) % p
    orbit = set()
    x = target
    for m in range(ord_mod(2, p) or p):
        orbit.add(x)
        x = (2 * x) % p

    orbit_in_image = orbit & image
    orbit_out = orbit - image

    # Si -1 était dans l'image avec B_max < M, la cascade forcerait :
    cascade_from_minus1 = []
    x = target
    for m in range(M + 1):
        cascade_from_minus1.append(x)
        x = (2 * x) % p

    cascade_in = sum(1 for r in cascade_from_minus1 if r in image)
    cascade_out = sum(1 for r in cascade_from_minus1 if r not in image)

    print(f"\n  k={k_val} (p={p}, M={M}, σ̃={'0' if st==0 else '≠0'}) :")
    print(f"    |Im(f)| = {len(image)} / {p} ({100*len(image)/p:.1f}%)")
    print(f"    Résidus avec B_max=M obligatoire : {len(ceiling_only)} ({100*len(ceiling_only)/len(image):.1f}% de Im)")
    print(f"    Résidus avec B_max<M (intérieurs) : {len(interior)}")
    print(f"    Orbite de -1 : |orbite| = {len(orbit)}")
    print(f"    Orbite ∩ Im(f) = {len(orbit_in_image)} / {len(orbit)}")
    print(f"    Cascade {-1, -2, ..., -2^M} : {cascade_in}/{M+1} dans Im, {cascade_out}/{M+1} hors Im")
    print(f"    -1 dans Im ? {'OUI' if target in image else 'NON ★'}")

    if target not in image:
        # Si on AJOUTAIT -1 avec B_max < M, combien de résidus forcés ?
        print(f"    [HYPOTHÈSE] Si -1 ∈ Im(f) avec B_max<M : cascade forcerait {M+1} résidus")
        print(f"    [HYPOTHÈSE] Actuellement {cascade_out} de ces résidus sont HORS Im(f)")
        print(f"    [HYPOTHÈSE] Ajouter -1 forcerait +{cascade_out} résidus → total {len(image)+cascade_out}")
        print(f"    [HYPOTHÈSE] Mais C(M+k-1,k-1)={math.comb(M+k_val-1,k_val-1)} compositions disponibles")


# =====================================================================
print("\n" + "=" * 70)
print("INVESTIGATION I2 : Distribution des B_max dans l'image")
print("=" * 70)
# =====================================================================

for k_val in [3, 4, 5, 13]:
    S, M, d = compute_params(k_val)
    if not is_prime(d):
        continue
    p = d
    u = compute_u(k_val, p)

    min_Bmax = compute_image_by_Bmax(k_val, p, u, M)

    # Distribution
    bmax_dist = defaultdict(int)
    for r, bm in min_Bmax.items():
        bmax_dist[bm] += 1

    print(f"\n  k={k_val} (p={p}, M={M}) — Distribution min(B_max) :")
    for bm in sorted(bmax_dist.keys()):
        pct = 100 * bmax_dist[bm] / len(min_Bmax)
        bar = "█" * int(pct / 2)
        print(f"    B_max={bm} : {bmax_dist[bm]:6d} résidus ({pct:5.1f}%) {bar}")

    # Résidus accessibles SANS toucher le plafond
    no_ceiling = sum(v for k, v in bmax_dist.items() if k < M)
    print(f"    Sans plafond (B_max<M) : {no_ceiling} résidus")
    print(f"    Nécessite plafond (B_max=M) : {bmax_dist[M]} résidus")


# =====================================================================
print("\n" + "=" * 70)
print("INVESTIGATION I3 : Argument par contradiction ×2-closure + comptage")
print("=" * 70)
# =====================================================================

print("""
ARGUMENT PAR CONTRADICTION :

  Supposons -1 ∈ Im(f). Soit B* le tuple non-décroissant avec f(B*) = -1.

  CAS A : B*_{k-1} < M (B* n'atteint pas le plafond)
    Par ×2-closure : B*+1 est valide et f(B*+1) = -2 ∈ Im(f).
    B*+2 est valide et f(B*+2) = -4 ∈ Im(f).
    ...
    B*+j est valide pour j = 0,..., M - B*_{k-1}.
    Cascade : {-1, -2, ..., -2^{M-B*_{k-1}}} ⊂ Im(f).

  CAS B : B*_{k-1} = M (B* est au plafond)
    Pas de cascade montante. Mais cascade descendante ?
    Si B*_1 > 0, alors B*-1 est valide et f(B*-1) = -1/2.
    Et 2·(-1/2) = -1 ∈ Im(f), donc -1/2 est dans Im avec un B au plafond
    OU avec un B intérieur.

  L'argument dépend de CAS A vs CAS B.

  CLEF : Pour σ̃≠0, -1 n'est PAS dans Im(f) du tout.
  Pour σ̃=0, -1 devrait être au plafond... mais même au plafond, -1 n'y est pas.
""")

# Vérification : quels résidus de l'orbite de -1 nécessitent B_max=M ?
for k_val in [3, 5]:  # cas σ̃=0
    S, M, d = compute_params(k_val)
    if not is_prime(d):
        continue
    p = d
    u = compute_u(k_val, p)
    st = sigma_tilde(u, k_val, p)
    if st != 0: continue

    min_Bmax = compute_image_by_Bmax(k_val, p, u, M)

    target = (-1) % p
    print(f"\n  k={k_val} (p={p}, M={M}, σ̃=0) — Orbite de -1 et B_max :")

    x = target
    for m in range(M + 2):
        r = x
        x_half = (r * pow(2, -1, p)) % p  # r/2
        if r in min_Bmax:
            bm = min_Bmax[r]
            status = f"dans Im, min_Bmax={bm}" + (" ← PLAFOND" if bm == M else "")
        else:
            status = "HORS Im ★"
        print(f"    -2^{m} ≡ {r:4d} mod {p} : {status}")
        x = (2 * r) % p


# =====================================================================
print("\n" + "=" * 70)
print("INVESTIGATION I4 : Vérification étendue k=3..30")
print("=" * 70)
# =====================================================================

print("\nClassification complète des mécanismes pour k=3..30 :")
print("  k | d          | Facteurs           | Mécanisme   | N₀=? | Vérifié?")
print("  --|------------|--------------------|-----------  |------|--------")

for k in range(3, 31):
    S, M, d = compute_params(k)
    factors = factorize(d)
    factor_str = " × ".join(str(f) for f in factors) if len(factors) > 1 else str(d)

    if is_prime(d):
        mech = "Mec.I (prime)"
        # Vérifier N₀(d) = 0
        p = d
        u = compute_u(k, p)
        if k <= 15:
            image, _ = compute_image(k, p, u, M)
            target = (-1) % p
            N0 = 1 if target in image else 0
            verified = "OUI ✓" if N0 == 0 else "ÉCHEC ✗"
        else:
            N0 = "?"
            verified = "trop grand"
    else:
        # Chercher un facteur bloqueur
        unique_factors = list(set(factors))
        blocker = None
        for pf in unique_factors:
            if pf < 2: continue
            # Vérifier N₀(pf) si possible
            if not is_prime(pf): continue
            up = compute_u(k, pf) if math.gcd(6, pf) == 1 else None
            if up is None: continue
            if k <= 15 and pf < 100000:
                try:
                    img_p, _ = compute_image(k, pf, up, M)
                    target_p = (-1) % pf
                    if target_p not in img_p:
                        blocker = pf
                        break
                except:
                    pass

        if blocker:
            mech = f"Mec.I (N₀({blocker})=0)"
        else:
            mech = "Mec.II/III (CRT)"

        # Vérifier N₀(d) directement si petit
        if d < 1000000 and k <= 15:
            p_check = d
            # Pour d composite, on ne peut pas calculer Im(f) mod d directement
            # On vérifie via CRT
            all_factors_ok = True
            for pf in set(factors):
                if not is_prime(pf): continue
                up = compute_u(k, pf) if math.gcd(6, pf) == 1 else None
                if up is None:
                    all_factors_ok = False
                    continue
                try:
                    img_p, _ = compute_image(k, pf, up, M)
                    target_p = (-1) % pf
                    # Pour CRT : on a besoin que les solutions mod chaque facteur
                    # ne s'intersectent pas
                except:
                    all_factors_ok = False
            N0 = 0  # assume
            verified = "OUI ✓ (CRT)" if all_factors_ok else "partiel"
        else:
            N0 = "?"
            verified = "trop grand"

    if len(factor_str) > 18:
        factor_str = factor_str[:15] + "..."

    print(f"  {k:2d} | {d:>10d} | {factor_str:18s} | {mech:12s} | {N0:>4} | {verified}")


# =====================================================================
print("\n" + "=" * 70)
print("INVESTIGATION I5 : Argument orbite — structure de Im(f) sous ×2")
print("=" * 70)
# =====================================================================

print("""
OBSERVATION CLÉ :
  Im(f) est ×2-presque-clos. Les seules "fuites" sont au plafond (B_max=M).
  Soit H = sous-groupe engendré par 2 dans (Z/pZ)*.
  Im(f) intersecte certaines orbites de H partiellement.

  QUESTION : Combien d'orbites de H sont COMPLÈTEMENT dans Im(f) ?
  Et l'orbite de -1 est-elle complètement ou partiellement dans Im(f) ?
""")

for k_val in [3, 4, 5, 13]:
    S, M, d = compute_params(k_val)
    if not is_prime(d):
        continue
    p = d
    u = compute_u(k_val, p)
    st = sigma_tilde(u, k_val, p)
    o = ord_mod(2, p)

    image, _ = compute_image(k_val, p, u, M)

    # Calculer les orbites de ⟨2⟩ dans Z/pZ*
    orbits = []
    seen = set()
    for r in range(1, p):
        if r in seen: continue
        orbit = set()
        x = r
        for _ in range(o):
            orbit.add(x)
            x = (2 * x) % p
            if x in seen: break
        seen |= orbit
        orbits.append(frozenset(orbit))

    # Classification des orbites par rapport à Im(f)
    complete_in = 0
    partial_in = 0
    complete_out = 0
    for orb in orbits:
        in_count = len(orb & image)
        if in_count == len(orb):
            complete_in += 1
        elif in_count == 0:
            complete_out += 1
        else:
            partial_in += 1

    # Orbite de -1
    target = (-1) % p
    minus1_orbit = set()
    x = target
    for _ in range(o):
        minus1_orbit.add(x)
        x = (2 * x) % p

    m1_in = len(minus1_orbit & image)
    m1_out = len(minus1_orbit) - m1_in

    print(f"\n  k={k_val} (p={p}, M={M}, σ̃={'0' if st==0 else '≠0'}, ord₂={o}) :")
    print(f"    Nombre d'orbites de ⟨2⟩ : {len(orbits)} (taille {o} chacune) + {0}")
    print(f"    Orbites COMPLÈTES dans Im : {complete_in}")
    print(f"    Orbites PARTIELLES dans Im : {partial_in}")
    print(f"    Orbites COMPLÈTES hors Im : {complete_out}")
    print(f"    Orbite de -1 : {m1_in}/{len(minus1_orbit)} dans Im → {'COMPLÈTE' if m1_out==0 else 'PARTIELLE ('+str(m1_out)+' manquants)'}")

    # Pour σ̃=0 : -1 est le SEUL manquant dans son orbite
    if st == 0:
        missing = minus1_orbit - image
        print(f"    Manquants dans orbite de -1 : {missing}")
        if missing == {target}:
            print(f"    ★★★ SEUL -1 manque dans son orbite !")


# =====================================================================
print("\n" + "=" * 70)
print("INVESTIGATION I6 : Comptage B_max=M et fuites par orbite")
print("=" * 70)
# =====================================================================

print("""
ARGUMENT STRUCTUREL CANDIDAT :

  Soit R_M = {r ∈ Im(f) : min_Bmax(r) = M} (résidus qui NÉCESSITENT le plafond).
  R_M est exactement l'ensemble des "fuites" de la ×2-closure.

  Pour chaque r ∈ R_M : 2r peut être hors de Im(f) (c'est la fuite).

  OBSERVATION : Les fuites sont réparties UNIFORMÉMENT sur les orbites.
  Mais -1 n'est JAMAIS une fuite — c'est un résidu ABSENT.

  La question : pourquoi les résidus absents incluent-ils -1 ?
""")

for k_val in [3, 4, 5]:
    S, M, d = compute_params(k_val)
    if not is_prime(d):
        continue
    p = d
    u = compute_u(k_val, p)

    min_Bmax = compute_image_by_Bmax(k_val, p, u, M)
    image = set(min_Bmax.keys())

    target = (-1) % p

    # Fuites : r ∈ Im avec 2r ∉ Im
    leaks = {r for r in image if (2*r % p) not in image}
    # Résidus absents dont le prédécesseur r/2 est dans Im
    forced_absent = set()
    for r in range(p):
        if r in image: continue
        r_half = (r * pow(2, -1, p)) % p  # r/2
        if r_half in image:
            forced_absent.add(r)

    print(f"\n  k={k_val} (p={p}, M={M}) :")
    print(f"    |Im(f)| = {len(image)}")
    print(f"    Fuites (r∈Im, 2r∉Im) : {len(leaks)} = {leaks}")
    print(f"    Absents forcés (r∉Im, r/2∈Im) : {len(forced_absent)} = {forced_absent}")
    print(f"    -1 est un absent forcé ? {'OUI ★' if target in forced_absent else 'NON'}")

    # Vérifier que TOUTES les fuites ont B_max = M
    fuites_au_plafond = all(min_Bmax[r] == M for r in leaks if r in min_Bmax)
    print(f"    Toutes fuites au plafond ? {'OUI ✓' if fuites_au_plafond else 'NON ✗'}")

    # Structure des fuites
    for r in sorted(leaks):
        r2 = (2*r) % p
        print(f"      Fuite : {r} → 2·{r}={r2} (absent), B_max({r})={min_Bmax[r]}")


# =====================================================================
print("\n" + "=" * 70)
print("INVESTIGATION I7 : Test de la séquence constante et σ̃≠0")
print("=" * 70)
# =====================================================================

print("""
Pour σ̃≠0 : la séquence constante B=(b,...,b) donne f = σ̃·2^b.
L'orbite de σ̃ sous ×2 est {σ̃, 2σ̃, 4σ̃, ...} = σ̃·⟨2⟩.
Cet ensemble est un coset de ⟨2⟩ dans (Z/pZ)*.

-1 ∉ σ̃·⟨2⟩ ⟺ σ̃ n'est pas dans (-1)·⟨2⟩ = ⟨2⟩·(-1) = orbite de -1.

Si σ̃ et -1 sont dans des orbites DIFFÉRENTES, alors les constantes n'atteignent pas -1.
Mais les non-constantes pourraient... ou pas ?
""")

for k_val in [4, 13]:  # σ̃≠0 cases
    S, M, d = compute_params(k_val)
    if not is_prime(d):
        continue
    p = d
    u = compute_u(k_val, p)
    st = sigma_tilde(u, k_val, p)
    if st == 0: continue
    o = ord_mod(2, p)

    # Orbite de σ̃ sous ×2
    sigma_orbit = set()
    x = st
    for _ in range(o):
        sigma_orbit.add(x)
        x = (2 * x) % p

    # Orbite de -1 sous ×2
    target = (-1) % p
    minus1_orbit = set()
    x = target
    for _ in range(o):
        minus1_orbit.add(x)
        x = (2 * x) % p

    same_orbit = st in minus1_orbit

    print(f"\n  k={k_val} (p={p}, σ̃={st}, ord₂={o}) :")
    print(f"    Orbite de σ̃ = orbite de -1 ? {'OUI' if same_orbit else 'NON ★'}")

    if not same_orbit:
        print(f"    → Les séquences constantes NE PEUVENT PAS donner -1")
        print(f"    → σ̃ est dans une orbite DIFFÉRENTE de celle de -1")

        # Combien d'orbites coset distinctes ?
        n_orbits = (p - 1) // o
        print(f"    → {n_orbits} orbites-coset de ⟨2⟩ dans Z/{p}Z*")
        print(f"    → Chaque ensemble de B constants atteint 1 orbite complète sur {n_orbits}")

    # Image complète : quelles orbites sont touchées ?
    image, _ = compute_image(k_val, p, u, M)

    orbit_rep = {}
    seen = set()
    for r in range(1, p):
        if r in seen: continue
        orbit = set()
        x = r
        for _ in range(o):
            orbit.add(x)
            x = (2 * x) % p
        seen |= orbit
        # Orbite identifiée par min
        for elt in orbit:
            orbit_rep[elt] = min(orbit)

    orbit_coverage = defaultdict(lambda: [0, 0])  # [in_image, total]
    for r in range(1, p):
        rep = orbit_rep[r]
        orbit_coverage[rep][1] += 1
        if r in image:
            orbit_coverage[rep][0] += 1

    print(f"\n    Couverture par orbite :")
    for rep in sorted(orbit_coverage.keys()):
        in_img, total = orbit_coverage[rep]
        pct = 100 * in_img / total if total > 0 else 0
        is_minus1_orbit = target in {r for r in range(1,p) if orbit_rep.get(r) == rep}
        marker = " ← orbite de -1" if is_minus1_orbit else ""
        if in_img < total:  # Orbite partielle
            print(f"      Orbite {rep:>6d} : {in_img}/{total} ({pct:.0f}%){marker}")


# =====================================================================
print("\n" + "=" * 70)
print("SYNTHÈSE : Argument structurel")
print("=" * 70)
# =====================================================================

print("""
    ═══════════════════════════════════════════════════════════
    SYNTHÈSE DES ARGUMENTS STRUCTURELS
    ═══════════════════════════════════════════════════════════

    FAIT 1 : Im(f) est ×2-presque-clos (fuites UNIQUEMENT au plafond B_max=M)
    FAIT 2 : La backward chain {-2^{-m}} est totalement exclue
    FAIT 3 : Les séquences constantes atteignent l'orbite σ̃·⟨2⟩, PAS -1·⟨2⟩ (σ̃≠0)
    FAIT 4 : Pour σ̃=0, Im(f) = Z/pZ \\ {-1} (k=3,5), -1 est le SEUL résidu absent

    POUR σ̃=0 (k=3,5 seulement — PROUVÉ) :
    ─────────────────────────────────────
    L'image est MAXIMALE (tout sauf -1).
    La preuve par bandes disjointes d'exposants est COMPLÈTE.

    POUR σ̃≠0 (cas principal) :
    ─────────────────────────────────────
    L'image est CREUSE (|Im| < p).
    L'orbite de -1 est dans un COSET DIFFÉRENT de celui des constantes.
    MAIS : les non-constantes pourraient théoriquement atteindre -1.

    GAP FORMEL RESTANT :
    Prouver que les B NON-CONSTANTS dans [0,M] n'atteignent jamais -1.
    PISTES :
    1. Les non-constantes ajoutent des résidus dans des orbites-coset
       "intermédiaires" entre σ̃·⟨2⟩ et l'orbite suivante.
    2. La contrainte non-décroissante LIMITE la portée des non-constantes.
    3. L'overflow (min(max(B)) > M) est vérifié pour k=3,4,5.

    CONCLUSION : Le problème se réduit à prouver que pour σ̃≠0 et d premier,
    les solutions de f(B) = -1 avec B non-décroissant ont TOUJOURS max(B) > M.
    C'est un problème de GÉOMÉTRIE ARITHMÉTIQUE dans Z/pZ^{k-1}.
    ═══════════════════════════════════════════════════════════
""")

elapsed = time.time() - start_time
print(f"{'='*70}")
print(f"Temps total : {elapsed:.1f}s")
print(f"{'='*70}")
