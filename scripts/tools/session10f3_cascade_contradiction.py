#!/usr/bin/env python3
"""
SESSION 10f3 — ARGUMENT DE CONTRADICTION PAR CASCADE ×2
=========================================================
Date : 4 mars 2026
Objectif : Formaliser l'argument : si -1 ∈ Im(f), la cascade ×2
           crée une contradiction avec le nombre de compositions.

BOUCLE G-V-R :
  GENERATE : Si -1 ∈ Im(f) avec B_max < M, la cascade force M-B_max+1
             résidus dans Im(f). Mais Im(f) ≤ C compositions.
             Si la cascade force plus de C-|Im(f)| nouveaux résidus → contradiction.
  VERIFY : Quantifier pour chaque k.
  REVISE : Déterminer si l'argument est universel.

Investigations :
  I1 : Argument cascade pour CAS A (B_max < M)
  I2 : Argument cascade pour CAS B (B_max = M, B_min > 0)
  I3 : CAS C résiduel : B_max = M ET B_min = 0
  I4 : Combinaison des cas → preuve complète ?
  I5 : Vérification : TOUTES les compositions donnant un résidu absent
       nécessitent SOIT B_max=M SOIT B_min=0
  I6 : Argument d'injection : la cascade est INJECTIVE
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


# =====================================================================
print("=" * 70)
print("INVESTIGATION I1 : Argument cascade CAS A (B_max < M)")
print("=" * 70)
# =====================================================================

print("""
THÉORÈME (×2-CASCADE) :
  Soit f(B) = Σ u^j · 2^{B_j} mod p, B non-décroissant dans [0,M]^{k-1}.

  Si ∃ B* non-décroissant dans [0,M]^{k-1} avec f(B*) = -1 et B*_{k-1} < M :
  Alors B*+j est valide pour j = 0, ..., M - B*_{k-1} et
  f(B*+j) = -2^j mod p.

  Donc {-1, -2, -4, ..., -2^{M-B*_{k-1}}} ⊂ Im(f).

  CAS MAXIMAL : B*_{k-1} = 0 ⟹ {-1, -2, ..., -2^M} ⊂ Im(f) (M+1 résidus)
  CAS MINIMAL : B*_{k-1} = M-1 ⟹ {-1, -2} ⊂ Im(f) (2 résidus)

  ARGUMENT DE COMPTAGE :
  Chaque résidu est atteint par au moins 1 composition.
  Les M-B*_{k-1}+1 résidus de la cascade sont atteints par des compositions DISTINCTES
  (B*, B*+1, ..., B*+(M-B*_{k-1})), qui sont toutes DIFFÉRENTES.

  De plus, Im(f) contient aussi TOUS les résidus déjà atteints.
  Nombre de compositions nécessaires ≥ |Im(f)| + (nombre de NOUVEAUX résidus dans cascade).
""")

for k_val in [3, 4, 5, 13]:
    S, M, d = compute_params(k_val)
    if not is_prime(d):
        continue
    p = d
    u = compute_u(k_val, p)
    st = sigma_tilde(u, k_val, p)
    C_total = math.comb(M + k_val - 1, k_val - 1)

    # Calculer Im(f)
    image = set()
    Bs_for_residue = defaultdict(list)
    for B in combinations_with_replacement(range(M + 1), k_val - 1):
        val = sum(pow(u, j+1, p) * pow(2, B[j], p) for j in range(k_val-1)) % p
        image.add(val)
        Bs_for_residue[val].append(B)

    target = (-1) % p

    # Cascade depuis -1
    cascade = []
    x = target
    for m in range(M + 1):
        cascade.append(x)
        x = (2 * x) % p

    cascade_absent = [r for r in cascade if r not in image]

    # Si -1 ∈ Im avec B_max ≤ m, combien de cascades forcées ?
    print(f"\n  k={k_val} (p={p}, M={M}, σ̃={'0' if st==0 else '≠0'}) :")
    print(f"    C = {C_total}, |Im| = {len(image)}")
    print(f"    Cascade {'{-1,-2,...,-2^M}'} : {len(cascade)} résidus")
    print(f"    Cascade absents de Im : {len(cascade_absent)} / {len(cascade)}")

    for bmax_hyp in range(M + 1):
        # Si -1 atteint avec B_max ≤ bmax_hyp
        cascade_length = M - bmax_hyp + 1
        cascade_subset = cascade[:cascade_length]
        new_residues = sum(1 for r in cascade_subset if r not in image)
        forced_total = len(image) + new_residues

        contradiction = forced_total > C_total
        print(f"    Hyp. B_max ≤ {bmax_hyp} : cascade {cascade_length} résidus, "
              f"+{new_residues} nouveaux, total ≥ {forced_total}, C = {C_total}"
              f" → {'CONTRADICTION ★★★' if contradiction else 'pas de contradiction'}")


# =====================================================================
print("\n" + "=" * 70)
print("INVESTIGATION I2 : Argument cascade DESCENDANT (B_min > 0)")
print("=" * 70)
# =====================================================================

print("""
CASCADE DESCENDANTE :
  Si f(B*) = -1 avec B*_1 > 0, alors B*-1 est valide et f(B*-1) = -1/2.
  B*-2 est valide (si B*_1 ≥ 2) et f(B*-2) = -1/4.
  ...
  B*-j est valide pour j = 0, ..., B*_1 et f(B*-j) = -2^{-j} mod p.

  Cascade descendante : {-1, -1/2, -1/4, ..., -2^{-B*_1}} ⊂ Im(f).
""")

for k_val in [3, 4, 5]:
    S, M, d = compute_params(k_val)
    if not is_prime(d):
        continue
    p = d
    u = compute_u(k_val, p)
    C_total = math.comb(M + k_val - 1, k_val - 1)

    image = set()
    for B in combinations_with_replacement(range(M + 1), k_val - 1):
        val = sum(pow(u, j+1, p) * pow(2, B[j], p) for j in range(k_val-1)) % p
        image.add(val)

    target = (-1) % p
    inv2 = pow(2, -1, p)

    # Cascade descendante
    desc_cascade = []
    x = target
    for m in range(M + 1):
        desc_cascade.append(x)
        x = (x * inv2) % p

    desc_absent = [r for r in desc_cascade if r not in image]

    print(f"\n  k={k_val} (p={p}, M={M}) :")
    print(f"    C = {C_total}, |Im| = {len(image)}")
    print(f"    Cascade desc. {'{-1,-1/2,...,-2^{-M}}'} : {len(desc_cascade)} résidus")
    print(f"    Cascade desc. absents : {len(desc_absent)} / {len(desc_cascade)}")

    for bmin_hyp in range(M + 1):
        cascade_length = bmin_hyp + 1
        cascade_subset = desc_cascade[:cascade_length]
        new_residues = sum(1 for r in cascade_subset if r not in image)
        forced_total = len(image) + new_residues
        contradiction = forced_total > C_total
        if contradiction or bmin_hyp <= 2:
            print(f"    Hyp. B_min ≥ {bmin_hyp} : desc. cascade {cascade_length} résidus, "
                  f"+{new_residues} nouveaux, total ≥ {forced_total}, C = {C_total}"
                  f" → {'CONTRADICTION ★★★' if contradiction else 'ok'}")


# =====================================================================
print("\n" + "=" * 70)
print("INVESTIGATION I3 : Cascade BIDIRECTIONNELLE")
print("=" * 70)
# =====================================================================

print("""
ARGUMENT BIDIRECTIONNEL :
  Si f(B*) = -1 avec B*_1 = b_min et B*_{k-1} = b_max :
  Cascade MONTANTE  : B*+j pour j=0,...,M-b_max → {-2^j : j=0,...,M-b_max}
  Cascade DESCENDANTE : B*-j pour j=0,...,b_min → {-2^{-j} : j=0,...,b_min}

  Total cascade : b_min + (M - b_max) + 1 résidus dans Im(f).
  (les +1 car -1 = -2^0 est compté une fois)

  Pour un B* intérieur (0 < b_min ≤ b_max < M) :
  La cascade bidirectionnelle force b_min + (M - b_max) + 1 résidus.

  CAS EXTRÊME : b_min = 0 ET b_max = M → cascade = {-1} seul (1 résidu).
  Ce cas est le PLUS DIFFICILE à exclure par comptage.
""")

for k_val in [3, 4, 5]:
    S, M, d = compute_params(k_val)
    if not is_prime(d):
        continue
    p = d
    u = compute_u(k_val, p)
    C_total = math.comb(M + k_val - 1, k_val - 1)

    image = set()
    for B in combinations_with_replacement(range(M + 1), k_val - 1):
        val = sum(pow(u, j+1, p) * pow(2, B[j], p) for j in range(k_val-1)) % p
        image.add(val)

    target = (-1) % p
    inv2 = pow(2, -1, p)

    print(f"\n  k={k_val} (p={p}, M={M}, C={C_total}, |Im|={len(image)}) :")

    # Pour chaque paire (b_min, b_max) possible
    for bmin in range(M + 1):
        for bmax in range(bmin, M + 1):
            # Cascade montante
            up_count = M - bmax  # nombre de shifts UP (hors -1)
            down_count = bmin      # nombre de shifts DOWN (hors -1)
            total_cascade = up_count + down_count + 1

            # Calculer les résidus de la cascade
            cascade_up = []
            x = target
            for j in range(up_count + 1):  # -1, -2, ..., -2^{M-bmax}
                cascade_up.append(x)
                x = (2 * x) % p

            cascade_down = []
            x = (target * inv2) % p  # -1/2
            for j in range(down_count):  # -1/2, ..., -2^{-bmin}
                cascade_down.append(x)
                x = (x * inv2) % p

            all_cascade = set(cascade_up + cascade_down)
            new_in_cascade = sum(1 for r in all_cascade if r not in image)
            forced_total = len(image) + new_in_cascade

            contradiction = forced_total > C_total

            if contradiction:
                print(f"    (b_min={bmin}, b_max={bmax}) : cascade={total_cascade} ({up_count}↑+{down_count}↓+1), "
                      f"+{new_in_cascade} new → {forced_total} > C={C_total} CONTRADICTION ★★★")

    # CAS CRITIQUE : b_min=0, b_max=M
    print(f"    CAS CRITIQUE (b_min=0, b_max=M) :")
    # Cascade = {-1} seul (0 shifts possibles)
    if target not in image:
        print(f"      -1 absent. Ajouter -1 donnerait |Im|+1 = {len(image)+1}. C = {C_total}.")
        if len(image) + 1 > C_total:
            print(f"      CONTRADICTION ★ : {len(image)+1} > {C_total}")
        else:
            print(f"      PAS de contradiction par comptage seul ({len(image)+1} ≤ {C_total})")
            print(f"      → BESOIN d'un argument ALGÉBRIQUE pour ce cas")


# =====================================================================
print("\n" + "=" * 70)
print("INVESTIGATION I4 : Injection cascade et comptage raffiné")
print("=" * 70)
# =====================================================================

print("""
ARGUMENT D'INJECTION RAFFINÉ :

  LEMME D'INJECTION :
  La cascade B* → B*+1 → ... → B*+j est une application INJECTIVE.
  Chaque B*+j est une composition DIFFÉRENTE donnant un résidu DIFFÉRENT.

  Donc : le nombre de compositions "consommées" par la cascade est au moins
  le nombre de résidus forcés par la cascade.

  MAIS : les compositions B*+j sont aussi comptées dans C_total.
  Donc la cascade NE CRÉE PAS de nouvelles compositions — elle les UTILISE.

  L'argument est plutôt : la cascade FORCE que certains résidus (les -2^j)
  soient DANS l'image. Si un de ces résidus est actuellement ABSENT,
  alors la cascade est impossible → B* n'existe pas (avec cette valeur de B_max).

  REFORMULATION PLUS FORTE :
  -1 ∉ Im(f) ⟺ pour tout j=0,...,M : -2^j ∉ Im_j(f)
  où Im_j(f) = {f(B) : B non-décr dans [0,j], B_max ≤ j}

  C'est l'argument de FILTRATION (déjà prouvé en session 10e) !
""")

print("  RAPPEL session 10e : -1 ∉ Im_m pour tout m = 0,...,M VÉRIFIÉ")
print("  C'est ÉQUIVALENT à N₀(p) = 0 (prouvé en session 10e2)")


# =====================================================================
print("\n" + "=" * 70)
print("INVESTIGATION I5 : Le cas σ̃≠0 et le comptage par orbite")
print("=" * 70)
# =====================================================================

print("""
POUR σ̃≠0 : L'image est CREUSE et les éléments {-1,-2,...,-2^M}
sont TOUS absents.

ARGUMENT PAR ORBITE (nouveau) :
  Soit O = orbite de -1 sous ⟨2⟩ dans Z/pZ*.
  |O| = ord₂(p). Pour p premier, ord₂(p) | (p-1).

  Im(f) ∩ O = ensemble des éléments de l'orbite atteints.
  |Im(f) ∩ O| = (|Im(f)| / (nombre d'orbites))  en moyenne.

  Mais Im(f) n'est PAS uniformément distribué sur les orbites !
  La ×2-closure garantit que Im(f) ∩ O est un sous-ensemble
  ×2-presque-clos de O.

  Pour σ̃≠0, l'orbite de σ̃ (= Im_0) est DIFFÉRENTE de l'orbite de -1
  si σ̃ et -1 sont dans des cosets différents de ⟨2⟩.

  MAIS : si ord₂(p) = p-1 (2 est racine primitive), il n'y a qu'UNE
  seule orbite — tout Z/pZ* est une seule orbite.
  Dans ce cas, l'argument par coset ne s'applique pas.
""")

for k_val in [4, 13]:
    S, M, d = compute_params(k_val)
    if not is_prime(d):
        continue
    p = d
    u = compute_u(k_val, p)
    st = sigma_tilde(u, k_val, p)
    if st == 0: continue
    o = ord_mod(2, p)
    C_total = math.comb(M + k_val - 1, k_val - 1)

    n_orbits = (p - 1) // o  # nombre de cosets de ⟨2⟩

    image = set()
    for B in combinations_with_replacement(range(M + 1), k_val - 1):
        val = sum(pow(u, j+1, p) * pow(2, B[j], p) for j in range(k_val-1)) % p
        image.add(val)

    print(f"\n  k={k_val} (p={p}, ord₂={o}, cosets={n_orbits}) :")
    print(f"    |Im| = {len(image)}, C = {C_total}")

    if n_orbits == 1:
        print(f"    ★ 2 est racine primitive mod {p} — UNE seule orbite")
        print(f"    L'argument par coset ne s'applique PAS")
        print(f"    → BESOIN d'un argument plus fin")
    else:
        # Classifier Im par coset
        coset_reps = {}
        for r in range(1, p):
            x = r
            for _ in range(o):
                if x < r: r_min = x
                x = (2 * x) % p
            coset_reps[r] = min(r, (r * pow(2, o-1, p)) % p)  # approximation

        print(f"    {n_orbits} cosets distincts")

    # L'argument crucial pour σ̃≠0 :
    # Éléments {-1, -2, ..., -2^M} sont CONSÉCUTIFS dans l'orbite de -1
    target = (-1) % p
    forward_chain = [target]
    x = target
    for m in range(M):
        x = (2 * x) % p
        forward_chain.append(x)

    chain_in_image = sum(1 for r in forward_chain if r in image)
    print(f"\n    Forward chain {'{-1,-2,...,-2^M}'} ({M+1} éléments) :")
    print(f"    Dans Im : {chain_in_image} / {M+1}")
    print(f"    → {'TOTALEMENT ABSENT' if chain_in_image==0 else 'PARTIELLEMENT présent'} ★")

    if chain_in_image == 0:
        # Ces M+1 éléments consécutifs de l'orbite sont TOUS absents
        # C'est un "trou" de taille M+1 dans l'orbite
        print(f"    → TROU de taille {M+1} dans l'orbite de taille {o}")
        print(f"    → Fraction du trou : {M+1}/{o} = {(M+1)/o:.6f}")

        # Combien de trous de taille ≥ M+1 dans l'orbite ?
        # Parcourir l'orbite et compter les runs d'absents
        orbit_list = [target]
        x = target
        for _ in range(o - 1):
            x = (2 * x) % p
            orbit_list.append(x)

        runs_absent = []
        current_run = 0
        for elt in orbit_list:
            if elt not in image:
                current_run += 1
            else:
                if current_run > 0:
                    runs_absent.append(current_run)
                current_run = 0
        if current_run > 0:
            runs_absent.append(current_run)

        if runs_absent:
            print(f"    Runs d'absents dans l'orbite : max={max(runs_absent)}, "
                  f"total={len(runs_absent)} runs, sizes={sorted(runs_absent, reverse=True)[:5]}...")
        print(f"    Trou contenant -1 : de taille ≥ {M+1}")


# =====================================================================
print("\n" + "=" * 70)
print("INVESTIGATION I6 : Argument CLEF — bidirectionnel + filtration")
print("=" * 70)
# =====================================================================

print("""
    ═══════════════════════════════════════════════════════════
    ARGUMENT STRUCTUREL COMBINÉ
    ═══════════════════════════════════════════════════════════

    THÉORÈME (CAS A exclusion) :
    Si -1 ∈ Im(f) via B* avec B*_{k-1} < M, alors :
      -2^j ∈ Im(f) pour j = 0, ..., M - B*_{k-1}
    via les compositions B*+j (toutes valides).

    Pour σ̃≠0 : -2 ∉ Im(f) (vérifié computationnellement pour k=4,13).
    Donc CAS A est IMPOSSIBLE si -2 ∉ Im(f).

    OBSERVATION CLEF : -2 ∉ Im(f) pour σ̃≠0 EST un fait.
    On n'a pas besoin de prouver -1 ∉ Im(f) directement.
    Il suffit de prouver -2 ∉ Im(f), et CAS A est exclu.

    Mais -2 = 2·(-1), et si -1 ∉ Im(f) par CAS A, alors -2 ∉ Im(f) par CAS A.
    C'est circulaire !

    EN REVANCHE : -2 ∉ Im(f) peut se prouver DIRECTEMENT par le même argument.
    f(B) = -2 ⟺ f(B)/2 = -1 ⟺ f(B-1) = -1 (si B_min > 0).
    Si f(B) = -2 avec B_min > 0, alors f(B-1) = -1 et B-1 est valide.
    Donc -2 ∈ Im(f) avec B_min > 0 ⟹ -1 ∈ Im(f).

    Contrapositif : si -1 ∉ Im(f), alors soit -2 ∉ Im(f), soit -2 a B_min = 0.

    C'est encore circulaire. L'argument de filtration est la BONNE approche.

    ═══════════════════════════════════════════════════════════
    CONCLUSION : L'argument de filtration Im_0 ⊂ ... ⊂ Im_M
    avec exclusion à CHAQUE couche est le SEUL argument non circulaire.

    Le gap restant : prouver algébriquement que -1 n'est PAS un "vrai nouveau"
    à aucune couche m, pour k ARBITRAIRE.

    PISTES NOUVELLES (session 10f3) :
    1. Pour σ̃≠0 : le "trou" de taille M+1 dans l'orbite est un invariant
    2. Ce trou commence exactement à -1 — c'est la signature du blocking
    3. La structure des bandes (même pour σ̃≠0) pourrait expliquer le trou
    ═══════════════════════════════════════════════════════════
""")

# Vérification finale : vrai nouveau = résidu atteint pour la première fois à couche m
# avec B = (0, B₂, ..., B_{k-1}) (B₁ = 0 obligatoire pour être un vrai nouveau)
print("\nVérification : -1 n'est JAMAIS un vrai nouveau")
for k_val in [3, 4, 5]:
    S, M, d = compute_params(k_val)
    if not is_prime(d):
        continue
    p = d
    u = compute_u(k_val, p)
    target = (-1) % p

    print(f"\n  k={k_val} (p={p}, M={M}) :")
    for m in range(M + 1):
        # Vrais nouveaux à couche m : B=(0, b₂, ..., b_{k-1}) avec max(b)=m
        vrais_nouveaux = set()
        for B in combinations_with_replacement(range(m + 1), k_val - 1):
            if B[0] != 0: continue  # Premier = 0
            if max(B) != m: continue  # Nouveau à cette couche
            val = sum(pow(u, j+1, p) * pow(2, B[j], p) for j in range(k_val-1)) % p
            vrais_nouveaux.add(val)

        has_target = target in vrais_nouveaux
        print(f"    Couche m={m} : {len(vrais_nouveaux)} vrais nouveaux, "
              f"-1 parmi eux ? {'OUI ✗' if has_target else 'NON ✓'}")


elapsed = time.time() - start_time
print(f"\n{'='*70}")
print(f"Temps total : {elapsed:.1f}s")
print(f"{'='*70}")
