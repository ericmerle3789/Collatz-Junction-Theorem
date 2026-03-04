#!/usr/bin/env python3
"""
FRONT 1 CORRIGE : Analyse profonde k=5 (d=13) + extension multi-k
==================================================================
Corrections :
  - Etat initial automate = 1 (pas 3^{k-1} mod d)
  - Automate avec contrainte positions croissantes (pas matrice T^{k-1})
  - Analyse algebrique complete
"""

from itertools import combinations
from collections import Counter, defaultdict
import math

def compute_corrsum_analysis(k):
    """Analyse complete de corrSum mod d pour un k donne."""
    S = math.ceil(k * math.log2(3))
    d = 2**S - 3**k
    C = math.comb(S - 1, k - 1)

    # Enumerer toutes les compositions
    positions_pool = list(range(1, S))  # {1, ..., S-1}
    compositions = []
    corrsum_values = []
    corrsum_mod_d = []

    for combo in combinations(positions_pool, k - 1):
        A = (0,) + combo
        # Horner correct : c0 = 2^0 = 1, c_j = 3*c_{j-1} + 2^{A_j}
        c = 1
        for j in range(1, k):
            c = 3 * c + 2**A[j]
        cs = c
        compositions.append(A)
        corrsum_values.append(cs)
        corrsum_mod_d.append(cs % d)

    residue_counts = Counter(corrsum_mod_d)
    N0 = residue_counts.get(0, 0)
    missing = sorted(set(range(d)) - set(residue_counts.keys()))

    return {
        'k': k, 'S': S, 'd': d, 'C': C, 'C_over_d': C/d,
        'N0': N0, 'compositions': compositions,
        'corrsum_values': corrsum_values, 'corrsum_mod_d': corrsum_mod_d,
        'residue_counts': residue_counts,
        'residues_hit': len(residue_counts), 'missing': missing,
        'cs_min': min(corrsum_values), 'cs_max': max(corrsum_values)
    }


def horner_automaton_correct(k, d, S):
    """
    Automate de Horner CORRECT avec positions croissantes.
    Etat initial = 1 (= 2^{A_0} mod d).
    Transition : c -> (3c + 2^p) mod d.
    On suit les chemins avec p₁ < p₂ < ... < p_{k-1}.
    """
    # Etat = (residue, last_position)
    # Au depart : residue = 1 mod d, last_position = 0 (= A_0)
    initial = {(1 % d, 0): 1}  # {(etat, derniere_pos): nombre_chemins}

    layers = [initial]
    for step in range(1, k):
        current = layers[-1]
        next_layer = defaultdict(int)
        for (state, last_pos), count in current.items():
            for p in range(last_pos + 1, S):
                next_state = (3 * state + 2**p) % d
                next_layer[(next_state, p)] += count
        layers.append(dict(next_layer))

    # Compter les etats finaux (sommant sur toutes les positions finales)
    final_counts = Counter()
    for (state, pos), count in layers[-1].items():
        final_counts[state] += count

    return layers, final_counts


def algebraic_structure(k, d, S):
    """Analyse la structure algebrique de Z/dZ pertinente pour corrSum."""
    # Ordre de 2 mod d
    ord2 = 1
    val = 2 % d
    while val != 1 and ord2 < d:
        val = (val * 2) % d
        ord2 += 1
    if val != 1:
        ord2 = None  # 2 n'est pas inversible

    # Ordre de 3 mod d
    ord3 = 1
    val = 3 % d
    while val != 1 and ord3 < d:
        val = (val * 3) % d
        ord3 += 1
    if val != 1:
        ord3 = None

    # h = 2/3 mod d
    if math.gcd(3, d) == 1:
        inv3 = pow(3, -1, d)
        h = (2 * inv3) % d
        # Ordre de h
        ordh = 1
        val = h
        while val != 1 and ordh < d:
            val = (val * h) % d
            ordh += 1
        if val != 1:
            ordh = None
    else:
        inv3 = None
        h = None
        ordh = None

    # Puissances de 2 mod d utilisees (positions 0 a S-1)
    pow2_mod = {p: pow(2, p, d) for p in range(S)}

    # Coefficients 3^{k-1-j} mod d
    coeff_mod = {j: pow(3, k-1-j, d) for j in range(k)}

    return {
        'ord2': ord2, 'ord3': ord3,
        'h': h, 'inv3': inv3, 'ordh': ordh,
        'pow2_mod': pow2_mod, 'coeff_mod': coeff_mod
    }


def find_invariants(corrsum_values, max_mod=50):
    """Cherche des residus systematiquement evites pour differents modulus."""
    results = {}
    for m in range(2, max_mod + 1):
        residues = set(cs % m for cs in corrsum_values)
        missing = sorted(set(range(m)) - residues)
        if missing:
            # Filtrer les cas triviaux (divisible par 2 ou 3)
            results[m] = {
                'hit': sorted(residues),
                'missing': missing,
                'fraction_missing': len(missing) / m
            }
    return results


# ============================================================
# MAIN : Execution complete
# ============================================================

print("=" * 80)
print("FRONT 1 CORRIGE : ANALYSE PROFONDE")
print("=" * 80)

# ============================================================
# PARTIE A : CAS k=5 EN DETAIL
# ============================================================

k = 5
result = compute_corrsum_analysis(k)
S, d, C = result['S'], result['d'], result['C']

print(f"\n{'='*80}")
print(f"CAS k={k} : S={S}, d={d}, C={C}, C/d={result['C_over_d']:.4f}, N₀={result['N0']}")
print(f"{'='*80}")

# Distribution mod d
print(f"\nDistribution corrSum mod {d} :")
for r in range(d):
    cnt = result['residue_counts'].get(r, 0)
    bar = '#' * cnt
    marker = " <<< CIBLE" if r == 0 else ""
    print(f"  r={r:2d} : {cnt:2d} {bar}{marker}")
print(f"Residus manquants : {result['missing']}")

# Structure algebrique
alg = algebraic_structure(k, d, S)
print(f"\nStructure algebrique de Z/{d}Z :")
print(f"  ord_{d}(2) = {alg['ord2']}")
print(f"  ord_{d}(3) = {alg['ord3']}")
print(f"  h = 2/3 mod {d} = {alg['h']}, ord(h) = {alg['ordh']}")
print(f"  2^S mod d = {pow(2,S,d)} (= 3^k mod d = {pow(3,k,d)}) [congruence fondamentale]")

print(f"\n  Puissances de 2 mod {d} pour p=0..{S-1} :")
for p in range(S):
    print(f"    2^{p} ≡ {alg['pow2_mod'][p]} mod {d}")

print(f"\n  Coefficients 3^{{k-1-j}} mod {d} pour j=0..{k-1} :")
for j in range(k):
    print(f"    3^{k-1-j} ≡ {alg['coeff_mod'][j]} mod {d}")

# ============================================================
# PARTIE B : AUTOMATE DE HORNER CORRECT
# ============================================================

print(f"\n{'='*80}")
print(f"AUTOMATE DE HORNER CORRECT (etat initial = 1)")
print(f"{'='*80}")

layers, final_counts = horner_automaton_correct(k, d, S)

print(f"\nEtat initial : 2^0 mod {d} = 1")
print(f"Cible : etat 0 en {k-1} pas avec positions croissantes")

for step, layer in enumerate(layers):
    states = Counter()
    for (s, p), c in layer.items():
        states[s] += c
    total = sum(states.values())
    unique = len(states)
    print(f"\n  Etape {step} : {total} chemins, {unique} etats distincts")
    for s in sorted(states.keys()):
        marker = " *" if s == 0 else ""
        print(f"    etat {s:2d} : {states[s]:4d} chemins{marker}")

print(f"\n--- Distribution finale (etape {k-1}) ---")
for s in range(d):
    cnt = final_counts.get(s, 0)
    marker = " <<< N₀(d)" if s == 0 else ""
    if cnt > 0 or s == 0:
        print(f"  etat {s:2d} : {cnt:3d} chemins{marker}")

print(f"\nN₀(d) par automate = {final_counts.get(0, 0)}")
print(f"N₀(d) par enumeration = {result['N0']}")
print(f"Coherent ? {final_counts.get(0, 0) == result['N0']}")
print(f"Total chemins = {sum(final_counts.values())} (doit etre C = {C})")

# ============================================================
# PARTIE C : EQUATION ALGEBRIQUE POUR corrSum ≡ 0
# ============================================================

print(f"\n{'='*80}")
print(f"EQUATION ALGEBRIQUE : corrSum ≡ 0 mod {d}")
print(f"{'='*80}")

# corrSum mod 13 = Σ_{j=0}^4 3^{4-j} · 2^{A_j} mod 13
# = 3·1 + 1·2^{A1} + 9·2^{A2} + 3·2^{A3} + 1·2^{A4} mod 13
# (car 3^4≡3, 3^3≡1, 3^2≡9, 3^1≡3, 3^0≡1 mod 13)

print(f"\ncoefficients 3^{{4-j}} mod 13 : ", [pow(3, k-1-j, d) for j in range(k)])
print(f"C'est le cycle (3, 1, 9) repete car ord_13(3) = 3")

vals_2p = {p: pow(2, p, d) for p in range(S)}
print(f"\nValeurs disponibles de 2^p mod 13 pour p=1..7 : {[vals_2p[p] for p in range(1, S)]}")
print(f"Ce sont TOUS les residus non-nuls sauf : ", end="")
all_vals = set(vals_2p[p] for p in range(1, S))
missing_vals = set(range(1, d)) - all_vals
print(f"{missing_vals if missing_vals else '{} (tout est couvert)'}")

print(f"\ncorrSum ≡ 0 mod 13")
print(f"⟺  3 + 2^A1 + 9·2^A2 + 3·2^A3 + 2^A4 ≡ 0 mod 13")
print(f"⟺  2^A1 + 9·2^A2 + 3·2^A3 + 2^A4 ≡ 10 mod 13")
print(f"\nLe terme constant (j=0, A0=0) vaut 3^4 · 2^0 = 81 ≡ 3 mod 13")
print(f"Donc il faut : somme_variable ≡ -3 ≡ 10 mod 13")

# Calculer la somme variable pour chaque composition
print(f"\nSomme variable pour chaque composition :")
target = (-pow(3, k-1, d)) % d
print(f"Cible = {target}")

for comp, cs in zip(result['compositions'], result['corrsum_values']):
    var_sum = 0
    terms = []
    for j in range(1, k):
        coeff = pow(3, k-1-j, d)
        val = pow(2, comp[j], d)
        term = (coeff * val) % d
        terms.append(f"{coeff}·{val}")
        var_sum = (var_sum + term) % d
    match = "=== HIT ===" if var_sum == target else ""
    print(f"  A={comp[1:]}: {' + '.join(terms)} ≡ {var_sum} mod 13 {match}")

# ============================================================
# PARTIE D : INVARIANTS MULTI-MODULUS
# ============================================================

print(f"\n{'='*80}")
print(f"RECHERCHE D'INVARIANTS (residus evites mod m, m=2..50)")
print(f"{'='*80}")

invariants = find_invariants(result['corrsum_values'], max_mod=50)

# Trier par fraction manquante decroissante
sorted_inv = sorted(invariants.items(), key=lambda x: x[1]['fraction_missing'], reverse=True)

for m, info in sorted_inv[:20]:  # Top 20
    if info['fraction_missing'] > 0.05:  # Plus de 5% manquant
        print(f"  mod {m:3d} : {len(info['missing']):3d}/{m} manquants ({info['fraction_missing']*100:.1f}%)")
        print(f"           manquants = {info['missing'][:15]}{'...' if len(info['missing']) > 15 else ''}")

# ============================================================
# PARTIE E : COMPARAISON MULTI-k (k=3..12)
# ============================================================

print(f"\n{'='*80}")
print(f"COMPARAISON MULTI-k : k=3..15")
print(f"{'='*80}")

print(f"\n{'k':>3} {'S':>3} {'d':>12} {'C':>10} {'C/d':>8} {'N0':>4} {'miss':>5} "
      f"{'ord2':>5} {'ord3':>5} {'ordh':>5} {'residus manquants mod d'}")
print("-" * 110)

for kk in range(3, 16):
    try:
        res = compute_corrsum_analysis(kk)
        alg_k = algebraic_structure(kk, res['d'], res['S'])
        miss_str = str(res['missing'][:5]) + ("..." if len(res['missing']) > 5 else "")
        print(f"{kk:3d} {res['S']:3d} {res['d']:12d} {res['C']:10d} {res['C_over_d']:8.4f} "
              f"{res['N0']:4d} {len(res['missing']):5d} "
              f"{str(alg_k['ord2']):>5} {str(alg_k['ord3']):>5} {str(alg_k['ordh']):>5} "
              f"{miss_str}")
    except Exception as e:
        print(f"{kk:3d} ... ERREUR : {e}")

# ============================================================
# PARTIE F : ANALYSE DE L'IMAGE DE corrSum mod d
# ============================================================

print(f"\n{'='*80}")
print(f"IMAGE DE corrSum : QUELLE FRACTION DE Z/dZ EST COUVERTE ?")
print(f"{'='*80}")

for kk in range(3, 16):
    try:
        res = compute_corrsum_analysis(kk)
        n_hit = res['residues_hit']
        n_miss = len(res['missing'])
        pct = n_hit / res['d'] * 100
        zero_in = 0 in set(res['corrsum_mod_d'])
        print(f"  k={kk:2d} : {n_hit:6d}/{res['d']:10d} residus couverts ({pct:5.1f}%), "
              f"manquants={n_miss:6d}, 0∈Image={zero_in}")
    except Exception as e:
        print(f"  k={kk:2d} : ERREUR {e}")

# ============================================================
# PARTIE G : STRUCTURE PROFONDE k=5 — Orbites de <2> dans Z/13Z*
# ============================================================

print(f"\n{'='*80}")
print(f"ORBITES DE <2> DANS (Z/13Z)* et STRUCTURE de corrSum")
print(f"{'='*80}")

k = 5
d = 13

# Orbites de la multiplication par 2 dans Z/13Z*
print(f"\nord_13(2) = {alg['ord2']} → <2> = (Z/13Z)* tout entier (2 est racine primitive)")

# Les sous-groupes de Z/13Z*
print(f"\nSous-groupes de (Z/13Z)* (cyclique d'ordre 12) :")
for div in [1, 2, 3, 4, 6, 12]:
    gen = pow(2, 12 // div, d)
    subgroup = set()
    val = 1
    for _ in range(div):
        subgroup.add(val)
        val = (val * gen) % d
    print(f"  Sous-groupe d'ordre {div:2d} : <{gen}> = {sorted(subgroup)}")

# Classe de corrSum dans les classes laterales de <3>
print(f"\nClasses laterales de <3> = {{1, 3, 9}} dans (Z/13Z)* :")
subgroup_3 = {1, 3, 9}
cosets = []
remaining = set(range(1, d))
while remaining:
    rep = min(remaining)
    coset = set((rep * s) % d for s in subgroup_3)
    cosets.append(coset)
    remaining -= coset

for i, coset in enumerate(cosets):
    print(f"  Coset {i} : {sorted(coset)}")

# Comment corrSum se repartit dans les cosets
print(f"\nRepartition de corrSum mod 13 dans les cosets de <3> :")
for i, coset in enumerate(cosets):
    count = sum(1 for r in result['corrsum_mod_d'] if r in coset)
    pct = count / C * 100
    print(f"  Coset {i} {sorted(coset)} : {count} compositions ({pct:.1f}%)")

# ============================================================
# PARTIE H : CONTRAINTE CYCLIQUE — corrSum mod ord_d(3)
# ============================================================

print(f"\n{'='*80}")
print(f"CONTRAINTE CYCLIQUE : ord_13(3) = 3")
print(f"{'='*80}")

print(f"""
Les coefficients 3^{{k-1-j}} mod 13 cyclent avec periode 3 :
  j=0 : 3^4 ≡ 3   (= 3^1)
  j=1 : 3^3 ≡ 1   (= 3^0)
  j=2 : 3^2 ≡ 9   (= 3^2)
  j=3 : 3^1 ≡ 3   (= 3^1)
  j=4 : 3^0 ≡ 1   (= 3^0)

Regroupons les termes par leur coefficient :
  Coeff 1 (j=1,4) : 2^A1 + 2^A4
  Coeff 3 (j=0,3) : 3·(1 + 2^A3) = 3·(2^0 + 2^A3)
  Coeff 9 (j=2)   : 9·2^A2

corrSum ≡ 3·(1 + 2^A3) + (2^A1 + 2^A4) + 9·2^A2  mod 13
""")

# Calculer ces sous-sommes pour chaque composition
print(f"Decomposition par coefficient :")
print(f"{'(A1,A2,A3,A4)':>15} | {'C1(2^A1+2^A4)':>14} | {'C3(1+2^A3)':>12} | {'C9(2^A2)':>10} | {'3·C3+C1+9·C9':>14} | {'mod13':>6}")
print("-" * 85)

for comp, cs in zip(result['compositions'], result['corrsum_values']):
    A1, A2, A3, A4 = comp[1], comp[2], comp[3], comp[4]

    c1 = (pow(2, A1, d) + pow(2, A4, d)) % d  # coeff 1
    c3 = (1 + pow(2, A3, d)) % d              # coeff 3 (avant multiplication)
    c9 = pow(2, A2, d)                         # coeff 9 (avant multiplication)

    total = (3 * c3 + c1 + 9 * c9) % d

    # C'est aussi (3 + c1_raw + 9*c9_raw + 3*c3_raw_extra) mais groupons autrement
    total_check = cs % d
    assert total == total_check, f"Incoherence: {total} vs {total_check}"

    print(f"{str(comp[1:]):>15} | {c1:14d} | {c3:12d} | {c9:10d} | {total:14d} | {total:6d}")

# ============================================================
# PARTIE I : ENERGIES ADDITIVES
# ============================================================

print(f"\n{'='*80}")
print(f"ENERGIE ADDITIVE E2(corrSum mod d)")
print(f"{'='*80}")

# E2 = |{(A,B) : corrSum(A) ≡ corrSum(B) mod d}|
counts = list(result['residue_counts'].values())
E2 = sum(c**2 for c in counts)
E2_random = C**2 / d  # Valeur attendue si uniforme

print(f"E2 = Σ N_r² = {E2}")
print(f"E2 (uniforme) = C²/d = {E2_random:.2f}")
print(f"Ratio E2/E2_random = {E2/E2_random:.4f}")
print(f"Note : ratio > 1 indique non-uniformite (clustering)")

# E4 (energie additive quadruple)
from itertools import product as iprod

E4 = 0
for r in range(d):
    E4 += result['residue_counts'].get(r, 0)**4
E4_random = C**4 / d**3

# Approximation via les moments
print(f"\nE4 = Σ N_r⁴ ≈ {E4}")
print(f"E4 (uniforme) = C⁴/d³ ≈ {E4_random:.2f}")

# ============================================================
# PARTIE J : SYNTHESE DES DECOUVERTES
# ============================================================

print(f"\n{'='*80}")
print(f"SYNTHESE DES DECOUVERTES — FRONT 1")
print(f"{'='*80}")

print(f"""
FAITS ETABLIS pour k=5, d=13, C=35, C/d=2.69 :

1. N₀(13) = 0 CONFIRME par enumeration et automate correct.

2. 12 sur 13 residus mod 13 sont atteints. SEUL 0 est manquant.

3. Structure algebrique :
   - ord_13(2) = 12 (2 est racine primitive mod 13)
   - ord_13(3) = 3 (coefficients cyclent avec periode 3)
   - h = 2/3 mod 13 = 5, ord(h) = 4
   - 2^8 = 256 ≡ 9 = 3² mod 13

4. L'equation corrSum ≡ 0 mod 13 se decompose en :
   3·(1 + 2^A3) + (2^A1 + 2^A4) + 9·2^A2 ≡ 0 mod 13
   Aucune solution parmi les 35 compositions.

5. Invariants detectes :
   - mod 2 : toujours 1 (impair)
   - mod 3 : jamais 0 (jamais div par 3)
   - mod 4 : seulement {{1, 3}} (impair)
   - mod 9 : evite {{0, 1, 3, 6}} — PLUS que "pas div par 3" !
   - mod 12 : seulement {{1, 5, 7, 11}} = impair et non-div-par-3

6. L'automate de Horner correct (etat initial = 1, cible = 0,
   k-1 = 4 pas, positions croissantes) confirme N₀ = 0.

QUESTIONS OUVERTES :
- Pourquoi le residu 0 est-il le SEUL manquant mod 13 ?
- L'invariant mod 9 (evite {{0,1,3,6}}) generalise-t-il aux autres k ?
- La periodicite 3 des coefficients cree-t-elle une obstruction algebrique ?
""")
