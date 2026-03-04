#!/usr/bin/env python3
"""
FRONT 1 : Analyse exhaustive du cas k=5, d=13
=============================================
Objectif : Comprendre POURQUOI N₀(13) = 0 alors que C/d = 2.69

Parametres :
  k = 5, S = ceil(5*log2(3)) = 8, d = 2^8 - 3^5 = 256 - 243 = 13
  C = binom(7,4) = 35 compositions
  Comp(8,5) = {A : 0=A₀ < A₁ < A₂ < A₃ < A₄ < 8}, A₀=0 fixe

corrSum(A) = 3⁴ + 3³·2^A₁ + 3²·2^A₂ + 3¹·2^A₃ + 3⁰·2^A₄
           = 81 + 27·2^A₁ + 9·2^A₂ + 3·2^A₃ + 2^A₄

On enumere toutes les 35 compositions et on analyse la distribution mod 13.
"""

from itertools import combinations
from collections import Counter
import math

# ============================================================
# SECTION 1 : ENUMERATION COMPLETE
# ============================================================

k = 5
S = math.ceil(k * math.log2(3))  # = 8
d = 2**S - 3**k  # = 256 - 243 = 13
C = math.comb(S - 1, k - 1)  # = binom(7,4) = 35

print("=" * 70)
print(f"FRONT 1 : ANALYSE EXHAUSTIVE  k={k}, S={S}, d={d}, C={C}")
print(f"C/d = {C/d:.4f}")
print("=" * 70)

# Les positions A₁, A₂, A₃, A₄ sont choisies parmi {1,2,3,4,5,6,7}
# (A₀ = 0 est fixe, positions dans {1,...,S-1} = {1,...,7})
positions_pool = list(range(1, S))  # [1, 2, 3, 4, 5, 6, 7]

compositions = []
corrsum_values = []
corrsum_mod_d = []

print(f"\n--- Enumeration des {C} compositions ---")
print(f"{'#':>3} | {'(A1,A2,A3,A4)':>15} | {'corrSum':>10} | {'mod {}'.format(d):>6} | {'corrSum/d':>10} | {'n0':>6}")
print("-" * 70)

for idx, combo in enumerate(combinations(positions_pool, k - 1)):
    A = (0,) + combo  # A₀=0, puis les k-1 positions choisies

    # corrSum = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{A_j}
    cs = sum(3**(k - 1 - j) * (2**A[j]) for j in range(k))

    cs_mod = cs % d
    n0 = cs // d if cs_mod == 0 else None

    compositions.append(A)
    corrsum_values.append(cs)
    corrsum_mod_d.append(cs_mod)

    n0_str = str(n0) if n0 is not None else "-"
    print(f"{idx+1:3d} | {str(combo):>15} | {cs:10d} | {cs_mod:6d} | {cs/d:10.2f} | {n0_str:>6}")

# ============================================================
# SECTION 2 : DISTRIBUTION MOD d
# ============================================================

print("\n" + "=" * 70)
print("DISTRIBUTION DES corrSum mod 13")
print("=" * 70)

residue_counts = Counter(corrsum_mod_d)

print(f"\n{'Residu r':>10} | {'Count N_r':>10} | {'Attendu C/d':>12} | {'Ratio':>8} | {'corrSum values':>30}")
print("-" * 80)

for r in range(d):
    count = residue_counts.get(r, 0)
    expected = C / d
    ratio = count / expected if expected > 0 else 0

    # Lister les corrSum qui tombent sur ce residu
    vals = [cs for cs, m in zip(corrsum_values, corrsum_mod_d) if m == r]
    vals_str = str(vals[:5]) + ("..." if len(vals) > 5 else "")

    marker = " <<<< CIBLE (N₀ = 0)" if r == 0 else ""
    print(f"{r:10d} | {count:10d} | {expected:12.2f} | {ratio:8.2f} | {vals_str:>30}{marker}")

print(f"\nTotal : {sum(residue_counts.values())} (verification : C = {C})")
print(f"Residus atteints : {len(residue_counts)}/{d}")
print(f"Residus manquants : {set(range(d)) - set(residue_counts.keys())}")

# ============================================================
# SECTION 3 : PROPRIETES ARITHMETIQUES
# ============================================================

print("\n" + "=" * 70)
print("PROPRIETES ARITHMETIQUES DE corrSum")
print("=" * 70)

print(f"\n--- Parite ---")
parities = [cs % 2 for cs in corrsum_values]
print(f"corrSum mod 2 : {Counter(parities)}")
print(f"Tous impairs ? {all(p == 1 for p in parities)}")

print(f"\n--- Mod 3 ---")
mod3 = [cs % 3 for cs in corrsum_values]
print(f"corrSum mod 3 : {Counter(mod3)}")
print(f"Aucun divisible par 3 ? {all(m != 0 for m in mod3)}")

print(f"\n--- Mod 4 ---")
mod4 = [cs % 4 for cs in corrsum_values]
print(f"corrSum mod 4 : {Counter(mod4)}")

print(f"\n--- Mod 6 ---")
mod6 = [cs % 6 for cs in corrsum_values]
print(f"corrSum mod 6 : {Counter(mod6)}")

print(f"\n--- Mod 13 (= d) ---")
print(f"corrSum mod 13 : {Counter(corrsum_mod_d)}")

# ============================================================
# SECTION 4 : PLAGE DE corrSum ET MULTIPLES DE d
# ============================================================

print("\n" + "=" * 70)
print("ANALYSE DE PLAGE ET MULTIPLES")
print("=" * 70)

cs_min = min(corrsum_values)
cs_max = max(corrsum_values)

print(f"corrSum min = {cs_min} (composition {compositions[corrsum_values.index(cs_min)]})")
print(f"corrSum max = {cs_max} (composition {compositions[corrsum_values.index(cs_max)]})")
print(f"Plage : [{cs_min}, {cs_max}]")
print(f"Largeur : {cs_max - cs_min}")

# Multiples de d dans la plage
multiples_in_range = [m * d for m in range(cs_min // d, cs_max // d + 1) if cs_min <= m * d <= cs_max]
print(f"\nMultiples de d={d} dans [{cs_min}, {cs_max}] :")
for m in multiples_in_range:
    n0 = m // d
    print(f"  {m} = {n0} * {d}")
print(f"Nombre de multiples : {len(multiples_in_range)}")
print(f"Ratio multiples/compositions : {len(multiples_in_range)/C:.3f}")

# Les corrSum realises qui sont proches d'un multiple de d
print(f"\nProximite des corrSum aux multiples de d :")
for cs in sorted(corrsum_values):
    nearest_multiple = round(cs / d) * d
    distance = cs - nearest_multiple
    print(f"  corrSum={cs:6d}, plus proche multiple = {nearest_multiple:6d}, distance = {distance:+4d}, mod {d} = {cs % d}")

# ============================================================
# SECTION 5 : AUTOMATE DE HORNER mod d
# ============================================================

print("\n" + "=" * 70)
print("AUTOMATE DE HORNER mod 13")
print("=" * 70)

print("""
Recurrence de Horner : c₀ = 1 (car 3^{k-1} * 2^0 = 81 et on normalise)
  c_j = (3 * c_{j-1} + 2^{p_j}) mod d

Automate : d=13 etats, transition c → (3c + 2^p) mod 13
  Etat initial : c₀ = 3^4 mod 13 = 81 mod 13 = 3
  Etat cible : 0
  Nombre de pas : k-1 = 4
  Positions : p₁ < p₂ < p₃ < p₄ dans {1,...,7}
""")

# Etat initial
c0 = (3**(k-1)) % d
print(f"Etat initial : 3^{k-1} mod {d} = {3**(k-1)} mod {d} = {c0}")

# Table de transition complete
print(f"\nTable de transition : (3*c + 2^p) mod {d}")
print(f"{'c\\p':>4}", end="")
for p in range(1, S):
    print(f" | p={p:2d}", end="")
print()
print("-" * (6 + 8 * (S - 1)))

transition = {}
for c in range(d):
    print(f"{c:4d}", end="")
    for p in range(1, S):
        next_c = (3 * c + 2**p) % d
        transition[(c, p)] = next_c
        print(f" | {next_c:4d}", end="")
    print()

# Tracer tous les chemins de 4 pas depuis c0
print(f"\n--- Tous les chemins de longueur 4 depuis c₀={c0} ---")
print(f"{'Positions':>15} | {'Chemin etats':>25} | {'Etat final':>12} | {'= 0 ?':>6}")
print("-" * 70)

paths_to_zero = 0
for combo in combinations(range(1, S), k - 1):
    state = c0
    path = [state]
    for p in combo:
        state = (3 * state + 2**p) % d
        path.append(state)

    is_zero = "OUI" if state == 0 else "non"
    if state == 0:
        paths_to_zero += 1
    print(f"{str(combo):>15} | {str(path):>25} | {state:12d} | {is_zero:>6}")

print(f"\nNombre de chemins atteignant 0 : {paths_to_zero} (= N₀(d) = {paths_to_zero})")

# ============================================================
# SECTION 6 : STRUCTURE DE L'ORBITE DE h = 2/3 mod d
# ============================================================

print("\n" + "=" * 70)
print("STRUCTURE ALGEBRIQUE : h = 2 * 3^{-1} mod 13")
print("=" * 70)

# Inverse de 3 mod 13
inv3 = pow(3, -1, d)
h = (2 * inv3) % d
print(f"3^(-1) mod {d} = {inv3}")
print(f"h = 2/3 mod {d} = {h}")
print(f"Verification : 3 * {inv3} mod {d} = {(3 * inv3) % d}")

# Orbite de h dans (Z/dZ)*
orbit = []
current = 1
for i in range(d + 1):
    orbit.append(current)
    if current == 1 and i > 0:
        break
    current = (current * h) % d

print(f"\nOrbite de h={h} dans (Z/{d}Z)* :")
print(f"Ordre de h : {len(orbit) - 1}")
for i, v in enumerate(orbit):
    print(f"  h^{i} = {v}")

# Les puissances de 2 mod d
print(f"\nPuissances de 2 mod {d} :")
for p in range(S):
    print(f"  2^{p} mod {d} = {(2**p) % d}")

# Les puissances de 3 mod d
print(f"\nPuissances de 3 mod {d} :")
for j in range(k):
    print(f"  3^{j} mod {d} = {(3**j) % d}")

# ============================================================
# SECTION 7 : corrSum REFORMULE via h
# ============================================================

print("\n" + "=" * 70)
print("REFORMULATION : corrSum = 3^{k-1} * (1 + Σ h^{A_j}) mod d")
print("=" * 70)

# corrSum = Σ 3^{k-1-j} * 2^{A_j}
# En factorisant 3^{k-1} et utilisant h = 2/3 mod d :
# corrSum = 3^{k-1} * Σ (2/3)^{A_j} * 3^{A_j - A_j} ...
# Plus precisement :
# corrSum = Σ_{j=0}^{k-1} 3^{k-1-j} * 2^{A_j}
# = 3^{k-1} * Σ_{j=0}^{k-1} (2/3)^j * ... Non, les poids dependent de j ET de A_j.

# Forme plus utile : corrSum = Σ_{j=0}^{k-1} 3^{k-1-j} * 2^{A_j}
# Avec substitution : soit w_j = 2^{A_j}, alors
# corrSum = Σ 3^{k-1-j} * w_j = evaluation de Horner

# Via h : corrSum/3^{k-1} = Σ (2/3)^{???}...
# En fait, h^p = (2/3)^p mod d = 2^p * 3^{-p} mod d
# Donc 3^{k-1-j} * 2^{A_j} = 3^{k-1} * 3^{-j} * 2^{A_j} = 3^{k-1} * (2^{A_j}/3^j)
# Mais A_j et j ne sont pas directement lies...

# La bonne reformulation :
# corrSum ≡ 0 mod d  ssi  Σ_{j=0}^{k-1} 3^{k-1-j} * 2^{A_j} ≡ 0 mod d
# En divisant par 3^{k-1} (inversible mod d car gcd(3,d)=gcd(3,13)=1) :
# Σ_{j=0}^{k-1} 3^{-j} * 2^{A_j} ≡ 0 mod d
# = Σ_{j=0}^{k-1} (3^{-1})^j * 2^{A_j}
# = Σ_{j=0}^{k-1} (inv3)^j * 2^{A_j}

print(f"3^{{-1}} mod {d} = {inv3}")
print(f"\ncorrSum ≡ 0 mod {d}")
print(f"⟺  Σ_{{j=0}}^{{{k-1}}} {inv3}^j · 2^{{A_j}} ≡ 0 mod {d}")
print(f"\nCalcul pour chaque composition :")

for idx, (combo_full, cs) in enumerate(zip(compositions, corrsum_values)):
    # combo_full = (0, A1, A2, A3, A4)
    terms = []
    total = 0
    for j in range(k):
        term = (pow(inv3, j, d) * pow(2, combo_full[j], d)) % d
        terms.append(term)
        total = (total + term) % d

    print(f"  A={combo_full}: Σ = {' + '.join(str(t) for t in terms)} ≡ {total} mod {d}  (corrSum={cs}, corrSum mod d={cs%d})")

# ============================================================
# SECTION 8 : MATRICE DE TRANSFERT ET SPECTRE
# ============================================================

print("\n" + "=" * 70)
print("MATRICE DE TRANSFERT T")
print("=" * 70)

import numpy as np

# Matrice T : T[i][j] = nombre de positions p dans {1,...,7} telles que (3*i + 2^p) mod d = j
T_matrix = np.zeros((d, d), dtype=int)

for i in range(d):
    for p in range(1, S):
        j = (3 * i + 2**p) % d
        T_matrix[i][j] += 1

print(f"Matrice T ({d}x{d}) : T[i][j] = |{{p ∈ {{1,...,{S-1}}} : (3i + 2^p) mod {d} = j}}|")
print(f"\n{T_matrix}")

# Vecteur initial : e_{c0} (etat c0)
e_c0 = np.zeros(d)
e_c0[c0] = 1

# T^{k-1} * e_{c0} = distribution apres k-1 pas
# N₀(d) = (T^{k-1} * e_{c0})[0]

T_power = np.linalg.matrix_power(T_matrix, k - 1)
result_vector = T_power @ e_c0

print(f"\nVecteur e_{{c0}} = e_{c0} (etat initial = {c0})")
print(f"\n(T^{k-1}) · e_{c0} = distribution apres {k-1} pas :")
for state in range(d):
    count = int(result_vector[state])
    marker = " <<<< N₀(d)" if state == 0 else ""
    print(f"  Etat {state:2d} : {count:5d} chemins{marker}")

print(f"\nVerification : total = {int(sum(result_vector))} (doit etre C = {C})")

# Valeurs propres
print(f"\n--- Spectre de T ---")
eigenvalues = np.linalg.eigvals(T_matrix.astype(float))
eigenvalues_sorted = sorted(eigenvalues, key=lambda x: abs(x), reverse=True)

for i, ev in enumerate(eigenvalues_sorted):
    print(f"  λ_{i} = {ev:.6f}  (|λ| = {abs(ev):.6f})")

print(f"\nRayon spectral : {max(abs(ev) for ev in eigenvalues):.6f}")
print(f"Gap spectral (|λ₀| - |λ₁|) : {abs(eigenvalues_sorted[0]) - abs(eigenvalues_sorted[1]):.6f}")

# ============================================================
# SECTION 9 : GRAPHE D'ACCESSIBILITE DEPUIS c0
# ============================================================

print("\n" + "=" * 70)
print(f"GRAPHE D'ACCESSIBILITE DEPUIS c₀={c0}")
print("=" * 70)

# BFS depuis c0 avec contrainte de positions croissantes
from collections import deque

# Etats accessibles a chaque etape
print(f"\nEtats accessibles a chaque etape (positions croissantes) :")

# Etape 0 : {c0}
# Etape j : depuis chaque (etat, derniere_position), appliquer p > derniere_position

# Format : (etat, derniere_position_utilisee)
current_states = {(c0, 0)}  # Apres A0=0, etat = c0

for step in range(1, k):
    next_states = set()
    for (state, last_pos) in current_states:
        for p in range(last_pos + 1, S):
            next_state = (3 * state + 2**p) % d
            next_states.add((next_state, p))

    states_only = sorted(set(s for s, _ in next_states))
    print(f"  Etape {step} : {len(next_states)} paires (etat, pos), etats uniques = {states_only}")
    current_states = next_states

# Etats finaux
final_states = Counter(s for s, _ in current_states)
print(f"\nDistribution des etats finaux (= corrSum mod d) :")
for state in range(d):
    count = final_states.get(state, 0)
    marker = " <<<< CIBLE" if state == 0 else ""
    if count > 0 or state == 0:
        print(f"  Etat {state:2d} : {count:3d} chemins{marker}")

# ============================================================
# SECTION 10 : RECHERCHE D'INVARIANTS
# ============================================================

print("\n" + "=" * 70)
print("RECHERCHE D'INVARIANTS SUPPLEMENTAIRES")
print("=" * 70)

# Tester corrSum mod m pour differents m
print(f"\ncorrSum mod m pour m = 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13 :")
for m in range(2, 14):
    residues = sorted(set(cs % m for cs in corrsum_values))
    missing = sorted(set(range(m)) - set(residues))
    print(f"  mod {m:2d} : residus atteints = {residues}")
    if missing:
        print(f"          residus MANQUANTS = {missing}")

# Tester des combinaisons lineaires
print(f"\n--- Somme des positions mod d ---")
for combo, cs in zip(compositions, corrsum_values):
    pos_sum = sum(combo)
    print(f"  A={combo}, Σ positions = {pos_sum}, corrSum mod {d} = {cs % d}")

# Tester la parite de la somme des positions
print(f"\n--- Parite de Σ positions vs corrSum mod d ---")
parity_residue = {}
for combo, cs in zip(compositions, corrsum_values):
    par = sum(combo) % 2
    r = cs % d
    if par not in parity_residue:
        parity_residue[par] = []
    parity_residue[par].append(r)

for par in sorted(parity_residue):
    residues = sorted(set(parity_residue[par]))
    print(f"  Parite Σ pos = {par} : residus mod {d} = {residues}")

print("\n" + "=" * 70)
print("FIN DE L'ANALYSE FRONT 1")
print("=" * 70)
