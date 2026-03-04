#!/usr/bin/env python3
"""
SESSION 10f8b — DP OPTIMISÉ : bitarray pour grands k
======================================================
Date : 4 mars 2026
Objectif : Vérifier N₀(p)=0 pour chaque facteur premier de d,
  en utilisant un DP optimisé basé sur des arrays numpy.

L'approche :
  - State = (last_B, residue mod p) → boolean
  - Implémenté comme array 2D de taille (M+1) × p
  - Chaque couche j met à jour le tableau en O(M² × p)
  - Total : O(k × M² × p) — faisable si p < qq millions

Stratégie de couverture :
  1. Pour chaque k composé, vérifier CHAQUE facteur premier via DP
  2. Si un facteur bloque → Mec.I → N₀(d)=0
  3. Si aucun ne bloque → besoin de Mec.II (anti-corrélation)
"""

import math
import time
import sys

start_time = time.time()

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    if n < 1000000:
        i = 5
        while i*i <= n:
            if n % i == 0 or n % (i+2) == 0: return False
            i += 6
        return True
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
        if a >= n: continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1: continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1: break
        else:
            return False
    return True

def compute_params(k):
    S = math.ceil(k * math.log2(3))
    M = S - k
    d = (1 << S) - 3**k
    return S, M, d

def factorize_small(n, limit=10**7):
    factors = []
    temp = n
    for p in range(2, min(limit, int(temp**0.5) + 2)):
        while temp % p == 0:
            factors.append(p)
            temp //= p
    if temp > 1:
        factors.append(temp)
    return factors

def compute_u(k, p):
    return (2 * pow(3, -1, p)) % p


def dp_check_target_fast(k, p, M, target=None):
    """
    DP optimisé pour vérifier si target ∈ Im(f) mod p.

    State : reachable[last_B][residue] = True/False
    Implémenté comme liste de sets (pour la compacité).

    Pour p petit (< 100K) : utilise tableau 2D
    Pour p moyen (< 5M) : utilise dict de sets avec guard

    Retourne : (has_target: bool, n_residues: int) ou (None, None) si p trop grand.
    """
    if target is None:
        target = (-1) % p

    u = compute_u(k, p)
    u_pows = [pow(u, j, p) for j in range(k)]
    n_vars = k - 1

    # Guard : si p trop grand, skip
    if p > 2_000_000:
        return None, None

    # Précalculer les termes coeff * 2^b mod p pour chaque (j, b)
    # Pour chaque couche j, coeff = u^(j+1)
    # add_vals[b] = coeff * 2^b mod p

    # Layer 0 : variable B_1
    coeff = u_pows[1]
    current = [set() for _ in range(M + 1)]
    for b in range(M + 1):
        val = (coeff * pow(2, b, p)) % p
        current[b].add(val)

    # Layers 1 to n_vars-1
    for layer in range(1, n_vars):
        j = layer + 1  # index dans u_pows
        coeff = u_pows[j]

        # Précalculer add_vals
        add_vals = [(coeff * pow(2, b, p)) % p for b in range(M + 1)]

        new_current = [set() for _ in range(M + 1)]

        # Optimisation : accumuler les résidus "héritables"
        # Pour un nouveau b, on peut hériter de tous last_b ≤ b.
        # Donc on accumule au fur et à mesure.
        accumulated = set()
        for b in range(M + 1):
            # Ajouter les résidus de current[b] à l'accumulation
            accumulated.update(current[b])
            # Pour ce b comme nouveau choix, les résidus atteignables sont :
            add_val = add_vals[b]
            for r in accumulated:
                new_current[b].add((r + add_val) % p)

        # Guard mémoire
        total = sum(len(s) for s in new_current)
        if total > 10_000_000:
            return None, None

        current = new_current

    # Collecter tous les résidus finaux
    all_residues = set()
    for s in current:
        all_residues.update(s)

    return target in all_residues, len(all_residues)


# =====================================================================
print("=" * 70)
print("VALIDATION DP optimisé")
print("=" * 70)

test_cases = [
    (6, 5, False),     # N₀(5)>0 → -1 DANS image
    (6, 59, False),    # N₀(59)>0
    (6, 295, True),    # N₀(295)=0 → -1 PAS dans image
    (3, 5, True),      # N₀(5)=0
    (4, 47, True),     # N₀(47)=0
    (5, 13, True),     # N₀(13)=0
    (9, 13085, True),  # N₀(d)=0
    (10, 6487, True),  # N₀(d)=0
]

all_pass = True
for k_val, p_val, expected_absent in test_cases:
    S, M, d = compute_params(k_val)
    has, im_size = dp_check_target_fast(k_val, p_val, M)
    if has is not None:
        result_absent = not has
        ok = result_absent == expected_absent
        if not ok: all_pass = False
        print(f"  k={k_val}, p={p_val:>6d} : -1 absent={result_absent}, attendu={expected_absent} → {'PASS ✓' if ok else 'FAIL ✗'}")
    else:
        print(f"  k={k_val}, p={p_val:>6d} : skip (trop grand)")
        all_pass = False

print(f"  {'★ VALIDATION OK' if all_pass else '✗ ÉCHEC'}")

# =====================================================================
print("\n" + "=" * 70)
print("COUVERTURE k ∈ [3, 200] — d composé, facteur par facteur")
print("=" * 70)

mec1_count = 0
mec2_count = 0
inconnu_count = 0
echec_count = 0

# Aussi vérifier d premier
prime_verified = 0
prime_inconnu = 0

t_limit = 180  # 3 min max total

for k_val in range(3, 201):
    S, M, d = compute_params(k_val)
    if d <= 1:
        continue

    if time.time() - start_time > t_limit:
        print(f"\n  ⏰ Timeout global après k={k_val}")
        break

    if is_prime(d):
        # d premier : vérifier directement
        has, im_size = dp_check_target_fast(k_val, d, M)
        if has is not None:
            if not has:
                prime_verified += 1
            else:
                print(f"  k={k_val:3d} : d={d} (premier), -1 DANS IMAGE ✗✗✗")
                echec_count += 1
        else:
            prime_inconnu += 1
        continue

    # d composé
    factors = factorize_small(d)
    unique_primes = sorted(set(factors))

    blocking_factor = None
    all_solvable = True
    any_skip = False

    for pp in unique_primes:
        if pp < 5:
            continue

        has, im_size = dp_check_target_fast(k_val, pp, M)
        if has is None:
            any_skip = True
        elif not has:
            blocking_factor = pp
            break
        # else: has=True, solvable

    if blocking_factor:
        mec1_count += 1
    elif not any_skip:
        # Tous les facteurs sont solvables → vérifier mod d
        has_d, _ = dp_check_target_fast(k_val, d, M)
        if has_d is None:
            inconnu_count += 1
            if k_val <= 50:
                print(f"  k={k_val:3d} : d={d:>15d} (composé) | AUCUN facteur bloque, d trop grand pour DP")
        elif has_d:
            echec_count += 1
            print(f"  k={k_val:3d} : d={d} (composé) | ÉCHEC: -1 dans Im mod d ✗✗✗")
        else:
            mec2_count += 1
    else:
        # Certains facteurs skippés, aucun ne bloque
        # Essayer quand même mod d si d petit
        if d < 2_000_000:
            has_d, _ = dp_check_target_fast(k_val, d, M)
            if has_d is not None and not has_d:
                mec2_count += 1
            elif has_d is not None and has_d:
                echec_count += 1
                print(f"  k={k_val:3d} : d={d} | ÉCHEC ✗✗✗")
            else:
                inconnu_count += 1
        else:
            inconnu_count += 1

elapsed = time.time() - start_time
print(f"\n  Temps : {elapsed:.1f}s")
print(f"\n  ═══ RÉSUMÉ COMPLET k ∈ [3, 200] ═══")
print(f"  d premier :")
print(f"    N₀=0 vérifié  : {prime_verified}")
print(f"    INCONNU (DP)  : {prime_inconnu}")
print(f"  d composé :")
print(f"    Mécanisme I   : {mec1_count}")
print(f"    Mécanisme II  : {mec2_count}")
print(f"    INCONNU       : {inconnu_count}")
print(f"    ÉCHEC         : {echec_count}")

total_verified = prime_verified + mec1_count + mec2_count
total = prime_verified + prime_inconnu + mec1_count + mec2_count + inconnu_count + echec_count
print(f"\n  TOTAL : {total_verified}/{total} vérifiés N₀(d)=0")

if echec_count > 0:
    print(f"  ✗✗✗ {echec_count} CONTRE-EXEMPLES !")
else:
    print(f"  ★ AUCUN contre-exemple")

# =====================================================================
print("\n" + "=" * 70)
print("ANALYSE DES FACTEURS BLOQUANTS")
print("=" * 70)

print("""
  Pour les cas Mec.I : quel facteur bloque ?
  HYPOTHÈSE : c'est toujours le PLUS GRAND facteur premier.
""")

for k_val in range(3, 101):
    S, M, d = compute_params(k_val)
    if d <= 1 or is_prime(d):
        continue

    factors = factorize_small(d)
    unique_primes = sorted(set(factors))

    blocking = []
    non_blocking = []

    for pp in unique_primes:
        if pp < 5:
            continue
        has, im_size = dp_check_target_fast(k_val, pp, M)
        if has is None:
            continue
        if not has:
            blocking.append((pp, im_size))
        else:
            non_blocking.append((pp, im_size))

    if blocking:
        blk_str = ', '.join(f"{p}(|Im|={sz}/{p})" for p, sz in blocking)
        nb_str = ', '.join(f"{p}(|Im|={sz}/{p})" for p, sz in non_blocking[:3])
        print(f"  k={k_val:3d} : BLOQUE par {blk_str} ; non-bloquant : {nb_str}")
    elif non_blocking:
        nb_str = ', '.join(f"{p}(|Im|={sz}/{p})" for p, sz in non_blocking[:4])
        print(f"  k={k_val:3d} : AUCUN facteur ne bloque. Solvables : {nb_str}")


# =====================================================================
print("\n" + "=" * 70)
print("QUESTION CRITIQUE : Image mod petit premier")
print("=" * 70)

print("""
  Pour les petits premiers (5, 7, 11, 13), l'image SATURE-t-elle pour grand k ?
  Si oui : Mec.I ne peut JAMAIS fonctionner via ces petits premiers.
  La seule chance est que les GRANDS facteurs bloquent (si d composé)
  ou que d soit premier.
""")

small_primes = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

for pp in small_primes:
    print(f"\n  p = {pp} :")
    print(f"    k   | M  | |Im|/p | -1 ∈ Im ?")
    print(f"    ----|----|---------|---------")

    for k_val in range(3, 51):
        S, M, d = compute_params(k_val)
        if d <= 1:
            continue
        # Vérifier mod pp (indépendamment de la factorisation de d)
        # Il faut que pp | d pour que ce soit pertinent
        # Mais on peut quand même calculer l'image de f mod pp
        if d % pp != 0:
            continue  # pp n'est pas facteur de d pour ce k

        has, im_size = dp_check_target_fast(k_val, pp, M)
        if has is not None:
            ratio = im_size / pp
            print(f"    {k_val:3d} | {M:2d} | {ratio:6.3f}  | {'OUI' if has else 'NON'}")


elapsed = time.time() - start_time
print(f"\n  ═══ Temps total : {elapsed:.1f}s ═══")
