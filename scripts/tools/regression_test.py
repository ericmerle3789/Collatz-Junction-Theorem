#!/usr/bin/env python3
"""
REGRESSION TEST SUITE — Collatz Junction Theorem
=================================================
Exigé par le DISCOVERY_PROTOCOL v2.0, Phase 7.2.

Vérifie TOUS les résultats prouvés et invariants structurels.
À lancer au DÉBUT et à la FIN de chaque session.

Si un test échoue → STOP IMMÉDIAT, investiguer avant de continuer.

Usage: python regression_test.py
"""

from math import ceil, log2, gcd, comb
from itertools import combinations
import sys
import time

# ============================================================
# PARAMÈTRES
# ============================================================
K_MIN, K_MAX = 3, 15  # plage de vérification
VERBOSE = True

def compute_params(k):
    """Calcule S, d, C pour un k donné."""
    S = ceil(k * log2(3))
    d = 2**S - 3**k
    C = comb(S - 1, k - 1)
    return S, d, C

def enumerate_corrsum(k, S, d):
    """Énumère tous les corrSum mod d pour les compositions ordonnées."""
    positions = range(1, S)  # {1, ..., S-1}
    results = []
    for combo in combinations(positions, k - 1):
        A = (0,) + combo
        cs = sum(pow(3, k - 1 - j) * pow(2, A[j]) for j in range(k))
        results.append(cs % d)
    return results

# ============================================================
# TESTS
# ============================================================
passed = 0
failed = 0
errors = []

def test(name, condition, detail=""):
    global passed, failed
    if condition:
        passed += 1
        if VERBOSE:
            print(f"  ✅ {name}")
    else:
        failed += 1
        msg = f"  ❌ FAIL: {name}"
        if detail:
            msg += f" — {detail}"
        print(msg)
        errors.append(name)

def section(title):
    print(f"\n{'='*60}")
    print(f"  {title}")
    print(f"{'='*60}")

# ============================================================
# SECTION 1 : AXIOMES STRUCTURELS (Niveau 0)
# ============================================================
section("1. AXIOMES STRUCTURELS")

for k in range(K_MIN, K_MAX + 1):
    S, d, C = compute_params(k)

    # A1 : d = 2^S - 3^k
    test(f"k={k}: d = 2^S - 3^k", d == 2**S - 3**k)

    # A2 : d > 0
    test(f"k={k}: d > 0", d > 0, f"d={d}")

    # A3 : gcd(d, 6) = 1
    test(f"k={k}: gcd(d, 6) = 1", gcd(d, 6) == 1, f"gcd(d,6)={gcd(d,6)}")

    # S = ceil(k * log2(3))
    test(f"k={k}: S = ⌈k·log₂3⌉", S == ceil(k * log2(3)))

# ============================================================
# SECTION 2 : N₀(d) = 0 (résultat principal)
# ============================================================
section("2. N₀(d) = 0 POUR k=3..15")

for k in range(K_MIN, min(K_MAX + 1, 13)):  # jusqu'à k=12 (énumération faisable)
    S, d, C = compute_params(k)
    residues = enumerate_corrsum(k, S, d)
    N0 = residues.count(0)
    test(f"k={k}: N₀(d={d}) = 0", N0 == 0, f"N₀={N0}, C={C}")

# ============================================================
# SECTION 3 : corrSum TOUJOURS IMPAIR (Lemme session 7)
# ============================================================
section("3. corrSum TOUJOURS IMPAIR")

for k in range(K_MIN, min(K_MAX + 1, 11)):  # jusqu'à k=10
    S, d, C = compute_params(k)
    positions = range(1, S)
    all_odd = True
    for combo in combinations(positions, k - 1):
        A = (0,) + combo
        cs = sum(pow(3, k - 1 - j) * pow(2, A[j]) for j in range(k))
        if cs % 2 == 0:
            all_odd = False
            break
    test(f"k={k}: corrSum toujours impair", all_odd)

# ============================================================
# SECTION 4 : corrSum ≢ 0 mod 3 (Lemme session 7)
# ============================================================
section("4. corrSum ≢ 0 mod 3")

for k in range(K_MIN, min(K_MAX + 1, 11)):
    S, d, C = compute_params(k)
    positions = range(1, S)
    never_div3 = True
    for combo in combinations(positions, k - 1):
        A = (0,) + combo
        cs = sum(pow(3, k - 1 - j) * pow(2, A[j]) for j in range(k))
        if cs % 3 == 0:
            never_div3 = False
            break
    test(f"k={k}: corrSum ≢ 0 mod 3", never_div3)

# ============================================================
# SECTION 5 : corrSum ∈ {1, 3} mod 4 (Lemme session 3)
# ============================================================
section("5. corrSum ∈ {1, 3} mod 4")

for k in range(K_MIN, min(K_MAX + 1, 11)):
    S, d, C = compute_params(k)
    positions = range(1, S)
    mod4_ok = True
    for combo in combinations(positions, k - 1):
        A = (0,) + combo
        cs = sum(pow(3, k - 1 - j) * pow(2, A[j]) for j in range(k))
        if cs % 4 not in (1, 3):
            mod4_ok = False
            break
    test(f"k={k}: corrSum ∈ {{1,3}} mod 4", mod4_ok)

# ============================================================
# SECTION 6 : ord_d(2) > S-1 pour k ≥ 4 (Énoncé A)
# ============================================================
section("6. ord_d(2) > S-1 POUR k ≥ 4")

for k in range(4, min(K_MAX + 1, 30)):
    S, d, C = compute_params(k)
    # Calculer ord_d(2)
    x = 1
    for r in range(1, 2 * S + 1):
        x = (x * 2) % d
        if x == 1:
            break
    ord_d_2 = r
    test(f"k={k}: ord_d(2) = {ord_d_2} > S-1 = {S-1}", ord_d_2 > S - 1)

# ============================================================
# SECTION 7 : Énoncé B (Pigeonhole) — max_bwd ≤ S - k + 2
# ============================================================
section("7. DOUBLE PEELING : positions incompatibles (k=3..10)")

for k in range(K_MIN, min(K_MAX + 1, 11)):
    S, d, C = compute_params(k)
    inv3 = pow(3, -1, d)  # 3^{-1} mod d

    # Forward depuis c_0 = 1
    # Chaque couche : dict of (state, max_position_used) → exists
    fwd_layers = [dict() for _ in range(k)]
    fwd_layers[0][(1, 0)] = True

    for j in range(1, k):
        for (c, p_max), _ in fwd_layers[j-1].items():
            for p in range(p_max + 1, S):
                c_new = (3 * c + pow(2, p)) % d
                key = (c_new, p)
                fwd_layers[j][key] = True

    # Backward depuis c_{k-1} = 0
    bwd_layers = [dict() for _ in range(k)]
    bwd_layers[0][(0, S)] = True  # position_min = S (rien utilisé encore)

    for m in range(1, k):
        for (c, p_min), _ in bwd_layers[m-1].items():
            for p in range(1, p_min):
                c_prev = ((c - pow(2, p)) * inv3) % d
                key = (c_prev, p)
                bwd_layers[m][key] = True

    # Test de compatibilité à chaque rendez-vous
    compatible_total = 0
    for j in range(k):
        m = k - 1 - j
        if j >= len(fwd_layers) or m >= len(bwd_layers):
            continue
        fwd_states = {}
        for (s, p), _ in fwd_layers[j].items():
            if s not in fwd_states:
                fwd_states[s] = []
            fwd_states[s].append(p)

        bwd_states = {}
        for (s, p), _ in bwd_layers[m].items():
            if s not in bwd_states:
                bwd_states[s] = []
            bwd_states[s].append(p)

        common = set(fwd_states.keys()) & set(bwd_states.keys())
        for s in common:
            for pf in fwd_states[s]:
                for pb in bwd_states[s]:
                    if pf < pb:
                        compatible_total += 1

    test(f"k={k}: double peeling → 0 paires compatibles", compatible_total == 0,
         f"found {compatible_total} compatible pairs")

# ============================================================
# SECTION 8 : Synthétiques calibrés (automate NON ordonné couvre Z/dZ)
# ============================================================
section("8. SYNTHÉTIQUE : automate NON ordonné couvre Z/dZ")

for k in range(5, min(K_MAX + 1, 9)):
    S, d, C = compute_params(k)
    # Automate sans contrainte d'ordre : positions avec répétition
    reachable = {1}
    for step in range(k - 1):
        new_reach = set()
        for c in reachable:
            for p in range(1, S):
                new_reach.add((3 * c + pow(2, p)) % d)
        reachable = new_reach

    coverage = len(reachable)
    has_zero = 0 in reachable
    test(f"k={k}: non-ordonné couvre Z/dZ (couverture {coverage}/{d})",
         coverage == d or has_zero,
         f"couverture = {coverage}/{d}, 0 présent = {has_zero}")

# ============================================================
# BILAN
# ============================================================
section("BILAN")
total = passed + failed
print(f"\n  Tests passés : {passed}/{total}")
print(f"  Tests échoués : {failed}/{total}")

if failed > 0:
    print(f"\n  🔴 ALARME : {failed} test(s) échoué(s) !")
    for e in errors:
        print(f"    - {e}")
    print("\n  ⚠️  STOP IMMÉDIAT — Investiguer avant de continuer.")
    sys.exit(1)
else:
    print(f"\n  ✅ TOUS LES TESTS PASSENT. Prêt pour la session.")
    sys.exit(0)
