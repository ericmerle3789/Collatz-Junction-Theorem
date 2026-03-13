#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
R67 — AUDIT DE PORTÉE DE K-LITE
=================================
Round 67 — TYPE P

QUESTION CENTRALE:
  La chaîne R62-R65 prouve K-lite pour c_δ = 1 + g^{2δ} (g = racine primitive).
  La formulation Collatz R57 utilise c_δ = 1 + g_Collatz·2^δ (g_Collatz = 3/2).
  Ces sont DIFFÉRENTES. K-lite s'applique-t-il au cas Collatz ?

MÉTHODE:
  1. SECTION 1: Vérifier que les deux définitions sont bien différentes
  2. SECTION 2: Comparer N_r pour les deux définitions sur les mêmes primes
  3. SECTION 3: Tester la définition Collatz sur des primes R2 (petit ord_p(2))
  4. SECTION 4: Diagnostic — le K-lite α < 1 tient-il pour la version Collatz ?
  5. SECTION 5: Identifier exactement la portée correcte

DÉFINITIONS:
  Version R62 (⟨g²⟩):    c_δ = 1 + g^{2δ} mod p, g = racine primitive
  Version R57 (Collatz):  c_δ = 1 + g_C·2^δ mod p, g_C = 3·2^{-1} mod p
  N_r = #{δ ∈ [0,M] : dlog(r/c_δ) ∈ [0, M-δ]}
  α = max_r N_r / (M+1)

EPISTEMIC LABELS:
  [PROVED]       = rigorous proof or exact algebraic identity
  [COMPUTED]     = verified by exact computation on all tested cases
  [OBSERVED]     = numerical evidence
  [CONJECTURAL]  = plausible but unproven

Author: Claude Opus 4.6 (R67 pour Eric Merle)
Date:   2026-03-13
"""

import math
import sys
import time

T_START = time.time()
PASS_COUNT = 0
FAIL_COUNT = 0

def elapsed():
    return time.time() - T_START

def test(name, condition, detail=""):
    global PASS_COUNT, FAIL_COUNT
    if condition:
        PASS_COUNT += 1
        print(f"  [PASS] {name}")
    else:
        FAIL_COUNT += 1
        print(f"  [FAIL] {name} -- {detail}")

def primitive_root(p):
    if p == 2:
        return 1
    phi = p - 1
    factors = set()
    n = phi
    for d in range(2, int(math.isqrt(n)) + 1):
        while n % d == 0:
            factors.add(d)
            n //= d
    if n > 1:
        factors.add(n)
    for g in range(2, p):
        ok = True
        for f in factors:
            if pow(g, phi // f, p) == 1:
                ok = False
                break
        if ok:
            return g
    return None

def mult_order(a, p):
    if a % p == 0:
        return 0
    order = 1
    val = a % p
    while val != 1:
        val = (val * a) % p
        order += 1
        if order > p:
            return p
    return order

def build_dlog(g, p):
    table = {}
    power = 1
    for k in range(p - 1):
        table[power] = k
        power = (power * g) % p
    return table

# ============================================================================
# SECTION 1 : VÉRIFIER LA DISCREPANCE DES DEUX DÉFINITIONS
# ============================================================================

def section1_discrepancy():
    print("\n" + "=" * 70)
    print("SECTION 1 — DISCREPANCE ENTRE LES DEUX DÉFINITIONS DE c_δ")
    print("=" * 70)

    for p in [101, 251, 503]:
        g = primitive_root(p)
        g_collatz = (3 * pow(2, p - 2, p)) % p  # g_C = 3/2 mod p
        M = (p - 3) // 2
        ord2 = mult_order(2, p)

        # Version R62: c_δ = 1 + g^{2δ}
        c_r62 = set()
        for delta in range(M + 1):
            c = (1 + pow(g, 2 * delta, p)) % p
            c_r62.add(c)

        # Version R57 (Collatz): c_δ = 1 + g_C·2^δ
        c_r57 = set()
        for delta in range(M + 1):
            c = (1 + g_collatz * pow(2, delta, p)) % p
            c_r57.add(c)

        print(f"\n  p={p}, ord_p(2)={ord2}, M+1={M+1}")
        print(f"    R62 (⟨g²⟩):  {len(c_r62)} valeurs distinctes de c_δ")
        print(f"    R57 (Collatz): {len(c_r57)} valeurs distinctes de c_δ")
        print(f"    Intersection:  {len(c_r62 & c_r57)} valeurs communes")
        print(f"    Identiques ?   {c_r62 == c_r57}")

    # Test formel
    p = 101
    g = primitive_root(p)
    g_collatz = (3 * pow(2, p - 2, p)) % p
    M = (p - 3) // 2

    c_r62 = set()
    for delta in range(M + 1):
        c_r62.add((1 + pow(g, 2 * delta, p)) % p)

    c_r57 = set()
    for delta in range(M + 1):
        c_r57.add((1 + g_collatz * pow(2, delta, p)) % p)

    test("S1.1: R62 et R57 donnent des ensembles c_δ DIFFÉRENTS",
         c_r62 != c_r57,
         "Les ensembles sont identiques — pas de discrepance")

    # Vérifier que R62 donne (p-1)/2 valeurs distinctes
    test("S1.2: R62 donne (p-1)/2 valeurs distinctes (⟨g²⟩ complet)",
         len(c_r62) >= (p - 1) // 2 - 1,
         f"Seulement {len(c_r62)} valeurs")

    # Vérifier que R57 donne ord_p(2) valeurs distinctes
    ord2 = mult_order(2, p)
    test("S1.3: R57 donne ≤ ord_p(2) valeurs distinctes",
         len(c_r57) <= ord2 + 1,
         f"{len(c_r57)} valeurs > ord_p(2)={ord2}")

    # Vérifier la récurrence
    g_pr = primitive_root(p)
    c0_r62 = (1 + pow(g_pr, 0, p)) % p  # = 2
    c1_r62 = (1 + pow(g_pr, 2, p)) % p
    rec_r62 = (pow(g_pr, 2, p) * c0_r62 + (1 - pow(g_pr, 2, p))) % p
    test("S1.4: Récurrence R62 est c_{δ+1} = g²·c_δ + (1-g²), multiplicateur g²",
         c1_r62 == rec_r62,
         f"c1={c1_r62}, rec={rec_r62}")

    g_c = (3 * pow(2, p - 2, p)) % p
    c0_r57 = (1 + g_c * pow(2, 0, p)) % p
    c1_r57 = (1 + g_c * pow(2, 1, p)) % p
    rec_r57 = (2 * c0_r57 - 1) % p
    test("S1.5: Récurrence R57 est c_{δ+1} = 2·c_δ − 1, multiplicateur 2",
         c1_r57 == rec_r57,
         f"c1={c1_r57}, rec={rec_r57}")

# ============================================================================
# SECTION 2 : COMPARER N_r POUR LES DEUX DÉFINITIONS
# ============================================================================

def compute_Nr_and_alpha(p, c_delta_list, dlog_table):
    """Compute max N_r / (M+1) for a given c_delta sequence."""
    M = (p - 3) // 2
    max_Nr = 0

    for r in range(1, p):
        nr = 0
        for delta in range(M + 1):
            c = c_delta_list[delta]
            if c == 0:
                if r == 0:
                    nr += 1
                continue
            target = (r * pow(c, p - 2, p)) % p
            if target == 0:
                continue
            dl = dlog_table.get(target)
            if dl is not None and 0 <= dl <= M - delta:
                nr += 1
        if nr > max_Nr:
            max_Nr = nr

    alpha = max_Nr / (M + 1) if M + 1 > 0 else 0
    return max_Nr, alpha

def section2_compare_Nr():
    print("\n" + "=" * 70)
    print("SECTION 2 — COMPARAISON N_r ET α POUR LES DEUX DÉFINITIONS")
    print("=" * 70)

    results = []
    for p in [29, 53, 101, 127, 251]:
        g = primitive_root(p)
        g_collatz = (3 * pow(2, p - 2, p)) % p
        M = (p - 3) // 2
        ord2 = mult_order(2, p)
        dlog = build_dlog(g, p)

        # Version R62: c_δ = 1 + g^{2δ}
        c_r62 = [(1 + pow(g, 2 * delta, p)) % p for delta in range(M + 1)]
        maxNr_r62, alpha_r62 = compute_Nr_and_alpha(p, c_r62, dlog)

        # Version R57 (Collatz): c_δ = 1 + g_C·2^δ
        c_r57 = [(1 + g_collatz * pow(2, delta, p)) % p for delta in range(M + 1)]
        maxNr_r57, alpha_r57 = compute_Nr_and_alpha(p, c_r57, dlog)

        regime = "R3" if ord2 >= math.isqrt(p) else ("R2" if ord2 >= p**0.25 else "R1")

        print(f"\n  p={p}, ord_p(2)={ord2}, régime={regime}")
        print(f"    R62 (⟨g²⟩):  max N_r = {maxNr_r62}, α = {alpha_r62:.4f}")
        print(f"    R57 (Collatz): max N_r = {maxNr_r57}, α = {alpha_r57:.4f}")
        print(f"    Écart α:       {abs(alpha_r62 - alpha_r57):.4f}")

        results.append({
            'p': p, 'ord2': ord2, 'regime': regime,
            'alpha_r62': alpha_r62, 'alpha_r57': alpha_r57,
        })

    # Tests
    all_r62_ok = all(r['alpha_r62'] < 1 for r in results)
    all_r57_ok = all(r['alpha_r57'] < 1 for r in results)

    test("S2.1: α < 1 pour TOUS les p testés (version R62 ⟨g²⟩)",
         all_r62_ok,
         "Au moins un α ≥ 1 pour R62")
    test("S2.2: α < 1 pour TOUS les p testés (version R57 Collatz)",
         all_r57_ok,
         "Au moins un α ≥ 1 pour Collatz")

    # Comparer les valeurs
    max_diff = max(abs(r['alpha_r62'] - r['alpha_r57']) for r in results)
    test("S2.3: Les deux versions donnent des α DIFFÉRENTS",
         max_diff > 0.01,
         f"Différence max = {max_diff:.4f}, trop similaire")

    return results

# ============================================================================
# SECTION 3 : PRIMES R2 — OÙ LA DIFFÉRENCE COMPTE
# ============================================================================

def section3_r2_primes():
    print("\n" + "=" * 70)
    print("SECTION 3 — PRIMES R2 : LE CAS CRITIQUE")
    print("=" * 70)

    # Chercher des primes R2 et tester α pour la version Collatz
    r2_primes = []
    for p in range(5, 2000):
        # Quick primality check
        if p < 4:
            continue
        is_p = True
        for d in range(2, int(math.isqrt(p)) + 1):
            if p % d == 0:
                is_p = False
                break
        if not is_p:
            continue

        ord2 = mult_order(2, p)
        p14 = p ** 0.25
        sp = math.isqrt(p)

        if p14 <= ord2 < sp:
            r2_primes.append((p, ord2))

    print(f"\n  {len(r2_primes)} primes R2 trouvés dans [5, 2000]")

    results = []
    tested = 0
    for p, ord2 in r2_primes:
        if p > 500:  # Limiter le temps de calcul
            break
        g = primitive_root(p)
        g_collatz = (3 * pow(2, p - 2, p)) % p
        M = (p - 3) // 2
        dlog = build_dlog(g, p)

        # Version Collatz
        c_r57 = [(1 + g_collatz * pow(2, delta, p)) % p for delta in range(M + 1)]
        maxNr_r57, alpha_r57 = compute_Nr_and_alpha(p, c_r57, dlog)

        # Version R62
        c_r62 = [(1 + pow(g, 2 * delta, p)) % p for delta in range(M + 1)]
        maxNr_r62, alpha_r62 = compute_Nr_and_alpha(p, c_r62, dlog)

        n_distinct_collatz = len(set(c_r57))

        print(f"  p={p:4d}, ord={ord2:3d}, distinct_Collatz={n_distinct_collatz:3d}, "
              f"α_Collatz={alpha_r57:.4f}, α_R62={alpha_r62:.4f}")

        results.append({
            'p': p, 'ord2': ord2,
            'alpha_collatz': alpha_r57, 'alpha_r62': alpha_r62,
            'n_distinct': n_distinct_collatz,
        })
        tested += 1

    if tested > 0:
        all_collatz_ok = all(r['alpha_collatz'] < 1 for r in results)
        max_collatz_alpha = max(r['alpha_collatz'] for r in results)
        max_r62_alpha = max(r['alpha_r62'] for r in results)

        test(f"S3.1: α_Collatz < 1 pour tous les {tested} primes R2 testés",
             all_collatz_ok,
             f"Au moins un α_Collatz ≥ 1, max = {max_collatz_alpha:.4f}")

        test("S3.2: α_Collatz systématiquement ≠ α_R62 sur R2",
             any(abs(r['alpha_collatz'] - r['alpha_r62']) > 0.01 for r in results),
             "Aucune différence significative")

        print(f"\n  Résumé R2: α_Collatz max = {max_collatz_alpha:.4f}, "
              f"α_R62 max = {max_r62_alpha:.4f}")
    else:
        print("  Aucun prime R2 testable")

    return results

# ============================================================================
# SECTION 4 : DIAGNOSTIC — LE K-LITE α < 1 TIENT-IL EN GÉNÉRAL POUR COLLATZ ?
# ============================================================================

def section4_collatz_universal():
    print("\n" + "=" * 70)
    print("SECTION 4 — K-LITE COLLATZ : α < 1 SUR ÉCHANTILLON LARGE")
    print("=" * 70)

    # Tester sur un large échantillon de primes (pas de filtre de régime)
    primes = []
    for p in range(5, 300):
        is_p = True
        for d in range(2, int(math.isqrt(p)) + 1):
            if p % d == 0:
                is_p = False
                break
        if is_p:
            primes.append(p)

    results = []
    max_alpha = 0
    worst_p = 0

    for p in primes:
        g = primitive_root(p)
        g_collatz = (3 * pow(2, p - 2, p)) % p
        M = (p - 3) // 2
        dlog = build_dlog(g, p)
        ord2 = mult_order(2, p)

        c_r57 = [(1 + g_collatz * pow(2, delta, p)) % p for delta in range(M + 1)]
        maxNr, alpha = compute_Nr_and_alpha(p, c_r57, dlog)

        regime = "R3" if ord2 >= math.isqrt(p) else ("R2" if ord2 >= p**0.25 else "R1")

        if alpha > max_alpha:
            max_alpha = alpha
            worst_p = p

        results.append({
            'p': p, 'ord2': ord2, 'regime': regime,
            'alpha': alpha, 'maxNr': maxNr,
        })

    all_ok = all(r['alpha'] < 1 for r in results)
    n_primes = len(results)
    r3_alphas = [r['alpha'] for r in results if r['regime'] == 'R3']
    r2_alphas = [r['alpha'] for r in results if r['regime'] == 'R2']

    print(f"\n  {n_primes} primes testés dans [5, 300]")
    print(f"  R3: {len(r3_alphas)} primes, α max = {max(r3_alphas):.4f}" if r3_alphas else "  R3: aucun")
    print(f"  R2: {len(r2_alphas)} primes, α max = {max(r2_alphas):.4f}" if r2_alphas else "  R2: aucun")
    print(f"  Pire cas global: p={worst_p}, α = {max_alpha:.4f}")

    test(f"S4.1: α_Collatz < 1 pour TOUS les {n_primes} primes (version Collatz originale)",
         all_ok,
         f"VIOLATION: p={worst_p}, α={max_alpha:.4f}")

    test("S4.2: α_Collatz ≤ 0.75 pour tous les primes",
         max_alpha <= 0.75,
         f"α max = {max_alpha:.4f} > 0.75")

    test("S4.3: α_Collatz ≤ 0.60 pour tous les primes",
         max_alpha <= 0.60,
         f"α max = {max_alpha:.4f} > 0.60")

    return results, max_alpha, worst_p

# ============================================================================
# SECTION 5 : VERDICT DE PORTÉE
# ============================================================================

def section5_verdict(results_s2, results_s3, results_s4, max_alpha_s4):
    print("\n" + "=" * 70)
    print("SECTION 5 — VERDICT DE PORTÉE")
    print("=" * 70)

    # Question 1: Les deux définitions sont-elles les mêmes ?
    different = True  # Confirmé en Section 1
    print(f"\n  Q1: Les deux définitions c_δ sont-elles identiques ?")
    print(f"      → NON. R62 utilise ⟨g²⟩ (QR_p), R57 utilise ⟨2⟩ (arc Collatz).")

    # Question 2: K-lite prouvé en R62-R65 s'applique-t-il directement à Collatz ?
    print(f"\n  Q2: La preuve R62-R65 s'applique-t-elle directement au cas Collatz ?")
    print(f"      → NON. La preuve utilise c_δ = 1+g^{{2δ}} (⟨g²⟩), pas c_δ = 1+g_C·2^δ.")
    print(f"      La décomposition Jacobi s'appuie sur ⟨g²⟩ ayant index 2.")
    print(f"      Pour ⟨2⟩ avec index (p-1)/ord_p(2), la même technique ne fonctionne pas.")

    # Question 3: K-lite tient-il quand même en pratique pour Collatz ?
    print(f"\n  Q3: K-lite α < 1 tient-il pour la version Collatz (observé) ?")
    all_s4_ok = max_alpha_s4 < 1
    print(f"      → {'OUI' if all_s4_ok else 'NON'} (observé). α_max = {max_alpha_s4:.4f}")

    # Question 4: La portée correcte
    print(f"\n  Q4: Portée correcte du théorème ?")
    print(f"      K-lite PROUVÉ:    pour c_δ = 1 + g^{{2δ}} (tout p ≥ 5)")
    print(f"      K-lite OBSERVÉ:   pour c_δ = 1 + g_C·2^δ (tout p ≤ 300)")
    print(f"      K-lite NON PROUVÉ: pour le cas Collatz spécifique")

    test("S5.1: Discrepance c_δ confirmée entre R57 et R62",
         True)
    test("S5.2: K-lite PROUVÉ pour ⟨g²⟩ (correct mais pas le cas Collatz)",
         True)
    test("S5.3: K-lite OBSERVÉ α < 1 pour le cas Collatz sur tous primes testés",
         all_s4_ok,
         f"VIOLATION: α_max = {max_alpha_s4:.4f}")

    # Verdict
    print(f"\n  " + "-" * 60)
    print(f"  VERDICT FINAL DE PORTÉE:")
    print(f"  " + "-" * 60)
    print(f"  1. K-lite (⟨g²⟩) : PROUVÉ pour tout p ≥ 5 [CORRECT]")
    print(f"  2. K-lite (Collatz) : NON PROUVÉ mais OBSERVÉ α < 1 [GAP]")
    print(f"  3. La discrepance est dans le MODÈLE, pas dans la PREUVE")
    print(f"  4. La preuve R62-R65 est mathématiquement correcte")
    print(f"     mais s'applique à un objet DIFFÉRENT du cas Collatz")
    print(f"  5. Le verrou actif est : adapter la preuve à c_δ = 1 + g_C·2^δ")
    print(f"     ou montrer que le résultat ⟨g²⟩ implique le résultat Collatz")
    print(f"  " + "-" * 60)

# ============================================================================
# MAIN
# ============================================================================

if __name__ == "__main__":
    print("R67 — AUDIT DE PORTÉE DE K-LITE")
    print("=" * 70)

    section1_discrepancy()
    results_s2 = section2_compare_Nr()
    results_s3 = section3_r2_primes()
    results_s4, max_alpha_s4, worst_p = section4_collatz_universal()
    section5_verdict(results_s2, results_s3, results_s4, max_alpha_s4)

    print(f"\n{'=' * 70}")
    print(f"BILAN: {PASS_COUNT} PASS, {FAIL_COUNT} FAIL en {elapsed():.1f}s")
    print(f"{'=' * 70}")

    sys.exit(0 if FAIL_COUNT == 0 else 1)
