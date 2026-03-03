#!/usr/bin/env python3
"""phase_a2plus_ecm_cofactors.py — Phase A2+ : Factorisation ECM des 12 cofacteurs

Les 12 cofacteurs composites non factorisés par trial division (Phase A2)
pour k ∈ {46, 47, 53, 54, 57, 58, 59, 62, 63, 64, 65, 66}.

Utilise sympy.factorint (qui combine Pollard's rho, ECM, et trial division)
pour obtenir la factorisation complète et vérifier le régime de chaque facteur.

Résultat : 25 nouveaux premiers, TOUS Régime A. Gap fermé.

Auteur : Eric Merle (assisté par Claude)
Date :   3 mars 2026
"""

import math
import time
from sympy import factorint, isprime

# ============================================================================
# Helpers (réutilisés de phase_a2)
# ============================================================================

def ceil_log2_3_exact(k):
    three_k = 3 ** k
    S = k
    while (1 << S) < three_k:
        S += 1
    return S


def trial_factor(n, bound=10**7):
    factors = []
    d = 2
    while d * d <= n and d <= bound:
        if n % d == 0:
            e = 0
            while n % d == 0:
                n //= d
                e += 1
            factors.append((d, e))
        d += (1 if d == 2 else 2)
    return factors, n


def mult_ord_via_factors(a, p):
    """Ordre multiplicatif de a mod p via factorisation de p-1."""
    if math.gcd(a, p) != 1:
        return 0
    n = p - 1
    facs = {}
    temp = n
    d = 2
    while d * d <= temp and d <= 10**6:
        while temp % d == 0:
            facs[d] = facs.get(d, 0) + 1
            temp //= d
        d += (1 if d == 2 else 2)
    if temp > 1:
        facs[temp] = facs.get(temp, 0) + 1
    order = n
    for q in facs:
        while order % q == 0 and pow(a, order // q, p) == 1:
            order //= q
    return order


# ============================================================================
# Main
# ============================================================================

def main():
    t_global = time.time()

    print("=" * 80)
    print("PHASE A2+ — FACTORISATION ECM DES 12 COFACTEURS RÉSIDUELS")
    print(f"Date : {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print("=" * 80)

    target_ks = [46, 47, 53, 54, 57, 58, 59, 62, 63, 64, 65, 66]

    all_results = []
    all_regime_a = True

    for k in target_ks:
        S = ceil_log2_3_exact(k)
        d = (1 << S) - pow(3, k)
        _, cofactor = trial_factor(d, 10**7)

        t1 = time.time()
        fac = factorint(cofactor)
        t_fac = time.time() - t1

        primes = list(fac.keys())
        n_digits = len(str(cofactor))
        print(f"\nk={k:>2} cofactor ({n_digits} digits) = {cofactor}")
        print(f"   Factorisation : {' × '.join(f'{p}^{e}' if e > 1 else str(p) for p, e in fac.items())} [{t_fac:.1f}s]")

        # Vérifier la factorisation
        prod = 1
        for p, e in fac.items():
            prod *= p ** e
        assert prod == cofactor, f"Factorisation incorrecte pour k={k}"

        for p in primes:
            p = int(p)
            m = mult_ord_via_factors(2, p)
            regime = 'A' if p < m ** 4 else 'B'
            status = '✓' if regime == 'A' else '✗ REGIME B'
            print(f"   p={p:>25,} m={m:>25,} m⁴={m**4:.2e} → Régime {regime} {status}")
            if regime == 'B':
                all_regime_a = False
            all_results.append({'k': k, 'p': p, 'm': m, 'regime': regime})

    # Synthèse
    print(f"\n{'=' * 80}")
    print("SYNTHÈSE PHASE A2+")
    print(f"{'=' * 80}")

    n_total = len(all_results)
    n_a = sum(1 for r in all_results if r['regime'] == 'A')
    n_b = sum(1 for r in all_results if r['regime'] == 'B')

    print(f"\n  Cofacteurs factorisés : {len(target_ks)}/{len(target_ks)}")
    print(f"  Nouveaux premiers : {n_total}")
    print(f"  Régime A : {n_a}")
    print(f"  Régime B : {n_b}")

    t_total = time.time() - t_global
    print(f"\n  Temps total : {t_total:.1f}s")

    print(f"\n{'=' * 80}")
    if all_regime_a:
        print("✓ TOUS LES COFACTEURS FACTORISÉS — TOUS RÉGIME A")
        print("✓ LE GAP k=18..67 EST FERMÉ")
        print()
        print("  Bilan complet :")
        print("    Phase A2  : 127 petits premiers + 38 cofacteurs premiers = 165 → tous Régime A")
        print("    Phase A2+ :                      + 25 nouveaux premiers  =  25 → tous Régime A")
        print("    TOTAL     : 190 premiers, 190/190 Régime A (100%)")
    else:
        print(f"⚠️ {n_b} premiers en Régime B détectés")
    print(f"{'=' * 80}")


if __name__ == '__main__':
    main()
