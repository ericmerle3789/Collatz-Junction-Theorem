#!/usr/bin/env python3
"""
R172 — CARTOGRAPHIE ARITHMÉTIQUE UNIVERSELLE
=============================================

Pour chaque k de 3 à 100 et S = S_min :
1. Factoriser d(k) = 2^S - 3^k
2. Pour chaque facteur premier p :
   - ord_p(2) = r
   - ord_p(3)
   - gcd(r, k) → n_eff (via T162)
   - 3 ∈ ⟨2⟩ mod p ? (T163 dichotomie)
   - N₀(p) par DP (si C(k,r) raisonnable)
   - N_H(0) = main term (si gcd(r,k)=1 → R=0 par T159)
3. Identifier les k "faciles" (∃ p | d avec N₀(p) = 0)
   et les k "durs" (∀ p | d, N₀(p) > 0)

Objectif : trouver un PATRON universel qui couvre tous les k.
"""

import math
from collections import defaultdict
from sympy import factorint, isprime, primitive_root, n_order
import json
import time


def compute_S_min(k):
    """Plus petit S tel que 2^S > 3^k."""
    S = math.ceil(k * math.log2(3))
    if 2**S <= 3**k:
        S += 1
    return S


def ord_mod(base, p):
    """Ordre multiplicatif de base mod p."""
    if base % p == 0:
        return 0
    return n_order(base, p)


def is_in_subgroup(element, generator, order, p):
    """Vérifie si element ∈ ⟨generator⟩ mod p."""
    # element ∈ ⟨generator⟩ iff element^((p-1)/order) ≡ 1 mod p
    if element % p == 0:
        return False
    exp = (p - 1) // order
    return pow(element % p, exp, p) == 1


def count_N0_dp(k, p, max_C=500000):
    """
    Compte N₀(p) = #{compositions monotones B avec corrSum ≡ 0 mod p}.
    DP sur le simplexe monotone.
    Retourne (N0, C_total) ou None si trop gros.
    """
    r = ord_mod(2, p)
    if r == 0:
        return None

    # Réduction mod p : 2^b mod p a période r
    # Donc on travaille dans Z/rZ pour les exposants
    top = compute_S_min(k) - k  # = S - k

    # Pour k grand, C = C(top+k-1, k-1) peut être énorme
    # Estimer C
    from math import comb
    C = comb(top + k - 1, k - 1)
    if C > max_C:
        return None  # Trop gros pour DP

    # DP : dp[j][s] = nombre de compositions B_0 ≤ ... ≤ B_{j-1} avec
    #   Σ_{i=0}^{j-1} 3^{k-1-i} * 2^{B_i} ≡ s mod p
    #   et B_{j-1} ≤ top (= B_{k-1} = top à la fin)
    # B_j ∈ [prev_B, top]

    # Version simplifiée pour petits k
    g = pow(3, p - 2, p)  # 3^{-1} mod p = g

    # Coefficients : alpha_j = 3^{k-1-j} mod p
    alphas = [pow(3, k - 1 - j, p) for j in range(k)]

    # DP forward
    # dp[b_prev][sum_mod_p] = count
    # b_prev = dernière valeur de B choisie (0 à top)
    # On itère j = 0, 1, ..., k-1

    if top > 500 or k > 30:
        return None  # Trop gros

    # État initial : vide
    dp = defaultdict(int)
    dp[(0, 0)] = 1  # (b_min_allowed, partial_sum)

    for j in range(k):
        new_dp = defaultdict(int)
        alpha_j = alphas[j]

        for (b_min, s), cnt in dp.items():
            b_max = top if j < k - 1 else top  # B_{k-1} must be exactly top
            if j == k - 1:
                # Last: B_{k-1} = top
                b = top
                if b >= b_min:
                    val = (alpha_j * pow(2, b, p)) % p
                    new_s = (s + val) % p
                    new_dp[(b, new_s)] += cnt
            else:
                for b in range(b_min, top + 1):
                    val = (alpha_j * pow(2, b, p)) % p
                    new_s = (s + val) % p
                    new_dp[(b, new_s)] += cnt

        dp = new_dp

    # Compter N₀ et C
    N0 = 0
    C_total = 0
    for (b_last, s), cnt in dp.items():
        C_total += cnt
        if s == 0:
            N0 += cnt

    return N0, C_total


def analyze_k(k, verbose=False):
    """Analyse complète d'un k donné."""
    S = compute_S_min(k)
    d = 2**S - 3**k

    result = {
        'k': k,
        'S_min': S,
        'd': d,
        'log2_d': math.log2(d) if d > 0 else 0,
        'primes': [],
        'has_blocking_prime': False,
        'best_prime': None,
    }

    # Factoriser d
    factors = factorint(d)

    for p, mult in sorted(factors.items()):
        if p <= 3:
            continue  # Skip 2 and 3 (can't appear in d since d is odd and coprime to 3)

        r = ord_mod(2, p)
        r3 = ord_mod(3, p)
        gcd_rk = math.gcd(r, k)
        n_eff = gcd_rk - 1
        three_in_H = is_in_subgroup(3, 2, r, p)

        prime_info = {
            'p': p,
            'mult': mult,
            'ord_2': r,
            'ord_3': r3,
            'gcd_r_k': gcd_rk,
            'n_eff': n_eff,
            '3_in_H': three_in_H,
            'N0': None,
            'C': None,
            'N0_is_zero': None,
        }

        # Tenter le calcul DP de N₀(p)
        dp_result = count_N0_dp(k, p)
        if dp_result is not None:
            N0, C = dp_result
            prime_info['N0'] = N0
            prime_info['C'] = C
            prime_info['N0_is_zero'] = (N0 == 0)
            prime_info['ratio'] = N0 * p / C if C > 0 else None

            if N0 == 0:
                result['has_blocking_prime'] = True
                if result['best_prime'] is None:
                    result['best_prime'] = p

        result['primes'].append(prime_info)

    return result


def main():
    print("=" * 72)
    print("R172 — CARTOGRAPHIE ARITHMÉTIQUE UNIVERSELLE")
    print("=" * 72)

    t0 = time.time()
    all_results = []
    blocking_ks = []
    non_blocking_ks = []
    unknown_ks = []

    for k in range(3, 69):  # k = 3 to 68
        try:
            result = analyze_k(k)
            all_results.append(result)

            # Classifier
            if result['has_blocking_prime']:
                blocking_ks.append(k)
                status = "✅ BLOCKING PRIME"
            else:
                # Vérifier si on a pu tester tous les primes
                all_tested = all(p['N0'] is not None for p in result['primes'])
                if all_tested and result['primes']:
                    non_blocking_ks.append(k)
                    status = "❌ NO BLOCKING PRIME"
                else:
                    unknown_ks.append(k)
                    status = "❓ UNKNOWN (DP too large)"

            # Résumé
            primes_str = ", ".join(
                f"{p['p']}(r={p['ord_2']},gcd={p['gcd_r_k']},N₀={'?' if p['N0'] is None else p['N0']})"
                for p in result['primes'][:5]
            )
            extra = f"  +{len(result['primes'])-5} more" if len(result['primes']) > 5 else ""
            print(f"  k={k:3d}: S={result['S_min']:3d}, d≈2^{result['log2_d']:.1f}, "
                  f"{status}  [{primes_str}{extra}]")

        except Exception as e:
            print(f"  k={k:3d}: ERROR — {e}")
            unknown_ks.append(k)

    elapsed = time.time() - t0

    # Résumé
    print(f"\n{'='*72}")
    print(f"RÉSUMÉ (t={elapsed:.1f}s)")
    print(f"{'='*72}")
    print(f"  ✅ Blocking prime trouvé : {len(blocking_ks)} k-values")
    print(f"     k = {blocking_ks[:20]}{'...' if len(blocking_ks) > 20 else ''}")
    print(f"  ❌ Pas de blocking prime : {len(non_blocking_ks)} k-values")
    print(f"     k = {non_blocking_ks[:20]}{'...' if len(non_blocking_ks) > 20 else ''}")
    print(f"  ❓ Inconnu (DP trop gros) : {len(unknown_ks)} k-values")
    print(f"     k = {unknown_ks[:20]}{'...' if len(unknown_ks) > 20 else ''}")

    # Pattern analysis
    print(f"\n--- ANALYSE DES PATTERNS ---")

    # Pour chaque k avec blocking prime, quel type de prime bloque ?
    print(f"\nk avec gcd(r,k)=1 et R=0 (T159 actif) :")
    for r in all_results:
        if r['has_blocking_prime']:
            for p in r['primes']:
                if p['N0'] == 0:
                    t159 = "T159" if p['gcd_r_k'] == 1 else "other"
                    print(f"  k={r['k']}: p={p['p']}, r={p['ord_2']}, "
                          f"gcd(r,k)={p['gcd_r_k']}, N₀=0 [{t159}]")
                    break

    # Sauvegarder
    # Simplifier pour JSON (les gros entiers posent problème)
    simple_results = []
    for r in all_results:
        sr = {
            'k': r['k'], 'S_min': r['S_min'],
            'log2_d': round(r['log2_d'], 2),
            'has_blocking_prime': r['has_blocking_prime'],
            'best_prime': r['best_prime'],
            'n_primes': len(r['primes']),
            'primes_summary': [
                {
                    'p': p['p'], 'ord_2': p['ord_2'],
                    'gcd_r_k': p['gcd_r_k'], 'n_eff': p['n_eff'],
                    '3_in_H': p['3_in_H'],
                    'N0': p['N0'], 'C': p['C'],
                    'N0_zero': p['N0_is_zero'],
                }
                for p in r['primes'][:10]
            ]
        }
        simple_results.append(sr)

    with open('R172_arithmetic_landscape.json', 'w') as f:
        json.dump(simple_results, f, indent=2, default=str)
    print(f"\nRésultats sauvegardés dans R172_arithmetic_landscape.json")


if __name__ == '__main__':
    main()
