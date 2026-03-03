#!/usr/bin/env python3
"""phase_b3_PU_verify.py — Phase B3 : Vérification numérique de PU

Proportion Uniformity (PU) : Pour A = {a₀,...,a_{k-1}} ⊂ {0,...,S-1},
soit π(A,r) = #{σ ∈ S_k : Φ_σ(A) ≡ r mod p} où
  Φ_σ(A) = Σ_{j=0}^{k-1} 3^j · 2^{a_{σ(j)}}

PU affirme que π(A,0)/k! ≈ 1/p uniformément en A "typique".

Protocole :
1. Pour k = 5..8 et p premier diviseur de d(k) :
   - Échantillonner N_sample sous-ensembles A aléatoires
   - Pour chaque A, calculer π(A,r) pour tout r ∈ F_p
   - Mesurer la distribution de π(A,0)/k! vs 1/p
   - Test χ² de la distribution de Φ_σ sur F_p

2. Aussi tester sur les compositions strictement croissantes
   (les "vraies" compositions de la preuve Collatz)

Auteur : Eric Merle (assisté par Claude)
Date :   3 mars 2026
"""

import math
import time
import numpy as np
from itertools import permutations, combinations
from collections import Counter
import random

# ============================================================================
# Configuration
# ============================================================================

N_SAMPLE_SUBSETS = 500  # Nombre de sous-ensembles A à tester par (k,p)
SEED = 42

# ============================================================================
# Helpers
# ============================================================================

def ceil_log2_3_exact(k):
    three_k = 3 ** k
    S = k
    while (1 << S) < three_k:
        S += 1
    return S


def phi_sigma(A, sigma, p, pow3):
    """Calculer Φ_σ(A) = Σ 3^j · 2^{a_{σ(j)}} mod p."""
    val = 0
    for j, sj in enumerate(sigma):
        val = (val + pow3[j] * pow(2, A[sj], p)) % p
    return val


def compute_pi_distribution(A, p, pow3):
    """Pour un sous-ensemble A, calculer π(A,r) pour tout r ∈ F_p.

    Retourne le Counter des valeurs Φ_σ(A) mod p sur S_k.
    """
    k = len(A)
    dist = Counter()
    for sigma in permutations(range(k)):
        val = phi_sigma(A, sigma, p, pow3)
        dist[val] += 1
    return dist


def compute_pi_distribution_fast(A, p, pow3):
    """Version optimisée : pré-calculer 2^{a_i} mod p."""
    k = len(A)
    pow2_A = [pow(2, a, p) for a in A]
    dist = Counter()
    for sigma in permutations(range(k)):
        val = 0
        for j, sj in enumerate(sigma):
            val = (val + pow3[j] * pow2_A[sj]) % p
        dist[val] += 1
    return dist


def trial_factor_small(n, bound=10**6):
    factors = []
    d = 2
    while d * d <= n and d <= bound:
        if n % d == 0:
            while n % d == 0:
                n //= d
            factors.append(d)
        d += (1 if d == 2 else 2)
    if n > 1:
        factors.append(n)
    return factors


# ============================================================================
# Analyse PU pour une paire (k, p)
# ============================================================================

def analyze_PU(k, p, n_samples=N_SAMPLE_SUBSETS, verbose=True):
    """Vérifier PU pour (k, p)."""
    S = ceil_log2_3_exact(k)
    factorial_k = math.factorial(k)
    expected = factorial_k / p  # π(A,0) attendu sous PU

    # Pré-calculer 3^j mod p
    pow3 = [1] * k
    for j in range(1, k):
        pow3[j] = (pow3[j - 1] * 3) % p

    # Échantillonner des sous-ensembles A
    rng = random.Random(SEED + k * 1000 + p)
    pi0_values = []
    chi2_values = []

    for _ in range(n_samples):
        # Sous-ensemble aléatoire de taille k dans {0,...,S-1}
        A = sorted(rng.sample(range(S), k))

        # Calculer π(A,r) pour tout r
        dist = compute_pi_distribution_fast(A, p, pow3)

        # π(A,0)
        pi0 = dist.get(0, 0)
        pi0_values.append(pi0)

        # χ² test : distribution sur F_p
        chi2 = 0.0
        for r in range(p):
            obs = dist.get(r, 0)
            chi2 += (obs - expected) ** 2 / expected
        chi2_values.append(chi2)

    pi0_arr = np.array(pi0_values, dtype=float)
    chi2_arr = np.array(chi2_values)

    # Statistiques
    mean_pi0 = np.mean(pi0_arr)
    std_pi0 = np.std(pi0_arr)
    ratio_mean = mean_pi0 / expected if expected > 0 else float('inf')
    mean_chi2 = np.mean(chi2_arr)
    chi2_per_dof = mean_chi2 / (p - 1) if p > 1 else 0

    # Proportion de A avec π(A,0) = 0
    prop_zero = np.mean(pi0_arr == 0)

    if verbose:
        print(f"  k={k:>2} p={p:>6} S={S:>3}  "
              f"⟨π₀⟩={mean_pi0:>8.2f} (attendu {expected:>8.2f}) "
              f"ratio={ratio_mean:.4f}  "
              f"σ={std_pi0:.2f}  "
              f"χ²/(p-1)={chi2_per_dof:.4f}  "
              f"P(π₀=0)={prop_zero:.3f}")

    return {
        'k': k, 'p': p, 'S': S,
        'mean_pi0': mean_pi0, 'expected': expected,
        'ratio': ratio_mean, 'std_pi0': std_pi0,
        'chi2_per_dof': chi2_per_dof,
        'prop_zero': prop_zero,
        'n_samples': n_samples,
    }


# ============================================================================
# Main
# ============================================================================

def main():
    t_global = time.time()

    print("=" * 72)
    print("PHASE B3 — VÉRIFICATION NUMÉRIQUE PU (Proportion Uniformity)")
    print(f"Date : {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"Config : N_SAMPLE={N_SAMPLE_SUBSETS}, SEED={SEED}")
    print("=" * 72)

    # Paires (k, p) à tester
    test_cases = []
    for k in [5, 6, 7, 8]:
        S = ceil_log2_3_exact(k)
        d = (1 << S) - pow(3, k)
        if d <= 1:
            continue
        primes = trial_factor_small(d)
        for p in primes:
            if p <= 500:  # Limiter pour que k! permutations soient faisables
                test_cases.append((k, p))

    # Ajouter quelques primes de calibration
    for k in [5, 6, 7, 8]:
        for p in [13, 29, 53, 97]:
            if (k, p) not in test_cases:
                test_cases.append((k, p))

    print(f"\n{len(test_cases)} paires (k, p) à tester\n")
    print(f"  {'k':>2} {'p':>6} {'S':>3}  {'⟨π₀⟩':>8} {'attendu':>8} "
          f"{'ratio':>7}  {'σ':>6}  {'χ²/dof':>7}  {'P(π₀=0)':>8}")
    print("  " + "-" * 80)

    all_results = []
    for k, p in sorted(test_cases):
        result = analyze_PU(k, p, n_samples=N_SAMPLE_SUBSETS)
        all_results.append(result)

    # Synthèse
    print(f"\n{'='*72}")
    print("SYNTHÈSE PHASE B3")
    print(f"{'='*72}")

    ratios = [r['ratio'] for r in all_results]
    chi2s = [r['chi2_per_dof'] for r in all_results]

    print(f"\n  Ratio ⟨π₀⟩ / (k!/p) :")
    print(f"    min = {min(ratios):.4f}, max = {max(ratios):.4f}, "
          f"mean = {np.mean(ratios):.4f}")
    print(f"  χ²/(p-1) :")
    print(f"    min = {min(chi2s):.4f}, max = {max(chi2s):.4f}, "
          f"mean = {np.mean(chi2s):.4f}")

    # PU vérifiée si ratio ≈ 1.0 et χ²/dof ≈ 1.0
    pu_pass = sum(1 for r in all_results
                  if 0.8 < r['ratio'] < 1.2 and r['chi2_per_dof'] < 2.0)

    print(f"\n  PU (ratio ∈ [0.8, 1.2] et χ²/dof < 2) : "
          f"{pu_pass}/{len(all_results)}")

    # Cas avec ratio déviant
    deviants = [r for r in all_results
                if r['ratio'] < 0.8 or r['ratio'] > 1.2]
    if deviants:
        print(f"\n  ⚠️  {len(deviants)} cas avec ratio déviant :")
        for r in deviants:
            print(f"    k={r['k']}, p={r['p']}: ratio={r['ratio']:.4f}")
    else:
        print(f"\n  ✓ Aucun cas déviant détecté")

    # Conclusion
    print(f"\n{'='*72}")
    if pu_pass == len(all_results):
        print("✓ PU NUMÉRIQUEMENT CONFIRMÉE pour tous les cas testés")
    elif pu_pass > 0.9 * len(all_results):
        print(f"⚠️ PU partiellement confirmée ({pu_pass}/{len(all_results)})")
    else:
        print(f"✗ PU NON CONFIRMÉE ({pu_pass}/{len(all_results)})")
    print(f"{'='*72}")

    t_total = time.time() - t_global
    print(f"\nTemps total : {t_total:.1f}s")


if __name__ == '__main__':
    main()
