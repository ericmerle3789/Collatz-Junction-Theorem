#!/usr/bin/env python3
"""
PROBLEM REFORMULATOR — Change the formulation to open new proof paths
========================================================================

Le même problème (N₀=0) peut être vu sous DIFFÉRENTS angles :

FORMULATION 1 (originale) :
  ∀σ ∈ Comp_cum(S,k) : corrSum(σ) ≢ 0 mod d

FORMULATION 2 (δ-séquences) :
  ∀δ faiblement croissant : 1 + Σ ρ^i · 2^{δ_i} ≢ 0 mod d

FORMULATION 3 (polynomiale) :
  ∀δ non-trié avec F(δ)=0 : R_δ(ρ) ≠ 0

FORMULATION 4 (ensembliste) :
  {corrSum(σ) mod d} ∩ {0} = ∅

FORMULATION 5 (géométrique) :
  Le point (2^{σ_0},...,2^{σ_{k-1}}) pondéré par (3^{k-1},...,1)
  ne tombe jamais sur le réseau d·Z

FORMULATION 6 (analytique) :
  La fonction génératrice Σ_σ z^{corrSum(σ)} n'a pas de coefficient
  aux positions d·n pour n ∈ Z⁺

FORMULATION 7 (p-adique) :
  |corrSum(σ)|_p < |d|_p pour au moins un p | d, pour tout σ

FORMULATION 8 (informationnelle) :
  L'information de Shannon de la distribution corrSum mod d
  est strictement inférieure à log₂(d) bits

FORMULATION 9 (catégorielle) :
  Le foncteur Ev_d : Comp → Z/dZ n'est pas essentiellement surjectif sur {0}

FORMULATION 10 (dynamique) :
  La dynamique T(n) = (3n+1)/2^{v₂(3n+1)} n'a pas d'orbite périodique
  de longueur k pour aucun n > 0

Chaque formulation suggère des OUTILS DIFFÉRENTS.
Le reformulateur essaie chacune et mesure le "potentiel de preuve".
"""

import sys, os
from math import ceil, log2, comb, gcd, log
from itertools import combinations
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


def evaluate_formulation_potential(name, description, test_fn, k_max=10):
    """Evaluate the 'proof potential' of a formulation.
    Higher score = more structure visible = more likely to yield proof."""
    score = 0
    details = []

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 100000: continue

        result = test_fn(k, S, d)
        if result is not None:
            score += result.get('score', 0)
            details.append({'k': k, **result})

    return {
        'name': name,
        'description': description,
        'total_score': score,
        'details': details,
    }


def form_original(k, S, d):
    """Formulation 1: direct corrSum mod d check."""
    residues = [corrsum_cumulative(sigma, k) % d
               for sigma in enumerate_cumulative_sequences(k, S)]
    n_zero = sum(1 for r in residues if r == 0)
    coverage = len(set(residues)) / d
    return {'score': 1.0 if n_zero == 0 else 0, 'n_zero': n_zero, 'coverage': coverage}


def form_delta_rho(k, S, d):
    """Formulation 2: REST' = Σ ρ^i · 2^{δ_i} ≡ -1?"""
    inv3 = pow(3, -1, d)
    rho = (2 * inv3) % d
    rho_pow = [pow(rho, i, d) for i in range(k)]
    max_delta = S - k

    # Check if the ρ-representation reveals more structure
    # Measure: how many distinct REST' values? (should be C)
    from itertools import combinations_with_replacement
    rest_values = set()
    for deltas in combinations_with_replacement(range(max_delta + 1), k - 1):
        val = (1 + sum(rho_pow[i+1] * pow(2, deltas[i], d) % d for i in range(k-1))) % d
        rest_values.add(val)

    # Score: structure visibility
    target = 0  # REST'+1 ≡ 0 means corrSum ≡ 0
    target_hit = target in rest_values
    return {
        'score': 1.5 if not target_hit else 0,
        'n_rest_values': len(rest_values),
        'target_hit': target_hit,
        'rho': rho, 'ord_rho': min(d, 100000),  # Placeholder
    }


def form_polynomial(k, S, d):
    """Formulation 3: R_δ(ρ) ≠ 0 for all free δ."""
    # Score based on degree of R (lower = easier to prove)
    deg_R = k - 3
    if d > deg_R:
        score = 2.0 * (1 - deg_R / d)  # Higher score when d >> deg
    else:
        score = 0.5
    return {'score': score, 'deg_R': deg_R, 'max_roots': deg_R, 'd': d}


def form_geometric(k, S, d):
    """Formulation 5: lattice point avoidance."""
    # The corrSum values live in a k-dim sublattice of Z
    # Score: measure how "far" they are from d·Z in a geometric sense
    residues = [corrsum_cumulative(sigma, k) % d
               for sigma in enumerate_cumulative_sequences(k, S)]
    if not residues: return None
    min_dist = min(min(r, d-r) for r in residues)
    avg_dist = sum(min(r, d-r) for r in residues) / len(residues)
    return {
        'score': 1.0 + min_dist / max(1, d) * 10,
        'min_dist': min_dist,
        'avg_dist': avg_dist,
    }


def form_padic(k, S, d):
    """Formulation 7: p-adic valuation analysis."""
    factors = {}
    n = d
    for p in range(2, min(10000, n)):
        while n % p == 0:
            factors[p] = factors.get(p, 0) + 1
            n //= p
    if n > 1:
        factors[n] = 1

    # For each prime p|d: check max v_p(corrSum)
    best_block = 0
    for p, vd in factors.items():
        max_vp = 0
        for sigma in enumerate_cumulative_sequences(k, S):
            cs = corrsum_cumulative(sigma, k)
            v = 0
            while cs > 0 and cs % p == 0:
                v += 1; cs //= p
            max_vp = max(max_vp, v)
        if max_vp < vd:
            best_block = max(best_block, vd - max_vp)

    return {
        'score': 1.0 + best_block * 2,
        'factors': factors,
        'best_block': best_block,
    }


def form_information(k, S, d):
    """Formulation 8: information-theoretic."""
    residues = [corrsum_cumulative(sigma, k) % d
               for sigma in enumerate_cumulative_sequences(k, S)]
    C = len(residues)
    counts = Counter(residues)
    # Shannon entropy of the distribution
    entropy = -sum(c/C * log(c/C) for c in counts.values() if c > 0)
    max_entropy = log(d) if d > 0 else 0
    info_gap = max_entropy - entropy
    return {
        'score': 0.5 + info_gap,
        'entropy': entropy,
        'max_entropy': max_entropy,
        'info_gap': info_gap,
    }


def run_reformulator(k_max=10):
    """Test all formulations and rank by proof potential."""
    print("PROBLEM REFORMULATOR — Ranking formulations by proof potential")
    print("=" * 65)

    formulations = [
        ("F1_original", "corrSum ≢ 0 mod d", form_original),
        ("F2_delta_rho", "REST' = Σρ^i·2^{δ_i} ≢ -1", form_delta_rho),
        ("F3_polynomial", "R_δ(ρ) ≠ 0, deg=k-3", form_polynomial),
        ("F5_geometric", "Lattice point avoidance", form_geometric),
        ("F7_padic", "p-adic valuation blocking", form_padic),
        ("F8_information", "Shannon entropy gap", form_information),
    ]

    results = []
    for name, desc, fn in formulations:
        r = evaluate_formulation_potential(name, desc, fn, k_max)
        results.append(r)

    # Rank
    results.sort(key=lambda r: r['total_score'], reverse=True)

    print(f"\n{'Formulation':<25} {'Score':>8} {'Description':<35}")
    print("-" * 70)
    for r in results:
        print(f"{r['name']:<25} {r['total_score']:>8.2f} {r['description']:<35}")

    # Best formulation
    best = results[0]
    print(f"\n★ BEST FORMULATION: {best['name']}")
    print(f"  {best['description']}")
    print(f"  Total score: {best['total_score']:.2f}")

    return results


if __name__ == '__main__':
    run_reformulator(k_max=10)
