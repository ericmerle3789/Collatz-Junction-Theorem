#!/usr/bin/env python3
"""
Phase 22 — Borne CRT amplifiée pour N₀(d)
===========================================

Idée centrale : N₀(d) = 0 ne requiert PAS que N₀(p) = 0 pour un seul p.
Il suffit que le PRODUIT des probabilités P(corrSum ≡ 0 mod p_i) soit < 1/C.

Par CRT : N₀(d) ≈ C · Π_{p|d} (N₀(p)/C)

Si ce produit < 1, alors N₀(d) = 0.

Le théorème candidat :
  Pour k ≥ 3, avec d = 2^S - 3^k, on a
  Π_{p | d} (N₀(p) / C) < 1/C
  ce qui force N₀(d) = 0.

Auteur : Eric Merle (assisté par Claude)
Date : 28 février 2026
"""
import math
from itertools import combinations
from functools import reduce
import operator

def prime_factorization(n):
    """Factorisation complète de n (avec multiplicités)."""
    n = abs(n)
    factors = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors

def prime_factors(n):
    return sorted(prime_factorization(abs(n)).keys())

def corrsum_mod(A, k, m):
    """corrSum(A) mod m via Horner."""
    c = 0
    for j in range(k):
        c = (3 * c + pow(2, A[j], m)) % m
    return c

def all_compositions(S, k):
    """Comp(S, k) : compositions strictement croissantes commençant par 0."""
    return [(0,) + rest for rest in combinations(range(1, S), k - 1)]

log2_3 = math.log2(3)

# ============================================================
# SECTION 1 : Borne CRT multiplicative exacte
# ============================================================
print("=" * 80)
print("SECTION 1 : Borne CRT multiplicative — N₀(d) vs produit des N₀(p)/C")
print("=" * 80)
print(f"{'k':>3} {'S':>3} {'d':>12} {'C':>10} {'#primes':>7} "
      f"{'Π(N₀/C)':>12} {'C·Π':>10} {'N₀(d)':>6} {'exclu':>5}")
print("-" * 80)

for k in range(2, 21):
    S = math.ceil(k * log2_3)
    d = (1 << S) - 3**k
    if d <= 0:
        continue

    C = math.comb(S - 1, k - 1)
    if C > 2_000_000:
        print(f"{k:3d} {S:3d} {d:12d} {C:10d}  [C trop grand pour énumération]")
        continue

    primes = prime_factors(d)
    comps = all_compositions(S, k)

    # N₀(p) pour chaque premier p|d
    n0_primes = {}
    for p in primes:
        count = sum(1 for A in comps if corrsum_mod(A, k, p) == 0)
        n0_primes[p] = count

    # Produit CRT : Π (N₀(p) / C)
    product = 1.0
    for p in primes:
        product *= n0_primes[p] / C

    # N₀(d) exact
    n0_d = sum(1 for A in comps if corrsum_mod(A, k, d) == 0)

    # Prédiction CRT : N₀(d) ≈ C · Π (N₀(p)/C)
    predicted = C * product

    excluded = "OUI" if n0_d == 0 else "NON"

    print(f"{k:3d} {S:3d} {d:12d} {C:10d} {len(primes):7d} "
          f"{product:12.6e} {predicted:10.3f} {n0_d:6d} {excluded:>5}")

# ============================================================
# SECTION 2 : Analyse fine — ratio N₀(p)/C vs 1/p
# ============================================================
print("\n" + "=" * 80)
print("SECTION 2 : Biais — N₀(p)/C vs 1/p (le biais est-il systématiquement < 1 ?)")
print("=" * 80)
print(f"{'k':>3} {'p':>6} {'N₀(p)':>7} {'C':>10} {'N₀/C':>10} {'1/p':>10} "
      f"{'ratio':>8} {'biais':>8}")
print("-" * 80)

for k in range(2, 17):
    S = math.ceil(k * log2_3)
    d = (1 << S) - 3**k
    if d <= 0:
        continue

    C = math.comb(S - 1, k - 1)
    primes = prime_factors(d)
    comps = all_compositions(S, k)

    for p in primes:
        if p > 500:
            continue
        n0 = sum(1 for A in comps if corrsum_mod(A, k, p) == 0)
        ratio = (n0 / C) / (1 / p) if p > 1 else float('inf')
        biais = n0 / C - 1 / p
        sign = "+" if biais >= 0 else "-"
        print(f"{k:3d} {p:6d} {n0:7d} {C:10d} {n0/C:10.6f} {1/p:10.6f} "
              f"{ratio:8.4f} {sign}{abs(biais):7.6f}")

# ============================================================
# SECTION 3 : Indépendance CRT — corrélation entre résidus
# ============================================================
print("\n" + "=" * 80)
print("SECTION 3 : Test d'indépendance CRT")
print("=" * 80)

for k in [5, 7, 10, 12]:
    S = math.ceil(k * log2_3)
    d = (1 << S) - 3**k
    if d <= 0:
        continue
    C = math.comb(S - 1, k - 1)
    if C > 1_000_000:
        print(f"\nk={k}: C={C} trop grand, skip")
        continue

    primes = prime_factors(d)
    comps = all_compositions(S, k)

    print(f"\nk={k}, d={d}, primes={primes[:6]}")

    if len(primes) >= 2:
        p1, p2 = primes[0], primes[1]

        # Distribution jointe (r1, r2) mod (p1, p2)
        joint = {}
        marg1 = {}
        marg2 = {}
        for A in comps:
            r1 = corrsum_mod(A, k, p1)
            r2 = corrsum_mod(A, k, p2)
            joint[(r1, r2)] = joint.get((r1, r2), 0) + 1
            marg1[r1] = marg1.get(r1, 0) + 1
            marg2[r2] = marg2.get(r2, 0) + 1

        # Test : P(r1=0, r2=0) vs P(r1=0) * P(r2=0)
        p_joint = joint.get((0, 0), 0) / C
        p_marg1 = marg1.get(0, 0) / C
        p_marg2 = marg2.get(0, 0) / C
        p_indep = p_marg1 * p_marg2

        chi2_contrib = (p_joint - p_indep)**2 / max(p_indep, 1e-15) * C

        print(f"  p1={p1}, p2={p2}")
        print(f"  P(0,0) = {p_joint:.6f}")
        print(f"  P(0)·P(0) = {p_marg1:.6f} × {p_marg2:.6f} = {p_indep:.6f}")
        print(f"  Ratio = {p_joint/max(p_indep, 1e-15):.4f}")
        print(f"  chi² contribution = {chi2_contrib:.4f}")

        # Corrélation entre les vecteurs (corrSum mod p1) et (corrSum mod p2)
        import numpy as np
        v1 = np.array([corrsum_mod(A, k, p1) for A in comps])
        v2 = np.array([corrsum_mod(A, k, p2) for A in comps])
        corr = np.corrcoef(v1, v2)[0, 1]
        print(f"  Pearson correlation = {corr:.6f}")

# ============================================================
# SECTION 4 : Le théorème CRT quantitatif — prédiction vs réalité
# ============================================================
print("\n" + "=" * 80)
print("SECTION 4 : Prédiction CRT quantitative vs N₀(d) exact")
print("=" * 80)
print(f"{'k':>3} {'N₀(d)':>7} {'C·Π(N₀/C)':>12} {'C·Π(1/p)':>12} "
      f"{'rapport':>10} {'qualité':>10}")
print("-" * 70)

for k in range(2, 17):
    S = math.ceil(k * log2_3)
    d = (1 << S) - 3**k
    if d <= 0:
        continue

    C = math.comb(S - 1, k - 1)
    primes = prime_factors(d)
    comps = all_compositions(S, k)

    # Calculs
    n0_primes = {}
    for p in primes:
        n0_primes[p] = sum(1 for A in comps if corrsum_mod(A, k, p) == 0)

    n0_d = sum(1 for A in comps if corrsum_mod(A, k, d) == 0)

    # Prédiction CRT (avec biais mesuré)
    prod_biased = C * reduce(operator.mul, [n0_primes[p] / C for p in primes], 1.0)

    # Prédiction CRT naïve (1/p uniforme)
    prod_naive = C / d  # = C · Π(1/p^{e_p})

    rapport = n0_d / max(prod_biased, 1e-15)

    quality = "EXACT" if abs(n0_d - round(prod_biased)) <= 1 else \
              "BON" if abs(n0_d - prod_biased) < max(2, prod_biased * 0.3) else "DIVERGE"

    print(f"{k:3d} {n0_d:7d} {prod_biased:12.3f} {prod_naive:12.4f} "
          f"{rapport:10.4f} {quality:>10}")

# ============================================================
# SECTION 5 : Le mécanisme d'exclusion — POURQUOI N₀(d) = 0
# ============================================================
print("\n" + "=" * 80)
print("SECTION 5 : Décomposition de l'exclusion — quelles primes excluent ?")
print("=" * 80)

for k in range(3, 17):
    S = math.ceil(k * log2_3)
    d = (1 << S) - 3**k
    if d <= 0:
        continue

    C = math.comb(S - 1, k - 1)
    if C > 1_000_000:
        print(f"k={k}: C={C} trop grand, skip")
        continue

    primes = prime_factors(d)
    comps = all_compositions(S, k)

    # Intersection CRT progressive
    survivors = list(range(len(comps)))
    info = []
    for p in primes:
        new_survivors = [i for i in survivors if corrsum_mod(comps[i], k, p) == 0]
        ratio = len(new_survivors) / max(len(survivors), 1)
        info.append(f"{p}:{len(new_survivors)}")
        survivors = new_survivors
        if len(survivors) == 0:
            break

    n0_d = len(survivors)
    killed_by = "none" if n0_d > 0 else f"cumul→{info[-1].split(':')[0]}" if info else "?"

    print(f"k={k:2d}: d={d:>10d}, N₀(d)={n0_d}, path=[{', '.join(info)}], killed_by={killed_by}")

# ============================================================
# SECTION 6 : Borne théorique — CRT sous hypothèse de quasi-uniformité
# ============================================================
print("\n" + "=" * 80)
print("SECTION 6 : Borne théorique CRT avec quasi-uniformité mesurée")
print("=" * 80)

print("\nSi N₀(p) ≤ C/p · (1 + ε_p), alors :")
print("  N₀(d) ≤ C · Π(1/p · (1+ε_p)) = (C/d) · Π(1+ε_p)")
print("  Pour N₀(d) = 0, il suffit que (C/d) · Π(1+ε_p) < 1")
print("  i.e., C/d < Π(1/(1+ε_p))")
print()
print(f"{'k':>3} {'C/d':>10} {'Π(1+ε)':>10} {'(C/d)·Π':>10} {'bound<1':>8}")
print("-" * 60)

for k in range(2, 17):
    S = math.ceil(k * log2_3)
    d = (1 << S) - 3**k
    if d <= 0:
        continue

    C = math.comb(S - 1, k - 1)
    primes = prime_factors(d)
    comps = all_compositions(S, k)

    # Mesurer ε_p pour chaque p
    product_eps = 1.0
    for p in primes:
        if p > 1000:
            n0_est = C / p  # approximation
        else:
            n0_est = sum(1 for A in comps if corrsum_mod(A, k, p) == 0)
        eps_p = (n0_est / (C / p)) - 1.0 if C / p > 0 else 0
        product_eps *= (1 + eps_p)

    crt_bound = (C / d) * product_eps
    ok = "OUI" if crt_bound < 1 else "non"

    print(f"{k:3d} {C/d:10.4f} {product_eps:10.4f} {crt_bound:10.4f} {ok:>8}")

print("\n✓ Phase 22 amplification CRT terminée.")
