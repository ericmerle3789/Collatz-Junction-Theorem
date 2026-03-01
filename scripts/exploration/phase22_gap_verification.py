#!/usr/bin/env python3
"""
Phase 22 — Vérification du gap k=16,17 + Monte Carlo k=18..40
==============================================================

Objectif 1 : Vérifier exhaustivement N₀(d) pour k=16,17.
Objectif 2 : Pour k=18..40, estimer N₀(d) par Monte Carlo (échantillonnage).
Objectif 3 : Vérifier N₀(p) pour les premiers p|d accessibles (k ≤ 40).

Auteur : Eric Merle (assisté par Claude)
Date : 28 février 2026
"""
import math
import random
from itertools import combinations
import time

def prime_factorization(n):
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
    c = 0
    for j in range(k):
        c = (3 * c + pow(2, A[j], m)) % m
    return c

def corrsum_exact(A, k):
    """corrSum exact (entiers Python arbitraires)."""
    c = 0
    for j in range(k):
        c = 3 * c + (1 << A[j])
    return c

def random_composition(S, k):
    """Composition aléatoire : 0 = A_0 < A_1 < ... < A_{k-1} ≤ S-1."""
    rest = sorted(random.sample(range(1, S), k - 1))
    return (0,) + tuple(rest)

log2_3 = math.log2(3)

# ============================================================
# SECTION 1 : Vérification exhaustive k=16, k=17
# ============================================================
print("=" * 80)
print("SECTION 1 : Vérification exhaustive N₀(d) pour k=16 et k=17")
print("=" * 80)

for k in [16, 17]:
    S = math.ceil(k * log2_3)
    d = (1 << S) - 3**k
    C = math.comb(S - 1, k - 1)
    primes = prime_factors(d)

    print(f"\nk={k}, S={S}, d={d}, C={C}")
    print(f"  Facteurs premiers de d: {primes[:8]}{'...' if len(primes)>8 else ''}")
    print(f"  C/d = {C/d:.6f}")

    t0 = time.time()

    # N₀(p) pour chaque petit premier
    n0_by_prime = {}
    for p in primes:
        if p > 100000:
            continue
        count = 0
        for rest in combinations(range(1, S), k - 1):
            A = (0,) + rest
            if corrsum_mod(A, k, p) == 0:
                count += 1
        n0_by_prime[p] = count
        print(f"  N₀({p}) = {count} (N₀/C = {count/C:.6f}, 1/p = {1/p:.6f})")

    # N₀(d) par CRT progressif
    survivors = set(range(C))
    comps_iter = list(combinations(range(1, S), k - 1))

    for p in primes:
        if p > 100000:
            # Pour les grands premiers, vérifier parmi les survivants
            new_survivors = set()
            for idx in survivors:
                A = (0,) + comps_iter[idx]
                if corrsum_mod(A, k, p) == 0:
                    new_survivors.add(idx)
        else:
            new_survivors = set()
            for idx in survivors:
                A = (0,) + comps_iter[idx]
                if corrsum_mod(A, k, p) == 0:
                    new_survivors.add(idx)

        ratio = len(new_survivors) / max(len(survivors), 1)
        print(f"  CRT mod {p:>10d}: {len(survivors):>8d} → {len(new_survivors):>8d} "
              f"(ratio: {ratio:.6f}, 1/p: {1/p:.6f})")
        survivors = new_survivors
        if len(survivors) == 0:
            break

    t1 = time.time()
    print(f"  *** N₀(d) = {len(survivors)} *** (temps: {t1-t0:.1f}s)")

# ============================================================
# SECTION 2 : Monte Carlo pour k=18..40
# ============================================================
print("\n" + "=" * 80)
print("SECTION 2 : Monte Carlo — estimation de P(corrSum ≡ 0 mod d)")
print("=" * 80)
print("  N_samples = 10^6 pour chaque k")
print()

N_samples = 1_000_000

print(f"{'k':>3} {'S':>3} {'C/d':>10} {'hits/N':>12} {'est_N₀':>10} "
      f"{'95% CI':>20} {'verdict':>8}")
print("-" * 80)

for k in range(18, 41):
    S = math.ceil(k * log2_3)
    d = (1 << S) - 3**k
    if d <= 0:
        continue

    C = math.comb(S - 1, k - 1)

    # Monte Carlo : échantillonner N_samples compositions
    hits = 0
    for _ in range(N_samples):
        A = random_composition(S, k)
        if corrsum_mod(A, k, d) == 0:
            hits += 1

    # Intervalle de confiance (Clopper-Pearson approché)
    p_hat = hits / N_samples
    se = math.sqrt(p_hat * (1 - p_hat) / N_samples) if hits > 0 else 1 / N_samples
    ci_low = max(0, p_hat - 1.96 * se)
    ci_high = p_hat + 1.96 * se

    est_n0 = p_hat * C

    verdict = "N₀=0?" if hits == 0 else f"~{est_n0:.0f}"

    print(f"{k:3d} {S:3d} {C/d:10.6f} {hits}/{N_samples:<7d} "
          f"{est_n0:10.2f} [{ci_low:.6f}, {ci_high:.6f}] {verdict:>8}")

# ============================================================
# SECTION 3 : Vérification N₀(p) pour petits p|d, k=18..40
# ============================================================
print("\n" + "=" * 80)
print("SECTION 3 : N₀(p) par Monte Carlo pour petits premiers p|d")
print("=" * 80)

N_mc = 500_000

for k in range(18, 41):
    S = math.ceil(k * log2_3)
    d = (1 << S) - 3**k
    if d <= 0:
        continue

    C = math.comb(S - 1, k - 1)
    primes = prime_factors(d)

    small_primes = [p for p in primes if p <= 1000]
    if not small_primes:
        # Trouver quelques petits premiers parmi la factorisation
        small_primes = primes[:3]

    info_parts = []
    for p in small_primes[:4]:
        hits = sum(1 for _ in range(N_mc)
                   if corrsum_mod(random_composition(S, k), k, p) == 0)
        ratio = (hits / N_mc) / (1 / p)
        info_parts.append(f"p={p}: {hits/N_mc:.4f}≈{1/p:.4f} (r={ratio:.3f})")

    print(f"k={k:2d}: C/d={C/d:.4e}, {', '.join(info_parts)}")

# ============================================================
# SECTION 4 : Le cas critique k=2 — pourquoi N₀ ≠ 0
# ============================================================
print("\n" + "=" * 80)
print("SECTION 4 : k=2, le cycle trivial — anatomie")
print("=" * 80)

k, S = 2, 4
d = (1 << S) - 3**k  # 16 - 9 = 7
C = math.comb(S - 1, k - 1)  # C(3,1) = 3
print(f"k=2, S=4, d=7, C=3")
print("Compositions et corrSum :")
for rest in combinations(range(1, S), k - 1):
    A = (0,) + rest
    cs = corrsum_exact(A, k)
    print(f"  A={A}: corrSum = 3·2^{A[0]} + 2^{A[1]} = 3·{1<<A[0]} + {1<<A[1]} "
          f"= {cs}, mod 7 = {cs % 7}")

print(f"\nA=(0,2): corrSum = 7 ≡ 0 mod 7 → n₀ = 1 → cycle trivial 1→2→1")

print("\n✓ Phase 22 vérification du gap terminée.")
