#!/usr/bin/env python3
"""
Phase 22 — Exploration : Factorisation multiplicative des sommes de Horner
Objectif : Tester l'hypothèse que e(t·corrSum/p) = Π e(t·3^{k-1-j}·2^{A_j}/p)
           permet de borner |T(t)| via la structure ordonnée des compositions.

Auteur : Eric Merle (assisté par Claude)
Date : 28 février 2026
"""
import math
import cmath
from itertools import combinations
from functools import reduce

PI2 = 2 * math.pi

def factorize(n):
    """Factorisation en premiers."""
    if n <= 1:
        return []
    factors = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.append(d)
            n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors

def prime_factors(n):
    return sorted(set(factorize(abs(n))))

def ord_mod(g, p):
    """Ordre multiplicatif de g mod p."""
    if p <= 1 or g % p == 0:
        return 0
    o, x = 1, g % p
    while x != 1:
        x = (x * g) % p
        o += 1
    return o

def corrsum_mod(A, k, p):
    """corrSum(A) mod p via Horner."""
    c = 0
    for j in range(k):
        c = (3 * c + pow(2, A[j], p)) % p
    return c

def compute_T(t, k, S, p, compositions):
    """Somme exponentielle T(t) = Σ_A e(t·corrSum(A)/p)."""
    total = 0j
    for A in compositions:
        cs = corrsum_mod(A, k, p)
        total += cmath.exp(2j * cmath.pi * t * cs / p)
    return total

def all_compositions(S, k):
    """Toutes les compositions A = (0, A_1, ..., A_{k-1}) de Comp(S, k)."""
    comps = []
    for rest in combinations(range(1, S), k - 1):
        comps.append((0,) + rest)
    return comps

# ============================================================
# SECTION 1 : Factorisation multiplicative de la phase
# ============================================================
print("=" * 70)
print("SECTION 1 : Vérification de la factorisation multiplicative")
print("=" * 70)

# Pour q3 : k=5, S=8, p=13
k, S, p = 5, 8, 13
comps = all_compositions(S, k)
C = len(comps)
print(f"\nq3 : k={k}, S={S}, p={p}, C={C}")

for t in [1, 3, 5]:
    T_direct = compute_T(t, k, S, p, comps)

    # Vérification : e(t·corrSum/p) = Π_j e(t·3^{k-1-j}·2^{A_j}/p)
    T_product = 0j
    for A in comps:
        prod = 1.0
        for j in range(k):
            phase = PI2 * t * pow(3, k-1-j, p) * pow(2, A[j], p) / p
            prod *= cmath.exp(1j * phase)
        T_product += prod

    print(f"  t={t}: T_direct = {T_direct:.6f}, T_product = {T_product:.6f}, "
          f"match = {abs(T_direct - T_product) < 1e-8}")

# ============================================================
# SECTION 2 : Facteurs individuels G_j = Σ_b e(t·α_j·2^b/p)
# ============================================================
print("\n" + "=" * 70)
print("SECTION 2 : Facteurs géométriques G_j (sommes sur 2^b)")
print("=" * 70)

omega = ord_mod(2, p)
print(f"ord_{p}(2) = {omega}")

for t in [1, 3, 5]:
    print(f"\n  t = {t}:")
    G_product = 1.0
    for j in range(k):
        alpha_j = (t * pow(3, k-1-j, p)) % p
        G_j = sum(cmath.exp(2j * cmath.pi * alpha_j * pow(2, b, p) / p)
                   for b in range(S))
        print(f"    G_{j} (α={alpha_j:3d}): |G_{j}| = {abs(G_j):.4f}, "
              f"arg = {cmath.phase(G_j):.4f}, G/S = {abs(G_j)/S:.4f}")
        G_product *= G_j

    # Le produit libre (sans contrainte d'ordre) = Π G_j / normalisation
    print(f"    |Π G_j| = {abs(G_product):.4f}")
    T_val = compute_T(t, k, S, p, comps)
    print(f"    |T(t)|  = {abs(T_val):.4f}")
    print(f"    Ratio |T|/C = {abs(T_val)/C:.4f}")

# ============================================================
# SECTION 3 : Distribution de corrSum et N_0 pour k = 2..30
# ============================================================
print("\n" + "=" * 70)
print("SECTION 3 : N_0 systématique et premiers candidats")
print("=" * 70)

log2_3 = math.log2(3)
results = []

for k in range(2, 31):
    S = math.ceil(k * log2_3)
    d = (1 << S) - 3**k
    if d <= 0:
        continue

    C = math.comb(S - 1, k - 1)
    primes_d = prime_factors(d)

    # Pour les petits k, on peut énumérer
    if C <= 500000:
        comps = all_compositions(S, k)

        # N_0 pour chaque premier p | d
        n0_by_prime = {}
        for pp in primes_d:
            dist = {}
            for A in comps:
                r = corrsum_mod(A, k, pp)
                dist[r] = dist.get(r, 0) + 1
            n0_by_prime[pp] = dist.get(0, 0)

        # CRT : N_0 global
        n0_d = sum(1 for A in comps if corrsum_mod(A, k, d) == 0)

        excluded = "OUI" if n0_d == 0 else "NON"
        prime_info = ", ".join(f"N₀({pp})={n0_by_prime[pp]}" for pp in primes_d[:4])
        results.append((k, S, d, C, n0_d, excluded, prime_info))
        print(f"k={k:2d} S={S:2d} d={d:>10d} C={C:>10d} C/d={C/d:.4f} "
              f"N₀(d)={n0_d:>6d} [{excluded}] {prime_info}")
    else:
        results.append((k, S, d, C, -1, "?", f"C trop grand ({C})"))
        print(f"k={k:2d} S={S:2d} d={d:>10d} C={C:>10d} C/d={C/d:.4f} "
              f"[C trop grand pour énumération]")

# ============================================================
# SECTION 4 : Le mécanisme CRT en détail
# ============================================================
print("\n" + "=" * 70)
print("SECTION 4 : Synergie CRT — intersection progressive")
print("=" * 70)

for k in [5, 7, 10, 12]:
    S = math.ceil(k * log2_3)
    d = (1 << S) - 3**k
    if d <= 0:
        continue
    C = math.comb(S - 1, k - 1)
    if C > 500000:
        print(f"\nk={k}: C={C} trop grand, skip")
        continue

    comps = all_compositions(S, k)
    primes_d = prime_factors(d)

    print(f"\nk={k}, d={d} = {'×'.join(str(pp) for pp in primes_d)}")

    # Intersection progressive
    survivors = set(range(len(comps)))
    for pp in primes_d:
        new_survivors = set()
        for idx in survivors:
            if corrsum_mod(comps[idx], k, pp) == 0:
                new_survivors.add(idx)
        print(f"  mod {pp:>6d}: {len(survivors):>6d} → {len(new_survivors):>6d} "
              f"(ratio: {len(new_survivors)/max(len(survivors),1):.4f}, "
              f"attendu: {1/pp:.6f})")
        survivors = new_survivors

    print(f"  FINAL N₀(d) = {len(survivors)}")

print("\n✓ Phase 22 exploration terminée.")
