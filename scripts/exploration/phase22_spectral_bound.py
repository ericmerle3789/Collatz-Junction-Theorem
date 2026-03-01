#!/usr/bin/env python3
"""
Phase 22 — Borne spectrale rigoureuse pour N₀
Théorème candidat : borne de N₀(p) via le trou spectral de l'opérateur de Horner.

L'idée : la récurrence c_{j+1} = 3c_j + 2^{A_j} mod p définit un opérateur
de transfert L sur F_p. Le trou spectral Δ = 1 - |λ₂| contrôle la TV distance
à l'uniformité après k étapes. Si TV < (1 - C/p), alors N₀ = 0.

Auteur : Eric Merle (assisté par Claude)
Date : 28 février 2026
"""
import math
import numpy as np
from itertools import combinations

def ord_mod(g, p):
    if p <= 1 or g % p == 0:
        return 0
    o, x = 1, g % p
    while x != 1:
        x = (x * g) % p
        o += 1
    return o

def prime_factors(n):
    n = abs(n)
    factors = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.append(d)
            n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return sorted(set(factors))

def build_transfer_operator(p, S, inv3):
    """
    Opérateur de transfert L (p × p) pour UNE étape de Horner.
    (Lπ)(s) = (1/S) Σ_{a=0}^{S-1} π(inv3 * (s - 2^a) mod p)

    En pratique : L[s][r] = prob de passer de r à s en une étape.
    """
    L = np.zeros((p, p))
    pow2 = [pow(2, a, p) for a in range(S)]

    for a in range(S):
        two_a = pow2[a]
        for r in range(p):
            s = (3 * r + two_a) % p
            L[s][r] += 1.0 / S

    return L

def spectral_gap(L):
    """Calcule le trou spectral Δ = 1 - |λ₂|."""
    eigenvalues = np.linalg.eigvals(L)
    mods = sorted(np.abs(eigenvalues), reverse=True)
    # λ₁ = 1, λ₂ = second largest
    return 1.0 - mods[1] if len(mods) > 1 else 1.0, mods[1]

def exact_distribution(k, S, p):
    """Distribution exacte de corrSum mod p par énumération."""
    dist = np.zeros(p)
    count = 0
    for rest in combinations(range(1, S), k - 1):
        A = (0,) + rest
        c = 0
        for j in range(k):
            c = (3 * c + pow(2, A[j], p)) % p
        dist[c] += 1
        count += 1
    return dist, count

def tv_distance(dist, C, p):
    """Distance en variation totale à la distribution uniforme."""
    uniform = C / p
    return 0.5 * sum(abs(dist[r] - uniform) for r in range(p))

log2_3 = math.log2(3)

# ============================================================
# SECTION 1 : Trou spectral et borne TV pour k = 2..14
# ============================================================
print("=" * 80)
print("SECTION 1 : Trou spectral, TV exacte, et borne théorique sur N₀")
print("=" * 80)
print(f"{'k':>3} {'p':>6} {'ω':>4} {'S/ω':>6} {'Δ':>7} {'|λ₂|':>7} "
      f"{'TV_exact':>9} {'N₀':>5} {'C/p':>7} {'bound':>9} {'exclu':>6}")
print("-" * 80)

for k in range(2, 15):
    S = math.ceil(k * log2_3)
    d = (1 << S) - 3**k
    if d <= 0:
        continue

    C = math.comb(S - 1, k - 1)
    primes = prime_factors(d)

    for p in primes:
        if p > 300:  # Limiter la taille de la matrice
            continue

        omega = ord_mod(2, p)
        inv3 = pow(3, p - 2, p)

        # Opérateur de transfert
        L = build_transfer_operator(p, S, inv3)
        delta, lam2 = spectral_gap(L)

        # Distribution exacte
        dist, count = exact_distribution(k, S, p)
        tv = tv_distance(dist, C, p)
        N0 = int(dist[0])

        # Borne théorique TV après k étapes
        # TV ≤ √(p) · |λ₂|^k / 2  (borne standard pour chaînes de Markov)
        tv_bound = math.sqrt(p) * lam2**k / 2

        # Borne sur N₀ : N₀ ≤ C/p + C · tv_bound / (C/p * p)
        # Plus précisément : |N₀ - C/p| ≤ TV · C / (C/p) = TV * p
        # Donc N₀ ≤ C/p + TV * ...
        # La bonne borne : N₀ ≤ C/p + tv * 2  (par def de TV)
        # Plus fin : N₀ ≤ C * (1/p + tv_bound)

        n0_bound_upper = C * (1.0/p + tv_bound)
        excluded = "OUI" if n0_bound_upper < 1.0 else "non"

        print(f"{k:3d} {p:6d} {omega:4d} {S/omega:6.2f} {delta:7.4f} {lam2:7.4f} "
              f"{tv/C:9.5f} {N0:5d} {C/p:7.3f} {n0_bound_upper:9.3f} {excluded:>6}")

# ============================================================
# SECTION 2 : Analyse fine — pourquoi N₀ = 0 pour k=5, p=13
# ============================================================
print("\n" + "=" * 80)
print("SECTION 2 : Anatomie de l'exclusion pour q₃ (k=5, p=13)")
print("=" * 80)

k, S, p = 5, 8, 13
omega = ord_mod(2, p)
C = math.comb(S - 1, k - 1)

# Distribution étape par étape
print(f"\nk={k}, S={S}, p={p}, ω={omega}, C={C}")
print("\nDistribution de c_j mod p à chaque étape de Horner :")

comps = list(combinations(range(1, S), k - 1))
comps = [(0,) + c for c in comps]

for step in range(1, k + 1):
    dist = np.zeros(p)
    for A in comps:
        c = 0
        for j in range(step):
            c = (3 * c + pow(2, A[j], p)) % p
        dist[c] += 1

    n0 = int(dist[0])
    tv = tv_distance(dist, C, p)
    max_r = int(max(dist))
    min_r = int(min(dist))
    print(f"  Étape {step}: N₀={n0:3d}, TV/C={tv/C:.4f}, "
          f"max={max_r}, min={min_r}, spread={max_r-min_r}")

# Distribution finale détaillée
print(f"\nDistribution finale corrSum mod {p}:")
dist_final, _ = exact_distribution(k, S, p)
for r in range(p):
    bar = '█' * int(dist_final[r])
    print(f"  r={r:2d}: {int(dist_final[r]):3d} {bar}")

# ============================================================
# SECTION 3 : Le "target" structural — pourquoi 0 est évité
# ============================================================
print("\n" + "=" * 80)
print("SECTION 3 : Structure du target -3^{k-1} mod p")
print("=" * 80)

for k in range(2, 15):
    S = math.ceil(k * log2_3)
    d = (1 << S) - 3**k
    if d <= 0:
        continue

    primes = prime_factors(d)
    for p in primes[:2]:
        if p > 300:
            continue
        omega = ord_mod(2, p)
        target = (-pow(3, k-1, p)) % p

        # V(A) = corrSum - 3^{k-1} doit atteindre target pour corrSum = 0
        # V vit dans les résidus pairs si tous les A_i >= 1
        # Target est -3^{k-1} mod p

        # Le log discret de target dans <2>
        log_target = None
        x = 1
        for i in range(omega):
            if x == target % p:
                log_target = i
                break
            x = (x * 2) % p

        in_orbit = log_target is not None
        print(f"k={k:2d}, p={p:5d}: target = {target:5d}, "
              f"ω={omega:3d}, target ∈ ⟨2⟩ = {in_orbit}, "
              f"{'log₂=' + str(log_target) if in_orbit else 'TYPE II'}")

# ============================================================
# SECTION 4 : Borne par le second moment (Parseval)
# ============================================================
print("\n" + "=" * 80)
print("SECTION 4 : Second moment et borne de Parseval")
print("=" * 80)

import cmath
PI2 = 2 * math.pi

for k in range(3, 13):
    S = math.ceil(k * log2_3)
    d = (1 << S) - 3**k
    if d <= 0:
        continue
    C = math.comb(S - 1, k - 1)
    primes = prime_factors(d)

    for p in primes[:1]:
        if p > 200:
            continue

        # Distribution exacte
        dist, _ = exact_distribution(k, S, p)
        N0 = int(dist[0])

        # Second moment E₂ = Σ N_r²
        E2 = sum(dist[r]**2 for r in range(p))

        # Si uniforme : E2_unif = C²/p
        E2_unif = C**2 / p

        # Non-uniformité = E₂ / E₂_unif
        nu = E2 / E2_unif

        # Parseval : Σ_{t≠0} |T(t)|² = p · E₂ - C²
        parseval_nontriv = p * E2 - C**2

        # Borne triviale : max |T(t)| ≤ C
        # Par Parseval : mean |T(t)|² = parseval_nontriv / (p-1)
        mean_T2 = parseval_nontriv / (p - 1)
        rms_T = math.sqrt(mean_T2)

        print(f"k={k:2d} p={p:5d}: N₀={N0:4d}, E₂={E2:12.0f}, "
              f"E₂/uniform={nu:.4f}, rms|T|={rms_T:.2f}, "
              f"rms/C={rms_T/C:.4f}")

print("\n✓ Phase 22 borne spectrale terminée.")
