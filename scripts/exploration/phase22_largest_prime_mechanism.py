#!/usr/bin/env python3
"""
Phase 22 — Le mécanisme du plus grand premier
==============================================

Observation empirique : Pour k = 3..15, N₀(d) = 0 parce qu'il existe un premier
p | d (toujours le plus grand) tel que N₀(p) = 0.

Question : POURQUOI le plus grand premier p de d exclut-il toujours 0 ?

Hypothèse : Quand p est le plus grand premier de d = 2^S - 3^k, on a
  C = C(S-1, k-1) < p
ce qui force N₀(p) < C/p · p = C, et plus finement, la structure de Horner
combinée à la taille de p empêche d'atteindre 0.

Auteur : Eric Merle (assisté par Claude)
Date : 28 février 2026
"""
import math
from itertools import combinations

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

def ord_mod(g, p):
    if p <= 1 or g % p == 0:
        return 0
    o, x = 1, g % p
    while x != 1:
        x = (x * g) % p
        o += 1
    return o

def corrsum_mod(A, k, m):
    c = 0
    for j in range(k):
        c = (3 * c + pow(2, A[j], m)) % m
    return c

def all_compositions(S, k):
    return [(0,) + rest for rest in combinations(range(1, S), k - 1)]

log2_3 = math.log2(3)

# ============================================================
# SECTION 1 : Le plus grand premier et ses propriétés
# ============================================================
print("=" * 90)
print("SECTION 1 : Plus grand premier de d — C/p et ordre de 2")
print("=" * 90)
print(f"{'k':>3} {'S':>3} {'d':>12} {'p_max':>10} {'C':>10} {'C/p':>8} "
      f"{'ω₂':>5} {'S/ω':>6} {'N₀':>6} {'3∈⟨2⟩':>6}")
print("-" * 90)

for k in range(2, 25):
    S = math.ceil(k * log2_3)
    d = (1 << S) - 3**k
    if d <= 0:
        continue

    C = math.comb(S - 1, k - 1)
    primes = prime_factors(d)
    p_max = primes[-1]

    omega2 = ord_mod(2, p_max)
    omega3 = ord_mod(3, p_max)

    # 3 ∈ ⟨2⟩ mod p_max ?
    x, in_2 = 1, False
    for i in range(omega2):
        if x == 3 % p_max:
            in_2 = True
            break
        x = (x * 2) % p_max

    n0 = "?"
    if C <= 2_000_000:
        comps = all_compositions(S, k)
        n0 = sum(1 for A in comps if corrsum_mod(A, k, p_max) == 0)

    print(f"{k:3d} {S:3d} {d:12d} {p_max:10d} {C:10d} {C/p_max:8.4f} "
          f"{omega2:5d} {S/omega2:6.2f} {str(n0):>6} {'oui' if in_2 else 'NON':>6}")

# ============================================================
# SECTION 2 : Quand C < p_max — l'argument pigeonhole
# ============================================================
print("\n" + "=" * 90)
print("SECTION 2 : Analyse C < p_max (argument de comptage)")
print("=" * 90)

for k in range(2, 25):
    S = math.ceil(k * log2_3)
    d = (1 << S) - 3**k
    if d <= 0:
        continue

    C = math.comb(S - 1, k - 1)
    primes = prime_factors(d)
    p_max = primes[-1]

    if C < p_max:
        # Si C < p, alors corrSum mod p prend au plus C valeurs parmi p possibles
        # Donc il manque au moins p - C résidus
        # Question : 0 est-il parmi les absents ?
        status = "C < p"
        missing = p_max - C
        frac = C / p_max
    else:
        status = "C ≥ p"
        missing = 0
        frac = C / p_max

    n0 = "?"
    if C <= 2_000_000:
        comps = all_compositions(S, k)
        n0 = sum(1 for A in comps if corrsum_mod(A, k, p_max) == 0)
        image_size = len(set(corrsum_mod(A, k, p_max) for A in comps))
    else:
        image_size = "?"

    if C < p_max or C <= 2_000_000:
        print(f"k={k:2d}: p_max={p_max:>10d}, C={C:>10d}, C/p={frac:.4f}, "
              f"|Im|={str(image_size):>6}, N₀={str(n0):>6}, {status}")

# ============================================================
# SECTION 3 : Image de corrSum mod p_max — taille vs p
# ============================================================
print("\n" + "=" * 90)
print("SECTION 3 : Taille de l'image Im(corrSum mod p_max)")
print("=" * 90)
print(f"{'k':>3} {'p_max':>10} {'C':>10} {'|Im|':>7} {'|Im|/p':>8} "
      f"{'p-|Im|':>8} {'0∈Im':>5}")
print("-" * 70)

for k in range(2, 17):
    S = math.ceil(k * log2_3)
    d = (1 << S) - 3**k
    if d <= 0:
        continue

    C = math.comb(S - 1, k - 1)
    primes = prime_factors(d)
    p_max = primes[-1]

    if C > 2_000_000:
        continue

    comps = all_compositions(S, k)
    image = set(corrsum_mod(A, k, p_max) for A in comps)
    im_size = len(image)
    zero_in = 0 in image

    print(f"{k:3d} {p_max:10d} {C:10d} {im_size:7d} {im_size/p_max:8.4f} "
          f"{p_max - im_size:8d} {'oui' if zero_in else 'NON':>5}")

# ============================================================
# SECTION 4 : L'image pour les PETITS premiers — est-elle toujours surjective ?
# ============================================================
print("\n" + "=" * 90)
print("SECTION 4 : Image de corrSum mod petits premiers (p | d, p ≠ p_max)")
print("=" * 90)

for k in range(2, 17):
    S = math.ceil(k * log2_3)
    d = (1 << S) - 3**k
    if d <= 0:
        continue

    C = math.comb(S - 1, k - 1)
    primes = prime_factors(d)

    if C > 2_000_000 or len(primes) < 2:
        continue

    comps = all_compositions(S, k)

    for p in primes[:-1]:  # Tous sauf le plus grand
        image = set(corrsum_mod(A, k, p) for A in comps)
        im_size = len(image)
        zero_in = 0 in image
        n0 = sum(1 for A in comps if corrsum_mod(A, k, p) == 0)
        surj = "SURJ" if im_size == p else f"miss {p - im_size}"

        print(f"k={k:2d}, p={p:>6d}: |Im|={im_size:>5d}/{p}, {surj:>8}, "
              f"0∈Im={'oui' if zero_in else 'NON'}, N₀={n0}")

# ============================================================
# SECTION 5 : Analyse par ordre de 2 — corrélation S/ω et exclusion
# ============================================================
print("\n" + "=" * 90)
print("SECTION 5 : Le ratio S/ω₂(p) comme prédicteur d'exclusion")
print("=" * 90)

print(f"{'k':>3} {'p':>10} {'ω₂':>5} {'S/ω':>8} {'C/p':>8} {'N₀':>7} "
      f"{'N₀=0':>5} {'verdict':>20}")
print("-" * 80)

for k in range(2, 17):
    S = math.ceil(k * log2_3)
    d = (1 << S) - 3**k
    if d <= 0:
        continue

    C = math.comb(S - 1, k - 1)
    primes = prime_factors(d)

    if C > 2_000_000:
        continue

    comps = all_compositions(S, k)

    for p in primes:
        omega = ord_mod(2, p)
        n0 = sum(1 for A in comps if corrsum_mod(A, k, p) == 0)
        ratio_sw = S / omega
        excluded = n0 == 0

        if excluded:
            if ratio_sw < 1:
                verdict = "S<ω → troncature"
            elif C < p:
                verdict = "C<p → pigeonhole"
            else:
                verdict = "structure Horner"
        else:
            verdict = "non exclu"

        print(f"{k:3d} {p:10d} {omega:5d} {ratio_sw:8.3f} {C/p:8.3f} {n0:7d} "
              f"{'OUI' if excluded else 'non':>5} {verdict:>20}")

# ============================================================
# SECTION 6 : Le ratio critique C/d et le déficit entropique
# ============================================================
print("\n" + "=" * 90)
print("SECTION 6 : C/d = f(k) et son évolution asymptotique")
print("=" * 90)

ratios = []
for k in range(2, 100):
    S = math.ceil(k * log2_3)
    d = (1 << S) - 3**k
    if d <= 0:
        continue

    C = math.comb(S - 1, k - 1)
    ratio = C / d if d != 0 else float('inf')

    # Approximation Stirling : C ≈ 2^S / √(2πk·α(1-α)) avec α = k/S ≈ log₂3
    alpha = k / S
    if 0 < alpha < 1:
        h_alpha = -alpha * math.log2(alpha) - (1 - alpha) * math.log2(1 - alpha)
        stirling_approx = 2**(S * h_alpha) / math.sqrt(2 * math.pi * S * alpha * (1 - alpha))
        log_ratio = math.log2(C) - math.log2(d) if d > 0 and C > 0 else 0
    else:
        stirling_approx = 0
        log_ratio = 0

    ratios.append((k, S, d, C, ratio, log_ratio))

    if k <= 30 or k % 10 == 0:
        print(f"k={k:3d}: S={S:3d}, C/d={ratio:.6e}, log₂(C/d)={log_ratio:+8.3f}")

# Régression sur log₂(C/d)
print("\nRégression linéaire sur log₂(C/d) :")
import numpy as np
ks = np.array([r[0] for r in ratios if r[0] >= 5])
logs = np.array([r[5] for r in ratios if r[0] >= 5])
if len(ks) > 2:
    coeffs = np.polyfit(ks, logs, 1)
    print(f"  log₂(C/d) ≈ {coeffs[0]:.6f} · k + {coeffs[1]:.4f}")
    print(f"  Pente = {coeffs[0]:.6f} (attendu ≈ -γ·ln2/ln2 = -γ = {-0.0500:.4f})")
    print(f"  Taux de décroissance de C/d : 2^({coeffs[0]:.4f}·k) = {2**coeffs[0]:.6f}^k")

print("\n✓ Phase 22 mécanisme du plus grand premier terminée.")
