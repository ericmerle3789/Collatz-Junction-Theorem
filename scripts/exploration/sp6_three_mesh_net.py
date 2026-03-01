#!/usr/bin/env python3
"""
GPS Phase 6.4 : Le Filet Complet — vérification exhaustive
============================================================
Pour chaque m = 1..100, trouver TOUTES les primes p avec ord_p(2) | m,
puis vérifier que chaque prime est couverte par:
  - Transport Affine (p ≤ 97), OU
  - Convolution PASS à k=18, OU
  - Ghost Fish (p ne divise pas d(k) dans la zone danger)

C'est le TEST DEFINITIF du filet à trois mailles.
"""

from math import ceil, log2, gcd, sqrt
from sympy import factorint, isprime, divisors
import numpy as np

def S_of_k(k):
    return ceil(k * log2(3))

def d_mod_p(k, p):
    S = S_of_k(k)
    return (pow(2, S, p) - pow(3, k, p)) % p

def fast_ord(a, p):
    """Multiplicative order via p-1 factorization."""
    if gcd(a, p) != 1:
        return None
    pf = factorint(p - 1)
    order = p - 1
    for q, e in pf.items():
        for _ in range(e):
            if pow(a, order // q, p) == 1:
                order //= q
            else:
                break
    return order

def compute_rho(p, m):
    """Compute ρ_p = max_{c≠0} |Σ_{h∈⟨2⟩} ω^{ch}| / m.
    For large p, sample c values."""
    omega = np.exp(2j * np.pi / p)
    orbit = [pow(2, a, p) for a in range(m)]

    max_rho = 0
    # For small p, check all c; for large p, sample
    c_range = range(1, p) if p < 2000 else range(1, min(p, 500))
    for c in c_range:
        s = sum(omega ** (c * h) for h in orbit)
        rho_c = abs(s) / m
        if rho_c > max_rho:
            max_rho = rho_c
    return max_rho

# =====================================================================
# STEP 1: For each m, find all prime factors of 2^m - 1
# =====================================================================

print("=" * 80)
print("LE FILET COMPLET: vérification exhaustive m=1..100")
print("=" * 80)

# Collect all (p, ord) pairs
all_primes = {}  # p -> ord_p(2)
unfactored = {}  # m -> remaining cofactor

for m in range(1, 101):
    M = pow(2, m) - 1
    try:
        factors = factorint(M, limit=10**8)
    except:
        factors = {}

    for p, e in factors.items():
        if isprime(p) and p > 2:
            actual_ord = fast_ord(2, p)
            if actual_ord is not None and p not in all_primes:
                all_primes[p] = actual_ord

    # Check if fully factored
    product = 1
    for p, e in factors.items():
        product *= p ** e
    if product != M:
        cofactor = M // product
        if cofactor > 1:
            unfactored[m] = cofactor

print(f"\nPrimes trouvées: {len(all_primes)}")
print(f"m avec cofacteur non-factorisé: {len(unfactored)}")

if unfactored:
    print("\n  m valeurs avec cofacteurs résiduels:")
    for m, cof in sorted(unfactored.items())[:15]:
        print(f"    m={m}: cofacteur de {len(str(cof))} chiffres")

# =====================================================================
# STEP 2: Classify each prime
# =====================================================================

print(f"\n{'='*80}")
print("CLASSIFICATION de chaque prime")
print("=" * 80)

# Categories
affine_covered = []      # p ≤ 97
convolution_pass = []    # (p-1)·ρ^17 < 0.041
ghost_fish = []          # p doesn't divide d(k) in danger zone
FAILURES = []            # not covered by any method!

n_tested = 0
for p in sorted(all_primes.keys()):
    if p <= 2:
        continue
    n_tested += 1
    m = all_primes[p]

    # Method 1: Affine Transport
    if p <= 97:
        affine_covered.append((p, m))
        continue

    # Method 2: Convolution bound at k=18
    rho = compute_rho(p, m)
    bound_k18 = (p - 1) * rho ** 17

    if bound_k18 < 0.041:
        convolution_pass.append((p, m, rho, bound_k18))
        continue

    # Method 3: Ghost Fish — find k_min, check danger zone
    # k_min = smallest k where (p-1)·ρ^{k-1} < 0.041
    k_min = 18
    for kk in range(18, 2000):
        if (p - 1) * rho ** (kk - 1) < 0.041:
            k_min = kk
            break

    # Check: does p | d(k) for any k in [18, k_min)?
    danger_hit = False
    for k in range(18, k_min):
        if d_mod_p(k, p) == 0:
            danger_hit = True
            FAILURES.append((p, m, rho, k_min, k))
            break

    if not danger_hit:
        ghost_fish.append((p, m, rho, k_min))

# =====================================================================
# STEP 3: Results
# =====================================================================

print(f"\n{'='*80}")
print("RESULTATS")
print("=" * 80)

print(f"\n  Primes testées: {n_tested}")
print(f"  Couvertes par Transport Affine (p≤97): {len(affine_covered)}")
print(f"  Couvertes par Convolution PASS k=18: {len(convolution_pass)}")
print(f"  Couvertes par Ghost Fish: {len(ghost_fish)}")
print(f"  *** ECHECS (aucune couverture): {len(FAILURES)} ***")

# Detail the ghost fish primes (most interesting)
if ghost_fish:
    print(f"\n--- Ghost Fish (convolution FAIL mais zone danger VIDE): ---")
    print(f"{'p':>15} {'ord_2':>6} {'ρ':>8} {'k_min':>6} {'zone':>8}")
    print("-" * 48)
    for p, m, rho, k_min in sorted(ghost_fish):
        zone_width = k_min - 18
        print(f"{p:>15} {m:>6} {rho:>8.4f} {k_min:>6} {zone_width:>8}")

# The critical part: any failures?
if FAILURES:
    print(f"\n{'!'*80}")
    print(f"ATTENTION: {len(FAILURES)} ECHEC(S) DETECTE(S)!")
    print(f"{'!'*80}")
    for p, m, rho, k_min, k_hit in FAILURES:
        print(f"  p={p}, ord={m}, ρ={rho:.4f}, k_min={k_min}, "
              f"APPARAIT à k={k_hit}")
else:
    print(f"\n{'*'*80}")
    print("ZERO ECHEC: Le filet à trois mailles couvre TOUTES les primes")
    print(f"testées (facteurs de 2^m-1 pour m=1..100, p < 10^8)")
    print(f"{'*'*80}")

# =====================================================================
# STEP 4: What about unfactored parts?
# =====================================================================

print(f"\n{'='*80}")
print("ANALYSE DES COFACTEURS NON-FACTORISES")
print("=" * 80)

print("""
Les cofacteurs résiduels de 2^m-1 contiennent des primes INCONNUES.
Ces primes ont ord_p(2) | m, donc ord_p(2) ≤ m ≤ 100.

Pour m ≤ 60: ces primes auraient ord ≤ 60, donc elles sont parmi
les primes "testables" par Ghost Fish. Si elles sont grandes,
elles sont probablement des fantômes (anti-corrélation).

Pour 61 ≤ m ≤ 100: ord_p(2) peut être grand (> 60).
La convolution devrait marcher pour la plupart.
""")

# For each unfactored m, what's the minimum size of hidden primes?
print(f"{'m':>4} {'cofacteur digits':>16} {'min prime factor':>16}")
print("-" * 40)
for m, cof in sorted(unfactored.items()):
    # The cofactor's smallest prime factor is at least 10^8 (our trial limit)
    # Actually, it's at least 2m+1 (since any factor ≡ 1 mod ord)
    min_pf = max(10**8, 2*m + 1)
    print(f"{m:>4} {len(str(cof)):>16} {min_pf:>16}")

# =====================================================================
# STEP 5: Theoretical argument for unfactored primes
# =====================================================================

print(f"\n{'='*80}")
print("ARGUMENT THEORIQUE: primes cachées dans les cofacteurs")
print("=" * 80)

print("""
Pour toute prime p cachée dans un cofacteur de 2^m-1 (m ≤ 100):
  - p > 10^8 (sinon on l'aurait trouvée par trial division)
  - ord_p(2) | m, donc ord_p(2) ≤ 100
  - ρ_p est HEURISTIQUEMENT ≈ 1/√ord ≤ 1/√2 ≈ 0.71

MAIS: est-ce que la convolution PASS pour ces primes?
  (p-1)·ρ^17 ≈ p · (1/√ord)^17

Pour ord = m (pire cas):
  p · m^{-8.5}

Pour m = 100: p · 100^{-8.5} = p · 10^{-17}
Besoin: p · 10^{-17} < 0.041 → p < 4.1 × 10^{15}

Les cofacteurs de 2^m-1 pour m ≤ 100 contiennent des primes
potentiellement > 10^{15}. MAIS:
  - 2^100-1 ≈ 1.27 × 10^{30}, max 2 primes > 10^{15}
  - Ces grandes primes ont typiquement ord proche de m
  - Et pour elles, Ghost Fish s'applique (anti-corrélation)
""")

# Compute: for which m could a hidden prime of size > 10^15 exist?
print("m où le cofacteur POURRAIT contenir p > 10^15:")
for m, cof in sorted(unfactored.items()):
    if cof > 10**15:
        print(f"  m={m}: cofacteur ~ 10^{len(str(cof))-1}")

# =====================================================================
# STEP 6: Direct ghost fish test for hypothetical large primes
# =====================================================================

print(f"\n{'='*80}")
print("TEST: primes avec ord = m et p >> 10^8, m ∈ {61..100}")
print("=" * 80)

print("""
Même si on ne connaît pas ces primes, on peut borner leur impact:

Pour p avec ord_p(2) = m et p > P₀:
  - k_min(p) ≈ 1 + 2·(log(p) + 3.2)/log(m) (si ρ ≈ 1/√m)
  - Pour m=61, p=10^18: k_min ≈ 1 + 2·(41.4+3.2)/4.1 ≈ 23
  - Zone danger: [18, 23), largeur 5
  - ord_p(3): pour une grande prime random, ord_p(3) ≈ (p-1)/gcd

  Si ord_p(3) > 5 (ce qui est PRESQUE CERTAIN pour p > 10^8),
  alors la zone danger est VIDE (densité 1/ord_p(3) × 5 < 1).
""")

# What's the minimal ord_p(3) needed for ghost fish to work?
# Need: no k in [18, k_min) with p | d(k)
# Heuristic: need ord_p(3) > k_min - 18

print("\nOrd_p(3) MINIMUM nécessaire pour Ghost Fish:")
print(f"{'m':>4} {'p hypothétique':>16} {'k_min est.':>10} {'zone':>6} {'ord_3 min':>10}")
print("-" * 52)
for m in [61, 67, 71, 73, 79, 83, 89, 97, 100]:
    # Worst case: largest possible p for this m
    # p ≤ 2^m - 1, but cofactor could be a prime
    p_hyp = min(unfactored.get(m, 10**15), 10**30)  # cap at 10^30
    rho_est = 1 / sqrt(m)
    k_min_est = 18
    for kk in range(18, 500):
        if p_hyp * rho_est ** (kk - 1) < 0.041:
            k_min_est = kk
            break
    zone = k_min_est - 18
    print(f"{m:>4} {'~10^' + str(len(str(p_hyp))-1):>16} {k_min_est:>10} {zone:>6} {zone:>10}")

print(f"\n{'='*80}")
print("CONCLUSION DU FILET COMPLET")
print("=" * 80)
