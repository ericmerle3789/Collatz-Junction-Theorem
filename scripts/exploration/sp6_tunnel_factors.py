#!/usr/bin/env python3
"""
GPS Phase 6.3 : Le Tunnel v2 — Version rapide
===============================================
Question PRECISE: les facteurs premiers de d(k) = 2^S - 3^k
ont-ils un ord_p(2) intrinsèquement GRAND ?

Si oui: la convolution marche pour TOUS les facteurs de d(k),
et on n'a pas besoin de Ghost Fish du tout.

Stratégie: factoriser d(k) pour PETIT k uniquement (18-45),
où d(k) reste factorisable rapidement.
"""

from math import ceil, log2, gcd
from sympy import factorint, isprime
from collections import Counter, defaultdict

def S_of_k(k):
    return ceil(k * log2(3))

def fast_ord(a, p):
    """Compute ord_p(a) using p-1 factorization."""
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

print("=" * 70)
print("LE TUNNEL v2: ord_p(2) des facteurs de d(k)")
print("=" * 70)

# =====================================================================
# PART 1: Factor d(k) for small k, collect all primes + their ord_2
# =====================================================================

all_factors = {}  # p -> {ord_2, appears_at_k, ...}
k_factors = {}    # k -> list of (p, e)

print(f"\n{'k':>4} {'S':>4} {'d(k) digits':>12} {'factors':>50}")
print("-" * 75)

for k in range(18, 46):
    S = S_of_k(k)
    d = pow(2, S) - pow(3, k)

    if d <= 0:
        print(f"{k:>4} {S:>4} {'d <= 0':>12}")
        continue

    n_digits = len(str(d))

    # Factor with reasonable limit
    try:
        factors = factorint(d, limit=10**7)
    except Exception:
        factors = {d: 1}

    k_factors[k] = list(factors.items())

    for p, e in factors.items():
        if p > 2 and p not in all_factors:
            ord_2 = fast_ord(2, p)
            all_factors[p] = {'ord_2': ord_2, 'k_list': []}
        if p > 2:
            all_factors[p]['k_list'].append(k)

    factor_str = " × ".join(f"{p}^{e}" if e > 1 else str(p)
                            for p, e in sorted(factors.items()))
    if len(factor_str) > 50:
        factor_str = factor_str[:47] + "..."

    print(f"{k:>4} {S:>4} {n_digits:>12} {factor_str:>50}")

# =====================================================================
# PART 2: Distribution of ord_p(2) among factors
# =====================================================================

print(f"\n{'='*70}")
print("DISTRIBUTION de ord_p(2) parmi les facteurs de d(k), k ∈ [18, 45]")
print("=" * 70)

ord_counts = Counter()
for p, info in all_factors.items():
    if info['ord_2'] is not None:
        ord_counts[info['ord_2']] += 1

print(f"\n{'ord_p(2)':>10} {'# primes':>10} {'primes (échantillon)':>40}")
print("-" * 65)

for ord_val in sorted(ord_counts.keys()):
    primes_with_ord = sorted([p for p, info in all_factors.items()
                              if info['ord_2'] == ord_val])
    sample = str(primes_with_ord[:5])
    if len(primes_with_ord) > 5:
        sample += f" ...({len(primes_with_ord)} total)"
    print(f"{ord_val:>10} {ord_counts[ord_val]:>10} {sample:>40}")

# =====================================================================
# PART 3: KEY QUESTION — any factor with ord_p(2) ≤ 60?
# =====================================================================

print(f"\n{'='*70}")
print("QUESTION CLEF: facteurs avec ord_p(2) ≤ 60 ?")
print("=" * 70)

small_ord_factors = {p: info for p, info in all_factors.items()
                     if info['ord_2'] is not None and info['ord_2'] <= 60}

if small_ord_factors:
    print(f"\n{'p':>15} {'ord_2':>8} {'k où p|d(k)':>30}")
    print("-" * 58)
    for p in sorted(small_ord_factors.keys()):
        info = small_ord_factors[p]
        k_str = str(info['k_list'][:10])
        print(f"{p:>15} {info['ord_2']:>8} {k_str:>30}")

    # Further analysis: which of these are "hard" (would fail convolution)?
    print(f"\n--- Parmi ceux-ci, lesquels FAIL convolution à k=18? ---")
    import numpy as np
    for p in sorted(small_ord_factors.keys()):
        m = small_ord_factors[p]['ord_2']
        if m is None or m < 2:
            continue
        omega = np.exp(2j * np.pi / p)
        orbit = [pow(2, a, p) for a in range(m)]

        max_rho = 0
        for c in range(1, min(p, 500)):  # Sample if p large
            s = sum(omega ** (c * h) for h in orbit)
            max_rho = max(max_rho, abs(s) / m)

        bound_k18 = (p - 1) * max_rho ** 17
        status = "FAIL" if bound_k18 >= 0.041 else "PASS"
        print(f"  p={p}, ord={m}, ρ≈{max_rho:.4f}, "
              f"(p-1)·ρ^17={bound_k18:.2e} → {status}")
else:
    print("\nAUCUN facteur avec ord_p(2) ≤ 60 !")

# =====================================================================
# PART 4: Minimum ord_p(2) observed
# =====================================================================

print(f"\n{'='*70}")
print("STATISTIQUES")
print("=" * 70)

ords = [info['ord_2'] for info in all_factors.values()
        if info['ord_2'] is not None]

if ords:
    print(f"  Nombre de primes distinctes: {len(ords)}")
    print(f"  ord_p(2) minimum: {min(ords)}")
    print(f"  ord_p(2) maximum: {max(ords)}")
    print(f"  ord_p(2) médiane: {sorted(ords)[len(ords)//2]}")
    print(f"  Primes avec ord ≤ 10: {sum(1 for o in ords if o <= 10)}")
    print(f"  Primes avec ord ≤ 30: {sum(1 for o in ords if o <= 30)}")
    print(f"  Primes avec ord ≤ 60: {sum(1 for o in ords if o <= 60)}")

# =====================================================================
# PART 5: Direct test — are any of the 17 HARD primes factors of d(k)?
# =====================================================================

print(f"\n{'='*70}")
print("TEST DIRECT: les 17 primes 'dures' divisent-elles d(k)?")
print("=" * 70)

# The 17 hard primes from Phase 6.1
hard_primes = [
    7, 31, 73, 89, 127, 151, 233, 331, 337, 397,
    683, 1103, 2089, 5419, 8191, 131071, 524287
]

def d_mod_p(k, p):
    S = S_of_k(k)
    return (pow(2, S, p) - pow(3, k, p)) % p

for p in hard_primes:
    appearances = []
    for k in range(18, 200):
        if d_mod_p(k, p) == 0:
            appearances.append(k)
            if len(appearances) >= 3:
                break

    in_factors = p in all_factors
    status = "dans d(k)" if in_factors else "ABSENT de d(k)"
    app_str = str(appearances[:3]) if appearances else "JAMAIS dans [18,200)"
    print(f"  p={p:>8}: {status:>15}, apparitions: {app_str}")

# =====================================================================
# PART 6: The deeper structure — why?
# =====================================================================

print(f"\n{'='*70}")
print("STRUCTURE PROFONDE: pourquoi les facteurs ont grand ord?")
print("=" * 70)

print("""
OBSERVATION: p | d(k) ⟹ 2^S ≡ 3^k (mod p), avec S = ⌈k·log₂3⌉.

Si ord_p(2) = m, alors S mod m DETERMINE 2^S mod p.
Il y a seulement m valeurs possibles pour 2^S mod p.
Et 3^k mod p a ord_p(3) = n valeurs.

Pour que p | d(k), il faut que 2^S mod p = 3^k mod p,
c'est-à-dire que deux séquences quasi-périodiques s'alignent.

La DENSITE de k où ça arrive dépend de gcd(pattern_S, n).

Si m est PETIT (prime "dure"):
  → 2^S mod p a TRES PEU de valeurs distinctes (m valeurs)
  → 3^k mod p a BEAUCOUP de valeurs (n ≈ p/m ou plus)
  → L'ALIGNEMENT est RARE: densité ≈ m/(m·n) = 1/n

Mais surtout: S = ⌈k·log₂3⌉ impose que S parcourt les entiers
à vitesse ≈ 1.585, ce qui COUPLE S et k de manière rigide.
""")

# Verify: for factors with small ord, what is their ord_3?
print("Vérification: ord_p(3) pour les facteurs à petit ord_p(2):")
for p, info in sorted(all_factors.items()):
    if info['ord_2'] is not None and info['ord_2'] <= 30:
        ord_3 = fast_ord(3, p)
        print(f"  p={p}, ord_2={info['ord_2']}, ord_3={ord_3}, "
              f"ratio ord_3/ord_2={ord_3/info['ord_2']:.1f}")

print(f"\n{'='*70}")
print("CONCLUSION DU TUNNEL v2")
print("=" * 70)
