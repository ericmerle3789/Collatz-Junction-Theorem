#!/usr/bin/env python3
"""
session10f26k_algebraic.py — Algebraic structure exploration
for d(q_n) = 2^{S_n} - 3^{k_n}, targeting n=23, 25, 59

Protocol G-V-R: Generate hypotheses, Verify computationally, Refine.

APPROCHES:
  1. Calcul exact des petits d_n et factorisation
  2. Test des facteurs algebriquement lies contre cibles
  3. Chaines GCD via Theoreme R
  4. Reduction d'exposants (Euclidien sur le reseau CF)
  5. Analyse des classes de residus des facteurs connus
  6. Structure des ordres multiplicatifs
"""
import sys
import time
from mpmath import mp, mpf, log, floor as mpfloor
from sympy import factorint, isprime, gcd as sgcd, nextprime, primitive_root
from sympy.ntheory.factor_ import totient
from sympy.ntheory import n_order

mp.dps = 200

SEPARATOR = "=" * 70

def compute_cf_and_convergents(num_terms=82):
    """CF [a_0; a_1, ...] de log_2(3) et convergents p_n/q_n."""
    x = mp.log(3) / mp.log(2)
    cf = [int(mpfloor(x))]
    p_prev, p_curr = 1, cf[0]
    q_prev, q_curr = 0, 1
    convergents = [(p_curr, q_curr)]
    remainder = x - mpfloor(x)

    for i in range(1, num_terms):
        if remainder < mp.mpf('1e-50'):
            break
        x_new = 1 / remainder
        a_i = int(mpfloor(x_new))
        cf.append(a_i)
        remainder = x_new - a_i
        p_prev, p_curr = p_curr, a_i * p_curr + p_prev
        q_prev, q_curr = q_curr, a_i * q_curr + q_prev
        convergents.append((p_curr, q_curr))

    return cf, convergents


# ================================================================
print(SEPARATOR)
print("EXPLORATION ALGEBRIQUE — Session 10f26k")
print("Cibles: n=23, n=25, n=59 (aucun facteur <= 10^11)")
print(SEPARATOR)
print()

t0 = time.time()
cf, conv = compute_cf_and_convergents(82)
print(f"CF log_2(3) (30 premiers termes): {cf[:30]}")
print(f"Convergents calcules: {len(conv)}")

# Verification cles
print("\nVerification convergents cles:")
checks = {23: (217976794617, 137528045312),
           25: (8573543875303, 5409303924479)}
for n, (ep, eq) in checks.items():
    p_n, q_n = conv[n]
    ok = "OK" if p_n == ep and q_n == eq else "ERREUR"
    print(f"  n={n}: p={p_n}, q={q_n} [{ok}]")

# ================================================================
print(f"\n{SEPARATOR}")
print("PARTIE 1 : Calcul exact des petits d_n (n impair)")
print(SEPARATOR)

exact_d = {}  # n -> d_n (exact)
for n in range(1, 20, 2):
    if n >= len(conv):
        break
    p_n, q_n = conv[n]
    if p_n > 3000:
        print(f"  n={n}: p_n={p_n} trop grand pour calcul exact direct")
        break
    d_n = 2**p_n - 3**q_n
    exact_d[n] = d_n
    ndigits = len(str(abs(d_n)))
    print(f"\n  n={n}: p_n={p_n}, q_n={q_n}")
    if ndigits < 30:
        print(f"    d_n = {d_n}")
    else:
        print(f"    d_n a {ndigits} chiffres")
    if d_n > 0:
        is_p = isprime(d_n) if ndigits < 50 else "?"
        print(f"    Premier? {is_p}")
    if abs(d_n) > 1 and ndigits < 80:
        try:
            factors = factorint(abs(d_n), limit=10**9)
            print(f"    Facteurs: {factors}")
            remaining = abs(d_n)
            for f, e in factors.items():
                remaining //= f**e
            if remaining > 1:
                print(f"    Cofacteur non factorise: {remaining} ({len(str(remaining))} chiffres)")
        except Exception as e:
            print(f"    Factorisation: {e}")

# Meme chose pour n pair (pour les chaines GCD)
for n in range(2, 14, 2):
    if n >= len(conv):
        break
    p_n, q_n = conv[n]
    if p_n > 3000:
        break
    d_n = 2**p_n - 3**q_n
    exact_d[n] = d_n
    ndigits = len(str(abs(d_n)))
    print(f"\n  n={n} (pair): p_n={p_n}, q_n={q_n}")
    if ndigits < 30:
        print(f"    d_n = {d_n}")
    else:
        print(f"    d_n a {ndigits} chiffres")
    if ndigits < 80:
        try:
            factors = factorint(abs(d_n), limit=10**9)
            print(f"    Facteurs: {factors}")
        except:
            pass

# ================================================================
print(f"\n{SEPARATOR}")
print("PARTIE 2 : Test des facteurs algebriquement lies")
print(SEPARATOR)

# Collecter TOUS les facteurs premiers connus
known_factors = {
    7: 929, 9: 5, 11: 23, 13: 15661, 15: 17, 17: 10499517109,
    19: 5, 21: 79, 27: 23, 29: 13, 31: 47, 33: 151,
    35: 5, 37: 73, 39: 196171, 41: 467, 43: 17218217,
    45: 9343, 47: 13, 49: 136421, 51: 23, 53: 329009,
    55: 5, 57: 11633, 61: 11, 63: 5, 65: 4975245329,
    67: 433, 69: 5, 71: 60853189, 73: 229, 75: 33521,
    77: 1661926991, 79: 172583,
}

all_primes = set()
for p in known_factors.values():
    if isprime(p):
        all_primes.add(p)
    else:
        for f in factorint(p):
            all_primes.add(f)

# Ajouter les facteurs des petits d_n
for n, d_n in exact_d.items():
    if abs(d_n) > 1 and abs(d_n) < 10**80:
        try:
            for f in factorint(abs(d_n), limit=10**9):
                if f > 4:
                    all_primes.add(f)
        except:
            pass

print(f"  {len(all_primes)} facteurs premiers uniques collectes")

# Tester contre cibles
target_data = {
    23: (217976794617, 137528045312),
    25: (8573543875303, 5409303924479),
}

for t_n, (S, k) in target_data.items():
    print(f"\n  Cible n={t_n}: S={S}, k={k}")
    hits = []
    for p in sorted(all_primes):
        if p < 5:
            continue
        v2 = pow(2, S, p)
        v3 = pow(3, k, p)
        if v2 == v3:
            hits.append(p)
            print(f"    *** FACTEUR TROUVE: {p} ***")
    if not hits:
        print(f"    Aucun facteur parmi {len(all_primes)} candidats algebriques")

# ================================================================
print(f"\n{SEPARATOR}")
print("PARTIE 3 : Chaines GCD (Theoreme R)")
print(SEPARATOR)

# GCD entre d_n consecutifs
print("\n  GCD entre d_n consecutifs:")
sorted_ns = sorted(exact_d.keys())
for i in range(len(sorted_ns) - 1):
    n1, n2 = sorted_ns[i], sorted_ns[i+1]
    if n2 == n1 + 1:
        g = sgcd(abs(exact_d[n1]), abs(exact_d[n2]))
        mark = " *** COMMUN ***" if g > 1 else ""
        print(f"    gcd(|d_{n1}|, |d_{n2}|) = {g}{mark}")

# GCD entre d_n impairs non consecutifs
print("\n  GCD entre d_n impairs:")
odd_ns = sorted([n for n in exact_d if n % 2 == 1 and exact_d[n] > 0])
for i in range(len(odd_ns)):
    for j in range(i+1, len(odd_ns)):
        n1, n2 = odd_ns[i], odd_ns[j]
        g = sgcd(abs(exact_d[n1]), abs(exact_d[n2]))
        if g > 1:
            print(f"    gcd(|d_{n1}|, |d_{n2}|) = {g} ***")

# Verification Th.R computationnelle pour petits n
print("\n  Verification Th.R pour petits n:")
for n in range(4, min(max(sorted_ns), 14)):
    if n not in exact_d or n-1 not in exact_d or n-2 not in exact_d:
        continue
    if n >= len(conv):
        continue
    a_n = cf[n]
    q_nm1 = conv[n-1][1]
    d_n = exact_d[n]
    d_nm1 = exact_d[n-1]
    d_nm2 = exact_d[n-2]
    if d_nm1 != 0:
        rhs = pow(3, q_nm1, abs(d_nm1))**a_n * d_nm2 % abs(d_nm1)
        lhs = d_n % abs(d_nm1)
        # Handle signs
        if lhs < 0:
            lhs += abs(d_nm1)
        rhs = rhs % abs(d_nm1)
        ok = "✓" if lhs == rhs else "✗"
        print(f"    n={n}: d_n mod |d_{{n-1}}| = {lhs}, RHS = {rhs} {ok}")

# ================================================================
print(f"\n{SEPARATOR}")
print("PARTIE 4 : Reduction d'exposants pour n=23")
print(SEPARATOR)

S_23, k_23 = 217976794617, 137528045312
print(f"\n  Cible: (S_23, k_23) = ({S_23}, {k_23})")
print(f"  Ratio S/k = {S_23/k_23:.15f}")
print(f"  log_2(3) = {float(mp.log(3)/mp.log(2)):.15f}")

# Reduction par chaque convergent
print("\n  Reductions par convergents individuels:")
reduction_candidates = []  # (r_S, r_k, source_n)

for m in range(1, 23):
    if m >= len(conv):
        break
    S_m, k_m = conv[m]
    if S_m == 0 or S_m > S_23:
        continue
    q_div = S_23 // S_m
    r_S = S_23 - q_div * S_m
    r_k = k_23 - q_div * k_m

    print(f"  n={m} (S_m={S_m}, k_m={k_m}): q={q_div}, r_S={r_S}, r_k={r_k}")

    # Si les residus sont petits, calculer et factoriser
    if 0 < r_S < 5000 and abs(r_k) < 3500:
        reduction_candidates.append((r_S, r_k, m))
        if r_k > 0:
            val = 2**r_S - 3**r_k
            ndigits = len(str(abs(val)))
            if ndigits < 100:
                print(f"    2^{r_S} - 3^{r_k} : {ndigits} chiffres")
                if ndigits < 60:
                    try:
                        factors = factorint(abs(val), limit=10**9)
                        print(f"    Facteurs: {factors}")
                        for f in factors:
                            if f > 4 and isprime(f):
                                v2 = pow(2, S_23, f)
                                v3 = pow(3, k_23, f)
                                if v2 == v3:
                                    print(f"    *** FACTEUR {f} DIVISE d_23! ***")
                    except:
                        pass
        elif r_k < 0:
            val = 2**r_S - 3**abs(r_k)
            ndigits = len(str(abs(val)))
            if ndigits < 100:
                print(f"    2^{r_S} - 3^{abs(r_k)} : {ndigits} chiffres")
                # Aussi tester 2^{r_S} * 3^{|r_k|} - 1 ?
                val2 = 2**r_S * 3**abs(r_k) - 1
                print(f"    Alt: 2^{r_S}*3^{abs(r_k)} - 1 : {len(str(abs(val2)))} chiffres")

# Multi-step reduction (Euclide sur le reseau)
print(f"\n  Reduction multi-etapes (Euclide sur le reseau CF):")
S_curr, k_curr = S_23, k_23
for step in range(20):
    # Trouver le meilleur convergent pour reduire
    best_m = None
    best_r = float('inf')
    for m in range(1, len(conv)):
        S_m, k_m = conv[m]
        if S_m == 0 or S_m >= S_curr:
            continue
        q_div = S_curr // S_m
        if q_div == 0:
            continue
        r_S = abs(S_curr - q_div * S_m)
        if r_S < best_r:
            best_r = r_S
            best_m = m

    if best_m is None or best_r >= S_curr:
        break

    S_m, k_m = conv[best_m]
    q_div = S_curr // S_m
    r_S = S_curr - q_div * S_m
    r_k = k_curr - q_div * k_m

    print(f"  Etape {step+1}: par n={best_m} (q={q_div}): ({S_curr}, {k_curr}) -> ({r_S}, {r_k})")
    S_curr, k_curr = abs(r_S), r_k  # Attention aux signes

    if S_curr < 5000:
        print(f"    EXPOSANTS REDUITS! S={S_curr}, k={k_curr}")
        if k_curr > 0 and S_curr > 0 and S_curr < 10000 and k_curr < 7000:
            val = 2**S_curr - 3**k_curr
            ndigits = len(str(abs(val)))
            print(f"    2^{S_curr} - 3^{k_curr} : {ndigits} chiffres")
            if ndigits < 60:
                try:
                    factors = factorint(abs(val), limit=10**9)
                    print(f"    Facteurs: {factors}")
                    for f in factors:
                        if f > 4 and isprime(f):
                            v2 = pow(2, S_23, f)
                            v3 = pow(3, k_23, f)
                            if v2 == v3:
                                print(f"    *** FACTEUR {f} DIVISE d_23! ***")
                except:
                    print(f"    Factorisation lente...")
        break

# ================================================================
print(f"\n{SEPARATOR}")
print("PARTIE 5 : Reduction d'exposants pour n=25")
print(SEPARATOR)

S_25, k_25 = 8573543875303, 5409303924479
print(f"\n  Cible: (S_25, k_25) = ({S_25}, {k_25})")

S_curr, k_curr = S_25, k_25
for step in range(20):
    best_m = None
    best_r = float('inf')
    for m in range(1, len(conv)):
        S_m, k_m = conv[m]
        if S_m == 0 or S_m >= S_curr:
            continue
        q_div = S_curr // S_m
        if q_div == 0:
            continue
        r_S = abs(S_curr - q_div * S_m)
        if r_S < best_r:
            best_r = r_S
            best_m = m
    if best_m is None or best_r >= S_curr:
        break
    S_m, k_m = conv[best_m]
    q_div = S_curr // S_m
    r_S = S_curr - q_div * S_m
    r_k = k_curr - q_div * k_m
    print(f"  Etape {step+1}: par n={best_m} (q={q_div}): ({S_curr}, {k_curr}) -> ({r_S}, {r_k})")
    S_curr, k_curr = abs(r_S), r_k
    if S_curr < 5000:
        print(f"    EXPOSANTS REDUITS! S={S_curr}, k={k_curr}")
        if k_curr > 0 and S_curr > 0 and S_curr < 10000 and k_curr < 7000:
            val = 2**S_curr - 3**k_curr
            ndigits = len(str(abs(val)))
            print(f"    2^{S_curr} - 3^{k_curr} : {ndigits} chiffres")
            if ndigits < 60:
                try:
                    factors = factorint(abs(val), limit=10**9)
                    print(f"    Facteurs: {factors}")
                    for f in factors:
                        if f > 4 and isprime(f):
                            v2 = pow(2, S_25, f)
                            v3 = pow(3, k_25, f)
                            if v2 == v3:
                                print(f"    *** FACTEUR {f} DIVISE d_25! ***")
                except:
                    print(f"    Factorisation lente...")
        break

# ================================================================
print(f"\n{SEPARATOR}")
print("PARTIE 6 : Structure des ordres multiplicatifs")
print(SEPARATOR)

print("\n  Pour chaque facteur premier connu p de d_n:")
print(f"  {'n':>3} {'p':>12} {'ord_p(2)':>12} {'ord_p(3)':>12} {'p-1':>12} {'p%12':>5} {'p%24':>5}")
print(f"  {'-'*3} {'-'*12} {'-'*12} {'-'*12} {'-'*12} {'-'*5} {'-'*5}")

ord_data = []
for n in sorted(known_factors.keys()):
    p = known_factors[n]
    if not isprime(p) or p > 10**8:  # skip large primes (ord too slow)
        continue
    try:
        o2 = n_order(2, p)
        o3 = n_order(3, p)
        print(f"  {n:>3} {p:>12} {o2:>12} {o3:>12} {p-1:>12} {p%12:>5} {p%24:>5}")
        ord_data.append((n, p, o2, o3))
    except:
        pass

# Analyse: quel est le ratio o2/o3 par rapport a S_n/k_n?
print("\n  Analyse des ratios ord_p(2)/ord_p(3) vs S_n/k_n:")
for n, p, o2, o3 in ord_data:
    if n >= len(conv):
        continue
    S_n, k_n = conv[n]
    ratio_SK = S_n / k_n
    ratio_ord = o2 / o3 if o3 > 0 else 0
    # S_n mod o2 et k_n mod o3
    S_mod = S_n % o2
    k_mod = k_n % o3
    print(f"  n={n}: S/k={ratio_SK:.6f}, o2/o3={ratio_ord:.6f}, "
          f"S mod o2 = {S_mod}, k mod o3 = {k_mod}")

# Analyse des classes de congruence des facteurs
print("\n  Distribution des facteurs par classe mod 12:")
from collections import Counter
mod12_dist = Counter()
for p in known_factors.values():
    if isprime(p) and p > 5:
        mod12_dist[p % 12] += 1
for cls in sorted(mod12_dist.keys()):
    print(f"    p ≡ {cls} (mod 12): {mod12_dist[cls]} facteurs")

# ================================================================
print(f"\n{SEPARATOR}")
print("PARTIE 7 : Candidats par forme speciale")
print(SEPARATOR)

# Pour p | d_n, on a 2^S ≡ 3^k (mod p).
# Donc ord_p(2) | S et ord_p(3) | k (pas necessairement).
# Plus precisement: 2^S = 3^k dans (Z/pZ)*, donc
# S * log_g(2) ≡ k * log_g(3) (mod p-1) pour un generateur g.
#
# Candidats: primes p tels que p-1 a des diviseurs compatibles avec S et k.
# Pour n=23: S=217976794617, k=137528045312
# Factorisons S et k pour comprendre les ordres possibles.

print("\n  Factorisation des exposants S et k des cibles:")
for t_n, (S, k) in target_data.items():
    print(f"\n  n={t_n}: S = {S}")
    try:
        fs = factorint(S, limit=10**8)
        print(f"    Facteurs de S: {fs}")
        remaining = S
        for f, e in fs.items():
            remaining //= f**e
        if remaining > 1:
            print(f"    Cofacteur: {remaining}")
    except:
        print(f"    Factorisation lente")

    print(f"  n={t_n}: k = {k}")
    try:
        fk = factorint(k, limit=10**8)
        print(f"    Facteurs de k: {fk}")
        remaining = k
        for f, e in fk.items():
            remaining //= f**e
        if remaining > 1:
            print(f"    Cofacteur: {remaining}")
    except:
        print(f"    Factorisation lente")

# ================================================================
print(f"\n{SEPARATOR}")
print("PARTIE 8 : Test de propagation Th.R depuis facteurs connus")
print(SEPARATOR)

# Pour chaque facteur connu p de d_m (m impair < 23),
# tester si p | d_{m+2}, d_{m+4}, ..., d_{23}
# Via: pour p | d_n, il suffit que pow(2, S_n, p) == pow(3, k_n, p)

print("\n  Propagation des facteurs le long des convergents impairs:")
for m in sorted(known_factors.keys()):
    if m >= 23:
        continue
    p = known_factors[m]
    if not isprime(p) or p < 5:
        continue
    # Tester si p divise d_{m+2}, d_{m+4}, ..., d_23
    chain = [m]
    for n2 in range(m+2, 24, 2):
        if n2 >= len(conv):
            break
        S_n2, k_n2 = conv[n2]
        v2 = pow(2, S_n2, p)
        v3 = pow(3, k_n2, p)
        if v2 == v3:
            chain.append(n2)
    if len(chain) > 1:
        print(f"  p={p} (de n={m}): divise aussi d_n pour n = {chain}")
        if 23 in chain:
            print(f"  *** p={p} DIVISE d_23 PAR PROPAGATION! ***")
    # Verifier directement d_23
    v2 = pow(2, S_23, p)
    v3 = pow(3, k_23, p)
    if v2 == v3 and 23 not in chain:
        chain.append(23)
        print(f"  p={p} (de n={m}): divise d_23 (pas par chaine continue)")

# ================================================================
total_time = time.time() - t0
print(f"\n{SEPARATOR}")
print(f"TEMPS TOTAL: {total_time:.1f}s")
print(SEPARATOR)
