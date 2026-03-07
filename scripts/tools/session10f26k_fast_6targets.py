#!/usr/bin/env python3
"""
SESSION 10f26k (partie 5) — TEST RAPIDE POUR 6 CONVERGENTS IMPAIRS
===================================================================
Approche optimisee : au lieu du crible segmente Python (LENT),
utiliser directement pow(2,S,p) - pow(3,k,p) pour des primes
generes par test de primalite rapide dans des plages croissantes.

Strategie : pour chaque cible, tester des nombres aleatoires
dans des plages croissantes [10^8, 10^9], [10^9, 10^10], etc.
"""
import math
import time
import sys
import random

sys.set_int_max_str_digits(100000)

print("=" * 72, flush=True)
print("SESSION 10f26k (partie 5) — TEST RAPIDE 6 CIBLES", flush=True)
print("=" * 72, flush=True)

# CF haute precision
from mpmath import mp, mpf, log, floor
mp.dps = 200
log2_3_precise = log(3) / log(2)

x = log2_3_precise
cf = []
convs = []
p_prev, p_curr = mpf(1), None
q_prev, q_curr = mpf(0), None
for i in range(80):
    a = int(floor(x))
    cf.append(a)
    if i == 0:
        p_curr = mpf(a)
        q_curr = mpf(1)
    else:
        p_next = a * p_curr + p_prev
        q_next = a * q_curr + q_prev
        p_prev, p_curr = p_curr, p_next
        q_prev, q_curr = q_curr, q_next
    convs.append((i, int(p_curr), int(q_curr), a))
    frac = x - a
    if frac < mpf(10) ** (-150):
        break
    x = 1 / frac

# 6 cibles impaires non resolues
targets = []
for idx in [17, 23, 25, 59, 65, 77]:
    _, pn, qn, _ = convs[idx]
    delta = float(mpf(pn) - qn * log2_3_precise)
    targets.append((idx, pn, qn, delta))

print(f"\n6 cibles :", flush=True)
for idx, pn, qn, delta in targets:
    n_digits = int(qn * math.log10(3))
    print(f"  n={idx:>2}: q_n={qn}, d a ~{n_digits} chiffres, delta={delta:.3e}", flush=True)

# Miller-Rabin rapide
def is_prime_mr(n, k=10):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0: return False
    s, d = 0, n - 1
    while d % 2 == 0:
        s += 1
        d //= 2
    for _ in range(k):
        a = random.randrange(2, n - 1) if n > 4 else 2
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True

# Sieve classique pour les premiers <= 10^8
print(f"\n  Crible <= 10^8...", flush=True)
t0 = time.time()

def sieve(n):
    s = bytearray(b'\x01') * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n**0.5) + 1):
        if s[i]:
            s[i*i::i] = b'\x00' * len(s[i*i::i])
    return [i for i in range(2, n + 1) if s[i]]

primes_100M = sieve(100_000_000)
print(f"  {len(primes_100M)} premiers ({time.time()-t0:.1f}s)", flush=True)

# Phase 1 : test rapide avec premiers <= 10^8
print(f"\n--- PHASE 1 : PREMIERS <= 10^8 ---\n", flush=True)
resolved = {}

for idx, pn, qn, delta in targets:
    t0 = time.time()
    found = None
    for p in primes_100M:
        d_mod_p = (pow(2, pn, p) - pow(3, qn, p)) % p
        if d_mod_p == 0:
            found = p
            break
    dt = time.time() - t0
    if found:
        resolved[idx] = found
        print(f"  n={idx}: COMPOSITE, facteur {found} ({dt:.1f}s)", flush=True)
    else:
        print(f"  n={idx}: pas de facteur <= 10^8 ({dt:.1f}s)", flush=True)

# Phase 2 : pour les non resolus, test par batches de primes aleatoires
remaining = [(idx, pn, qn, delta) for idx, pn, qn, delta in targets
             if idx not in resolved]

if remaining:
    print(f"\n--- PHASE 2 : PRIMES ALEATOIRES [10^8, 10^12] ---\n", flush=True)
    print(f"  {len(remaining)} cibles restantes", flush=True)

    # Pour chaque plage, generer des nombres impairs aleatoires et tester
    ranges = [
        (10**8, 10**9, 200000),
        (10**9, 10**10, 200000),
        (10**10, 10**11, 100000),
        (10**11, 10**12, 100000),
    ]

    random.seed(42)

    for lo, hi, n_tests in ranges:
        still_remaining = [(idx, pn, qn, delta) for idx, pn, qn, delta in remaining
                          if idx not in resolved]
        if not still_remaining:
            break

        print(f"\n  Plage [{lo:.0e}, {hi:.0e}], {n_tests} candidats...", flush=True)
        t0 = time.time()

        primes_found = 0
        for _ in range(n_tests):
            # Generer un nombre impair aleatoire
            candidate = random.randrange(lo | 1, hi, 2)
            if not is_prime_mr(candidate):
                continue
            primes_found += 1

            for idx, pn, qn, delta in still_remaining:
                if idx in resolved:
                    continue
                d_mod_p = (pow(2, pn, candidate) - pow(3, qn, candidate)) % candidate
                if d_mod_p == 0:
                    resolved[idx] = candidate
                    elapsed = time.time() - t0
                    print(f"    n={idx}: COMPOSITE ! facteur {candidate} ({elapsed:.1f}s, "
                          f"apres {primes_found} premiers testes)", flush=True)

        dt = time.time() - t0
        n_remaining = len(still_remaining) - sum(1 for i,_,_,_ in still_remaining if i in resolved)
        print(f"    {primes_found} premiers testes en {dt:.1f}s, "
              f"{n_remaining} cibles restantes", flush=True)

# Phase 3 : approche systematique pour les "petits" cas non resolus
remaining_final = [(idx, pn, qn, delta) for idx, pn, qn, delta in targets
                   if idx not in resolved]

if remaining_final:
    # Pour n=17 (q ~ 1.7*10^8, d ~ 82M digits) : le plus petit facteur
    # pourrait etre > 10^12. Essayons primes dans [10^12, 10^15]
    print(f"\n--- PHASE 3 : PRIMES TRES GRANDS [10^12, 10^15] ---\n", flush=True)
    print(f"  {len(remaining_final)} cibles restantes", flush=True)

    ranges_big = [
        (10**12, 10**13, 50000),
        (10**13, 10**14, 50000),
        (10**14, 10**15, 50000),
    ]

    for lo, hi, n_tests in ranges_big:
        still_remaining = [(idx, pn, qn, delta) for idx, pn, qn, delta in remaining_final
                          if idx not in resolved]
        if not still_remaining:
            break

        print(f"\n  Plage [{lo:.0e}, {hi:.0e}], {n_tests} candidats...", flush=True)
        t0 = time.time()

        primes_found = 0
        for _ in range(n_tests):
            candidate = random.randrange(lo | 1, hi, 2)
            if not is_prime_mr(candidate):
                continue
            primes_found += 1

            for idx, pn, qn, delta in still_remaining:
                if idx in resolved:
                    continue
                d_mod_p = (pow(2, pn, candidate) - pow(3, qn, candidate)) % candidate
                if d_mod_p == 0:
                    resolved[idx] = candidate
                    elapsed = time.time() - t0
                    print(f"    n={idx}: COMPOSITE ! facteur {candidate} ({elapsed:.1f}s)", flush=True)

        dt = time.time() - t0
        n_remaining = len(still_remaining) - sum(1 for i,_,_,_ in still_remaining if i in resolved)
        print(f"    {primes_found} premiers testes en {dt:.1f}s, "
              f"{n_remaining} cibles restantes", flush=True)

# === BILAN ===
print(f"\n{'='*72}", flush=True)
print(f"BILAN SESSION 10f26k (partie 5)", flush=True)
print(f"{'='*72}", flush=True)

all_odd = list(range(7, 80, 2))
n_resolved_total = 0
n_unresolved = 0

# Facteurs connus des sessions precedentes
known = {
    7: 929, 9: 5, 11: 23, 13: 15661, 15: 17, 19: 5, 21: 79,
    27: 23, 29: 13, 31: 47, 33: 151, 35: 5, 37: 73, 39: 196171,
    41: 467, 43: 17218217, 45: 9343, 47: 13, 49: 136421, 51: 23,
    53: 329009, 55: 5, 57: 11633, 59: 0, 61: 11, 63: 5, 65: 0,
    67: 433, 69: 5, 71: 60853189, 73: 229, 75: 33521, 77: 0, 79: 172583,
}
known.update(resolved)

print(f"\nTABLEAU CONVERGENTS IMPAIRS (n=7..79) :", flush=True)
print(f"  {'n':>3} {'q_n':>25} {'delta':>12} {'Facteur':>15} {'Status':>10}", flush=True)
print(f"  {'-'*70}", flush=True)

for n_idx in all_odd:
    if n_idx >= len(convs):
        continue
    _, pn, qn, _ = convs[n_idx]
    delta = float(mpf(pn) - qn * log2_3_precise)
    if delta > 0.015:
        continue

    f = known.get(n_idx, 0)
    if f > 0:
        status = "COMPOSITE"
        n_resolved_total += 1
    else:
        status = "NON RESOLU"
        n_unresolved += 1

    f_str = str(f) if f > 0 else "?"
    q_str = str(qn) if qn < 10**20 else f"{qn:.3e}"
    print(f"  {n_idx:>3} {q_str:>25} {delta:>12.3e} {f_str:>15} {status:>10}", flush=True)

print(f"\n  Score convergents impairs : {n_resolved_total}/{n_resolved_total+n_unresolved} COMPOSITES", flush=True)

if n_unresolved == 0:
    print(f"\n  *** TOUS COMPOSITES *** Gap G2c ferme computationnellement.", flush=True)
else:
    print(f"\n  {n_unresolved} cas non resolus.", flush=True)
    print(f"  Rappel : convergents PAIRS ont delta~1, NON dangereux (Th.S).", flush=True)

print(f"\n{'='*72}", flush=True)
print(f"FIN SESSION 10f26k (partie 5)", flush=True)
print(f"{'='*72}", flush=True)
