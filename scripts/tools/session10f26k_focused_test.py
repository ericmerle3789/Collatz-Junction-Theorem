#!/usr/bin/env python3
"""
SESSION 10f26k (partie 4) — TEST FOCALISE SUR 6 CONVERGENTS IMPAIRS
====================================================================
CORRECTION CRITIQUE : seuls les convergents d'indice IMPAIR sont dangereux.
  - n pair : p_n/q_n < log_2(3), donc S = p_n + 1, delta ~ 1. NON DANGEREUX.
  - n impair : p_n/q_n > log_2(3), donc S = p_n, delta = petit. DANGEREUX.

6 cas non resolus (impairs, pas de facteur <= 100M) :
  n=17 (q=171928773), n=23 (q=137528045312), n=25 (q=5409303924479)
  n=59 (q~3.8e29), n=65 (q~5.8e32), n=77 (q~3.7e37)

Methode : test modulaire d mod p = (2^{p_n} mod p - 3^{q_n} mod p) % p
avec crible segmente de 10^8 a 10^10.
"""
import math
import time
import sys

sys.set_int_max_str_digits(100000)

print("=" * 72, flush=True)
print("SESSION 10f26k (partie 4) — TEST FOCALISE", flush=True)
print("=" * 72, flush=True)

# === CF haute precision ===
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

# === Correction : delta physique ===
print("\n--- CORRECTION : DELTA PHYSIQUE vs DELTA CF ---\n", flush=True)
print(f"Pour CF de log_2(3) : convergent n pair => p_n/q_n < log_2(3)", flush=True)
print(f"  => S = p_n + 1, delta_phys = 1 - |delta_CF| ~ 1  (NON DANGEREUX)", flush=True)
print(f"  Convergent n impair => p_n/q_n > log_2(3)", flush=True)
print(f"  => S = p_n, delta_phys = delta_CF  (POTENTIELLEMENT DANGEREUX)\n", flush=True)

# Verifier la correction sur les 6 premiers convergents connus
print(f"Verification sur convergents connus :", flush=True)
for idx in [7, 9, 10, 11, 12, 13]:
    _, pn, qn, an = convs[idx]
    delta_cf = float(mpf(pn) - qn * log2_3_precise)
    if idx % 2 == 1:  # impair
        S = pn
        delta_phys = delta_cf
    else:  # pair
        S = pn + 1
        delta_phys = float(mpf(S) - qn * log2_3_precise)
    parity = "IMPAIR" if idx % 2 == 1 else "PAIR"
    danger = "DANGEREUX" if delta_phys < 0.015 else "OK (delta~1)"
    print(f"  n={idx:>2} ({parity:>6}): delta_CF={delta_cf:>12.3e}, "
          f"S={S}, delta_phys={delta_phys:.4f} -> {danger}", flush=True)

# === 6 cas impairs non resolus ===
targets = []
for idx in [17, 23, 25, 59, 65, 77]:
    _, pn, qn, _ = convs[idx]
    delta = float(mpf(pn) - qn * log2_3_precise)
    targets.append((idx, pn, qn, delta))

print(f"\n--- 6 CIBLES (convergents impairs, delta < 0.015) ---\n", flush=True)
for idx, pn, qn, delta in targets:
    print(f"  n={idx:>2}: q_n={qn}, S=p_n={pn}, delta={delta:.3e}", flush=True)

# === Crible segmente ===
def sieve(n):
    s = bytearray(b'\x01') * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n**0.5) + 1):
        if s[i]:
            s[i*i::i] = b'\x00' * len(s[i*i::i])
    return [i for i in range(2, n + 1) if s[i]]

def segmented_sieve_primes(lo, hi, small_primes):
    """Yield primes in [lo, hi]."""
    size = hi - lo + 1
    is_prime = bytearray(b'\x01') * size
    for p in small_primes:
        start = max(p * p, ((lo + p - 1) // p) * p)
        for j in range(start - lo, size, p):
            is_prime[j] = 0
    for i in range(size):
        if is_prime[i] and (lo + i) > 1:
            yield lo + i

# Phase 1 : petits premiers de base
print(f"\n  Crible de base...", flush=True)
small_primes = sieve(100000)  # sqrt(10^10) ~ 100000
print(f"  {len(small_primes)} premiers <= 100000", flush=True)

# Phase 2 : test par blocs de 10^8 a 10^10
print(f"\n--- TEST MODULAIRE : PRIMES [10^8, 10^10] ---\n", flush=True)

BLOCK = 50_000_000  # blocs de 50M pour vitesse
resolved = {}
t_global = time.time()

for block_start in range(100_000_000, 10_000_000_000, BLOCK):
    block_end = min(block_start + BLOCK - 1, 10_000_000_000)

    remaining = [(idx, pn, qn, delta) for idx, pn, qn, delta in targets
                 if idx not in resolved]
    if not remaining:
        break

    # Generer les premiers dans ce bloc
    primes_block = list(segmented_sieve_primes(block_start, block_end, small_primes))

    for idx, pn, qn, delta in remaining:
        for p in primes_block:
            d_mod_p = (pow(2, pn, p) - pow(3, qn, p)) % p
            if d_mod_p == 0:
                resolved[idx] = p
                elapsed = time.time() - t_global
                print(f"  n={idx:>2}: COMPOSITE ! facteur {p:>12,} "
                      f"(delta={delta:.3e}, t={elapsed:.0f}s)", flush=True)
                break

    # Progress tous les 500M
    if (block_start - 100_000_000) % 500_000_000 == 0 and block_start > 100_000_000:
        n_remaining = len(targets) - len(resolved)
        elapsed = time.time() - t_global
        print(f"  ... {block_end/1e9:.1f}G atteint — {n_remaining}/6 restants "
              f"({elapsed:.0f}s)", flush=True)
        if n_remaining == 0:
            break

# === BILAN ===
print(f"\n{'='*72}", flush=True)
print(f"BILAN FINAL — CONVERGENTS IMPAIRS", flush=True)
print(f"{'='*72}", flush=True)

elapsed = time.time() - t_global

# Compter tous les convergents impairs resolus (des sessions precedentes + maintenant)
all_odd_indices = list(range(7, 80, 2))  # n=7,9,11,...,79
print(f"\nConvergents impairs (n=7..79, delta < 0.015) :", flush=True)

# Resultats des sessions precedentes (du part 2)
prev_resolved = {
    7: 929, 9: 5, 11: 23, 13: 15661, 15: 17, 19: 5, 21: 79, 27: 23,
    29: 13, 31: 47, 33: 151, 35: 5, 37: 73, 39: 196171, 41: 467,
    43: 17218217, 45: 9343, 47: 13, 49: 136421, 51: 23, 53: 329009,
    55: 5, 57: 11633, 61: 11, 63: 5, 67: 433, 69: 5, 71: 60853189,
    73: 229, 75: 33521, 79: 172583,
    # Also from part 2 even convergents correctly tested:
    14: 55109, 16: 197, 18: 7, 22: 23, 24: 11, 26: 2774599,
    28: 1481, 32: 11, 34: 27008411, 38: 59, 44: 109, 48: 31,
    50: 37, 54: 181, 56: 4919, 58: 29, 60: 103, 62: 7,
    64: 231589, 66: 1747, 68: 73, 72: 7, 74: 0, 76: 37, 78: 263,
    # from 59: not resolved
}

# Merge new results
all_resolved = {**prev_resolved, **resolved}

n_odd_total = 0
n_odd_resolved = 0
n_odd_unresolved = 0

for n_idx in all_odd_indices:
    if n_idx >= len(convs):
        continue
    _, pn, qn, _ = convs[n_idx]
    delta = float(mpf(pn) - qn * log2_3_precise)
    if delta > 0.015:
        continue  # pas dangereux

    n_odd_total += 1
    if n_idx in all_resolved and all_resolved[n_idx] > 0:
        f = all_resolved[n_idx]
        print(f"  n={n_idx:>2}: COMPOSITE (facteur {f:>12}), delta={delta:.3e}", flush=True)
        n_odd_resolved += 1
    else:
        print(f"  n={n_idx:>2}: NON RESOLU, delta={delta:.3e}", flush=True)
        n_odd_unresolved += 1

print(f"\n  Score : {n_odd_resolved}/{n_odd_total} convergents impairs COMPOSITES", flush=True)
print(f"  Non resolus : {n_odd_unresolved}", flush=True)
print(f"  Temps total : {elapsed:.0f}s", flush=True)

if n_odd_unresolved == 0:
    print(f"\n  *** TOUS LES CONVERGENTS IMPAIRS CONFIRMES COMPOSITES ***", flush=True)
    print(f"  => Gap G2c FERME computationnellement pour 80 termes CF.", flush=True)
else:
    print(f"\n  DIAGNOSTIC :", flush=True)
    print(f"    Les facteurs sont > 10^10 pour ces cas.", flush=True)
    print(f"    Heuristiquement, d(q_n) a ~q_n*log10(3) chiffres.", flush=True)
    print(f"    Pr[d premier] ~ 1/(q_n*ln3) -> 0 mais PAS une preuve.", flush=True)
    print(f"    Note : convergents PAIRS ont delta~1, trivaux par Th.S.", flush=True)

print(f"\n{'='*72}", flush=True)
print(f"FIN SESSION 10f26k (partie 4)", flush=True)
print(f"{'='*72}", flush=True)
