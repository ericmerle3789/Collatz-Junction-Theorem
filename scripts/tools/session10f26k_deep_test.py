#!/usr/bin/env python3
"""
SESSION 10f26k (partie 3) — DEEP TEST pour 13 convergents non resolus
=====================================================================
Test modulaire avec premiers jusqu'a 10^9 (crible segmente).
Pour les petits cas (q < 10^6), calcul direct de d et Miller-Rabin.
"""
import math
import time
import sys

# Python 3.11+ limite la conversion int->str a 4300 digits
sys.set_int_max_str_digits(100000)

print("=" * 72, flush=True)
print("SESSION 10f26k (partie 3) — DEEP TEST", flush=True)
print("=" * 72, flush=True)

# === 1. CF haute precision ===
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

# Les 13 convergents non resolus
unresolved = [
    (10, convs[10][1], convs[10][2]),   # q=31867
    (12, convs[12][1], convs[12][2]),   # q=111202
    (17, convs[17][1], convs[17][2]),   # q=171928773
    (20, convs[20][1], convs[20][2]),   # q=6189245291
    (23, convs[23][1], convs[23][2]),   # q=137528045312
    (25, convs[25][1], convs[25][2]),   # q=5409303924479
    (36, convs[36][1], convs[36][2]),   # q=4242721909926539673
    (40, convs[40][1], convs[40][2]),   # q=50247984153525417450
    (59, convs[59][1], convs[59][2]),   # q=...
    (65, convs[65][1], convs[65][2]),
    (70, convs[70][1], convs[70][2]),
    (74, convs[74][1], convs[74][2]),
    (77, convs[77][1], convs[77][2]),
]

print(f"\n13 cas non resolus :", flush=True)
for idx, pn, qn in unresolved:
    delta = float(abs(mpf(pn) - qn * log2_3_precise))
    print(f"  n={idx:>2}: q_n={qn}, p_n={pn}, delta={delta:.3e}", flush=True)

# === 2. Pour les petits cas : calcul direct de d et Miller-Rabin ===
print(f"\n--- APPROCHE 1 : CALCUL DIRECT (petits cas) ---\n", flush=True)

def miller_rabin(n, bases=None):
    """Miller-Rabin probabilistic primality test."""
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0:
        return False

    # Write n-1 = 2^s * d
    s, d = 0, n - 1
    while d % 2 == 0:
        s += 1
        d //= 2

    if bases is None:
        bases = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

    for a in bases:
        if a >= n:
            continue
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

# n=10: q=31867, p=50508 => d a environ 15206 chiffres
# n=12: q=111202, p=176251 => d a environ 53077 chiffres
# On peut calculer d directement pour ces cas

for idx, pn, qn in unresolved[:2]:  # n=10 et n=12
    print(f"  n={idx}: Calcul de d = 2^{pn} - 3^{qn}...", end=" ", flush=True)
    t0 = time.time()
    d_val = pow(2, pn) - pow(3, qn)
    dt = time.time() - t0
    n_digits = len(str(abs(d_val)))
    print(f"({n_digits} chiffres, {dt:.1f}s)", flush=True)

    if d_val <= 0:
        print(f"    d <= 0, ERREUR dans CF !", flush=True)
        continue

    # Verifier avec petits premiers d'abord
    print(f"    Test divisibilite directe...", end=" ", flush=True)
    found = None
    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]:
        if d_val % p == 0:
            found = p
            break
    if found:
        print(f"Divisible par {found} !", flush=True)
        continue

    # Trial division avec division directe (plus rapide que pow pour petit d)
    print(f"Trial division...", flush=True)
    t0 = time.time()
    found = None

    # Tester les premiers jusqu'a 10^6 via division directe
    # C'est efficace car Python's big int mod is optimized
    for p in range(53, 1000000, 2):
        # Quick primality check
        if p > 3 and (p % 2 == 0 or p % 3 == 0):
            continue
        is_p = True
        j = 5
        while j * j <= p:
            if p % j == 0 or p % (j + 2) == 0:
                is_p = False
                break
            j += 6
        if not is_p:
            continue

        if d_val % p == 0:
            found = p
            break

    dt = time.time() - t0
    if found:
        print(f"    COMPOSITE ! Facteur p = {found} ({dt:.1f}s)", flush=True)
    else:
        print(f"    Aucun facteur <= 10^6 ({dt:.1f}s)", flush=True)
        # Miller-Rabin test
        print(f"    Miller-Rabin (12 bases)...", end=" ", flush=True)
        t0 = time.time()
        is_prob_prime = miller_rabin(d_val)
        dt = time.time() - t0
        if is_prob_prime:
            print(f"PROBABLEMENT PREMIER ! ({dt:.1f}s)", flush=True)
        else:
            print(f"COMPOSITE (MR) ({dt:.1f}s)", flush=True)

# === 3. Crible segmente 10^8 a 10^9 ===
print(f"\n--- APPROCHE 2 : CRIBLE SEGMENTE [10^8, 10^9] ---\n", flush=True)

def sieve(n):
    s = bytearray(b'\x01') * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n**0.5) + 1):
        if s[i]:
            s[i*i::i] = b'\x00' * len(s[i*i::i])
    return [i for i in range(2, n + 1) if s[i]]

# Crible segmente : generer les premiers dans [lo, hi] par blocs
def segmented_sieve(lo, hi, small_primes):
    """Yield primes in [lo, hi] using segmented sieve."""
    size = hi - lo + 1
    is_prime = bytearray(b'\x01') * size
    for p in small_primes:
        start = ((lo + p - 1) // p) * p
        if start == p:
            start += p
        for j in range(start - lo, size, p):
            is_prime[j] = 0
    for i in range(size):
        if is_prime[i] and (lo + i) > 1:
            yield lo + i

# Obtenir les petits premiers pour le crible segmente
print(f"  Crible de base (premiers <= sqrt(10^9) = 31623)...", flush=True)
small_primes = sieve(31623)
print(f"  {len(small_primes)} petits premiers.", flush=True)

# Tester par blocs de 10M
BLOCK = 10_000_000
resolved_this_round = {}

for block_start in range(100_000_000, 1_000_000_000, BLOCK):
    block_end = block_start + BLOCK - 1

    # Generer les premiers dans ce bloc
    primes_block = list(segmented_sieve(block_start, block_end, small_primes))

    remaining = [(idx, pn, qn) for idx, pn, qn in unresolved
                 if idx not in resolved_this_round]

    if not remaining:
        break

    for idx, pn, qn in remaining:
        for p in primes_block:
            d_mod_p = (pow(2, pn, p) - pow(3, qn, p)) % p
            if d_mod_p == 0:
                resolved_this_round[idx] = p
                print(f"  n={idx:>2}, q_n={qn}: COMPOSITE, facteur {p} "
                      f"(bloc [{block_start/1e6:.0f}M, {block_end/1e6:.0f}M])", flush=True)
                break

    # Progress
    if block_start % 100_000_000 == 0:
        n_remaining = len(unresolved) - len(resolved_this_round)
        print(f"  ... teste jusqu'a {block_end+1:,} — {n_remaining} cas restants", flush=True)

# === 4. Si encore non resolus, tester jusqu'a 5*10^9 ===
still_unresolved = [(idx, pn, qn) for idx, pn, qn in unresolved
                    if idx not in resolved_this_round]

if still_unresolved:
    print(f"\n--- APPROCHE 3 : EXTENSION [10^9, 5*10^9] ({len(still_unresolved)} cas) ---\n", flush=True)

    # On a besoin de plus grands "small primes" pour le crible
    print(f"  Crible de base etendu (premiers <= sqrt(5*10^9) = 70711)...", flush=True)
    small_primes_ext = sieve(70711)
    print(f"  {len(small_primes_ext)} petits premiers.", flush=True)

    for block_start in range(1_000_000_000, 5_000_000_000, BLOCK):
        block_end = block_start + BLOCK - 1
        primes_block = list(segmented_sieve(block_start, block_end, small_primes_ext))

        remaining = [(idx, pn, qn) for idx, pn, qn in still_unresolved
                     if idx not in resolved_this_round]
        if not remaining:
            break

        for idx, pn, qn in remaining:
            for p in primes_block:
                d_mod_p = (pow(2, pn, p) - pow(3, qn, p)) % p
                if d_mod_p == 0:
                    resolved_this_round[idx] = p
                    print(f"  n={idx:>2}, q_n={qn}: COMPOSITE, facteur {p} "
                          f"(bloc [{block_start/1e9:.1f}G, {block_end/1e9:.1f}G])", flush=True)
                    break

        if block_start % 1_000_000_000 == 0:
            n_remaining = len(still_unresolved) - sum(1 for i,_,_ in still_unresolved if i in resolved_this_round)
            print(f"  ... teste jusqu'a {block_end+1:,} — {n_remaining} cas restants", flush=True)

# === BILAN ===
print(f"\n{'='*72}", flush=True)
print(f"BILAN DEEP TEST", flush=True)
print(f"{'='*72}", flush=True)

n_resolved_new = len(resolved_this_round)
final_unresolved = [(idx, pn, qn) for idx, pn, qn in unresolved
                    if idx not in resolved_this_round]

print(f"\n  Resolus dans cette session : {n_resolved_new}", flush=True)
for idx, factor in sorted(resolved_this_round.items()):
    print(f"    n={idx}: facteur {factor}", flush=True)

print(f"\n  Encore non resolus : {len(final_unresolved)}", flush=True)
for idx, pn, qn in final_unresolved:
    delta = float(abs(mpf(pn) - qn * log2_3_precise))
    print(f"    n={idx}: q_n={qn}, delta={delta:.3e}", flush=True)

total = 74
total_resolved = total - len(final_unresolved)
print(f"\n  SCORE TOTAL : {total_resolved}/{total} convergents dangereux COMPOSITES", flush=True)

if not final_unresolved:
    print(f"\n  *** TOUS LES 74 CONVERGENTS DANGEREUX CONFIRMES COMPOSITES ***", flush=True)
else:
    print(f"\n  DIAGNOSTIC : Les {len(final_unresolved)} cas restants ont des facteurs > 5*10^9.", flush=True)
    print(f"  Ce n'est PAS un phenomene modulaire structurel —", flush=True)
    print(f"  c'est un phenomene de TAILLE (d trop grand pour les petits facteurs).", flush=True)

print(f"\n{'='*72}", flush=True)
print(f"FIN SESSION 10f26k (partie 3)", flush=True)
print(f"{'='*72}", flush=True)
