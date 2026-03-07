#!/usr/bin/env python3
"""
SESSION 10f26k (partie 6) — TEST INTENSIF n=17 + ANALYSE STRUCTURELLE
======================================================================
1. Analyse les proprietes des 6 indices non resolus (CF structure)
2. Test intensif pour n=17 avec BEAUCOUP plus de primes
3. Approche "wheel" + Miller-Rabin pour couverture dense [10^8, 5*10^9]
"""
import math
import time
import sys
import random

sys.set_int_max_str_digits(100000)

print("=" * 72, flush=True)
print("SESSION 10f26k (partie 6) — ANALYSE + TEST INTENSIF n=17", flush=True)
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

# =================================================================
# PARTIE 1 : ANALYSE STRUCTURELLE DES CF
# =================================================================
print("\n--- PARTIE 1 : STRUCTURE DES FRACTIONS CONTINUES ---\n", flush=True)

# Afficher les 40 premiers quotients partiels
print("Quotients partiels CF de log_2(3) :", flush=True)
for i in range(0, min(40, len(cf)), 10):
    chunk = cf[i:i+10]
    print(f"  a[{i:>2}..{i+len(chunk)-1:>2}] = {chunk}", flush=True)

# Analyser les 6 indices non resolus
unresolved_indices = [17, 23, 25, 59, 65, 77]
resolved_odd = {
    7: 929, 9: 5, 11: 23, 13: 15661, 15: 17, 19: 5, 21: 79,
    27: 23, 29: 13, 31: 47, 33: 151, 35: 5, 37: 73, 39: 196171,
    41: 467, 43: 17218217, 45: 9343, 47: 13, 49: 136421, 51: 23,
    53: 329009, 55: 5, 57: 11633, 61: 11, 63: 5, 67: 433, 69: 5,
    71: 60853189, 73: 229, 75: 33521, 79: 172583,
}

print(f"\n--- INDICES NON RESOLUS vs RESOLUS ---\n", flush=True)
print(f"{'n':>3} {'a_n':>5} {'a_{n+1}':>7} {'q_n':>25} {'log10(facteur)':>15} {'Status':>12}", flush=True)
print(f"  {'-'*75}", flush=True)

for n_idx in range(7, 80, 2):
    if n_idx >= len(convs):
        continue
    _, pn, qn, an = convs[n_idx]
    delta = float(mpf(pn) - qn * log2_3_precise)
    if delta > 0.015:
        continue

    an_next = cf[n_idx + 1] if n_idx + 1 < len(cf) else 0

    if n_idx in resolved_odd:
        f = resolved_odd[n_idx]
        f_log = f"{math.log10(f):.1f}"
        status = "COMPOSITE"
    elif n_idx in unresolved_indices:
        f_log = ">8.0"
        status = "NON RESOLU"
    else:
        f_log = "?"
        status = "?"

    q_str = str(qn) if qn < 10**20 else f"{qn:.3e}"
    print(f"  {n_idx:>3} {an:>5} {an_next:>7} {q_str:>25} {f_log:>15} {status:>12}", flush=True)

# Correlation entre a_{n+1} et taille du facteur
print(f"\n--- CORRELATION a_{{n+1}} et FACTORISATION ---\n", flush=True)
print("Hypothese : a_{n+1} grand => q_{n+1}/q_n grand => delta_n petit", flush=True)
print("           => d(q_n) plus petit => facteur plus facile a trouver ?\n", flush=True)

for n_idx in unresolved_indices:
    if n_idx >= len(convs):
        continue
    _, pn, qn, an = convs[n_idx]
    an_next = cf[n_idx + 1] if n_idx + 1 < len(cf) else 0
    delta = float(mpf(pn) - qn * log2_3_precise)
    log_d = float(qn * log(mpf(3)) / log(mpf(10)))
    print(f"  n={n_idx:>2}: a_n={an}, a_{{n+1}}={an_next}, delta={delta:.3e}, "
          f"log10(d)~{log_d:.1e}", flush=True)

# =================================================================
# PARTIE 2 : CONDITION DE RESONANCE
# =================================================================
print(f"\n--- PARTIE 2 : ANALYSE DE RESONANCE ---\n", flush=True)
print("Pour p | d(q_n), il faut 2^{p_n} ≡ 3^{q_n} (mod p)", flush=True)
print("i.e., p_n ≡ q_n * log_p(2)/log_p(3) (mod ord_p(2))\n", flush=True)

# Pour les petits primes, calculer les ordres et verifier la condition
def multiplicative_order(a, n):
    """Compute ord_n(a)."""
    if math.gcd(a, n) != 1:
        return 0
    order = 1
    current = a % n
    while current != 1:
        current = (current * a) % n
        order += 1
        if order > n:
            return 0
    return order

# Analyser pourquoi n=17 n'a pas de petit facteur
_, pn17, qn17, _ = convs[17]
print(f"CAS n=17 : S = p_17 = {pn17}, k = q_17 = {qn17}\n", flush=True)

small_primes = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
print(f"{'p':>5} {'ord_p(2)':>10} {'ord_p(3)':>10} {'S mod ord':>10} {'k mod ord3':>10} {'2^S mod p':>10} {'3^k mod p':>10} {'Match':>6}", flush=True)
print(f"  {'-'*80}", flush=True)

for p in small_primes:
    t2 = multiplicative_order(2, p)
    t3 = multiplicative_order(3, p)
    s_mod = pn17 % t2 if t2 > 0 else -1
    k_mod = qn17 % t3 if t3 > 0 else -1
    val2 = pow(2, pn17, p)
    val3 = pow(3, qn17, p)
    match = "OUI" if val2 == val3 else "non"
    print(f"  {p:>5} {t2:>10} {t3:>10} {s_mod:>10} {k_mod:>10} {val2:>10} {val3:>10} {match:>6}", flush=True)

# =================================================================
# PARTIE 3 : TEST INTENSIF n=17
# =================================================================
print(f"\n{'='*72}", flush=True)
print(f"PARTIE 3 : TEST INTENSIF n=17 — PRIMES [10^8, 5*10^9]", flush=True)
print(f"{'='*72}\n", flush=True)

# Miller-Rabin rapide
def is_prime_mr(n, k=8):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0: return False
    if n % 3 == 0: return False
    if n % 5 == 0: return False
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

S_17 = pn17
k_17 = qn17

# Strategie : balayer systematiquement avec un wheel mod 30
# Wheel mod 30 : residus copremiers a 30 = {1,7,11,13,17,19,23,29}
wheel_residues = [1, 7, 11, 13, 17, 19, 23, 29]

random.seed(42)
total_primes_tested = 0
total_candidates = 0
found = None

# Phase A : balayage dense [10^8, 10^9]
print(f"Phase A : balayage dense [10^8, 10^9]...", flush=True)
t0 = time.time()

for base in range(100_000_000, 1_000_000_000, 30):
    for r in wheel_residues:
        c = base + r
        if c < 100_000_007:  # skip below 10^8
            continue
        if c >= 1_000_000_000:
            break
        total_candidates += 1
        if not is_prime_mr(c, k=5):
            continue
        total_primes_tested += 1
        if (pow(2, S_17, c) - pow(3, k_17, c)) % c == 0:
            found = c
            break
    if found:
        break
    # Progress every 10M
    if base % 100_000_000 == 0 and base > 100_000_000:
        dt = time.time() - t0
        rate = total_primes_tested / dt if dt > 0 else 0
        print(f"  {base/1e9:.1f}G, {total_primes_tested:,} primes ({rate:.0f}/s), "
              f"t={dt:.0f}s", flush=True)

dt = time.time() - t0
if found:
    print(f"\n  *** n=17 COMPOSITE ! facteur = {found} ***", flush=True)
    print(f"  Verification : (2^S - 3^k) mod {found} = "
          f"{(pow(2, S_17, found) - pow(3, k_17, found)) % found}", flush=True)
else:
    print(f"  [10^8, 10^9] : {total_primes_tested:,} primes, aucun facteur ({dt:.0f}s)", flush=True)

if not found:
    # Phase B : balayage dense [10^9, 5*10^9]
    print(f"\nPhase B : balayage dense [10^9, 5*10^9]...", flush=True)
    t0b = time.time()
    primes_b = 0

    for base in range(1_000_000_000, 5_000_000_000, 30):
        for r in wheel_residues:
            c = base + r
            if c >= 5_000_000_000:
                break
            total_candidates += 1
            if not is_prime_mr(c, k=5):
                continue
            total_primes_tested += 1
            primes_b += 1
            if (pow(2, S_17, c) - pow(3, k_17, c)) % c == 0:
                found = c
                break
        if found:
            break
        if base % 500_000_000 == 0 and base > 1_000_000_000:
            dt = time.time() - t0b
            rate = primes_b / dt if dt > 0 else 0
            print(f"  {base/1e9:.1f}G, {primes_b:,} primes ({rate:.0f}/s), "
                  f"t={dt:.0f}s", flush=True)

    dt = time.time() - t0b
    if found:
        print(f"\n  *** n=17 COMPOSITE ! facteur = {found} ***", flush=True)
        print(f"  Verification : (2^S - 3^k) mod {found} = "
              f"{(pow(2, S_17, found) - pow(3, k_17, found)) % found}", flush=True)
    else:
        print(f"  [10^9, 5*10^9] : {primes_b:,} primes, aucun facteur ({dt:.0f}s)", flush=True)

if not found:
    # Phase C : echantillonnage aleatoire massif [5*10^9, 10^18]
    print(f"\nPhase C : echantillonnage aleatoire [5*10^9, 10^18]...", flush=True)
    random.seed(2026)
    t0c = time.time()
    primes_c = 0

    ranges_c = [
        (5*10**9, 10**10, 500000),
        (10**10, 10**11, 500000),
        (10**11, 10**12, 500000),
        (10**12, 10**13, 500000),
        (10**13, 10**14, 300000),
        (10**14, 10**15, 300000),
        (10**15, 10**16, 200000),
        (10**16, 10**17, 200000),
        (10**17, 10**18, 200000),
    ]

    for lo, hi, n_tests in ranges_c:
        t_range = time.time()
        primes_range = 0
        for _ in range(n_tests):
            candidate = random.randrange(lo | 1, hi, 2)
            if candidate % 3 == 0 or candidate % 5 == 0:
                continue
            if not is_prime_mr(candidate, k=5):
                continue
            primes_range += 1
            primes_c += 1
            total_primes_tested += 1
            if (pow(2, S_17, candidate) - pow(3, k_17, candidate)) % candidate == 0:
                found = candidate
                break
        if found:
            dt_r = time.time() - t_range
            print(f"  [{lo:.0e}, {hi:.0e}]: *** FACTEUR {found} *** ({dt_r:.1f}s)", flush=True)
            print(f"  Verification : (2^S - 3^k) mod {found} = "
                  f"{(pow(2, S_17, found) - pow(3, k_17, found)) % found}", flush=True)
            break
        else:
            dt_r = time.time() - t_range
            print(f"  [{lo:.0e}, {hi:.0e}]: {primes_range} primes, aucun facteur ({dt_r:.1f}s)", flush=True)

    if not found:
        dt_total = time.time() - t0c
        print(f"\n  Total Phase C : {primes_c:,} primes, aucun facteur ({dt_total:.0f}s)", flush=True)

# =================================================================
# BILAN
# =================================================================
print(f"\n{'='*72}", flush=True)
print(f"BILAN SESSION 10f26k (partie 6)", flush=True)
print(f"{'='*72}\n", flush=True)

print(f"  Total primes testes pour n=17 : {total_primes_tested:,}", flush=True)
if found:
    print(f"  RESULTAT : n=17 COMPOSITE, facteur {found}", flush=True)
    print(f"  Score : 32/37 convergents impairs COMPOSITES (5 non resolus)", flush=True)
else:
    print(f"  RESULTAT : n=17 toujours NON RESOLU (facteur > plage testee)", flush=True)
    print(f"  Score : 31/37 convergents impairs COMPOSITES (6 non resolus)", flush=True)
    print(f"\n  DIAGNOSTIC :", flush=True)
    print(f"    Le plus petit facteur premier de d(q_17) est > {5*10**9:.0e}.", flush=True)
    print(f"    d(q_17) a ~82 millions de chiffres.", flush=True)
    print(f"    Heuristiquement, Pr[facteur > B] ~ rho(log(d)/log(B)) -> 0 lentement.", flush=True)
    print(f"    Un calcul C/GMP couvrant [10^8, 10^12] systematiquement est recommande.", flush=True)

print(f"\n{'='*72}", flush=True)
print(f"FIN SESSION 10f26k (partie 6)", flush=True)
print(f"{'='*72}", flush=True)
