#!/usr/bin/env python3
"""
SESSION 10f26k (partie 2) — TEST COMPOSITENESS ETENDU
======================================================
Test modulaire rapide pour TOUS les convergents de log_2(3) (80 termes CF).
Methode : d(q_n) mod p = (2^{p_n} mod p - 3^{q_n} mod p) mod p
Si d mod p == 0, d est composite.

CONTEXTE :
  - Covering set (10f26k partie 1) : ECHEC avec premiers <= 251
  - Les facteurs sont grands et erratiques (929, 15661, 4919, 8022437...)
  - On etend systematiquement le crible : 1M, puis 10M si necessaire
"""
import math
import time
import sys

print("=" * 72, flush=True)
print("SESSION 10f26k (partie 2) — COMPOSITENESS ETENDUE", flush=True)
print("=" * 72, flush=True)

# === 1. CF de log_2(3) avec haute precision ===
print("\n--- 1. FRACTIONS CONTINUES DE log_2(3) ---\n", flush=True)

try:
    from mpmath import mp, mpf, log, floor
    mp.dps = 200
    log2_3_precise = log(3) / log(2)

    x = log2_3_precise
    cf = []
    convs = []  # (index, p_n, q_n, a_n)
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

        pn = int(p_curr)
        qn = int(q_curr)
        convs.append((i, pn, qn, a))

        frac = x - a
        if frac < mpf(10) ** (-150):
            break
        x = 1 / frac

    print(f"CF ({len(cf)} termes) calcule avec {mp.dps} digits.", flush=True)

except ImportError:
    print("ERREUR: mpmath requis. pip install mpmath", flush=True)
    sys.exit(1)

# === 2. Identifier convergents dangereux ===
print("\n--- 2. CONVERGENTS DANGEREUX (delta < 0.015) ---\n", flush=True)

dangerous = []
for idx, pn, qn, an in convs:
    if qn < 4:
        continue
    delta_mp = mpf(pn) - qn * log2_3_precise
    delta = float(abs(delta_mp))
    if delta < 0.015:
        dangerous.append((idx, pn, qn, an, delta))

print(f"{'n':>3} {'a_n':>5} {'q_n':>25} {'p_n':>25} {'delta':>15} {'m_max':>12}", flush=True)
print("-" * 92, flush=True)
for idx, pn, qn, an, delta in dangerous:
    m_max = 1.0 / (delta * math.log(2)) if delta > 1e-15 else float('inf')
    print(f"{idx:>3} {an:>5} {qn:>25} {pn:>25} {delta:>15.3e} {m_max:>12.0f}", flush=True)

print(f"\nTotal : {len(dangerous)} convergents dangereux.", flush=True)

# === 3. Crible de premiers ===
print("\n--- 3. CRIBLE ---\n", flush=True)

def sieve(n):
    s = bytearray(b'\x01') * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n**0.5) + 1):
        if s[i]:
            s[i*i::i] = b'\x00' * len(s[i*i::i])
    return [i for i in range(2, n + 1) if s[i]]

t0 = time.time()
primes_1M = sieve(1_000_000)
print(f"  {len(primes_1M)} premiers <= 1M ({time.time()-t0:.1f}s)", flush=True)

# === 4. Test modulaire pour chaque convergent dangereux ===
print(f"\n--- 4. TEST MODULAIRE RAPIDE ---\n", flush=True)
print(f"{'n':>3} {'q_n':>25} {'delta':>12} {'Status':>12} {'Facteur':>12} {'Temps':>8}", flush=True)
print("-" * 78, flush=True)

results = []
unresolved = []

for idx, pn, qn, an, delta in dangerous:
    t0 = time.time()
    found = None

    # Phase 1 : premiers <= 1M
    for p in primes_1M:
        d_mod_p = (pow(2, pn, p) - pow(3, qn, p)) % p
        if d_mod_p == 0:
            found = p
            break

    dt = time.time() - t0

    if found:
        print(f"{idx:>3} {qn:>25} {delta:>12.3e} {'COMPOSITE':>12} {found:>12} {dt:>7.2f}s", flush=True)
        results.append((idx, pn, qn, delta, "COMPOSITE", found))
    else:
        print(f"{idx:>3} {qn:>25} {delta:>12.3e} {'???':>12} {'':>12} {dt:>7.2f}s  <- BESOIN 10M", flush=True)
        unresolved.append((idx, pn, qn, an, delta))
        results.append((idx, pn, qn, delta, "PENDING", 0))

# === 5. Extension a 10M pour les non resolus ===
if unresolved:
    print(f"\n--- 5. EXTENSION A 10M ({len(unresolved)} cas) ---\n", flush=True)

    t0 = time.time()
    primes_10M = sieve(10_000_000)
    print(f"  {len(primes_10M)} premiers <= 10M ({time.time()-t0:.1f}s)", flush=True)

    still_unresolved = []
    for idx, pn, qn, an, delta in unresolved:
        t0 = time.time()
        found = None

        # Tester seulement les premiers > 1M
        for p in primes_10M:
            if p <= 1_000_000:
                continue
            d_mod_p = (pow(2, pn, p) - pow(3, qn, p)) % p
            if d_mod_p == 0:
                found = p
                break

        dt = time.time() - t0

        if found:
            print(f"  n={idx:>3}, q_n={qn}: COMPOSITE, facteur {found} ({dt:.2f}s)", flush=True)
            # Mettre a jour dans results
            for i, r in enumerate(results):
                if r[0] == idx:
                    results[i] = (idx, pn, qn, delta, "COMPOSITE", found)
                    break
        else:
            print(f"  n={idx:>3}, q_n={qn}: PAS DE FACTEUR <= 10M ({dt:.2f}s)", flush=True)
            still_unresolved.append((idx, pn, qn, an, delta))

    # === 6. Extension a 100M pour les cas extremes ===
    if still_unresolved:
        print(f"\n--- 6. EXTENSION A 100M ({len(still_unresolved)} cas) ---\n", flush=True)
        print("  Crible 100M...", flush=True)

        t0 = time.time()
        primes_100M = sieve(100_000_000)
        print(f"  {len(primes_100M)} premiers <= 100M ({time.time()-t0:.1f}s)", flush=True)

        final_unresolved = []
        for idx, pn, qn, an, delta in still_unresolved:
            t0 = time.time()
            found = None

            for p in primes_100M:
                if p <= 10_000_000:
                    continue
                d_mod_p = (pow(2, pn, p) - pow(3, qn, p)) % p
                if d_mod_p == 0:
                    found = p
                    break

            dt = time.time() - t0

            if found:
                print(f"  n={idx:>3}, q_n={qn}: COMPOSITE, facteur {found} ({dt:.2f}s)", flush=True)
                for i, r in enumerate(results):
                    if r[0] == idx:
                        results[i] = (idx, pn, qn, delta, "COMPOSITE", found)
                        break
            else:
                print(f"  n={idx:>3}, q_n={qn}: PAS DE FACTEUR <= 100M ({dt:.2f}s)", flush=True)
                final_unresolved.append((idx, pn, qn, an, delta))
else:
    still_unresolved = []
    final_unresolved = []

# === 7. Verification croisee : 21 d premiers connus ===
print(f"\n--- 7. CONTROLE : 21 d PREMIERS CONNUS ---\n", flush=True)

known_prime_k = [3, 4, 5, 13, 56, 61, 69, 73, 76, 148, 185,
                 655, 917, 2183, 3540, 3895, 4500, 6891, 7752, 10291, 13695]

errors = 0
for k in known_prime_k:
    S = math.ceil(k * float(log2_3_precise))
    found = None
    for p in primes_1M[:1000]:  # Test rapide avec 1000 premiers
        d_mod_p = (pow(2, S, p) - pow(3, k, p)) % p
        if d_mod_p == 0:
            found = p
            break
    delta = S - k * float(log2_3_precise)
    if found:
        print(f"  k={k:>5}: ERREUR facteur {found} (delta={delta:.4f})", flush=True)
        errors += 1
    else:
        print(f"  k={k:>5}: OK (delta={delta:.4f})", flush=True)

print(f"\n  Controle : {21-errors}/21 OK", flush=True)

# === BILAN FINAL ===
print(f"\n{'='*72}", flush=True)
print(f"BILAN FINAL SESSION 10f26k (partie 2)", flush=True)
print(f"{'='*72}", flush=True)

n_total = len(dangerous)
n_composite = sum(1 for r in results if r[4] == "COMPOSITE")
n_pending = sum(1 for r in results if r[4] == "PENDING")

print(f"\n  Convergents dangereux (delta < 0.015) : {n_total}", flush=True)
print(f"  COMPOSITES (facteur trouve)           : {n_composite}", flush=True)
print(f"  NON RESOLUS                           : {n_pending}", flush=True)

if n_pending == 0:
    print(f"\n  *** TOUS LES CONVERGENTS DANGEREUX SONT COMPOSITES ***", flush=True)
    print(f"\n  IMPLICATION :", flush=True)
    print(f"    Pour k >= 4, d(k) premier :", flush=True)
    print(f"      delta >= 0.0145 => PROUVE (Th.S)", flush=True)
    print(f"      delta < 0.0145  => d(k) COMPOSITE (verifie pour 80 termes CF)", flush=True)
    print(f"    => Gap G2c FERME computationnellement.", flush=True)
else:
    print(f"\n  CAS NON RESOLUS :", flush=True)
    for r in results:
        if r[4] == "PENDING":
            idx, pn, qn, delta = r[0], r[1], r[2], r[3]
            print(f"    n={idx}, q_n={qn}, delta={delta:.3e}", flush=True)
            print(f"      Besoin : test Fermat ou primes > 100M", flush=True)

print(f"\n  TABLEAU RECAPITULATIF :", flush=True)
print(f"  {'n':>3} {'q_n':>25} {'delta':>12} {'Status':>12} {'Facteur':>12}", flush=True)
print(f"  {'-'*68}", flush=True)
for idx, pn, qn, delta, status, factor in results:
    f_str = str(factor) if factor else "—"
    print(f"  {idx:>3} {qn:>25} {delta:>12.3e} {status:>12} {f_str:>12}", flush=True)

print(f"\n{'='*72}", flush=True)
print(f"FIN SESSION 10f26k (partie 2)", flush=True)
print(f"{'='*72}", flush=True)
