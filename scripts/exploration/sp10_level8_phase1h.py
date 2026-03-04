#!/usr/bin/env python3
"""
SP10 Level 8 — Phase I.1h : Verification (Q) avec sympy FULL
==============================================================
Utilise sympy factorint SANS limite (Pollard rho + ECM)
avec timeout par k via signal.alarm.

OPTIMISATION de fast_order pour les grands premiers.
"""

import math
import cmath
import time
import signal
import sys
from sympy import isprime, factorint, n_order

sys.stdout = open(sys.stdout.fileno(), mode='w', buffering=1)

def S(k):
    return int(math.ceil(k * math.log2(3)))

class Timeout(Exception):
    pass

def timeout_handler(signum, frame):
    raise Timeout()

def fast_order_2(p):
    """Calcule ord_p(2) rapidement."""
    if p <= 2:
        return 1
    n = p - 1
    # Factoriser p-1 avec sympy (rapide pour < 30 digits)
    try:
        facs = factorint(n, limit=10**6)
        # Verifier si factorisation complete
        product = 1
        for q, e in facs.items():
            product *= q ** e
        if product != n:
            # Incomplete, utiliser n_order de sympy
            return n_order(2, p)
    except:
        return n_order(2, p)

    order = n
    for q in facs:
        while order % q == 0 and pow(2, order // q, p) == 1:
            order //= q
    return order

def verify_Q_weil(p, m, k):
    """Verifie (Q) par borne de Weil. Retourne (pass, rho_bound)."""
    n_idx = (p - 1) // m
    if n_idx <= 0:
        n_idx = 1
    rho_weil = (1 + max(n_idx - 1, 0) * math.sqrt(p)) / max(p - 1, 1)
    if rho_weil >= 1:
        return None, rho_weil  # Weil ne suffit pas
    q_val = (p - 1) * rho_weil ** (k - 17)
    return q_val < 0.041, rho_weil

print("=" * 70)
print("SP10 L8 — PHASE I.1h : Verification (Q) k=69..200")
print("  Methode : sympy factorint (Pollard rho + ECM)")
print("  Timeout : 30s par k")
print("=" * 70)

t0 = time.time()
TIMEOUT_PER_K = 30  # secondes

total_complete_pass = 0
total_complete_fail = 0
total_timeout = 0
total_incomplete = 0  # factorise partiellement, cofacteur > 100 digits
dib_cases = []

for k in range(69, 201):
    Sk = S(k)
    dk = (1 << Sk) - 3**k
    if dk <= 0:
        Sk += 1
        dk = (1 << Sk) - 3**k

    # Factoriser avec timeout
    signal.signal(signal.SIGALRM, timeout_handler)
    signal.alarm(TIMEOUT_PER_K)

    try:
        factors = factorint(dk)
        signal.alarm(0)

        # Verifier si complet
        product = 1
        for p, e in factors.items():
            product *= p ** e
        complete = (product == dk)

        if not complete:
            # Cofacteur restant
            cofactor = dk // product
            cof_bits = cofactor.bit_length()
            if isprime(cofactor):
                factors[cofactor] = 1
                complete = True

        if not complete:
            total_incomplete += 1
            elapsed = time.time() - t0
            cof_bits = (dk // product).bit_length()
            print(f"  k={k:>3}: INCOMPLETE (cofacteur {cof_bits}b)  [{elapsed:.0f}s]")
            continue

        # Verifier (Q) pour chaque facteur premier
        all_pass = True
        for p_factor in factors:
            if not isprime(p_factor):
                all_pass = None  # can't verify
                continue

            m = fast_order_2(p_factor)
            ratio = p_factor / (m * m)

            q_pass, rho = verify_Q_weil(p_factor, m, k)

            if q_pass is None:
                # Regime non-Weil : calcul direct si p petit
                if p_factor < 500000:
                    omega = cmath.exp(2j * cmath.pi / p_factor)
                    pows = [pow(2, j, p_factor) for j in range(m)]
                    max_rho = 0
                    for c in range(1, min(p_factor, 3001)):
                        s = sum(omega ** ((c * pw) % p_factor) for pw in pows)
                        val = abs(s) / m
                        if val > max_rho:
                            max_rho = val
                    q_val = (p_factor - 1) * max_rho ** (k - 17)
                    q_pass = q_val < 0.041
                    dib_cases.append((k, p_factor, m, ratio, max_rho, q_val, q_pass))
                else:
                    all_pass = None
                    dib_cases.append((k, p_factor, m, ratio, None, None, None))

            if q_pass is False:
                all_pass = False

        if all_pass is True:
            total_complete_pass += 1
        elif all_pass is False:
            total_complete_fail += 1
            print(f"  k={k:>3}: (Q) FAIL !!!")
        else:
            total_incomplete += 1
            elapsed = time.time() - t0
            print(f"  k={k:>3}: partial (facteur DI_B/HARD > 500K)  [{elapsed:.0f}s]")

    except Timeout:
        signal.alarm(0)
        total_timeout += 1
        elapsed = time.time() - t0
        print(f"  k={k:>3}: TIMEOUT ({TIMEOUT_PER_K}s)  [{elapsed:.0f}s]")

    except Exception as e:
        signal.alarm(0)
        total_timeout += 1
        elapsed = time.time() - t0
        print(f"  k={k:>3}: ERROR ({e})  [{elapsed:.0f}s]")

    # Progress checkpoints
    if k % 25 == 0:
        elapsed = time.time() - t0
        print(f"  --- checkpoint k={k}: {total_complete_pass} PASS, "
              f"{total_complete_fail} FAIL, {total_timeout} timeout, "
              f"{total_incomplete} partial  [{elapsed:.0f}s] ---")

elapsed = time.time() - t0

# ============================================================
# RAPPORT
# ============================================================
print(f"\n{'='*70}")
print(f"RAPPORT Phase I.1h (k=69..200, {elapsed:.0f}s)")
print(f"{'='*70}")

total = 200 - 69 + 1
print(f"\n  k total : {total}")
print(f"  (Q) PASS complet : {total_complete_pass}/{total} ({100*total_complete_pass/total:.1f}%)")
print(f"  (Q) FAIL         : {total_complete_fail}/{total}")
print(f"  Timeout           : {total_timeout}/{total}")
print(f"  Partiel           : {total_incomplete}/{total}")

if dib_cases:
    print(f"\n  Cas Di Benedetto/HARD ({len(dib_cases)}) :")
    for k, p, m, ratio, rho, qval, qpass in dib_cases:
        status = "PASS" if qpass else ("FAIL" if qpass is False else "?")
        rho_s = f"{rho:.4f}" if rho else "?"
        print(f"    k={k}, p={p}, m={m}, p/m^2={ratio:.2f}, rho={rho_s}, (Q)={status}")

print(f"\n{'='*70}")
print(f"★ VERDICT ★")
print(f"{'='*70}")

if total_complete_fail == 0:
    print(f"  ✓ ZERO echec (Q) !")
    print(f"  ✓ {total_complete_pass} verifications completes sur {total}")
    remaining = total - total_complete_pass
    print(f"  → {remaining} valeurs restent non-verifiees (timeout/partial)")
    if remaining == 0:
        print(f"\n  ★★★ REGIME A COMPLETEMENT FERME pour k=69..200 ! ★★★")
    elif remaining <= 10:
        print(f"\n  ★★ Regime A quasi-ferme. {remaining} cas a traiter. ★★")
