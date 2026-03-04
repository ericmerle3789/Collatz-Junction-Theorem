#!/usr/bin/env python3
"""
SP10 Level 8 — Phase I.1f : Analyse RAPIDE des d(k) k=69..300
================================================================
Strategie : trial division jusqu'a 10^6 UNIQUEMENT (rapide),
puis analyser les cofacteurs.

OBJECTIF : comprendre la STRUCTURE, pas forcer la factorisation.
"""

import math
import time
import sys
from sympy import isprime, factorint, n_order

sys.stdout = open(sys.stdout.fileno(), mode='w', buffering=1)

def S(k):
    return int(math.ceil(k * math.log2(3)))

print("=" * 70)
print("SP10 L8 — PHASE I.1f : Analyse rapide d(k) k=69..300")
print("=" * 70)

t0 = time.time()

# Phase 1 : Trial division rapide + classification
data = {}

for k in range(69, 301):
    Sk = S(k)
    dk = (1 << Sk) - 3**k
    if dk <= 0:
        Sk += 1
        dk = (1 << Sk) - 3**k

    # Trial division RAPIDE (limit=10^6)
    factors = factorint(dk, limit=10**6)
    product = 1
    for p, e in factors.items():
        product *= p ** e

    complete = (product == dk)
    cofactor = dk // product if not complete else 1

    # Classer les facteurs premiers
    prime_factors = []
    for p, e in factors.items():
        if isprime(p):
            try:
                m = n_order(2, p)
                ratio = p / (m * m)
                prime_factors.append((p, m, ratio, "WEIL" if ratio < 1 else "DI_B"))
            except:
                prime_factors.append((p, None, None, "?"))
        else:
            prime_factors.append((p, None, None, "COMPOSITE"))

    data[k] = {
        "Sk": Sk,
        "dk_bits": dk.bit_length(),
        "complete": complete,
        "cofactor_bits": cofactor.bit_length() if not complete else 0,
        "cofactor_is_prime": None,  # a tester
        "prime_factors": prime_factors,
        "n_known_primes": sum(1 for _, _, _, t in prime_factors if t in ["WEIL", "DI_B"]),
        "all_weil": all(t == "WEIL" for _, _, _, t in prime_factors if t not in ["COMPOSITE", "?"]),
    }

    # Si cofacteur petit, tester primalite
    if not complete and cofactor.bit_length() < 100:
        try:
            data[k]["cofactor_is_prime"] = isprime(cofactor)
        except:
            pass

elapsed = time.time() - t0
print(f"Phase 1 terminee en {elapsed:.1f}s")

# ============================================================
# Analyse par tranches
# ============================================================
print("\n" + "=" * 70)
print("ANALYSE PAR TRANCHES")
print("=" * 70)

tranches = [(69, 100), (101, 150), (151, 200), (201, 250), (251, 300)]

for k_start, k_end in tranches:
    n = k_end - k_start + 1
    n_complete = sum(1 for k in range(k_start, k_end+1) if data[k]["complete"])
    n_incomplete = n - n_complete
    n_weil = sum(1 for k in range(k_start, k_end+1) if data[k]["all_weil"])

    # Cofacteurs
    cof_bits = [data[k]["cofactor_bits"] for k in range(k_start, k_end+1)
                if not data[k]["complete"]]
    cof_prime = sum(1 for k in range(k_start, k_end+1)
                   if data[k].get("cofactor_is_prime") is True)

    avg_bits = sum(cof_bits) / len(cof_bits) if cof_bits else 0
    max_bits = max(cof_bits) if cof_bits else 0

    print(f"\n  k={k_start}..{k_end} ({n} valeurs) :")
    print(f"    Factorisation complete : {n_complete}/{n}")
    print(f"    Tous facteurs WEIL : {n_weil}/{n}")
    if n_incomplete > 0:
        print(f"    Cofacteurs : avg={avg_bits:.0f} bits, max={max_bits} bits")
        print(f"    Cofacteurs premiers : {cof_prime}")

# ============================================================
# Liste detaillee des k INCOMPLETS
# ============================================================
print("\n" + "=" * 70)
print("k AVEC FACTORISATION INCOMPLETE")
print("=" * 70)

print(f"\n{'k':>4} {'Sk':>5} {'dk_bits':>8} {'cof_bits':>10} {'cof_prime':>10} {'n_primes':>10}")
print("-" * 55)

incomplete_ks = []
for k in range(69, 301):
    if not data[k]["complete"]:
        incomplete_ks.append(k)
        cof_pr = data[k].get("cofactor_is_prime")
        cof_str = "OUI" if cof_pr is True else ("NON" if cof_pr is False else "?")
        print(f"{k:>4} {data[k]['Sk']:>5} {data[k]['dk_bits']:>8} "
              f"{data[k]['cofactor_bits']:>10} {cof_str:>10} "
              f"{data[k]['n_known_primes']:>10}")

print(f"\nTotal incomplets : {len(incomplete_ks)}/{300-69+1}")

# ============================================================
# Pour les cofacteurs PREMIERS, verifier (Q)
# ============================================================
print("\n" + "=" * 70)
print("COFACTEURS PREMIERS : Verification (Q)")
print("=" * 70)

cofactor_prime_pass = 0
cofactor_prime_fail = 0
cofactor_prime_total = 0

for k in incomplete_ks:
    if data[k].get("cofactor_is_prime") is not True:
        continue

    Sk = S(k)
    dk = (1 << Sk) - 3**k
    if dk <= 0:
        Sk += 1
        dk = (1 << Sk) - 3**k

    factors = factorint(dk, limit=10**6)
    product = 1
    for p, e in factors.items():
        product *= p ** e
    cofactor = dk // product

    cofactor_prime_total += 1

    try:
        m = n_order(2, cofactor)
        m2 = m * m
        ratio = cofactor / m2

        if ratio < 1:
            n_idx = (cofactor - 1) // m
            rho_weil = (1 + max(n_idx - 1, 0) * math.sqrt(cofactor)) / max(cofactor - 1, 1)
            q_value = (cofactor - 1) * rho_weil ** (k - 17)
            q_pass = q_value < 0.041
        else:
            q_pass = None  # Besoin calcul direct

        regime = "WEIL" if ratio < 1 else "DI_B"
        status = "PASS" if q_pass is True else ("FAIL" if q_pass is False else "?")

        print(f"  k={k}: cofacteur={cofactor} ({cofactor.bit_length()}b), "
              f"m={m}, p/m^2={ratio:.4f}, {regime}, (Q)={status}")

        if q_pass is True:
            cofactor_prime_pass += 1
        elif q_pass is False:
            cofactor_prime_fail += 1

    except Exception as e:
        print(f"  k={k}: cofacteur={cofactor.bit_length()}b, erreur: {e}")

print(f"\n  Cofacteurs premiers verifies (Q) PASS : {cofactor_prime_pass}/{cofactor_prime_total}")
print(f"  Cofacteurs premiers (Q) FAIL : {cofactor_prime_fail}")

# ============================================================
# SYNTHESE
# ============================================================
print("\n" + "=" * 70)
print("SYNTHESE FINALE Phase I.1f")
print("=" * 70)

total_k = 300 - 69 + 1
n_fully_verified = sum(1 for k in range(69, 301)
                       if data[k]["complete"] and data[k]["all_weil"])
n_complete = sum(1 for k in range(69, 301) if data[k]["complete"])
n_complete_with_cof_prime = sum(1 for k in incomplete_ks
                                if data[k].get("cofactor_is_prime") is True)

print(f"\n  k total : {total_k}")
print(f"  Factorisation complete (trial div 10^6) : {n_complete}/{total_k}")
print(f"  Tous facteurs en regime WEIL : {n_fully_verified}/{total_k}")
print(f"  Incomplete avec cofacteur PREMIER : {n_complete_with_cof_prime}/{len(incomplete_ks)}")
print(f"  Incomplete avec cofacteur COMPOSITE/? : {len(incomplete_ks) - n_complete_with_cof_prime}/{len(incomplete_ks)}")

verifiable = n_fully_verified + cofactor_prime_pass
print(f"\n  ★ TOTAL (Q) VERIFIABLE : {verifiable}/{total_k}")
print(f"  ★ (Q) ECHOUE : {cofactor_prime_fail}")
print(f"  ★ RESTANT (non factorise) : {total_k - verifiable - cofactor_prime_fail}")
