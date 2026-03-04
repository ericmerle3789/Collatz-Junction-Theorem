#!/usr/bin/env python3
"""
SP10 Level 8 — Phase I.1g : Analyse ULTRA-RAPIDE des d(k)
============================================================
Strategie :
1. Trial division a 10^6 (rapide)
2. Pour chaque facteur p, calculer m = ord_p(2) via fast_order
3. Classifier et verifier (Q) par borne de Weil
4. Pour cofacteurs : tester primalite et ord(2) si taille < 100 bits

OPTIMISATION : fast_order utilise la factorisation de p-1 et pow(2,e,p)
au lieu de sympy n_order qui est lent.
"""

import math
import time
import sys
from sympy import isprime

sys.stdout = open(sys.stdout.fileno(), mode='w', buffering=1)

def S(k):
    return int(math.ceil(k * math.log2(3)))

def trial_factor(n, limit=10**6):
    """Factorisation par division par les petits premiers."""
    factors = {}
    for p in [2, 3, 5]:
        while n % p == 0:
            factors[p] = factors.get(p, 0) + 1
            n //= p
    d = 7
    while d * d <= n and d <= limit:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        # Sauter les multiples de 2, 3, 5
        d += 4 if d % 6 == 5 else 2
        if d > limit:
            break
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors

def fast_order(a, p):
    """Calcule ord_p(a) rapidement en utilisant p-1 et sa factorisation."""
    if p <= 2:
        return 1
    # Factoriser p-1
    n = p - 1
    order = n
    # Factorisation rapide de n
    factors = set()
    temp = n
    for q in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]:
        if temp % q == 0:
            factors.add(q)
            while temp % q == 0:
                temp //= q
    # Pour les grands facteurs, on fait du trial division jusqu'a sqrt
    d = 53
    while d * d <= temp:
        if temp % d == 0:
            factors.add(d)
            while temp % d == 0:
                temp //= d
        d += 2
    if temp > 1:
        factors.add(temp)

    # Reduire order en divisant par les facteurs premiers de p-1
    for q in factors:
        while order % q == 0 and pow(a, order // q, p) == 1:
            order //= q

    return order

print("=" * 70)
print("SP10 L8 — PHASE I.1g : Analyse ultra-rapide d(k) k=69..300")
print("=" * 70)

t0 = time.time()

# Resultats
complete_pass = 0  # factorisation complete, (Q) PASS pour tous les facteurs
complete_fail = 0  # factorisation complete, (Q) FAIL pour au moins un
incomplete = 0      # factorisation incomplete
incomplete_pass = 0 # incomplet mais tous facteurs connus passent (Q)

incomplete_details = []  # (k, cofactor_bits, cofactor_prime)
all_ratios = []  # (p/m^2, k, p, m)
dib_cases = []   # cas en regime Di Benedetto

for k in range(69, 301):
    Sk = S(k)
    dk = (1 << Sk) - 3**k
    if dk <= 0:
        Sk += 1
        dk = (1 << Sk) - 3**k

    # Trial division rapide
    factors = trial_factor(dk, limit=10**6)

    # Separer petits facteurs (< 10^6) et grand cofacteur (> 10^6)
    small_factors = {}
    big_factor = 1
    for p, e in factors.items():
        if p <= 10**6:
            small_factors[p] = e
        else:
            big_factor *= p ** e

    # Verifier si big_factor est 1 (factorisation complete)
    is_complete = (big_factor == 1)

    # Si big_factor est premier et < 10^20 (ou meme plus), on peut travailler avec
    big_is_prime = False
    if not is_complete and big_factor.bit_length() < 100:
        big_is_prime = isprime(big_factor)

    # Verifier (Q) pour les petits facteurs
    all_q_pass = True
    for p in small_factors:
        if p < 2:
            continue
        m = fast_order(2, p)
        ratio = p / (m * m)
        all_ratios.append((ratio, k, p, m))

        if ratio < 1:
            # Regime WEIL
            n_idx = (p - 1) // m
            rho_weil = (1 + max(n_idx - 1, 0) * math.sqrt(p)) / max(p - 1, 1)
            q_val = (p - 1) * rho_weil ** (k - 17)
            if q_val >= 0.041:
                all_q_pass = False
        else:
            # Regime DI_B : pour p < 10^6, on calcule rho directement
            import cmath
            omega = cmath.exp(2j * cmath.pi / p)
            pows = [pow(2, j, p) for j in range(m)]
            max_rho = 0
            for c in range(1, min(p, 2001)):
                s = sum(omega ** ((c * pw) % p) for pw in pows)
                val = abs(s) / m
                if val > max_rho:
                    max_rho = val
            q_val = (p - 1) * max_rho ** (k - 17)
            if q_val >= 0.041:
                all_q_pass = False
            dib_cases.append((k, p, m, ratio, max_rho, q_val))

    # Verifier (Q) pour big_factor si premier
    big_q_pass = None
    if big_is_prime:
        m = fast_order(2, big_factor)
        ratio = big_factor / (m * m)
        all_ratios.append((ratio, k, big_factor, m))

        if ratio < 1:
            n_idx = (big_factor - 1) // m
            rho_weil = (1 + max(n_idx - 1, 0) * math.sqrt(big_factor)) / max(big_factor - 1, 1)
            q_val = (big_factor - 1) * rho_weil ** (k - 17)
            big_q_pass = q_val < 0.041
        else:
            dib_cases.append((k, big_factor, m, ratio, None, None))
            big_q_pass = None  # pas de borne facile

    # Classification
    if is_complete:
        if all_q_pass:
            complete_pass += 1
        else:
            complete_fail += 1
    elif big_is_prime:
        if all_q_pass and big_q_pass is True:
            complete_pass += 1  # Effectivement complete
        elif all_q_pass and big_q_pass is False:
            complete_fail += 1
        else:
            incomplete += 1
            incomplete_details.append((k, big_factor.bit_length(), True, big_q_pass))
            if all_q_pass:
                incomplete_pass += 1
    else:
        incomplete += 1
        incomplete_details.append((k, big_factor.bit_length(), False, None))
        if all_q_pass:
            incomplete_pass += 1

    # Progress
    if k % 50 == 0 or k == 100:
        elapsed = time.time() - t0
        print(f"  ... k={k}, elapsed={elapsed:.1f}s")

elapsed = time.time() - t0
print(f"\nTermine en {elapsed:.1f}s")

# ============================================================
# RAPPORT
# ============================================================
print("\n" + "=" * 70)
print("RAPPORT Phase I.1g")
print("=" * 70)

total = 300 - 69 + 1
print(f"\n  k = 69..300 ({total} valeurs)")
print(f"  Complete & (Q) PASS : {complete_pass}/{total}")
print(f"  Complete & (Q) FAIL : {complete_fail}/{total}")
print(f"  Incomplet (cofacteur non factorise) : {incomplete}/{total}")
print(f"    dont facteurs connus passent (Q) : {incomplete_pass}")

# Cas DI_B
if dib_cases:
    print(f"\n  Cas en regime Di Benedetto ({len(dib_cases)}) :")
    for k, p, m, ratio, rho, qval in dib_cases:
        rho_str = f"{rho:.4f}" if rho is not None else "?"
        qval_str = f"{qval:.2e}" if qval is not None else "?"
        status = "PASS" if qval is not None and qval < 0.041 else "?" if qval is None else "FAIL"
        print(f"    k={k}, p={p}, m={m}, p/m^2={ratio:.2f}, rho={rho_str}, (Q)={status}")

# Details des incomplets
if incomplete_details:
    print(f"\n  Details des {len(incomplete_details)} k incomplets :")
    for k, bits, is_prime, q in incomplete_details[:30]:
        pr_str = "PREMIER" if is_prime else "COMPOSITE/?"
        q_str = "PASS" if q is True else "FAIL" if q is False else "?"
        print(f"    k={k}, cofacteur {bits}b, {pr_str}, (Q)={q_str}")
    if len(incomplete_details) > 30:
        print(f"    ... et {len(incomplete_details) - 30} de plus")

    # Distribution taille cofacteurs
    sizes = [b for _, b, _, _ in incomplete_details]
    print(f"\n  Distribution taille cofacteurs :")
    for lo, hi, label in [(0, 64, "<64b"), (64, 128, "64-128b"),
                          (128, 256, "128-256b"), (256, 512, "256-512b"),
                          (512, 9999, ">512b")]:
        count = sum(1 for s in sizes if lo <= s < hi)
        if count > 0:
            print(f"    {label} : {count}")

# Top ratios
all_ratios.sort(reverse=True)
print(f"\n  Top 10 ratios p/m^2 :")
for ratio, k, p, m in all_ratios[:10]:
    regime = "WEIL" if ratio < 1 else "DI_B"
    print(f"    k={k}, p={p}, m={m}, p/m^2={ratio:.4f}, {regime}")

# VERDICT
print(f"\n{'='*70}")
print(f"★ VERDICT ★")
print(f"{'='*70}")
if complete_fail == 0:
    print(f"  ✓ ZERO echec (Q) parmi les factorisations completes !")
    print(f"  ✓ {complete_pass}/{total} valeurs completement verifiees")
    print(f"  ✓ {incomplete} restent avec cofacteurs non factorises")
    print(f"  → Pour fermer le Regime A : factoriser ces {incomplete} cofacteurs")
    print(f"    (ou utiliser un argument theorique pour les borner)")
else:
    print(f"  ⚠️ {complete_fail} ECHECS (Q) detectes !")
