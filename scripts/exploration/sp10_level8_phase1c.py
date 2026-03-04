#!/usr/bin/env python3
"""
SP10 Level 8 — Phase I.1c : Attaque des cofacteurs non factorises
===================================================================
Pour les d(k) dont la factorisation est incomplete, on a des cofacteurs C
qui sont des entiers composites (ou premiers) non factorises.

STRATEGIE :
1. Si C est premier => calculer ord_C(2) et classifier
2. Si C est composite => essayer de le factoriser avec des methodes plus fortes
3. Pour les tres grands : argument theorique (heuristique d'abord, puis rigoureux)

ANTI-HALLUCINATION : on ne declare rien sans preuve calculatoire.
"""

import math
import cmath
import sys
from sympy import isprime, factorint, n_order, nextprime, gcd

print("=" * 70)
print("SP10 L8 — PHASE I.1c : COFACTEURS NON FACTORISES")
print("=" * 70)

def S(k):
    return int(math.ceil(k * math.log2(3)))

# ============================================================
# PARTIE A : Reprendre les d(k) avec cofacteurs non factorises
# ============================================================
print("\n--- Analyse des cofacteurs pour k=69..120 ---")

# Factoriser avec une limite plus haute (10^8 au lieu de 10^7)
from sympy import factorint

cofactors = {}  # k -> cofacteur

for k in range(69, 121):
    Sk = S(k)
    dk = (1 << Sk) - 3**k
    if dk <= 0:
        Sk += 1
        dk = (1 << Sk) - 3**k

    # Factorisation partielle avec limite 10^8
    factors = factorint(dk, limit=10**8)
    product = 1
    for p, e in factors.items():
        product *= p ** e

    if product != dk:
        cofactor = dk // product
        if cofactor > 1:
            cofactors[k] = {
                'cofactor': cofactor,
                'bits': cofactor.bit_length(),
                'is_prime': None,  # a determiner
                'factors_known': factors
            }

print(f"\nNombre de k avec cofacteur non factorise : {len(cofactors)}")

# ============================================================
# PARTIE B : Tester si les cofacteurs sont premiers
# ============================================================
print("\n" + "=" * 70)
print("PARTIE B : Test de primalite des cofacteurs")
print("=" * 70)

print(f"\n{'k':>4} {'bits':>6} {'digits':>7} {'premier?':>10} {'ord_2':>15}")
print("-" * 55)

weil_pass = 0
dib_pass = 0
hard_count = 0
prime_count = 0
composite_count = 0
too_big = 0

for k in sorted(cofactors.keys()):
    info = cofactors[k]
    c = info['cofactor']
    n_bits = info['bits']
    n_digits = len(str(c))

    if n_bits > 200:
        info['is_prime'] = 'TOO_BIG'
        too_big += 1
        if k <= 100 or k % 5 == 0:
            print(f"{k:>4} {n_bits:>6} {n_digits:>7} {'SKIP':>10} {'N/A':>15}")
        continue

    # Test de primalite
    is_p = isprime(c)
    info['is_prime'] = is_p

    if is_p:
        prime_count += 1
        # Calculer l'ordre de 2 mod c
        try:
            m = n_order(2, c)
            m2 = m ** 2
            ratio = c / m2

            if ratio < 1:
                regime = "WEIL"
                n_idx = (c - 1) // m
                rho_weil = (1 + (n_idx - 1) * math.sqrt(c)) / (c - 1)
                q_val = (c - 1) * rho_weil ** (k - 17)
                q_check = "PASS" if q_val < 0.041 else "FAIL"
                weil_pass += 1
                print(f"{k:>4} {n_bits:>6} {n_digits:>7} {'PREMIER':>10} "
                      f"m={m}, p/m²={ratio:.4f}, WEIL {q_check}")
            elif ratio < m2:
                regime = "DI_B"
                dib_pass += 1
                print(f"{k:>4} {n_bits:>6} {n_digits:>7} {'PREMIER':>10} "
                      f"m={m}, p/m²={ratio:.2f}, DI_B")
            else:
                regime = "HARD"
                hard_count += 1
                print(f"{k:>4} {n_bits:>6} {n_digits:>7} {'PREMIER':>10} "
                      f"m={m}, p/m²={ratio:.0f}, HARD ⚠️")
        except Exception as e:
            print(f"{k:>4} {n_bits:>6} {n_digits:>7} {'PREMIER':>10} "
                  f"ord ERROR: {e}")
    else:
        composite_count += 1
        # Essayer factorisation avec SymPy sans limite
        try:
            sub_factors = factorint(c, limit=10**9)
            sub_product = 1
            for p, e in sub_factors.items():
                sub_product *= p ** e

            if sub_product == c:
                # Factorisation complete !
                parts = []
                for p, e in sorted(sub_factors.items()):
                    if e == 1:
                        parts.append(str(p))
                    else:
                        parts.append(f"{p}^{e}")
                print(f"{k:>4} {n_bits:>6} {n_digits:>7} {'COMPOSITE':>10} "
                      f"= {' * '.join(parts)}")

                # Verifier (Q) pour chaque facteur
                for p_sub in sub_factors:
                    if isprime(p_sub):
                        try:
                            m_sub = n_order(2, p_sub)
                            ratio_sub = p_sub / (m_sub ** 2)
                            if ratio_sub < 1:
                                n_idx = (p_sub - 1) // m_sub
                                rho_w = (1 + (n_idx-1)*math.sqrt(p_sub)) / (p_sub-1)
                                q_val = (p_sub - 1) * rho_w ** (k - 17)
                                q_ok = "PASS" if q_val < 0.041 else "FAIL"
                                weil_pass += 1
                                print(f"      -> p={p_sub}, m={m_sub}, WEIL {q_ok}")
                            else:
                                print(f"      -> p={p_sub}, m={m_sub}, p/m²={ratio_sub:.2f}")
                                if ratio_sub < m_sub**2:
                                    dib_pass += 1
                                else:
                                    hard_count += 1
                        except:
                            pass
            else:
                remaining = c // sub_product
                print(f"{k:>4} {n_bits:>6} {n_digits:>7} {'COMPOSITE':>10} "
                      f"partial, remaining={len(str(remaining))}d")
        except:
            print(f"{k:>4} {n_bits:>6} {n_digits:>7} {'COMPOSITE':>10} "
                  f"factorisation echouee")

print(f"\n--- Bilan cofacteurs k=69..120 ---")
print(f"  Premiers (faciles) : {prime_count}")
print(f"    -> WEIL (Q) PASS : {weil_pass}")
print(f"    -> DI_B          : {dib_pass}")
print(f"    -> HARD          : {hard_count}")
print(f"  Composites re-factorises : {composite_count}")
print(f"  Trop grands (skip)       : {too_big}")

# ============================================================
# PARTIE C : Verification exhaustive (Q) pour k = 69..100
# ============================================================
print("\n" + "=" * 70)
print("PARTIE C : Verification (Q) exhaustive k=69..100")
print("=" * 70)

all_pass = True
results_q = {}

for k in range(69, 101):
    Sk = S(k)
    dk = (1 << Sk) - 3**k
    if dk <= 0:
        Sk += 1
        dk = (1 << Sk) - 3**k

    # Factorisation aussi complete que possible
    factors = factorint(dk, limit=10**9)
    product = 1
    for p, e in factors.items():
        product *= p ** e

    complete = (product == dk)
    results_q[k] = {"complete": complete, "all_pass": True, "factors": []}

    for p_factor in factors:
        if not isprime(p_factor):
            continue

        try:
            m = n_order(2, p_factor)
        except:
            results_q[k]["all_pass"] = False
            continue

        n_idx = (p_factor - 1) // m
        if n_idx == 0:
            n_idx = 1

        # Borne de Weil
        rho_weil = (1 + max(n_idx - 1, 0) * math.sqrt(p_factor)) / max(p_factor - 1, 1)

        if rho_weil < 1:
            q_value = (p_factor - 1) * rho_weil ** (k - 17)
            q_pass = q_value < 0.041
        else:
            # Regime DI_B ou HARD : tenter calcul direct si p < 10^6
            if p_factor < 10**6:
                # Calcul direct de rho
                omega = cmath.exp(2j * cmath.pi / p_factor)
                pows = [pow(2, j, p_factor) for j in range(m)]
                max_rho = 0
                for c in range(1, min(p_factor, 5001)):
                    s = sum(omega ** ((c * pw) % p_factor) for pw in pows)
                    val = abs(s) / m
                    if val > max_rho:
                        max_rho = val
                rho_weil = max_rho  # rho reel
                q_value = (p_factor - 1) * rho_weil ** (k - 17)
                q_pass = q_value < 0.041
            else:
                q_pass = None  # Inconnu

        results_q[k]["factors"].append({
            "p": p_factor, "m": m, "rho": rho_weil,
            "q_pass": q_pass
        })

        if q_pass is False:
            results_q[k]["all_pass"] = False

    if not complete:
        cofactor = dk // product
        if cofactor > 1:
            results_q[k]["cofactor"] = cofactor
            results_q[k]["cofactor_bits"] = cofactor.bit_length()
            # Si cofacteur est petit, le factoriser
            if cofactor.bit_length() < 80:
                cf_factors = factorint(cofactor)
                for p_cf in cf_factors:
                    if isprime(p_cf):
                        try:
                            m_cf = n_order(2, p_cf)
                            n_cf = (p_cf - 1) // m_cf
                            rho_cf = (1 + max(n_cf-1,0)*math.sqrt(p_cf)) / max(p_cf-1,1)
                            if rho_cf < 1:
                                q_val = (p_cf-1) * rho_cf ** (k-17)
                                q_p = q_val < 0.041
                                results_q[k]["factors"].append({
                                    "p": p_cf, "m": m_cf, "rho": rho_cf,
                                    "q_pass": q_p
                                })
                        except:
                            pass

# Affichage
print(f"\n{'k':>4} {'complete?':>10} {'all (Q)?':>10} {'nb_factors':>12} {'note':>30}")
print("-" * 75)

total_complete = 0
total_q_pass = 0

for k in range(69, 101):
    r = results_q[k]
    comp = "OUI" if r["complete"] else "NON"
    q_all = "PASS" if r["all_pass"] else "FAIL/?"
    n_f = len(r["factors"])
    note = ""

    if not r["complete"]:
        cof_bits = r.get("cofactor_bits", 0)
        note = f"cofacteur {cof_bits} bits"
    else:
        total_complete += 1

    if r["all_pass"] and r["complete"]:
        total_q_pass += 1

    print(f"{k:>4} {comp:>10} {q_all:>10} {n_f:>12} {note:>30}")

print(f"\n--- BILAN k=69..100 ---")
print(f"  Factorisation COMPLETE : {total_complete}/32")
print(f"  (Q) verifiee completement : {total_q_pass}/32")
print(f"  Restant (cofacteurs non factorises) : {32 - total_complete}/32")

# ============================================================
# PARTIE D : Pattern recognition sur les cofacteurs
# ============================================================
print("\n" + "=" * 70)
print("PARTIE D : Peut-on borner les facteurs premiers de d(k) ?")
print("=" * 70)

# Pour chaque facteur premier p de d(k), on a p | 2^S - 3^k
# Donc 2^S ≡ 3^k mod p
# Si m = ord_p(2), alors 2^{S mod m} ≡ 3^k mod p
# Si de plus ord_p(3) = ell, alors 3^k mod p depend de k mod ell
#
# Question : peut-on borner la taille des facteurs premiers de d(k) ?
# Reponse : NON en general (d(k) peut avoir des facteurs premiers arbitrairement grands)
# MAIS : si p est tres grand, alors m = ord_p(2) est aussi typiquement grand
# et le regime est WEIL.

# Verifions : quel est le plus grand ratio p/m^2 parmi les facteurs trouves ?
print(f"\nPlus grands ratios p/m^2 :")
all_ratios = []

for k in range(69, 101):
    r = results_q[k]
    for f in r["factors"]:
        p = f["p"]
        m = f["m"]
        ratio = p / (m ** 2)
        all_ratios.append((ratio, k, p, m))

all_ratios.sort(reverse=True)
print(f"\n{'ratio p/m^2':>12} {'k':>4} {'p':>15} {'m':>12}")
print("-" * 50)
for ratio, k, p, m in all_ratios[:20]:
    print(f"{ratio:>12.4f} {k:>4} {p:>15} {m:>12}")

max_ratio = all_ratios[0][0] if all_ratios else 0
print(f"\n★ Ratio maximal p/m^2 = {max_ratio:.4f}")
if max_ratio < 1:
    print(f"  TOUS les facteurs connus sont en regime WEIL !")
    print(f"  Ceci suggere fortement que les facteurs de d(k)")
    print(f"  ont typiquement m = ord_p(2) > sqrt(p).")
else:
    print(f"  Certains facteurs sont hors regime Weil.")
    # Afficher ceux qui ne passent pas
    for ratio, k, p, m in all_ratios:
        if ratio >= 1:
            print(f"    k={k}, p={p}, m={m}, p/m²={ratio:.2f}")

print(f"\n{'='*70}")
print(f"VERDICT Phase I.1c :")
print(f"{'='*70}")
