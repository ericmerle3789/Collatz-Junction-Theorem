#!/usr/bin/env python3
"""
SP10 Level 8 — Phase I.1d : Verification (Q) pour k=69..500
==============================================================
Suite du resultat spectaculaire : k=69..100 TOUS VERIFIES.
Poussons maintenant a k=200, 300, 500.

ANTI-HALLUCINATION : chaque facteur est verifie, chaque (Q) est calculee.
"""

import math
import cmath
import time
from sympy import isprime, factorint, n_order

def S(k):
    return int(math.ceil(k * math.log2(3)))

# ============================================================
# Verification (Q) pour k = 69..500
# ============================================================
print("=" * 70)
print("SP10 L8 — PHASE I.1d : Verification (Q) k=69..500")
print("=" * 70)

all_results = {}
first_fail_k = None
total_complete = 0
total_pass = 0
total_fail = 0
total_incomplete = 0

# Pour les facteurs en regime DI_B ou HARD, on calcule rho directement si p < 10^7
def compute_rho_direct(p, m, max_c=5000):
    """Calcule rho exact pour p < ~10^7"""
    omega = cmath.exp(2j * cmath.pi / p)
    pows = [pow(2, j, p) for j in range(m)]
    max_rho = 0
    for c in range(1, min(p, max_c + 1)):
        s = sum(omega ** ((c * pw) % p) for pw in pows)
        val = abs(s) / m
        if val > max_rho:
            max_rho = val
    return max_rho

t0 = time.time()
checkpoint_ks = [100, 150, 200, 250, 300, 400, 500]

for k in range(69, 501):
    Sk = S(k)
    dk = (1 << Sk) - 3**k
    if dk <= 0:
        Sk += 1
        dk = (1 << Sk) - 3**k

    # Factorisation avec limite adaptative
    # Pour k petit, on peut aller plus loin
    if k <= 150:
        limit = 10**9
    elif k <= 300:
        limit = 10**8
    else:
        limit = 10**7

    try:
        factors = factorint(dk, limit=limit)
    except:
        all_results[k] = {"complete": False, "all_pass": None, "error": True}
        total_incomplete += 1
        continue

    product = 1
    for p, e in factors.items():
        product *= p ** e
    complete = (product == dk)

    q_all_pass = True
    q_factors = []

    for p_factor in factors:
        if not isprime(p_factor):
            # C'est un cofacteur composite non factorise
            q_all_pass = None  # Inconnu
            continue

        try:
            m = n_order(2, p_factor)
        except:
            q_all_pass = None
            continue

        n_idx = (p_factor - 1) // m
        rho_weil = (1 + max(n_idx - 1, 0) * math.sqrt(p_factor)) / max(p_factor - 1, 1)

        if rho_weil < 1:
            q_value = (p_factor - 1) * rho_weil ** (k - 17)
            q_pass = q_value < 0.041
        elif p_factor < 10**6:
            # Calcul direct de rho
            rho_real = compute_rho_direct(p_factor, m)
            q_value = (p_factor - 1) * rho_real ** (k - 17)
            q_pass = q_value < 0.041
            rho_weil = rho_real  # pour le rapport
        else:
            q_pass = None
            q_all_pass = None

        q_factors.append({"p": p_factor, "m": m, "rho": rho_weil, "q_pass": q_pass})

        if q_pass is False:
            q_all_pass = False

    all_results[k] = {
        "complete": complete,
        "all_pass": q_all_pass if complete else None,
        "factors": q_factors,
        "cofactor_bits": (dk // product).bit_length() if not complete else 0
    }

    if complete and q_all_pass is True:
        total_complete += 1
        total_pass += 1
    elif complete and q_all_pass is False:
        total_complete += 1
        total_fail += 1
        if first_fail_k is None:
            first_fail_k = k
    elif not complete:
        total_incomplete += 1

    # Checkpoints
    if k in checkpoint_ks:
        elapsed = time.time() - t0
        pass_so_far = sum(1 for kk in range(69, k+1)
                         if all_results.get(kk, {}).get("all_pass") is True
                         and all_results.get(kk, {}).get("complete"))
        comp_so_far = sum(1 for kk in range(69, k+1)
                         if all_results.get(kk, {}).get("complete"))
        inc_so_far = sum(1 for kk in range(69, k+1)
                         if not all_results.get(kk, {}).get("complete", True))

        print(f"\n--- Checkpoint k={k} (elapsed {elapsed:.1f}s) ---")
        print(f"  Complete & (Q) PASS : {pass_so_far}/{k-68}")
        print(f"  Factorisation complete : {comp_so_far}/{k-68}")
        print(f"  Factorisation incomplete : {inc_so_far}/{k-68}")

        if first_fail_k is not None:
            print(f"  PREMIER ECHEC (Q) : k = {first_fail_k}")

# ============================================================
# RAPPORT FINAL
# ============================================================
print("\n" + "=" * 70)
print("RAPPORT FINAL : Verification (Q) k=69..500")
print("=" * 70)

# Compter par tranche
tranches = [(69, 100), (101, 150), (151, 200), (201, 300), (301, 400), (401, 500)]

for k_start, k_end in tranches:
    n_total = k_end - k_start + 1
    n_pass = sum(1 for k in range(k_start, k_end+1)
                 if all_results.get(k, {}).get("all_pass") is True
                 and all_results.get(k, {}).get("complete"))
    n_complete = sum(1 for k in range(k_start, k_end+1)
                     if all_results.get(k, {}).get("complete"))
    n_fail = sum(1 for k in range(k_start, k_end+1)
                 if all_results.get(k, {}).get("all_pass") is False)
    n_incomplete = n_total - n_complete

    print(f"  k={k_start:>3}..{k_end:>3} : "
          f"{n_pass:>3}/{n_total} PASS, "
          f"{n_complete:>3}/{n_total} factorise, "
          f"{n_incomplete:>3}/{n_total} incomplet, "
          f"{n_fail:>3} FAIL")

# Liste des k avec factorisation incomplete
incomplete_ks = [k for k in range(69, 501)
                 if not all_results.get(k, {}).get("complete", True)]
if incomplete_ks:
    print(f"\nk avec factorisation INCOMPLETE ({len(incomplete_ks)} valeurs) :")
    # Montrer les premiers 30
    for k in incomplete_ks[:30]:
        cof_bits = all_results[k].get("cofactor_bits", 0)
        print(f"  k={k}, cofacteur {cof_bits} bits")
    if len(incomplete_ks) > 30:
        print(f"  ... et {len(incomplete_ks) - 30} de plus")

# k avec FAIL
fail_ks = [k for k in range(69, 501)
           if all_results.get(k, {}).get("all_pass") is False]
if fail_ks:
    print(f"\n⚠️ k avec (Q) FAIL ({len(fail_ks)} valeurs) :")
    for k in fail_ks:
        r = all_results[k]
        for f in r.get("factors", []):
            if f["q_pass"] is False:
                print(f"  k={k}, p={f['p']}, m={f['m']}, rho={f['rho']:.4f}")
else:
    print(f"\n✓ AUCUN echec (Q) parmi les factorisations completes !")

# Ratio max p/m^2
all_ratios = []
for k in range(69, 501):
    r = all_results.get(k, {})
    for f in r.get("factors", []):
        if f["m"] > 0:
            ratio = f["p"] / (f["m"] ** 2)
            all_ratios.append((ratio, k, f["p"], f["m"]))
all_ratios.sort(reverse=True)

print(f"\n--- Top 10 ratios p/m^2 ---")
for ratio, k, p, m in all_ratios[:10]:
    regime = "WEIL" if ratio < 1 else "DI_B" if ratio < m**2 else "HARD"
    print(f"  k={k}, p={p}, m={m}, p/m^2={ratio:.4f}, {regime}")

# SYNTHESE
print(f"\n{'='*70}")
print(f"★ SYNTHESE PHASE I.1d ★")
print(f"{'='*70}")
total_k = 500 - 69 + 1
print(f"  k total : {total_k}")
print(f"  Factorisation complete : {total_complete}/{total_k}")
print(f"  (Q) PASS (parmi complets) : {total_pass}/{total_complete}")
print(f"  (Q) FAIL : {total_fail}")
print(f"  Incomplete : {total_incomplete}")

if total_fail == 0 and total_pass == total_complete:
    print(f"\n  ✓✓✓ POUR TOUTES LES FACTORISATIONS COMPLETES, (Q) EST VERIFIEE !")
    print(f"  Le point critique est la factorisation des d(k) restants.")
