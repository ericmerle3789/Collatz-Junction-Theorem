#!/usr/bin/env python3
"""
SESSION 10f26b — EXTENSION CATALOGUE d(k) PREMIERS
Scanne k = 10001..30000 pour trouver de nouveaux d(k) = 2^S - 3^k premiers.
Pour chaque nouveau d premier: Camera Thermique + analyse partielle.

Utilise gmpy2 pour la performance (test de primalite rapide).
"""
import sys
import math
import time
import json

sys.stdout.reconfigure(line_buffering=True)

try:
    import gmpy2
    from gmpy2 import mpz, is_prime as gmp_is_prime, powmod
    print("  gmpy2 charge ✓")
except ImportError:
    print("  ERREUR: gmpy2 requis pour ce script")
    sys.exit(1)

def ceil_log2_3(k):
    return math.ceil(k * math.log2(3))

# ======================================================================
# CONFIGURATION
# ======================================================================
K_START = 10001
K_END = 30000
CHECKPOINT_INTERVAL = 1000  # Afficher progression chaque 1000 k
RESULTS_FILE = "/Users/ericmerle/Documents/Collatz-Junction-Theorem/research_protocol/artin_extend_10f26b.json"

# Les 19 connus
KNOWN_K = [3, 4, 5, 13, 56, 61, 69, 73, 76, 148, 185, 655, 917,
           2183, 3540, 3895, 4500, 6891, 7752]

print("=" * 78)
print(f"SESSION 10f26b — SCAN d(k) PREMIERS, k ∈ [{K_START}, {K_END}]")
print("=" * 78)
print()

t_global = time.time()
new_primes = []
total_tested = 0
last_checkpoint = K_START

for k in range(K_START, K_END + 1):
    S = ceil_log2_3(k)
    d = pow(2, S) - pow(3, k)

    if d <= 1:
        continue

    total_tested += 1
    is_p = bool(gmp_is_prime(d))

    if is_p:
        d_bits = d.bit_length()
        elapsed = time.time() - t_global

        # Camera Thermique rapide
        dm1 = d - 1
        M = 1
        temp = dm1
        p = 2
        while p <= S - 1:
            while temp % p == 0:
                M *= p
                temp //= p
            p += 1 if p == 2 else 2
        R = temp
        M_bits = M.bit_length()
        R_bits = R.bit_length()
        thermal = (powmod(2, M, d) != 1)

        print(f"  *** NOUVEAU d PREMIER: k={k}, S={S}, d={d_bits}b ***")
        print(f"      M={M_bits}b, R={R_bits}b ({R_bits/d_bits*100:.1f}%), "
              f"Thermal={'PASS ✓' if thermal else 'FAIL ✗'}")
        print(f"      Temps cumule: {elapsed:.1f}s")
        sys.stdout.flush()

        new_primes.append({
            "k": k, "S": S, "d_bits": d_bits,
            "M_bits": M_bits, "R_bits": R_bits,
            "R_ratio": round(R_bits / d_bits, 4),
            "thermal_pass": thermal,
        })

    # Checkpoint
    if k >= last_checkpoint + CHECKPOINT_INTERVAL:
        elapsed = time.time() - t_global
        rate = total_tested / elapsed if elapsed > 0 else 0
        print(f"  [checkpoint k={k}] teste={total_tested}, "
              f"nouveaux={len(new_primes)}, "
              f"rate={rate:.1f} k/s, temps={elapsed:.1f}s")
        sys.stdout.flush()
        last_checkpoint = k

# ======================================================================
# SYNTHESE
# ======================================================================
elapsed_total = time.time() - t_global
print("\n" + "=" * 78)
print("SYNTHESE")
print("=" * 78)

print(f"\n  Range: k ∈ [{K_START}, {K_END}]")
print(f"  Testes: {total_tested}")
print(f"  Nouveaux d premiers: {len(new_primes)}")
print(f"  Temps total: {elapsed_total:.1f}s")
print(f"  Rate: {total_tested/elapsed_total:.1f} k/s")

if new_primes:
    print(f"\n  Nouveaux k:")
    all_thermal = True
    for p in new_primes:
        print(f"    k={p['k']}, S={p['S']}, d={p['d_bits']}b, "
              f"Thermal={'PASS' if p['thermal_pass'] else 'FAIL'}")
        if not p['thermal_pass']:
            all_thermal = False
    print(f"\n  Camera Thermique: {'TOUS PASS ✓' if all_thermal else 'CERTAINS FAIL ✗'}")
else:
    print("\n  Aucun nouveau d premier dans cette plage.")

# Densite
total_k_tested = K_END - K_START + 1
print(f"\n  Densite heuristique (k ≤ 10000): {len(KNOWN_K)}/{10000} = {len(KNOWN_K)/10000*100:.2f}%")
if len(new_primes) > 0:
    print(f"  Densite observee (k ∈ [{K_START}, {K_END}]): {len(new_primes)}/{total_k_tested} = {len(new_primes)/total_k_tested*100:.4f}%")
else:
    print(f"  Densite observee (k ∈ [{K_START}, {K_END}]): 0/{total_k_tested}")

# Heuristique: P(d premier) ≈ 1/(S·ln2) ≈ 1/(k·(log₂3)·ln2) ≈ 1/(1.1·k)
# Nombre attendu dans [K_START, K_END]:
expected = sum(1.0 / (1.1 * k * math.log(2) * math.log2(3)) for k in range(K_START, K_END + 1))
print(f"  Nombre attendu (heuristique 1/ln(d)): {expected:.2f}")

# Catalogue total
all_k = sorted(KNOWN_K + [p['k'] for p in new_primes])
print(f"\n  CATALOGUE TOTAL: {len(all_k)} d premiers")
print(f"  k = {all_k}")

# Sauvegarder
results = {
    "range": [K_START, K_END],
    "new_primes": new_primes,
    "total_tested": total_tested,
    "elapsed": elapsed_total,
    "all_k": all_k,
    "n_total": len(all_k),
}
try:
    with open(RESULTS_FILE, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\n  Resultats sauves: {RESULTS_FILE}")
except Exception as e:
    print(f"\n  Erreur sauvegarde: {e}")

print("\n" + "=" * 78)
print("FIN SESSION 10f26b")
print("=" * 78)
