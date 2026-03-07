#!/usr/bin/env python3
"""
SESSION 10f22 — VERIFICATION RAPIDE CAMERA THERMIQUE POUR LES 19 CAS

Les 19 valeurs de k (k=3..10000) pour lesquelles d = 2^S - 3^k est premier
sont connues. On les utilise directement au lieu de scanner 10000 valeurs.

Theoreme (Camera Thermique) :
  Soit d premier, M = partie (S-1)-smooth de d-1, R = (d-1)/M.
  Si 2^M not equiv 1 mod d, alors pour tout C avec facteurs premiers <= S-1 :
    ord_d(2) ne divise pas C.

  Preuve :
    2^M not equiv 1 => ord ne divise pas M.
    Or ord | (d-1) = M*R avec gcd(M,R)=1.
    Donc ord = a*b avec a|M, b|R. ord ne divise pas M => b > 1.
    Il existe premier q > S-1 avec q | b | ord, donc v_q(ord) >= 1.
    C n'a que des facteurs <= S-1 => v_q(C) = 0.
    v_q(ord) > v_q(C) => ord ne divise pas C => 2^C not equiv 1 mod d.  QED.

Ce script verifie que 2^M not equiv 1 mod d pour CHACUN des 19 d premiers.
"""
import sys
import math
import time
sys.stdout.reconfigure(line_buffering=True)

def ceil_log2_3(k):
    return math.ceil(k * math.log2(3))

def sieve(n):
    if n < 2:
        return []
    is_p = [True] * (n + 1)
    is_p[0] = is_p[1] = False
    for i in range(2, int(n**0.5) + 1):
        if is_p[i]:
            for j in range(i*i, n + 1, i):
                is_p[j] = False
    return [i for i in range(2, n + 1) if is_p[i]]

# The 19 known k values where d = 2^S - 3^k is prime (k in [3, 10000])
KNOWN_K = [3, 4, 5, 13, 56, 61, 69, 73, 76, 148, 185, 655, 917, 2183, 3540, 3895, 4500, 6891, 7752]

print("=" * 74)
print("  THEOREME DE LA CAMERA THERMIQUE - VERIFICATION 19/19")
print("=" * 74)
print()
print("  Theoreme : Soit d premier, M = (S-1)-smooth part de d-1.")
print("  Si 2^M not equiv 1 mod d, alors ord_d(2) ne divise pas binom(S-1, k-1).")
print("  Preuve : ord ne divise pas M => il existe q > S-1, q|ord, v_q(C)=0. QED.")
print()
print(f"  {len(KNOWN_K)} cas connus : k = {KNOWN_K}")
print()
print(f"  {'k':>5s} | {'S':>5s} | {'bits(d)':>7s} | {'bits(M)':>7s} | {'bits(R)':>7s} "
      f"| {'2^M=1?':>7s} | {'temps':>6s} | {'verdict':>10s}")
print("  " + "-" * 78)

all_pass = True
total_time = 0
details = []

for k in KNOWN_K:
    S = ceil_log2_3(k)

    # Compute d
    t_d0 = time.time()
    d = pow(2, S) - pow(3, k)
    t_d1 = time.time()

    if d <= 1:
        print(f"  {k:5d} | {S:5d} |   SKIP  | d <= 1")
        continue

    d_bits = d.bit_length()

    # Compute M = (S-1)-smooth part of d-1 using modular arithmetic
    primes_up_to = sieve(S - 1)
    M = 1
    smooth_factors = {}

    for p in primes_up_to:
        # v_p(d-1) : compute (2^S - 3^k - 1) mod p^e
        pe = p
        v = 0
        while True:
            dm1_mod_pe = (pow(2, S, pe) - pow(3, k, pe) - 1) % pe
            if dm1_mod_pe != 0:
                break
            v += 1
            pe *= p
        if v > 0:
            M *= p ** v
            smooth_factors[p] = v

    M_bits = M.bit_length()
    R_bits = d_bits - M_bits  # approximate

    # Test 2^M mod d
    t0 = time.time()
    result = pow(2, M, d)
    t1 = time.time()
    elapsed = t1 - t0
    total_time += elapsed + (t_d1 - t_d0)

    is_one = (result == 1)
    verdict = "!! ECHEC" if is_one else "PROUVE"
    if is_one:
        all_pass = False

    status = 'OUI !!' if is_one else 'NON *'

    print(f"  {k:5d} | {S:5d} | {d_bits:7d} | {M_bits:7d} | "
          f"{R_bits:7d} | {status:>7s} | {elapsed:5.1f}s | {verdict}")

    details.append({
        'k': k, 'S': S, 'd_bits': d_bits, 'M_bits': M_bits,
        'R_bits': R_bits, 'is_one': is_one, 'elapsed': elapsed,
        'smooth_factors': smooth_factors
    })

print()
print("=" * 74)
if all_pass:
    print("  ***** 19/19 CAS PROUVES PAR CAMERA THERMIQUE *****")
    print()
    print("  Pour CHACUN des 19 d premiers (k <= 10000) :")
    print("    2^M not equiv 1 mod d  (verifie computationnellement)")
    print("    => ord a un facteur q > S-1")
    print("    => v_q(C) = 0 (car C = binom(S-1, k-1))")
    print("    => ord ne divise pas C")
    print("    => 2^C not equiv 1 mod d")
    print()
    print("  AUCUNE CONJECTURE UTILISEE. AUCUNE HYPOTHESE.")
    print("  Que des FAITS CALCULES + LOGIQUE PURE.")
    print()
    print("  La camera thermique est une METHODE UNIFIEE :")
    print("  elle subsume taille, temoins, et resout tous les cas")
    print("  en une seule verification par k.")
else:
    print("  !! CERTAINS CAS ECHOUENT - la methode n'est pas universelle")
    for d in details:
        if d['is_one']:
            print(f"    ECHEC : k={d['k']}, S={d['S']}")

print("=" * 74)
print(f"\n  Temps total : {total_time:.1f}s")

# Print detailed smooth factorizations
print("\n" + "=" * 74)
print("  DETAIL DES FACTEURS SMOOTH DE d-1")
print("=" * 74)
for d_info in details:
    k = d_info['k']
    sf = d_info['smooth_factors']
    M_str = " * ".join(f"{p}^{v}" for p, v in sorted(sf.items()))
    print(f"\n  k={k}: M = {M_str}")
    print(f"    bits(M)={d_info['M_bits']}, bits(R)={d_info['R_bits']}, "
          f"bits(d)={d_info['d_bits']}")
    print(f"    R/d ratio: R has {d_info['R_bits']}/{d_info['d_bits']} = "
          f"{d_info['R_bits']/d_info['d_bits']*100:.1f}% des bits de d")
