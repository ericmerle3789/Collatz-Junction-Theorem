#!/usr/bin/env python3
"""
SESSION 10f22 — G-V-R ITERATION 5ter : CAMERA THERMIQUE
Pour k=6891 (seul rebelle restant).

METAPHORE D'ERIC :
  Vision nocturne = n'envoie pas de lumière, amplifie l'existant.
  Caméra thermique = détecte ce que l'objet EMET.

TRADUCTION MATHEMATIQUE :
  Au lieu de bombarder d-1 avec des premiers externes (ultrason),
  EXTRAIRE la signature thermique de d-1 :
  1. Calculer M = partie (S-1)-smooth de d-1 (tous les petits facteurs)
  2. R = (d-1)/M = résidu "chaud" (facteurs GRANDS, > S-1)
  3. Si R > 1 : tester 2^M mod d
     - Si ≢ 1 : l'ordre a un composant dans R, et TOUS les facteurs de R
       ont v_q(C) = 0 (car q > S-1). Donc un de ces facteurs est TEMOIN.
       => ord ∤ C => 2^C ≢ 1 mod d  QED.

C'est la "caméra thermique" : on ne sonde pas avec des sondes externes,
on DETECTE ce que d-1 émet — son résidu après extraction des petits facteurs.
"""
import sys
import math
import time
sys.stdout.reconfigure(line_buffering=True)

k = 6891
S = math.ceil(k * math.log2(3))

print("=" * 70)
print("CAMERA THERMIQUE : EXTRACTION DU RESIDU R DE d-1")
print("=" * 70)

# ================================================================
# T1. CALCULER d-1 ET SES VALUATIONS POUR TOUS PRIMES p ≤ S-1
# ================================================================
print("\nT1. EXTRACTION DE LA PARTIE (S-1)-SMOOTH DE d-1")
print("-" * 50)

# Sieve primes up to S-1
def sieve(n):
    is_p = [True] * (n + 1)
    is_p[0] = is_p[1] = False
    for i in range(2, int(n**0.5) + 1):
        if is_p[i]:
            for j in range(i*i, n + 1, i):
                is_p[j] = False
    return [i for i in range(2, n + 1) if is_p[i]]

primes_up_to_S = sieve(S - 1)
print(f"  {len(primes_up_to_S)} premiers p ≤ {S-1}")

# For each prime p, compute v_p(d-1) using modular arithmetic
# d-1 = 2^S - 3^k - 1
# v_p(d-1) : compute d-1 mod p^e for increasing e

t0 = time.time()
smooth_factors = {}  # p -> v_p(d-1)
M_log2 = 0  # log_2(M) pour tracking

for p in primes_up_to_S:
    # Quick check: does p | (d-1)?
    dm1_mod_p = (pow(2, S, p) - pow(3, k, p) - 1) % p
    if dm1_mod_p != 0:
        continue

    # p divides d-1. Find v_p(d-1).
    v = 0
    pe = 1
    for e in range(1, 100):  # v_p won't exceed 100
        pe *= p
        dm1_mod_pe = (pow(2, S, pe) - pow(3, k, pe) - 1) % pe
        if dm1_mod_pe != 0:
            v = e - 1
            break
    else:
        v = 99  # shouldn't happen

    if v > 0:
        smooth_factors[p] = v
        M_log2 += v * math.log2(p)

t1 = time.time()

print(f"  Extraction en {t1-t0:.2f}s")
print(f"\n  Facteurs premiers de d-1 parmi p ≤ {S-1} :")
print(f"  {len(smooth_factors)} premiers distincts divisant d-1")
print(f"\n  Détail (premiers avec v_p > 0) :")
for p, v in sorted(smooth_factors.items()):
    print(f"    p={p}: v_p(d-1) = {v}")

print(f"\n  log_2(M) = {M_log2:.1f} (M = partie {S-1}-smooth de d-1)")
print(f"  log_2(d-1) ≈ {S * math.log2(2):.1f}")
print(f"  log_2(R) = log_2(d-1) - log_2(M) ≈ {S - M_log2:.1f}")

if M_log2 < S - 1:
    print(f"\n  ★ R = (d-1)/M > 1 ! Le résidu est NON TRIVIAL.")
    print(f"    R a environ {S - M_log2:.0f} bits.")
    print(f"    Tous les facteurs premiers de R sont > {S-1}.")
    print(f"    => Pour tout q | R : v_q(C) = 0 GARANTI.")
else:
    print(f"\n  ⚠ R ≈ 1 : d-1 est {S-1}-smooth. Approche thermique inapplicable.")

# ================================================================
# T2. VERIFICATION : NOUVELLE VERIF DES PRIMES 10001-10921
# ================================================================
print("\n" + "=" * 70)
print("T2. VERIFICATION GAP : PRIMES 10001 ≤ p ≤ 10921")
print("=" * 70)

# Iter 5 checked up to 10000 only. Check 10001-10921 for witnesses.
print(f"\n  Ces primes sont ≤ S-1 = {S-1}, donc v_p(C) peut être > 0.")
print(f"  Mais vérifions s'il y a un témoin dans ce gap.\n")

# Need d for modular exponentiation
print("  Calcul de d ... ", end="", flush=True)
t2 = time.time()
d = pow(2, S) - pow(3, k)
dm1 = d - 1
t3 = time.time()
print(f"fait ({t3-t2:.2f}s)")

def v_p_val(n, p):
    if n == 0: return float('inf')
    v = 0
    while n % p == 0:
        v += 1
        n //= p
    return v

def v_p_binom(n, k_choose, p):
    def v_p_fact(m):
        s = 0; pk = p
        while pk <= m:
            s += m // pk
            pk *= p
        return s
    return v_p_fact(n) - v_p_fact(k_choose) - v_p_fact(n - k_choose)

gap_primes = [p for p in primes_up_to_S if 10000 < p <= S - 1]
print(f"  {len(gap_primes)} premiers dans le gap [10001, {S-1}]")

gap_witnesses = []
for p in gap_primes:
    if p not in smooth_factors:
        continue  # p ne divise pas d-1, skip

    vp_dm1 = smooth_factors[p]
    vp_C = v_p_binom(S - 1, k - 1, p)

    if vp_dm1 <= vp_C:
        continue  # Can't be witness

    # Check v_p(Q)
    vp_Q = 0
    for e in range(1, vp_dm1 + 1):
        if pow(2, dm1 // (p**e), d) == 1:
            vp_Q += 1
        else:
            break

    vp_ord = vp_dm1 - vp_Q
    if vp_ord > vp_C:
        gap_witnesses.append((p, vp_ord, vp_C, vp_dm1, vp_Q))
        print(f"  ★ TEMOIN DANS LE GAP : p={p}")
        print(f"    v_p(ord)={vp_ord} > v_p(C)={vp_C}")
        print(f"    [v_p(d-1)={vp_dm1}, v_p(Q)={vp_Q}]")

if not gap_witnesses:
    print(f"  Aucun témoin dans le gap [10001, {S-1}].")

# ================================================================
# T3. CALCUL EXACT DE M ET R, PUIS TEST 2^M mod d
# ================================================================
print("\n" + "=" * 70)
print("T3. CAMERA THERMIQUE : TEST 2^M mod d")
print("=" * 70)

# Compute M = product of p^{v_p(d-1)} for all p ≤ S-1
print(f"\n  Calcul de M = ∏ p^v_p(d-1) pour p ≤ {S-1} ...")
t4 = time.time()
M = 1
for p, v in smooth_factors.items():
    M *= p ** v
t5 = time.time()
print(f"  M calculé en {t5-t4:.3f}s")
print(f"  M a {M.bit_length()} bits")

# Compute R = (d-1) / M
print(f"\n  Calcul de R = (d-1) / M ...")
R, remainder = divmod(dm1, M)
print(f"  Reste de la division : {remainder}")
if remainder == 0:
    print(f"  ★ M | (d-1) exactement (pas de reste)")
    print(f"  R = {R if R.bit_length() < 100 else f'(nombre de {R.bit_length()} bits)'}")
    print(f"  R a {R.bit_length()} bits")
    if R == 1:
        print(f"  ⚠ R = 1 : d-1 est exactement {S-1}-smooth. Caméra thermique inapplicable.")
    else:
        print(f"  ★★ R > 1 : d-1 a des facteurs > {S-1} !")
        print(f"  Tous les facteurs premiers de R sont > {S-1} (donc > S-1).")
        print(f"  => Pour tout q | R : v_q(C) = 0 GARANTI.")
        print(f"\n  Test : 2^M mod d ...")
        print(f"  Si 2^M ≢ 1 mod d : ord a un composant dans R")
        print(f"    => un facteur de R est témoin (v_q(C) = 0)")
        print(f"    => ord ∤ C => 2^C ≢ 1 mod d  QED")
        print(f"\n  Calcul de 2^M mod d (M a {M.bit_length()} bits, d a {d.bit_length()} bits)...")
        t6 = time.time()
        result = pow(2, M, d)
        t7 = time.time()
        print(f"  Temps : {t7-t6:.1f}s")
        if result == 1:
            print(f"\n  ⚠ 2^M ≡ 1 mod d")
            print(f"  L'ordre DIVISE M. Donc ord est {S-1}-smooth.")
            print(f"  Les facteurs de R ne contribuent PAS à l'ordre.")
            print(f"  La caméra thermique montre que la 'chaleur' (R) n'est pas dans l'ordre.")
        else:
            print(f"\n  ★★★★★ 2^M ≢ 1 mod d ★★★★★")
            print(f"  L'ORDRE NE DIVISE PAS M !")
            print(f"  => ord a au moins un facteur premier q > {S-1}")
            print(f"  => v_q(C) = 0 (car q > S-1 et C = binom(S-1, k-1))")
            print(f"  => v_q(ord) ≥ 1 > 0 = v_q(C)")
            print(f"  => ord ∤ C")
            print(f"  => 2^C ≢ 1 mod d")
            print(f"\n  ★★★ k={k} EST RESOLU PAR CAMERA THERMIQUE ★★★")
            print(f"  SCORE : 19/19 INCONDITIONNEL !")
else:
    print(f"  ⚠ M ne divise pas d-1 exactement (reste = {remainder})")
    print(f"  Erreur dans le calcul de M. Vérification nécessaire.")

# ================================================================
# T4. SYNTHESE
# ================================================================
print("\n" + "=" * 70)
print("T4. SYNTHESE CAMERA THERMIQUE")
print("=" * 70)

print(f"""
  METHODE : Extraire la partie {S-1}-smooth M de d-1,
  calculer R = (d-1)/M, tester 2^M mod d.

  Si 2^M ≢ 1 mod d :
    ord ∤ M, donc ord a un facteur q | R avec q > {S-1}.
    Comme C = binom({S-1}, {k-1}) n'a que des facteurs ≤ {S-1} :
    v_q(C) = 0 < v_q(ord) ≥ 1.
    Donc ord ∤ C. CQFD.

  C'est la CAMERA THERMIQUE d'Eric :
  on n'envoie pas de lumière (pas de premier externe),
  on détecte ce que d-1 EMET (son résidu R)
  et on vérifie que l'ordre y participe.
""")

print("=" * 70)
print("FIN ITERATION 5ter : CAMERA THERMIQUE")
print("=" * 70)
