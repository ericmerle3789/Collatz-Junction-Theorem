#!/usr/bin/env python3
"""
SESSION 10f22 — G-V-R ITERATION 5bis : ULTRASON
Pour k=6891 (seul rebelle), chercher un prime q > S-1 = 10921
tel que q | (d-1) et q ∤ Q.

ARGUMENT THEORIQUE (IRONCLAD) :
  C = binom(S-1, k-1). Tout facteur premier de binom(n,k) est ≤ n.
  Donc pour q > S-1 : v_q(C) = 0 TOUJOURS.

  Si q | (d-1) et 2^{(d-1)/q} ≢ 1 mod d (i.e. q ∤ Q) :
    v_q(ord) = v_q(d-1) ≥ 1 > 0 = v_q(C)
    => q est prime témoin => ord ∤ C => 2^C ≢ 1 mod d  QED.

C'est l'"ultrason" d'Eric : une fréquence AU-DELA du spectre audible
de C (premiers ≤ S-1), où C est "sourd" (v_q(C) = 0).

STRATEGIE :
  1. Scanner les premiers q > 10921 pour trouver q | (d-1)
     Condition : 2^S ≡ 3^k + 1 (mod q)  [RAPIDE : O(log S) par prime]
  2. Pour chaque hit, vérifier 2^{(d-1)/q} mod d ≢ 1
     [LENT : exponentiation modulaire ~10917 bits, mais faisable]
"""
import sys
import math
import time
sys.stdout.reconfigure(line_buffering=True)

k = 6891
S = math.ceil(k * math.log2(3))
print(f"k = {k}, S = {S}, S-1 = {S-1}")
print(f"C = binom({S-1}, {k-1}) n'a que des facteurs premiers ≤ {S-1}")
print(f"Tout premier q > {S-1} divisant d-1 a v_q(C) = 0 GARANTI.\n")

# ================================================================
# U1. ARGUMENT THEORIQUE
# ================================================================
print("=" * 70)
print("U1. ARGUMENT THEORIQUE : POURQUOI q > S-1 EST UN 'ULTRASON'")
print("=" * 70)
print(f"""
  C = binom(n, k) = n! / (k! (n-k)!)
  Facteurs premiers de n! : tous ≤ n.
  Donc facteurs premiers de binom(n,k) : tous ≤ n.

  Pour notre cas : n = S-1 = {S-1}, k = {k-1}.
  => Tout premier q > {S-1} a v_q(C) = 0.

  Si q | (d-1) et q ∤ Q :
    v_q(ord) = v_q(d-1) ≥ 1
    v_q(C) = 0
    => v_q(ord) > v_q(C) : q est TEMOIN
    => ord ∤ C => 2^C ≢ 1 mod d  QED.

  Note : Q_pred = 3 pour k=6891. Si Q = 3, alors tout q > 3
  avec q | (d-1) satisfait q ∤ Q automatiquement.
  Mais on vérifie DIRECTEMENT 2^{{(d-1)/q}} mod d ≢ 1
  (ne dépend PAS de Q_pred).
""")

# ================================================================
# U2. CALCUL DE d ET d-1
# ================================================================
print("=" * 70)
print("U2. CALCUL DE d ET d-1")
print("=" * 70)

t0 = time.time()
d = pow(2, S) - pow(3, k)
dm1 = d - 1
t1 = time.time()
print(f"\n  d = 2^{S} - 3^{k}")
print(f"  d a {d.bit_length()} bits ({len(str(d))} chiffres)")
print(f"  Calcul en {t1-t0:.2f}s")

# Vérification rapide de primalité (Fermat)
print(f"\n  Test de primalité (Fermat bases 2,3,5) :")
for base in [2, 3, 5]:
    t2 = time.time()
    r = pow(base, dm1, d)
    t3 = time.time()
    print(f"    {base}^(d-1) mod d = {'1 ✓' if r == 1 else f'{r} ✗'} ({t3-t2:.2f}s)")

# ================================================================
# U3. RECHERCHE DE q | (d-1) AVEC q > S-1
# ================================================================
print("\n" + "=" * 70)
print("U3. RECHERCHE DE PREMIERS q > S-1 DIVISANT d-1")
print("=" * 70)

def sieve_range(lo, hi):
    """Crible d'Eratosthène pour [lo, hi]."""
    if lo < 2:
        lo = 2
    size = hi - lo + 1
    is_p = [True] * size
    # Crible par petits premiers
    p = 2
    while p * p <= hi:
        # Premier multiple de p >= lo
        start = ((lo + p - 1) // p) * p
        if start == p:
            start += p
        for j in range(start - lo, size, p):
            is_p[j] = False
        p += 1
    return [lo + i for i in range(size) if is_p[i]]

# Phase 1 : Scanner les premiers q ∈ (S-1, X] pour q | (d-1)
# Condition : 2^S ≡ 3^k + 1 (mod q)
# Ceci est RAPIDE : pow(2, S, q) et pow(3, k, q) sont O(log(S)·log(q)²)

print(f"\n  Condition pour q | (d-1) : 2^{S} ≡ 3^{k} + 1 (mod q)")
print(f"  Ceci est rapide à vérifier pour chaque premier q.\n")

# Scan by batches
batch_size = 100000
min_q = S  # S-1+1 = S = 10922
max_q = 10_000_000  # Scan up to 10M

print(f"  Scan : premiers q ∈ ({min_q}, {max_q}]")
print(f"  Par lots de {batch_size}\n")

hits = []
total_primes_checked = 0
t_start = time.time()

lo = min_q + 1
while lo <= max_q:
    hi = min(lo + batch_size - 1, max_q)
    primes_batch = sieve_range(lo, hi)
    total_primes_checked += len(primes_batch)

    for q in primes_batch:
        # Check q | (d-1) : 2^S ≡ 3^k + 1 mod q
        lhs = pow(2, S, q)
        rhs = (pow(3, k, q) + 1) % q
        if lhs == rhs:
            hits.append(q)
            elapsed = time.time() - t_start
            print(f"  ★ HIT : q = {q} divise d-1 ! "
                  f"({total_primes_checked} premiers testés en {elapsed:.1f}s)")

    lo = hi + 1

    # Progress every 500K
    if total_primes_checked % 500000 < batch_size:
        elapsed = time.time() - t_start
        rate = total_primes_checked / elapsed if elapsed > 0 else 0
        print(f"    ... {total_primes_checked} premiers testés, "
              f"{len(hits)} hits, {elapsed:.1f}s ({rate:.0f} primes/s)")

t_scan = time.time() - t_start
print(f"\n  Scan terminé : {total_primes_checked} premiers testés en {t_scan:.1f}s")
print(f"  Hits (q | d-1, q > {min_q}) : {len(hits)}")
if hits:
    print(f"  Premiers hits : {hits[:10]}")

# ================================================================
# U4. VERIFICATION : CHAQUE HIT EST-IL UN TEMOIN ?
# ================================================================
if hits:
    print("\n" + "=" * 70)
    print("U4. VERIFICATION DES TEMOINS (2^{(d-1)/q} mod d ≢ 1 ?)")
    print("=" * 70)

    for q in hits[:5]:  # Test first 5 hits
        print(f"\n  q = {q} :")
        print(f"    v_q(d-1) ≥ 1 (car q | d-1)")
        print(f"    v_q(C) = 0 (car q > S-1 = {S-1})")

        # Compute v_q(d-1)
        temp = dm1
        vq = 0
        while temp % q == 0:
            vq += 1
            temp //= q
        print(f"    v_q(d-1) = {vq}")

        # Check 2^{(d-1)/q} mod d
        exp = dm1 // q
        print(f"    Calcul de 2^((d-1)/{q}) mod d ... ", end="", flush=True)
        t4 = time.time()
        r = pow(2, exp, d)
        t5 = time.time()

        if r == 1:
            print(f"≡ 1 (q | Q) [{t5-t4:.1f}s]")
            print(f"    ⚠ q divise Q, v_q(ord) < v_q(d-1). Pas un témoin direct.")
            # Check higher powers
            if vq >= 2:
                exp2 = dm1 // (q * q)
                r2 = pow(2, exp2, d)
                if r2 != 1:
                    print(f"    Mais 2^((d-1)/q²) ≢ 1, donc v_q(Q) = 1")
                    print(f"    v_q(ord) = {vq} - 1 = {vq-1}")
                    if vq - 1 > 0:
                        print(f"    v_q(ord) = {vq-1} > 0 = v_q(C)")
                        print(f"    ★★★ q={q} EST TEMOIN ★★★")
        else:
            print(f"≢ 1 [{t5-t4:.1f}s]")
            print(f"    q ∤ Q, donc v_q(ord) = v_q(d-1) = {vq}")
            print(f"    v_q(ord) = {vq} > 0 = v_q(C)")
            print(f"    ★★★ q = {q} EST TEMOIN ULTRASON ★★★")
            print(f"    => ord ∤ C => 2^C ≢ 1 mod d  QED pour k={k} !")
            break

# ================================================================
# U5. SYNTHESE
# ================================================================
print("\n" + "=" * 70)
print("U5. SYNTHESE ULTRASON")
print("=" * 70)

if hits:
    print(f"\n  RESULTAT : {len(hits)} premiers q > {S-1} divisent d-1")
    print(f"  Premier hit : q = {hits[0]}")
    print(f"  Pour CHACUN : v_q(C) = 0 (garanti car q > S-1)")
    print(f"  Si un seul satisfait q ∤ Q : k={k} est RESOLU.")
else:
    print(f"\n  Aucun premier q ∈ ({min_q}, {max_q}] ne divise d-1.")
    print(f"  Etendre la recherche ou changer d'approche.")

print(f"\n  ARGUMENT THEORIQUE GENERAL :")
print(f"  Pour k quelconque avec d premier, si d-1 a un facteur premier q > S-1")
print(f"  avec q ∤ Q, alors G2c est prouvé pour ce k.")
print(f"  Probabilité que d-1 soit (S-1)-smooth : ~ u^{{-u}}")
u = S * math.log(2) / math.log(S - 1)
print(f"  u = S·ln(2)/ln(S-1) = {u:.1f}")
print(f"  u^(-u) ≈ {u:.1f}^(-{u:.1f}) ≈ 10^(-{u*math.log10(u):.0f})")
print(f"  => d-1 a un facteur > S-1 avec probabilité écrasante.")

print("\n" + "=" * 70)
print("FIN ITERATION 5bis : ULTRASON")
print("=" * 70)
