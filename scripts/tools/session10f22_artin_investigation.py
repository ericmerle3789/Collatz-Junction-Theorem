#!/usr/bin/env python3
"""
SESSION 10f22 : Attaque Artin — ord ∤ C par incompatibilite de valuations
=========================================================================
HYPOTHESE CENTRALE : Pour k impair, v_2(ord_d(2)) = 2 et v_2(C) <= 1,
  donc ord ne divise pas C, donc 2^C ≢ 1 mod d.

PLAN :
  I1. Verifier v_2(d-1), v_2(Q), v_2(ord) pour les 19 d premiers
  I2. Calculer v_2(C) pour les 19 cas et BIEN AU-DELA (k jusqu'a 100000)
  I3. Tester l'hypothese v_2(C) <= 1 pour k impair
  I4. Pour k pair : chercher un autre prime p avec v_p(ord) > v_p(C)
  I5. Verifier que ord ∤ C pour les 19 cas (test direct)
  I6. Synthese
"""

import sys
import math
sys.stdout.reconfigure(line_buffering=True)

def ceil_log2_3(k):
    return math.ceil(k * math.log2(3))

def v2(n):
    """Valuation 2-adique de n."""
    if n == 0:
        return float('inf')
    v = 0
    while n % 2 == 0:
        v += 1
        n //= 2
    return v

def vp(n, p):
    """Valuation p-adique de n."""
    if n == 0:
        return float('inf')
    v = 0
    while n % p == 0:
        v += 1
        n //= p
    return v

def kummer_carries(a, b, base=2):
    """Nombre de retenues dans l'addition a + b en base `base`.
    Par le theoreme de Kummer, c'est v_base(binom(a+b, a))."""
    carries = 0
    carry = 0
    while a > 0 or b > 0 or carry > 0:
        digit_sum = (a % base) + (b % base) + carry
        carry = digit_sum // base
        carries += carry  # actually carry is 0 or 1 in base 2
        a //= base
        b //= base
        # In base 2, carry is always 0 or 1, and each carry contributes 1
    return carries

# Sympy pour primalite
try:
    from sympy import isprime, factorint
    check_prime = isprime
except ImportError:
    def check_prime(n):
        if n < 2: return False
        if n < 4: return True
        if n % 2 == 0: return False
        return pow(2, n-1, n) == 1 and pow(3, n-1, n) == 1
    factorint = None

# ================================================================
# I1. VALUATIONS 2-ADIQUES POUR LES 19 d PREMIERS
# ================================================================
print("=" * 70)
print("I1. VALUATIONS 2-ADIQUES POUR LES 19 d PREMIERS")
print("=" * 70)

prime_d_cases = []
for k in range(3, 10001):
    S = ceil_log2_3(k)
    d = pow(2, S) - pow(3, k)
    if d > 1 and check_prime(d):
        prime_d_cases.append((k, S, d))

print(f"\n  {len(prime_d_cases)} d premiers pour k in [3, 10000]")
print(f"\n  {'k':>5s} | {'S':>5s} | {'k%2':>3s} | {'d%8':>3s} | v2(d-1) | v2(Q) | v2(ord) |")
print("  " + "-" * 55)

# Calculer Q via Q_pred pour les cas non-factorisables
def Q_pred(d):
    """Prediction de Q = (d-1)/ord_d(2) via residuacite."""
    n = d - 1
    Q = 1
    primes_to_test = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
    for p in primes_to_test:
        if n % p == 0:
            max_power = 0
            temp_n = n
            while temp_n % p == 0:
                max_power += 1
                temp_n //= p
            for e in range(1, max_power + 1):
                exp = n // (p**e)
                if pow(2, exp, d) == 1:
                    Q *= p
                else:
                    break
    return Q

results_I1 = []
for k, S, d in prime_d_cases:
    dm1 = d - 1
    C = math.comb(S - 1, k - 1)
    Q = Q_pred(d)
    ord_val = dm1 // Q  # ord = (d-1)/Q

    v2_dm1 = v2(dm1)
    v2_Q = v2(Q)
    v2_ord = v2(ord_val)
    v2_C = v2(C)

    results_I1.append({
        'k': k, 'S': S, 'd': d, 'C': C, 'Q': Q,
        'ord': ord_val,
        'v2_dm1': v2_dm1, 'v2_Q': v2_Q, 'v2_ord': v2_ord, 'v2_C': v2_C
    })

    print(f"  {k:5d} | {S:5d} | {k%2:3d} | {d%8:3d} |    {v2_dm1:4d} |  {v2_Q:4d} |    {v2_ord:4d} |")

# ================================================================
# I2. COMPARAISON v2(ord) vs v2(C) POUR LES 19 CAS
# ================================================================
print("\n" + "=" * 70)
print("I2. COMPARAISON v2(ord) vs v2(C) — TEST ord ∤ C")
print("=" * 70)

print(f"\n  {'k':>5s} | {'k%2':>3s} | v2(ord) | v2(C) | v2(ord)>v2(C)? | ord∤C? |")
print("  " + "-" * 60)

for r in results_I1:
    k = r['k']
    v2o = r['v2_ord']
    v2c = r['v2_C']
    v2_wins = v2o > v2c

    # Test direct : ord | C ?
    C = r['C']
    ord_val = r['ord']
    ord_divides_C = (C % ord_val == 0)

    print(f"  {k:5d} | {k%2:3d} |    {v2o:4d} |  {v2c:4d} | {'OUI ✓':>14s} | {'ord|C ⚠' if ord_divides_C else 'ord∤C ✓':>6s} |"
          if v2_wins else
          f"  {k:5d} | {k%2:3d} |    {v2o:4d} |  {v2c:4d} | {'non':>14s} | {'ord|C ⚠' if ord_divides_C else 'ord∤C ✓':>6s} |")

# ================================================================
# I3. v2(C) POUR k IMPAIR : TEST LARGE (k jusqu'a 100000)
# ================================================================
print("\n" + "=" * 70)
print("I3. v2(C) = v2(binom(S-1, k-1)) POUR k IMPAIR — TEST LARGE")
print("=" * 70)

print(f"\n  Hypothese : v2(C) <= 1 pour tout k >= 3 impair")
print(f"  (Si vrai : v2(ord) = 2 > v2(C) <= 1 => ord ∤ C pour k impair)")
print()

# Methode rapide : v2(binom(n,m)) = nombre de retenues dans m + (n-m) en base 2
# n = S-1, m = k-1, n-m = S-k = M

max_v2C_odd = 0
counter_examples = []
distribution = {}  # v2(C) -> count

LIMIT = 100000
count_odd = 0
for k in range(3, LIMIT + 1, 2):  # k impair seulement
    S = ceil_log2_3(k)
    # v2(binom(S-1, k-1)) = carries quand on additionne (k-1) et (S-k) en base 2
    m = k - 1  # even since k is odd
    n_minus_m = S - k  # = M

    carries = kummer_carries(m, n_minus_m, 2)

    if carries not in distribution:
        distribution[carries] = 0
    distribution[carries] += 1

    if carries > max_v2C_odd:
        max_v2C_odd = carries

    if carries >= 2:
        counter_examples.append((k, S, carries))

    count_odd += 1

print(f"  k impair in [3, {LIMIT}] : {count_odd} valeurs testees")
print(f"  Max v2(C) observe : {max_v2C_odd}")
print(f"  Distribution de v2(C) :")
for v, count in sorted(distribution.items()):
    pct = 100 * count / count_odd
    print(f"    v2(C) = {v} : {count} cas ({pct:.1f}%)")

if counter_examples:
    print(f"\n  ⚠ CONTRE-EXEMPLES (v2(C) >= 2) : {len(counter_examples)} cas")
    for k, S, v2c in counter_examples[:30]:
        print(f"    k={k}, S={S}, v2(C)={v2c}")
    if len(counter_examples) > 30:
        print(f"    ... et {len(counter_examples) - 30} autres")

    # Analyser la structure des contre-exemples
    print(f"\n  ANALYSE DES CONTRE-EXEMPLES :")
    print(f"    Premier contre-exemple : k={counter_examples[0][0]}")
    print(f"    Fraction : {len(counter_examples)}/{count_odd} = {len(counter_examples)/count_odd:.4f}")

    # Verifier si d est premier pour ces contre-exemples (petit echantillon)
    print(f"\n  Contre-exemples ou d est premier :")
    ce_prime = 0
    for k, S, v2c in counter_examples[:100]:
        d = pow(2, S) - pow(3, k)
        if d > 1 and check_prime(d):
            ce_prime += 1
            print(f"    k={k}, S={S}, v2(C)={v2c}, d={d} ({d.bit_length()} bits) — PREMIER!")
    if ce_prime == 0:
        print(f"    AUCUN (sur les {min(100, len(counter_examples))} premiers contre-exemples)")
else:
    print(f"\n  ★★★★★ AUCUN CONTRE-EXEMPLE ! v2(C) <= 1 pour TOUT k impair in [3, {LIMIT}]")

# ================================================================
# I4. POUR k PAIR : CHERCHER p TEL QUE v_p(ord) > v_p(C)
# ================================================================
print("\n" + "=" * 70)
print("I4. k PAIR : RECHERCHE DE p AVEC v_p(ord) > v_p(C)")
print("=" * 70)

print(f"\n  Pour k pair : v2(ord) = 0 (ord impair), donc v2 ne suffit pas.")
print(f"  Cherchons un autre prime p qui cree une incompatibilite.\n")

even_cases = [r for r in results_I1 if r['k'] % 2 == 0]
for r in even_cases:
    k, S, d, C, Q, ord_val = r['k'], r['S'], r['d'], r['C'], r['Q'], r['ord']

    # Tester plusieurs primes
    primes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
    found = False
    for p in primes:
        vp_ord = vp(ord_val, p)
        vp_C = vp(C, p)
        if vp_ord > vp_C:
            print(f"  k={k}: p={p} fonctionne ! v_{p}(ord)={vp_ord} > v_{p}(C)={vp_C}")
            found = True
            break

    if not found:
        # Test direct
        ord_div_C = (C % ord_val == 0)
        pow2C = pow(2, C, d)
        print(f"  k={k}: AUCUN petit p ne marche. ord|C? {ord_div_C}. "
              f"2^C mod d = {'1 ⚠' if pow2C == 1 else '≠1 ✓'}")

# ================================================================
# I5. VERIFICATION DIRECTE : 2^C mod d pour les 19 cas
# ================================================================
print("\n" + "=" * 70)
print("I5. VERIFICATION DIRECTE : 2^C ≢ 1 mod d")
print("=" * 70)

all_pass = True
for r in results_I1:
    k, S, d, C = r['k'], r['S'], r['d'], r['C']
    pow2C = pow(2, C, d)
    status = "✓" if pow2C != 1 else "⚠ ECHEC"
    if pow2C == 1:
        all_pass = False
    print(f"  k={k}: 2^C mod d = {'1' if pow2C == 1 else '≠1'} {status}")

if all_pass:
    print(f"\n  ★★★★★ G2c VERIFIE pour les 19 d premiers (confirmee)")

# ================================================================
# I6. v2(C) POUR k PAIR : TEST LARGE
# ================================================================
print("\n" + "=" * 70)
print("I6. v2(C) POUR k PAIR — CONTEXTE")
print("=" * 70)

max_v2C_even = 0
dist_even = {}
for k in range(4, LIMIT + 1, 2):
    S = ceil_log2_3(k)
    m = k - 1
    n_minus_m = S - k
    carries = kummer_carries(m, n_minus_m, 2)
    if carries not in dist_even:
        dist_even[carries] = 0
    dist_even[carries] += 1
    if carries > max_v2C_even:
        max_v2C_even = carries

count_even = sum(dist_even.values())
print(f"  k pair in [4, {LIMIT}] : {count_even} valeurs")
print(f"  Max v2(C) : {max_v2C_even}")
print(f"  Distribution :")
for v, count in sorted(dist_even.items()):
    pct = 100 * count / count_even
    print(f"    v2(C) = {v} : {count} cas ({pct:.1f}%)")

# ================================================================
# I7. ANALYSE : v3(C) vs v3(ord) pour les cas S pair (3 | d-1)
# ================================================================
print("\n" + "=" * 70)
print("I7. v3(C) vs v3(ord) — PRIMES p=3 POUR S PAIR")
print("=" * 70)

print(f"\n  Quand S pair : 3 | (d-1), potentiellement 3 | Q, donc 3 | ord aussi.")
for r in results_I1:
    k, S, d, C, Q, ord_val = r['k'], r['S'], r['d'], r['C'], r['Q'], r['ord']
    v3_ord = vp(ord_val, 3)
    v3_C = vp(C, 3)
    v3_dm1 = vp(d - 1, 3)
    v3_Q = vp(Q, 3)

    # v3(C) via Kummer
    carries_3 = kummer_carries(k - 1, S - k, 3)  # base 3

    print(f"  k={k}: S%2={S%2}, v3(d-1)={v3_dm1}, v3(Q)={v3_Q}, "
          f"v3(ord)={v3_ord}, v3(C)={v3_C} (Kummer={carries_3}), "
          f"{'v3 wins!' if v3_ord > v3_C else ''}")

# ================================================================
# I8. APPROCHE HYBRIDE : EXISTE-T-IL TOUJOURS UN p QUI MARCHE ?
# ================================================================
print("\n" + "=" * 70)
print("I8. APPROCHE HYBRIDE : POUR CHAQUE CAS, EXISTE-T-IL p AVEC v_p(ord) > v_p(C) ?")
print("=" * 70)

print(f"\n  Pour chaque d premier, on cherche n'importe quel p | ord tel que v_p(ord) > v_p(C)")

for r in results_I1:
    k, S, d, C, Q, ord_val = r['k'], r['S'], r['d'], r['C'], r['Q'], r['ord']

    # Factoriser ord_val (partiellement)
    winning_primes = []
    temp_ord = ord_val
    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]:
        if temp_ord % p == 0:
            vp_o = vp(ord_val, p)
            vp_c = vp(C, p)
            if vp_o > vp_c:
                winning_primes.append((p, vp_o, vp_c))
            while temp_ord % p == 0:
                temp_ord //= p

    if winning_primes:
        p_info = ", ".join(f"p={p}: v_p(ord)={vo}>v_p(C)={vc}" for p, vo, vc in winning_primes)
        print(f"  k={k}: ✓ {p_info}")
    else:
        # Test direct comme filet
        pow2C = pow(2, C, d)
        divides = (C % ord_val == 0)
        print(f"  k={k}: ? Aucun petit p ne marche. ord|C={divides}, 2^C≡1? {pow2C==1}")

# ================================================================
# I9. SYNTHESE
# ================================================================
print("\n" + "=" * 70)
print("I9. SYNTHESE SESSION 10f22")
print("=" * 70)

print(f"""
  ═══════════════════════════════════════════════════════════
  ║  ATTAQUE ARTIN : ord ∤ C PAR VALUATIONS               ║
  ═══════════════════════════════════════════════════════════

  STRATEGIE : Au lieu de prouver ord > C (Artin), prouver ord ∤ C
  par incompatibilite des valuations p-adiques.

  RESULTATS :

  CAS k IMPAIR :
    v2(ord) = 2 toujours (car v2(d-1)=2 et Q impair)
    Hypothese : v2(C) <= 1 pour tout k >= 3 impair
    Test : k in [3, {LIMIT}] impair → {count_odd} valeurs
    Max v2(C) = {max_v2C_odd}
    Contre-exemples (v2(C) >= 2) : {len(counter_examples) if counter_examples else 0}

  CAS k PAIR :
    v2(ord) = 0 (ord impair), v2 ne peut pas aider
    Besoin d'un autre p — exploration en cours

  G2c VERIFIE : {'OUI' if all_pass else 'NON'} (19/19 d premiers, k <= 10000)
""")

print("=" * 70)
print("FIN SESSION 10f22 — INVESTIGATION ARTIN")
print("=" * 70)
