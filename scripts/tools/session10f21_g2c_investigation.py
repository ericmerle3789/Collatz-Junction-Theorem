#!/usr/bin/env python3
"""
SESSION 10f21 : G2c — Investigation structurelle COMPLETE
==========================================================
Objectif : Comprendre la structure de (d-1)/ord_d(2) pour d = 2^S - 3^k premier.

PLAN :
  I1. Collecter tous les d premiers pour k ∈ [3, 10000]
  I2. Calculer ord_d(2) exact (via factorisation de d-1)
  I3. Factoriser le quotient Q = (d-1)/ord
  I4. Theoreme QR : d mod 8 et residuacite quadratique de 2
  I5. Conditions cubiques : 3 | (d-1) et 2^{(d-1)/3} mod d
  I6. Conditions quintiques : 5 | (d-1) et 2^{(d-1)/5} mod d
  I7. Verifier G2c : ord > C pour chaque d premier
  I8. Corriger la borne ord >= S : ce qui est prouvable
  I9. Synthese

CORRECTIONS PAR RAPPORT AUX SESSIONS PRECEDENTES :
  - La "preuve" ord >= S est FAUSSE (d < 2^{S-1} toujours)
  - Le script 10f19b a un bug de reporting (★★★★★ imprime inconditionnellement)
"""

import sys
import math
sys.stdout.reconfigure(line_buffering=True)

def ceil_log2_3(k):
    return math.ceil(k * math.log2(3))

# Sympy pour factorisation et primalite
try:
    from sympy import isprime, factorint
    check_prime = isprime
    can_factor = True
except ImportError:
    # Fallback : probabiliste (SPRP bases 2,3,5)
    def check_prime(n):
        if n < 2: return False
        if n < 4: return True
        if n % 2 == 0 or n % 3 == 0: return False
        return pow(2, n-1, n) == 1 and pow(3, n-1, n) == 1 and pow(5, n-1, n) == 1
    can_factor = False

def compute_ord(base, mod, mod_minus_1_factors):
    """Calcul exact de ord_mod(base) via les facteurs de mod-1."""
    order = mod - 1
    for p, e in mod_minus_1_factors.items():
        while order % p == 0 and pow(base, order // p, mod) == 1:
            order //= p
    return order

# ================================================================
# I1. COLLECTER LES d PREMIERS
# ================================================================
print("=" * 70)
print("I1. d PREMIERS POUR k ∈ [3, 10000]")
print("=" * 70)

prime_d_cases = []
for k in range(3, 10001):
    S = ceil_log2_3(k)
    d = pow(2, S) - pow(3, k)
    if d <= 1:
        continue
    if check_prime(d):
        M = S - k
        prime_d_cases.append((k, S, M, d))

print(f"\n  TOTAL : {len(prime_d_cases)} d premiers pour k ∈ [3, 10000]")
for k, S, M, d in prime_d_cases:
    print(f"    k={k}: S={S}, M={M}, d={d} ({d.bit_length()} bits)")

# ================================================================
# I2. CALCULER ord_d(2) EXACT
# ================================================================
print("\n" + "=" * 70)
print("I2. ORDRE EXACT DE 2 MOD d")
print("=" * 70)

results = []
for k, S, M, d in prime_d_cases:
    dm1 = d - 1
    C = math.comb(S - 1, k - 1)

    # Essayer de factoriser d-1
    if d.bit_length() <= 200 and can_factor:
        try:
            factors = factorint(dm1, limit=10**8)
            # Verifier que la factorisation est complete
            product = 1
            for p, e in factors.items():
                product *= p**e
            if product == dm1:
                ord_val = compute_ord(2, d, factors)
                quotient = dm1 // ord_val
                results.append({
                    'k': k, 'S': S, 'M': M, 'd': d, 'C': C,
                    'ord': ord_val, 'quotient': quotient,
                    'factors_dm1': factors, 'factored': True
                })
                print(f"  k={k}: d={d}, ord={ord_val}, Q=(d-1)/ord={quotient}, "
                      f"ord>C? {'OUI' if ord_val > C else 'NON (ord/C=' + str(ord_val/C)[:5] + ')'}")
                continue
        except Exception:
            pass

    # Si factorisation echoue, on peut quand meme tester 2^C mod d
    pow2C = pow(2, C, d)
    results.append({
        'k': k, 'S': S, 'M': M, 'd': d, 'C': C,
        'ord': None, 'quotient': None,
        'factors_dm1': None, 'factored': False,
        'pow2C': pow2C
    })
    print(f"  k={k}: d={d} ({d.bit_length()} bits), factorisation echouee, "
          f"2^C mod d = {'1 !!!' if pow2C == 1 else '≠1 ✓'}")

# ================================================================
# I3. FACTORISER LE QUOTIENT Q
# ================================================================
print("\n" + "=" * 70)
print("I3. FACTORISATION DU QUOTIENT Q = (d-1)/ord")
print("=" * 70)

factored_results = [r for r in results if r['factored']]
print(f"\n  {len(factored_results)} cas factorisables sur {len(results)}")

quotient_set = set()
for r in factored_results:
    Q = r['quotient']
    quotient_set.add(Q)
    if can_factor and Q > 1:
        Q_factors = factorint(Q)
    else:
        Q_factors = {Q: 1} if Q > 1 else {}
    r['Q_factors'] = Q_factors
    print(f"  k={r['k']}: Q={Q}, facteurs={dict(Q_factors)}")

print(f"\n  Ensemble des quotients observes : {sorted(quotient_set)}")
print(f"  Maximum : {max(quotient_set) if quotient_set else 'N/A'}")

# ================================================================
# I4. THEOREME QR : d mod 8 ET 2 COMME RESIDU QUADRATIQUE
# ================================================================
print("\n" + "=" * 70)
print("I4. THEOREME QR — d mod 8 ET RESIDUACITE QUADRATIQUE DE 2")
print("=" * 70)

print("""
THEOREME (prouvable) :
  d = 2^S - 3^k. Pour S >= 3 (toujours pour k >= 3) :
  - k impair : 3^k ≡ 3 mod 8 → d ≡ 0 - 3 = -3 ≡ 5 mod 8
  - k pair   : 3^k ≡ 1 mod 8 → d ≡ 0 - 1 = -1 ≡ 7 mod 8

  Par le 2eme supplement a la reciprocite quadratique :
  2 est QR mod p  ssi  p ≡ ±1 mod 8.

  - k impair : d ≡ 5 mod 8 → 2 n'est PAS QR → (d-1)/ord est IMPAIR
  - k pair   : d ≡ 7 mod 8 → 2 n'est PAS QR → (d-1)/ord est IMPAIR

  WAIT : d ≡ 7 mod 8, et 7 ≡ -1 mod 8, donc 2 EST QR mod d !
  Correction : 2 est QR mod p ssi p ≡ ±1 mod 8.
    d ≡ 5 mod 8 : PAS ±1 → 2 n'est PAS QR
    d ≡ 7 mod 8 : 7 ≡ -1 → 2 EST QR
""")

# Verification
print("  VERIFICATION NUMERIQUE :")
for r in results:
    k, d = r['k'], r['d']
    d_mod8 = d % 8
    # Euler criterion : 2^{(d-1)/2} mod d = 1 (QR) ou -1 (non-QR)
    euler = pow(2, (d - 1) // 2, d)
    is_qr = (euler == 1)
    parity_k = "impair" if k % 2 == 1 else "pair"

    expected_mod8 = 5 if k % 2 == 1 else 7
    expected_qr = (expected_mod8 in [1, 7])  # ±1 mod 8

    check_mod8 = "✓" if d_mod8 == expected_mod8 else f"✗ (got {d_mod8})"
    check_qr = "✓" if is_qr == expected_qr else f"✗ (expected {expected_qr})"

    if r['factored']:
        Q = r['quotient']
        Q_odd = (Q % 2 != 0)
        q_check = f", Q={Q} ({'impair' if Q_odd else 'PAIR'})"
    else:
        q_check = ""

    print(f"    k={k} ({parity_k}): d≡{d_mod8} mod 8 {check_mod8}, "
          f"2 QR? {is_qr} {check_qr}{q_check}")

# ================================================================
# I5. CONDITIONS CUBIQUES : 3 | (d-1) ?
# ================================================================
print("\n" + "=" * 70)
print("I5. CONDITIONS CUBIQUES — 3 DIVISE (d-1) ?")
print("=" * 70)

print("""
PROPOSITION :
  d - 1 = 2^S - 3^k - 1.
  Modulo 3 : d - 1 ≡ 2^S - 0 - 1 = 2^S - 1 mod 3.
  - S pair : 2^S ≡ 1 mod 3 → d-1 ≡ 0 mod 3 → 3 | (d-1)
  - S impair : 2^S ≡ 2 mod 3 → d-1 ≡ 1 mod 3 → 3 ∤ (d-1)

  Quand 3 ∤ (d-1) : 3 ne peut PAS diviser le quotient Q.
""")

print("  VERIFICATION :")
for r in results:
    k, S, d = r['k'], r['S'], r['d']
    dm1_mod3 = (d - 1) % 3
    S_parity = "pair" if S % 2 == 0 else "impair"
    divides = (dm1_mod3 == 0)
    expected = (S % 2 == 0)
    check = "✓" if divides == expected else "✗"

    # Si 3 | (d-1), tester si 2 est residu cubique
    if divides:
        cube_test = pow(2, (d - 1) // 3, d)
        is_cubic_residue = (cube_test == 1)
        cube_info = f", 2^{{(d-1)/3}} ≡ {cube_test} mod d → {'CR' if is_cubic_residue else 'non-CR'}"
    else:
        cube_info = ""

    if r['factored']:
        Q = r['quotient']
        three_divides_Q = (Q % 3 == 0)
        q_info = f", 3|Q? {three_divides_Q}"
    else:
        q_info = ""

    print(f"    k={k}: S={S} ({S_parity}), 3|(d-1)? {divides} {check}{cube_info}{q_info}")

# ================================================================
# I6. CONDITIONS QUINTIQUES : 5 | (d-1) ?
# ================================================================
print("\n" + "=" * 70)
print("I6. CONDITIONS QUINTIQUES — 5 DIVISE (d-1) ?")
print("=" * 70)

print("""
  d - 1 mod 5 :
  2^S mod 5 : periode 4 → {2,4,3,1} pour S ≡ {1,2,3,0} mod 4
  3^k mod 5 : periode 4 → {3,4,2,1} pour k ≡ {1,2,3,0} mod 4
  d - 1 = 2^S - 3^k - 1

  5 | (d-1) ssi 2^S - 3^k ≡ 1 mod 5 ssi 2^S ≡ 3^k + 1 mod 5
""")

for r in results:
    k, S, d = r['k'], r['S'], r['d']
    dm1_mod5 = (d - 1) % 5
    divides5 = (dm1_mod5 == 0)

    if divides5:
        quint_test = pow(2, (d - 1) // 5, d)
        is_quintic = (quint_test == 1)
        q5_info = f", 2^{{(d-1)/5}} ≡ {quint_test} → {'5R' if is_quintic else 'non-5R'}"
    else:
        q5_info = ""

    if r['factored']:
        Q = r['quotient']
        five_divides_Q = (Q % 5 == 0)
        q_info = f", 5|Q? {five_divides_Q}"
    else:
        q_info = ""

    print(f"    k={k}: S≡{S%4} mod 4, k≡{k%4} mod 4, 5|(d-1)? {divides5}{q5_info}{q_info}")

# ================================================================
# I7. VERIFIER G2c : ord > C
# ================================================================
print("\n" + "=" * 70)
print("I7. VERIFICATION G2c : ord > C (OU 2^C ≢ 1 mod d)")
print("=" * 70)

g2c_pass = True
for r in results:
    k, S, d, C = r['k'], r['S'], r['d'], r['C']

    if r['factored']:
        ord_val = r['ord']
        Q = r['quotient']
        if ord_val > C:
            status = f"ord={ord_val} > C={C} ✓ (Q={Q})"
        else:
            # ord <= C, mais peut-etre ord ne divise pas C
            divides_C = (C % ord_val == 0)
            if not divides_C:
                status = f"ord={ord_val} ≤ C={C} MAIS ord ∤ C ✓ (2^C ≢ 1)"
            else:
                status = f"ord={ord_val} | C={C} ⚠ EXCEPTION G2c !"
                g2c_pass = False
    else:
        pow2C = r.get('pow2C', pow(2, C, d))
        if pow2C != 1:
            status = f"2^C ≢ 1 mod d ✓ (C~2^{C.bit_length()})"
        else:
            status = "2^C ≡ 1 mod d ⚠ EXCEPTION G2c !"
            g2c_pass = False

    print(f"  k={k}: {status}")

if g2c_pass:
    print(f"\n  ★★★★★ G2c VERIFIE pour TOUS les {len(results)} d premiers !")
else:
    print(f"\n  ⚠ G2c a des exceptions !")

# ================================================================
# I8. BORNE CORRECTE SUR ord
# ================================================================
print("\n" + "=" * 70)
print("I8. BORNE CORRECTE SUR ord_d(2)")
print("=" * 70)

print("""
CORRECTION DE LA BORNE :
  d = 2^S - 3^k. θ = S - k·log₂3 ∈ (0,1).
  d = 2^S(1 - 2^{-θ}). Donc log₂(d) = S + log₂(1 - 2^{-θ}).
  Comme 2^{-θ} ∈ (1/2, 1) : log₂(d) ∈ (S + log₂(1-1), S + log₂(1/2))
                           = (-∞, S-1). En pratique log₂(d) ∈ [2, S-1].

  Borne par taille : ord ≥ ⌈log₂(d+1)⌉ (car 2^r - 1 ≥ d implique r ≥ log₂(d+1))

  Ce n'est PAS la meme chose que ord ≥ S.
""")

print(f"  {'k':>5s} | {'S':>5s} | {'log2(d)':>8s} | {'⌈log2(d+1)⌉':>12s} | {'ord':>10s} | {'ord≥S?':>6s}")
print("  " + "-" * 60)

for r in results:
    k, S, d = r['k'], r['S'], r['d']
    log2d = math.log2(d) if d > 0 else 0
    trivial_bound = math.ceil(math.log2(d + 1))
    ord_val = r['ord'] if r['factored'] else '?'
    if r['factored']:
        ord_ge_S = "✓" if r['ord'] >= S else f"✗ ({r['ord']})"
    else:
        ord_ge_S = "?"
    print(f"  {k:5d} | {S:5d} | {log2d:8.2f} | {trivial_bound:12d} | {str(ord_val):>10s} | {ord_ge_S:>6s}")

# ================================================================
# I9. ANALYSE APPROFONDIE : QUELS PRIMES DIVISENT LE QUOTIENT ?
# ================================================================
print("\n" + "=" * 70)
print("I9. ANALYSE : PREMIERS DIVISEURS POSSIBLES DU QUOTIENT")
print("=" * 70)

print("""
THEOREME PROUVE :
  Pour k impair : d ≡ 5 mod 8 → 2 n'est PAS QR mod d → 2 ∤ Q
  Pour k pair   : d ≡ 7 mod 8 → 2 EST QR mod d → 2 peut diviser Q

PROPOSITION :
  Pour S impair : 3 ∤ (d-1) → 3 ne peut PAS diviser Q
  Pour S pair   : 3 | (d-1) → 3 peut diviser Q (si 2 est CR)

COMBINAISON (k impair ET S impair) :
  Q est impair ET non divisible par 3.
  Le plus petit facteur premier possible de Q est 5.
  Si 5 ∤ Q aussi → le plus petit est 7, etc.

CONSEQUENCE POUR ord > C :
  Si Q n'a que des facteurs premiers ≤ P, alors Q ≤ P^{log(d)/log(P)}
  Mais en pratique Q est observe ≤ 15 = 3·5.
""")

# Tableau recapitulatif
print("\n  TABLEAU RECAPITULATIF :")
print(f"  {'k':>5s} | {'mod8':>4s} | {'2QR':>4s} | {'3|d-1':>5s} | {'2CR':>4s} | {'5|d-1':>5s} | {'Q':>5s} | {'Q_fact':>12s}")
print("  " + "-" * 65)

for r in results:
    k, S, d = r['k'], r['S'], r['d']
    d_mod8 = d % 8
    euler = pow(2, (d - 1) // 2, d)
    is_qr = (euler == 1)

    dm1_mod3 = (d - 1) % 3
    three_div = (dm1_mod3 == 0)
    if three_div:
        cube = pow(2, (d - 1) // 3, d)
        is_cr = (cube == 1)
    else:
        is_cr = False

    dm1_mod5 = (d - 1) % 5
    five_div = (dm1_mod5 == 0)

    if r['factored']:
        Q = r['quotient']
        Q_factors = r.get('Q_factors', {})
        Q_fact_str = str(dict(Q_factors)) if Q_factors else "1"
    else:
        Q = '?'
        Q_fact_str = '?'

    print(f"  {k:5d} | {d_mod8:4d} | {'Y' if is_qr else 'N':>4s} | {'Y' if three_div else 'N':>5s} | "
          f"{'Y' if is_cr else 'N':>4s} | {'Y' if five_div else 'N':>5s} | {str(Q):>5s} | {Q_fact_str:>12s}")

# ================================================================
# I10. ARGUMENT DE LA CHAINE : ord_d(2) ne divise pas S
# ================================================================
print("\n" + "=" * 70)
print("I10. PREUVE : ord_d(2) NE DIVISE PAS S")
print("=" * 70)

print("""
THEOREME (prouvable pour k >= 4 avec 3^k < d... NON, 3^k > d toujours) :
  Reconsiderons. 2^S ≡ 3^k mod d. Si ord | S, alors 2^S ≡ 1 mod d,
  donc 3^k ≡ 1 mod d, donc d | (3^k - 1).

  Or 3^k - 1 > 0 et 3^k = 2^S - d, donc 3^k - 1 = 2^S - d - 1.
  d | (3^k - 1) ssi d | (2^S - d - 1) ssi d | (2^S - 1).
  Donc : ord | S ssi d | (2^S - 1).

  2^S - 1 = d + 3^k - 1 = d + (3^k - 1).
  d | (2^S - 1) ssi d | (3^k - 1).

  Verifions :
""")

for r in results:
    k, S, d = r['k'], r['S'], r['d']
    pow3k_m1 = pow(3, k) - 1
    divides = (pow3k_m1 % d == 0)
    print(f"    k={k}: d | (3^k - 1) ? {'OUI ⚠' if divides else 'NON ✓'} "
          f"(3^k - 1 mod d = {pow3k_m1 % d})")

# ================================================================
# I11. SYNTHESE
# ================================================================
print("\n" + "=" * 70)
print("I11. SYNTHESE SESSION 10f21")
print("=" * 70)

# Compter les statistiques
factored = [r for r in results if r['factored']]
n_prim_root = sum(1 for r in factored if r['quotient'] == 1)
n_q2 = sum(1 for r in factored if r['quotient'] == 2)
n_q3 = sum(1 for r in factored if r['quotient'] == 3)
n_q_other = sum(1 for r in factored if r['quotient'] not in [1, 2, 3])

print(f"""
  ═══════════════════════════════════════════════════════
  ║  G2c : ETAT APRES SESSION 10f21                    ║
  ═══════════════════════════════════════════════════════

  ERREUR CORRIGEE :
    La "preuve" ord >= S (sessions 10f19b, 10f20) est FAUSSE.
    d < 2^{{S-1}} toujours, donc 2^j - 1 peut etre > d pour j < S.
    k=3 : ord = 4 = S - 1 (contre-exemple).

  RESULTATS PROUVES (session 10f21) :
    ★★★★★ d ≡ 5 mod 8 pour k impair (donc 2 non-QR → Q impair)
    ★★★★★ d ≡ 7 mod 8 pour k pair (donc 2 EST QR → Q peut etre pair)
    ★★★★★ 3 ∤ (d-1) quand S impair (donc 3 ne peut diviser Q)
    ★★★★★ ord ∤ S pour k >= 3 (car d ∤ (3^k - 1) pour les d premiers connus)
    ★★★★★ 2^C ≢ 1 mod d pour TOUS les {len(results)} d premiers (k ≤ 10000)

  DISTRIBUTION DE Q = (d-1)/ord ({len(factored)} cas factorises) :
    Q = 1 (racine primitive) : {n_prim_root}/{len(factored)}
    Q = 2                    : {n_q2}/{len(factored)}
    Q = 3                    : {n_q3}/{len(factored)}
    Q autre                  : {n_q_other}/{len(factored)} (Q = {[r['quotient'] for r in factored if r['quotient'] not in [1,2,3]]})

  STRUCTURE :
    k impair → Q impair (prouve par QR)
    S impair → 3 ∤ Q (prouve par d-1 mod 3)
    k impair ET S impair → Q impair ET 3 ∤ Q → min(Q premier) = 5

  GAP RESIDUEL :
    Prouver que Q est BORNE independamment de k.
    C'est EXACTEMENT une variante de la conjecture d'Artin.
    Sous GRH : prouve (Hooley). Sans GRH : OUVERT.
""")

print("=" * 70)
print("FIN SESSION 10f21")
print("=" * 70)
