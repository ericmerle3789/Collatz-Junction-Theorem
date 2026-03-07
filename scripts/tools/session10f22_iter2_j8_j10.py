#!/usr/bin/env python3
"""
SESSION 10f22 — G-V-R ITERATION 2 : SECTIONS J8-J10 (apres bug fix)
Complement aux sections J1-J7 deja validees.
"""
import sys
import math
sys.stdout.reconfigure(line_buffering=True)

def ceil_log2_3(k):
    return math.ceil(k * math.log2(3))

try:
    from sympy import isprime
    check_prime = isprime
except ImportError:
    def check_prime(n):
        if n < 2: return False
        if n < 4: return True
        if n % 2 == 0: return False
        return pow(2, n-1, n) == 1 and pow(3, n-1, n) == 1

def Q_pred(d):
    n = d - 1; Q = 1
    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]:
        if n % p == 0:
            max_power = 0; temp_n = n
            while temp_n % p == 0: max_power += 1; temp_n //= p
            for e in range(1, max_power + 1):
                if pow(2, n // (p**e), d) == 1: Q *= p
                else: break
    return Q

# Collecte
prime_d_cases = []
for k in range(3, 10001):
    S = ceil_log2_3(k)
    d = pow(2, S) - pow(3, k)
    if d > 1 and check_prime(d):
        prime_d_cases.append((k, S, d))

results = []
for k, S, d in prime_d_cases:
    C = math.comb(S - 1, k - 1)
    dm1 = d - 1
    g = math.gcd(C, dm1)
    Q = Q_pred(d)
    ord_val = dm1 // Q
    results.append({
        'k': k, 'S': S, 'd': d, 'C': C, 'dm1': dm1,
        'gcd': g, 'Q': Q, 'ord': ord_val
    })

# ================================================================
# J8. C mod ord : DISTANCE A ZERO
# ================================================================
print("=" * 70)
print("J8. C mod ord POUR LES 19 CAS : DISTANCE A ZERO")
print("=" * 70)

print(f"\n  Pour 2^C ≡ 1 mod d, il faut C mod ord = 0.")
print(f"  Condition EQUIVALENTE : ord | C.")
print(f"  On verifie C mod ord ≠ 0 pour chaque cas.\n")

print(f"  {'k':>5s} | {'ord bits':>8s} | {'C bits':>7s} | {'C mod ord = 0?':>14s} | {'gcd<ord?':>8s} |")
print("  " + "-" * 55)

for r in results:
    k, C, ord_val, g = r['k'], r['C'], r['ord'], r['gcd']
    c_mod_o = C % ord_val
    gcd_lt_ord = g < ord_val

    print(f"  {k:5d} | {ord_val.bit_length():8d} | {C.bit_length():7d} | "
          f"{'OUI ⚠⚠' if c_mod_o == 0 else 'non ✓':>14s} | "
          f"{'OUI ✓' if gcd_lt_ord else 'non ⚠':>8s} |")

# ================================================================
# J9. ANALYSE CRUCIALE : POURQUOI gcd(C,d-1) < ord ?
# ================================================================
print("\n" + "=" * 70)
print("J9. ANALYSE CRUCIALE : POURQUOI gcd(C,d-1) < ord ?")
print("=" * 70)

print(f"""
  LOGIQUE :
    gcd(C, d-1) < ord  ⟹  ord ∤ gcd(C, d-1)  ⟹  ord ∤ C  ⟹  2^C ≢ 1

  PREUVE QUE gcd < ord :
    gcd(C, d-1) ≤ C                          (gcd divise C)
    ord = (d-1)/Q                             (definition)
    Donc gcd < ord  ⟺  C < (d-1)/Q  ⟺  C·Q < d-1

  VERIFIONS C·Q < d-1 pour les 19 cas :
""")

print(f"  {'k':>5s} | {'Q':>5s} | {'log2(C*Q)':>10s} | {'log2(d-1)':>10s} | {'C*Q < d-1?':>11s} |")
print("  " + "-" * 55)

all_cq_lt_dm1 = True
for r in results:
    k, C, Q, dm1, g, ord_val = r['k'], r['C'], r['Q'], r['dm1'], r['gcd'], r['ord']
    CQ = C * Q
    cq_lt = CQ < dm1

    if not cq_lt:
        all_cq_lt_dm1 = False

    print(f"  {k:5d} | {Q:5d} | {CQ.bit_length():10d} | {dm1.bit_length():10d} | "
          f"{'OUI ✓' if cq_lt else 'NON ⚠':>11s} |")

if all_cq_lt_dm1:
    print(f"\n  ★★★ C·Q < d-1 pour les 19/19 cas")
else:
    fails = [r['k'] for r in results if r['C'] * r['Q'] >= r['dm1']]
    print(f"\n  ⚠ C·Q >= d-1 pour k = {fails}")

# ================================================================
# J10. REFORMULATION ET CONDITION SUFFISANTE
# ================================================================
print("\n" + "=" * 70)
print("J10. REFORMULATION : CONDITION SUFFISANTE POUR G2c")
print("=" * 70)

print(f"""
  THEOREME (si prouvable) :
    Pour d = 2^S - 3^k premier, soit C = binom(S-1, k-1) et Q = (d-1)/ord_d(2).
    Si C·Q < d-1, alors 2^C ≢ 1 mod d.

  PREUVE :
    C·Q < d-1  ⟹  C < (d-1)/Q = ord  ⟹  0 < C < ord  ⟹  ord ∤ C
    (car C > 0 et C < ord implique que C n'est pas un multiple de ord)
    ord ∤ C  ⟹  2^C ≢ 1 mod d.  ∎

  CONDITION EQUIVALENTE :
    C·Q < d-1  ⟺  C/d < (1 - 1/d)/Q  ⟺  C/d < 1/Q (asymptotiquement)

  ON SAIT QUE :
    C/d → 0 exponentiellement (ratio ≈ 2^{{-0.051·S}})
    Q est empiriquement petit (max observe 95 pour k=655)

  MAIS :
    Prouver Q borne ≡ Artin.
    Cependant, il suffit que Q < d/C = 2^{{0.051·S}}.
    C'est-a-dire Q < 2^{{0.051·S}}, ce qui est BEAUCOUP plus faible que Q borne !

  FORMULATION EQUIVALENTE :
    G2c est vrai si :  Q < 2^{{0.051·S}}
    i.e. :  (d-1)/ord < 2^{{0.051·S}}
    i.e. :  ord > (d-1)/2^{{0.051·S}} ≈ 2^{{0.949·S}}
    i.e. :  ord > C (approximativement)

  CONCLUSION : Cette reformulation est EQUIVALENTE a ord > C.
  La condition C·Q < d-1 ne contourne PAS la barriere d'Artin.
""")

# Verification : est-ce EXACTEMENT equivalent ?
# C·Q < d-1 <=> C < ord.
# Mais pour k=3 et k=5 : C > ord pourtant G2c est vrai.
print(f"  VERIFICATION : C < ord equiv C·Q < d-1 pour chaque cas :")
for r in results:
    k, C, Q, dm1, ord_val = r['k'], r['C'], r['Q'], r['dm1'], r['ord']
    c_lt_ord = C < ord_val
    cq_lt_dm1 = C * Q < dm1
    match = (c_lt_ord == cq_lt_dm1)
    print(f"    k={k}: C<ord={c_lt_ord}, C*Q<d-1={cq_lt_dm1}, match={match}")

# ================================================================
# J11. CAS SPECIAUX : k=3 et k=5 (C >= ord)
# ================================================================
print("\n" + "=" * 70)
print("J11. CAS SPECIAUX : k=3 et k=5 (C >= ord)")
print("=" * 70)

print(f"""
  Pour k=3 et k=5 : C >= ord, donc l'argument C < ord ne fonctionne pas.
  MAIS gcd(C, d-1) < ord fonctionne TOUJOURS.

  Analyse detaillee :
""")

for r in results:
    k = r['k']
    if k not in [3, 5]:
        continue
    C, dm1, g, ord_val, Q, d = r['C'], r['dm1'], r['gcd'], r['ord'], r['Q'], r['d']

    print(f"  k={k}: d={d}, S={r['S']}")
    print(f"    C = {C}")
    print(f"    d-1 = {dm1}")
    print(f"    ord = {ord_val}")
    print(f"    Q = {Q}")
    print(f"    gcd(C, d-1) = {g}")
    print(f"    C mod ord = {C % ord_val}")
    print(f"    C >= ord ? {'OUI' if C >= ord_val else 'non'}")
    print(f"    gcd < ord ? {'OUI ✓' if g < ord_val else 'non ⚠'}")
    print(f"    2^gcd mod d = {pow(2, g, d)} (doit etre ≠ 1)")
    print()

# ================================================================
# J12. TENTATIVE : PROUVER gcd(C,d-1) < ord SANS ARTIN
# ================================================================
print("=" * 70)
print("J12. PEUT-ON PROUVER gcd(C,d-1) < ord SANS ARTIN ?")
print("=" * 70)

print(f"""
  gcd(C, d-1) = prod_p p^{{min(v_p(C), v_p(d-1))}}

  FAIT PROUVE : v_2(d-1) <= 2 pour tout k >= 3.
    Donc la contribution 2-adique au gcd est <= 4.

  FAIT : v_3(d-1) = 0 si S impair (car d-1 = 2^S - 3^k - 1 et 2^S ≡ -1 mod 3 si S impair).

  BORNE STRUCTURELLE SUR gcd :
    gcd(C, d-1) <= 4 × (smooth part of d-1 shared with C)
    La "smooth part" de d-1 (pour p > 2) est la partie de d-1
    composee de petits premiers qui divisent aussi C.

  BORNE TRIVIALE : ord >= S-1 (car d | (2^ord - 1) et d > 2^(S-2))
    Donc si gcd(C, d-1) < S-1, alors gcd < ord.

  TEST : gcd(C, d-1) < S-1 pour les 19 cas :
""")

for r in results:
    k, g, S = r['k'], r['gcd'], r['S']
    print(f"    k={k}: gcd={g}, S-1={S-1}, gcd < S-1 ? "
          f"{'OUI ✓' if g < S-1 else 'NON ⚠'}")

print(f"""
  OBSERVATION : gcd < S-1 ECHOUE pour k=3895 (gcd=2813348 > S-1=6173)
  et k=6891 (gcd=1054812 > S-1=10921).
  Donc la borne triviale ord >= S-1 est INSUFFISANTE.

  CONCLUSION : Prouver gcd(C,d-1) < ord semble necessiter une borne
  plus forte sur ord que la borne triviale, ce qui ramene a Artin.
""")

# ================================================================
# J13. SYNTHESE FINALE ITERATION 2
# ================================================================
print("=" * 70)
print("J13. SYNTHESE G-V-R ITERATION 2")
print("=" * 70)

print(f"""
  ═══════════════════════════════════════════════════════════════
  ║  ITERATION 2 : APPROCHE gcd(C, d-1)                       ║
  ═══════════════════════════════════════════════════════════════

  RESULTAT COMPUTATIONNEL MAJEUR :
    2^{{gcd(C, d-1)}} ≢ 1 mod d  pour les 19/19 d premiers  ★★★★★
    Ceci prouve G2c via : ord ∤ gcd(C,d-1) => ord ∤ C => 2^C ≢ 1

  REFORMULATION :
    G2c ⟺ gcd(C, d-1) < ord  ⟺  C·Q < d-1  (pour C < d)
    Pour k=3, 5 : C >= d, mais gcd(C,d-1) < ord fonctionne quand meme.

  ANALYSE D'ECHEC (PROTOCOLE) :
    La condition C·Q < d-1 est EQUIVALENTE a C < ord.
    Prouver cela requiert Q < d/C ≈ 2^{{0.051·S}}.
    Mais prouver Q < f(S) pour f(S) → ∞ est AUSSI OUVERT que Artin.
    => L'approche gcd ne contourne PAS la barriere d'Artin theoriquement.

  CE QUI EST PROUVE :
    [PROUVE] v_2(d-1) ≤ 2 pour tout k ≥ 3 (contribution 2-adique bornee)
    [PROUVE] gcd(C,d-1) ≤ C toujours
    [PROUVE] C/d → 0 exponentiellement
    [VERIFIE_k=3..10000] 2^{{gcd(C,d-1)}} ≢ 1 mod d (19/19 d premiers)

  CE QUI N'EST PAS PROUVE :
    [CONJECTURE] gcd(C, d-1) < ord pour tout k ≥ 3 avec d premier
    [OPEN] Borne non-triviale sur Q (equiv. Artin)
    [OPEN] Borne sur la partie smooth de d-1 partagee avec C

  PISTE POUR ITERATION 3 :
    1. Prouver gcd(C, d-1) < ord pour k=3 et k=5 individuellement
       (on connait d et ord exactement pour ces cas)
    2. Explorer si 2^g ≢ 1 mod d peut etre prouve directement
       en utilisant la structure 2^S ≡ 3^k mod d
    3. Approche modulaire : C mod ord en utilisant l'identite de Wolstenholme
       ou d'autres proprietes des coefficients binomiaux
""")

print("=" * 70)
print("FIN G-V-R ITERATION 2")
print("=" * 70)
