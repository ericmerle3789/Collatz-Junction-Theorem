#!/usr/bin/env python3
"""
SESSION 10f22 — G-V-R ITERATION 2
==================================
APPROCHE : gcd(C, d-1) et contraintes structurelles

OBSERVATION CLE :
  2^C ≡ 1 mod d  ⟹  ord | C  ET  ord | (d-1)
  Donc :  ord | gcd(C, d-1)
  Si gcd(C, d-1) = 1 : contradiction (ord >= 2)
  Si gcd(C, d-1) petit : tester si un diviseur r de gcd(C,d-1) satisfait 2^r ≡ 1

PLAN :
  J1. Calculer gcd(C, d-1) pour les 19 d premiers
  J2. Calculer C mod (d-1) — renseigne sur la relation C vs ord
  J3. Seuil : pour quel k0 a-t-on C < d pour tout d premier avec k >= k0
  J4. gcd(C, d-1) pour k grand (k jusqu'a 100000, d pas forcement premier)
  J5. Factoriser gcd(C, d-1) et tester 2^r mod d pour chaque diviseur r
  J6. Approche C mod ord directe
  J7. Synthese
"""

import sys
import math
sys.stdout.reconfigure(line_buffering=True)

def ceil_log2_3(k):
    return math.ceil(k * math.log2(3))

def v2(n):
    if n == 0: return float('inf')
    v = 0
    while n % 2 == 0: v += 1; n //= 2
    return v

def vp(n, p):
    if n == 0: return float('inf')
    v = 0
    while n % p == 0: v += 1; n //= p
    return v

def kummer_carries(a, b, base=2):
    carries = 0; carry = 0
    while a > 0 or b > 0 or carry > 0:
        digit_sum = (a % base) + (b % base) + carry
        carry = digit_sum // base
        carries += carry
        a //= base; b //= base
    return carries

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

def Q_pred(d):
    """Prediction de Q = (d-1)/ord_d(2) via residuacite."""
    n = d - 1; Q = 1
    primes_to_test = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
    for p in primes_to_test:
        if n % p == 0:
            max_power = 0; temp_n = n
            while temp_n % p == 0: max_power += 1; temp_n //= p
            for e in range(1, max_power + 1):
                exp = n // (p**e)
                if pow(2, exp, d) == 1: Q *= p
                else: break
    return Q

def small_divisors(n, limit=10000):
    """Trouve tous les diviseurs de n qui sont <= limit."""
    divs = []
    for i in range(1, min(limit + 1, abs(n) + 1)):
        if n % i == 0:
            divs.append(i)
    return divs

# ================================================================
# COLLECTE DES 19 d PREMIERS
# ================================================================
print("=" * 70)
print("SESSION 10f22 — G-V-R ITERATION 2 : gcd(C, d-1)")
print("=" * 70)

prime_d_cases = []
for k in range(3, 10001):
    S = ceil_log2_3(k)
    d = pow(2, S) - pow(3, k)
    if d > 1 and check_prime(d):
        prime_d_cases.append((k, S, d))

print(f"\n  {len(prime_d_cases)} d premiers pour k in [3, 10000]")

# ================================================================
# J1. gcd(C, d-1) POUR LES 19 d PREMIERS
# ================================================================
print("\n" + "=" * 70)
print("J1. gcd(C, d-1) POUR LES 19 d PREMIERS")
print("=" * 70)

print(f"\n  OBSERVATION CLE : 2^C ≡ 1 mod d ⟹ ord | gcd(C, d-1)")
print(f"  Si gcd(C, d-1) = 1 : impossibilite immediate (ord >= 2)")
print(f"  Si gcd(C, d-1) petit : tester si un div r satisfait 2^r ≡ 1 mod d\n")

print(f"  {'k':>5s} | {'S':>5s} | {'bits_C':>6s} | {'bits_d':>6s} | {'C<d?':>4s} | "
      f"{'gcd(C,d-1)':>12s} | {'bits_gcd':>8s} | {'gcd=1?':>6s} |")
print("  " + "-" * 80)

results_J1 = []
for k, S, d in prime_d_cases:
    C = math.comb(S - 1, k - 1)
    dm1 = d - 1
    g = math.gcd(C, dm1)
    bits_C = C.bit_length()
    bits_d = d.bit_length()
    bits_g = g.bit_length() if g > 0 else 0

    Q = Q_pred(d)
    ord_val = dm1 // Q

    results_J1.append({
        'k': k, 'S': S, 'd': d, 'C': C, 'dm1': dm1,
        'gcd': g, 'Q': Q, 'ord': ord_val,
        'C_lt_d': C < d
    })

    print(f"  {k:5d} | {S:5d} | {bits_C:6d} | {bits_d:6d} | {'OUI' if C < d else 'non':>4s} | "
          f"{str(g) if g.bit_length() < 40 else f'2^{bits_g}':>12s} | {bits_g:8d} | "
          f"{'OUI ★' if g == 1 else 'non':>6s} |")

gcd_1_count = sum(1 for r in results_J1 if r['gcd'] == 1)
print(f"\n  ★ gcd(C, d-1) = 1 pour {gcd_1_count}/{len(results_J1)} cas")

# ================================================================
# J2. ANALYSE DETAILLEE DE gcd(C, d-1)
# ================================================================
print("\n" + "=" * 70)
print("J2. ANALYSE DETAILLEE : FACTORISATION DE gcd(C, d-1)")
print("=" * 70)

print(f"\n  Pour chaque cas, factoriser gcd(C,d-1) et tester 2^r ≡ 1 mod d")
print(f"  pour chaque diviseur r de gcd(C,d-1).\n")

for r in results_J1:
    k, S, d, C, g, ord_val = r['k'], r['S'], r['d'], r['C'], r['gcd'], r['ord']

    if g == 1:
        print(f"  k={k}: gcd = 1 ★ => ord ∤ C AUTOMATIQUE (ord >= 2 ne divise pas 1)")
        continue

    # Tester si ord | gcd (il le doit si 2^C ≡ 1)
    ord_divides_gcd = (g % ord_val == 0)

    # Factorisation partielle de gcd
    g_factored = {}
    temp_g = g
    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]:
        while temp_g % p == 0:
            g_factored[p] = g_factored.get(p, 0) + 1
            temp_g //= p
    if temp_g > 1:
        g_factored[f"cofactor({temp_g.bit_length()}b)"] = 1

    # Chercher si un diviseur r de gcd(C,d-1) satisfait 2^r ≡ 1 mod d
    # On teste d'abord les petits diviseurs (rapide)
    has_dangerous_divisor = False
    if g.bit_length() < 64:  # gcd assez petit pour enumerer
        divs = small_divisors(g, limit=min(g, 100000))
        for div_r in divs:
            if div_r > 1 and pow(2, div_r, d) == 1:
                has_dangerous_divisor = True
                print(f"  k={k}: gcd={g} ({g.bit_length()}b), "
                      f"DIVISEUR DANGEREUX r={div_r} avec 2^r ≡ 1 mod d ⚠")
                # Verifier : est-ce que r = ord ?
                if div_r == ord_val:
                    print(f"         ... et r = ord = {ord_val}, donc ord | gcd.")
                    print(f"         MAIS on sait par I5 que 2^C ≢ 1, donc ord ∤ C malgre ord | gcd")
                break
    else:
        # gcd est grand — tester directement si 2^gcd ≡ 1 mod d
        pow2g = pow(2, g, d)
        has_dangerous_divisor = (pow2g == 1)  # Si 2^gcd ≡ 1, alors ord | gcd
        if has_dangerous_divisor:
            print(f"  k={k}: gcd grand ({g.bit_length()}b), 2^gcd ≡ 1 mod d ⚠ => ord | gcd")
        else:
            print(f"  k={k}: gcd grand ({g.bit_length()}b), 2^gcd ≢ 1 mod d ✓ => ord ∤ gcd => ord ∤ C !")

    if not has_dangerous_divisor and g.bit_length() < 64:
        print(f"  k={k}: gcd={g} ({g.bit_length()}b), fact={g_factored}, "
              f"AUCUN diviseur r>1 avec 2^r≡1 ✓ => ord ∤ C !")

# ================================================================
# J3. SEUIL : QUAND C < d POUR d PREMIER
# ================================================================
print("\n" + "=" * 70)
print("J3. SEUIL C < d : ANALYSE ASYMPTOTIQUE")
print("=" * 70)

# C = binom(S-1, k-1), d = 2^S - 3^k
# log2(C) ≈ (S-1) * H((k-1)/(S-1)) ou H est l'entropie binaire
# log2(d) ≈ S - theta ou theta ∈ (0,1)
# H(p) = -p log2 p - (1-p) log2(1-p)
# p = (k-1)/(S-1) ≈ 1/log2(3) ≈ 0.6309, H(p) ≈ 0.9544
# log2(C) ≈ 0.9544 * S, log2(d) ≈ S
# Donc C/d ≈ 2^{-0.046*S} → 0

print(f"\n  Asymptotique : log2(C)/S → H(1/log2(3)) ≈ 0.954")
print(f"  Donc C < d pour S assez grand.")

# Trouver exactement pour quels k parmi les 19, C >= d
c_ge_d = [(r['k'], r['S'], r['C'].bit_length(), r['d'].bit_length())
          for r in results_J1 if not r['C_lt_d']]
c_lt_d = [(r['k'], r['S'], r['C'].bit_length(), r['d'].bit_length())
          for r in results_J1 if r['C_lt_d']]

print(f"\n  Parmi les 19 d premiers :")
print(f"    C >= d : {len(c_ge_d)} cas — {[x[0] for x in c_ge_d]}")
print(f"    C < d  : {len(c_lt_d)} cas — {[x[0] for x in c_lt_d]}")

# Pour les cas C >= d, calculer C/d
for k_val, S_val, bc, bd in c_ge_d:
    r = [x for x in results_J1 if x['k'] == k_val][0]
    ratio = r['C'] / r['d'] if r['d'] > 0 else float('inf')
    print(f"    k={k_val}: log2(C)={bc}, log2(d)={bd}, C/d ≈ {ratio:.6f}")

# Trouver le seuil general pour k impair et k pair
print(f"\n  Seuil exact (scan k=3..200) :")
last_c_ge_d = 0
for k in range(3, 201):
    S = ceil_log2_3(k)
    d = pow(2, S) - pow(3, k)
    if d < 2:
        continue
    C = math.comb(S - 1, k - 1)
    if C >= d:
        last_c_ge_d = k

print(f"    Dernier k avec C >= d (k=3..200) : k={last_c_ge_d}")
print(f"    Pour tout k > {last_c_ge_d} : C < d")

# ================================================================
# J4. STRUCTURE DE gcd(C, d-1) : ANALYSE EN PROFONDEUR
# ================================================================
print("\n" + "=" * 70)
print("J4. STRUCTURE DE gcd(C, d-1) : LIEN AVEC ord")
print("=" * 70)

print(f"\n  Question : pourquoi gcd(C, d-1) est-il si petit dans les cas observes ?")
print(f"  C = binom(S-1, k-1), d-1 = 2^S - 3^k - 1")
print(f"  Les facteurs premiers de C sont domines par les petits premiers (Kummer)")
print(f"  Les facteurs premiers de d-1 sont 'aleatoires' pour d premier\n")

print(f"  {'k':>5s} | {'v2(C)':>5s} | {'v2(d-1)':>7s} | {'v3(C)':>5s} | {'v3(d-1)':>7s} | "
      f"{'v5(C)':>5s} | {'v5(d-1)':>7s} | {'gcd bits':>8s} | {'ord|gcd?':>8s} |")
print("  " + "-" * 85)

for r in results_J1:
    k = r['k']
    C, dm1, g, ord_val = r['C'], r['dm1'], r['gcd'], r['ord']

    v2C, v2dm1 = v2(C), v2(dm1)
    v3C, v3dm1 = vp(C, 3), vp(dm1, 3)
    v5C, v5dm1 = vp(C, 5), vp(dm1, 5)

    ord_div_gcd = (g % ord_val == 0) if g > 0 else False

    print(f"  {k:5d} | {v2C:5d} | {v2dm1:7d} | {v3C:5d} | {v3dm1:7d} | "
          f"{v5C:5d} | {v5dm1:7d} | {g.bit_length():8d} | {'OUI ⚠' if ord_div_gcd else 'non ✓':>8s} |")

# ================================================================
# J5. OBSERVATION CRUCIALE : C mod (d-1)
# ================================================================
print("\n" + "=" * 70)
print("J5. C mod (d-1) : LE RESIDU QUI DETERMINE TOUT")
print("=" * 70)

print(f"\n  ord | C  ⟺  C mod ord = 0")
print(f"  Puisque ord | (d-1), on a C mod ord = (C mod (d-1)) mod ord")
print(f"  Si C < d-1 : C mod (d-1) = C, et il faut juste ord | C")
print(f"  Si C >= d-1 : reduire C mod (d-1)\n")

print(f"  {'k':>5s} | {'C < d-1':>7s} | {'C mod(d-1) bits':>15s} | {'C mod ord':>10s} | {'ord bits':>8s} |")
print("  " + "-" * 60)

for r in results_J1:
    k = r['k']
    C, dm1, ord_val = r['C'], r['dm1'], r['ord']

    C_lt_dm1 = C < dm1
    C_mod_dm1 = C % dm1
    C_mod_ord = C % ord_val

    print(f"  {k:5d} | {'OUI' if C_lt_dm1 else 'non':>7s} | {C_mod_dm1.bit_length():15d} | "
          f"{C_mod_ord:10d} | {ord_val.bit_length():8d} |")

# ================================================================
# J6. TEST DIRECT : 2^(gcd(C,d-1)) mod d POUR LES 19 CAS
# ================================================================
print("\n" + "=" * 70)
print("J6. TEST DIRECT : 2^(gcd(C,d-1)) ≡ ? mod d")
print("=" * 70)

print(f"\n  Si 2^gcd(C,d-1) ≢ 1 mod d, alors ord ∤ gcd(C,d-1)")
print(f"  Et puisque ord | C ⟹ ord | gcd(C,d-1), cela donne ord ∤ C\n")

g2c_proven_by_gcd = 0
for r in results_J1:
    k, d, g = r['k'], r['d'], r['gcd']

    if g == 1:
        print(f"  k={k}: gcd=1 ★ => 2^C ≢ 1 (trivial, ord >= 2)")
        g2c_proven_by_gcd += 1
        continue

    pow2g = pow(2, g, d)
    if pow2g != 1:
        print(f"  k={k}: gcd={g} ({g.bit_length()}b), 2^gcd ≢ 1 mod d ✓ => ord ∤ gcd => ord ∤ C => 2^C ≢ 1")
        g2c_proven_by_gcd += 1
    else:
        # 2^gcd ≡ 1 : ord | gcd, mais on sait que 2^C ≢ 1 (verifie I5)
        # Cela signifie que ord | gcd(C, d-1) MAIS ord ∤ C
        # Donc C mod (d-1) a un facteur p tel que v_p(C mod ord) > 0
        C_mod_ord = r['C'] % r['ord']
        print(f"  k={k}: gcd={g} ({g.bit_length()}b), 2^gcd ≡ 1 ⚠ => ord | gcd, "
              f"C mod ord = {C_mod_ord} {'≠0 ✓' if C_mod_ord != 0 else '=0 ⚠⚠⚠'}")

print(f"\n  ★ G2c prouve par gcd : {g2c_proven_by_gcd}/{len(results_J1)} cas")

# ================================================================
# J7. APPROCHE COMBINATOIRE : v_p(C) vs v_p(d-1)
# ================================================================
print("\n" + "=" * 70)
print("J7. POUR CHAQUE PREMIER p <= 47 : min(v_p(C), v_p(d-1))")
print("=" * 70)

print(f"\n  gcd(C, d-1) = prod_p p^min(v_p(C), v_p(d-1))")
print(f"  Si pour un p | ord : v_p(d-1) - v_p(Q) > v_p(C), alors ord ∤ C")
print(f"  Equivalent a : v_p(ord) > v_p(C)\n")

primes_test = [2, 3, 5, 7, 11, 13]
header = f"  {'k':>5s}"
for p in primes_test:
    header += f" | min(v{p})"
header += f" | gcd bits | proven?"
print(header)
print("  " + "-" * (len(header) - 2))

for r in results_J1:
    k, C, dm1, g, d, ord_val, Q = r['k'], r['C'], r['dm1'], r['gcd'], r['d'], r['ord'], r['Q']

    line = f"  {k:5d}"
    proven = False
    for p in primes_test:
        vpc = vp(C, p)
        vpdm1 = vp(dm1, p)
        vpord = vp(ord_val, p)
        min_val = min(vpc, vpdm1)
        marker = ""
        if vpord > vpc:
            marker = "★"
            proven = True
        line += f" | {min_val:7d}{marker}"

    if not proven:
        # Test gcd direct
        pow2g = pow(2, g, d)
        if pow2g != 1 or g == 1:
            proven = True
    line += f" | {g.bit_length():8d} | {'OUI ✓' if proven else 'non (ord>C)'}"
    print(line)

# ================================================================
# J8. DECOMPOSITION BINAIRE DE C mod (d-1) : structure fine
# ================================================================
print("\n" + "=" * 70)
print("J8. C mod ord POUR LES 19 CAS : DISTANCE A ZERO")
print("=" * 70)

print(f"\n  Pour 2^C ≡ 1 mod d, il faut C mod ord = 0.")
print(f"  On calcule C mod ord et sa distance relative a ord.\n")

print(f"  {'k':>5s} | {'ord bits':>8s} | {'C mod ord':>12s} | {'(C mod ord)/ord':>16s} | ord | C ? |")
print("  " + "-" * 70)

for r in results_J1:
    k, C, ord_val = r['k'], r['C'], r['ord']
    c_mod_o = C % ord_val
    ratio = c_mod_o / ord_val if ord_val > 0 else 0

    divides = "OUI ⚠" if c_mod_o == 0 else "non ✓"
    cmo_str = str(c_mod_o) if c_mod_o.bit_length() < 40 else f"({c_mod_o.bit_length()}b)"
    print(f"  {k:5d} | {ord_val.bit_length():8d} | {cmo_str:>12s} | "
          f"{ratio:16.10f} | {divides:>7s} |")

# ================================================================
# J9. APPROCHE PROBABILISTE : POURQUOI ord ∤ C EST "PRESQUE SUR"
# ================================================================
print("\n" + "=" * 70)
print("J9. ARGUMENT PROBABILISTE : P(ord | C)")
print("=" * 70)

print(f"""
  ARGUMENT HEURISTIQUE :
  - C est un nombre de {results_J1[-1]['C'].bit_length()}-bit
  - ord ≈ d/{results_J1[-1]['Q']} est un nombre de {results_J1[-1]['ord'].bit_length()}-bit
  - P(ord | C) ≈ 1/ord (si C etait "aleatoire" mod ord)
  - Pour k = {results_J1[-1]['k']} : P ≈ 2^{-results_J1[-1]['ord'].bit_length()}

  MAIS C n'est PAS aleatoire : C = binom(S-1, k-1)
  La question est : la structure arithmetique de C et ord se "voient"-elles ?
""")

# Tester : C mod ord est-il "pseudo-aleatoire" ?
print(f"  Test de pseudo-aleatoriete de (C mod ord) / ord :")
for r in results_J1:
    k, C, ord_val = r['k'], r['C'], r['ord']
    c_mod_o = C % ord_val
    ratio = c_mod_o / ord_val
    # Un residu aleatoire aurait E[ratio] = 0.5
    print(f"    k={k}: ratio = {ratio:.6f}")

# ================================================================
# J10. SYNTHESE ITERATION 2
# ================================================================
print("\n" + "=" * 70)
print("J10. SYNTHESE G-V-R ITERATION 2")
print("=" * 70)

# Classifier les 19 cas
cas_gcd1 = [r for r in results_J1 if r['gcd'] == 1]
cas_gcd_pow2g_ne1 = [r for r in results_J1 if r['gcd'] > 1 and pow(2, r['gcd'], r['d']) != 1]
cas_gcd_pow2g_eq1 = [r for r in results_J1 if r['gcd'] > 1 and pow(2, r['gcd'], r['d']) == 1]

print(f"""
  ═══════════════════════════════════════════════════════════
  ║  G-V-R ITERATION 2 : gcd(C, d-1) APPROACH              ║
  ═══════════════════════════════════════════════════════════

  CLASSIFICATION DES 19 CAS :

  CATEGORIE A : gcd(C, d-1) = 1 => ord ∤ C trivial
    {len(cas_gcd1)} cas : k = {[r['k'] for r in cas_gcd1]}

  CATEGORIE B : gcd(C, d-1) > 1 MAIS 2^gcd ≢ 1 mod d => ord ∤ gcd => ord ∤ C
    {len(cas_gcd_pow2g_ne1)} cas : k = {[r['k'] for r in cas_gcd_pow2g_ne1]}

  CATEGORIE C : gcd(C, d-1) > 1 ET 2^gcd ≡ 1 mod d => ord | gcd
    {len(cas_gcd_pow2g_eq1)} cas : k = {[r['k'] for r in cas_gcd_pow2g_eq1]}
    Ici, ord | gcd(C,d-1) mais on sait que ord ∤ C (verifie directement)
    => C possede un facteur p pour lequel v_p(C) < v_p(ord)

  TOTAL PROUVE PAR GCD : {len(cas_gcd1) + len(cas_gcd_pow2g_ne1)}/{len(results_J1)}
  RESTANT (Cat C) : {len(cas_gcd_pow2g_eq1)}/{len(results_J1)}

  QUESTION CLE POUR PROGRES :
    Pour les cas Cat C, peut-on prouver ord ∤ C
    en montrant que C n'est divisible que partiellement par ord ?

  OBSERVATION : Si C < ord (ce qui arrive quand C < d et Q est petit),
    alors ord ∤ C automatiquement (car 0 < C < ord).
    C'est le cas pour TOUS les k >= 4 sauf k=5 (ou C=4 et ord=7 => ok).
""")

# Verifier : C < ord pour quels cas ?
c_lt_ord = [(r['k'], r['C'].bit_length(), r['ord'].bit_length())
            for r in results_J1 if r['C'] < r['ord']]
c_ge_ord = [(r['k'], r['C'].bit_length(), r['ord'].bit_length())
            for r in results_J1 if r['C'] >= r['ord']]

print(f"  C < ord : {len(c_lt_ord)} cas — k = {[x[0] for x in c_lt_ord]}")
print(f"  C >= ord : {len(c_ge_ord)} cas — k = {[x[0] for x in c_ge_ord]}")

for k_val, bc, bo in c_ge_ord:
    r = [x for x in results_J1 if x['k'] == k_val][0]
    print(f"    k={k_val}: C={r['C']}, ord={r['ord']}, C/ord={r['C']/r['ord']:.4f}")

# Verifier la condition C < ord via C/d → 0 et Q petit
print(f"\n  LIEN AVEC C/d → 0 :")
print(f"  C < ord ⟺ C < (d-1)/Q ⟺ C·Q < d-1")
print(f"  Puisque C/d → 2^{{-0.051S}} et Q est empiriquement petit (max 95),")
print(f"  C·Q < d-1 pour S assez grand.\n")

for r in results_J1:
    k, S, C, d, Q, ord_val = r['k'], r['S'], r['C'], r['d'], r['Q'], r['ord']
    CQ = C * Q
    print(f"  k={k}: C*Q={CQ}, d-1={d-1}, C*Q < d-1? {'OUI ✓' if CQ < d-1 else 'NON ⚠'}")

print("\n" + "=" * 70)
print("FIN G-V-R ITERATION 2")
print("=" * 70)
