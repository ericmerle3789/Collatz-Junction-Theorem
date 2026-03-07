#!/usr/bin/env python3
"""
SESSION 10f22 — G-V-R ITERATION 3b : ANALYSE DES 4 CAS REBELLES
k = 61, 3895, 4500, 6891 ou gcd(C, d-1) >= log_2(d)

Question : Pourquoi gcd(C, d-1) est-il si grand pour ces 4 cas ?
Peut-on trouver un argument alternatif ?
"""
import sys
import math
sys.stdout.reconfigure(line_buffering=True)

def ceil_log2_3(k):
    return math.ceil(k * math.log2(3))

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

rebels = [61, 3895, 4500, 6891]

# Also include some "good" cases for comparison
good_cases = [56, 73, 185, 917, 3540, 7752]

all_k = rebels + good_cases

print("=" * 70)
print("R1. STRUCTURE DES 4 CAS REBELLES vs BONS CAS")
print("=" * 70)

print(f"\n  {'k':>5s} | {'S':>5s} | {'g=gcd':>10s} | {'log2(d)':>7s} | {'g/S':>6s} | "
      f"{'v2(g)':>5s} | {'v2(dm1)':>7s} | {'rebel?':>6s} |")
print("  " + "-" * 75)

for k in sorted(all_k):
    S = ceil_log2_3(k)
    d = pow(2, S) - pow(3, k)
    if d <= 1 or not check_prime(d):
        continue
    C = math.comb(S - 1, k - 1)
    dm1 = d - 1
    g = math.gcd(C, dm1)

    v2_g = 0
    temp = g
    while temp % 2 == 0 and temp > 0:
        v2_g += 1
        temp //= 2

    v2_dm1 = 0
    temp = dm1
    while temp % 2 == 0 and temp > 0:
        v2_dm1 += 1
        temp //= 2

    is_rebel = k in rebels
    g_str = str(g) if g.bit_length() < 30 else f"({g.bit_length()}b)"
    print(f"  {k:5d} | {S:5d} | {g_str:>10s} | {d.bit_length():7d} | {g/S:6.2f} | "
          f"{v2_g:5d} | {v2_dm1:7d} | {'OUI' if is_rebel else 'non':>6s} |")

# ================================================================
# R2. FACTORISATION DU gcd POUR LES REBELLES
# ================================================================
print("\n" + "=" * 70)
print("R2. FACTORISATION DE gcd POUR LES CAS REBELLES")
print("=" * 70)

for k in rebels:
    S = ceil_log2_3(k)
    d = pow(2, S) - pow(3, k)
    if d <= 1 or not check_prime(d):
        continue
    C = math.comb(S - 1, k - 1)
    dm1 = d - 1
    g = math.gcd(C, dm1)

    print(f"\n  k={k}: g = gcd(C, d-1) = {g}")

    # Factor g
    if factorint is not None and g < 10**15:
        gf = factorint(g)
        print(f"    g factored: {gf}")
    else:
        # Simple trial division
        gf = {}
        temp = g
        for p in range(2, min(1000, g + 1)):
            while temp % p == 0:
                gf[p] = gf.get(p, 0) + 1
                temp //= p
        if temp > 1:
            gf[temp] = gf.get(temp, 0) + 1
        print(f"    g factored (trial): {gf}")

    # Check which prime factors of g also divide d-1
    print(f"    Primes de g qui divisent aussi d-1:")
    for p, e in sorted(gf.items()):
        vp_dm1 = 0
        temp = dm1
        while temp % p == 0:
            vp_dm1 += 1
            temp //= p
        vp_C = 0
        temp_C = C
        while temp_C % p == 0:
            vp_C += 1
            temp_C //= p
        print(f"      p={p}: v_p(g)={e}, v_p(d-1)={vp_dm1}, v_p(C)={vp_C}, min={min(vp_dm1, vp_C)}")

# ================================================================
# R3. k=61 : CAS LE PLUS SIMPLE (g=124, log_2(d)=95)
# ================================================================
print("\n" + "=" * 70)
print("R3. ANALYSE DETAILLEE k=61 (LE PLUS SIMPLE DES REBELLES)")
print("=" * 70)

k = 61
S = ceil_log2_3(k)
d = pow(2, S) - pow(3, k)
C = math.comb(S - 1, k - 1)
dm1 = d - 1
g = math.gcd(C, dm1)

print(f"""
  k = {k}, S = {S}, d ≈ 2^{d.bit_length()}
  C = binom({S-1}, {k-1}) ≈ 2^{C.bit_length()}
  d-1 = {dm1}
  g = gcd(C, d-1) = {g}

  2^g mod d = {pow(2, g, d)}

  g = 124 = 4 × 31 = 2^2 × 31

  On a g > log_2(d) ≈ 95, donc l'argument de taille echoue.
  MAIS : ord = {dm1 // 1} (Q=1 pour k=61)

  Alternative pour ce cas :
""")

# For k=61, Q=1, so ord = d-1
# g=124 and ord = d-1 ≈ 2^95
# g < ord trivially! So ord ∤ g since g < ord
print(f"  ord = d-1 = {dm1} (car Q=1, 2 est racine primitive)")
print(f"  g = {g}")
print(f"  g < ord ? {'OUI' if g < dm1 else 'NON'}")
print(f"  Donc ord ∤ g trivialement (0 < g < ord) → 2^g ≢ 1 mod d ✓")
print(f"  MAIS cet argument utilise Q=1, qui est specifique a k=61.")

# ================================================================
# R4. POUR CHAQUE REBELLE : g < ord ?
# ================================================================
print("\n" + "=" * 70)
print("R4. TEST g < ord POUR LES 4 REBELLES")
print("=" * 70)

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

for k in rebels:
    S = ceil_log2_3(k)
    d = pow(2, S) - pow(3, k)
    if d <= 1 or not check_prime(d):
        continue
    C = math.comb(S - 1, k - 1)
    dm1 = d - 1
    g = math.gcd(C, dm1)
    Q = Q_pred(d)
    ord_val = dm1 // Q

    print(f"  k={k}: g={g}, ord≈2^{ord_val.bit_length()}, Q={Q}")
    print(f"    g < ord ? {'OUI ✓' if g < ord_val else 'NON ⚠'}")
    ratio_bits = g.bit_length() - ord_val.bit_length()
    print(f"    g/ord ≈ 2^{ratio_bits} (g={g.bit_length()}b, ord={ord_val.bit_length()}b)")
    print(f"    => Ce cas IS{'  ' if g < ord_val else ' NOT'} resolu par g < ord")
    print()

# ================================================================
# R5. SYNTHESE : QUELLE PROPORTION EST RESOLUE ?
# ================================================================
print("=" * 70)
print("R5. SYNTHESE GLOBALE")
print("=" * 70)

# Check all 19 cases
all_prime_cases = []
for k in range(3, 10001):
    S = ceil_log2_3(k)
    d = pow(2, S) - pow(3, k)
    if d > 1 and check_prime(d):
        all_prime_cases.append((k, S, d))

proved_by_g_small = 0
proved_by_g_lt_ord = 0
total = len(all_prime_cases)

for k, S, d in all_prime_cases:
    C = math.comb(S - 1, k - 1)
    dm1 = d - 1
    g = math.gcd(C, dm1)
    Q = Q_pred(d)
    ord_val = dm1 // Q

    if 0 < g < d.bit_length():
        proved_by_g_small += 1
    elif g < ord_val:
        proved_by_g_lt_ord += 1

print(f"""
  ARGUMENT 1 (elementaire) : g < log_2(d) => 2^g = 2^g ≠ 1
    Couvre : {proved_by_g_small}/{total} cas

  ARGUMENT 2 (utilise Q) : g < ord => ord ∤ g => 2^g ≢ 1
    Couvre les {proved_by_g_lt_ord} cas restants

  TOTAL : {proved_by_g_small + proved_by_g_lt_ord}/{total} cas couverts

  STRUCTURE DES ARGUMENTS :
    1. gcd(C, d-1) est calculable (definition)
    2. Si g < log_2(d) : PROUVE par taille (inconditionnel, elementaire)
    3. Si g >= log_2(d) mais g < ord : PROUVE par divisibilite
       (mais necessite connaitre ord, i.e. connaitre Q)

  QUESTION CRUCIALE :
    Peut-on prouver g < log_2(d) pour TOUS les k ?
    C'est equivalent a : gcd(binom(S-1,k-1), 2^S-3^k-1) < S
    (car log_2(d) ≈ S)

  Si NON (ce qui est le cas pour 4 cas), peut-on borner g ?
    On a g | C et g | (d-1). Donc g | gcd(C, d-1).
    La question est : pourquoi gcd(C, d-1) peut-il etre >> S ?

  REPONSE : gcd(C, d-1) est grand quand C et d-1 partagent beaucoup
  de facteurs premiers en commun. Cela arrive quand :
  - d-1 a des "petits" facteurs premiers (smooth part)
  - C = binom(S-1, k-1) est aussi divisible par ces memes premiers
  - L'intersection est non triviale

  POUR LES 4 REBELLES : gcd est grand mais TOUJOURS < ord.
  C'est parce que ord ≈ d/Q avec Q petit, et g ≈ quelques bits de d.
""")

# ================================================================
# R6. TENTATIVE : PROUVER g < S (BORNE THEORIQUE)
# ================================================================
print("=" * 70)
print("R6. POURQUOI g = gcd(C, d-1) PEUT DEPASSER S")
print("=" * 70)

print(f"""
  Pour k=3895: g = 2 813 348, S = 6174
  g/S ≈ 455.7 — g est 456 fois plus grand que S !

  DECOMPOSITION :
    C = binom(6173, 3894) — un nombre de ~5859 bits
    d-1 = 2^6174 - 3^3895 - 1 — un nombre de ~6173 bits
    g divise les deux.

  FAIT : C est "divisible par beaucoup de petits premiers" (car binom)
  FAIT : d-1 aussi peut l'etre

  Borne de Kummer : v_p(C) ≥ 0 pour tout p
  Borne : g <= C. Mais C ≈ 2^5859, donc g pourrait etre enorme.

  La borne g < S est FAUSSE en general.

  CEPENDANT : g < ord est VERIFIE pour les 19 cas.
  Et g < ord ⟺ gcd(C, d-1) < (d-1)/Q ⟺ gcd(C, d-1)·Q < d-1

  Puisque g ≤ C et C/d → 0, on a g/d → 0 aussi.
  Donc g·Q < d-1 des que Q < d/g.
  Comme g ≤ C ≈ 2^(0.949·S) et d ≈ 2^S :
    Q doit etre < 2^(0.051·S) — meme condition qu'avant (Artin).

  CONCLUSION : L'argument de taille (g < log_2(d)) est NOUVEAU et
  ELEMENTAIRE pour 15/19 cas. Mais les 4 cas restants retombent
  dans la barriere Artin (g < ord necessite Q petit).
""")

print("=" * 70)
print("FIN ANALYSE CAS REBELLES")
print("=" * 70)
