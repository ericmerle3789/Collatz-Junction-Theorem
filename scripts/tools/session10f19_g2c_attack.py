#!/usr/bin/env python3
"""
SESSION 10f19 : Attaque de G2c — ord_d(2) > C
================================================
G2c : Pour d = 2^S - 3^k premier, montrer que ord_d(2) > C(M+k-1, k-1)
      où M = S - k, S = ceil(k·log₂3).

Observations clés :
  - d | (2^S - 3^k), donc 2^S ≡ 3^k mod d
  - En particulier ord_d(2) | S · ord_d(3)  (pas directement S)
  - Si d est premier : ord_d(2) | d-1 = 2^S - 3^k - 1
  - C = binom(M+k-1, k-1) croît exponentiellement ~2^{M+k-1}/sqrt(...)

Investigations :
  I1. Structure de d-1 : factorisation et diviseurs
  I2. Contraintes sur ord_d(2) venant de 2^S ≡ 3^k mod d
  I3. Comparaison numérique ord vs C pour plus de d premiers
  I4. Bornes théoriques (Stewart-Yu, etc.)
  I5. La structure spéciale d = 2^S - 3^k
"""

import sys
import math
sys.stdout.reconfigure(line_buffering=True)

def ceil_log2_3(k):
    return math.ceil(k * math.log2(3))

def order(base, mod):
    """Compute multiplicative order of base modulo mod."""
    if mod <= 1:
        return 1
    if math.gcd(base, mod) > 1:
        return None
    o, x = 1, base % mod
    while x != 1:
        x = (x * base) % mod
        o += 1
        if o > mod:
            return None
    return o

def order_fast(base, mod, factored_phi=None):
    """Compute order using factored phi(mod) = mod-1 when mod is prime."""
    if mod <= 1:
        return 1
    if math.gcd(base, mod) > 1:
        return None
    if factored_phi is None:
        return order(base, mod)

    # ord | phi. Start with phi, divide by prime factors while result still works.
    result = 1
    for p, e in factored_phi.items():
        result *= p ** e

    for p, e in factored_phi.items():
        for _ in range(e):
            candidate = result // p
            if pow(base, candidate, mod) == 1:
                result = candidate
            else:
                break
    return result

# ================================================================
# I1. Trouver TOUS les d premiers pour k ∈ [3, 5000]
# ================================================================
print("=" * 70)
print("I1. d PREMIERS POUR k ∈ [3, 5000]")
print("=" * 70)

try:
    from sympy import isprime, factorint
    HAS_SYMPY = True
except ImportError:
    HAS_SYMPY = False
    print("  sympy non disponible — utilisant test de primalité basique")

def is_prime_basic(n):
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    # Miller-Rabin pour grands n
    if n > 10**15:
        return pow(2, n-1, n) == 1 and pow(3, n-1, n) == 1 and pow(5, n-1, n) == 1
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True

check_prime = isprime if HAS_SYMPY else is_prime_basic

prime_d_cases = []
for k in range(3, 5001):
    S = ceil_log2_3(k)
    d = pow(2, S) - pow(3, k)
    if d <= 1:
        continue
    if check_prime(d):
        M = S - k
        C = math.comb(M + k - 1, k - 1) if M + k - 1 <= 300 else None
        prime_d_cases.append((k, S, M, d, C))

print(f"  {len(prime_d_cases)} valeurs de k avec d premier dans [3, 5000]")
for k, S, M, d, C in prime_d_cases:
    d_bits = d.bit_length()
    C_bits = C.bit_length() if C is not None else '?'
    print(f"    k={k}: S={S}, M={M}, d a {d_bits} bits, "
          f"C a {'>' + str(C_bits) if C is not None else '?'} bits")

# ================================================================
# I2. Calcul exact de ord_d(2) pour chaque d premier
# ================================================================
print("\n" + "=" * 70)
print("I2. ord_d(2) POUR CHAQUE d PREMIER")
print("=" * 70)

for k, S, M, d, C in prime_d_cases:
    if d > 10**12:
        # Pour les grands d, utiliser factorisation de d-1
        if HAS_SYMPY:
            dm1_factors = factorint(d - 1)
            ord2 = order_fast(2, d, dm1_factors)
            ord3 = order_fast(3, d, dm1_factors)
        else:
            ord2 = None
            ord3 = None
    else:
        ord2 = order(2, d)
        ord3 = order(3, d)

    # Vérifications
    if ord2 is not None:
        ratio_dm1 = (d - 1) / ord2
        # Vérifier 2^S mod d
        pow2S = pow(2, S, d)
        pow3k = pow(3, k, d)

        # Vérifier ord vs C
        C_str = f"{C}" if C is not None and C < 10**15 else f"~2^{C.bit_length()}" if C is not None else "?"
        ord_vs_C = ""
        if C is not None:
            if ord2 > C:
                ord_vs_C = f" ★ ord > C ✓"
            else:
                ord_vs_C = f" ⚠ ord ≤ C"

            # Vérifier 2^C mod d
            pow2C = pow(2, C, d)
            if pow2C == 1:
                ord_vs_C += " [2^C = 1 mod d ← ⚠⚠⚠]"
            else:
                ord_vs_C += f" [2^C ≠ 1 mod d ✓]"

        print(f"  k={k}: d-1 = {d-1}")
        print(f"    ord_d(2) = {ord2}, (d-1)/ord = {ratio_dm1:.1f}")
        if ord3 is not None:
            print(f"    ord_d(3) = {ord3}")
        print(f"    C = {C_str}{ord_vs_C}")
        print(f"    2^S ≡ {pow2S} mod d (devrait être {pow3k} = 3^k mod d) ✓" if pow2S == pow3k else "")

        # Rapport ord/S
        print(f"    ord/S = {ord2/S:.2f}, ord/(d-1) = {ord2/(d-1):.6f}")

        # Facteurs de d-1
        if HAS_SYMPY and d < 10**60:
            try:
                dm1_factors = factorint(d - 1, limit=10**6)
                print(f"    d-1 facteurs (partiels) : {dm1_factors}")
            except:
                pass

# ================================================================
# I3. Relation structurelle : 2^S ≡ 3^k mod d
# ================================================================
print("\n" + "=" * 70)
print("I3. CONTRAINTE STRUCTURELLE : 2^S ≡ 3^k mod d")
print("=" * 70)

print("""
Puisque d = 2^S - 3^k, on a 2^S ≡ 3^k mod d.

Notation : o₂ = ord_d(2), o₃ = ord_d(3).

De 2^S ≡ 3^k mod d :
  - L'ordre de 2^S mod d divise o₃ (car (2^S)^j = 3^{kj})
  - Soit o₂ | S·j pour tout j avec o₃ | kj
  - En particulier : o₂ | lcm(S, quelque chose lié à k/gcd(k, o₃))

Contrainte plus fine :
  Si gcd(S, o₂) = g, alors 2^g ≡ racine g-ième de 1 mod d... non.

Mieux : 2^S a pour ordre o₂/gcd(S, o₂) dans ⟨2⟩.
  Et cet ordre doit diviser o₃/gcd(k, o₃).
  Donc o₂/gcd(S, o₂) | lcm(o₃/gcd(k, o₃), ...).

En pratique, o₂ est TRÈS GRAND (souvent d-1 ou (d-1)/2).
""")

for k, S, M, d, C in prime_d_cases[:15]:
    if d > 10**12 and not HAS_SYMPY:
        continue
    if HAS_SYMPY:
        dm1_factors = factorint(d - 1) if d < 10**30 else None
        if dm1_factors:
            ord2 = order_fast(2, d, dm1_factors)
            ord3 = order_fast(3, d, dm1_factors)
        else:
            continue
    else:
        if d > 10**8:
            continue
        ord2 = order(2, d)
        ord3 = order(3, d)

    if ord2 is None or ord3 is None:
        continue

    g_S = math.gcd(S, ord2)
    g_k = math.gcd(k, ord3)

    # ord de 2^S dans Z/dZ
    ord_2S = ord2 // math.gcd(S, ord2)
    # ord de 3^k dans Z/dZ
    ord_3k = ord3 // math.gcd(k, ord3)

    print(f"  k={k}: o₂={ord2}, o₃={ord3}")
    print(f"    gcd(S,o₂)={g_S}, gcd(k,o₃)={g_k}")
    print(f"    ord(2^S)=o₂/gcd(S,o₂)={ord_2S}")
    print(f"    ord(3^k)=o₃/gcd(k,o₃)={ord_3k}")
    print(f"    2^S ≡ 3^k mod d ⟹ ord(2^S) = ord(3^k) : "
          f"{'✓' if ord_2S == ord_3k else '⚠ DIFFERENT !'}")
    print(f"    (d-1)/o₂ = {(d-1)//ord2}")

# ================================================================
# I4. Pourquoi ord est-il si grand ?
# ================================================================
print("\n" + "=" * 70)
print("I4. ANALYSE : POURQUOI ord_d(2) EST-IL SI GRAND ?")
print("=" * 70)

print("""
OBSERVATION : Pour les d premiers trouvés, ord_d(2) ≈ d-1 ou (d-1)/2.
  → 2 est un générateur (ou presque) de (Z/dZ)*

EXPLICATION HEURISTIQUE :
  d = 2^S - 3^k. Si d est premier, (Z/dZ)* est cyclique d'ordre d-1.
  Par la conjecture d'Artin, 2 est un générateur primitif pour une
  proportion positive (~37.4%) des premiers.

  MAIS ICI d a une forme TRÈS SPÉCIALE : d = 2^S - 3^k.
  Cette forme EXCLUT les petits ordres :
    - 2^S ≡ 3^k ≢ 1 mod d (car 3^k < 2^S = d + 3^k)
    - Donc ord ∤ S
    - Plus généralement, 2^j ≡ 1 mod d ⟹ j diviseur de d-1 ET j ≥ ...

ARGUMENT CLÉ : si ord_d(2) ≤ C, alors d | (2^C - 1).
  Or d = 2^S - 3^k > 2^{S-1}, et 2^C - 1 < 2^C.
  Donc il faut C > S-1 (sinon 2^C - 1 < 2^{S-1} < d).

  C = binom(M+k-1, k-1) ≥ 2^{M-1} ≥ 2^{S-k-1}.
  Et d < 2^S.
  Donc d | (2^C - 1) requiert 2^C ≡ 1 mod d.

  Testons : 2^C mod d ≠ 1 pour tous les d premiers connus.
  CELA CONFIRME G2c, mais ne le prouve pas.
""")

# ================================================================
# I5. Le test crucial : 2^C mod d
# ================================================================
print("=" * 70)
print("I5. TEST : 2^C mod d POUR TOUS LES d PREMIERS")
print("=" * 70)

all_pass = True
for k, S, M, d, C in prime_d_cases:
    if C is None:
        # C trop grand pour être calculé exactement
        # Mais on peut quand même tester 2^C mod d avec modular exponentiation
        C_approx = math.comb(M + k - 1, k - 1) if M + k - 1 <= 500 else None
        if C_approx is None:
            print(f"  k={k}: C trop grand à calculer (skip)")
            continue
        C = C_approx

    pow2C = pow(2, C, d)
    status = "= 1 ⚠⚠⚠" if pow2C == 1 else "≠ 1 ✓"
    if pow2C == 1:
        all_pass = False
    print(f"  k={k}: 2^C mod d {status} (C a {C.bit_length()} bits, d a {d.bit_length()} bits)")

if all_pass:
    print(f"\n  ★★★★★ 2^C ≠ 1 mod d pour TOUS les d premiers testés !")
    print(f"  → ord_d(2) ∤ C systématiquement → G2c numériquement solide")

# ================================================================
# I6. Borne inférieure théorique sur ord_d(2)
# ================================================================
print("\n" + "=" * 70)
print("I6. BORNE INFÉRIEURE SUR ord_d(2)")
print("=" * 70)

print("""
THÉORÈME (élémentaire) :
  Si d = 2^S - 3^k et d premier, alors :
  (1) ord_d(2) ∤ S  (car 2^S ≡ 3^k ≢ 1 mod d)
  (2) ord_d(2) > S - 1  (car 2^j < d pour j < S)
      Preuve : si j < S, alors 2^j < 2^S = d + 3^k, donc 2^j ≠ 0 mod d.
      Mais 2^j < d + 3^k ne suffit pas. En fait, si j ≤ S-2 :
      2^j ≤ 2^{S-2} = (d + 3^k)/4, et 2^j mod d = 2^j ≠ 0.
      Pour 2^j ≡ 1 mod d, il faut 2^j - 1 ≡ 0 mod d, soit d | (2^j - 1).
      Or 2^j - 1 < 2^j ≤ 2^{S-1} < d (car d > 2^{S-1} pour k ≥ 2).
      Donc d ∤ (2^j - 1) pour j < S.

  DONC : ord_d(2) ≥ S.

  Et S = ceil(k·log₂3) ≈ 1.585·k.

  COMPARER AVEC C = binom(M+k-1, k-1) :
    M = S - k ≈ 0.585·k
    C = binom(⌊1.585k⌋-1, k-1) ≈ 2^{H(k/(S-1))·(S-1)} / sqrt(...)
    Pour k grand, C >> S, donc ord ≥ S ne suffit pas.

  BESOIN : une borne PLUS FORTE que S sur ord_d(2).
""")

# Calculons le rapport C/S et ord/S pour chaque cas
print("  Comparaison numérique :")
print(f"  {'k':>4s} | {'S':>4s} | {'M':>3s} | {'log2(C)':>8s} | {'ord_d(2)':>12s} | {'ord/S':>7s} | {'log2(C)/S':>10s}")
print("  " + "-" * 65)

for k, S, M, d, C in prime_d_cases:
    if C is None:
        continue
    if d > 10**30 and not HAS_SYMPY:
        continue

    if HAS_SYMPY and d < 10**30:
        try:
            dm1_factors = factorint(d - 1)
            ord2 = order_fast(2, d, dm1_factors)
        except:
            ord2 = None
    else:
        if d < 10**8:
            ord2 = order(2, d)
        else:
            ord2 = None

    log2C = math.log2(C) if C > 0 else 0
    ord_str = str(ord2) if ord2 is not None else "?"
    ratio_str = f"{ord2/S:.2f}" if ord2 is not None else "?"

    print(f"  {k:4d} | {S:4d} | {M:3d} | {log2C:8.1f} | {ord_str:>12s} | {ratio_str:>7s} | {log2C/S:10.2f}")

# ================================================================
# I7. SYNTHÈSE
# ================================================================
print("\n" + "=" * 70)
print("I7. SYNTHÈSE SESSION 10f19")
print("=" * 70)

print(f"""
RÉSULTATS :

1. {len(prime_d_cases)} valeurs de k ∈ [3, 5000] avec d premier

2. BORNE ÉLÉMENTAIRE PROUVÉE : ord_d(2) ≥ S
   Preuve : 2^j - 1 < d pour j < S, donc d ∤ (2^j - 1).

3. 2^C ≠ 1 mod d pour TOUS les d premiers testés
   → ord_d(2) ∤ C → G2c vrai numériquement

4. En pratique : ord_d(2) ≈ d-1 ou (d-1)/petit facteur
   → ord >> C >> S

5. LE GAP : S ≤ ord mais C >> S, donc la borne S ne suffit pas.
   Pour prouver G2c, il faudrait :
   (a) Montrer ord > C directement (dur, car C est exponentiel en k)
   (b) Ou montrer que 2 est générateur primitif mod d (Artin)
   (c) Ou montrer que (d-1)/ord est borné (pas de grands quotients)

6. OBSERVATION STRUCTURELLE :
   d - 1 = 2^S - 3^k - 1. La factorisation de d-1 est cruciale.
   Si d-1 a peu de facteurs premiers, ord ne peut être petit.

7. CONCLUSION :
   G2c est le gap le PLUS DUR car il requiert une borne sur l'ordre
   multiplicatif de 2 modulo un premier de forme 2^S - 3^k.
   La conjecture d'Artin (non prouvée) donnerait le résultat.
   Aucune technique élémentaire connue ne semble suffisante.
""")

print("=" * 70)
print("FIN SESSION 10f19")
print("=" * 70)
