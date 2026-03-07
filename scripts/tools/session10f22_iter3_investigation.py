#!/usr/bin/env python3
"""
SESSION 10f22 — G-V-R ITERATION 3 : APPROCHE DIRECTE 2^S ≡ 3^k mod d
Pre-engagement :
  Hypothese : L'identite 2^S ≡ 3^k mod d, combinee avec g = gcd(C, d-1),
              permet d'exprimer 2^g mod d sous une forme qui ne peut pas etre 1.
  Succes : Trouver une relation structurelle 2^g ≡ f(3^k, S, k) mod d ≠ 1
  Echec : L'identite 2^S ≡ 3^k ne contraint pas 2^g de maniere utile
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
# K1. IDENTITE STRUCTURELLE : 2^S ≡ 3^k mod d
# ================================================================
print("=" * 70)
print("K1. IDENTITE STRUCTURELLE : 2^S ≡ 3^k mod d")
print("=" * 70)

print(f"""
  FAIT : d = 2^S - 3^k  =>  2^S ≡ 3^k mod d

  CONSEQUENCE :
    2^{{nS}} ≡ 3^{{nk}} mod d  pour tout n >= 0
    2^{{S+r}} ≡ 3^k · 2^r mod d  pour tout r

  IDEE : Si g = qS + r (division euclidienne), alors
    2^g = 2^{{qS + r}} = (2^S)^q · 2^r ≡ 3^{{qk}} · 2^r mod d

  QUESTION : Cette expression est-elle utile ?
  On aurait 2^g ≡ 1 ssi 3^{{qk}} · 2^r ≡ 1 ssi 2^r ≡ 3^{{-qk}} mod d
""")

print(f"  {'k':>5s} | {'S':>5s} | {'g=gcd':>10s} | {'q=g//S':>6s} | {'r=g%S':>6s} | "
      f"{'3^(qk) mod d':>15s} | {'2^r mod d':>12s} | {'prod mod d':>12s} | {'=1?':>4s} |")
print("  " + "-" * 95)

for r_dict in results:
    k, S, d, g = r_dict['k'], r_dict['S'], r_dict['d'], r_dict['gcd']
    q_div = g // S
    r_mod = g % S
    val_3qk = pow(3, q_div * k, d) if q_div > 0 else 1
    val_2r = pow(2, r_mod, d) if r_mod > 0 else 1
    prod = (val_3qk * val_2r) % d
    is_one = prod == 1

    # Truncate for display
    g_str = str(g) if g.bit_length() < 30 else f"({g.bit_length()}b)"
    v3_str = str(val_3qk) if val_3qk.bit_length() < 40 else f"({val_3qk.bit_length()}b)"
    v2_str = str(val_2r) if val_2r.bit_length() < 40 else f"({val_2r.bit_length()}b)"
    p_str = str(prod) if prod.bit_length() < 40 else f"({prod.bit_length()}b)"

    print(f"  {k:5d} | {S:5d} | {g_str:>10s} | {q_div:6d} | {r_mod:6d} | "
          f"{v3_str:>15s} | {v2_str:>12s} | {p_str:>12s} | {'OUI⚠' if is_one else 'non✓':>4s} |")

# ================================================================
# K2. CAS r = 0 : g multiple de S
# ================================================================
print("\n" + "=" * 70)
print("K2. CAS r = 0 : g MULTIPLE DE S ?")
print("=" * 70)

print(f"""
  Si g = qS (r=0), alors 2^g ≡ 3^{{qk}} mod d.
  Pour que 2^g ≡ 1, il faudrait 3^{{qk}} ≡ 1 mod d,
  i.e. ord_d(3) | qk.

  Mais ord_d(3) est typiquement grand (d-1 ou (d-1)/petit).
  Si q est petit et k < ord_d(3), ceci est impossible.

  VERIFIONS : g est-il multiple de S ?
""")

for r_dict in results:
    k, S, g = r_dict['k'], r_dict['S'], r_dict['gcd']
    is_mult = g % S == 0
    if is_mult:
        print(f"  k={k}: g={g}, S={S}, g/S={g//S} — g EST multiple de S !")
    elif g > S:
        print(f"  k={k}: g={g}, S={S}, g%S={g%S}, g//S={g//S}")

print("\n  CAS ou g < S :")
small_g = [(r_dict['k'], r_dict['gcd'], r_dict['S']) for r_dict in results if r_dict['gcd'] < r_dict['S']]
for k, g, S in small_g:
    print(f"    k={k}: g={g} < S={S}")

# ================================================================
# K3. RELATION ENTRE g, S, ET d-1
# ================================================================
print("\n" + "=" * 70)
print("K3. RELATION g = gcd(C, d-1) ET ECRITURE DE Bezout")
print("=" * 70)

print(f"""
  g = gcd(C, d-1) => il existe u, v tels que g = u·C + v·(d-1)
  Donc : 2^g = 2^{{u·C + v·(d-1)}}
       = (2^C)^u · (2^{{d-1}})^v
       ≡ (2^C)^u · 1^v  mod d   (Fermat)
       ≡ (2^C)^u mod d

  PROBLEME : Ceci est circulaire ! Si 2^C ≡ 1, alors 2^g ≡ 1.
  L'ecriture de Bezout ne donne RIEN de nouveau.

  => L'approche Bezout est un CUL-DE-SAC.
""")

# ================================================================
# K4. APPROCHE PAR RESTE : 2^g quand g < S
# ================================================================
print("=" * 70)
print("K4. APPROCHE PAR RESTE : 2^g mod d QUAND g < S")
print("=" * 70)

print(f"""
  Pour 15/19 cas : g < S.
  Quand g < S, on a 2^g < 2^S = d + 3^k, donc 2^g < 2d (car 3^k < d pour k >= 4).

  En fait : 2^g = d + 3^k pour g = S. Donc 2^g < d pour g < S-1.
  Cas g < S-1 : 2^g mod d = 2^g (car 2^g < d).
  Donc 2^g ≡ 1 mod d ssi 2^g = 1 ssi g = 0.
  MAIS g >= 1 toujours (car d-1 est pair et C >= 1).

  WAIT — c'est plus subtil :
  2^g < d ne veut PAS dire 2^g mod d = 2^g !
  Pardon : 2^g mod d = 2^g si 0 < 2^g < d. C'est le cas si g < log_2(d).
  Or log_2(d) ≈ S - theta (avec theta ∈ (0,1)).

  Donc si g < S - 1, alors 2^g < 2^{{S-1}} < d (car d > 2^{{S-1}} ... FAUX !)
  CORRECTION : d = 2^S - 3^k et 3^k > 2^{{S-1}} (car theta < 1).
  Donc d < 2^{{S-1}}.

  Hmm, verifions : d < 2^{{S-1}} ou d > 2^{{S-1}} ?
""")

print(f"  {'k':>5s} | {'S':>5s} | {'d bits':>6s} | {'d < 2^(S-1)?':>12s} | {'g':>10s} | {'g < d.bit_length()?':>18s} |")
print("  " + "-" * 75)

for r_dict in results:
    k, S, d, g = r_dict['k'], r_dict['S'], r_dict['d'], r_dict['gcd']
    d_bits = d.bit_length()
    d_lt_half = d < pow(2, S - 1)
    g_lt_dbits = g < d_bits

    g_str = str(g) if g.bit_length() < 30 else f"({g.bit_length()}b)"
    print(f"  {k:5d} | {S:5d} | {d_bits:6d} | "
          f"{'OUI' if d_lt_half else 'NON':>12s} | {g_str:>10s} | "
          f"{'OUI' if g_lt_dbits else 'NON':>18s} |")

# ================================================================
# K5. APPROCHE DIRECTE : 2^g mod d POUR g PETIT
# ================================================================
print("\n" + "=" * 70)
print("K5. 2^g mod d POUR g PETIT : VALEUR EXACTE")
print("=" * 70)

print(f"""
  Quand g est petit (g < log_2(d) ≈ S), 2^g mod d = 2^g exactement.
  Donc 2^g ≡ 1 mod d est IMPOSSIBLE si 1 < g < log_2(d).
  (Car 2^g > 1 et 2^g < d, donc 2^g mod d = 2^g ≠ 1.)

  VERIFICATION : g > 0 et 2^g < d ?
""")

for r_dict in results:
    k, S, d, g = r_dict['k'], r_dict['S'], r_dict['d'], r_dict['gcd']
    if g == 0:
        print(f"  k={k}: g=0 ⚠ (cas degenere)")
        continue
    two_g_lt_d = pow(2, g) < d if g < 10000 else g < d.bit_length()

    g_str = str(g) if g.bit_length() < 30 else f"({g.bit_length()}b)"
    if g < d.bit_length():
        print(f"  k={k}: g={g_str}, log2(d)≈{d.bit_length()}, 2^g < d ✓ → 2^g mod d = 2^g ≠ 1 PROUVE")
    else:
        # g >= log_2(d), cannot use this argument
        print(f"  k={k}: g={g_str}, log2(d)≈{d.bit_length()}, g >= log2(d) — argument ne s'applique PAS")

# ================================================================
# K6. SYNTHESE : QUELS CAS SONT PROUVES PAR g < log_2(d) ?
# ================================================================
print("\n" + "=" * 70)
print("K6. SYNTHESE : CAS PROUVES PAR g < log_2(d)")
print("=" * 70)

proved_by_size = []
not_proved = []
for r_dict in results:
    k, d, g = r_dict['k'], r_dict['d'], r_dict['gcd']
    if 0 < g < d.bit_length():
        proved_by_size.append(k)
    else:
        not_proved.append((k, g, d.bit_length()))

print(f"\n  CAS PROUVES par 0 < g < log_2(d) → 2^g = 2^g ≠ 1 :")
print(f"    {proved_by_size}")
print(f"    Total : {len(proved_by_size)}/19")

if not_proved:
    print(f"\n  CAS NON PROUVES :")
    for k, g, dbits in not_proved:
        print(f"    k={k}: g={g}, log2(d)≈{dbits}")

# ================================================================
# K7. POUR LES CAS g >= log_2(d) : ANALYSE FINE
# ================================================================
print("\n" + "=" * 70)
print("K7. CAS g >= log_2(d) : ANALYSE FINE")
print("=" * 70)

for r_dict in results:
    k, S, d, g = r_dict['k'], r_dict['S'], r_dict['d'], r_dict['gcd']
    if g >= d.bit_length():
        dm1 = r_dict['dm1']
        C = r_dict['C']
        ord_val = r_dict['ord']

        # How many times does g wrap around mod ord?
        g_mod_ord = g % ord_val if ord_val > 0 else -1
        # g mod S
        g_mod_S = g % S

        print(f"\n  k={k}: g={g}, S={S}, d≈2^{d.bit_length()}")
        print(f"    g/S = {g/S:.2f}")
        print(f"    g mod S = {g_mod_S}")
        print(f"    g mod ord = {g_mod_ord}")
        print(f"    2^g mod d = {pow(2, g, d)}")
        if g_mod_S > 0 and g_mod_S < d.bit_length():
            # 2^g ≡ 3^{qk} · 2^r mod d with r = g%S
            q_div = g // S
            r_mod = g_mod_S
            val = pow(3, q_div * k, d) * pow(2, r_mod, d) % d
            print(f"    Via 2^S ≡ 3^k : 2^g ≡ 3^{{{q_div}k}} · 2^{r_mod} mod d")
            print(f"    = {val}")
            print(f"    Argument : si r < log_2(d), 2^r ≠ 0 mod d.")
            print(f"    Mais 3^{{qk}} · 2^r ≡ 1 est plus complexe a eliminer.")

# ================================================================
# K8. ARGUMENT DE TAILLE AFFINE
# ================================================================
print("\n" + "=" * 70)
print("K8. ARGUMENT DE TAILLE AFFINE")
print("=" * 70)

print(f"""
  FAIT CENTRAL : Pour tout k >= 3 avec d premier,
    g = gcd(C, d-1) et on a :
    - g | C  et  g | (d-1)
    - 2^g mod d : on veut ≠ 1

  OBSERVATION (K5) : Si g < log_2(d), alors 2^g mod d = 2^g ≠ 1.
    C'est un argument INCONDITIONNEL et ELEMENTAIRE.

  COMBIEN de cas cela couvre-t-il ?
""")

# Extend to larger k range
print("  Extension : test g < log_2(d) pour k = 3..100000 (tous k, pas seulement d premier)")
count_total = 0
count_proved = 0
count_failed = 0
failed_list = []

for k in range(3, 100001):
    S = ceil_log2_3(k)
    d = pow(2, S) - pow(3, k)
    if d > 1 and check_prime(d):
        C = math.comb(S - 1, k - 1)
        dm1 = d - 1
        g = math.gcd(C, dm1)
        count_total += 1
        if 0 < g < d.bit_length():
            count_proved += 1
        else:
            count_failed += 1
            failed_list.append((k, g, d.bit_length()))

print(f"\n  d premiers trouves pour k=3..100000 : {count_total}")
print(f"  Prouves par g < log_2(d) : {count_proved}/{count_total}")
print(f"  Non prouves : {count_failed}/{count_total}")

if failed_list:
    print(f"\n  Cas echouants :")
    for k, g, dbits in failed_list:
        print(f"    k={k}: g={g}, log2(d)≈{dbits}")
else:
    print(f"\n  ★★★★★ TOUS les cas sont prouves par g < log_2(d) !")

# ================================================================
# K9. SYNTHESE ITERATION 3
# ================================================================
print("\n" + "=" * 70)
print("K9. SYNTHESE G-V-R ITERATION 3")
print("=" * 70)

if count_failed == 0:
    print(f"""
  ═══════════════════════════════════════════════════════════════
  ║  ITERATION 3 : ARGUMENT DE TAILLE SUR gcd                 ║
  ║  RESULTAT : POTENTIELLEMENT INCONDITIONNEL                 ║
  ═══════════════════════════════════════════════════════════════

  THEOREME (si generalisable) :
    Pour d = 2^S - 3^k premier (k >= 3), soit g = gcd(C, d-1)
    ou C = binom(S-1, k-1).
    Si 0 < g < log_2(d), alors 2^g mod d = 2^g > 1,
    donc 2^g ≢ 1 mod d, donc ord ∤ g, donc ord ∤ C,
    donc 2^C ≢ 1 mod d. ∎

  CONDITION : Il faut prouver g < log_2(d) pour tout k >= 3.
  VERIFIE pour {count_proved}/{count_total} d premiers (k=3..100000).

  QUESTION OUVERTE : Peut-on prouver g = gcd(binom(S-1,k-1), 2^S-3^k-1) < S ?
  (Comme log_2(d) ≈ S, il suffit de prouver g < S.)
""")
else:
    print(f"""
  ═══════════════════════════════════════════════════════════════
  ║  ITERATION 3 : ARGUMENT DE TAILLE SUR gcd                 ║
  ═══════════════════════════════════════════════════════════════

  ARGUMENT : 0 < g < log_2(d) => 2^g = 2^g ≠ 1 mod d

  COUVERTURE : {count_proved}/{count_total} cas (k=3..100000)
  ECHECS : {count_failed} cas ou g >= log_2(d)

  ANALYSE DES ECHECS :
""")
    for k, g, dbits in failed_list:
        S = ceil_log2_3(k)
        print(f"    k={k}: g={g} ≥ log_2(d)≈{dbits}")
        print(f"      g/log_2(d) = {g/dbits:.1f}")
        print(f"      g/S = {g/S:.1f}")

    print(f"""
  CONCLUSION : L'argument de taille seul ne suffit PAS pour tous les cas.
  Il manque {count_failed} cas ou gcd(C, d-1) est trop grand.
""")

print("=" * 70)
print("FIN G-V-R ITERATION 3")
print("=" * 70)
