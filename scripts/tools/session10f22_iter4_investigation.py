#!/usr/bin/env python3
"""
SESSION 10f22 — G-V-R ITERATION 4 : CONTROLE DE gcd(C, d-1) VIA d-1 mod p
Pre-engagement :
  Hypothese : Pour p premier divisant C = binom(S-1, k-1), la probabilite
              que p | (d-1) est 1/(p-1) (heuristique). Donc le produit des
              p | gcd(C, d-1) est borne par un nombre "petit" (< d).
  Succes : Prouver que gcd(C, d-1) < d^{1-eps} pour tout k >= k_0
  Echec : gcd peut etre arbitrairement grand relativement a d
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

# Collect all 19 prime d cases
prime_d_cases = []
for k in range(3, 10001):
    S = ceil_log2_3(k)
    d = pow(2, S) - pow(3, k)
    if d > 1 and check_prime(d):
        prime_d_cases.append((k, S, d))

# ================================================================
# L1. FACTEURS PREMIERS DE gcd(C, d-1) : D'OU VIENNENT-ILS ?
# ================================================================
print("=" * 70)
print("L1. FACTEURS PREMIERS DE gcd(C, d-1)")
print("=" * 70)

print(f"""
  Pour chaque k avec d premier, on calcule g = gcd(C, d-1) et on regarde
  les facteurs premiers de g. Un premier p | g ssi p | C ET p | (d-1).

  CONDITION p | (d-1) : d ≡ 1 mod p, i.e. 2^S - 3^k ≡ 1 mod p
                        i.e. 2^S ≡ 3^k + 1 mod p

  C'est une condition ARITHMETIQUE qui depend de S mod ord_p(2) et
  de k mod ord_p(3).
""")

# For the 4 rebels, analyze each prime factor
rebels = [61, 3895, 4500, 6891]

for k0, S0, d0 in prime_d_cases:
    if k0 not in rebels:
        continue
    C = math.comb(S0 - 1, k0 - 1)
    dm1 = d0 - 1
    g = math.gcd(C, dm1)

    # Factor g
    g_factors = {}
    temp = g
    for p in range(2, min(10000, g + 1)):
        while temp % p == 0:
            g_factors[p] = g_factors.get(p, 0) + 1
            temp //= p
    if temp > 1:
        g_factors[temp] = g_factors.get(temp, 0) + 1

    print(f"\n  k={k0}, S={S0}, g={g}, facteurs={g_factors}")

    for p, e in sorted(g_factors.items()):
        if p > 2:
            # Compute ord_p(2)
            ord_p2 = 1
            val = 2 % p
            while val != 1 and ord_p2 < p:
                val = val * 2 % p
                ord_p2 += 1

            # S mod ord_p(2)
            s_mod = S0 % ord_p2
            # 3^k + 1 mod p
            target = (pow(3, k0, p) + 1) % p
            # 2^S mod p
            actual = pow(2, S0, p)

            print(f"    p={p}: ord_p(2)={ord_p2}, S mod ord_p(2) = {s_mod}")
            print(f"      2^S mod p = {actual}, 3^k+1 mod p = {target}")
            print(f"      Match (p | d-1): {'OUI' if actual == target else 'NON'}")

# ================================================================
# L2. POUR QUELS PREMIERS p, p | C EST GARANTI ?
# ================================================================
print("\n" + "=" * 70)
print("L2. PREMIERS p | C = binom(S-1, k-1)")
print("=" * 70)

print(f"""
  Par Kummer : v_p(C) = nombre de retenues dans (k-1) + (S-k) base p.
  Tout premier p <= S-1 peut diviser C.
  Les premiers p avec p <= k-1 divisent GENERIQUEMENT C
  (car binom(n,m) est divisible par "beaucoup" de premiers <= n).

  QUESTION : Pour les rebelles, quels p | C ne divisent PAS d-1 ?
  Si la plupart des p | C ne divisent pas d-1, alors g est petit.
""")

# For k=61 (smallest rebel), exhaustive check
k0, S0 = 61, 97
d0 = pow(2, S0) - pow(3, k0)
C = math.comb(S0 - 1, k0 - 1)
dm1 = d0 - 1
g = math.gcd(C, dm1)

# All primes up to S-1 = 96
from sympy import primerange
primes_small = list(primerange(2, S0))

count_div_C = 0
count_div_both = 0
div_both = []
div_C_only = []

for p in primes_small:
    div_C = (C % p == 0)
    div_dm1 = (dm1 % p == 0)
    if div_C:
        count_div_C += 1
        if div_dm1:
            count_div_both += 1
            div_both.append(p)
        else:
            div_C_only.append(p)

print(f"  k={k0}: premiers p <= {S0-1}:")
print(f"    p | C : {count_div_C}")
print(f"    p | C et p | (d-1) : {count_div_both} → {div_both}")
print(f"    p | C mais p ∤ (d-1) : {len(div_C_only)} → {div_C_only[:20]}...")
print(f"    Ratio : {count_div_both}/{count_div_C} = {count_div_both/count_div_C:.4f}")

# Do the same for other rebels
for k0 in [3895, 4500, 6891]:
    S0 = ceil_log2_3(k0)
    d0 = pow(2, S0) - pow(3, k0)
    C = math.comb(S0 - 1, k0 - 1)
    dm1 = d0 - 1
    g = math.gcd(C, dm1)

    # Check primes up to 1000 (not all primes up to S)
    count_div_C = 0
    count_div_both = 0
    div_both_list = []

    for p in primerange(2, 1001):
        div_C = (C % p == 0)
        div_dm1 = (dm1 % p == 0)
        if div_C:
            count_div_C += 1
            if div_dm1:
                count_div_both += 1
                div_both_list.append(p)

    print(f"\n  k={k0}: premiers p <= 1000:")
    print(f"    p | C : {count_div_C}")
    print(f"    p | C et p | (d-1) : {count_div_both} → {div_both_list}")
    print(f"    Ratio : {count_div_both}/{count_div_C} = {count_div_both/count_div_C:.4f}")

# ================================================================
# L3. HEURISTIQUE : TAILLE ATTENDUE DE gcd(C, d-1)
# ================================================================
print("\n" + "=" * 70)
print("L3. HEURISTIQUE : TAILLE ATTENDUE DE gcd(C, d-1)")
print("=" * 70)

print(f"""
  MODELE HEURISTIQUE :
    Pour un premier p, Prob(p | d-1) ≈ 1/(p-1) (pour d "aleatoire")
    Et Prob(p | C) est generiquement elevee pour p <= S-1.

    E[log gcd] ≈ sum_{{p | C}} log(p) · 1/(p-1)
               ≈ sum_{{p <= S}} log(p)/(p-1)
               ≈ log(S) (par Mertens)

    Donc heuristiquement : gcd(C, d-1) ≈ S^c pour une constante c.
    C'est BEAUCOUP plus petit que d ≈ 2^S.

  VERIFICATION :
""")

for k0, S0, d0 in prime_d_cases:
    C = math.comb(S0 - 1, k0 - 1)
    dm1 = d0 - 1
    g = math.gcd(C, dm1)

    log_g = math.log(g) if g > 0 else 0
    log_S = math.log(S0)
    ratio = log_g / log_S if log_S > 0 else 0

    print(f"  k={k0:5d}: g={g:>12d}, log(g)/log(S) = {ratio:.2f}, "
          f"g ≈ S^{ratio:.1f}")

# ================================================================
# L4. REFORMULATION : g < d SUFFIT-IL ?
# ================================================================
print("\n" + "=" * 70)
print("L4. REFORMULATION : CONDITION g < d POUR PROUVER G2c")
print("=" * 70)

print(f"""
  RAPPEL : On veut 2^g ≢ 1 mod d.

  ARGUMENT DE TAILLE (iter 3) : si g < log_2(d), c'est trivial.

  ARGUMENT D'ORDRE : si g < ord = (d-1)/Q, alors ord ∤ g.

  NOUVELLE OBSERVATION : si g < d-1, alors 2^g ≡ 1 mod d ssi ord | g.
  Les diviseurs de d-1 qui sont < d-1 et multiples de ord sont :
    ord, 2·ord, 3·ord, ..., (Q-1)·ord

  Il y a exactement Q-1 tels multiples (excluant d-1 lui-meme).
  Pour que g soit l'un d'eux, il faudrait que g soit un multiple de ord.

  Comme g = gcd(C, d-1), g | (d-1). Donc g est un diviseur de d-1.
  Parmi les diviseurs de d-1, combien sont multiples de ord ?
  Ce sont les diviseurs de d-1 dans {{ord, 2·ord, ..., (Q-1)·ord, d-1}}.
  Leur nombre est le nombre de diviseurs de Q.

  La DENSITE de ces "mauvais" diviseurs parmi tous les diviseurs de d-1
  est d(Q)/d(d-1), typiquement TRES petite.

  VERIFICATION : g est-il multiple de ord pour un des 19 cas ?
""")

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

any_bad = False
for k0, S0, d0 in prime_d_cases:
    C = math.comb(S0 - 1, k0 - 1)
    dm1 = d0 - 1
    g = math.gcd(C, dm1)
    Q = Q_pred(d0)
    ord_val = dm1 // Q

    is_mult_ord = (g % ord_val == 0)
    if is_mult_ord:
        any_bad = True
        print(f"  k={k0}: g={g} EST multiple de ord={ord_val} ⚠⚠⚠")
    # Only print for rebels and a few others
    elif k0 in rebels or k0 in [3, 5, 13]:
        print(f"  k={k0}: g%ord = {g % ord_val if ord_val < 10**9 else '≠0'} ≠ 0 ✓")

if not any_bad:
    print(f"\n  ★★★ g n'est multiple de ord pour AUCUN des 19 cas.")

# ================================================================
# L5. CLE : ARGUMENT STRUCTUREL SUR g ET ord
# ================================================================
print("\n" + "=" * 70)
print("L5. ARGUMENT STRUCTUREL : g | (d-1) ET ord | (d-1)")
print("=" * 70)

print(f"""
  FAIT : g = gcd(C, d-1) divise d-1.
  FAIT : ord divise d-1.

  Pour que ord | g, il faut que ord | gcd(C, d-1), ce qui est equivalent
  a ord | C (car ord | d-1 toujours).

  C'est EXACTEMENT la condition qu'on veut NIER : ord ∤ C.

  DONC : l'approche gcd ne donne rien de plus que la question originale.
  "g n'est pas multiple de ord" EST la meme question que "ord ∤ C".

  L'argument de TAILLE (g < log_2(d)) est la seule NOUVEAUTE de cette approche.
  Pour les cas ou g < log_2(d), c'est un argument INCONDITIONNEL.
  Pour les cas ou g >= log_2(d), on retombe dans la question originale.

  BILAN FINAL DE L'APPROCHE gcd :
    - 15/19 cas : PROUVE inconditionnellement (g < log_2(d))
    - 4/19 cas : EQUIVALENT a la question originale (ord ∤ C)
""")

# ================================================================
# L6. PEUT-ON PROUVER g < log_2(d) EN GENERAL ?
# ================================================================
print("=" * 70)
print("L6. CONDITION g < log_2(d) : PROUVABLE ?")
print("=" * 70)

print(f"""
  g = gcd(binom(S-1, k-1), 2^S - 3^k - 1) < S ?

  BORNE SUPERIEURE SUR g :
    g | (d-1), donc g <= d-1 < 2^S  → trivial, inutile
    g | C, donc g <= C ≈ 2^(0.949·S) → mieux mais toujours >> S

  BORNE PAR FACTORISATION :
    g = prod_p p^{{min(v_p(C), v_p(d-1))}}
    Pour p > S : v_p(C) = 0 (car C = binom(S-1, k-1) et p > S-1)
    Donc seuls les premiers p <= S-1 contribuent.

  NOMBRE DE PREMIERS <= S : π(S) ≈ S/ln(S)

  Si chaque p contribue p^1 au gcd, le produit maximal est :
    prod_{{p <= S}} p = primorial(S) ≈ e^S (theoreme des nombres premiers)

  C'est BEAUCOUP plus grand que S ! Donc g < S n'est PAS garanti
  par la structure seule. Il faut que la PLUPART des p <= S ne
  divisent pas d-1.

  HEURISTIQUE : Prob(p | d-1) ≈ 1/(p-1)
    E[nombre de p <= S divisant d-1] ≈ sum_{{p<=S}} 1/(p-1) ≈ ln(ln(S))
    E[g] ≈ produit de ln(ln(S)) premiers aleatoires ≈ S^c pour c petit

  MAIS ce n'est qu'une heuristique. Prouver g < S inconditionnellement
  semble requierir un controle sur la divisibilite de d-1 par les petits
  premiers, ce qui est un probleme de theorie analytique des nombres
  (type Vinogradov / crible).

  CONCLUSION : g < S est "presque toujours vrai" heuristiquement
  mais pas prouvable avec les outils actuels pour TOUS les k.
""")

# ================================================================
# L7. SYNTHESE ITERATION 4
# ================================================================
print("=" * 70)
print("L7. SYNTHESE G-V-R ITERATION 4")
print("=" * 70)

print(f"""
  ═══════════════════════════════════════════════════════════════
  ║  SYNTHESE SESSION 10f22 — ATTAQUE ARTIN POUR G2c          ║
  ═══════════════════════════════════════════════════════════════

  RESULTAT PRINCIPAL (NOUVEAU) :
    Pour 15/19 d premiers (k=3..10000), G2c est prouve par un
    argument ELEMENTAIRE et INCONDITIONNEL :
      g = gcd(C, d-1) < log_2(d) => 2^g = 2^g ≠ 1 mod d
      => ord ∤ gcd(C,d-1) => ord ∤ C => 2^C ≢ 1 mod d  ∎

  CAS RESTANTS (4/19) :
    k=61, 3895, 4500, 6891 ont gcd(C, d-1) >= log_2(d).
    Pour ceux-ci, G2c est verifie numeriquement mais pas prouve.
    Prouver G2c pour ces cas est EQUIVALENT a prouver ord ∤ C,
    qui retombe dans la barriere d'Artin.

  RESUME DES 4 ITERATIONS :
    Iter 1 (v_2) : v_2(C) <= 1 FAUX. Prouve pour 5 cas specifiques.
    Iter 2 (gcd) : 2^{{gcd}} ≢ 1 pour 19/19. Theorique ≡ Artin.
    Iter 3 (taille) : g < log_2(d) prouve 15/19 inconditionnellement. ★★★
    Iter 4 (d-1 mod p) : Heuristique g ≈ S^c mais non prouvable.

  STATUT G2c :
    [PROUVE_ELEMENTAIRE] 15/19 cas (argument de taille sur gcd)
    [VERIFIE_k=3..10000] 19/19 cas (computationnel)
    [OPEN_THEORIQUE] 4 cas ou gcd >= log_2(d)
    [CONDITIONNEL_GRH] Tous les cas (via Hooley 1967)

  RECOMMANDATION :
    - Documenter l'argument de taille comme RESULTAT PARTIEL INCONDITIONNEL
    - Les 4 cas restants : conditionnel a GRH ou verification cas par cas
    - NE PAS faire d'iteration 5 : la barriere est fondamentale pour les 4 cas
    - Piste minimale : prouver g < S pour les familles denses de k (k impair etc.)
""")

print("=" * 70)
print("FIN G-V-R ITERATION 4")
print("=" * 70)
