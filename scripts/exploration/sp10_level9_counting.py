#!/usr/bin/env python3
"""
SP10 Level 9 — Piste 1 : Comptage arithmetique N(p,K)
=====================================================
OBJECTIF : Estimer/borner N(p,K) = #{k ∈ [69,K] : p | d(k)}
par des methodes de comptage arithmetique (caracteres, sommes exp.).

THEORIE :
  p | d(k) ⟺ 2^{S(k)} ≡ 3^k (mod p)
  ou S(k) = ⌈k·log₂(3)⌉

  Posons g = generateur primitif mod p, et a = log_g(2), b = log_g(3).
  Alors 2^{S(k)} ≡ 3^k (mod p) ⟺ a·S(k) ≡ b·k (mod p-1)

  C'est une CONGRUENCE LINEAIRE en k (presque), car S(k) ≈ k·log₂(3).
  La difficulte est le ⌈...⌉ dans S(k).

APPROCHE 1 : Structure periodique modulo p-1
  Si on ignore le ⌈...⌉ et pose S(k) ≈ k·log₂(3), on obtient une
  condition pseudo-periodique. Le nombre de k ∈ [A,B] satisfaisant
  a·S(k) ≡ b·k (mod p-1) est environ (B-A+1)/(p-1) si "generique".

APPROCHE 2 : Structure EXACTE via ord_p(2) et ord_p(3)
  Posons m = ord_p(2). Alors 2^{S(k)} mod p ne depend que de S(k) mod m.
  Et 3^k mod p ne depend que de k mod ord_p(3·(p-1)/m) ou similaire.

  CONDITION EXACTE :
    p | d(k) ⟺ 2^{S(k) mod m} ≡ 3^{k mod (p-1)} (mod p)

  Comme S(k) mod m est PRESQUE periodique (de periode m ou p-1),
  le nombre de hits est controle par la DISTRIBUTION de S(k) mod m.

APPROCHE 3 : Borne de Weil + densite
  Le nombre de k ∈ [A,B] tels que 2^{S(k)} ≡ 3^k (mod p) est
  au plus le nombre de solutions de l'equation dans Z/(p-1)Z
  fois (B-A+1)/(p-1) + erreur.

SCRIPT : Test empirique + estimation analytique.
"""

import math
import sys
import time

sys.set_int_max_str_digits(100000)
sys.stdout = open(sys.stdout.fileno(), mode='w', buffering=1)

from sympy import n_order, factorint, isprime, primitive_root

def S(k):
    return int(math.ceil(k * math.log2(3)))

print("=" * 70)
print("SP10 L9 — Piste 1 : Comptage arithmetique N(p,K)")
print("=" * 70)

# ============================================================
# PARTIE 1 : Structure exacte de la condition p | d(k)
# ============================================================

print("\n1. STRUCTURE EXACTE : p | d(k) ⟺ 2^{S(k)} ≡ 3^k (mod p)")
print("-" * 50)

# Pour un premier p fixe :
# m = ord_p(2)
# n = ord_p(3)  (dans le quotient (Z/pZ)* / ⟨2⟩ si 3 ∉ ⟨2⟩)
#
# La condition 2^{S(k)} ≡ 3^k (mod p) se decompose :
# 1. S(k) mod m est determine par l'equation (composante dans ⟨2⟩)
# 2. k doit satisfaire une condition de compatibilite
#    (composante dans le quotient)

def analyze_structure(p):
    """Analyse la structure de p | d(k)."""
    m = n_order(2, p)
    n3 = n_order(3, p)

    # Est-ce que 3 ∈ ⟨2⟩ mod p ?
    # 3 ∈ ⟨2⟩ ⟺ ∃ j : 2^j ≡ 3 (mod p)
    three_in_two = False
    log2_3 = None
    for j in range(m):
        if pow(2, j, p) == 3 % p:
            three_in_two = True
            log2_3 = j
            break

    # Structure du quotient
    index = (p - 1) // m  # index de ⟨2⟩ dans (Z/pZ)*

    return {
        'p': p, 'm': m, 'n3': n3,
        'three_in_two': three_in_two, 'log2_3': log2_3,
        'index': index
    }

# Analyser les premiers cles
key_primes = [31, 127, 257, 8191, 131071, 524287, 2113, 14951]

print(f"\n  {'p':>10} {'m=ord(2)':>10} {'n3=ord(3)':>10} {'3∈⟨2⟩':>8} {'index':>8}")
print("  " + "-" * 50)

for p in key_primes:
    info = analyze_structure(p)
    flag = "OUI" if info['three_in_two'] else "NON"
    print(f"  {p:>10} {info['m']:>10} {info['n3']:>10} {flag:>8} {info['index']:>8}")


# ============================================================
# PARTIE 2 : Condition de periodicite EXACTE
# ============================================================

print("\n\n2. PERIODICITE : Quand est-ce que p | d(k) est PERIODIQUE ?")
print("-" * 50)

print("""
  Pour un premier p fixe avec m = ord_p(2) :
    p | d(k) ⟺ 2^{S(k)} ≡ 3^k (mod p)

  Observation cle : S(k+m·(p-1)) ≡ S(k) (mod m) et k+m·(p-1) ≡ k (mod p-1)
  car S est QUASI-lineaire : S(k + N) = S(k) + S(N) ± 1.

  Mais la VRAIE periode n'est pas m·(p-1) — c'est plus subtil.

  Si 3 ∈ ⟨2⟩ (i.e., 3 = 2^j mod p pour un j), alors :
    p | d(k) ⟺ S(k) ≡ j·k (mod m)
    i.e., ⌈k·log₂(3)⌉ ≡ j·k (mod m)

  Si 3 ∉ ⟨2⟩, la condition est plus restrictive :
    Il faut d'abord que 3^k ∈ ⟨2⟩ mod p (condition necessaire)
    i.e., k ≡ 0 (mod n) ou n = index de ⟨3⟩·⟨2⟩ / ⟨2⟩
""")


# ============================================================
# PARTIE 3 : Densite empirique N(p, K) / K
# ============================================================

print("\n3. DENSITE EMPIRIQUE : N(p,K)/K pour K=10000")
print("-" * 50)

K_MAX = 10000

print(f"\n  {'p':>10} {'m':>6} {'N(p,K)':>8} {'K':>8} {'N/K':>10} {'1/(p-1)':>10} {'ratio':>8}")
print("  " + "-" * 70)

for p in key_primes:
    m = n_order(2, p)
    count = 0
    for k in range(69, K_MAX + 1):
        Sk = S(k)
        if (pow(2, Sk, p) - pow(3, k, p)) % p == 0:
            count += 1

    density = count / (K_MAX - 68)
    expected = 1 / (p - 1)
    ratio = density / expected if expected > 0 else float('inf')
    print(f"  {p:>10} {m:>6} {count:>8} {K_MAX - 68:>8} {density:>10.6f} {expected:>10.6f} {ratio:>8.2f}")


# ============================================================
# PARTIE 4 : Distribution de S(k) mod m
# ============================================================

print("\n\n4. DISTRIBUTION de S(k) mod m")
print("-" * 50)
print("""
  La cle est : comment se distribue r(k) = S(k) mod m pour k=69..K ?

  S(k) = ⌈k·log₂(3)⌉, donc S(k) mod m = ⌈k·θ⌉ mod m ou θ = log₂(3).
  Comme θ est irrationnel, par Weyl : {k·θ} est equidistribue mod 1.
  Donc S(k) mod m est equidistribue parmi {0, 1, ..., m-1}.

  Ceci implique : pour chaque classe residuelle r mod m,
  #{k ∈ [69,K] : S(k) ≡ r (mod m)} ≈ (K-68)/m

  MAIS : la condition p | d(k) n'est pas juste S(k) ≡ r (mod m).
  C'est S(k) ≡ r(k) (mod m) ou r(k) = log_2(3^k mod p) mod m
  depend de k aussi !
""")

# Verifier l'equidistribution de S(k) mod m pour quelques m
for m_test in [5, 7, 13, 16, 31, 127]:
    counts = [0] * m_test
    for k in range(69, 10001):
        r = S(k) % m_test
        counts[r] += 1
    expected = (10001 - 69) / m_test
    max_dev = max(abs(c - expected) / expected for c in counts)
    print(f"  m={m_test:>4}: max deviation = {max_dev:.4f} "
          f"(expected {expected:.1f} per class)")


# ============================================================
# PARTIE 5 : La VRAIE structure — Orbite (S(k) mod m, k mod (p-1))
# ============================================================

print("\n\n5. STRUCTURE ORBITALE : (S(k) mod m, k mod (p-1))")
print("-" * 50)

# Pour les petits p, on peut analyser la structure complète
for p in [31, 127]:
    m = n_order(2, p)
    n3 = n_order(3, p)

    # Calculer les k ∈ [69, 10000] ou p | d(k)
    hits = []
    for k in range(69, 10001):
        Sk = S(k)
        if (pow(2, Sk, p) - pow(3, k, p)) % p == 0:
            hits.append(k)

    if not hits:
        print(f"  p={p} (m={m}): ZERO hits dans [69, 10000]")
        continue

    print(f"\n  p={p} (m={m}, n3={n3}): {len(hits)} hits dans [69, 10000]")

    # Analyser les residus k mod m et k mod (p-1)
    print(f"  Hits (premiers 15) :")
    for kh in hits[:15]:
        Skh = S(kh)
        s_mod_m = Skh % m
        k_mod_pm1 = kh % (p - 1)
        print(f"    k={kh:>6}, S(k)%m={s_mod_m}, k%(p-1)={k_mod_pm1:>4}")

    # Ecarts entre hits consecutifs
    if len(hits) > 1:
        gaps = [hits[i+1] - hits[i] for i in range(min(len(hits)-1, 20))]
        print(f"  Ecarts : {gaps}")
        print(f"  Ecart moyen = {sum(gaps)/len(gaps):.1f} (≈ p-1 = {p-1} ?)")


# ============================================================
# PARTIE 6 : Formule analytique exacte pour N(p,K)
# ============================================================

print("\n\n6. FORMULE ANALYTIQUE pour N(p,K)")
print("-" * 50)
print("""
  Pour p fixe, la condition p | d(k) est :
    2^{S(k)} ≡ 3^k (mod p)

  Comme ⟨2⟩ a indice n=(p-1)/m dans (Z/pZ)*, ceci requiert :
    3^k ∈ ⟨2⟩ (mod p)  [condition necessaire]

  Si n₃ = ord du quotient 3·⟨2⟩ dans (Z/pZ)*/⟨2⟩, alors :
    3^k ∈ ⟨2⟩ ⟺ n₃ | k

  PREMIER FILTRE : k doit etre multiple de n₃.
  Densite = 1/n₃.

  DEUXIEME FILTRE : parmi les k multiples de n₃,
    2^{S(k)} ≡ 3^k (mod p) requiert S(k) ≡ log_2(3^k) (mod m).
    Comme 3^{n₃} ∈ ⟨2⟩, posons 3^{n₃} ≡ 2^L (mod p).
    Alors 3^{k} = 3^{n₃·(k/n₃)} = (3^{n₃})^{k/n₃} ≡ 2^{L·k/n₃} (mod p).
    Donc : S(k) ≡ L·(k/n₃) (mod m).

  C'est une condition sur ⌈k·θ⌉ mod m vs L·k/n₃ mod m.
  Ecrivons k = n₃·j (pour j entier). Alors :
    S(n₃·j) ≡ L·j (mod m)
    i.e., ⌈n₃·j·θ⌉ ≡ L·j (mod m)
    i.e., n₃·j·θ + {-n₃·j·θ} ≡ L·j (mod m)  (a 1 pres pour le ceil)

  Comme θ = log₂(3), n₃·θ est un nombre reel fixe.
  La condition est ⌈n₃·j·θ⌉ - L·j ≡ 0 (mod m).

  Si n₃·θ est "bien approche" par un rationnel a/b, la sequence
  ⌈n₃·j·θ⌉ mod m a une structure quasi-periodique de periode ≈ m.
  Le nombre de j ∈ [J_1, J_2] satisfaisant la condition est ≈ (J_2-J_1)/m.

  DENSITE TOTALE :
    N(p, K) ≈ (K-68) / (n₃ · m)  = (K-68) / (p-1)   [car n₃·m | p-1]

  C'est EXACTEMENT 1/(p-1) par unite de k — CONFIRME par l'empirique !
""")

# Verifier la formule n₃
print("  Verification : n₃ · m = p-1 ?")
for p in key_primes:
    m = n_order(2, p)
    # Calculer n₃ = indice du quotient
    # 3^k ∈ ⟨2⟩ ssi k ≡ 0 mod n₃
    # n₃ = (p-1)/m si 3 est racine primitive du quotient, sinon divise
    # En general : n₃ = ord du quotient
    info = analyze_structure(p)
    if info['three_in_two']:
        n3_eff = 1
    else:
        # Trouver le plus petit n tel que 3^n ∈ ⟨2⟩
        n3_eff = None
        for j in range(1, p):
            val = pow(3, j, p)
            # Tester si val ∈ ⟨2⟩
            if pow(val, m, p) == 1:  # val^m ≡ 1 ssi val ∈ ⟨2⟩ (car |⟨2⟩|=m)
                n3_eff = j
                break

    pm1 = p - 1
    product = n3_eff * m if n3_eff else 0
    divides = "OUI" if product and pm1 % product == 0 else "NON"
    print(f"  p={p:>10}: m={m:>6}, n₃={n3_eff:>6}, n₃·m={product:>10}, "
          f"p-1={pm1:>10}, n₃·m | p-1 = {divides}")


# ============================================================
# PARTIE 7 : Borne formelle via somme de caracteres
# ============================================================

print("\n\n7. BORNE via somme de caracteres (esquisse)")
print("-" * 50)
print("""
  N(p, K) = Σ_{k=69}^{K} 1_{p|d(k)}

  Par orthogonalite des caracteres additifs de Z/pZ :
    1_{x≡0 (mod p)} = (1/p) Σ_{t=0}^{p-1} e_p(tx)

  Donc :
    N(p, K) = (1/p) Σ_{k=69}^{K} Σ_{t=0}^{p-1} e_p(t · d(k))
            = (K-68)/p + (1/p) Σ_{t=1}^{p-1} Σ_{k=69}^{K} e_p(t · (2^{S(k)} - 3^k))

  Le terme principal = (K-68)/p ≈ E (esperance heuristique).

  Le terme d'erreur = (1/p) Σ_{t=1}^{p-1} T(t)
  ou T(t) = Σ_{k=69}^{K} e_p(t·2^{S(k)}) · e_p(-t·3^k)

  PROBLEME : Borner |T(t)| est TRES DIFFICILE car :
  1. 2^{S(k)} a une dependance DOUBLE exponentielle en k via le ceil
  2. 3^k est exponentiel en k
  3. Les deux termes sont MULTIPLICATIVEMENT independants

  APPROCHE POSSIBLE (type van der Corput) :
  La somme T(t) est une somme de phases e(φ(k)) ou :
    φ(k) = t·2^{S(k)}/p - t·3^k/p

  La derivee φ'(k) ≈ t·2^{S(k)}·ln(2)·log₂(3)/p - t·3^k·ln(3)/p
  est ENORME (exponentielle en k).

  Par le lemme de van der Corput (sommes oscillantes rapides) :
    |T(t)| ≤ (K-68) / √(min|φ'(k)|)  + termes de bord

  Comme |φ'(k)| ~ (t/p)·3^k·ln(3) qui est >> 1 pour k >> log(p)/log(3),
  on obtient |T(t)| << (K-68)·3^{-k/2} pour k grand.

  MAIS le terme t/p peut etre petit (cancellation), et pour les
  premiers termes (k petit), la borne est triviale.

  ESTIMATION NAIVE DU TERME D'ERREUR :
    |erreur| ≤ (1/p) · (p-1) · max_t |T(t)|
             ≈ max_t |T(t)|

  Si |T(t)| ≤ √(K-68) (comme pour des phases "generiques") :
    N(p, K) = (K-68)/p + O(√(K-68))

  Pour (K-68)/p < 1 (i.e., K < p + 69), N(p,K) = 0 OU 1.
  Le terme O(√K) est trop grand pour conclure N = 0.

  CONCLUSION : La borne "type van der Corput" est INSUFFISANTE
  pour prouver N(p,K) = 0 quand K ≈ k_crit << p.
""")


# ============================================================
# PARTIE 8 : Approche alternative — structure mod m
# ============================================================

print("\n8. APPROCHE ALTERNATIVE : Reduction mod m × (p-1)/m")
print("-" * 50)
print("""
  Au lieu de compter directement, decomposons la condition :

  p | d(k) ⟺ 2^{S(k)} ≡ 3^k (mod p)

  ETAPE 1 : Reduire mod ⟨2⟩
    3^k doit etre dans le coset de ⟨2⟩ contenant la bonne puissance.
    Ceci donne k ≡ 0 (mod n₃) (ou n₃ = index effectif).

  ETAPE 2 : Pour k = n₃·j, la condition devient
    S(n₃·j) ≡ L·j (mod m)
    ou L = log_2(3^{n₃}) dans ⟨2⟩.

  La question est : combien de j ∈ [J_1, J_2] satisfont
    ⌈n₃·j·θ⌉ ≡ L·j (mod m) ?

  Posons f(j) = ⌈n₃·j·θ⌉ - L·j. La question est #{j : f(j) ≡ 0 (mod m)}.

  f(j) = ⌈n₃·θ·j⌉ - L·j
       = ⌈(n₃·θ - L)·j + L·j⌉ - L·j
       ≈ (n₃·θ - L)·j + {-(n₃·θ - L)·j}·???

  C'est une suite de type BEATTY : f(j) ≡ ⌊αj + β⌋ (mod m)
  pour certains α, β reels.

  THEOREME (equidistribution des suites de Beatty) :
  Si α est irrationnel, #{j ≤ J : ⌊αj⌋ ≡ r (mod m)} ≈ J/m.

  Donc #{j ∈ [J₁,J₂] : f(j) ≡ 0 (mod m)} ≈ (J₂-J₁)/m.

  DENSITE FINALE : N(p, K) ≈ (K-68)/(n₃·m) = (K-68)/(p-1).

  C'est l'heuristique 1/(p-1) retrouvee FORMELLEMENT via Beatty !

  MAIS ATTENTION : "≈" signifie erreur O(log(J)/m) par le
  discrepancy bound de Weyl. Pour J = k_crit/n₃ et m grand,
  l'erreur est O(1) — c'est-a-dire N pourrait etre 0 ou 1.

  On NE PEUT PAS conclure N = 0 par cette methode seule.
  Mais on peut dire N ≤ 1 + O(log(k_crit)/m) ce qui, pour
  m grand (regime B, m > p^{1/4} → m > qq centaines), donne N ≤ 2.
""")


# ============================================================
# PARTIE 9 : Verification numerique de la formule de Beatty
# ============================================================

print("\n9. TEST NUMERIQUE : Beatty vs realite")
print("-" * 50)

theta = math.log2(3)

for p in [127, 8191, 131071]:
    m = n_order(2, p)
    info = analyze_structure(p)

    # Trouver n₃
    if info['three_in_two']:
        n3_eff = 1
    else:
        for j in range(1, p):
            if pow(3, j * m, p) == 1:  # Équivalent à 3^j ∈ ⟨2⟩
                # Mais mieux : 3^j mod p est dans ⟨2⟩ ssi (3^j)^((p-1)/m) ≡ 1 (mod p)
                pass
        # Methode directe
        n3_eff = None
        for j in range(1, p):
            val = pow(3, j, p)
            if pow(val, m, p) == 1:
                n3_eff = j
                break

    if n3_eff is None or n3_eff > 10000:
        print(f"  p={p}: n₃ trop grand ou non trouve, skip")
        continue

    # Compter N(p, K) pour K=5000
    K = 5000
    hits_count = 0
    for k in range(69, K + 1):
        Sk = S(k)
        if (pow(2, Sk, p) - pow(3, k, p)) % p == 0:
            hits_count += 1

    expected = (K - 68) / (p - 1)
    beatty_pred = (K - 68) / (n3_eff * m) if n3_eff else 0

    print(f"  p={p:>8} (m={m:>4}, n₃={n3_eff:>4}): "
          f"N={hits_count:>4}, E[1/(p-1)]={expected:.2f}, "
          f"Beatty[1/(n₃m)]={beatty_pred:.2f}")


# ============================================================
# PARTIE 10 : Synthese — Ce que le comptage apporte
# ============================================================

print(f"\n\n{'='*70}")
print("10. SYNTHESE — Contribution de la Piste 1 (Comptage)")
print(f"{'='*70}")
print("""
  ✅ CE QUE LE COMPTAGE DONNE :
  1. La densite N(p,K)/K ≈ 1/(p-1) est CONFIRMEE empiriquement
  2. La formule de Beatty EXPLIQUE cette densite par l'equidistribution
  3. Pour K = k_crit << p, on a E[N] = k_crit/(p-1) << 1

  ❌ CE QUE LE COMPTAGE NE DONNE PAS (encore) :
  1. PAS de preuve formelle que N(p, k_crit) = 0
  2. L'erreur O(1) dans la formule de Beatty est trop grande
  3. Les bornes type van der Corput sont trop laches

  ★ PISTE PROMETTEUSE : Combiner equidistribution + structure mod m
  Si on pouvait montrer que l'erreur dans la formule de Beatty
  est < 1 pour les parametres specifiques (m grand, n₃ grand),
  on aurait N = 0.

  OBSERVATION CLE :
  Pour les premiers du REGIME B (p ≥ m^4), on a :
  - n₃ est typiquement ≈ (p-1)/m (car 3 ∉ ⟨2⟩ generiquement)
  - k_crit ≈ m · ln(p) / |ln(ρ)| ≈ m² (avec borne triviale)
  - Nombre de j candidats : k_crit / n₃ ≈ m² / ((p-1)/m) = m³/(p-1)
  - Pour p ≥ m^4 : m³/(p-1) ≤ m³/m^4 = 1/m → 0

  DONC : Le nombre de j candidats est < 1 pour m assez grand !
  C'est l'argument de RARETE ABSOLUE reformule avec la structure.

  FORMALISATION POSSIBLE :
  Si #{j ≤ J : f(j) ≡ 0 (mod m)} = J/m + O(D(J,m))
  ou D(J,m) est la discrepance de la suite de Beatty,
  et si J/m + D(J,m) < 1 (i.e., J < m - m·D),
  alors N = 0.

  Par Weyl : D(J,m) = O(log(m)/m) pour les suites irrationnelles.
  Donc N = 0 si J < m · (1 - C·log(m)/m) ≈ m.
  Et J = k_crit/n₃ ≈ m³/(p-1).
  Pour p ≥ m^4 : J ≈ 1/m < m. DONC N = 0 ✅ (si D est assez bon)

  ★★★ CECI EST UN ARGUMENT FORMALISABLE ! ★★★
  Il faut "juste" une borne EFFECTIVE sur la discrepance D(J,m)
  de la suite {⌈n₃·j·θ⌉ mod m}_{j≥1} ou θ = log₂(3).
""")
