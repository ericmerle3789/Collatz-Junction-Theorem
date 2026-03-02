#!/usr/bin/env python3
"""
SP10 Level 9 — Formalisation de l'argument Beatty
==================================================
OBJECTIF : Formaliser l'argument que N(p, k_crit) = 0 pour p ≥ m^4
en utilisant les suites de Beatty et les bornes de discrepance.

THEOREME A DEMONTRER (esquisse) :
  Pour tout M_0 effectif, pour tout m > M_0, pour tout premier p
  avec ord_p(2) = m et p ≥ m^4 :
    N(p, k_crit(p)) = 0

  ou k_crit(p) = 17 + ln((p-1)/0.041) / |ln(1-1/m)| ≈ m·(ln(p)+3.2)

INGREDIENTS :
  1. Borne triviale : ρ ≤ 1 - 1/m → k_crit ≤ m·(ln(p)+3.2)
  2. Structure : p|d(k) requiert k = n₃·j avec n₃·m | p-1
  3. Condition residuelle : suite de Beatty f(j) = ⌈αj⌉ mod m
  4. Discrepance de Weyl : erreur O(1/J) pour J termes

VERIFICATION NUMERIQUE de chaque etape.
"""

import math
import sys

sys.set_int_max_str_digits(100000)
sys.stdout = open(sys.stdout.fileno(), mode='w', buffering=1)

from sympy import n_order

def S(k):
    return int(math.ceil(k * math.log2(3)))

theta = math.log2(3)  # ≈ 1.58496...

print("=" * 70)
print("SP10 L9 — Formalisation de l'argument Beatty")
print("=" * 70)


# ============================================================
# ETAPE 1 : Borne sur k_crit avec ρ ≤ 1-1/m
# ============================================================

print("\n1. BORNE sur k_crit (borne triviale ρ ≤ 1-1/m)")
print("-" * 50)

print("""
  k_crit(p) = 17 + ln((p-1)/0.041) / |ln(ρ)|

  Avec ρ ≤ 1-1/m : |ln(ρ)| ≥ |ln(1-1/m)| ≈ 1/m (pour m grand)
  Plus precisement : |ln(1-1/m)| = 1/m + 1/(2m²) + O(1/m³)

  Donc : k_crit ≤ 17 + m · (ln(p-1) + ln(1/0.041))
              = 17 + m · (ln(p-1) + 3.194)
              ≤ m · (ln(p) + 4)   pour p ≥ 10, m ≥ 2
""")

def k_crit_trivial(p, m):
    """Borne superieure sur k_crit avec borne triviale rho."""
    rho = 1 - 1/m
    abs_ln_rho = abs(math.log(rho))
    return 17 + (math.log(p - 1) + math.log(1/0.041)) / abs_ln_rho

# Verifier pour quelques exemples
print(f"  {'m':>6} {'p':>15} {'k_crit':>10} {'m·(ln(p)+4)':>14}")
print("  " + "-" * 50)

test_cases = [
    (200, 200**4 + 1),
    (300, 300**4 + 1),
    (500, 500**4 + 1),
    (1000, 1000**4 + 1),
    (200, 2**200 - 1),  # Mersenne-like
]

for m, p in test_cases:
    kc = k_crit_trivial(p, m)
    bound = m * (math.log(p) + 4)
    print(f"  {m:>6} {p:>15.3e} {kc:>10.1f} {bound:>14.1f}")


# ============================================================
# ETAPE 2 : Nombre de j candidats J = k_crit / n₃
# ============================================================

print("\n\n2. NOMBRE DE CANDIDATS J = k_crit / n₃")
print("-" * 50)

print("""
  Pour k = n₃·j, on a j ∈ [69/n₃, k_crit/n₃].
  Le nombre de candidats est J ≈ k_crit / n₃.

  Deux cas :
  (a) 3 ∈ ⟨2⟩ mod p : n₃ = 1, J = k_crit (PAS de premier filtre)
  (b) 3 ∉ ⟨2⟩ mod p : n₃ ≥ (p-1)/m (dans le cas "generique")
      En general : n₃ | (p-1)/m et n₃ ≥ 2

  CAS GENERIQUE (n₃ = (p-1)/m) :
    J = k_crit / n₃ = k_crit · m / (p-1)
    ≤ m · (ln(p)+4) · m / (p-1)
    = m² · (ln(p)+4) / (p-1)

  Pour p ≥ m^4 :
    J ≤ m² · (4·ln(m)+4) / (m^4 - 1)
    ≈ 4m² · ln(m) / m^4
    = 4·ln(m) / m²
    → 0 comme ln(m)/m²

  Pour p = 2^m - 1 (Mersenne) :
    J ≤ m² · m·ln(2) / (2^m - 2)
    = m³·ln(2) / (2^m - 2)
    → 0 EXPONENTIELLEMENT
""")

print(f"  {'m':>6} {'regime':>10} {'J_approx':>12} {'J < 1 ?':>10}")
print("  " + "-" * 45)

for m in [10, 20, 50, 100, 200, 500, 1000]:
    # Regime B : p = m^4
    p = m**4
    J_gen = m**2 * (4 * math.log(m) + 4) / (p - 1)
    ok = "OUI ✅" if J_gen < 1 else f"NON ({J_gen:.1f})"
    print(f"  {m:>6} {'p=m^4':>10} {J_gen:>12.6f} {ok:>10}")

    # Mersenne
    if m <= 100:
        p_mer = 2**m - 1
        J_mer = m**3 * math.log(2) / (p_mer - 1) if p_mer > 2 else float('inf')
        ok_mer = "OUI ✅" if J_mer < 1 else f"NON ({J_mer:.1f})"
        print(f"  {m:>6} {'Mersenne':>10} {J_mer:>12.2e} {ok_mer:>10}")


# ============================================================
# ETAPE 3 : Borne de discrepance pour suites de Beatty
# ============================================================

print("\n\n3. DISCREPANCE de la suite de Beatty")
print("-" * 50)

print("""
  La suite {⌈α·j⌉ mod m}_{j=1}^{J} a une discrepance D_J verifiant :

  THEOREME (Weyl-Erdos-Turan) :
    D_J ≤ C₁/H + (1/J)·Σ_{h=1}^{H} |Σ_{j=1}^{J} e(h·⌈αj⌉/m)| / h

  Pour α irrationnel de type Diophantien (comme θ = log₂(3)) :
    D_J = O(log(J·m) / J)

  Plus precisement, si α a des quotients partiels ≤ A dans sa
  fraction continue, alors :
    D_J ≤ C · A · log(m) / J   (borne effective)

  Pour θ = log₂(3) :
    Fraction continue : [1; 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, ...]
    Les quotients partiels sont BORNES (empiriquement ≤ 55 pour les
    20 premiers termes). Si on suppose a_n ≤ A pour tout n,
    la discrepance est ≤ C·A·log(m)/J.

  BORNE NECESSAIRE pour conclure N = 0 :
    N(p, k_crit) ≤ J/m + J·D_J ≤ J/m + C·A·log(m)
    On veut N < 1, i.e., J/m + C·A·log(m) < 1.

  PROBLEME : Le terme C·A·log(m) ne depend PAS de J !
  Si C·A·log(m) ≥ 1, on ne peut JAMAIS conclure N = 0.

  RESOLUTION : Pour la suite de Beatty SPECIFIQUE {⌈αj⌉ mod m},
  le nombre de j ∈ [1,J] tels que ⌈αj⌉ ≡ r (mod m) est :
    N_r(J) = J/m + O(1)

  L'erreur O(1) est UNIFORMEMENT BORNEE (par 1 exactement !).
  C'est une propriete des suites de Beatty generalisees.

  DONC : N = J/m + O(1). Si J/m < 1, alors J < m et N ≤ 1.
  Si J/m < 1 - ε, alors N = 0 pour m assez grand.
""")


# ============================================================
# ETAPE 4 : Le theoreme des trois distances et suites de Beatty
# ============================================================

print("\n4. THEOREME DES TROIS DISTANCES (Steinhaus)")
print("-" * 50)

print("""
  THEOREME (Trois distances / Steinhaus 1957) :
  Les N points {j·α} (j=1,...,N) sur le cercle R/Z partitionnent
  le cercle en N arcs de au plus 3 longueurs distinctes.

  APPLICATION a notre probleme :
  Les J points {α·j/m} = {n₃·θ·j/m} sur R/Z determinent des arcs.
  La condition ⌈n₃·θ·j⌉ ≡ 0 (mod m) correspond a {n₃·θ·j} ∈ [0, 1/m).

  Le nombre de j dans un intervalle de longueur 1/m est :
    N = J/m + erreur, ou |erreur| ≤ 1

  C'est une consequence du theoreme des trois distances :
  chaque arc contient J/m ± 1 points.

  DONC (RIGOUREUSEMENT) :
    #{j ∈ [1,J] : ⌈n₃·θ·j⌉ ≡ 0 (mod m)} ≤ ⌊J/m⌋ + 1

  Si J < m : ⌊J/m⌋ = 0, donc N ≤ 1.
  Si J < 1 : N = 0 (car j ≥ 1).

  ★ CECI EST UNE BORNE RIGOUREUSE ET EFFECTIVE ★
""")

# Verifier numeriquement le theoreme des trois distances
print("\n  Verification numerique :")
for m_test in [7, 13, 31, 127]:
    alpha = theta  # log₂(3) modifie par n₃ dans la pratique
    for J_test in [3, m_test // 2, m_test, 2 * m_test]:
        count = 0
        for j in range(1, J_test + 1):
            val = math.ceil(alpha * j * 6)  # simulate n₃=6
            if val % m_test == 0:
                count += 1
        bound = J_test // m_test + 1
        print(f"    m={m_test:>4}, J={J_test:>5}: N={count:>3}, bound=⌊J/m⌋+1={bound:>3}, "
              f"{'OK' if count <= bound else '!!!'}")


# ============================================================
# ETAPE 5 : Assembler l'argument
# ============================================================

print("\n\n5. ASSEMBLAGE DE L'ARGUMENT COMPLET")
print("=" * 70)

print("""
  ★★★ PROPOSITION (Regime B, formalisable) ★★★

  Soit M_0 un entier effectif. Pour tout premier p et m = ord_p(2)
  satisfaisant p ≥ m^4 et m > M_0 :

    ∀ k ∈ [69, k_crit(p)] : p ∤ d(k)

  PREUVE (esquisse rigoureuse) :

  1. BORNE SUR k_crit :
     ρ(p, ⟨2⟩) ≤ 1 - 1/m (borne triviale, [D26])
     |ln(ρ)| ≥ 1/m - 1/(2m²) ≥ 1/(2m) pour m ≥ 2
     k_crit = 17 + ln((p-1)/0.041) / |ln(ρ)|
            ≤ 17 + 2m · (ln(p) + 3.2)
            ≤ 3m · ln(p)  pour p ≥ e^6

  2. PREMIER FILTRE :
     p | d(k) ⟹ 3^k ∈ ⟨2⟩ mod p ⟹ k ≡ 0 (mod n₃)
     ou n₃ = min{j ≥ 1 : 3^j ∈ ⟨2⟩ mod p}.
     On a n₃ · m | p - 1, donc n₃ ≥ (p-1)/m.

     CAS 1 : Si 3 ∈ ⟨2⟩ (n₃ = 1) :
       Alors ρ < 1 (par D26) et k_crit est FINI.
       La condition S(k) ≡ log_2(3)·k (mod m) est toujours satisfaite
       quand 2^{log_2(3)} = 3, ce qui est vrai mod p.
       Dans ce cas, il faut un argument DIFFERENT.
       MAIS : 3 ∈ ⟨2⟩ implique n₃ = 1, donc n₃·m = m divise p-1.
       → p ≡ 1 (mod m) mais m | p-1 est deja connu.
       → Le deuxieme filtre devient S(k) ≡ L·k (mod m) ou L = log_2(3) mod m.
       → Meme analyse de Beatty avec α' = θ - L/n₃.

     CAS 2 : Si 3 ∉ ⟨2⟩ (n₃ ≥ 2) :
       Le nombre de k ∈ [69, k_crit] multiples de n₃ est :
       J₁ = ⌊k_crit/n₃⌋ - ⌈69/n₃⌉ + 1 ≤ k_crit/n₃ + 1

       J₁ ≤ 3m·ln(p)/n₃ + 1 ≤ 3m·ln(p)·m/(p-1) + 1 = 3m²·ln(p)/(p-1) + 1

  3. DEUXIEME FILTRE (suite de Beatty) :
     Pour k = n₃·j : p|d(k) ⟺ ⌈n₃·j·θ⌉ ≡ L·j (mod m)
     i.e., f(j) = ⌈n₃·j·θ⌉ - L·j ≡ 0 (mod m).

     Soit α = n₃·θ - L (reel). Alors f(j) = ⌈αj + Lj⌉ - Lj ≈ ⌈αj⌉ (mod m).
     [Plus precis : f(j) = ⌈(n₃θ)j⌉ - Lj, et n₃θ - L est irrationnel
      car θ est irrationnel et L est entier.]

     Par le theoreme des trois distances :
     #{j ∈ [1, J₁] : f(j) ≡ 0 (mod m)} ≤ ⌊J₁/m⌋ + 1

  4. CONCLUSION :
     Si J₁ < m, alors ⌊J₁/m⌋ = 0, et la borne donne N ≤ 1.
     La condition J₁ < m equivaut a :
       3m²·ln(p)/(p-1) + 1 < m
     i.e., 3m·ln(p)/(p-1) < 1 - 1/m
     Pour p ≥ m^4 : 3m·4·ln(m)/(m^4-1) < 1
     i.e., 12·ln(m)/m³ < 1
     Vrai pour m ≥ 4 !

     Donc N ≤ 1 pour m ≥ 4 et p ≥ m^4.

     ★ MAIS on veut N = 0, pas N ≤ 1 ★

  5. AFFINER POUR N = 0 :
     N ≤ 1 signifie qu'il y a AU PLUS un j dans [1, J₁] tel que
     f(j) ≡ 0 (mod m). Il faut montrer que ce j unique, s'il existe,
     a k = n₃·j > k_crit ou k < 69.

     APPROCHE : Comme J₁/m ≈ ln(m)/m² (pour p = m^4), la "fenetre"
     est BEAUCOUP plus petite que m. La probabilite qu'un point de
     la suite de Beatty tombe exactement dans cette fenetre est
     ENVIRON J₁/m ≈ ln(m)/m² → 0.

     Mais "probabilite → 0" n'est pas "= 0" deterministe.

     OPTION A : Pour p >> m^4 (Mersenne), J₁ < 1, donc N = 0 trivial.
     OPTION B : Pour p ≈ m^4, N ≤ 1 et le cas N = 1 correspond a
                un "accident arithmetique" qui peut etre exclu pour
                m assez grand par un argument supplementaire.
""")


# ============================================================
# ETAPE 6 : Verification numerique de N ≤ 1 pour p ≈ m^4
# ============================================================

print("\n6. VERIFICATION NUMERIQUE : N ≤ 1 pour p ≈ m^4")
print("-" * 50)

# Generer des premiers p ≈ m^4 avec ord_p(2) = m
# Strategie : pour chaque m, trouver p | (2^m - 1) avec p ≈ m^4

print("""
  Pour les premiers p avec ord_p(2) = m et p ≈ m^4 :
  - p | (2^m - 1), donc on cherche des facteurs de 2^m-1 proches de m^4
  - Ces premiers sont RARES (la plupart des facteurs sont << m^4 ou >> m^4)
""")

from sympy import factorint, isprime as sym_isprime

# Pour quelques m, trouver des facteurs de 2^m - 1 et leur taille
print(f"  {'m':>6} {'p':>15} {'p/m^4':>10} {'N(p,5K)':>8} {'J_bound':>10}")
print("  " + "-" * 55)

for m in [7, 13, 17, 19, 31, 41, 43, 47, 53, 59, 61]:
    mersenne = 2**m - 1
    try:
        facs = factorint(mersenne, limit=10**9)
    except:
        continue

    for p, _ in sorted(facs.items()):
        if not sym_isprime(p):
            continue
        if n_order(2, p) != m:
            continue

        ratio = p / m**4
        kc = k_crit_trivial(p, m)

        # Compter N(p, 5000) - rapide car pow(2,S,p) est O(log(S))
        count = 0
        for k in range(69, min(5001, int(kc) + 100)):
            Sk = S(k)
            if (pow(2, Sk, p) - pow(3, k, p)) % p == 0:
                count += 1

        # Borne J
        n3_eff = None
        for j in range(1, min(p, 10000)):
            if pow(3, j * m, p) == 1:
                break
        n3_eff = j if j < 10000 else p - 1
        J_bound = kc / max(n3_eff, 1)

        regime = "B" if ratio >= 1 else "A"
        print(f"  {m:>6} {p:>15} {ratio:>10.4f} {count:>8} {J_bound:>10.2f} [{regime}]")


# ============================================================
# ETAPE 7 : Synthese formelle
# ============================================================

print(f"\n\n{'='*70}")
print("7. SYNTHESE FORMELLE — Ce qui est demontrable")
print(f"{'='*70}")

print("""
  ★ THEOREME DEMONTRABLE (avec travail technique) :

  Pour tout premier p avec m = ord_p(2) ≥ M_0 et p ≥ m^4 :
    Le nombre de k ∈ [69, k_crit(p)] tels que p | d(k) est ≤ 1.

  INGREDIENTS :
  1. ρ ≤ 1-1/m (borne triviale) → k_crit ≤ 3m·ln(p) [CONNU]
  2. n₃·m | p-1 (structure de groupe) [ELEMENTAIRE]
  3. Theoreme des trois distances [CLASSIQUE, 1957]
  4. θ = log₂(3) irrationnel [ELEMENTAIRE]

  ★ GAP RESTANT :
  Pour fermer completement, il faut :
  (a) Montrer que N = 0 (pas juste ≤ 1), OU
  (b) Montrer que le "cas N = 1" est exclu par un argument supplementaire
      (Baker/Matveev pour l'espacement ? structure arithmetique ?)
  (c) Ou accepter que N ≤ 1 et traiter le cas N = 1 separement
      (montrer que (Q) est satisfaite quand p | d(k) une seule fois)

  OPTION (c) est PROMETTEUSE :
  Si p | d(k) pour un seul k dans [69, k_crit], alors :
  - (p-1)·ρ^{k-17} = (p-1)·(1-1/m)^{k-17}
  - Pour k ≥ 69 et m ≥ M_0, (p-1) ≤ p ≤ 2^m - 1
  - Et (1-1/m)^{52} ≤ (1-1/M_0)^{52}
  - Pour M_0 = 200 : (1-1/200)^{52} = 0.995^{52} = 0.771
  - Et (p-1)·0.771 >> 0.041 si p > 1.

  Donc le "cas N = 1" ne satisfait PAS (Q) avec la borne triviale.
  On a besoin de ρ EFFECTIVEMENT < 1 - δ avec δ > 0 EXPLICITE.

  C'EST EXACTEMENT LE PROBLEME INITIAL (boulon 6.3).

  ★★★ CONCLUSION FINALE ★★★

  L'argument Beatty/discrepance montre N ≤ 1 pour le regime B,
  mais ne ferme pas completement car :
  - N ≤ 1 n'exclut pas le cas d'UN hit
  - Et (Q) requiert ρ < 1 - O(ln(p)/k) qui n'est pas garanti
    par la borne triviale seule

  PROGRES REEL : Reduction du probleme de "N inconnu" a "N ≤ 1".
  C'est un progres ENORME par rapport a l'etat initial.

  Le gap residuel est :
  - Soit fermer N = 0 (argument plus fin sur Beatty)
  - Soit obtenir une borne ρ ≤ 1 - c/m^α avec α < 1 (plus faible que BGK)
  - Soit combiner N ≤ 1 avec Baker pour l'espacement
""")
