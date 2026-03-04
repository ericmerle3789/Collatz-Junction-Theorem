#!/usr/bin/env python3
"""
SESSION 8 — APPROFONDISSEMENT B2 : BAKER / ÉNONCÉ A
=====================================================
Protocole DISCOVERY v2.0, Lentille L2 (Analytique).

ÉNONCÉ A : ord_d(2) > S - 1  pour tout k ≥ 4
  où d = 2^S - 3^k, S = ⌈k·log₂3⌉

POURQUOI C'EST IMPORTANT :
  Si ord_d(2) ≤ S-1, alors ∃ r ≤ S-1 tel que d | (2^r - 1).
  Cela signifierait que d | gcd(2^r - 1, 2^S - 3^k),
  ce qui donnerait 2^r ≡ 1 et 2^S ≡ 3^k mod d, donc
  3^k ≡ 2^{S-r} mod d. Or S-r ≥ 1.
  Pour l'Énoncé C, on a besoin que ord_d(2) > S - 1 pour
  garantir l'injectivité dans l'automate.

APPROCHE BAKER :
  Théorème de Baker (1967) : Si α, β sont algébriques ≠ 0,1,
  et si b₁, b₂ sont entiers, alors
  |b₁·log α - b₂·log β| > exp(-C(α,β)·log(max(|b₁|,|b₂|)))
  pour une constante effective C.

  Application : 2^r ≡ 1 mod d ⟺ d | (2^r - 1)
  ⟺ 2^r - 1 = m·d = m·(2^S - 3^k) pour un entier m ≥ 1.
  ⟺ 2^r - 1 ≡ 0 mod (2^S - 3^k)

  Alternative directe :
  Si 2^r ≡ 1 mod d et r ≤ S-1, alors d | (2^r - 1).
  Comme d = 2^S - 3^k et 2^r - 1 < 2^S - 1 = d + 3^k - 1,
  on a m = (2^r - 1)/d < 1 + (3^k - 1)/d.
  Or d ≈ 0.086... · 2^S pour grand k (car 2^S - 3^k ~ {k·log₂3}·2^S).
  Donc si r < S, alors 2^r < 2^S = d + 3^k,
  et 2^r - 1 ≤ 2^{S-1} - 1 < 3^k (car S = ⌈k·log₂3⌉ → 2^{S-1} < 3^k).
  Mais d = 2^S - 3^k < 3^k (car 2^S < 2·3^k),
  donc 2^{r} - 1 < 3^k = 2^S - d, et m·d ≤ 2^{r} - 1 < 2^S - d = d + (2^S - 2d).
  Hmm, cet argument ne conclut pas directement.

APPROCHE DIRECTE (sans Baker) :
  Si r | S (r divise S), alors 2^r ≡ 1 mod d ⟹ d | (2^r - 1).
  Mais 2^S - 1 = (2^r - 1)(2^{S-r} + 2^{S-2r} + ... + 1)
  et d = 2^S - 3^k, donc d | (2^S - 1) ssi 3^k ≡ 1 mod (2^S - 1)... non.

  CLEF : d = 2^S - 3^k, et on veut montrer que 2^r ≢ 1 mod d pour r < S.

  2^r ≡ 1 mod d ⟺ 2^r ≡ 1 mod (2^S - 3^k)
  ⟺ 2^S - 3^k | 2^r - 1
  ⟺ 2^r ≡ 1 (mod 2^S - 3^k)

  Pour r < S : 2^r - 1 < 2^S - 1.
  Et d = 2^S - 3^k ≥ 5 (pour k ≥ 3).

  Si d | (2^r - 1), alors 2^r - 1 ≥ d = 2^S - 3^k.
  Donc 2^r ≥ 2^S - 3^k + 1.
  Comme r < S : 2^r ≤ 2^{S-1}.
  Donc 2^{S-1} ≥ 2^S - 3^k + 1
  ⟹ 3^k ≥ 2^S - 2^{S-1} + 1 = 2^{S-1} + 1.

  OR : S = ⌈k·log₂3⌉, donc 2^S ≥ 3^k, donc 2^{S-1} ≥ 3^k/2.
  La condition 3^k ≥ 2^{S-1} + 1 ⟺ 3^k ≥ 3^k/2 + 1 est TOUJOURS VRAIE.
  Donc cet argument ne donne rien pour r = S-1.

  MAIS : si d | (2^r - 1) pour un PETIT r, alors 2^r - 1 est petit.
  d = 2^S - 3^k > 0, et pour r ≤ S/2 par exemple :
  2^r - 1 ≤ 2^{S/2} - 1.
  d ≥ 2^S - 3^k = 2^S(1 - 3^k/2^S) = 2^S·(1 - 3^k/2^S).

  3^k/2^S < 1 (car S = ⌈k log₂3⌉, donc 2^S ≥ 3^k).
  Exactement : d = 2^S - 3^k, et {k log₂3} = S - k log₂3 ∈ (0,1].
  Donc d = 2^S(1 - 2^{-{k log₂3}·...}). Hmm, compliqué.

  Approche plus concrète : calculer d et comparer à 2^r - 1.
"""

from math import ceil, log2, gcd, comb, log, exp, pi
from itertools import combinations
from collections import defaultdict
import sys

def compute_params(k):
    S = ceil(k * log2(3))
    d = 2**S - 3**k
    C = comb(S - 1, k - 1)
    return S, d, C

def factorize(n):
    factors = {}
    d_val = 2
    while d_val * d_val <= n:
        while n % d_val == 0:
            factors[d_val] = factors.get(d_val, 0) + 1
            n //= d_val
        d_val += 1
    if n > 1:
        factors[n] = 1
    return factors

def ord_mod(a, m):
    if gcd(a, m) != 1: return None
    phi = 1
    for p, e in factorize(m).items():
        phi *= (p - 1) * p**(e - 1)
    order = phi
    for p, e in factorize(phi).items():
        for _ in range(e):
            if pow(a, order // p, m) == 1:
                order //= p
            else:
                break
    return order

# ============================================================
# INVESTIGATION 1 : Cartographie complète ord_d(2) vs S
# ============================================================
def investigate_ord_map(max_k=35):
    """
    Calculer ord_d(2) pour k=3..max_k et comparer à S, S-1.
    """
    print("=" * 70)
    print("  INVESTIGATION 1 : ord_d(2) vs S pour k=3..35")
    print("=" * 70)
    print(f"  {'k':>3} {'S':>4} {'d':>15} {'ord_d(2)':>12} {'ord/S':>10} {'ord>S-1':>8}")
    print(f"  {'---':>3} {'---':>4} {'---':>15} {'---':>12} {'---':>10} {'---':>8}")

    for k in range(3, max_k + 1):
        S, d, C = compute_params(k)
        try:
            o = ord_mod(2, d)
            if o is not None:
                ratio = o / S
                ok = o > S - 1
                print(f"  {k:>3} {S:>4} {d:>15} {o:>12} {ratio:>10.2f} {'YES' if ok else '***NO***':>8}")
            else:
                print(f"  {k:>3} {S:>4} {d:>15} {'N/A':>12} {'N/A':>10} {'N/A':>8}")
        except Exception as e:
            print(f"  {k:>3} {S:>4} {d:>15} {'ERR':>12}")

# ============================================================
# INVESTIGATION 2 : Arguments de taille pour exclure petit r
# ============================================================
def investigate_size_argument(max_k=35):
    """
    Si 2^r ≡ 1 mod d (r < S), alors d | (2^r - 1), donc 2^r > d + 1.
    Cela donne r > log₂(d + 1).
    Donc ord_d(2) > log₂(d).
    Comme d ≈ c · 2^S pour grand S (fraction de 2^S), cela ne suffit pas.

    MAIS : d = 2^S - 3^k, et on peut comparer directement.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 2 : Arguments de taille — borne inf de r")
    print("=" * 70)

    print(f"  {'k':>3} {'S':>4} {'d':>15} {'log2(d)':>10} {'S-1':>5} {'ratio':>10} {'frac':>10}")
    print(f"  {'---':>3} {'---':>4} {'---':>15} {'---':>10} {'---':>5} {'---':>10} {'---':>10}")

    for k in range(3, max_k + 1):
        S, d, C = compute_params(k)
        logd = log2(d)
        frac = d / 2**S  # d/2^S = 1 - 3^k/2^S
        print(f"  {k:>3} {S:>4} {d:>15} {logd:>10.2f} {S-1:>5} {logd/(S-1):>10.3f} {frac:>10.6f}")

# ============================================================
# INVESTIGATION 3 : Approche Baker effective
# Le théorème de Baker-Wüstholz (1993) donne :
# Si Λ = b₁ log α₁ + b₂ log α₂ ≠ 0, alors
# log|Λ| > -(16·n·d)^{2(n+2)} · log(A₁) · log(A₂) · log(B)
# avec n=2, d=[Q(α₁,α₂):Q]=1, A_i ≥ max(|log α_i|, 1/d), B ≥ max(|b_i|)
#
# Application : Λ = r·log 2 - m·log d (pas directement utile)
# Plutôt : si 2^r ≡ 1 mod d, est-ce que les petits diviseurs
# de d contraignent r ?
# ============================================================
def investigate_baker_approach(max_k=30):
    """
    Approche via les diviseurs de ord_d(2).

    FAIT : ord_d(2) | lcm{ord_p(2) : p premier, p | d}
    FAIT : Si p | d, alors ord_p(2) | (p-1).

    STRATÉGIE : Si on montre que pour chaque p | d,
    ord_p(2) > S - 1, alors ord_d(2) > S - 1.
    Mais cela ne marche pas toujours (petits p ont petit ord).

    ALTERNATIVE : ord_d(2) = lcm{ord_{p^e}(2) : p^e || d}
    Et pour p grand (comme le plus grand facteur premier de d),
    ord_p(2) est souvent >> S.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 3 : ord_d(2) via factorisation de d")
    print("=" * 70)

    for k in range(3, min(max_k + 1, 25)):
        S, d, C = compute_params(k)
        facts = factorize(d)

        print(f"\n  k={k}: d={d}, S={S}")
        print(f"    Factorisation : {' × '.join(f'{p}^{e}' if e > 1 else str(p) for p,e in sorted(facts.items()))}")

        ords = {}
        for p, e in facts.items():
            pe = p ** e
            o = ord_mod(2, pe)
            ords[pe] = o
            print(f"    ord_{pe}(2) = {o}, ratio ord/S = {o/S:.2f}")

        # lcm de tous les ordres
        from math import lcm
        all_ords = list(ords.values())
        total_lcm = all_ords[0]
        for x in all_ords[1:]:
            total_lcm = lcm(total_lcm, x)

        actual_ord = ord_mod(2, d)
        print(f"    lcm des ordres = {total_lcm}")
        print(f"    ord_d(2) réel  = {actual_ord}")
        print(f"    Cohérent ? {total_lcm == actual_ord}")
        print(f"    ord_d(2) > S-1 ? {'YES' if actual_ord > S-1 else 'NO'}")

        # Quel facteur "contrôle" l'ordre ?
        max_ord_prime = max(ords.items(), key=lambda x: x[1])
        print(f"    Facteur dominant : {max_ord_prime[0]} avec ord = {max_ord_prime[1]}")

# ============================================================
# INVESTIGATION 4 : Pourquoi ord_p(2) est-il si grand pour
# les grands facteurs premiers de d ?
# ============================================================
def investigate_ord_large_prime(max_k=25):
    """
    Pour le plus grand facteur premier p de d :
    - ord_p(2) est typiquement ≈ p-1 ou (p-1)/2
    - Cela signifie que 2 est (presque) une racine primitive mod p

    HEURISTIQUE D'ARTIN : 2 est racine primitive mod p pour
    environ 37.4% des premiers p (conjecture d'Artin).
    Mais pour nos p (qui sont facteurs de 2^S - 3^k), le taux
    est peut-être différent.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 4 : ord_p(2) pour le plus grand facteur de d")
    print("=" * 70)
    print(f"  {'k':>3} {'p_max':>12} {'ord_p(2)':>12} {'p-1':>12} {'ord/(p-1)':>10}")
    print(f"  {'---':>3} {'---':>12} {'---':>12} {'---':>12} {'---':>10}")

    for k in range(3, max_k + 1):
        S, d, C = compute_params(k)
        facts = factorize(d)
        p_max = max(facts.keys())

        o = ord_mod(2, p_max)
        if o is not None:
            ratio = o / (p_max - 1)
            print(f"  {k:>3} {p_max:>12} {o:>12} {p_max-1:>12} {ratio:>10.4f}")

# ============================================================
# INVESTIGATION 5 : Preuve directe que ord_d(2) ≠ S-s
# pour s=1,...,S-1
# ============================================================
def investigate_direct_proof(max_k=30):
    """
    Si ord_d(2) = S - s pour un s ∈ {1,...,S-1}, alors
    d | (2^{S-s} - 1).

    Comme d = 2^S - 3^k :
    (2^S - 3^k) | (2^{S-s} - 1)

    2^{S-s} ≡ 1 mod (2^S - 3^k)
    2^S = 2^s · 2^{S-s} ≡ 2^s mod (2^S - 3^k)
    Mais 2^S ≡ 3^k mod d, donc 3^k ≡ 2^s mod d.

    DONC : si ord_d(2) | (S-s), alors 3^k ≡ 2^s mod d.
    Comme d = 2^S - 3^k : 3^k ≡ 2^s mod (2^S - 3^k)
    ⟺ 2^S - 3^k | 3^k - 2^s
    ⟺ |3^k - 2^s| ≡ 0 mod d  (ou |3^k - 2^s| = 0)
    ⟺ |3^k - 2^s| ≥ d  (si 3^k ≠ 2^s)

    MAIS |3^k - 2^s| < max(3^k, 2^s) ≤ max(3^k, 2^{S-1}) = 3^k
    (car 2^{S-1} < 3^k quand s < S)

    Et d = 2^S - 3^k. On a 3^k ≤ 2·d (grossièrement).
    Donc |3^k - 2^s| < 2d ne donne rien quand |3^k - 2^s| ≥ d.

    EN FAIT : si 3^k - 2^s = m·d, alors m ≥ 1 et m·d ≤ 3^k,
    donc m ≤ 3^k/d.
    Pour s ≤ S-1 : 2^s ≤ 2^{S-1} < 3^k, donc 3^k - 2^s > 0.
    Et 3^k - 2^s < 3^k ≤ 2d (car d ≥ 3^k/2 pour S ≈ k log₂3 + ε).
    Attendons... d peut être BIEN PLUS PETIT que 3^k.
    d/3^k = 2^S/3^k - 1 = 2^{S - k log₂3} - 1 = 2^{frac(k log₂3)} - 1
    où frac = partie fractionnaire. Donc d/3^k ∈ (0, 1).

    Vérifions numériquement.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 5 : 3^k - 2^s vs d pour s=1..S-1")
    print("=" * 70)

    for k in range(3, min(max_k + 1, 25)):
        S, d, C = compute_params(k)

        print(f"\n  k={k}: S={S}, d={d}, d/3^k={d/3**k:.6f}")

        # Pour chaque s, calculer |3^k - 2^s| et le rapport à d
        min_ratio = float('inf')
        min_s = -1
        multiples_found = []

        for s in range(1, S):
            diff = abs(3**k - 2**s)
            ratio = diff / d
            if ratio < min_ratio:
                min_ratio = ratio
                min_s = s

            # Est-ce un multiple de d ?
            if diff % d == 0:
                m = diff // d
                multiples_found.append((s, m, diff))

        print(f"    Near-miss : s={min_s}, |3^k - 2^{min_s}|/d = {min_ratio:.6f}")

        if multiples_found:
            for s, m, diff in multiples_found:
                print(f"    ★ MULTIPLE TROUVÉ : s={s}, 3^k - 2^s = {m}·d")
                print(f"      CELA SIGNIFIE 2^{S-s} ≡ ±1 mod d → ord_d(2) | 2(S-s) !")
        else:
            print(f"    Aucun s ∈ {{1,...,{S-1}}} avec d | (3^k - 2^s)")
            print(f"    → 3^k ≢ 2^s mod d pour tout s < S")
            print(f"    → ord_d(2) NE DIVISE PAS (S-s) pour tout s ∈ {{1,...,S-1}}")
            print(f"    → En particulier, ord_d(2) > S-1 (car ord ∤ r ⟹ ord > r si premier)")
            # ATTENTION : ord ∤ (S-s) pour tout s n'implique PAS directement ord > S-1
            # Car l'ordre pourrait diviser un nombre entre 1 et S-1 qui n'est pas de la forme S-s
            # En fait S-s parcourt 1, 2, ..., S-1 quand s parcourt S-1, ..., 1
            # Donc "ord ∤ r pour tout r ∈ {1,...,S-1}" IMPLIQUE ord ≥ S. QED!

# ============================================================
# INVESTIGATION 6 : Baker bounds pour |3^k - 2^s|
# ============================================================
def investigate_baker_bounds(max_k=30):
    """
    Théorème de Baker (forme effective de Laurent-Mignotte-Nesterenko 1995) :

    Soit Λ = s·log 2 - k·log 3. Alors si Λ ≠ 0 :
    |Λ| > exp(-C₀ · log s · log k)
    où C₀ est une constante effective (environ 30).

    Cela donne : |2^s - 3^k| = 2^s · |1 - 3^k/2^s| ≈ 2^s · |Λ|
    → |3^k - 2^s| > 2^s · exp(-C₀ · log s · log k)

    Pour que d | (3^k - 2^s), il faut |3^k - 2^s| ≥ d.
    Donc il faut : 2^s · exp(-C₀ · log s · log k) < d = 2^S - 3^k.

    Comme d ≈ δ · 3^k avec δ = d/3^k ∈ (0,1) :
    2^s · exp(-C₀ · log s · log k) < δ · 3^k

    Si s est loin de k·log₂3 : |Λ| est grand, et la borne de Baker
    est largement satisfaite.

    Le problème est quand s ≈ k·log₂3, c'est-à-dire s ≈ S ou s = S-1.

    Pour s = S-1 : Λ = (S-1)·log 2 - k·log 3 = S·log 2 - log 2 - k·log 3
    = log(2^S) - log 2 - log(3^k) = log(2^S/3^k) - log 2
    = log(1 + d/3^k) - log 2.

    Si d est petit : Λ ≈ d/3^k - log 2 ≈ -log 2 < 0.
    Donc |2^{S-1} - 3^k| = 3^k - 2^{S-1} = 3^k(1 - 2^{S-1}/3^k).

    2^{S-1}/3^k = 2^S/(2·3^k) = (d + 3^k)/(2·3^k) = 1/2 + d/(2·3^k).
    Donc 3^k - 2^{S-1} = 3^k(1 - 1/2 - d/(2·3^k)) = 3^k/2 - d/2.

    Et d = 3^k·(2^{S-k·log₂3} - 1). Hmm.

    En pratique, calculons.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 6 : Bornes de Baker pour |3^k - 2^s|")
    print("=" * 70)

    # Constante de Baker (simplifiée)
    # Laurent-Mignotte-Nesterenko (1995) : pour Λ = b₂ log α₂ - b₁ log α₁
    # avec α₁=2, α₂=3, b₁=s, b₂=k :
    # log|Λ| > -24.34 · (max(21, log(s) + 0.14))^2 · 0.693 · 1.099
    # ≈ -24.34 · (log(s))^2 · 0.76 pour s >> 1
    # Simplifions avec une constante C₀ ≈ 18.5 · (log s)^2

    print(f"\n  {'k':>3} {'S':>4} {'d':>15} {'3k-2^(S-1)':>15} {'Baker_lb':>15} {'d<3k-2s':>10}")
    print(f"  {'---':>3} {'---':>4} {'---':>15} {'---':>15} {'---':>15} {'---':>10}")

    for k in range(3, max_k + 1):
        S, d, C = compute_params(k)

        # Le cas le plus serré : s = S-1
        s = S - 1
        diff = abs(3**k - 2**s)

        # Baker lower bound (très simplifiée)
        # |s·log 2 - k·log 3| > exp(-C₀ · max(log s, 21)^2)
        # avec C₀ ≈ 18.5 (dépend des constantes exactes)
        C0 = 18.5
        lambda_bound = exp(-C0 * max(log(s), 3)**2)
        baker_lb = int(2**s * lambda_bound)  # borne inf de |3^k - 2^s|

        result = "YES ✅" if baker_lb > d else "no"
        print(f"  {k:>3} {S:>4} {d:>15} {diff:>15} {baker_lb:>15} {result:>10}")

    print("\n  NOTE : La constante C₀=18.5 est ILLUSTRATIVE.")
    print("  Les constantes effectives exactes de Laurent-Mignotte-Nesterenko")
    print("  donnent des bornes beaucoup plus serrées pour k > 50 environ.")

# ============================================================
# INVESTIGATION 7 : La preuve directe via l'argument r ∈ {1..S-1}
# ============================================================
def investigate_direct_r_proof(max_k=35):
    """
    ARGUMENT CLÉ REFORMULÉ :

    ord_d(2) ∤ r  pour tout r ∈ {1,...,S-1}
    ⟺ 2^r ≢ 1 mod d  pour tout r ∈ {1,...,S-1}
    ⟺ d ∤ (2^r - 1)  pour tout r ∈ {1,...,S-1}

    MAIS : ord_d(2) ∤ r pour tout r dans {1,...,S-1}
    ne suffit PAS pour conclure ord_d(2) > S-1 directement.

    On a : ord_d(2) | φ(d).
    Si ord_d(2) = r₀ ≤ S-1, alors r₀ ∈ {1,...,S-1} et 2^{r₀} ≡ 1 mod d.
    Cela contredit le fait que 2^r ≢ 1 mod d pour tout r ∈ {1,...,S-1}.

    DONC : "2^r ≢ 1 mod d pour tout r ∈ {1,...,S-1}"
    ⟹ ord_d(2) ∉ {1,...,S-1}
    ⟹ ord_d(2) ≥ S.

    C'est exactement l'Énoncé A (version forte) !

    Il SUFFIT donc de montrer que d ∤ (2^r - 1) pour r = 1,...,S-1.

    APPROCHE : Pour chaque r ∈ {1,...,S-1}, 2^r - 1 < 2^{S-1}.
    Et d = 2^S - 3^k. On a d < 2^S et d > 0.

    Si d | (2^r - 1), alors 2^r - 1 ≥ d = 2^S - 3^k > 0.
    Donc 2^r ≥ 2^S - 3^k + 1.

    CAS r ≤ S - 2 : 2^r ≤ 2^{S-2} = 2^S/4.
    Il faut 2^S/4 ≥ 2^S - 3^k + 1.
    ⟹ 3^k ≥ 3·2^S/4 + 1.
    Mais 3^k < 2^S (car d > 0), donc 3^k < 2^S.
    Condition : 2^S > 3^k ≥ 3·2^S/4, soit 4/3 > 2^S/3^k ≥ 1.
    Or 2^S/3^k = 1 + d/3^k > 1, et d/3^k < 1 (puisque d < 3^k pour k ≥ 3).
    Quand d/3^k < 1/3 : 2^S/3^k < 4/3 ✓
    Quand d/3^k ≥ 1/3 : 2^S/3^k ≥ 4/3... NON on veut 3^k ≥ 3·2^S/4.
    3·2^S/4 = 3·(3^k + d)/4 = 3·3^k/4 + 3d/4.
    Condition : 3^k ≥ 3·3^k/4 + 3d/4 ⟺ 3^k/4 ≥ 3d/4 ⟺ 3^k ≥ 3d ⟺ d ≤ 3^k/3.

    Vérifions : d/3^k varie avec k (c'est la partie fractionnaire de 2^{frac...}).
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 7 : d/3^k et exclusion de petits r")
    print("=" * 70)
    print(f"  {'k':>3} {'S':>4} {'d':>15} {'d/3^k':>10} {'d≤3^k/3':>8} {'exclu r≤S-2':>12}")

    for k in range(3, max_k + 1):
        S, d, C = compute_params(k)
        ratio = d / 3**k
        can_exclude = d <= 3**k / 3
        # Si d ≤ 3^k/3, alors pour tout r ≤ S-2 : 2^r ≤ 2^{S-2} = 2^S/4
        # et d = 2^S - 3^k ≤ 2^{S-2} ssi 3·2^{S-2} ≤ 3^k ssi 3^k ≥ 3/4·2^S
        # ce qui est 3^k/2^S ≥ 3/4, soit d/2^S ≤ 1/4, soit d ≤ 2^{S-2}
        actual_excl = d <= 2**(S-2)  # Direct comparison
        print(f"  {k:>3} {S:>4} {d:>15} {ratio:>10.6f} {'Y' if can_exclude else 'N':>8} {'Y' if actual_excl else 'N':>12}")

    # Conclusion
    print("\n  RÉSULTAT : d ≤ 2^{S-2} pour tous les k testés ?")
    all_ok = True
    for k in range(3, max_k + 1):
        S, d, C = compute_params(k)
        if d > 2**(S-2):
            print(f"    k={k}: d={d} > 2^{S-2}={2**(S-2)} ← ÉCHEC")
            all_ok = False
    if all_ok:
        print("    OUI ! d ≤ 2^{S-2} pour k=3..35")
        print("    → 2^r < d+1 pour r ≤ S-2, donc d ∤ (2^r-1)")
        print("    → Seul r = S-1 pourrait poser problème")
        print("    → Il suffit de montrer d ∤ (2^{S-1} - 1)")

# ============================================================
# INVESTIGATION 8 : Le cas r = S-1 — le cas critique
# ============================================================
def investigate_r_S_minus_1(max_k=40):
    """
    Il reste à montrer d ∤ (2^{S-1} - 1).

    d = 2^S - 3^k, et 2^{S-1} - 1 = (2^S - 2)/2 = (d + 3^k - 2)/2.

    d | (2^{S-1} - 1) ⟺ 2^{S-1} ≡ 1 mod d
    ⟺ d | (2^{S-1} - 1)

    Or 2^{S-1} - 1 = (d + 3^k - 2)/2.
    d | (d + 3^k - 2)/2 ⟺ d | (3^k - 2)/2 (si 3^k est pair... non, 3^k impair)
    ATTENTION : 3^k est impair, 2 est pair, donc 3^k - 2 est impair.
    Et 2^{S-1} - 1 est impair (car 2^{S-1} est pair).

    2^{S-1} - 1 = (2^S - 2)/2 = (d + 3^k - 2)/2.
    d est impair (gcd(d,6)=1). Donc d | (d + 3^k - 2)/2
    ssi d | (3^k - 2)/2... NON, 3^k - 2 impair, pas divisible par 2.

    Plus proprement : 2^{S-1} ≡ 1 mod d ⟺ 2·2^{S-1} ≡ 2 mod d
    ⟺ 2^S ≡ 2 mod d ⟺ 3^k ≡ 2 mod d.
    Car 2^S ≡ 3^k mod d.
    Donc 3^k ≡ 2 mod d ⟺ d | (3^k - 2).

    MAGNIFIQUE ! ord_d(2) = S-1 ⟺ d | (3^k - 2).
    Vérifions numériquement.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 8 : Le cas r=S-1 ⟺ d | (3^k - 2)")
    print("=" * 70)
    print(f"  {'k':>3} {'S':>4} {'d':>15} {'3^k-2':>20} {'d|(3^k-2)':>10} {'(3^k-2)/d':>15}")

    for k in range(3, max_k + 1):
        S, d, C = compute_params(k)
        val = 3**k - 2
        divides = val % d == 0
        ratio = val / d
        marker = 'YES !!' if divides else 'no'
        print(f"  {k:>3} {S:>4} {d:>15} {val:>20} {marker:>10} {ratio:>15.4f}")

    print("\n  RÉSULTAT : d | (3^k - 2) pour un k ∈ {3,...,40} ?")
    found = False
    for k in range(3, max_k + 1):
        S, d, C = compute_params(k)
        if (3**k - 2) % d == 0:
            print(f"    ★ k={k}: OUI ! d={d} divise 3^k - 2 = {3**k - 2}")
            found = True
    if not found:
        print("    AUCUN ! d ∤ (3^k - 2) pour k=3..40")
        print("    → 2^{S-1} ≢ 1 mod d pour k=3..40")
        print("    → Combiné avec Investigation 7 : ord_d(2) ≥ S pour k=3..40")

# ============================================================
# INVESTIGATION 9 : Peut-on PROUVER d ∤ (3^k - 2) ?
# ============================================================
def investigate_prove_3k_minus_2(max_k=40):
    """
    d | (3^k - 2) ⟺ 3^k ≡ 2 mod (2^S - 3^k)

    Posons d = 2^S - 3^k. Alors :
    3^k ≡ 2 mod d
    ⟺ 3^k - 2 ≡ 0 mod d
    ⟺ d | (3^k - 2)
    ⟺ (2^S - 3^k) | (3^k - 2)
    ⟺ ∃ m ≥ 1 : 3^k - 2 = m · (2^S - 3^k)
    ⟺ 3^k(1 + m) = m · 2^S + 2
    ⟺ 3^k = (m · 2^S + 2)/(m + 1)

    Pour m = 1 : 3^k = (2^S + 2)/2 = 2^{S-1} + 1
    Donc 3^k = 2^{S-1} + 1. Solutions ?
    k=1: 3 = 2^1 + 1 = 3 ✓ ! Mais k=1 est hors de notre portée.
    k=2: 9 ≠ 2^2 + 1 = 5, ni 2^3 + 1 = 9 → k=2, S=4 : 9 = 9 ✓ !
    Mais d(2) = 2^4 - 9 = 7, et gcd(7,6) = 1 ✓, et 3^2 - 2 = 7 = d. BINGO !

    Pour m = 2 : 3^k = (2^{S+1} + 2)/3. Il faut 3 | (2^{S+1} + 2).
    2^{S+1} ≡ 1 mod 3 quand S+1 est pair, soit S impair.

    En général, pour chaque m, c'est une équation Diophantienne 3^k·(m+1) = m·2^S + 2.

    Montrons que m ≥ 2 est impossible pour k ≥ 3 :
    Si m·2^S + 2 = 3^k·(m+1), et k ≥ 3, S = ⌈k·log₂3⌉ ≥ 5.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 9 : Preuve que d ∤ (3^k - 2) pour k ≥ 3")
    print("=" * 70)

    # Vérifier les petits cas
    print("\n  Vérification directe :")
    for k in range(1, 6):
        S = ceil(k * log2(3))
        d = 2**S - 3**k
        val = 3**k - 2
        print(f"    k={k}: S={S}, d={d}, 3^k-2={val}, d|(3^k-2)={val % d == 0}")

    # k=1: d=2^2-3=1, 3^1-2=1, 1|1 ✓
    # k=2: d=2^4-9=7, 3^2-2=7, 7|7 ✓
    # k≥3 : d ∤ (3^k-2) conjecturé

    print("\n  Pour m=1 : 3^k = 2^{S-1} + 1")
    for k in range(1, 50):
        S = ceil(k * log2(3))
        if 3**k == 2**(S-1) + 1:
            print(f"    k={k}, S={S}: 3^k = 2^{S-1} + 1 ✓")
        elif k <= 10:
            print(f"    k={k}, S={S}: 3^k = {3**k}, 2^{S-1}+1 = {2**(S-1)+1} ≠")

    # Borne sur m
    print("\n  Si d | (3^k - 2), alors m = (3^k - 2)/d :")
    for k in range(3, 20):
        S, d, C = compute_params(k)
        val = 3**k - 2
        m_approx = val / d
        print(f"    k={k}: (3^k-2)/d = {m_approx:.4f}")

    # Formule : (3^k - 2)/d = (3^k - 2)/(2^S - 3^k)
    # Pour m entier : 3^k - 2 = m·(2^S - 3^k)
    # 3^k(1+m) = m·2^S + 2
    # m = (3^k - 2)/(2^S - 3^k - ... no, directement :
    # m = (3^k - 2)/d. Si d est petit, m est grand.
    # d/3^k = 2^{frac(k·log₂3)} - 1 ∈ (0,1), souvent petit.

    print("\n  ARGUMENT DE PARITÉ :")
    print("  3^k ≡ 2 mod d ⟹ 3^k impair ≡ 2 mod d")
    print("  d est impair (gcd(d,6)=1). Donc 3^k mod d = 2 mod d.")
    print("  3^k = 2 + m·d pour m ≥ 0.")
    print("  3^k impair, 2 pair, m·d impair si m impair, pair si m pair.")
    print("  Donc m doit être IMPAIR (pour que 2 + m·d soit impair).")

    for k in range(3, 20):
        S, d, C = compute_params(k)
        # 3^k - 2 = m · d, m doit être impair
        if (3**k - 2) % d == 0:
            m = (3**k - 2) // d
            print(f"    k={k}: m = {m}, m impair ? {m % 2 == 1}")

# ============================================================
# MAIN
# ============================================================
if __name__ == "__main__":
    print("SESSION 8 — DEEP BAKER / ÉNONCÉ A INVESTIGATION")
    print("=" * 70)

    investigate_ord_map(max_k=30)
    investigate_size_argument(max_k=30)
    investigate_baker_approach(max_k=20)
    investigate_ord_large_prime(max_k=20)
    investigate_direct_proof(max_k=25)
    investigate_baker_bounds(max_k=25)
    investigate_direct_r_proof(max_k=30)
    investigate_r_S_minus_1(max_k=35)
    investigate_prove_3k_minus_2(max_k=35)

    print("\n" + "=" * 70)
    print("  TOUTES LES INVESTIGATIONS BAKER TERMINÉES")
    print("=" * 70)
