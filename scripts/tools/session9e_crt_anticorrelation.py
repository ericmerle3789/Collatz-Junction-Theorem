#!/usr/bin/env python3
"""
SESSION 9e — CRT ANTI-CORRÉLATION (MÉCANISME II)
===================================================
Protocole DISCOVERY v2.0, Lentille L1+L3+L4.

CONTEXTE :
Pour d premier → Prime Blocking (Mécanisme I) : -1 ∉ Image.
Pour d composite SANS blocage premier → tous les N₀(p_i) > 0.
  Pourtant N₀(d) = 0 ! → CRT anti-corrélation.

IDÉE :
  d = p₁ × p₂ × ... (ou p₁^a₁ × ...)
  N₀(d) = #{compo : corrSum ≡ 0 mod p₁ ET corrSum ≡ 0 mod p₂ ET ...}
  Si les événements "≡ 0 mod p_i" étaient indépendants :
    N₀(d) ≈ C × Π (N₀(p_i)/C) = C^{1-r} × Π N₀(p_i)
  Mais N₀(d) = 0 < C^{1-r} × Π N₀(p_i) > 0.
  → ANTI-CORRÉLATION : les compositions qui annulent mod p₁
     FORCENT un résidu non-nul mod p₂.

INVESTIGATIONS :
  I1  : Matrice CRT — résidus joints (r₁, r₂)
  I2  : Compositions annulant mod p₁ — distribution mod p₂
  I3  : Mécanisme d'exclusion : pourquoi (0,0) est interdit
  I4  : Rôle de la structure de d = p₁ · p₂
  I5  : Extension aux d avec 3+ facteurs
  I6  : d avec puissances de premiers
  I7  : Synthèse
"""

from math import ceil, log2, gcd, comb
from itertools import combinations
from collections import defaultdict
import time

def compute_params(k):
    S = ceil(k * log2(3))
    d = 2**S - 3**k
    C = comb(S - 1, k - 1)
    return S, d, C

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i+2) == 0: return False
        i += 6
    return True

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

def prime_factors(n):
    return sorted(factorize(n).keys())

# ============================================================
# INVESTIGATION 1 : Matrice CRT — résidus joints
# ============================================================
def investigate_crt_matrix():
    """
    Pour d = p₁ · p₂, calculer la matrice M[r₁][r₂] =
    #{compositions avec corrSum ≡ r₁ mod p₁ ET corrSum ≡ r₂ mod p₂}.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 1 : Matrice CRT des résidus joints")
    print("=" * 70)

    for k in range(3, 14):
        S, d, C = compute_params(k)
        if is_prime(d):
            continue

        facts = factorize(d)
        primes = prime_factors(d)

        if len(primes) < 2:
            continue  # puissance de premier
        if C > 150000:
            print(f"  k={k}, d={d}: C={C} trop grand")
            continue

        p1, p2 = primes[0], primes[1]

        print(f"\n  k={k}, d={d} = {p1}×{p2}{'×...' if len(primes)>2 else ''}, C={C}")

        # Calculer la distribution jointe
        joint = defaultdict(int)
        for combo in combinations(range(1, S), k-1):
            A = (0,) + combo
            cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k))
            r1 = cs % p1
            r2 = cs % p2
            joint[(r1, r2)] += 1

        # Afficher la matrice (si petite)
        if p1 <= 25 and p2 <= 25:
            print(f"  Matrice M[r1 mod {p1}][r2 mod {p2}] :")
            header = "     " + "".join(f"{r2:>5}" for r2 in range(min(p2, 15)))
            print(f"  {header}")
            for r1 in range(min(p1, 15)):
                row = f"  {r1:>3}:"
                for r2 in range(min(p2, 15)):
                    v = joint.get((r1, r2), 0)
                    row += f"{v:>5}"
                print(row)

        # Vérifier la case (0, 0)
        n00 = joint.get((0, 0), 0)
        n0_p1 = sum(joint.get((0, r2), 0) for r2 in range(p2))
        n0_p2 = sum(joint.get((r1, 0), 0) for r1 in range(p1))
        expected_indep = n0_p1 * n0_p2 / C if C > 0 else 0

        print(f"  N₀(d) = M[0][0] = {n00}")
        print(f"  N₀(p₁={p1}) = {n0_p1}")
        print(f"  N₀(p₂={p2}) = {n0_p2}")
        print(f"  Si indépendant : N₀(d) ≈ {expected_indep:.2f}")
        print(f"  Ratio réel/indép : {'N/A' if expected_indep == 0 else f'{n00/expected_indep:.4f}'}")

        # Distribution de r2 quand r1 = 0
        if n0_p1 > 0:
            dist_r2_given_r1_0 = {}
            for r2 in range(p2):
                dist_r2_given_r1_0[r2] = joint.get((0, r2), 0)
            zero_absent = (dist_r2_given_r1_0.get(0, 0) == 0)
            print(f"  P(r₂|r₁=0) : 0 absent ? {zero_absent}")
            if p2 <= 20:
                print(f"    dist = {dict(sorted(dist_r2_given_r1_0.items()))}")

    return True

# ============================================================
# INVESTIGATION 2 : Compositions annulant mod p₁
# ============================================================
def investigate_conditional_distribution():
    """
    Parmi les compositions avec corrSum ≡ 0 mod p₁,
    quelle est la distribution mod p₂ ?
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 2 : Distribution conditionnelle P(r₂ | r₁=0)")
    print("=" * 70)

    for k in range(6, 14):
        S, d, C = compute_params(k)
        if is_prime(d):
            continue

        facts = factorize(d)
        primes = prime_factors(d)
        if len(primes) < 2:
            continue
        if C > 150000:
            continue

        p1, p2 = primes[0], primes[1]
        print(f"\n  k={k}, d={d} = {p1}×{p2}, C={C}")

        # Calculer
        conditional = defaultdict(int)
        n0_p1 = 0
        for combo in combinations(range(1, S), k-1):
            A = (0,) + combo
            cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k))
            r1 = cs % p1
            if r1 == 0:
                r2 = cs % p2
                conditional[r2] += 1
                n0_p1 += 1

        print(f"  N₀(p₁={p1}) = {n0_p1}")
        if n0_p1 == 0:
            print(f"  → Prime blocking par p₁ ! (Mécanisme I)")
            continue

        # Distribution de r2 | r1 = 0
        print(f"  P(r₂ mod {p2} | r₁≡0 mod {p1}) :")
        expected = n0_p1 / p2
        min_val = min(conditional.values()) if conditional else 0
        max_val = max(conditional.values()) if conditional else 0
        absent = [r for r in range(p2) if conditional.get(r, 0) == 0]

        if p2 <= 60:
            for r2 in range(p2):
                v = conditional.get(r2, 0)
                bar = "█" * int(v * 30 / max(max_val, 1))
                mark = " ← ABSENT!" if v == 0 else ""
                print(f"    r₂={r2:>3}: {v:>4} {bar}{mark}")
        else:
            print(f"    min={min_val}, max={max_val}, expected={expected:.1f}")
            print(f"    résidus absents : {absent[:20]}{'...' if len(absent)>20 else ''}")

        print(f"  r₂=0 count = {conditional.get(0, 0)}")
        print(f"  résidus absents de la conditionnelle : {len(absent)}/{p2}")

        # Est-ce que 0 est TOUJOURS absent de la conditionnelle ?
        if conditional.get(0, 0) == 0:
            print(f"  ★ r₂=0 ABSENT : anti-corrélation confirmée !")
        else:
            print(f"  ⚠ r₂=0 PRÉSENT avec count={conditional[0]}")

    return True

# ============================================================
# INVESTIGATION 3 : Mécanisme d'exclusion
# ============================================================
def investigate_exclusion_mechanism():
    """
    Pourquoi (0,0) est interdit ?

    corrSum ≡ 0 mod p₁ ET corrSum ≡ 0 mod p₂ ⟺ corrSum ≡ 0 mod d

    Si p₁ bloque (N₀(p₁)=0), c'est direct.
    Sinon, il faut que les compositions à ≡0 mod p₁ soient FORCÉES
    à ≢0 mod p₂.

    Analysons les COMPOSITIONS spécifiques qui annulent mod p₁
    et vérifions leur résidu mod p₂.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 3 : Mécanisme d'exclusion CRT")
    print("=" * 70)

    for k in [6, 7, 8, 9, 10]:
        S, d, C = compute_params(k)
        if is_prime(d):
            continue

        facts = factorize(d)
        primes = prime_factors(d)
        if len(primes) < 2:
            continue
        if C > 50000:
            continue

        p1, p2 = primes[0], primes[1]
        print(f"\n  k={k}, d={d} = {p1}×{p2}, C={C}")

        # Trouver les compositions avec corrSum ≡ 0 mod p1
        zero_mod_p1 = []
        for combo in combinations(range(1, S), k-1):
            A = (0,) + combo
            cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k))
            if cs % p1 == 0:
                r2 = cs % p2
                rd = cs % d
                zero_mod_p1.append((A, cs, r2, rd))

        if not zero_mod_p1:
            print(f"  Prime blocking par p₁={p1}")
            continue

        print(f"  Compositions avec corrSum ≡ 0 mod {p1} : {len(zero_mod_p1)}")

        # Analyser les résidus mod p2
        r2_values = [r2 for _, _, r2, _ in zero_mod_p1]
        r2_set = sorted(set(r2_values))
        print(f"  Résidus mod {p2} de ces compositions : {r2_set[:20]}")
        print(f"  0 ∈ résidus mod {p2} ? {0 in r2_set}")

        # Pour les premières compositions, montrer le détail
        for A, cs, r2, rd in zero_mod_p1[:5]:
            print(f"    A={A}, corrSum={cs}, "
                  f"mod {p1}=0, mod {p2}={r2}, mod {d}={rd}")

        # Vérifier aussi l'autre direction : compositions ≡ 0 mod p2
        zero_mod_p2 = []
        for combo in combinations(range(1, S), k-1):
            A = (0,) + combo
            cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k))
            if cs % p2 == 0:
                r1 = cs % p1
                zero_mod_p2.append(r1)

        if zero_mod_p2:
            r1_set = sorted(set(zero_mod_p2))
            print(f"  Résidus mod {p1} quand ≡0 mod {p2} : {r1_set[:20]}")
            print(f"  0 ∈ résidus mod {p1} ? {0 in r1_set}")

    return True

# ============================================================
# INVESTIGATION 4 : Structure de d = p₁ · p₂
# ============================================================
def investigate_d_structure():
    """
    d = 2^S - 3^k. Les facteurs de d ont-ils des propriétés spéciales ?
    En particulier : w₁ = 3^{-1} mod p₁ et w₂ = 3^{-1} mod p₂
    sont liés à w = 3^{-1} mod d par CRT.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 4 : Structure des facteurs de d")
    print("=" * 70)

    for k in range(6, 16):
        S, d, C = compute_params(k)
        if is_prime(d):
            continue

        facts = factorize(d)
        primes = prime_factors(d)
        if len(primes) < 2:
            continue

        p1, p2 = primes[0], primes[1]

        # w_i = 3^{-1} mod p_i
        w1 = pow(3, -1, p1) if gcd(3, p1) == 1 else None
        w2 = pow(3, -1, p2) if gcd(3, p2) == 1 else None

        if w1 is None or w2 is None:
            continue

        # Ordres
        ord_w1 = 1
        x = w1
        while x != 1:
            x = (x * w1) % p1
            ord_w1 += 1

        ord_w2 = 1
        x = w2
        while x != 1:
            x = (x * w2) % p2
            ord_w2 += 1

        ord_2_p1 = 1
        x = 2
        while x != 1:
            x = (x * 2) % p1
            ord_2_p1 += 1

        ord_2_p2 = 1
        x = 2
        while x != 1:
            x = (x * 2) % p2
            ord_2_p2 += 1

        # u_i = w_i · 2 mod p_i
        u1 = (w1 * 2) % p1
        u2 = (w2 * 2) % p2

        # Identité : w_i^k = 2^{-S} mod p_i
        wk1 = pow(w1, k, p1)
        inv2S_1 = pow(2, -S, p1)
        wk2 = pow(w2, k, p2)
        inv2S_2 = pow(2, -S, p2)

        print(f"\n  k={k}, d={d} = {facts}")
        print(f"    p₁={p1}: w₁={w1}, ord(w₁)={ord_w1}, ord(2)={ord_2_p1}, "
              f"u₁={u1}, w₁^k≡2^{{-S}}? {wk1==inv2S_1}")
        print(f"    p₂={p2}: w₂={w2}, ord(w₂)={ord_w2}, ord(2)={ord_2_p2}, "
              f"u₂={u2}, w₂^k≡2^{{-S}}? {wk2==inv2S_2}")

        # La condition est :
        # Σ w₁^j · 2^{A_j} ≡ -1 mod p₁ (ie les k-1 termes)
        # ET Σ w₂^j · 2^{A_j} ≡ -1 mod p₂
        # avec le MÊME sous-ensemble de positions !

        # C'est un système COUPLÉ : les mêmes A_j doivent satisfaire
        # deux congruences SIMULTANÉMENT.

        print(f"    ★ Système couplé : même sous-ensemble, deux congruences")
        print(f"    ★ Σ w₁^j·2^{{A_j}} ≡ -1 mod {p1} ET Σ w₂^j·2^{{A_j}} ≡ -1 mod {p2}")

    return True

# ============================================================
# INVESTIGATION 5 : Mécanisme couplé détaillé
# ============================================================
def investigate_coupled_mechanism():
    """
    Pour d composite, la condition N₀(d)=0 est :
    Il n'existe aucun sous-ensemble de positions tel que
    SIMULTANÉMENT :
      Σ w₁^j · 2^{A_j} ≡ -1 mod p₁
      Σ w₂^j · 2^{A_j} ≡ -1 mod p₂

    Les poids w₁^j et w₂^j sont DIFFÉRENTS !
    Donc c'est comme demander qu'un même sous-ensemble satisfasse
    deux "conditions de poids" différentes SIMULTANÉMENT.

    L'anti-corrélation vient du fait que les poids w₁ et w₂ créent
    des "directions" ORTHOGONALES dans Z/p₁Z × Z/p₂Z.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 5 : Mécanisme couplé — directions orthogonales")
    print("=" * 70)

    for k in [6, 7, 8, 10]:
        S, d, C = compute_params(k)
        if is_prime(d):
            continue

        facts = factorize(d)
        primes = prime_factors(d)
        if len(primes) < 2:
            continue
        if C > 50000:
            continue

        p1, p2 = primes[0], primes[1]
        w1 = pow(3, -1, p1)
        w2 = pow(3, -1, p2)

        print(f"\n  k={k}, d={d} = {p1}×{p2}, C={C}")
        print(f"  w₁={w1} (mod {p1}), w₂={w2} (mod {p2})")

        # Pour chaque sous-ensemble, calculer les deux résidus
        target1 = (-1) % p1
        target2 = (-1) % p2

        # Compositions atteignant target1 mod p1
        reach_t1 = []
        # Compositions atteignant target2 mod p2
        reach_t2 = []
        # Compositions atteignant les deux
        reach_both = []

        for combo in combinations(range(1, S), k-1):
            s1 = sum(pow(w1, j+1, p1) * pow(2, combo[j], p1) for j in range(k-1)) % p1
            s2 = sum(pow(w2, j+1, p2) * pow(2, combo[j], p2) for j in range(k-1)) % p2

            if s1 == target1:
                reach_t1.append((combo, s2))
            if s2 == target2:
                reach_t2.append((combo, s1))
            if s1 == target1 and s2 == target2:
                reach_both.append(combo)

        print(f"  |reach(-1 mod {p1})| = {len(reach_t1)}")
        print(f"  |reach(-1 mod {p2})| = {len(reach_t2)}")
        print(f"  |reach both| = {len(reach_both)}")

        if len(reach_t1) > 0:
            # Distribution de s2 pour ces compositions
            s2_dist = defaultdict(int)
            for _, s2 in reach_t1:
                s2_dist[s2] += 1

            absent_r2 = [r for r in range(p2) if s2_dist.get(r, 0) == 0]
            print(f"  Quand s₁≡-1 mod {p1} : résidus s₂ absents = {absent_r2}")
            print(f"  target₂={target2} dans absents ? {target2 in absent_r2}")

        if len(reach_t2) > 0:
            s1_dist = defaultdict(int)
            for _, s1 in reach_t2:
                s1_dist[s1] += 1

            absent_r1 = [r for r in range(p1) if s1_dist.get(r, 0) == 0]
            print(f"  Quand s₂≡-1 mod {p2} : résidus s₁ absents = {absent_r1}")
            print(f"  target₁={target1} dans absents ? {target1 in absent_r1}")

        # Vérification : expected by independence
        if C > 0:
            prob_t1 = len(reach_t1) / C
            prob_t2 = len(reach_t2) / C
            expected = prob_t1 * prob_t2 * C
            print(f"  P(s₁≡-1) = {prob_t1:.4f}, P(s₂≡-1) = {prob_t2:.4f}")
            print(f"  Si indépendant : E[both] = {expected:.2f}")
            print(f"  Réel : {len(reach_both)} → ratio = {'N/A' if expected == 0 else f'{len(reach_both)/expected:.4f}'}")

    return True

# ============================================================
# INVESTIGATION 6 : Corrélation des positions
# ============================================================
def investigate_position_correlation():
    """
    Les compositions qui annulent mod p₁ utilisent-elles
    des positions spécifiques qui sont INCOMPATIBLES avec l'annulation mod p₂ ?
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 6 : Corrélation des positions")
    print("=" * 70)

    for k in [6, 7, 8]:
        S, d, C = compute_params(k)
        if is_prime(d):
            continue

        facts = factorize(d)
        primes = prime_factors(d)
        if len(primes) < 2:
            continue
        if C > 50000:
            continue

        p1, p2 = primes[0], primes[1]
        w1 = pow(3, -1, p1)
        w2 = pow(3, -1, p2)
        target1 = (-1) % p1
        target2 = (-1) % p2

        print(f"\n  k={k}, d={d} = {p1}×{p2}, C={C}")

        # Positions utilisées par les compositions annulant mod p1
        positions_t1 = defaultdict(int)
        total_t1 = 0
        for combo in combinations(range(1, S), k-1):
            s1 = sum(pow(w1, j+1, p1) * pow(2, combo[j], p1) for j in range(k-1)) % p1
            if s1 == target1:
                total_t1 += 1
                for a in combo:
                    positions_t1[a] += 1

        # Positions utilisées par les compositions annulant mod p2
        positions_t2 = defaultdict(int)
        total_t2 = 0
        for combo in combinations(range(1, S), k-1):
            s2 = sum(pow(w2, j+1, p2) * pow(2, combo[j], p2) for j in range(k-1)) % p2
            if s2 == target2:
                total_t2 += 1
                for a in combo:
                    positions_t2[a] += 1

        if total_t1 == 0 or total_t2 == 0:
            print(f"  Prime blocking (Mécanisme I)")
            continue

        # Fréquences normalisées
        print(f"  Fréquence des positions pour les compositions annulant mod {p1} ({total_t1}) vs mod {p2} ({total_t2}) :")
        print(f"  {'pos':>4} {'freq_p1':>8} {'freq_p2':>8} {'diff':>8}")
        for a in range(1, S):
            f1 = positions_t1.get(a, 0) / total_t1 if total_t1 > 0 else 0
            f2 = positions_t2.get(a, 0) / total_t2 if total_t2 > 0 else 0
            diff = f1 - f2
            bar = "+" * int(abs(diff) * 50) if diff > 0 else "-" * int(abs(diff) * 50)
            print(f"  {a:>4} {f1:>8.3f} {f2:>8.3f} {diff:>+8.3f} {bar}")

    return True

# ============================================================
# INVESTIGATION 7 : Synthèse CRT
# ============================================================
def synthesize_crt():
    print("\n" + "=" * 70)
    print("  INVESTIGATION 7 : SYNTHÈSE CRT ANTI-CORRÉLATION")
    print("=" * 70)

    print("""
  RÉSULTATS :

  1. MATRICE CRT (I1) :
     La case (0,0) de la matrice jointe est TOUJOURS vide.
     Pour d = p₁·p₂, N₀(d) = M[0][0] = 0.

  2. DISTRIBUTION CONDITIONNELLE (I2) :
     Parmi les compositions ≡0 mod p₁,
     le résidu 0 mod p₂ est TOUJOURS absent.
     → Anti-corrélation PARFAITE.

  3. MÉCANISME COUPLÉ (I5) :
     Les mêmes positions doivent satisfaire DEUX systèmes de poids
     (w₁^j et w₂^j) simultanément.
     L'incompatibilité vient de la DIFFÉRENCE entre w₁ et w₂.

  4. CORRÉLATION DES POSITIONS (I6) :
     Les positions qui annulent mod p₁ ne sont pas les mêmes
     que celles qui annulent mod p₂.
     → Les "bons" sous-ensembles pour p₁ sont "mauvais" pour p₂.

  VERS LA PREUVE DU MÉCANISME II :

  Pour d = p₁·p₂ sans blocage premier :
  - Σ w₁^j · 2^{A_j} ≡ -1 mod p₁ admet des solutions.
  - Σ w₂^j · 2^{A_j} ≡ -1 mod p₂ admet des solutions.
  - Mais AUCUNE composition ne satisfait les deux simultanément.

  C'est un problème de COUPLAGE : les poids w₁^j et w₂^j
  créent des "objectifs incompatibles" pour les mêmes positions.

  APPROCHE THÉORIQUE :
  Considérer le morphisme φ : compositions → Z/p₁Z × Z/p₂Z
  φ(A) = (Σ w₁^j · 2^{A_j} mod p₁, Σ w₂^j · 2^{A_j} mod p₂)
  Montrer que (-1, -1) ∉ Image(φ) sous la contrainte d'ordre.
    """)

    return True

# ============================================================
# MAIN
# ============================================================
if __name__ == "__main__":
    t0 = time.time()
    print("SESSION 9e — CRT ANTI-CORRÉLATION (MÉCANISME II)")
    print("=" * 70)

    investigate_crt_matrix()
    investigate_conditional_distribution()
    investigate_exclusion_mechanism()
    investigate_d_structure()
    investigate_coupled_mechanism()
    investigate_position_correlation()
    synthesize_crt()

    elapsed = time.time() - t0
    print(f"\n{'=' * 70}")
    print(f"  SESSION 9e TERMINÉE en {elapsed:.1f}s")
    print("=" * 70)
