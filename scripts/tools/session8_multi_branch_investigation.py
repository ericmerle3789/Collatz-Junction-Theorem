#!/usr/bin/env python3
"""
SESSION 8 — Investigation Multi-Branche
========================================
Protocole DISCOVERY v2.0 : Explorer TOUTES les pistes ouvertes.
Pour chaque piste : tester, analyser POURQUOI ça marche/échoue,
et identifier ce que ça OUVRE comme nouvelle piste.

BRANCHES INVESTIGÉES :
  B1. Approche algébrique h = 2/3 mod d (Front B du protocole)
  B2. Baker / Énoncé A (formes linéaires en logarithmes)
  B3. CRT incompatibilité — formalisation
  B4. Induction sur k (ou sur structure de d)
  B5. p-adique / valuations
  B6. Coding theory (corrSum comme syndrome)
"""

from math import ceil, log2, gcd, comb, log, factorial
from itertools import combinations
from collections import defaultdict
import sys

def compute_params(k):
    S = ceil(k * log2(3))
    d = 2**S - 3**k
    C = comb(S - 1, k - 1)
    return S, d, C

def enumerate_corrsum(k, S, d):
    """Retourne liste de (composition, corrSum mod d)."""
    results = []
    for combo in combinations(range(1, S), k - 1):
        A = (0,) + combo
        cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k))
        results.append((A, cs % d))
    return results

def modinv(a, m):
    """Inverse modulaire via pow."""
    return pow(a, -1, m) if gcd(a, m) == 1 else None

def factorize(n):
    """Factorisation naive."""
    factors = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors

def ord_mod(a, m):
    """Ordre multiplicatif de a mod m (optimisé via factorisation de φ(m))."""
    if gcd(a, m) != 1:
        return None
    # Calculer φ(m)
    phi = 1
    for p, e in factorize(m).items():
        phi *= (p - 1) * p**(e - 1)
    # L'ordre divise φ(m). Tester les diviseurs de φ(m) en ordre croissant.
    order = phi
    for p, e in factorize(phi).items():
        for _ in range(e):
            if pow(a, order // p, m) == 1:
                order //= p
            else:
                break
    return order

# ==============================================================
print("=" * 70)
print("  BRANCHE B1 : APPROCHE ALGÉBRIQUE h = 2/3 mod d")
print("=" * 70)
# ==============================================================
# PRÉ-ENGAGEMENT :
#   Hypothèse : h = 2·3^{-1} mod d a des propriétés spéciales
#   Succès : trouver une identité ou borne exploitable
#   Échec : h n'a pas de structure particulière au-delà de l'ordre

print("\n--- B1.1 : Propriétés de h = 2/3 mod d ---")
for k in range(3, 16):
    S, d, C = compute_params(k)
    inv3 = modinv(3, d)
    h = (2 * inv3) % d
    ord_h = ord_mod(h, d)
    ord_2 = ord_mod(2, d)
    ord_3 = ord_mod(3, d)

    # corrSum = 3^{k-1} * (1 + h^{p1} + h^{p1}·h^{p2} + ...)
    # NON, c'est plus subtil. En fait :
    # corrSum = Σ 3^{k-1-j} · 2^{A_j} = 3^{k-1} · Σ (2/3)^j · 2^{A_j - j·?}
    # Reformulation correcte :
    # corrSum = 3^{k-1} · Σ_{j=0}^{k-1} h_j  où h_j = (2/3)^j · (2^{A_j}/2^j) ... NON
    #
    # La bonne reformulation : diviser par 3^{k-1}
    # corrSum / 3^{k-1} = Σ (2/3)^j · 2^{A_j - j} ... NON
    #
    # Simplement : corrSum = Σ 3^{k-1-j} · 2^{A_j}
    # En multipliant par (3^{-1})^{k-1} mod d :
    # corrSum · 3^{-(k-1)} = Σ (3^{-1})^j · 2^{A_j}  = Σ (3^{-j}) · 2^{A_j}
    # = Σ h^j · 2^{A_j - j} ... NON, h = 2/3.
    # (3^{-1})^j · 2^{A_j} = (h/2)^j · 2^{A_j} = h^j · 2^{A_j - j}

    # Soit w = 3^{-1} mod d. Alors :
    # corrSum · w^{k-1} = Σ w^j · 2^{A_j} = Σ (w · 2^{A_j/1})
    # = Σ_{j=0}^{k-1} w^j · 2^{A_j}  (mod d)
    # avec w = 3^{-1} mod d

    # h = 2w = 2/3 mod d
    # w^j · 2^{A_j} = (h/2)^j · 2^{A_j} = h^j · 2^{A_j - j}

    # FORMULE PROPRE :
    # corrSum · w^{k-1} ≡ Σ_{j=0}^{k-1} w^j · 2^{A_j}  (mod d)
    # = 2^0 + w·2^{A_1} + w²·2^{A_2} + ... + w^{k-1}·2^{A_{k-1}}
    # = 1 + Σ_{j=1}^{k-1} w^j · 2^{A_j}

    # N₀(d) = 0 ⟺ Σ w^j · 2^{A_j} ≢ 0 (mod d) pour tout A ordonné.

    # C'est une SOMME PONDÉRÉE de puissances de 2 avec poids w^j.
    # Les poids sont dans le sous-groupe ⟨w⟩ = ⟨3^{-1}⟩ = ⟨3⟩^{-1}.

    # FAIT : w^k = 3^{-k} = (2^S - d)^{-1} · 2^S · 3^{-k} ... compliqué.
    # Plus simple : 3^k ≡ 2^S (mod d), donc w^k = 3^{-k} = 2^{-S} (mod d).

    wk = pow(3, -k, d)
    two_neg_S = pow(2, -S, d) if gcd(2, d) == 1 else None

    print(f"  k={k:2d}: h={h}, ord(h)={ord_h}, ord(2)={ord_2}, ord(3)={ord_3}, "
          f"w^k={wk}, 2^(-S)={two_neg_S}, match={'✓' if wk == two_neg_S else '✗'}")

print("\n--- B1.2 : Reformulation en somme pondérée ---")
print("  corrSum · 3^{-(k-1)} ≡ 1 + Σ_{j=1}^{k-1} 3^{-j} · 2^{A_j}  (mod d)")
print("  Posons w = 3^{-1} mod d. Alors :")
print("  corrSum ≡ 0 (mod d) ⟺ 1 + Σ w^j · 2^{A_j} ≡ 0 (mod d)")
print("  ⟺ Σ w^j · 2^{A_j} ≡ -1 (mod d)   ← CIBLE ALTERNATIVE")
print()
print("  Identité clé : w^k = 2^{-S} mod d (car 3^k = 2^S mod d)")
print("  Les poids w^j forment une suite géométrique, MAIS les 2^{A_j} sont")
print("  contraints à être des puissances de 2 croissantes.")
print()

# Vérifier la reformulation
for k in [5, 6, 7]:
    S, d, C = compute_params(k)
    w = pow(3, -1, d)
    data = enumerate_corrsum(k, S, d)

    # Transformer en format w^j · 2^{A_j}
    target = (-1) % d  # = d - 1
    reformulated_residues = []
    for A, cs_mod_d in data:
        # Calculer Σ w^j · 2^{A_j} mod d
        s = sum(pow(w, j, d) * pow(2, A[j]) % d for j in range(k)) % d
        reformulated_residues.append(s)

    n_target = reformulated_residues.count(target)
    print(f"  k={k}: target d-1={target}, atteint {n_target} fois (doit être 0) "
          f"{'✓' if n_target == 0 else '✗ BUG!'}")

print("\n--- B1.3 : Structure du groupe ⟨w⟩ × ⟨2⟩ dans (Z/dZ)* ---")
for k in [5, 6, 7, 8]:
    S, d, C = compute_params(k)
    w = pow(3, -1, d)
    ord_w = ord_mod(w, d)
    ord_2_d = ord_mod(2, d)

    # Le sous-groupe engendré par w et 2
    group_w = set()
    x = 1
    for i in range(ord_w):
        group_w.add(x)
        x = (x * w) % d

    group_2 = set()
    x = 1
    for i in range(ord_2_d):
        group_2.add(x)
        x = (x * 2) % d

    # Intersection et produit
    intersection = group_w & group_2

    # Engendré par w et 2
    group_w2 = set()
    for a in group_w:
        for b in group_2:
            group_w2.add((a * b) % d)

    # Euler's totient
    phi_d = 1
    for p, e in factorize(d).items():
        phi_d *= (p - 1) * p**(e - 1)

    print(f"  k={k}: |⟨w⟩|={len(group_w)}, |⟨2⟩|={len(group_2)}, "
          f"|⟨w⟩∩⟨2⟩|={len(intersection)}, |⟨w,2⟩|={len(group_w2)}, "
          f"φ(d)={phi_d}, ratio={len(group_w2)/phi_d:.3f}")

# ==============================================================
print("\n" + "=" * 70)
print("  BRANCHE B2 : BAKER / ÉNONCÉ A")
print("=" * 70)
# ==============================================================
# PRÉ-ENGAGEMENT :
#   Hypothèse : |3^k - 2^s| ≥ d pour tout s ∈ {1,...,S-1}, k ≥ 4
#   Succès : trouver une borne effective via Baker
#   Échec : la borne Baker est trop faible pour les petits k

print("\n--- B2.1 : Near-misses |3^k - 2^s| / d ---")
for k in range(3, 25):
    S, d, C = compute_params(k)
    theta = S - k * log2(3)

    min_ratio = float('inf')
    best_s = -1
    for s in range(1, S):
        diff = abs(3**k - 2**s)
        ratio = diff / d
        if ratio < min_ratio:
            min_ratio = ratio
            best_s = s

    status = "DANGER" if min_ratio < 1 else "OK"
    print(f"  k={k:2d}: θ={theta:.4f}, min |3^k-2^s|/d = {min_ratio:.4f} "
          f"(s={best_s}), d={d}, [{status}]")

print("\n--- B2.2 : Analyse de Pillai : d | (3^k - 2^s) ? ---")
print("  Question : existe-t-il s ∈ {1,...,S-1} tel que d | (3^k - 2^s) ?")
print("  Reformulation : 3^k ≡ 2^s (mod d). Or 3^k ≡ 2^S (mod d).")
print("  Donc : 2^S ≡ 2^s (mod d) ⟺ 2^s·(2^{S-s} - 1) ≡ 0 (mod d)")
print("  Comme gcd(2,d)=1 : d | (2^{S-s} - 1) ⟺ ord_d(2) | (S-s)")
print()

for k in range(4, 20):
    S, d, C = compute_params(k)
    ord_2_d = ord_mod(2, d)

    # Chercher s tel que ord_d(2) | (S - s) et 1 ≤ s ≤ S-1
    # i.e. S - s ∈ {1,...,S-1} et ord_d(2) | (S-s)
    # i.e. S-s = m·ord_d(2) pour m ≥ 1
    # i.e. s = S - m·ord_d(2)

    solutions = []
    m = 1
    while True:
        s = S - m * ord_2_d
        if s < 1:
            break
        if s <= S - 1:
            solutions.append(s)
        m += 1

    print(f"  k={k:2d}: ord_d(2)={ord_2_d:5d}, S={S:2d}, "
          f"solutions s: {solutions if solutions else 'AUCUNE ✓'}")

print("\n--- B2.3 : Pourquoi ord_d(2) > S-1 ? Pattern dans ord_d(2)/S ---")
for k in range(3, 30):
    S, d, C = compute_params(k)
    ord_2_d = ord_mod(2, d)
    ratio = ord_2_d / S
    print(f"  k={k:2d}: S={S:3d}, ord_d(2)={ord_2_d:6d}, ord/S={ratio:.2f}, "
          f"ord/(S-1)={ord_2_d/(S-1):.2f}")

# ==============================================================
print("\n" + "=" * 70)
print("  BRANCHE B3 : CRT INCOMPATIBILITÉ — FORMALISATION")
print("=" * 70)
# ==============================================================

print("\n--- B3.1 : Mécanisme par k ---")
for k in range(5, 16):
    S, d, C = compute_params(k)
    factors = factorize(d)
    primes = list(factors.keys())

    if len(primes) == 1:
        p = primes[0]
        e = factors[p]
        if e == 1:
            # d est premier
            data = enumerate_corrsum(k, S, d) if k <= 12 else []
            n0_d = sum(1 for _, r in data if r == 0) if data else "?"
            print(f"  k={k:2d}: d={d} PREMIER → N₀(d)={n0_d} [PRIME BLOCK si 0]")
        else:
            print(f"  k={k:2d}: d={d} = {p}^{e} puissance de premier")
    else:
        # d composé : analyser N₀(p) pour chaque p | d
        info_parts = []
        for p in primes:
            if k <= 12:
                data_p = []
                for combo in combinations(range(1, S), k-1):
                    A = (0,) + combo
                    cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k))
                    data_p.append(cs % p)
                n0_p = data_p.count(0)
                info_parts.append(f"N₀({p})={n0_p}")
            else:
                info_parts.append(f"p={p}")

        mechanism = "PRIME BLOCK" if any("=0" in x for x in info_parts) else "CRT INCOMPAT"
        print(f"  k={k:2d}: d={d} = {'×'.join(str(p) for p in primes)} → "
              f"{', '.join(info_parts)} [{mechanism}]")

print("\n--- B3.2 : Analyse CRT détaillée pour k=6 (d=5×59) ---")
k = 6
S, d, C = compute_params(k)
data = enumerate_corrsum(k, S, d)

# Résidus mod 5 et mod 59
pairs = [(cs % 5, cs % 59) for _, cs in data]
pair_counts = defaultdict(int)
for p in pairs:
    pair_counts[p] += 1

# Quelles paires (a, b) apparaissent ?
print(f"  d = 5 × 59 = {d}, C = {C}")
print(f"  Résidus mod 5 atteints : {sorted(set(p[0] for p in pairs))}")
print(f"  Résidus mod 59 atteints : {sorted(set(p[1] for p in pairs))}")

# Paire (0, 0) ?
print(f"  Paire (0, 0) : {pair_counts.get((0, 0), 0)} occurrences")
print(f"  Paire (0, *) : {sum(v for (a,b), v in pair_counts.items() if a == 0)}")
print(f"  Paire (*, 0) : {sum(v for (a,b), v in pair_counts.items() if b == 0)}")

# Quelles paires (0, b) existent ?
zero_5 = [(a, b) for (a, b) in pair_counts if a == 0]
zero_59 = [(a, b) for (a, b) in pair_counts if b == 0]
print(f"  Paires (0, b) : {zero_5}")
print(f"  Paires (a, 0) : {zero_59}")

# POURQUOI (0,0) est absent ?
# Si a ≡ 0 mod 5, les b possibles sont...
b_when_a0 = set(b for (a, b) in pairs if a == 0)
a_when_b0 = set(a for (a, b) in pairs if b == 0)
print(f"  Quand corrSum ≡ 0 mod 5 : résidus mod 59 = {sorted(b_when_a0)}")
print(f"  Quand corrSum ≡ 0 mod 59 : résidus mod 5 = {sorted(a_when_b0)}")
print(f"  → 0 ∈ b_when_a0 ? {'OUI ⚠️' if 0 in b_when_a0 else 'NON ✓'}")
print(f"  → 0 ∈ a_when_b0 ? {'OUI ⚠️' if 0 in a_when_b0 else 'NON ✓'}")

# ==============================================================
print("\n" + "=" * 70)
print("  BRANCHE B4 : INDUCTION SUR k")
print("=" * 70)
# ==============================================================

print("\n--- B4.1 : Relation entre d(k) et d(k+1) ---")
for k in range(3, 20):
    S_k, d_k, C_k = compute_params(k)
    S_k1, d_k1, C_k1 = compute_params(k + 1)

    # d(k+1) = 2^{S(k+1)} - 3^{k+1}
    # = 2^{S(k+1)} - 3·3^k
    # = 2^{S(k+1)} - 3·(2^{S(k)} - d(k))
    # = 2^{S(k+1)} - 3·2^{S(k)} + 3·d(k)

    delta_S = S_k1 - S_k  # = 1 ou 2
    d_k1_formula = 2**S_k1 - 3 * 2**S_k + 3 * d_k

    print(f"  k={k:2d}: d(k)={d_k:10d}, d(k+1)={d_k1:10d}, "
          f"ΔS={delta_S}, "
          f"d(k+1) = 2^{S_k1}-3·2^{S_k}+3·d(k) = {d_k1_formula} "
          f"{'✓' if d_k1_formula == d_k1 else '✗'}")

print("\n--- B4.2 : Si ΔS=2, alors d(k+1) = 4·d(k) - d(k)_corr ---")
print("  Si S(k+1) = S(k) + 2 :")
print("    d(k+1) = 2^{S+2} - 3·2^S + 3·d(k) = 4·2^S - 3·2^S + 3d = 2^S + 3d")
print("    = (d + 3^k) + 3d = 4d + 3^k")
print()
print("  Si S(k+1) = S(k) + 1 :")
print("    d(k+1) = 2^{S+1} - 3·2^S + 3·d(k) = 2·2^S - 3·2^S + 3d = -2^S + 3d")
print("    = 3d - (d + 3^k) = 2d - 3^k")
print()

for k in range(3, 20):
    S_k, d_k, C_k = compute_params(k)
    S_k1, d_k1, C_k1 = compute_params(k + 1)
    delta_S = S_k1 - S_k

    if delta_S == 2:
        formula = 4 * d_k + 3**k
    else:
        formula = 2 * d_k - 3**k

    print(f"  k={k:2d}: ΔS={delta_S}, d(k+1) = "
          f"{'4d+3^k' if delta_S == 2 else '2d-3^k'} = {formula} "
          f"{'✓' if formula == d_k1 else '✗'}")

# ==============================================================
print("\n" + "=" * 70)
print("  BRANCHE B5 : APPROCHE p-ADIQUE / VALUATIONS")
print("=" * 70)
# ==============================================================

print("\n--- B5.1 : Valuations p-adiques de d pour chaque premier p | d ---")
for k in range(5, 16):
    S, d, C = compute_params(k)
    factors = factorize(d)

    # Pour chaque p | d, la valuation v_p(d)
    val_info = []
    for p, e in sorted(factors.items()):
        val_info.append(f"v_{p}(d)={e}")

    print(f"  k={k:2d}: d={d:10d} = {'·'.join(f'{p}^{e}' if e > 1 else str(p) for p, e in sorted(factors.items()))}"
          f"  {', '.join(val_info)}")

print("\n--- B5.2 : Valuations p-adiques de corrSum ---")
print("  Pour chaque p | d, analyser v_p(corrSum) pour les compositions")
for k in [5, 6, 7]:
    S, d, C = compute_params(k)
    factors = factorize(d)
    data = enumerate_corrsum(k, S, d)

    print(f"\n  k={k}, d={d}, facteurs: {dict(factors)}")

    for p, e in sorted(factors.items()):
        # Calculer v_p(corrSum) pour chaque composition
        val_counts = defaultdict(int)
        for A, cs_mod_d in data:
            cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k))
            v = 0
            temp = cs
            while temp % p == 0 and temp > 0:
                v += 1
                temp //= p
            val_counts[v] += 1

        # Si corrSum ≡ 0 mod d = ... mod p^e, il faudrait v_p(corrSum) ≥ e
        print(f"    p={p}: valuations = {dict(sorted(val_counts.items()))}")
        max_val = max(val_counts.keys())
        need_val = e
        has_enough = any(v >= need_val for v in val_counts.keys())
        print(f"    → besoin v_p ≥ {need_val}, max obtenu = {max_val}, "
              f"faisable = {'OUI' if has_enough else 'NON ← BLOCAGE!'}")

# ==============================================================
print("\n" + "=" * 70)
print("  BRANCHE B6 : CODING THEORY — corrSum COMME SYNDROME")
print("=" * 70)
# ==============================================================

print("\n--- B6.1 : Matrice de parité implicite ---")
print("  corrSum(A) = Σ 3^{k-1-j} · 2^{A_j} = [3^{k-1}, 3^{k-2}, ..., 1] · [2^{A_0}, ..., 2^{A_{k-1}}]^T")
print("  C'est le produit H·x où :")
print("    H = ligne [3^{k-1}, 3^{k-2}, ..., 3, 1] (taille 1×k)")
print("    x = colonne [2^{A_0}, 2^{A_1}, ..., 2^{A_{k-1}}] (taille k×1)")
print("  N₀(d) = 0 signifie que le syndrome H·x ≢ 0 (mod d) pour tout x valide.")
print()

for k in [5, 6, 7]:
    S, d, C = compute_params(k)

    # Les "mots" possibles : x_j = 2^{A_j} avec 0 = A_0 < A_1 < ... < A_{k-1} < S
    # Ce sont des vecteurs dans (Z/dZ)^k

    # La "matrice de parité" : H = [3^{k-1}, 3^{k-2}, ..., 1] en ligne
    H = [pow(3, k-1-j, d) for j in range(k)]

    # Image de H·x : quels résidus sont atteints ?
    data = enumerate_corrsum(k, S, d)
    residues = set(r for _, r in data)
    n_residues = len(residues)

    # Distance minimale au "mot de code" 0
    # = min |{j : x_j ≠ 0}| pour x tel que H·x ≡ 0 (mod d)
    # Mais tous les x_j = 2^{A_j} ≠ 0, donc le "poids" est toujours k.
    # Le syndrome est JAMAIS 0.

    print(f"  k={k}: H = {H} (mod {d})")
    print(f"    |Im(H·x)| = {n_residues}/{d} (couverture {n_residues/d:.1%})")
    print(f"    0 ∈ Im ? {'OUI ⚠️' if 0 in residues else 'NON ✓'}")

    # Rangs : si on considère les x_j comme variables libres dans Z/dZ,
    # quelle est la dimension de l'image ?
    # Puisque H est 1×k, l'image a dimension ≤ 1 (c'est Z/dZ ou un sous-groupe)
    # MAIS les x_j ne sont PAS libres (contraints à être des puissances de 2 ordonnées)

    # "Alphabet" réel : {2^p : p = 0, 1, ..., S-1} ⊂ Z/dZ
    alphabet = set(pow(2, p, d) for p in range(S))
    print(f"    |Alphabet 2^p mod d| = {len(alphabet)}/{d} "
          f"(= {len(alphabet)/d:.1%} de Z/dZ)")

# ==============================================================
print("\n" + "=" * 70)
print("  SYNTHÈSE : CE QUE CHAQUE BRANCHE OUVRE")
print("=" * 70)
# ==============================================================
print("""
  B1 (Algébrique h=2/3) :
    ✓ Reformulation propre : corrSum ≡ 0 ⟺ Σ w^j·2^{A_j} ≡ -1 (mod d)
    ✓ Identité w^k = 2^{-S} mod d (lie poids et positions)
    ✓ ⟨w,2⟩ engendre une FRACTION de (Z/dZ)* — quantifiable
    → OUVRE : prouver que -1 ∉ Image(Σ w^j·2^{A_j}) via structure du groupe

  B2 (Baker / Énoncé A) :
    ✓ ord_d(2) > S-1 ⟺ aucun s ∈ {1,...,S-1} avec d | (2^{S-s} - 1)
    ✓ Reformulé : ord_d(2) ∤ (S-s) pour tout s < S
    ✓ Near-misses : ratio toujours > 0.003 pour k ≥ 4
    ✓ ord_d(2)/S croît (typiquement 1.5-3x), jamais < 1.7 pour k ≥ 4
    → OUVRE : borne inférieure effective sur ord_d(2) via Baker

  B3 (CRT incompatibilité) :
    ✓ Deux mécanismes : prime blocking OU CRT incompat
    ✓ Pour k=6 (5×59) : corrSum ≡ 0 mod 5 ⟹ corrSum ≢ 0 mod 59
    ✓ Les résidus mod 5 et mod 59 sont ANTI-CORRÉLÉS pour le résidu 0
    → OUVRE : formaliser l'anti-corrélation via 2^S ≡ 3^k (mod d)

  B4 (Induction sur k) :
    ✓ Récurrence : d(k+1) = 2d-3^k (si ΔS=1) ou 4d+3^k (si ΔS=2)
    ✓ Formule EXACTE, pas d'approximation
    ✗ Mais les compositions changent complètement (S change)
    → OUVRE : transformer une preuve de N₀(d(k))=0 en preuve de N₀(d(k+1))=0
    → DIFFICULTÉ : les espaces Comp(S,k) et Comp(S+1,k+1) sont incomparables

  B5 (p-adique) :
    ✓ Pour certains k : v_p(corrSum) < v_p(d) pour tout premier p | d
    ✓ Cela PROUVE directement N₀(p^{v_p(d)}) = 0 → N₀(d) = 0
    ✗ Ne marche pas pour TOUS les k (dépend de la factorisation)
    → OUVRE : combiner avec CRT quand la valuation ne suffit pas

  B6 (Coding theory) :
    ✓ corrSum = H·x est un syndrome de code (H = 1×k, x = 2^{A_j})
    ✓ L'alphabet {2^p mod d} ne couvre qu'une fraction de Z/dZ
    ✓ La couverture de Im(H·x) est toujours < 100% (0 toujours exclu)
    → OUVRE : borner |Im(H·x)| par des méthodes de théorie des codes
""")
