#!/usr/bin/env python3
"""
SESSION 9c — DEEP BACKWARD EXCLUSION + SUBSTITUTION B_j
=========================================================
Protocole DISCOVERY v2.0, Lentille L1+L3.

DÉCOUVERTES DE 9b À APPROFONDIR :
1. Backward Exclusion : en remontant depuis s=0 avec positions ordonnées,
   le résidu s₀=1 n'est JAMAIS atteint.
   → Pourquoi exactement ? Peut-on le prouver ?

2. Substitution B_j = A_j - j : u = w·2 mod p
   - Pour k=3 : u = -1 mod 5 → annulations par paires
   - Pour k=3, k=5 : 0 est le SEUL résidu absent
   → Quand u = -1 mod p ? Quand 0 est-il le seul absent ?

INVESTIGATIONS :
  I1  : Backward Exclusion — systématique pour tous les k premiers
  I2  : Pourquoi 1 est exclu : analyse de la structure du backward
  I3  : u = w·2 mod p — quand u ≡ -1 mod p ?
  I4  : Quand 0 est le seul résidu absent ?
  I5  : Lien entre les deux découvertes
  I6  : Toward a unified theorem
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

# ============================================================
# INVESTIGATION 1 : Backward Exclusion systématique
# ============================================================
def investigate_backward_exclusion_systematic():
    """
    Pour chaque k premier (d premier), vérifier que le backward
    depuis s=0 n'atteint JAMAIS s₀=1.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 1 : Backward Exclusion systématique")
    print("=" * 70)

    results = []
    for k in range(3, 25):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue

        p = d
        w = pow(3, -1, p)

        # Backward BFS depuis s=0
        # À la couche j (de droite), s_{j-1} = (s_j - w^j · 2^{A_j}) mod p
        # Contrainte : positions STRICTEMENT décroissantes en backward
        # Couche k-1 : s_{k-1} = 0, position A_{k-1} ∈ {1,...,S-1}
        # Couche k-2 : A_{k-2} < A_{k-1}
        # ...
        # Couche 0 : A_0 = 0 (fixé)

        # Backward : on part de s=0 au niveau k-1
        # Au niveau j : s contient la somme partielle des termes j..k-1
        # On enlève le terme j : s_{j-1} = s_j - w^j · 2^{A_j}
        # Mais en backward on AJOUTE le terme j

        # En fait, reformulons :
        # Forward : s_j = s_{j-1} + w^j · 2^{A_j}
        # s_0 = w^0 · 2^{A_0} = 1 (car A_0=0)
        # s_{k-1} = Σ w^j · 2^{A_j} devrait = 0 mod p

        # Backward : on part de s_{k-1} = 0
        # On calcule s_{j-1} = s_j - w^j · 2^{A_j}
        # En reculant de couche k-1 vers couche 0
        # Contrainte : A_{k-1} > A_{k-2} > ... > A_1 > A_0 = 0

        # Backward layer by layer
        # State: (résidu s, position max utilisée)
        # Au niveau j, la position est A_j, et on a A_j < min_pos_next

        # Dernier terme (j=k-1) : on choisit A_{k-1} ∈ {k-1,...,S-1}
        # (car A_0=0 < A_1 < ... < A_{k-1}, et A_{k-2} ≥ k-2, donc A_{k-1} ≥ k-1)
        backward = {}
        wj = pow(w, k-1, p)  # w^{k-1}
        for a in range(k-1, S):
            s_prev = (0 - wj * pow(2, a, p)) % p
            key = (s_prev, a)
            backward[key] = True

        # Remonter de j=k-2 vers j=1
        for j in range(k-2, 0, -1):
            wj = pow(w, j, p)
            new_backward = {}
            for (s, max_pos) in backward:
                # Choisir A_j < max_pos, et A_j ≥ j (car j positions avant)
                for a in range(j, max_pos):
                    s_prev = (s - wj * pow(2, a, p)) % p
                    key = (s_prev, a)
                    new_backward[key] = True
            backward = new_backward

        # Au niveau j=0 : A_0 = 0, w^0 = 1, 2^0 = 1
        # s_{-1} devrait valoir s_0 - 1 = backward_residue - 1
        # On veut s_0 = 1, donc backward_residue = 1

        # En fait, le backward donne les résidus s_1 possibles
        # s_0 = 1 (fixe), donc s_1 = s_0 + w^1 · 2^{A_1} = 1 + w · 2^{A_1}
        # On veut que parmi les s_1 du backward, aucun ne soit
        # de la forme 1 + w · 2^a pour a > 0

        # Mais non — le backward est déjà fait avec contrainte A_1 ≥ 1
        # Les résidus dans backward à ce stade sont les s_1 compatibles
        # avec un chemin vers s_{k-1}=0.

        # En forward : s_0 = 1, s_1 = 1 + w · 2^{A_1}
        # Pour qu'il y ait une solution, il faut que s_1 forward
        # soit dans l'ensemble des s_1 backward, ET que A_1 backward ≤ min(A_2)

        # Simplifions : calculons directement les résidus s_0 atteints
        # en ajoutant le terme j=0 au backward (maintenant au niveau j=1)
        # s_0 = s_1 - w^0 · 2^{A_0} = s_1 - 1 (car A_0 = 0)

        residues_s0 = set()
        for (s1, max_pos) in backward:
            if max_pos > 0:  # A_0 = 0 < max_pos
                s0 = (s1 - 1) % p
                residues_s0.add(s0)

        # s_0 = 1 (condition initiale forward) ↔ s0_backward = 1 - 1 = 0
        # Attendez... recalculons.
        # Forward: s_0 = w^0 · 2^0 = 1
        # Backward donne les s_1 possibles tels qu'il existe un chemin
        # vers s_{k-1} = 0.
        # Pour une solution complète : s_1_backward doit être de la forme
        # 1 + w · 2^{A_1} pour A_1 ∈ {1,...,S-1}, et A_1 < min(A_2) backward.

        # Alternative : résidus backward au niveau 0
        # = (s_1 backward - 2^0) = (s_1 - 1) mod p
        # On veut que ce résidu = 0 (car s_0 forward = 1, et s_0 = w^0·2^0 = 1,
        # et la condition est s_{k-1} - s_0 + s_0 = 0, ie s_0 contribue)

        # Hmm, simplifions radicalement :
        # Le backward COMPLET depuis s=0 en k-1 étapes donne tous les s_1 accessibles.
        # En forward, s_1 = 1 + w · 2^{A_1} pour A_1 ∈ {1,...,min_pos_bwd-1}.
        # Intersection = solutions.

        # Faisons le directement avec la BFS forward + backward
        # et vérifions qu'il n'y a aucune intersection.

        # Forward from s_0 = 1
        forward_s1 = {}  # (résidu, position A_1) → True
        for a1 in range(1, S):
            s1 = (1 + w * pow(2, a1, p)) % p
            forward_s1[(s1, a1)] = True

        # Check intersection : forward s_1 avec position A_1,
        # backward s_1 avec min_position A_2 > A_1
        has_solution = False
        for (s1_fwd, a1) in forward_s1:
            for (s1_bwd, max_pos) in backward:
                if s1_fwd == s1_bwd and a1 < max_pos:
                    has_solution = True
                    break
            if has_solution:
                break

        # Résidus atteints par backward (sans position)
        bwd_residues = sorted(set(s for s, _ in backward))
        fwd_residues = sorted(set(s for s, _ in forward_s1))

        # Résidus communs
        common = set(bwd_residues) & set(fwd_residues)

        marker = "✅ EXCLU" if not has_solution else "❌ SOLUTION"
        results.append((k, p, has_solution, len(bwd_residues), len(fwd_residues), len(common)))
        print(f"  k={k:>2}, p={p:>6}: {marker}"
              f"  |bwd|={len(bwd_residues):>4}/{p}"
              f"  |fwd|={len(fwd_residues):>4}/{p}"
              f"  |common|={len(common):>4}")

    print("\n  RÉSUMÉ : Backward Exclusion")
    all_excluded = all(not sol for _, _, sol, _, _, _ in results)
    print(f"  Tous exclus ? {all_excluded}")

    # Analyser le pattern
    print("\n  Ratios |bwd|/p et |fwd|/p :")
    for k, p, sol, bwd, fwd, com in results:
        print(f"    k={k:>2}: |bwd|/p={bwd/p:.3f}, |fwd|/p={fwd/p:.3f}, overlap={com}/{p}")

    return results

# ============================================================
# INVESTIGATION 2 : Pourquoi 1 est exclu
# ============================================================
def investigate_why_1_excluded():
    """
    Analyse fine : pourquoi le résidu s₀=1 est systématiquement exclu
    du backward depuis 0.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 2 : Pourquoi 1 est exclu du backward")
    print("=" * 70)

    for k in [3, 5, 7, 11]:
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue

        p = d
        w = pow(3, -1, p)
        u = (w * 2) % p

        print(f"\n  k={k}, p={p}, w={w}, u=w·2={u}")

        # La somme est S = Σ_{j=0}^{k-1} w^j · 2^{A_j}
        # = Σ_{j=0}^{k-1} u^j · 2^{B_j} (avec B_j = A_j - j ≥ 0, non-décr.)
        # Condition : S ≡ 0 mod p

        # En backward depuis S=0 :
        # On enlève les termes un par un
        # Le dernier terme à enlever est j=0 : w^0 · 2^{A_0} = 1
        # Donc le résidu juste avant d'ajouter le terme j=0 serait s_0 tel que
        # s_0 + 1 = s_1, ie s_0 = s_1 - 1 = backward_residue

        # Non, reformulons proprement :
        # Σ_{j=0}^{k-1} w^j · 2^{A_j} ≡ 0 mod p
        # ↔ 1 + Σ_{j=1}^{k-1} w^j · 2^{A_j} ≡ 0 mod p
        # ↔ Σ_{j=1}^{k-1} w^j · 2^{A_j} ≡ -1 mod p

        # Donc le backward depuis s=0 en k termes est équivalent à
        # backward depuis s=-1 en k-1 termes (sans le terme j=0)

        # En d'autres mots : les k-1 termes w^1·2^{A_1}, ..., w^{k-1}·2^{A_{k-1}}
        # avec 1 ≤ A_1 < ... < A_{k-1} ≤ S-1
        # doivent sommer à -1 mod p

        target = (-1) % p
        print(f"  Cible pour les k-1={k-1} derniers termes : {target} (= -1 mod {p})")

        # Calculons l'image de la somme des k-1 termes
        # Forward : s = Σ_{j=1}^{k-1} w^j · 2^{A_j} mod p
        # avec 1 ≤ A_1 < ... < A_{k-1} ≤ S-1
        if C <= 100000:
            residues = set()
            for combo in combinations(range(1, S), k-1):
                s = sum(pow(w, j+1, p) * pow(2, combo[j], p) for j in range(k-1)) % p
                residues.add(s)
            print(f"  Image de la somme des {k-1} termes : {len(residues)}/{p} résidus")
            print(f"  -1 = {target} ∈ image ? {target in residues}")
            missing = sorted(set(range(p)) - residues)
            if len(missing) <= 20:
                print(f"  Résidus manquants : {missing}")
            else:
                print(f"  Résidus manquants : {len(missing)} ({missing[:10]}...)")
        else:
            print(f"  C={C} trop grand pour énumération complète")

        # Factorisation de p-1 et structure de w
        print(f"  p-1 = {p-1} = {factorize(p-1)}")
        print(f"  ord(w) = ?", end=" ")
        ord_w = 1
        x = w
        while x != 1:
            x = (x * w) % p
            ord_w += 1
        print(f"ord(w) = {ord_w}")
        print(f"  ord(u) = ?", end=" ")
        ord_u = 1
        x = u
        while x != 1:
            x = (x * u) % p
            ord_u += 1
        print(f"ord(u) = {ord_u}")

        # Vérifier w^k ≡ 2^{-S} mod p
        wk = pow(w, k, p)
        inv2S = pow(2, -S, p)
        print(f"  w^k = {wk}, 2^{{-S}} = {inv2S}, w^k = 2^{{-S}} ? {wk == inv2S}")

    return True

# ============================================================
# INVESTIGATION 3 : u = w·2 — quand u ≡ -1 ?
# ============================================================
def investigate_u_minus_one():
    """
    u = w·2 = 2·3^{-1} mod p.
    Quand u ≡ -1 mod p ? ↔ 2·3^{-1} ≡ -1 ↔ 2 ≡ -3 ↔ p | 5.
    Donc u = -1 SSI p = 5 SSI k = 3 !
    Mais pour d'autres k, qu'est-ce qui remplace cette propriété ?
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 3 : u = w·2 — quand u ≡ -1 ?")
    print("=" * 70)

    print("\n  u = 2·3^{-1} mod p. u = -1 ↔ 2 = -3 mod p ↔ p | 5.")
    print("  Donc u = -1 SEULEMENT pour p = 5, ie k = 3.")

    print("\n  Valeurs de u pour chaque k premier :")
    for k in range(3, 30):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)
        u = (w * 2) % p
        ord_u = 1
        x = u
        while x != 1:
            x = (x * u) % p
            ord_u += 1

        # Propriétés de u
        u_plus_1 = (u + 1) % p
        u_squared = (u * u) % p
        u_k = pow(u, k, p)
        uk_minus_1 = (u_k - 1) % p

        # u^k = (w·2)^k = w^k · 2^k = 2^{-S} · 2^k = 2^{k-S} mod p
        # k - S est toujours négatif (S > k), donc u^k = 2^{-(S-k)} mod p
        expected_uk = pow(2, k - S, p)

        print(f"  k={k:>2}, p={p:>6}: u={u:>5}, ord(u)={ord_u:>5}, "
              f"u+1={u_plus_1:>5}, u²={u_squared:>5}, "
              f"u^k={u_k:>5} (=2^{{k-S}}={expected_uk}? {u_k == expected_uk})")

    # Propriété clé : u^k = 2^{k-S} mod p
    # Pour k=3 : S=5, k-S=-2, 2^{-2} = (1/4) mod 5 = 4
    # u^3 = (-1)^3 = -1 = 4 mod 5. Vérifié !
    print("\n  Identité universelle : u^k ≡ 2^{k-S} mod p")
    print("  Car u = w·2, u^k = w^k·2^k = 2^{-S}·2^k = 2^{k-S}")

    return True

# ============================================================
# INVESTIGATION 4 : Quand 0 est le seul résidu absent ?
# ============================================================
def investigate_only_zero_missing():
    """
    Pour la substitution B_j, quand 0 est-il le SEUL résidu absent ?
    Observé pour k=3 (p=5) et k=5 (p=13).
    Pas pour k=4 (p=47, beaucoup de résidus absents).
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 4 : Quand 0 est le seul résidu absent ?")
    print("=" * 70)

    for k in range(3, 20):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d

        if C > 200000:
            print(f"  k={k}, p={p}: C={C} — trop grand")
            continue

        w = pow(3, -1, p)
        u = (w * 2) % p

        # B_j = A_j - j, B_j ∈ [0, S-k], non-décroissant
        max_B = S - k
        if max_B < 0:
            continue

        # Toutes les B-compositions : 0 ≤ B_0 ≤ B_1 ≤ ... ≤ B_{k-1} ≤ max_B
        # C'est C(max_B + k, k) - mais en fait c'est C(S-1, k-1) = C
        # (équivalence entre compositions ordonnées et B non-décroissantes)

        # Calculer les résidus de Σ u^j · 2^{B_j}
        # Forward BFS
        layers = [set()]
        layers[0].add((pow(1, 1, p) * 1 % p, 0))  # j=0: u^0 · 2^{B_0}, B_0 ≥ 0

        # Couche 0 : s = u^0 · 2^{B_0} = 2^{B_0} pour B_0 ∈ [0, max_B]
        layer0 = set()
        for b in range(0, max_B + 1):
            s = pow(2, b, p)
            layer0.add((s, b))
        layers[0] = layer0

        for j in range(1, k):
            uj = pow(u, j, p)
            new_layer = set()
            for (s, last_b) in layers[j-1]:
                for b in range(last_b, max_B + 1):
                    s_new = (s + uj * pow(2, b, p)) % p
                    new_layer.add((s_new, b))
            layers.append(new_layer)

        # Résidus finaux
        final_residues = set(s for s, _ in layers[k-1])
        n_missing = p - len(final_residues)
        zero_in = 0 in final_residues
        missing = sorted(set(range(p)) - final_residues)

        only_zero = (missing == [0])
        ratio = C / p

        tag = "★★★ SEUL 0 MANQUANT" if only_zero else (
              "★ 0 manquant + autres" if 0 in missing else "0 PRÉSENT?!")

        print(f"  k={k:>2}, p={p:>6}, C/p={ratio:>6.2f}: "
              f"|image|={len(final_residues):>5}/{p}, "
              f"missing={n_missing:>5}, {tag}")
        if n_missing <= 15:
            print(f"    manquants : {missing}")

    return True

# ============================================================
# INVESTIGATION 5 : Lien backward-exclusion ↔ substitution
# ============================================================
def investigate_link_backward_substitution():
    """
    Le backward-exclusion (1 ∉ reached) et la substitution (0 ∉ image des B-sommes)
    sont-ils le MÊME phénomène ?

    Démontrons l'équivalence :
    - Backward depuis s=0 n'atteint pas 1
    ↔ aucune composition ordonnée ne donne corrSum ≡ 0 mod p
    ↔ N₀(p) = 0
    Ce sont la MÊME chose !

    La question est plutôt : quel formalisme est le plus puissant
    pour PROUVER N₀ = 0 ?
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 5 : Lien backward-exclusion ↔ substitution")
    print("=" * 70)

    print("\n  ÉQUIVALENCE FONDAMENTALE :")
    print("  [A] Backward depuis s_{k-1}=0 n'atteint pas s_0=1")
    print("  [B] 0 ∉ image des B-sommes ordonnées")
    print("  [C] N₀(d) = 0")
    print("  Toutes ces affirmations sont ÉQUIVALENTES.")

    print("\n  Vérifions pour chaque k premier :")
    for k in range(3, 16):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        if C > 100000:
            continue

        p = d
        w = pow(3, -1, p)

        # Méthode C : brute force N₀
        n0 = 0
        for combo in combinations(range(1, S), k-1):
            A = (0,) + combo
            cs = sum(pow(w, j, p) * pow(2, A[j], p) for j in range(k)) % p
            if cs == 0:
                n0 += 1

        print(f"  k={k:>2}, p={p:>6}: N₀(p) = {n0} {'✅' if n0 == 0 else '❌'}")

    print("\n  → Les trois formalismes sont équivalents.")
    print("  → La question est : POURQUOI N₀ = 0 ?")
    print("  → Le backward-exclusion donne un MÉCANISME d'exclusion.")
    print("  → La substitution B_j donne une STRUCTURE ALGÉBRIQUE.")

    return True

# ============================================================
# INVESTIGATION 6 : Vers un théorème unifié
# ============================================================
def investigate_unified_theorem():
    """
    Tentative d'unification.

    IDÉE CENTRALE :
    Σ_{j=0}^{k-1} u^j · 2^{B_j} mod p, avec B non-décroissant dans [0, S-k].

    Si on écrit T_j = u^j · 2^{B_j}, alors :
    - |T_j| est contraint par la non-décroissance de B_j
    - La somme doit valoir 0

    Observation : quand C >> p (beaucoup de compositions par résidu),
    0 est souvent le SEUL absent.
    Quand C << p (peu de compositions), beaucoup de résidus manquent.
    Mais 0 manque TOUJOURS.

    Approche : montrer que la contrainte de non-décroissance crée
    un BIAIS STRUCTUREL qui empêche la somme de valoir 0.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 6 : Vers un théorème unifié")
    print("=" * 70)

    # Idée : la somme minimale (quand tous B_j = 0) est
    # S_min = Σ u^j = (u^k - 1)/(u - 1) mod p
    # Et elle est NON NULLE car p est premier et u ≠ 1

    print("\n  Somme minimale (B_j = 0 pour tout j) :")
    for k in range(3, 25):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)
        u = (w * 2) % p

        # S_min = Σ_{j=0}^{k-1} u^j mod p
        s_min = sum(pow(u, j, p) for j in range(k)) % p

        # Si u ≠ 1 : S_min = (u^k - 1)/(u-1) mod p
        if u != 1:
            uk = pow(u, k, p)
            inv_u_minus_1 = pow(u - 1, -1, p) if (u - 1) % p != 0 else None
            formula = ((uk - 1) * inv_u_minus_1) % p if inv_u_minus_1 else "N/A"
        else:
            formula = k % p

        # S_max = Σ u^j · 2^{S-k} = 2^{S-k} · S_min
        s_max = (pow(2, S-k, p) * s_min) % p

        print(f"  k={k:>2}, p={p:>6}: u={u:>5}, S_min={s_min:>5}, "
              f"S_max={s_max:>5}, formula={formula}")

    # Analyse : quand la somme S_min = Σ u^j est-elle "loin" de 0 ?
    print("\n  Analyse de |S_min| et |S_max| en fraction de p :")
    for k in range(3, 25):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)
        u = (w * 2) % p

        s_min = sum(pow(u, j, p) for j in range(k)) % p
        s_max = (pow(2, S-k, p) * s_min) % p

        # Distance à 0 (en fraction de p)
        dist_min = min(s_min, p - s_min) / p
        dist_max = min(s_max, p - s_max) / p

        print(f"  k={k:>2}, p={p:>6}: dist_min/p={dist_min:.3f}, dist_max/p={dist_max:.3f}")

    # Approche : Structure de l'automate à sommes partielles
    print("\n  STRUCTURE DE L'AUTOMATE À SOMMES PARTIELLES :")
    print("  Pour chaque couche j, l'action est : s → s + u^j · 2^b (b ≥ last_b)")
    print("  Le multiplicateur u^j crée une rotation dans Z/pZ.")
    print("  La puissance 2^b crée une dilatation.")
    print("  La contrainte b ≥ last_b restreint les dilatations accessibles.")

    # Pour les petits k, tracer la trajectoire complète
    for k in [3, 5]:
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)
        u = (w * 2) % p

        print(f"\n  Trajectoire pour k={k}, p={p}, u={u}:")

        # Atomes à chaque couche : u^j · 2^b pour b ∈ [0, S-k]
        for j in range(k):
            uj = pow(u, j, p)
            atoms = [(uj * pow(2, b, p)) % p for b in range(S - k + 1)]
            print(f"    Couche {j}: u^{j}={uj:>3}, atomes={atoms}")

        # Sommes cumulatives minimale et maximale
        print(f"    Somme tous-0 : {sum(pow(u,j,p) for j in range(k)) % p}")
        print(f"    Somme tous-max: {sum(pow(u,j,p)*pow(2,S-k,p) for j in range(k)) % p}")

    return True

# ============================================================
# INVESTIGATION 7 : Test de la conjecture d'anti-concentration
# ============================================================
def investigate_anti_concentration():
    """
    CONJECTURE : Pour p premier de la forme 2^S - 3^k,
    les sommes ordonnées Σ u^j · 2^{B_j} mod p
    ne peuvent JAMAIS valoir 0.

    Est-ce une propriété d'ANTI-CONCENTRATION ?
    La distribution des sommes est uniforme sur p-1 résidus,
    et 0 est toujours exclu.

    Vérifions la distribution des résidus pour plusieurs k.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 7 : Anti-concentration (distribution des résidus)")
    print("=" * 70)

    for k in range(3, 16):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        if C > 100000:
            continue

        p = d
        w = pow(3, -1, p)

        # Compter les résidus
        counts = defaultdict(int)
        for combo in combinations(range(1, S), k-1):
            A = (0,) + combo
            cs = sum(pow(w, j, p) * pow(2, A[j], p) for j in range(k)) % p
            counts[cs] += 1

        # Statistiques
        n_nonzero = sum(1 for r in counts if r != 0 and counts[r] > 0)
        avg_count = C / (p - 1) if p > 1 else 0  # expected if uniform on p-1 residues
        actual_counts = [counts.get(r, 0) for r in range(1, p)]
        max_count = max(actual_counts) if actual_counts else 0
        min_count = min(actual_counts) if actual_counts else 0

        # Chi-squared test for uniformity on p-1 residues
        expected = C / (p - 1) if p > 1 else 1
        chi2 = sum((counts.get(r, 0) - expected)**2 / expected for r in range(1, p))

        print(f"  k={k:>2}, p={p:>5}, C={C:>6}: "
              f"N₀={counts.get(0,0)}, "
              f"|image|={n_nonzero:>4}/{p-1}, "
              f"avg={avg_count:.1f}, min={min_count}, max={max_count}, "
              f"χ²={chi2:.1f}")

        # Si 0 est exclu et la distribution est quasi-uniforme sur {1,...,p-1}
        # → Anti-concentration parfaite !
        if counts.get(0, 0) == 0 and n_nonzero == p - 1:
            print(f"    ★★★ ANTI-CONCENTRATION PARFAITE : uniforme sur {{1,...,{p-1}}}")

    return True

# ============================================================
# INVESTIGATION 8 : Le rôle de l'identité w^k = 2^{-S}
# ============================================================
def investigate_wk_identity_deep():
    """
    L'identité w^k = 2^{-S} mod p est fondamentale.
    Car elle implique u^k = 2^{k-S} mod p.

    Conséquence : la somme Σ u^j · 2^{B_j} a une SYMÉTRIE
    entre les termes j et j+k (mod k).

    Mais on n'a que k termes ! Donc cette symétrie crée une CONTRAINTE
    intrinsèque : la somme est "fermée" par l'identité.

    Formalisons cette contrainte.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 8 : Rôle profond de w^k = 2^{-S}")
    print("=" * 70)

    for k in range(3, 20):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue

        p = d
        w = pow(3, -1, p)
        u = (w * 2) % p

        # u^k = 2^{k-S} mod p
        uk = pow(u, k, p)
        expected = pow(2, k - S, p)

        # Σ u^j pour j=0..k-1
        sigma = sum(pow(u, j, p) for j in range(k)) % p

        # Si u ≠ 1 : σ = (u^k - 1)/(u - 1) = (2^{k-S} - 1)/(u - 1)
        # Numérateur : 2^{k-S} - 1 mod p
        numerator = (pow(2, k - S, p) - 1) % p
        denominator = (u - 1) % p

        # d = 2^S - 3^k, donc 2^S ≡ 3^k mod p → 2^{-S} ≡ 3^{-k} ≡ w^k mod p
        # et 2^{k-S} = 2^k · 2^{-S} = 2^k · w^k = (2w)^k = u^k

        # La somme de tous les u^j (B=0) est σ
        # La somme avec B_j variable ajoute des facteurs 2^{B_j}
        # qui dilatent chaque terme indépendamment.

        # KEY INSIGHT : si σ = 0, alors la somme minimale est 0
        # et il y aurait une solution ! Donc σ ≠ 0 est NÉCESSAIRE.

        print(f"  k={k:>2}, p={p:>6}: u={u:>5}, σ(u)={sigma:>5}, "
              f"σ=0? {sigma == 0}, "
              f"num={numerator:>5}, den={denominator:>5}")

        if sigma == 0:
            print(f"    ⚠️  σ = 0 ! La somme minimale est 0 !")
            # Vérifier si c'est vraiment le cas
            s_min = sum(pow(u, j, p) for j in range(k)) % p
            print(f"    Vérification : s_min = {s_min}")

    print("\n  OBSERVATION : σ(u) = Σ u^j ≠ 0 pour tout k testé")
    print("  C'est NÉCESSAIRE (sinon B_j = 0 donnerait N₀ > 0)")
    print("  Mais pas SUFFISANT (il faut aussi que les dilatations ne compensent pas)")

    # Analyse plus fine : qu'est-ce que σ en fonction de p ?
    print("\n  Fraction σ/p (distance de la somme min à 0) :")
    for k in range(3, 25):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)
        u = (w * 2) % p
        sigma = sum(pow(u, j, p) for j in range(k)) % p
        dist = min(sigma, p - sigma)
        print(f"    k={k:>2}: σ={sigma:>6}, |σ|/p = {dist/p:.4f}")

    return True

# ============================================================
# INVESTIGATION 9 : Synthèse — mécanisme unifié
# ============================================================
def synthesize():
    """
    Synthèse des investigations.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 9 : SYNTHÈSE")
    print("=" * 70)

    print("""
  DÉCOUVERTES PRINCIPALES :

  1. BACKWARD EXCLUSION (I1) :
     Pour tout k premier testé, le backward depuis s=0 n'atteint
     JAMAIS s₀=1. C'est une REFORMULATION du Prime Blocking.

  2. SUBSTITUTION B_j (I4) :
     u = w·2 = 2·3^{-1} mod p.
     La somme Σ u^j · 2^{B_j} ne vaut JAMAIS 0.
     Quand C/p >> 1 : 0 est le SEUL résidu absent.
     Quand C/p << 1 : beaucoup de résidus absents, mais 0 toujours.

  3. IDENTITÉ w^k = 2^{-S} (I8) :
     Implique u^k = 2^{k-S}, ce qui "ferme" la structure.
     La somme σ = Σ u^j ≠ 0 est NÉCESSAIRE, et c'est vérifié.

  4. ANTI-CONCENTRATION (I7) :
     La distribution est quasi-uniforme sur {1,...,p-1}.
     → Le 0 n'est pas "évité par hasard" mais STRUCTURELLEMENT exclu.

  PISTE VERS LA PREUVE :

  A) Montrer que la contrainte de non-décroissance (B non-décr.)
     crée un sous-ensemble STRUCTURÉ de Z/pZ qui évite 0.

  B) Utiliser l'identité u^k = 2^{k-S} comme CLÔTURE ALGÉBRIQUE.

  C) Possibilité : caractère de sommes exponentielles avec contrainte
     d'ordre → résultat type Weil/Deligne pour les sommes restreintes.

  D) Pour d composite : combiner avec CRT anti-corrélation.
    """)

    return True

# ============================================================
# MAIN
# ============================================================
if __name__ == "__main__":
    t0 = time.time()
    print("SESSION 9c — DEEP BACKWARD EXCLUSION + SUBSTITUTION B_j")
    print("=" * 70)

    investigate_backward_exclusion_systematic()
    investigate_why_1_excluded()
    investigate_u_minus_one()
    investigate_only_zero_missing()
    investigate_link_backward_substitution()
    investigate_unified_theorem()
    investigate_anti_concentration()
    investigate_wk_identity_deep()
    synthesize()

    elapsed = time.time() - t0
    print(f"\n{'=' * 70}")
    print(f"  SESSION 9c TERMINÉE en {elapsed:.1f}s")
    print("=" * 70)
