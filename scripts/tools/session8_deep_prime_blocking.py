#!/usr/bin/env python3
"""
SESSION 8 — APPROFONDISSEMENT B5 : PRIME BLOCKING
===================================================
Protocole DISCOVERY v2.0, Phase Multi-Lentille.

QUESTION CENTRALE :
  POURQUOI v_p(corrSum) = 0 pour TOUT d = p premier ?

DÉCOMPOSITION :
  corrSum = 3^{k-1} + Σ_{j=1}^{k-1} 3^{k-1-j} · 2^{A_j}
          = 3^{k-1} · (1 + Σ_{j=1}^{k-1} 3^{-j} · 2^{A_j})
          = 3^{k-1} · (1 + Σ_{j=1}^{k-1} w^j · 2^{A_j})    [w = 3^{-1} mod p]

  corrSum ≡ 0 mod p  ⟺  1 + Σ w^j · 2^{A_j} ≡ 0 mod p
                      ⟺  Σ w^j · 2^{A_j} ≡ -1 mod p

  (car 3^{k-1} ≢ 0 mod p puisque gcd(d,3)=1)

OBJECTIF : Comprendre POURQUOI -1 ∉ Image{Σ w^j · 2^{A_j}}
"""

from math import ceil, log2, gcd, comb
from itertools import combinations
from collections import defaultdict, Counter
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

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i+2) == 0: return False
        i += 6
    return True

def ord_mod(a, m):
    """Ordre multiplicatif de a mod m."""
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
# INVESTIGATION 1 : Décomposition corrSum = 3^{k-1} · (1 + Σ)
# Pour d premier, analyser la cible et l'image
# ============================================================
def investigate_target(max_k=12):
    """
    Pour chaque k où d est premier :
    - Calculer target = -1 mod p  (la valeur que Σ devrait atteindre)
    - Calculer l'image de Σ = Σ_{j=1}^{k-1} w^j · 2^{A_j}
    - Vérifier que target ∉ Image
    - Analyser la structure de l'image
    """
    print("=" * 70)
    print("  INVESTIGATION 1 : Image de Σ w^j · 2^{A_j} vs cible -1")
    print("=" * 70)

    for k in range(3, max_k + 1):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue

        p = d
        w = pow(3, -1, p)
        target = (-1) % p  # = p - 1

        # Calculer l'image de Σ_{j=1}^{k-1} w^j · 2^{A_j}
        # où A_j ∈ {1,...,S-1} strictement croissants, j=1..k-1
        images = []
        for combo in combinations(range(1, S), k - 1):
            # combo = (A_1, ..., A_{k-1}) strictement croissants
            sigma = sum(pow(w, j+1, p) * pow(2, combo[j], p) for j in range(k-1)) % p
            images.append(sigma)

        image_set = set(images)
        target_hit = target in image_set
        coverage = len(image_set) / p * 100

        print(f"\n  k={k}: d=p={p} (premier), S={S}, C={C}")
        print(f"    w = 3^{{-1}} mod {p} = {w}")
        print(f"    target = -1 mod {p} = {target}")
        print(f"    |Image(Σ)| = {len(image_set)}/{p} ({coverage:.1f}%)")
        print(f"    target ∈ Image ? {target_hit}")

        # Quelles valeurs MANQUENT dans l'image ?
        missing = sorted(set(range(p)) - image_set)
        if len(missing) <= 20:
            print(f"    Valeurs absentes : {missing}")
        else:
            print(f"    {len(missing)} valeurs absentes (premières: {missing[:10]}...)")

        # Distance minimale à la cible
        dist_to_target = [min(abs(img - target), p - abs(img - target)) for img in images]
        min_dist = min(dist_to_target) if dist_to_target else float('inf')
        print(f"    Distance min à la cible : {min_dist}")

        # Distribution des résidus
        counter = Counter(images)
        print(f"    Résidu le plus fréquent : {counter.most_common(1)[0] if counter else 'N/A'}")
        print(f"    Résidu le moins fréquent : {counter.most_common()[-1] if counter else 'N/A'}")

# ============================================================
# INVESTIGATION 2 : Structure algébrique de l'image
# L'alphabet est {w^j · 2^a : j=1..k-1, a=1..S-1}
# La contrainte est a_1 < a_2 < ... < a_{k-1}
# ============================================================
def investigate_alphabet(max_k=12):
    """
    Analyser l'alphabet sous-jacent et ses propriétés.
    Pour chaque j, les termes possibles sont {w^j · 2^a mod p : a=1..S-1}.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 2 : Structure de l'alphabet {w^j · 2^a mod p}")
    print("=" * 70)

    for k in range(3, max_k + 1):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue

        p = d
        w = pow(3, -1, p)

        print(f"\n  k={k}: p={p}, w={w}, S={S}")

        # Pour chaque j, calculer l'ensemble des termes w^j · 2^a mod p
        for j in range(1, min(k, 5)):
            wj = pow(w, j, p)
            terms = set()
            for a in range(1, S):
                terms.add((wj * pow(2, a, p)) % p)
            print(f"    j={j}: w^{j}={wj}, |{{w^{j}·2^a}}| = {len(terms)}/{p-1}")
            if len(terms) <= 20:
                print(f"           termes = {sorted(terms)}")

        # L'ensemble COMPLET des "atomes" : {w^j · 2^a : j=1..k-1, a=1..S-1}
        all_atoms = set()
        for j in range(1, k):
            wj = pow(w, j, p)
            for a in range(1, S):
                all_atoms.add((wj * pow(2, a, p)) % p)

        print(f"    Atomes totaux : {len(all_atoms)}/{p-1}")

        # Ordre de w et de 2 dans (Z/pZ)*
        ord_w = ord_mod(w, p)
        ord_2 = ord_mod(2, p)
        print(f"    ord_p(w) = {ord_w}, ord_p(2) = {ord_2}")
        print(f"    w^k mod p = {pow(w, k, p)}, 2^{{-S}} mod p = {pow(2, -S, p)}")

        # Vérifier w^k = 2^{-S} mod p
        wk = pow(w, k, p)
        two_neg_S = pow(2, -S, p)
        print(f"    w^k ≡ 2^{{-S}} mod p ? {wk == two_neg_S}")

# ============================================================
# INVESTIGATION 3 : Le rôle de la contrainte d'ordre
# Sans la contrainte a_1 < a_2 < ... < a_{k-1},
# est-ce que -1 serait atteint ?
# ============================================================
def investigate_ordering_constraint(max_k=10):
    """
    Comparer Image(Σ) avec et sans la contrainte d'ordre croissant.
    Si l'image NON ordonnée contient -1, alors la contrainte d'ordre
    est ESSENTIELLE pour le prime blocking.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 3 : Rôle de la contrainte d'ordre")
    print("  (Image ordonnée vs non ordonnée)")
    print("=" * 70)

    for k in range(3, min(max_k + 1, 9)):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue

        p = d
        w = pow(3, -1, p)
        target = (-1) % p

        # Image ORDONNÉE (contrainte a_1 < ... < a_{k-1})
        ordered_images = set()
        for combo in combinations(range(1, S), k - 1):
            sigma = sum(pow(w, j+1, p) * pow(2, combo[j], p) for j in range(k-1)) % p
            ordered_images.add(sigma)

        # Image NON ORDONNÉE (répétitions permises)
        # Calcul itératif : après étape j, ensemble des sommes partielles
        unordered_reach = {0}
        for j in range(1, k):
            wj = pow(w, j, p)
            new_reach = set()
            for s in unordered_reach:
                for a in range(1, S):
                    new_reach.add((s + wj * pow(2, a, p)) % p)
            unordered_reach = new_reach

        ordered_has_target = target in ordered_images
        unordered_has_target = target in unordered_reach

        print(f"\n  k={k}: p={p}, target={target}")
        print(f"    |Image ordonnée|   = {len(ordered_images)}/{p} ({len(ordered_images)/p*100:.1f}%)")
        print(f"    |Image non-ord.|   = {len(unordered_reach)}/{p} ({len(unordered_reach)/p*100:.1f}%)")
        print(f"    target ∈ ordonnée   ? {ordered_has_target}")
        print(f"    target ∈ non-ord.   ? {unordered_has_target}")

        if unordered_has_target and not ordered_has_target:
            print(f"    ★ La contrainte d'ORDRE est CRITIQUE pour le blocking !")
        elif not unordered_has_target:
            print(f"    ★ Même SANS contrainte d'ordre, target absente !")
            print(f"      → Le blocking est PUREMENT ALGÉBRIQUE (pas l'ordre)")

# ============================================================
# INVESTIGATION 4 : corrSum mod p terme par terme
# Décomposer corrSum = T_0 + T_1 + ... + T_{k-1}
# où T_j = 3^{k-1-j} · 2^{A_j}
# Analyser les sommes partielles mod p
# ============================================================
def investigate_partial_sums(max_k=10):
    """
    Pour chaque composition, tracer la trajectoire des sommes partielles
    (T_0, T_0+T_1, ..., corrSum) mod p.
    Identifier s'il y a un pattern dans les sommes partielles.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 4 : Trajectoires des sommes partielles mod p")
    print("=" * 70)

    for k in range(3, min(max_k + 1, 8)):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue

        p = d

        print(f"\n  k={k}: p={p}, S={S}, C={C}")

        # Pour chaque composition, calculer les sommes partielles
        final_residues = Counter()
        penultimate = Counter()  # avant-dernier résidu

        trajectories = []
        for combo in combinations(range(1, S), k - 1):
            A = (0,) + combo
            partial = 0
            traj = []
            for j in range(k):
                partial = (partial + pow(3, k-1-j) * pow(2, A[j])) % p
                traj.append(partial)
            trajectories.append(traj)
            final_residues[traj[-1]] += 1
            if len(traj) >= 2:
                penultimate[traj[-2]] += 1

        # Résidu final : distribution
        print(f"    Résidus finaux: {len(final_residues)} valeurs distinctes")
        print(f"    0 dans résidus finaux ? {0 in final_residues}")

        # Vérifier si les résidus finaux forment un sous-groupe
        vals = sorted(final_residues.keys())
        if len(vals) <= 20:
            print(f"    Résidus finaux = {vals}")

        # Résidu AVANT le dernier terme
        # Le dernier terme est T_{k-1} = 3^0 · 2^{A_{k-1}} = 2^{A_{k-1}}
        # corrSum = penultimate + 2^{A_{k-1}}
        # Si corrSum ≡ 0, alors penultimate ≡ -2^{A_{k-1}} mod p
        print(f"    Résidus avant-derniers: {len(penultimate)} valeurs distinctes")

        # Pour que corrSum ≡ 0, il faut:
        # penultimate ≡ -2^{A_{k-1}} mod p
        # Les valeurs -2^a mod p pour a=1..S-1 sont :
        neg_powers_2 = set()
        for a in range(1, S):
            neg_powers_2.add((-pow(2, a, p)) % p)

        print(f"    Cibles possibles (-2^a mod p) : {sorted(neg_powers_2)}")
        print(f"    Résidus avant-derniers atteints : {sorted(penultimate.keys())}")

        # Intersection
        intersection = set(penultimate.keys()) & neg_powers_2
        print(f"    Intersection penultimate ∩ cibles : {sorted(intersection)}")

        if not intersection:
            print(f"    ★ AUCUNE intersection ! Le blocking vient des (k-1) premiers termes")
        else:
            print(f"    → Intersection non vide, le blocking nécessite analyse plus fine")
            # Pour chaque valeur dans l'intersection, vérifier si les positions sont compatibles
            n_compat = 0
            for combo in combinations(range(1, S), k - 1):
                A = (0,) + combo
                partial = 0
                for j in range(k - 1):
                    partial = (partial + pow(3, k-1-j) * pow(2, A[j])) % p
                # partial = somme des k-1 premiers termes
                last_pos = combo[-1]  # A_{k-1} est la dernière position choisie
                # Pour annuler : partial + 2^{A_{k-1}} ≡ 0 mod p
                # Or A_{k-1} = last_pos (déjà fixé dans la composition)
                needed = (-partial) % p
                actual = pow(2, last_pos, p) % p
                if needed == actual:
                    n_compat += 1
            print(f"    Compositions avec annulation exacte : {n_compat}/{C}")

# ============================================================
# INVESTIGATION 5 : Analyse via DFT / caractères
# corrSum mod p = Σ 3^{k-1-j} · 2^{A_j}
# Utiliser les caractères additifs de Z/pZ
# ============================================================
def investigate_characters(max_k=10):
    """
    Utiliser la transformée de Fourier discrète pour comprendre
    la distribution de corrSum mod p.

    N₀ = (1/p) Σ_{t=0}^{p-1} Σ_{compositions} ω^{t·corrSum}

    où ω = e^{2πi/p}. Si on peut montrer que les sommes exponentielles
    sont bornées, on peut peut-être prouver N₀ = 0.
    """
    import cmath

    print("\n" + "=" * 70)
    print("  INVESTIGATION 5 : Analyse par caractères de Z/pZ")
    print("=" * 70)

    for k in range(3, min(max_k + 1, 10)):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue

        p = d
        omega = cmath.exp(2j * cmath.pi / p)

        print(f"\n  k={k}: p={p}, S={S}, C={C}")

        # Calculer S_t = Σ_{compositions} ω^{t·corrSum} pour t=0,...,p-1
        # S_0 = C (trivial)
        # N₀ = (1/p) Σ_{t=0}^{p-1} S_t

        corrsums = []
        for combo in combinations(range(1, S), k - 1):
            A = (0,) + combo
            cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k)) % p
            corrsums.append(cs)

        # Calculer chaque S_t
        S_t_values = []
        for t in range(p):
            S_t = sum(omega**(t * cs) for cs in corrsums)
            S_t_values.append(S_t)

        # N₀ = (1/p) Σ S_t
        N0_complex = sum(S_t_values) / p
        N0 = round(N0_complex.real)

        print(f"    N₀ = {N0} (vérifié par Fourier)")
        print(f"    S_0 = {C}")

        # Magnitude de chaque S_t
        magnitudes = [abs(S_t_values[t]) for t in range(p)]
        max_mag_t = max(range(p), key=lambda t: magnitudes[t] if t > 0 else 0)

        print(f"    max |S_t| (t>0) = {magnitudes[max_mag_t]:.4f} at t={max_mag_t}")
        print(f"    C/p = {C/p:.4f}")

        # CRUCIAL : Si max|S_t| ≥ C/(p-1), alors N₀ pourrait être non-nul
        # Si Σ_{t>0} |S_t| < C, alors N₀ = 0 est GARANTI
        sum_mag = sum(magnitudes[t] for t in range(1, p))
        print(f"    Σ_{t>0} |S_t| = {sum_mag:.4f}")
        print(f"    Σ_{t>0} |S_t| / C = {sum_mag/C:.4f}")
        print(f"    Condition suffisante N₀=0 (Σ|S_t| < C) : {sum_mag < C}")

        # Ratio max_mag / sqrt(C)
        print(f"    max|S_t|/√C = {magnitudes[max_mag_t]/C**0.5:.4f}")

        # Phase des S_t non trivaux
        # Si les phases sont "aléatoires", les annulations se font naturellement
        phases = [cmath.phase(S_t_values[t]) for t in range(1, p)]
        # Vérifier si les phases sont uniformément réparties
        phase_hist = [0] * 8
        for phi in phases:
            bucket = int((phi + cmath.pi) / (2*cmath.pi) * 8) % 8
            phase_hist[bucket] += 1
        print(f"    Distribution phases (8 bins) : {phase_hist}")

        # FACTORISATION de S_t comme PRODUIT
        # S_t = Σ_{0<a_1<...<a_{k-1}<S} ω^{t·Σ 3^{k-1-j}·2^{A_j}}
        # Le terme j=0 donne ω^{t·3^{k-1}} (fixe)
        # Peut-on factoriser le reste ?

        # Essai : séparer le terme j=0 (qui est constant = 3^{k-1})
        # corrSum = 3^{k-1} + Σ_{j=1}^{k-1} 3^{k-1-j}·2^{A_j}
        # S_t = ω^{t·3^{k-1}} · Σ_{compositions} ω^{t·Σ_{j=1}^{k-1} 3^{k-1-j}·2^{A_j}}

        T0 = pow(3, k-1) % p
        factor0 = omega**(0 * T0)  # pour t=0 c'est 1
        # Vérifier pour t > 0
        for t in [1, max_mag_t]:
            expected_factor = omega**(t * T0)
            inner_sum = S_t_values[t] / expected_factor
            print(f"    t={t}: S_t / ω^{{t·3^{{k-1}}}} = {inner_sum:.4f} (magnitude={abs(inner_sum):.4f})")

# ============================================================
# INVESTIGATION 6 : Pourquoi -1 est spéciale
# Exploiter l'identité 2^S ≡ 3^k mod p
# ============================================================
def investigate_identity_constraint(max_k=12):
    """
    L'identité fondamentale d ≡ 0 mod p ⟺ 2^S ≡ 3^k mod p
    contraint les sommes de la forme Σ w^j · 2^{A_j}.

    En particulier : w^k = (3^{-1})^k = 3^{-k} = 2^{-S} mod p

    Donc les puissances de w et 2 sont LIÉES.
    Explorer cette contrainte.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 6 : Contrainte 2^S ≡ 3^k mod p")
    print("=" * 70)

    for k in range(3, max_k + 1):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue

        p = d
        w = pow(3, -1, p)

        print(f"\n  k={k}: p={p}, S={S}")

        # Identité : 2^S ≡ 3^k mod p
        print(f"    2^S mod p = {pow(2, S, p)}, 3^k mod p = {pow(3, k, p)}")
        assert pow(2, S, p) == pow(3, k, p), "Identité violée !"

        # Conséquence : w·2 a un ordre spécial
        w2 = (w * 2) % p
        ord_w2 = ord_mod(w2, p)
        ord_w_val = ord_mod(w, p)
        ord_2_val = ord_mod(2, p)

        print(f"    w·2 mod p = {w2}, ord(w·2) = {ord_w2}")
        print(f"    ord(w) = {ord_w_val}, ord(2) = {ord_2_val}")

        # (w·2)^S = w^S · 2^S = (3^{-1})^S · 3^k mod p = 3^{k-S} mod p
        w2_S = pow(w2, S, p)
        three_kS = pow(3, k - S, p) if k >= S else pow(pow(3, -1, p), S - k, p)
        print(f"    (w·2)^S mod p = {w2_S}")
        print(f"    3^{{k-S}} mod p = {three_kS}")

        # La somme Σ w^j · 2^{A_j} peut se réécrire avec les exposants relatifs
        # w^j · 2^{A_j} = w^j · 2^{A_j}
        # Si on pose B_j = A_j - j (exposant "excédentaire"), alors
        # w^j · 2^{A_j} = (w·2)^j · 2^{B_j} avec B_j = A_j - j ≥ A_j - j
        # Mais B_j n'est pas nécessairement ≥ 0...

        # Essayons la substitution :
        # Σ_{j=1}^{k-1} w^j · 2^{A_j} = Σ (w·2)^j · 2^{A_j - j}
        # A_j ≥ j (car A_1 ≥ 1, A_2 ≥ 2, ...) OUI si A_j > A_{j-1} et A_0=0
        # En fait A_j ≥ j car les positions sont strictement croissantes à partir de 1

        print(f"\n    Substitution B_j = A_j - j :")
        print(f"    Σ w^j · 2^{{A_j}} = Σ (w·2)^j · 2^{{B_j}}")
        print(f"    avec B_j = A_j - j ≥ 0, et B_j strictement croissant")
        # WAIT: B_j = A_j - j. A_j croissant strict, donc A_j ≥ j
        # Mais B_{j+1} - B_j = (A_{j+1} - (j+1)) - (A_j - j) = A_{j+1} - A_j - 1 ≥ 0
        # Donc B_j est CROISSANT (pas strictement !)
        # B_j ∈ {0, 1, ..., S-1-j} - j = {-j, ..., S-1-2j}
        # Non, B_j = A_j - j ≥ 1 - j pour j=1, ce serait 0
        # A_1 ≥ 1, B_1 = A_1 - 1 ≥ 0
        # A_2 ≥ 2 (car > A_1 ≥ 1), B_2 = A_2 - 2 ≥ 0
        # etc. : B_j ≥ 0 pour tout j
        # B_j est croissant (non-strictly)
        # B_j ≤ S - 1 - j (car A_j ≤ S-1)

        # Calculons l'image avec cette substitution
        u = w2  # u = w·2 mod p
        # Σ_{j=1}^{k-1} u^j · 2^{B_j} avec 0 ≤ B_1 ≤ B_2 ≤ ... ≤ B_{k-1}
        # et B_j ≤ S - 1 - j

        # Vérifier cette reformulation
        n_checked = 0
        n_match = 0
        for combo in combinations(range(1, S), k - 1):
            # combo = (A_1, ..., A_{k-1})
            sigma_original = sum(pow(w, j+1, p) * pow(2, combo[j], p) for j in range(k-1)) % p
            B = tuple(combo[j] - (j+1) for j in range(k-1))
            sigma_new = sum(pow(u, j+1, p) * pow(2, B[j], p) for j in range(k-1)) % p
            if sigma_original == sigma_new:
                n_match += 1
            n_checked += 1
            if n_checked >= 100:
                break

        print(f"    Vérification reformulation : {n_match}/{n_checked} matchs")

# ============================================================
# INVESTIGATION 7 : Automate de Horner réduit mod p
# c_{j+1} = 3·c_j + 2^{A_j} mod p  (j=0..k-1, c_0=1)
# Si corrSum ≡ 0 mod p, alors c_{k} ≡ 0 mod p
# Mais c_k n'est PAS corrSum/d ; c'est corrSum mod p
# Étudier l'automate (c mod p, position_courante) → (c' mod p, position')
# ============================================================
def investigate_horner_mod_p(max_k=10):
    """
    L'automate de Horner mod p : partant de c=1,
    à chaque étape on choisit une position a ∈ {prev+1,...,S-1}
    et on fait c → (3c + 2^a) mod p.

    Après k-1 étapes, on teste si c ≡ 0 mod p.

    Étudier le graphe de transition de cet automate.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 7 : Automate de Horner mod p")
    print("=" * 70)

    for k in range(3, min(max_k + 1, 10)):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue

        p = d

        print(f"\n  k={k}: p={p}, S={S}")

        # BFS couche par couche
        # Couche 0 : {(1, 0)}  [c=1, dernière position utilisée = 0]
        # Couche j : ensemble de (c mod p, dernière position)

        layers = [dict() for _ in range(k)]
        # (c, last_pos) → count
        layers[0][(1, 0)] = 1

        for j in range(k - 1):
            for (c, last_pos), count in layers[j].items():
                for a in range(last_pos + 1, S):
                    c_new = (3 * c + pow(2, a, p)) % p
                    key = (c_new, a)
                    layers[j + 1][key] = layers[j + 1].get(key, 0) + count

        # Couche finale : compter les c ≡ 0
        final_states = layers[k - 1]
        zero_count = sum(cnt for (c, _), cnt in final_states.items() if c == 0)
        total_count = sum(final_states.values())

        # Distribution des c dans la couche finale
        c_dist = defaultdict(int)
        for (c, _), cnt in final_states.items():
            c_dist[c] += cnt

        print(f"    Couche finale : {len(final_states)} états, {total_count} chemins")
        print(f"    N₀(p) = {zero_count}")
        print(f"    |{{c dans couche finale}}| = {len(c_dist)}/{p}")

        # Valeurs de c absentes
        missing_c = sorted(set(range(p)) - set(c_dist.keys()))
        print(f"    c absents : {missing_c}")

        # Analyser la couche intermédiaire (k//2)
        mid = k // 2
        if mid > 0 and mid < k:
            mid_states = layers[mid]
            mid_c_dist = defaultdict(int)
            for (c, _), cnt in mid_states.items():
                mid_c_dist[c] += cnt
            print(f"    Couche {mid} : {len(mid_states)} états, |{{c}}| = {len(mid_c_dist)}/{p}")

        # Propriété clé : existe-t-il un c qui est un "puits" ?
        # c'est-à-dire que 3c + 2^a ≡ 0 mod p pour un a accessible
        # 2^a ≡ -3c mod p
        # a = log_2(-3c mod p)
        print(f"\n    Analyse des transitions vers 0 :")
        for a in range(1, S):
            c_needed = ((-pow(2, a, p)) * pow(3, -1, p)) % p
            # Pour atteindre 0 via position a, on a besoin de c = c_needed
            # Est-ce que c_needed est atteint à la couche k-2 avec last_pos < a ?
            found = False
            if k >= 2 and k-2 < len(layers):
                for (c, last_pos), cnt in layers[k - 2].items():
                    if c == c_needed and last_pos < a:
                        found = True
                        break
            if found:
                print(f"      a={a}: c_needed={c_needed} TROUVÉ en couche {k-2} avec pos < {a}")
            # Only print for small k
            if k <= 5:
                print(f"      a={a}: c_needed={c_needed}, trouvé={found}")

        # Compter combien de positions a POURRAIENT donner c=0
        # si le c_needed était disponible (sans contrainte de position)
        n_potential = 0
        for a in range(1, S):
            c_needed = ((-pow(2, a, p)) * pow(3, -1, p)) % p
            if c_needed in mid_c_dist or c_needed in c_dist:
                n_potential += 1
        print(f"    Positions a avec c_needed ∈ image : {n_potential}/{S-1}")

# ============================================================
# INVESTIGATION 8 : Test crucial — toujours vrai pour d premier ?
# Étendre la vérification à des k plus grands
# ============================================================
def investigate_extended_prime_test(max_k=20):
    """
    Vérifier N₀(p) = 0 pour tous les k où d est premier,
    jusqu'à un max_k élevé. Si on trouve un contre-exemple, le
    prime blocking est FAUX comme théorème général.

    Pour les grands k, on ne peut pas énumérer toutes les compositions.
    On utilise un échantillonnage aléatoire.
    """
    import random
    random.seed(42)

    print("\n" + "=" * 70)
    print("  INVESTIGATION 8 : Test étendu du prime blocking")
    print("=" * 70)

    for k in range(3, max_k + 1):
        S, d, C = compute_params(k)
        if not is_prime(d):
            # Pour d composé, trouver les facteurs premiers
            facts = factorize(d)
            primes_of_d = list(facts.keys())
            print(f"  k={k}: d={d} COMPOSÉ = {' × '.join(f'{p}^{e}' if e > 1 else str(p) for p, e in facts.items())}")
            # Tester N₀(p) pour chaque facteur premier
            for p in primes_of_d:
                if C <= 200000:  # Énumération faisable
                    count = 0
                    for combo in combinations(range(1, S), k - 1):
                        A = (0,) + combo
                        cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k))
                        if cs % p == 0:
                            count += 1
                    print(f"    N₀({p}) = {count}/{C} ({count/C*100:.1f}%)")
                else:
                    # Échantillonnage
                    n_samples = min(50000, C)
                    count = 0
                    for _ in range(n_samples):
                        positions = sorted(random.sample(range(1, S), k - 1))
                        A = (0,) + tuple(positions)
                        cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k))
                        if cs % p == 0:
                            count += 1
                    ratio = count / n_samples
                    print(f"    N₀({p}) ≈ {ratio*100:.2f}% (échantillon {n_samples})")
            continue

        p = d

        if C <= 200000:  # Énumération faisable
            zero_count = 0
            for combo in combinations(range(1, S), k - 1):
                A = (0,) + combo
                cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k))
                if cs % p == 0:
                    zero_count += 1
            print(f"  k={k}: d=p={p} PREMIER, N₀(p) = {zero_count}/{C} {'✅' if zero_count == 0 else '❌ CONTRE-EXEMPLE !'}")
        else:
            # Échantillonnage pour grands k
            n_samples = min(50000, C)
            zero_count = 0
            for _ in range(n_samples):
                positions = sorted(random.sample(range(1, S), k - 1))
                A = (0,) + tuple(positions)
                cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k))
                if cs % p == 0:
                    zero_count += 1
            print(f"  k={k}: d=p={p} PREMIER, N₀(p) ≈ {zero_count}/{n_samples} (échantillon) {'✅' if zero_count == 0 else '⚠️'}")

# ============================================================
# INVESTIGATION 9 : Analyse de l'interaction w-2 dans (Z/pZ)*
# Le sous-groupe ⟨w⟩ et ⟨2⟩ : leur interaction détermine le blocking
# ============================================================
def investigate_w2_interaction(max_k=12):
    """
    Étudier la structure du sous-groupe ⟨w, 2⟩ ⊂ (Z/pZ)*
    et comment elle contraint l'image de Σ w^j · 2^{A_j}.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 9 : Interaction ⟨w⟩ × ⟨2⟩ dans (Z/pZ)*")
    print("=" * 70)

    for k in range(3, max_k + 1):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue

        p = d
        w = pow(3, -1, p)

        ord_w_val = ord_mod(w, p)
        ord_2_val = ord_mod(2, p)

        # ⟨w, 2⟩ engendre quoi ?
        gen = set()
        for i in range(ord_w_val):
            for j in range(ord_2_val):
                gen.add((pow(w, i, p) * pow(2, j, p)) % p)

        print(f"\n  k={k}: p={p}")
        print(f"    ord(w) = {ord_w_val}, ord(2) = {ord_2_val}")
        print(f"    |⟨w, 2⟩| = {len(gen)}, p-1 = {p-1}")
        print(f"    ⟨w, 2⟩ = (Z/pZ)* ? {len(gen) == p - 1}")

        # Les cosets de ⟨2⟩ dans (Z/pZ)*
        # Chaque ligne j de l'alphabet est w^j · ⟨2⟩ ∩ {2^1,...,2^{S-1}}
        # = w^j · {2^1,...,2^{S-1}} mod p

        powers_2 = set()
        for a in range(1, S):
            powers_2.add(pow(2, a, p))

        print(f"    |{{2^a : a=1..S-1}}| = {len(powers_2)}")
        print(f"    ⟨2⟩ = {{2^a : a=0..ord-1}} a {ord_2_val} éléments")
        print(f"    S-1 = {S-1}, ratio (S-1)/ord_2 = {(S-1)/ord_2_val:.3f}")

        # Si S-1 < ord_2, les puissances {2^1,...,2^{S-1}} ne couvrent PAS ⟨2⟩
        # C'est le cas pour k petit !
        if S - 1 < ord_2_val:
            print(f"    ★ S-1 < ord(2) : les puissances de 2 sont INCOMPLÈTES dans ⟨2⟩")
            print(f"      → Chaque ligne de l'alphabet manque des éléments")

        # Pour l'identité w^k ≡ 2^{-S} mod p :
        # Cela signifie que dans le groupe ⟨w, 2⟩, il y a la relation
        # w^k · 2^S = 1 (mod p)
        # Si on écrit w = g^a, 2 = g^b (g générateur de (Z/pZ)*),
        # alors k·a + S·b ≡ 0 mod (p-1)

        # Trouver le logarithme discret de w et 2
        # Pour p petit, on peut utiliser la force brute
        if p < 10000:
            # Trouver un générateur primitif
            g = None
            for candidate in range(2, p):
                if ord_mod(candidate, p) == p - 1:
                    g = candidate
                    break

            if g is not None:
                # log_g(w) et log_g(2)
                log_w = None
                log_2 = None
                val = 1
                for i in range(p - 1):
                    if val == w:
                        log_w = i
                    if val == 2:
                        log_2 = i
                    val = (val * g) % p
                    if log_w is not None and log_2 is not None:
                        break

                if log_w is not None and log_2 is not None:
                    print(f"    g={g} (racine primitive)")
                    print(f"    log_g(w) = {log_w}, log_g(2) = {log_2}")
                    print(f"    Relation : k·log(w) + S·log(2) = {k*log_w + S*log_2} ≡ {(k*log_w + S*log_2) % (p-1)} mod {p-1}")

                    # -1 = g^{(p-1)/2} mod p
                    log_neg1 = (p - 1) // 2
                    print(f"    log_g(-1) = {log_neg1}")

                    # La cible est Σ w^j · 2^{A_j} ≡ -1 mod p
                    # En log : log(Σ ...) ≡ (p-1)/2 mod (p-1)
                    # Mais le log d'une SOMME n'est pas la somme des logs !
                    # Cependant, chaque terme w^j · 2^{A_j} = g^{j·log_w + A_j·log_2}
                    # a un log discret bien défini.

                    # La question est : la SOMME de g^{e_1} + g^{e_2} + ... + g^{e_{k-1}}
                    # peut-elle valoir g^{(p-1)/2} = -1 ?

                    # Exposants possibles des termes :
                    # e(j, a) = j·log_w + a·log_2 mod (p-1)
                    # pour j=1..k-1, a=1..S-1
                    exponents = set()
                    for j in range(1, k):
                        for a in range(1, S):
                            e = (j * log_w + a * log_2) % (p - 1)
                            exponents.add(e)

                    print(f"    |{{exposants e(j,a)}}| = {len(exponents)}/{p-1}")

                    # (p-1)/2 parmi les exposants ?
                    print(f"    (p-1)/2 = {log_neg1} ∈ exposants ? {log_neg1 in exponents}")

# ============================================================
# MAIN
# ============================================================
if __name__ == "__main__":
    print("SESSION 8 — DEEP PRIME BLOCKING INVESTIGATION")
    print("=" * 70)

    investigate_target(max_k=12)
    investigate_alphabet(max_k=12)
    investigate_ordering_constraint(max_k=8)
    investigate_partial_sums(max_k=8)
    investigate_characters(max_k=9)
    investigate_identity_constraint(max_k=12)
    investigate_horner_mod_p(max_k=9)
    investigate_extended_prime_test(max_k=18)
    investigate_w2_interaction(max_k=12)

    print("\n" + "=" * 70)
    print("  INVESTIGATION TERMINÉE")
    print("=" * 70)
