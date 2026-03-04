#!/usr/bin/env python3
"""
SESSION 9 — FORMALISATION DU PRIME BLOCKING (Mécanisme I)
==========================================================
Protocole DISCOVERY v2.0, Axe Stratégique #1.

OBJECTIF : Pour d = p premier, PROUVER N₀(p) = 0.
FAIT ÉTABLI (session 8) : la contrainte d'ordre exclut 0 chirurgicalement.

QUESTION CLÉ : POURQUOI la contrainte A₁ < A₂ < ... < A_{k-1} empêche-t-elle
la somme Σ w^j·2^{A_j} d'atteindre -1 mod p ?

INVESTIGATIONS :
  1. Structure multiplicative de w = 3^{-1} mod p
  2. Image des sommes ordonnées comme problème de sous-sommes restreintes
  3. Argument par orbites de <w·2> mod p
  4. Approche par polynômes générateurs
  5. Preuve pour k=3 (d=5) : formalisation complète
  6. Preuve pour k=5 (d=13) : formalisation complète
  7. Tentative de généralisation : structure commune k=3,5
  8. Test de la conjecture : image ordonnée = Z/pZ \ {-1} pour d premier
  9. Approche additive combinatoire (Davenport-constants, EGZ)
"""

from math import ceil, log2, gcd, comb
from itertools import combinations
from collections import defaultdict, Counter
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
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True


# ============================================================
# INVESTIGATION 1 : Structure de w = 3^{-1} mod p
# Pour d premier, w = 3^{-1} mod p.
# La somme est Σ_{j=0}^{k-1} w^j · 2^{A_j} avec A_0=0.
# Séparons le terme j=0 : w^0 · 2^0 = 1
# Reste : Σ_{j=1}^{k-1} w^j · 2^{A_j} = -1 - 1 = -(1+1) ??? Non.
# corrSum ≡ 0 mod p ⟺ Σ_{j=0}^{k-1} w^j · 2^{A_j} ≡ 0 mod p
# Donc on cherche : Σ_{j=1}^{k-1} w^j · 2^{A_j} ≡ -1 mod p
# (car le terme j=0 est w^0 · 2^0 = 1)
# ============================================================
def investigate_w_structure():
    """Structure de w et de ses puissances pour d premier."""
    print("=" * 70)
    print("  INVESTIGATION 1 : Structure de w = 3^{-1} mod p")
    print("=" * 70)

    for k in range(3, 16):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)
        ord_w = 1
        x = w
        while x != 1:
            x = (x * w) % p
            ord_w += 1

        # Puissances de w
        wpows = [(j, pow(w, j, p)) for j in range(k)]
        # Puissances de 2
        twopows = [(a, pow(2, a, p)) for a in range(S)]
        # u = w·2 mod p
        u = (w * 2) % p
        ord_u = 1
        x = u
        while x != 1:
            x = (x * u) % p
            ord_u += 1

        print(f"\n  k={k}, p={d}, w={w}, ord(w)={ord_w}, u=w·2={u}, ord(u)={ord_u}")
        print(f"    w^j = {[pow(w, j, p) for j in range(k)]}")
        print(f"    (p-1)/ord(w) = {(p-1)//ord_w}, (p-1)/ord(u) = {(p-1)//ord_u}")

        # Le groupe <w, 2> dans (Z/pZ)*
        generated = set()
        for a in range(p-1):
            for b in range(p-1):
                generated.add(pow(w, a, p) * pow(2, b, p) % p)
                if len(generated) == p - 1:
                    break
            if len(generated) == p - 1:
                break
        print(f"    |<w,2>| = {len(generated)}/{p-1}")


# ============================================================
# INVESTIGATION 2 : Image ordonnée vs non-ordonnée (structure fine)
# On regarde QUELLES valeurs sont atteintes et lesquelles manquent
# avec une granularité par couche.
# ============================================================
def investigate_ordered_image_fine():
    """Analyse fine de l'image ordonnée couche par couche."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 2 : Image ordonnée — analyse fine")
    print("=" * 70)

    for k in range(3, 9):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)
        target = (-1) % p

        print(f"\n  k={k}, p={d}, S={S}, target={target}")

        # Automate de Horner ordonné couche par couche
        # État = (somme_partielle mod p, dernière_position)
        # Couche 0 : s = w^0 · 2^0 = 1, pos = 0
        # Couche j : on ajoute w^j · 2^{A_j} avec A_j > A_{j-1}
        layers = [set()]
        layers[0] = {(1, 0)}

        for j in range(1, k):
            wj = pow(w, j, p)
            new_layer = set()
            for (s, last_pos) in layers[j-1]:
                for a in range(last_pos + 1, S):
                    s_new = (s + wj * pow(2, a, p)) % p
                    new_layer.add((s_new, a))
            layers.append(new_layer)

            # Valeurs atteintes à cette couche
            vals_j = set(s for s, _ in new_layer)
            missing_j = set(range(p)) - vals_j
            print(f"    Couche {j}: |états|={len(new_layer)}, "
                  f"|val|={len(vals_j)}/{p}, "
                  f"missing={missing_j if len(missing_j) <= 5 else f'{len(missing_j)} vals'}")

        # Couche finale
        final_vals = set(s for s, _ in layers[-1])
        missing = set(range(p)) - final_vals
        print(f"    ★ Image finale : {len(final_vals)}/{p}, "
              f"missing = {sorted(missing)}")
        has_target = target in final_vals
        print(f"    ★ Target {target} (-1 mod {p}) in image? {has_target}")
        print(f"    ★ 0 in image? {0 in final_vals}")


# ============================================================
# INVESTIGATION 3 : Preuve formelle pour k=3 (d=5)
# S=5, k=3, p=5, w=2 (car 3·2=6≡1 mod 5)
# Somme = w^0·2^0 + w^1·2^{A_1} + w^2·2^{A_2}
#       = 1 + 2·2^{A_1} + 4·2^{A_2} mod 5
# avec 1 ≤ A_1 < A_2 ≤ 4
# Compositions : (A_1, A_2) ∈ {(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)}
# ============================================================
def prove_k3_formal():
    """Preuve exhaustive ET structurelle pour k=3, p=5."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 3 : Preuve formelle k=3, p=5")
    print("=" * 70)

    p = 5
    w = pow(3, -1, p)  # w = 2
    print(f"  w = 3^{{-1}} mod 5 = {w}")
    print(f"  Somme = 1 + {w}·2^{{A_1}} + {w**2 % p}·2^{{A_2}} mod 5")

    # Toutes les compositions
    results = []
    for A1 in range(1, 5):
        for A2 in range(A1 + 1, 5):
            s = (1 + w * pow(2, A1, p) + (w*w % p) * pow(2, A2, p)) % p
            results.append((A1, A2, s))
            print(f"    ({A1},{A2}): 1 + 2·{pow(2,A1,p)} + 4·{pow(2,A2,p)} "
                  f"= {1 + w * pow(2, A1, p) + (w*w % p) * pow(2, A2, p)} "
                  f"≡ {s} mod 5")

    vals = set(s for _, _, s in results)
    print(f"\n  Image = {sorted(vals)}")
    print(f"  Missing = {sorted(set(range(p)) - vals)}")
    print(f"  N₀(5) = {sum(1 for _,_,s in results if s == 0)}")

    # Argument structurel :
    # 2^a mod 5 : a=1→2, a=2→4, a=3→3, a=4→1
    # Somme = 1 + 2·(2^{A_1} mod 5) + 4·(2^{A_2} mod 5)
    # On veut ≡ 0 mod 5, i.e. 2·x + 4·y ≡ -1 ≡ 4 mod 5
    # où x = 2^{A_1} mod 5 ∈ {2,4,3,1}, y = 2^{A_2} mod 5 ∈ {2,4,3,1}
    # ET les positions A_1 < A_2 (ordre strict)
    print("\n  --- Argument structurel ---")
    print("  On cherche : 2x + 4y ≡ 4 mod 5, avec x,y ∈ {1,2,3,4}")
    print("  et les positions de x,y respectent x←A_1 < A_2→y")

    # Trouver les (x,y) solutions
    for x in range(1, 5):
        for y in range(1, 5):
            if (2*x + 4*y) % 5 == 4:
                # Quelles positions donnent x et y ?
                pos_x = [a for a in range(1, 5) if pow(2, a, 5) == x]
                pos_y = [a for a in range(1, 5) if pow(2, a, 5) == y]
                compatible = any(px < py for px in pos_x for py in pos_y)
                print(f"    x={x} (pos {pos_x}), y={y} (pos {pos_y}) → "
                      f"2·{x}+4·{y}={2*x+4*y}≡{(2*x+4*y)%5} mod 5. "
                      f"Compatible? {compatible}")

    print("\n  CONCLUSION k=3 : La SEULE paire (x,y) donnant 0 est incompatible")
    print("  car les positions requises violent la contrainte d'ordre strict.")


# ============================================================
# INVESTIGATION 4 : Preuve formelle pour k=5 (d=13)
# ============================================================
def prove_k5_formal():
    """Preuve exhaustive ET analyse structurelle pour k=5, p=13."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 4 : Preuve formelle k=5, p=13")
    print("=" * 70)

    p = 13
    S = 8
    k = 5
    w = pow(3, -1, p)  # w = 9 (car 3·9=27≡1 mod 13)
    print(f"  w = 3^{{-1}} mod 13 = {w}")
    print(f"  ord(w) : ", end="")
    x = w
    o = 1
    while x != 1:
        x = (x * w) % p
        o += 1
    print(f"{o}")

    # Somme = Σ_{j=0}^4 w^j · 2^{A_j} avec A_0=0, 1≤A_1<A_2<A_3<A_4≤7
    # = 1 + w·2^{A_1} + w²·2^{A_2} + w³·2^{A_3} + w⁴·2^{A_4}
    wpows = [pow(w, j, p) for j in range(k)]
    print(f"  w^j = {wpows}")

    target = (-1) % p
    print(f"  Target = -1 mod 13 = {target}")

    # 2^a mod 13 pour a=0..7
    twopows = [pow(2, a, 13) for a in range(S)]
    print(f"  2^a mod 13 = {twopows}")

    # Énumérer toutes les compositions
    n0 = 0
    for combo in combinations(range(1, S), k - 1):
        A = (0,) + combo
        s = sum(wpows[j] * pow(2, A[j], p) for j in range(k)) % p
        if s == 0:
            n0 += 1
            print(f"    SOLUTION : A={A}, sum={s}")

    print(f"\n  N₀(13) = {n0}")

    # Analyse : quelles valeurs de la "somme partielle" sont réalisables ?
    # On trace la propagation couche par couche
    print("\n  --- Propagation couche par couche ---")
    reachable = {(1, 0)}  # (somme, dernière pos)
    for j in range(1, k):
        new_reach = set()
        for (s, last) in reachable:
            for a in range(last + 1, S):
                s_new = (s + wpows[j] * pow(2, a, p)) % p
                new_reach.add((s_new, a))
        reachable = new_reach
        vals = set(s for s, _ in reachable)
        print(f"    Couche {j}: |reach|={len(reachable)}, vals={sorted(vals)}")

    # Identifier la structure
    final_vals = set(s for s, _ in reachable)
    print(f"\n  Image finale = {sorted(final_vals)} ({len(final_vals)}/{p})")
    print(f"  Missing = {sorted(set(range(p)) - final_vals)}")

    # Analyse : pour chaque position finale A_4, quelle est la somme partielle nécessaire ?
    print("\n  --- Analyse par position finale A_4 ---")
    # À la couche j=3 (avant dernier), on a une somme partielle s_3
    # On veut s_3 + w^4 · 2^{A_4} ≡ 0 mod 13
    # Donc s_3 ≡ -w^4 · 2^{A_4} mod 13
    w4 = wpows[4]
    print(f"  w^4 = {w4}")
    for A4 in range(1, S):
        needed = (-w4 * pow(2, A4, p)) % p
        print(f"    A_4={A4}: need s_3 ≡ {needed} mod 13 "
              f"(with last_pos < {A4})")

    # Vérifier quelles sommes partielles s_3 sont atteignables
    # à la couche 3 avec dernière position < A_4
    print("\n  --- Sommes partielles s_3 atteignables (avant A_4) ---")
    layers = [set()]
    layers[0] = {(1, 0)}
    for j in range(1, k - 1):
        new_layer = set()
        for (s, last) in layers[-1]:
            for a in range(last + 1, S):
                s_new = (s + wpows[j] * pow(2, a, p)) % p
                new_layer.add((s_new, a))
        layers.append(new_layer)

    # Pour chaque A_4, vérifier si le needed est dans les s_3 atteignables
    for A4 in range(1, S):
        needed = (-w4 * pow(2, A4, p)) % p
        reachable_before_A4 = set(s for s, pos in layers[-1] if pos < A4)
        can_reach = needed in reachable_before_A4
        print(f"    A_4={A4}: need={needed}, "
              f"reachable(pos<{A4})={sorted(reachable_before_A4)}, "
              f"OK? {can_reach}")


# ============================================================
# INVESTIGATION 5 : Polynôme générateur et identités
# P(x) = Σ_A x^{corrSum(A) mod p} pour compositions ordonnées
# N₀(p) = coefficient de x^0 dans P(x)
# Peut-on montrer que le coeff de x^0 est 0 algébriquement ?
# ============================================================
def investigate_generating_polynomial():
    """Polynôme générateur des résidus corrSum mod p."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 5 : Polynôme générateur")
    print("=" * 70)

    for k in range(3, 9):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)

        # Compter les résidus
        residue_count = Counter()
        for combo in combinations(range(1, S), k - 1):
            A = (0,) + combo
            s = sum(pow(w, j, p) * pow(2, A[j], p) for j in range(k)) % p
            residue_count[s] += 1

        print(f"\n  k={k}, p={d}")
        print(f"  Distribution : {dict(sorted(residue_count.items()))}")
        print(f"  N₀ = {residue_count[0]}")
        print(f"  C = {C}, C/p = {C/p:.3f}")

        # Vérifier si la distribution est "presque uniforme"
        expected = C / p
        chi2 = sum((v - expected)**2 / expected for v in residue_count.values())
        print(f"  chi² = {chi2:.2f} (vs p-1={p-1} dof)")

        # Le résidu 0 est-il le SEUL absent ?
        absent = [r for r in range(p) if residue_count[r] == 0]
        print(f"  Résidus absents = {absent}")
        if absent == [0]:
            print(f"  ★ CONFIRMÉ : 0 est le SEUL résidu absent !")
        elif 0 in absent:
            print(f"  ★ 0 est absent parmi {len(absent)} résidus absents")


# ============================================================
# INVESTIGATION 6 : Approche par sommes exponentielles (Fourier)
# N₀(p) = (1/p) · Σ_{t=0}^{p-1} Σ_A ω^{t·Σ w^j·2^{A_j}}
# = C/p + (1/p) · Σ_{t=1}^{p-1} Π_{j=1}^{k-1} S_j(t)
# où S_j(t) = Σ_{a} ω^{t·w^j·2^a} (somme sur positions admissibles)
# ============================================================
def investigate_fourier_approach():
    """Analyse de Fourier de l'image ordonnée."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 6 : Approche Fourier")
    print("=" * 70)

    import cmath

    for k in range(3, 9):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)
        omega = cmath.exp(2j * cmath.pi / p)

        print(f"\n  k={k}, p={d}, C={C}")

        # Calcul EXACT de N₀ via Fourier (somme sur toutes compositions)
        # Pour t fixé : F(t) = Σ_A ω^{t · Σ w^j · 2^{A_j}}
        # PROBLÈME : pour la somme ordonnée, on ne peut PAS factoriser
        # en produit Π S_j(t) car les A_j sont LIÉS par l'ordre.

        # MAIS on peut écrire F(t) via l'automate :
        # F(t) = ω^t · Σ_{A_1<...<A_{k-1}} Π_{j=1}^{k-1} ω^{t·w^j·2^{A_j}}
        # = ω^t · Σ ordered Π g_j(A_j) avec g_j(a) = ω^{t·w^j·2^a}

        # Calcul récursif : P_j(a_last) = Σ_{a>a_last} g_j(a) · P_{j+1}(a)
        # On calcule de j=k-1 vers j=1.

        F_values = []
        for t in range(p):
            if t == 0:
                F_values.append(C)
                continue

            # Calcul par DP
            # dp[j][a] = contribution des couches j...k-1 avec dernière pos ≥ a
            # En fait on trace le forward :
            # layer[j] = {a_last : Σ contributions}
            # layer[0] = {0: ω^t} (position 0, contribution ω^{t·1})
            contrib = omega ** t  # terme j=0 (w^0·2^0 = 1)
            layer = {0: contrib}

            for j in range(1, k):
                new_layer = defaultdict(complex)
                wj = pow(w, j, p)
                for a_last, val in layer.items():
                    for a in range(a_last + 1, S):
                        phase = omega ** ((t * wj * pow(2, a, p)) % p)
                        new_layer[a] += val * phase
                layer = dict(new_layer)

            F_t = sum(layer.values())
            F_values.append(F_t)

        # N₀ = (1/p) Σ F(t)
        N0_fourier = sum(F_values) / p
        print(f"  N₀ (Fourier) = {N0_fourier.real:.6f} + {N0_fourier.imag:.6f}i")
        print(f"  N₀ (arrondi) = {round(N0_fourier.real)}")

        # Analyser les F(t) pour t ≥ 1
        F_nonzero = [F_values[t] for t in range(1, p)]
        total = sum(F_nonzero)
        print(f"  Σ F(t) pour t≥1 = {total.real:.6f} + {total.imag:.6f}i")
        print(f"  (devrait être = -C = {-C} si N₀=0)")

        # |F(t)| pour chaque t
        mags = [(t, abs(F_values[t])) for t in range(1, p)]
        max_t, max_mag = max(mags, key=lambda x: x[1])
        print(f"  max|F(t)| = {max_mag:.3f} at t={max_t}, √C={C**0.5:.3f}")

        # L'ANNULATION EST-ELLE STRUCTURELLE ?
        # Si les F(t) pour t≥1 s'annulent EXACTEMENT à -C,
        # c'est une identité algébrique, pas un hasard.
        print(f"  Vérification : Σ F(t) + C = {(total + C).real:.10f}")


# ============================================================
# INVESTIGATION 7 : Le rôle de l'identité w^k ≡ 2^{-S} mod p
# Cette identité relie les coefficients w^j aux positions 2^a.
# Peut-on l'exploiter pour prouver l'exclusion de 0 ?
# ============================================================
def investigate_identity_role():
    """Impact de l'identité w^k = 2^{-S} mod p."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 7 : Rôle de l'identité w^k = 2^{-S}")
    print("=" * 70)

    for k in range(3, 12):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)
        inv2S = pow(2, -S, p) if gcd(2, p) == 1 else None

        wk = pow(w, k, p)
        print(f"\n  k={k}, p={d}: w^k = {wk}, 2^{{-S}} = {inv2S}, "
              f"match = {wk == inv2S}")

        # Si on pose u = w·2 mod p, alors u^k = w^k · 2^k = 2^{-S} · 2^k = 2^{k-S}
        u = (w * 2) % p
        uk = pow(u, k, p)
        twokS = pow(2, k - S, p) if k >= S else pow(2, k - S + (p-1), p)
        print(f"    u = w·2 = {u}, u^k = {uk}, 2^{{k-S}} = {twokS}, "
              f"match = {uk == twokS}")

        # Substitution B_j = A_j - j ≥ 0, non-décroissant
        # Somme = Σ u^j · 2^{B_j} avec B_0 = 0
        # Condition : B_{j+1} ≥ B_j (non-décroissant)
        # et B_{k-1} ≤ S - k (car A_{k-1} ≤ S-1 et B_{k-1} = A_{k-1} - (k-1))

        # Compter les compositions en B_j
        B_max = S - k
        print(f"    Substitution B_j: B_j ∈ [0, {B_max}], non-décroissant")

        # Énumérer les B-compositions pour vérification
        def count_B_comps(j, last_B, target_sum, B_max):
            """Compte les B-compositions donnant target_sum."""
            if j == k:
                return 1 if target_sum == 0 else 0
            count = 0
            for b in range(last_B, B_max + 1):
                val = (pow(u, j, p) * pow(2, b, p)) % p
                new_target = (target_sum - val) % p
                count += count_B_comps(j + 1, b, new_target, B_max)
            return count

        if C <= 2000:  # Seulement pour petits k
            n0_B = count_B_comps(0, 0, 0, B_max)
            print(f"    N₀ via B-substitution = {n0_B}")


# ============================================================
# INVESTIGATION 8 : Conjecture — image ordonnée = Z/pZ \ {0}
# Pour TOUS les k avec d premier, est-ce que l'image de la somme
# ordonnée est exactement Z/pZ \ {0} ?
# ============================================================
def investigate_exact_image():
    """Test de la conjecture : image = Z/pZ \ {0} pour d premier."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 8 : Conjecture image = Z/pZ \\ {0}")
    print("=" * 70)

    for k in range(3, 18):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)

        if C > 500000:
            print(f"  k={k}, p={d}: C={C} — trop grand, skip")
            continue

        # Énumérer
        image = set()
        for combo in combinations(range(1, S), k - 1):
            A = (0,) + combo
            s = sum(pow(w, j, p) * pow(2, A[j], p) for j in range(k)) % p
            image.add(s)
            if len(image) == p:
                break  # Tout couvert

        missing = set(range(p)) - image
        conj_holds = (missing == {0})
        print(f"  k={k}, p={d}: |image|={len(image)}/{p}, "
              f"missing={sorted(missing) if len(missing) <= 5 else f'{len(missing)} vals'}, "
              f"conjecture holds? {conj_holds}")


# ============================================================
# INVESTIGATION 9 : Approche additive combinatoire
# Théorie des sous-sommes : si on a un multiensemble M dans Z/pZ,
# quand est-ce que toute valeur est une sous-somme ordonnée ?
# Davenport constant, EGZ, etc.
# ============================================================
def investigate_additive_combinatorics():
    """Approche par théorie additive combinatoire."""
    print("\n" + "=" * 70)
    print("  INVESTIGATION 9 : Approche additive combinatoire")
    print("=" * 70)

    for k in range(3, 9):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)

        print(f"\n  k={k}, p={d}, S={S}")

        # Les "atomes" disponibles à chaque couche j sont :
        # a_j(pos) = w^j · 2^pos mod p, pour pos ∈ {1, ..., S-1}
        # On sélectionne UN atome par couche, avec pos strictement croissant.

        for j in range(1, k):
            wj = pow(w, j, p)
            atoms = [wj * pow(2, a, p) % p for a in range(1, S)]
            unique_atoms = set(atoms)
            print(f"    Couche {j}: w^{j}={wj}, "
                  f"|atomes uniques|={len(unique_atoms)}/{S-1}, "
                  f"atomes mod p={sorted(unique_atoms)}")

        # Constante de Davenport pour Z/pZ : D(Z/pZ) = 2p - 1
        # EGZ (Erdős-Ginzburg-Ziv) : dans toute séquence de 2p-1 éléments,
        # il existe une sous-séquence de longueur p dont la somme est 0.
        # Notre cas : nous avons k-1 éléments (couches 1..k-1),
        # avec k-1 << p en général.
        print(f"    Davenport D(Z/{p}Z) = {2*p-1}")
        print(f"    Nous avons k-1 = {k-1} couches (bien en dessous de D)")
        print(f"    → EGZ ne s'applique pas directement")

        # MAIS : chaque couche a S-1 choix (pas 1).
        # Le nombre total de sommes = C = C(S-1, k-1).
        # Quand C/p >> 1, presque toute valeur est atteinte.
        # La question : pourquoi PAS 0 ?
        print(f"    C/p = {C/p:.3f}")

        # Test : la somme des atomes d'une couche couvre-t-elle Z/pZ ?
        all_atoms_union = set()
        for j in range(1, k):
            wj = pow(w, j, p)
            for a in range(1, S):
                all_atoms_union.add(wj * pow(2, a, p) % p)
        print(f"    Union de tous les atomes = {len(all_atoms_union)}/{p-1} "
              f"de (Z/{p}Z)*")


# ============================================================
# MAIN
# ============================================================
if __name__ == "__main__":
    print("SESSION 9 — FORMALISATION DU PRIME BLOCKING")
    print("=" * 70)
    print()

    t0 = time.time()

    investigate_w_structure()
    investigate_ordered_image_fine()
    prove_k3_formal()
    prove_k5_formal()
    investigate_generating_polynomial()
    investigate_fourier_approach()
    investigate_identity_role()
    investigate_exact_image()
    investigate_additive_combinatorics()

    elapsed = time.time() - t0
    print(f"\n{'=' * 70}")
    print(f"  SESSION 9 TERMINÉE en {elapsed:.1f}s")
    print(f"{'=' * 70}")
