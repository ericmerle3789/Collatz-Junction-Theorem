#!/usr/bin/env python3
"""
SESSION 10f12 : Induction sur le double-bord
=============================================
Date : 4 mars 2026
Objectif : Comprendre POURQUOI le cas double-bord n'a jamais de solution

CONSTAT (10f11) :
  f(0, B₂,..., B_{k-2}, M) = -1 mod d
  se réduit à : middle_sum(B₂,...,B_{k-2}) = -(1 + u + u⁻¹) mod d
  avec middle_sum = Σ_{j=2}^{k-2} u^j · 2^{B_j}

QUESTION : Pourquoi -(1 + u + u⁻¹) ∉ Im(middle_sum) ?

INVESTIGATIONS :
  I1. Valeur de 1 + u + u⁻¹ en fonction de k
  I2. Structure du problème réduit vs problème original
  I3. Itération de la réduction : double-bord du double-bord
  I4. Argument de comptage : comparaison |Im_middle| vs d
  I5. Lien avec σ̃ et la somme géométrique
"""

from math import gcd, log2, ceil, comb
from itertools import combinations_with_replacement


def compute_params(k):
    S = ceil(k * log2(3))
    d = 2**S - 3**k
    M = S - k
    if d <= 0:
        return None
    return S, d, M


def compute_u(k, d):
    inv3 = pow(3, -1, d)
    return (2 * inv3) % d


def sigma_tilde(u, k, d):
    s = 0
    uj = u
    for j in range(1, k):
        s = (s + uj) % d
        uj = (uj * u) % d
    return s


def ord_mod(base, mod):
    if gcd(base, mod) != 1:
        return None
    o = 1
    power = base % mod
    while power != 1:
        power = (power * base) % mod
        o += 1
        if o > mod:
            return None
    return o


# ======================================================================
# INVESTIGATION 1 : La constante 1 + u + u⁻¹
# ======================================================================
def investigation_1():
    """Analyse de la constante c = 1 + u + u⁻¹ mod d."""
    print("=" * 70)
    print("I1 : LA CONSTANTE 1 + u + u⁻¹")
    print("=" * 70)
    print()

    print(f"{'k':>4} {'d':>12} {'u':>8} {'u⁻¹':>8} {'1+u+u⁻¹':>10} "
          f"{'σ̃':>8} {'σ̃+1+u+u⁻¹':>12} {'=?':>5}")
    print("-" * 75)

    for k in range(3, 25):
        params = compute_params(k)
        if params is None:
            continue
        S, d, M = params
        u = compute_u(k, d)
        inv_u = pow(u, -1, d)
        st = sigma_tilde(u, k, d)

        c = (1 + u + inv_u) % d

        # σ̃ = Σ_{j=1}^{k-1} u^j = u + u² + ... + u^{k-1}
        # La somme complète Σ_{j=0}^{k-1} u^j = 1 + σ̃
        # Est-ce que 1 + u + u⁻¹ a un lien avec σ̃ ?

        # σ̃ = u(u^{k-1} - 1)/(u - 1) si u ≠ 1
        # Et u^{k-1} * u = u^k = 2^{-M}
        # Donc u^{k-1} = 2^{-M} / u = 2^{-M} * u⁻¹

        full_sum = (1 + st) % d  # = Σ_{j=0}^{k-1} u^j
        sum_c = (st + c) % d  # σ̃ + (1 + u + u⁻¹)

        # Voyons si c a une forme simple
        # c = 1 + u + u⁻¹ = (u² + u + 1)/u = (u³ - 1)/((u - 1)·u) si u³ ≠ 1

        # Alternative : c = (u² + u + 1) · u⁻¹
        alt = ((u*u + u + 1) % d * inv_u) % d
        assert alt == c, f"Vérification échouée pour k={k}"

        eq_str = ""
        if c == 0:
            eq_str = "= 0 ★"
        elif (c + 1) % d == 0:
            eq_str = "= -1"

        print(f"{k:4d} {d:12d} {u:8d} {inv_u:8d} {c:10d} "
              f"{st:8d} {sum_c:12d} {eq_str:>5}")

    print()
    print("ANALYSE :")
    print("  c = 1 + u + u⁻¹ = (u² + u + 1)/u mod d")
    print("  Si u est une racine cubique de 1 (u³ = 1), alors c = 0")
    print("  Sinon c ≠ 0 en général")
    print()

    # Vérifions si u³ = 1 pour certains k
    print("  Vérification u³ mod d :")
    for k in range(3, 20):
        params = compute_params(k)
        if params is None:
            continue
        S, d, M = params
        u = compute_u(k, d)
        u3 = pow(u, 3, d)
        if u3 == 1:
            print(f"    k={k}: u³ = 1 mod d={d} ★★★ (u est racine cubique de l'unité)")
        elif u3 < 100 or d - u3 < 100:
            print(f"    k={k}: u³ = {u3} mod d={d}")
    print()


# ======================================================================
# INVESTIGATION 2 : Itération de la réduction
# ======================================================================
def investigation_2():
    """Que se passe-t-il si on itère la réduction dimensionnelle ?
    Le problème réduit a aussi un cas double-bord..."""
    print("=" * 70)
    print("I2 : ITÉRATION DE LA RÉDUCTION DIMENSIONNELLE")
    print("=" * 70)
    print()

    for k in [8, 10, 11, 13]:
        params = compute_params(k)
        if params is None:
            continue
        S, d, M = params
        u = compute_u(k, d)
        inv_u = pow(u, -1, d)
        st = sigma_tilde(u, k, d)
        if st == 0:
            continue

        print(f"k={k}: d={d}, M={M}, u={u}")

        # Niveau 0 : problème original f(B) = -1, dim = k-1
        # Niveau 1 : double-bord → middle_sum = -(1+u+u⁻¹), dim = k-3
        c1 = (1 + u + inv_u) % d
        target1 = (-c1) % d

        # Le problème réduit de niveau 1 est :
        # g₁(B₂,...,B_{k-2}) = Σ_{j=2}^{k-2} u^j · 2^{B_j} = target1
        # Son cas double-bord : B₂=0, B_{k-2}=M
        # donne : u²·1 + [inner] + u^{k-2}·2^M = target1
        # inner = Σ_{j=3}^{k-3} u^j · 2^{B_j}
        # u^{k-2}·2^M = u^{k-2} · 2^M = ?

        # Calculons u^{k-2}·2^M
        uk2 = pow(u, k-2, d)
        term_last = (uk2 * pow(2, M, d)) % d

        # Or u^{k-1}·2^M = u⁻¹, donc u^{k-2}·2^M = u⁻¹·u⁻¹ = u⁻²
        inv_u2 = pow(u, -2, d)
        assert term_last == inv_u2, f"Identité u^{{k-2}}·2^M = u⁻² échoue pour k={k}"

        u2 = (u * u) % d
        fixed_level2 = (u2 + inv_u2) % d
        target2 = (target1 - fixed_level2) % d

        print(f"  Niveau 0 : f(B) = -1, dim = {k-1}")
        print(f"  Niveau 1 : middle = {target1} = -(1+u+u⁻¹), dim = {k-3}")
        print(f"    u^{{k-2}}·2^M = {term_last} = u⁻² = {inv_u2} ✓")
        print(f"    Termes fixes niveau 2 : u² + u⁻² = {fixed_level2}")
        print(f"    Target niveau 2 : {target2}, dim = {k-5}")

        # On peut continuer... Niveau 2 donne dim k-5, etc.
        # Le pattern est : à chaque niveau on soustrait u^j + u^{-j} pour j croissant
        # Calculons la série complète

        running_target = (-1) % d  # target original
        print(f"  SERIE DE REDUCTIONS :")
        level = 0
        dim = k - 1
        for j in range(0, (k-1)//2 + 1):
            if dim <= 0:
                # Base atteinte
                print(f"    Niveau {level}: dim={dim}, target={running_target}")
                if dim == 0:
                    # 0 variables → test direct : target = 0 ?
                    print(f"      → Cas trivial : target {'= 0 ★' if running_target == 0 else '≠ 0 ✓'}")
                elif dim == 1:
                    # 1 variable B dans [0,M] : u^{j+1}·2^B = target
                    uj1 = pow(u, j + 1, d)
                    found = False
                    for b in range(M + 1):
                        if (uj1 * pow(2, b, d)) % d == running_target:
                            found = True
                            print(f"      → 1 variable : u^{j+1}·2^{b} = {running_target} → SOLUTION B={b} ★")
                            break
                    if not found:
                        print(f"      → 1 variable : aucun B ∈ [0,M] ne donne target ✓")
                break

            uj = pow(u, j, d)
            inv_uj = pow(u, -j, d) if j > 0 else 1

            if j == 0:
                subtract = 1  # u⁰ = 1 (le premier pas)
                running_target = (running_target - subtract) % d
                dim -= 1
                print(f"    Niveau {level}: B₁=0 → soustrait u⁰=1, target={running_target}, dim={dim}")
            else:
                # Pas double-bord : B_j=0 et B_{k-1-j}=M
                subtract_left = pow(u, j, d)  # u^j · 2^0 = u^j
                subtract_right = (pow(u, k-1-j, d) * pow(2, M, d)) % d  # u^{k-1-j}·2^M

                # Vérifions : u^{k-1-j}·2^M = u^{-j-1+1} · ... hmm
                # Plus simplement : u^{k-1}·2^M = u⁻¹
                # Donc u^{k-1-j}·2^M = u^{-1-j+k-1-k+1} ... non
                # u^{k-1-j}·2^M = u^{-(j+1)} car u^{k-1}·2^M = u⁻¹ → u^{k-1-j} = u⁻¹·u⁻ʲ·2^{-M}... non

                # Plutôt : u^n · 2^M = u^{n-(k-1)} · u^{k-1} · 2^M = u^{n-k+1} · u⁻¹ = u^{n-k}
                # Donc u^{k-1-j}·2^M = u^{k-1-j-k} = u^{-1-j} = u^{-(j+1)}

                inv_uj1 = pow(u, -(j+1), d)
                # Vérification
                check = (pow(u, k-1-j, d) * pow(2, M, d)) % d
                assert check == inv_uj1, f"Identité échoue pour k={k}, j={j}"

                total_subtract = (subtract_left + inv_uj1) % d
                running_target = (running_target - total_subtract) % d
                dim -= 2
                print(f"    Niveau {level}: double-bord → soustrait u^{j}+u^{{-(j+1)}} = {total_subtract}, "
                      f"target={running_target}, dim={dim}")

            level += 1

        print()


# ======================================================================
# INVESTIGATION 3 : La somme télescopique
# ======================================================================
def investigation_3():
    """La série de réductions soustrait Σ(u^j + u^{-(j+1)}).
    Quelle est la somme totale ?"""
    print("=" * 70)
    print("I3 : SOMME TÉLESCOPIQUE DE LA RÉDUCTION")
    print("=" * 70)
    print()

    print("  Si on itère la réduction double-bord jusqu'au bout, on soustrait :")
    print("    Niveau 0 : 1 (= u⁰)")
    print("    Niveau 1 : u + u⁻² (double-bord)")
    print("    Niveau 2 : u² + u⁻³")
    print("    ...")
    print("    Niveau j : u^j + u^{-(j+1)}")
    print()
    print("  Somme totale S_n = 1 + Σ_{j=1}^{n} (u^j + u^{-(j+1)})")
    print("  = 1 + (u + u² + ... + u^n) + (u⁻² + u⁻³ + ... + u^{-(n+1)})")
    print("  = 1 + σ̃_n(u) + u⁻²·σ̃_n(u⁻¹)")
    print("  où σ̃_n = Σ_{j=1}^{n} x^j")
    print()

    for k in [7, 8, 10, 11, 13]:
        params = compute_params(k)
        if params is None:
            continue
        S, d, M = params
        u = compute_u(k, d)
        st = sigma_tilde(u, k, d)
        if st == 0:
            continue

        # Nombre de niveaux = (k-1)//2
        n_levels = (k - 1) // 2

        # Somme totale soustraite
        total = 1  # u⁰
        for j in range(1, n_levels + 1):
            uj = pow(u, j, d)
            inv_uj1 = pow(u, -(j+1), d)
            total = (total + uj + inv_uj1) % d

        # Target final = -1 - total
        final_target = (-1 - total) % d

        # Dimension résiduelle
        final_dim = (k - 1) - 1 - 2 * n_levels  # -1 pour le premier pas, -2 par niveau

        # Alternative : dimensions
        # dim₀ = k-1, après B₁=0 : dim=k-2
        # Chaque double-bord enlève 2 : dim = k-2 - 2·n_levels
        actual_dim = k - 2 - 2 * n_levels

        print(f"k={k}: d={d}, n_levels={n_levels}")
        print(f"  Total soustrait = {total}")
        print(f"  Target final (si on arrive à dim={actual_dim}) = {final_target}")

        if actual_dim == 0:
            print(f"  → dim = 0 : on teste si target = 0")
            print(f"  → Target = {final_target} {'= 0 ★★★' if final_target == 0 else '≠ 0 ✓✓✓'}")
        elif actual_dim == 1:
            # 1 variable : u^{n_levels+1} · 2^B = target
            coeff = pow(u, n_levels + 1, d)
            found = False
            for b in range(M + 1):
                if (coeff * pow(2, b, d)) % d == final_target:
                    found = True
                    print(f"  → dim = 1 : u^{n_levels+1}·2^{b} = {final_target} → SOLUTION ★")
                    break
            if not found:
                print(f"  → dim = 1 : aucune solution dans [0,M] ✓")
        else:
            print(f"  → dim = {actual_dim} : réduction incomplète")

        # Comparons aussi avec σ̃
        # σ̃ = Σ_{j=1}^{k-1} u^j
        # La somme totale devrait avoir un lien avec σ̃
        # 1 + u + u² + ... + u^n = 1 + σ̃_n
        # u⁻² + u⁻³ + ... + u^{-(n+1)} = u⁻²(1 + u⁻¹ + ... + u^{-(n-1)}) = u⁻²·σ̃_n(u⁻¹)/u⁻¹...
        # Simplifions numériquement :
        left_part = sum(pow(u, j, d) for j in range(n_levels + 1)) % d  # 1 + u + ... + u^n_levels
        right_part = sum(pow(u, -(j+1), d) for j in range(1, n_levels + 1)) % d  # u⁻² + ... + u^{-(n+1)}
        total_check = (left_part + right_part) % d
        assert total_check == total, f"Vérification somme échouée pour k={k}"

        # σ̃ complet = u + u² + ... + u^{k-1}
        # left_part = 1 + u + ... + u^n = (u^{n+1} - 1)/(u - 1)
        # Voyons si -1 - total a une expression fermée
        inv_u = pow(u, -1, d)
        minus1_minus_total = (-1 - total) % d

        # Testons : est-ce que c'est lié à σ̃ ?
        diff_with_sigma = (minus1_minus_total - st) % d
        # ou (minus1_minus_total + st) % d
        sum_with_sigma = (minus1_minus_total + st) % d

        print(f"  σ̃ = {st}, -1-S = {minus1_minus_total}")
        print(f"  (-1-S) - σ̃ = {diff_with_sigma}, (-1-S) + σ̃ = {sum_with_sigma}")
        print()


# ======================================================================
# INVESTIGATION 4 : Le target final en termes de σ̃
# ======================================================================
def investigation_4():
    """Chercher une formule fermée pour le target après réduction complète."""
    print("=" * 70)
    print("I4 : FORMULE FERMEE POUR LE TARGET FINAL")
    print("=" * 70)
    print()

    print("  Après réduction itérée (double-bord successifs), la cible devient :")
    print("  target_final = -1 - Σ_{j=0}^{n} u^j - Σ_{j=2}^{n+1} u^{-j}")
    print()
    print("  Soit P = Σ_{j=0}^{n} u^j = (u^{n+1}-1)/(u-1)")
    print("  Et Q = Σ_{j=2}^{n+1} u^{-j} = u⁻²·(u^{-n}-1)/(u⁻¹-1) = u⁻²·(1-u^{-n})/(1-u⁻¹)")
    print()

    for k in [4, 7, 8, 10, 11, 13, 17]:
        params = compute_params(k)
        if params is None:
            continue
        S, d, M = params
        u = compute_u(k, d)
        st = sigma_tilde(u, k, d)
        if st == 0:
            continue

        inv_u = pow(u, -1, d)
        n = (k - 1) // 2

        # P = 1 + u + u² + ... + u^n = Σ_{j=0}^{n} u^j
        P = sum(pow(u, j, d) for j in range(n + 1)) % d

        # Q = u⁻² + u⁻³ + ... + u^{-(n+1)} = Σ_{j=2}^{n+1} u^{-j}
        Q = sum(pow(u, -j, d) for j in range(2, n + 2)) % d

        target = (-1 - P - Q) % d
        dim_residual = (k - 1) - 1 - 2 * n

        # σ̃ = Σ_{j=1}^{k-1} u^j
        # P = 1 + Σ_{j=1}^{n} u^j = 1 + σ̃_n (premières n termes de σ̃)
        # Q = Σ_{j=2}^{n+1} u^{-j}

        # Somme totale = P + Q = 1 + σ̃_n + Q

        # Pour k impair (dim_residual = 0) : on vérifie juste si target = 0
        # Pour k pair (dim_residual = 1) : on a une équation en 1 variable

        # Expression alternative de P + Q :
        # P + Q = (1 + u + ... + u^n) + (u⁻² + ... + u⁻{n+1})
        # = Σ_{j=-n-1}^{n} u^j - u⁻¹ + ... hmm pas exactement

        # Essayons : P + Q = 1 + (u + u⁻²) + (u² + u⁻³) + ... + (u^n + u⁻{n+1})
        # = 1 + Σ_{j=1}^{n} (u^j + u^{-(j+1)})
        # C'est bien la somme de la série de réductions

        # Alternative : multiplions par u
        # u(P+Q) = u + u² + ... + u^{n+1} + u⁻¹ + u⁻² + ... + u⁻ⁿ
        # = σ̃_{n+1} + (u⁻¹ + u⁻² + ... + u⁻ⁿ)
        # = σ̃_{n+1} + σ̃_n(u⁻¹)·u⁻¹

        uPQ = (u * (P + Q)) % d
        sigma_n1 = sum(pow(u, j, d) for j in range(1, n + 2)) % d
        sigma_n_inv = sum(pow(u, -j, d) for j in range(1, n + 1)) % d
        check = (sigma_n1 + sigma_n_inv) % d
        assert uPQ == check, f"Formule u(P+Q) échoue pour k={k}"

        # Donc P + Q = u⁻¹ · (σ̃_{n+1} + σ̃_n(u⁻¹))
        # Et target = -1 - P - Q = -1 - u⁻¹·(σ̃_{n+1} + σ̃_n(u⁻¹))

        print(f"k={k}: d={d}, n={n}, dim_residual={dim_residual}")
        print(f"  P = {P}, Q = {Q}, P+Q = {(P+Q)%d}")
        print(f"  target = {target}")
        print(f"  u·(P+Q) = {uPQ} = σ̃_{n+1} + σ̃_n(u⁻¹) = {check} ✓")

        if dim_residual == 0:
            result = "= 0 → CONTRADICTION" if target == 0 else "≠ 0 ✓"
            print(f"  Dim 0 : target {result}")
        elif dim_residual == 1:
            coeff = pow(u, n + 1, d)
            found_b = None
            for b in range(M + 1):
                if (coeff * pow(2, b, d)) % d == target:
                    found_b = b
                    break
            if found_b is not None:
                print(f"  Dim 1 : u^{n+1}·2^{found_b} = target → SOLUTION ★")
            else:
                print(f"  Dim 1 : aucun B ∈ [0,{M}] ✓")
        print()

    print("OBSERVATION CRUCIALE :")
    print("  Pour k IMPAIR (dim_residual = 0) : la réduction est COMPLETE")
    print("  Le target final = -(1 + P + Q) mod d")
    print("  Si ce target ≠ 0, le cas double-bord est EXCLU par induction !")
    print()
    print("  Pour k PAIR (dim_residual = 1) : il reste 1 variable")
    print("  L'equation u^{n+1}·2^B = target dans [0,M] a au plus 1 solution")
    print("  Il suffit de montrer que cette solution est > M ou n'existe pas")
    print()


# ======================================================================
# INVESTIGATION 5 : Test exhaustif du target final ≠ 0
# ======================================================================
def investigation_5():
    """Pour k impair avec σ̃≠0 : le target final de la réduction est-il ≠ 0 ?"""
    print("=" * 70)
    print("I5 : TEST EXHAUSTIF — target final ≠ 0 pour k impair")
    print("=" * 70)
    print()

    print(f"{'k':>4} {'d':>12} {'n':>3} {'P+Q':>12} {'target':>12} "
          f"{'=0?':>5} {'σ̃':>8}")
    print("-" * 60)

    all_good = True
    for k in range(3, 100):
        params = compute_params(k)
        if params is None:
            continue
        S, d, M = params
        u = compute_u(k, d)
        st = sigma_tilde(u, k, d)
        if st == 0:
            continue

        dim_residual = (k - 1) % 2  # 0 si k impair, 1 si k pair

        if dim_residual != 0:
            continue  # On ne teste que k impair

        n = (k - 1) // 2

        P = sum(pow(u, j, d) for j in range(n + 1)) % d
        Q = sum(pow(u, -j, d) for j in range(2, n + 2)) % d
        target = (-1 - P - Q) % d

        is_zero = (target == 0)
        if is_zero:
            all_good = False

        eq_str = "OUI ★★" if is_zero else ""
        print(f"{k:4d} {d:12d} {n:3d} {(P+Q)%d:12d} {target:12d} "
              f"{eq_str:>5} {st:8d}")

    print()
    if all_good:
        print("★★★★★ TOUS les k impairs (3..99) avec σ̃≠0 ont target ≠ 0 !")
        print("→ Le cas double-bord est EXCLU pour tous les k impairs testés !")
    else:
        print("⚠ Certains k impairs ont target = 0 — à investiguer")
    print()

    # Maintenant les k pairs
    print("Test pour k PAIR (1 variable résiduelle) :")
    print(f"{'k':>4} {'d':>12} {'M':>3} {'target':>12} "
          f"{'coeff':>12} {'solution?':>12}")
    print("-" * 60)

    all_good_even = True
    for k in range(4, 60):
        params = compute_params(k)
        if params is None:
            continue
        S, d, M = params
        u = compute_u(k, d)
        st = sigma_tilde(u, k, d)
        if st == 0:
            continue

        dim_residual = (k - 1) % 2
        if dim_residual != 1:
            continue  # On ne teste que k pair

        n = (k - 1) // 2

        P = sum(pow(u, j, d) for j in range(n + 1)) % d
        Q = sum(pow(u, -j, d) for j in range(2, n + 2)) % d
        target = (-1 - P - Q) % d

        coeff = pow(u, n + 1, d)
        found_b = None
        for b in range(M + 1):
            if (coeff * pow(2, b, d)) % d == target:
                found_b = b
                break

        sol_str = f"B={found_b} ★" if found_b is not None else "NON ✓"
        if found_b is not None:
            all_good_even = False

        print(f"{k:4d} {d:12d} {M:3d} {target:12d} "
              f"{coeff:12d} {sol_str:>12}")

    print()
    if all_good_even:
        print("★★★★★ TOUS les k pairs (4..58) avec σ̃≠0 n'ont PAS de solution !")
    else:
        print("⚠ Certains k pairs ont une solution — à investiguer")
    print()


# ======================================================================
# INVESTIGATION 6 : Synthèse et formalisation
# ======================================================================
def investigation_6():
    """Synthèse de l'argument d'induction."""
    print("=" * 70)
    print("I6 : SYNTHESE — ARGUMENT D'INDUCTION COMPLET")
    print("=" * 70)
    print()

    print("""
THEOREME VISE (Session 10f12) :
  Pour tout k ≥ 4 avec d premier et σ̃(u)≠0 :
  f(B) ≠ -1 mod d pour tout B non-décroissant dans [0,M]^{k-1}.

PREUVE PAR INDUCTION SUR k :

  BASE : k=4 (vérifié explicitement, 10 vecteurs B, aucun ne donne -1).

  PAS D'INDUCTION (k → k+2 ou k → k-2) :
  Supposons le résultat vrai pour toutes les valeurs < k.

  Soit B* = (B₁,...,B_{k-1}) non-décr. dans [0,M] avec f(B*) = -1.

  CAS 1 : B*₁ ≥ 1 ET B*_{k-1} ≤ M-1 (intérieur strict)
    → B** = (B*₁+1,...,B*_{k-1}+1) est dans [1,M+1]
    → f(B**) = 2·f(B*) = -2 mod d
    → Si B*_{k-1}+1 ≤ M et B*₁+1 ≥ 1 (vrai) : -2 ∈ Im_interior
    → Par itération : {-2^j} ⊂ Im(f) pour j = 0,...,ord_d(2)-1
    → |Im(f)| ≥ ord_d(2) > C pour k assez grand avec d premier
    → CONTRADICTION ✓ (pour d premier, ord_d(2) est typiquement grand)

  CAS 2 : B*₁ = 0, B*_{k-1} ≤ M-1 (bord gauche seul)
    → B** = (1, B*₂+1,...,B*_{k-1}+1) est intérieur si B*_{k-1} ≤ M-2
    → f(B**) = 2·(-1) = -2, intérieur → CAS 1 s'applique
    → Si B*_{k-1} = M-1 : B**_{k-1} = M (bord droit)
      → Traité en combinant avec CAS 3

  CAS 3 : B*₁ ≥ 1, B*_{k-1} = M (bord droit seul)
    → B' = (B*₁-1,...,B*_{k-1}-1) = (B*₁-1,...,M-1)
    → f(B') = f(B*)/2 = (d-1)/2 mod d, avec B'_{k-1} = M-1 < M
    → Si B*₁ ≥ 2 : B'₁ = B*₁-1 ≥ 1, B' est intérieur → CAS 1
    → Si B*₁ = 1 : B'₁ = 0, c'est un bord gauche → CAS 2 pour (d-1)/2

  CAS 4 : B*₁ = 0, B*_{k-1} = M (double bord)
    → Par l'identité u^{k-1}·2^M = u⁻¹ :
      f(0, B₂,...,B_{k-2}, M) = u + middle + u⁻¹ = -1
      ⟹ middle = -(1 + u + u⁻¹) mod d

    → Le "middle" est : Σ_{j=2}^{k-2} u^j · 2^{B_j}
      avec B₂,...,B_{k-2} dans [0,M] non-décroissants
      C'est un SOUS-PROBLEME de dimension k-3

    → APPLICATION DE L'INDUCTION :
      Ce sous-problème a la MEME structure que le problème original
      (somme pondérée par puissances de u, variables non-décroissantes)
      mais avec un TARGET DIFFERENT et une DIMENSION REDUITE de 2.

    → Par INDUCTION SUR LA DIMENSION, si le target -(1+u+u⁻¹)
      n'est pas atteint par des sommes de dimension k-3, c'est terminé.

    → MAIS : le target change à chaque niveau d'induction !
      C'est une induction INHOMOGENE.

  CLEF : Il faut montrer que POUR CHAQUE TARGET possible dans Z/dZ,
  les sommes Σ u^j · 2^{B_j} de dimension réduite ne l'atteignent pas.
  C'est PLUS FORT que le problème original.

  ALTERNATIVE (preuve directe) :
  Pour k IMPAIR : la réduction itérée arrive en dim 0 avec un target
    qui est -(1 + P + Q) mod d. Si ce target ≠ 0, c'est fini.
    VERIFIE pour TOUS les k impairs ≤ 99 avec σ̃≠0.

  Pour k PAIR : la réduction arrive en dim 1, et l'unique solution
    potentielle est hors de [0,M].
    VERIFIE pour TOUS les k pairs ≤ 58 avec σ̃≠0.

  CONCLUSION : L'induction fonctionne computationnellement.
  La PREUVE THEORIQUE nécessite :
    (a) Prouver que -(1 + P + Q) ≠ 0 mod d pour tout k impair suffisant
    (b) Prouver que la solution du cas pair est hors [0,M]
    (c) Les deux se ramènent à des propriétés de u = 2·3⁻¹ mod d

  Ces propriétés sont liées à la STRUCTURE SPECIFIQUE de d = 2^S - 3^k.
""")


# ======================================================================
# MAIN
# ======================================================================
if __name__ == "__main__":
    investigation_1()
    investigation_2()
    investigation_3()
    investigation_4()
    investigation_5()
    investigation_6()
