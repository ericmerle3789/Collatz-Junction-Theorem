#!/usr/bin/env python3
"""keyhole_geometry.py — Phase 17: La Géométrie du Trou de la Serrure.

Vérifie les résultats de la Phase 17 du Théorème de Jonction de Collatz.

Sections:
  1. Polygone de Newton pour q₃ (plat, v_p = 0 pour tous les termes)
  2. Marche de Horner inverse (backward walk from c_k = 0, target c₁ = 1)
  3. Zigzag de coset pour p = 929 (Type II, alternance C₀/C₁)
  4. Tour de Hensel (double annulation P(2) = P'(2) = 0 mod p)
  5. Polynôme lacunaire : comptage de racines dans ⟨2⟩
  6. Résonance globale : 2^{S mod ω} ≡ 3^k (mod p)
  7. Incompatibilité de taille (bornes sur n₀)

Auteur: Eric Merle (assisté par Claude)
Date: Février 2026
"""
import math
import hashlib
import itertools
from collections import Counter


# ===========================================================================
# Auxiliary
# ===========================================================================

def mult_ord(a, m):
    if math.gcd(a, m) != 1:
        return 0
    cur, s = a % m, 1
    while cur != 1:
        cur = (cur * a) % m
        s += 1
    return s


def compositions(S, k):
    if k == 1:
        yield (0,)
        return
    for combo in itertools.combinations(range(1, S), k - 1):
        yield (0,) + combo


def corrsum_horner(A, p):
    c = 1
    for j in range(1, len(A)):
        c = (3 * c + pow(2, A[j], p)) % p
    return c


# ===========================================================================
# Section 1: Newton polygon (Proposition 17.1)
# ===========================================================================

def section1_newton_polygon():
    print("=" * 70)
    print("SECTION 1: Polygone de Newton (Proposition 17.1)")
    print("=" * 70)

    k, S, p = 5, 8, 13
    comps = list(compositions(S, k))

    print(f"\nq₃: k={k}, S={S}, p={p}")
    print(f"Vérification: v_p(3^j) = 0 pour tout j (car p={p} != 3)")

    for A in comps[:3]:
        terms = [3 ** (k - 1 - i) * (1 << A[i]) for i in range(k)]
        vals = []
        for t in terms:
            v = 0
            tt = t
            while tt % p == 0:
                tt //= p
                v += 1
            vals.append(v)
        print(f"  A={A}: termes = {terms}")
        print(f"         v_p   = {vals}")
        assert all(v == 0 for v in vals), f"Expected all v_p = 0, got {vals}"

    # Verify for ALL compositions
    flat_count = 0
    for A in comps:
        terms = [3 ** (k - 1 - i) * (1 << A[i]) for i in range(k)]
        all_zero = all(t % p != 0 for t in terms)
        if all_zero:
            flat_count += 1
    print(f"\nPolygone plat (tous v_p = 0): {flat_count}/{len(comps)} compositions")
    assert flat_count == len(comps)
    print("✓ Polygone de Newton plat pour toutes les compositions")
    print("→ L'argument ultrametrique d'unicité du minimum ÉCHOUE")


# ===========================================================================
# Section 2: Backward Horner walk (Proposition 17.2)
# ===========================================================================

def section2_backward_walk():
    print("\n" + "=" * 70)
    print("SECTION 2: Marche de Horner inverse (Proposition 17.2)")
    print("=" * 70)

    k, S, p = 5, 8, 13
    inv3 = pow(3, -1, p)
    comps = list(compositions(S, k))

    print(f"\np={p}, 3^(-1) mod p = {inv3}")
    print(f"Marche inverse: c_k=0 -> c_1 via c_j = (c_{'{j+1}'} - 2^A_j) * 3^(-1)")
    print(f"Cible: c_1 = 1\n")

    c1_values = []
    for A in comps:
        c = 0
        for j in range(k - 1, 0, -1):
            c = ((c - pow(2, A[j], p)) * inv3) % p
        c1_values.append(c)

    dist = Counter(c1_values)
    print("Distribution des c₁(backward from 0):")
    for r in range(p):
        nr = dist.get(r, 0)
        marker = " *** TARGET ***" if r == 1 else ""
        print(f"  c₁ = {r:2d}: {nr} compositions{marker}")

    N0 = dist.get(1, 0)
    print(f"\nCompositions avec c₁ = 1 (= cycles): {N0}")
    assert N0 == 0, f"Expected N₀ = 0, got {N0}"
    print("✓ Exclusion du zéro confirmée par marche inverse")

    # Verify consistency with forward Horner
    print("\nVérification forward vs backward:")
    for A in comps[:3]:
        fwd = corrsum_horner(A, p)
        c = 0
        for j in range(k - 1, 0, -1):
            c = ((c - pow(2, A[j], p)) * inv3) % p
        # c is the backward c₁ when starting from 0
        # If corrSum = 0, then backward c₁ should be 1
        # If corrSum = r, then backward c₁ from r should give 1
        c_from_r = fwd  # start backward from actual corrSum
        c_check = c_from_r
        for j in range(k - 1, 0, -1):
            c_check = ((c_check - pow(2, A[j], p)) * inv3) % p
        print(f"  A={A}: forward={fwd}, backward_from_{fwd}={c_check}")
        assert c_check == 1, f"Expected 1, got {c_check}"
    print("✓ Forward/backward consistency verified")


# ===========================================================================
# Section 3: Coset zigzag (Proposition 17.3)
# ===========================================================================

def section3_coset_zigzag():
    print("\n" + "=" * 70)
    print("SECTION 3: Zigzag de coset — p = 929, Type II")
    print("=" * 70)

    p = 929
    omega = mult_ord(2, p)
    m = (p - 1) // omega
    inv3 = pow(3, -1, p)

    print(f"\np = {p}, ω = {omega}, m = {m}")
    print(f"Type: {'I' if m == 1 else f'II (m={m})'}")

    # Build <2>
    gen2 = set()
    x = 1
    for _ in range(omega):
        gen2.add(x)
        x = (x * 2) % p

    print(f"|⟨2⟩| = {len(gen2)}")
    print(f"3 ∈ ⟨2⟩: {3 in gen2}")
    print(f"-1 ∈ ⟨2⟩: {(p - 1) in gen2}")

    # Zigzag pattern
    print(f"\nCoset of 3^(-j) for j=1..20:")
    pattern = []
    for j in range(1, 21):
        val = pow(inv3, j, p)
        c = "C₀" if val in gen2 else "C₁"
        pattern.append(c)
    print(f"  {' '.join(pattern)}")

    # Verify strict alternation
    expected = ["C₁" if j % 2 == 1 else "C₀" for j in range(1, 21)]
    assert pattern == expected, f"Expected alternation, got {pattern}"
    print("✓ Alternance stricte C₁/C₀ vérifiée (période 2)")

    # For k=306: count terms in each coset
    k = 306
    odd_count = sum(1 for j in range(1, k) if j % 2 == 1)
    even_count = sum(1 for j in range(1, k) if j % 2 == 0)
    print(f"\nPour k={k} (q₇): {odd_count} termes dans C₁, {even_count} termes dans C₀")
    print(f"Cible -1 = {p - 1} ∈ {'C₀' if (p-1) in gen2 else 'C₁'}")


# ===========================================================================
# Section 4: Hensel tower (Theorem 17.1)
# ===========================================================================

def section4_hensel_tower():
    print("\n" + "=" * 70)
    print("SECTION 4: Tour de Hensel — Double annulation")
    print("=" * 70)

    k, S, p = 5, 8, 13
    comps = list(compositions(S, k))
    C = len(comps)

    print(f"\nq₃: k={k}, S={S}, p={p}, C={C}")
    print(f"C/p = {C/p:.3f}, C/p² = {C/p**2:.4f}")

    # Check P(2) and P'(2) mod p for all compositions
    print(f"\nVérification P_A(2) et P_A'(2) mod {p}:")
    single_vanish = 0
    double_vanish = 0
    for A in comps:
        P_val = sum(pow(3, k - 1 - i, p) * pow(2, A[i], p)
                     for i in range(k)) % p
        # P'(X) = sum A_i * 3^{k-1-i} * X^{A_i - 1}
        dP_val = sum(A[i] * pow(3, k - 1 - i, p) * pow(2, max(A[i] - 1, 0), p)
                      for i in range(k)) % p
        if P_val == 0:
            single_vanish += 1
            if dP_val == 0:
                double_vanish += 1
                print(f"  DOUBLE: A={A}, P(2)={P_val}, P'(2)={dP_val}")
            else:
                print(f"  SIMPLE: A={A}, P(2)={P_val}, P'(2)={dP_val}")

    print(f"\nP(2) = 0 mod {p}: {single_vanish}/{C}")
    print(f"P(2) = P'(2) = 0 mod {p}: {double_vanish}/{C}")
    assert single_vanish == 0
    print(f"\n✓ Aucune annulation simple, a fortiori aucune double")
    print(f"  (Prédit par C/p² = {C/p**2:.4f} < 1 pour la double)")


# ===========================================================================
# Section 5: Lacunary polynomial roots (§6)
# ===========================================================================

def section5_lacunary_roots():
    print("\n" + "=" * 70)
    print("SECTION 5: Racines du polynôme lacunaire dans ⟨2⟩")
    print("=" * 70)

    k, S, p = 5, 8, 13
    omega = mult_ord(2, p)
    comps = list(compositions(S, k))

    print(f"\nq₃: p={p}, ω={omega} (Type I, primitif)")
    print(f"Évaluation P_A(2^j) pour j = 0, ..., {omega - 1}:")

    total_roots = 0
    root_at_j0 = 0  # j=0 means X=1
    root_at_j1 = 0  # j=1 means X=2 (our target)

    for A in comps:
        roots_j = []
        for j in range(omega):
            val = sum(pow(3, k - 1 - i, p) * pow(2, j * A[i], p)
                       for i in range(k)) % p
            if val == 0:
                roots_j.append(j)
        total_roots += len(roots_j)
        if 0 in roots_j:
            root_at_j0 += 1
        if 1 in roots_j:
            root_at_j1 += 1

    print(f"\nStatistiques de racines:")
    print(f"  Total racines dans ⟨2⟩: {total_roots} / ({len(comps)} × {omega})")
    print(f"  Moyenne par polynôme: {total_roots / len(comps):.2f}")
    print(f"  P_A(2^0 = 1) = 0: {root_at_j0} compositions")
    print(f"  P_A(2^1 = 2) = 0: {root_at_j1} compositions  ← TARGET")

    assert root_at_j1 == 0
    print(f"\n✓ Aucun P_A n'a X=2 comme racine mod {p}")

    # Bound comparison
    lacunary_bound = k * (p - 1) ** (1 - 1 / k)
    print(f"\nBorne lacunaire (Bi-Straus): k·(p-1)^(1-1/k) = "
          f"{k}·{p - 1}^{1 - 1 / k:.3f} = {lacunary_bound:.1f}")
    print(f"Borne triviale: deg(P) = S-1 = {S - 1}")
    print(f"Borne effective: min({S - 1}, {lacunary_bound:.1f}) = "
          f"{min(S - 1, lacunary_bound):.1f}")


# ===========================================================================
# Section 6: Global resonance (Proposition 17.4)
# ===========================================================================

def section6_global_resonance():
    print("\n" + "=" * 70)
    print("SECTION 6: Résonance globale — 2^{S mod ω} ≡ 3^k (mod p)")
    print("=" * 70)

    cases = [
        ("q₃", 5, 8, 13),
        ("q₇", 306, 485, 929),
    ]

    for label, k, S, p in cases:
        omega = mult_ord(2, p)
        s_mod = S % omega
        lhs = pow(2, s_mod, p)
        rhs = pow(3, k, p)

        print(f"\n{label}: k={k}, S={S}, p={p}, ω={omega}")
        print(f"  S mod ω = {S} mod {omega} = {s_mod}")
        print(f"  2^{s_mod} mod {p} = {lhs}")
        print(f"  3^{k} mod {p} = {rhs}")
        assert lhs == rhs, f"Resonance failed: {lhs} != {rhs}"
        print(f"  ✓ Résonance: 2^{s_mod} ≡ 3^{k} ≡ {rhs} (mod {p})")

    print("\n✓ Résonance globale vérifiée pour q₃ et q₇")


# ===========================================================================
# Section 7: Size incompatibility (Theorem 17.3)
# ===========================================================================

def section7_size_bounds():
    print("\n" + "=" * 70)
    print("SECTION 7: Incompatibilité de taille")
    print("=" * 70)

    convergents = [
        ("q₃", 5, 8),
        ("q₅", 41, 65),
        ("q₇", 306, 485),
    ]

    for label, k, S in convergents:
        d = (1 << S) - 3 ** k
        # Bounds on corrSum
        cs_min = (3 ** k - 2 ** k)  # dense composition
        cs_max = sum(3 ** (k - 1 - i) * (1 << (S - k + i)) for i in range(k))
        n0_max = cs_max / d if d > 0 else float('inf')
        log2_n0_max = math.log2(n0_max) if n0_max > 0 else 0

        print(f"\n{label} (k={k}, S={S}):")
        print(f"  d = 2^{S} - 3^{k} ≈ 2^{math.log2(d):.1f}")
        print(f"  corrSum_min = 3^k - 2^k ≈ 2^{math.log2(cs_min):.1f}")
        print(f"  corrSum_max ≈ 2^{math.log2(cs_max):.1f}")
        print(f"  n₀_max = corrSum_max / d ≈ 2^{log2_n0_max:.1f}")
        print(f"  n₀ doit être entier positif: 1 ≤ n₀ ≤ 2^{log2_n0_max:.1f}")


# ===========================================================================
# Main
# ===========================================================================

def main():
    print("=" * 70)
    print("  Phase 17: La Géométrie du Trou de la Serrure")
    print("  Vérification numérique — Collatz Junction Theorem")
    print("=" * 70)

    section1_newton_polygon()
    section2_backward_walk()
    section3_coset_zigzag()
    section4_hensel_tower()
    section5_lacunary_roots()
    section6_global_resonance()
    section7_size_bounds()

    print("\n" + "=" * 70)
    print("RÉSUMÉ")
    print("=" * 70)
    print("✓ Polygone de Newton plat confirmé (v_p = 0 pour tous les termes)")
    print("✓ Marche de Horner inverse: c₁=1 jamais atteint pour q₃")
    print("✓ Zigzag de coset vérifié pour p=929 (alternance C₀/C₁)")
    print("✓ Tour de Hensel: aucune annulation simple ni double pour q₃")
    print("✓ Polynôme lacunaire: X=2 n'est jamais racine pour q₃")
    print("✓ Résonance globale 2^{S mod ω} ≡ 3^k vérifiée")
    print("✓ Bornes de taille sur n₀ calculées")

    sig = "phase17_keyhole_geometry_v1"
    sha = hashlib.sha256(sig.encode()).hexdigest()[:16]
    print(f"\nSHA256(signature)[:16] = {sha}")
    print("✓ Tous les tests passent.")


if __name__ == "__main__":
    main()
