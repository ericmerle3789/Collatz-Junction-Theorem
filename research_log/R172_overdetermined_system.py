#!/usr/bin/env python3
"""
R172 — SYSTÈME SUR-DÉTERMINÉ PAR LES ROTATIONS
=================================================

IDÉE CLÉ : Pour un cycle, g(rot_j(v)) ≡ 0 mod d pour TOUT j.
L'identité boundary-swap (généralisée de Knight) donne :
  Pour toute rotation v' = 1·u·0 : 3g(v') - g(0·u·1) = 3^x - 2^{k-1}

Si v' et 0·u·1 sont TOUTES DEUX des rotations de v, alors :
  3·d·f(v') - d·f(0u1) = 3^x - 2^{k-1}
  d·(3f(v') - f(0u1)) = 3^x - 2^{k-1}
  Mais 3^x - 2^{k-1} ≡ 2^{k-1} mod d, donc d | 2^{k-1}, impossible.

QUESTION : Pour quels v est-ce que 0u1 est aussi une rotation de v ?
C'est le cas ssi v = 1·u·0 et 0·u·1 ∈ Orbit(v).

EXPLORATION SYSTÉMATIQUE :
1. Pour chaque v aperiodique, vérifier si une rotation 1u0 a son partner 0u1
   dans la même orbite.
2. Si OUI → contradiction directe (Knight généralisé).
3. Si NON → chercher d'AUTRES identités.

HYPOTHÈSE À TESTER : Pour tout v apériodique avec x ≥ 2 et k ≥ 3,
il existe TOUJOURS une rotation v'=1u0 dont le partner 0u1 est aussi
une rotation de v.
"""

from itertools import combinations
import math


def all_rotations(v):
    """Retourne l'ensemble de toutes les rotations distinctes de v."""
    k = len(v)
    rots = set()
    for j in range(k):
        rots.add(v[j:] + v[:j])
    return rots


def has_knight_pair(v):
    """
    Vérifie si v a une rotation v' = (1,...,0) dont le boundary-swap
    w' = (0,...,1) est aussi une rotation de v.

    Retourne (True, v', w') si trouvé, (False, None, None) sinon.
    """
    k = len(v)
    orbit = all_rotations(v)

    for rot in orbit:
        if rot[0] == 1 and rot[-1] == 0:
            # v' = 1·u·0
            u = rot[1:-1]
            w = (0,) + u + (1,)
            if w in orbit:
                return True, rot, w

    return False, None, None


def compute_g(v, x=None):
    """g(v) = Σ 3^{x-1-i} · 2^{pos_i} where pos_i are positions of 1s."""
    if x is None:
        x = sum(v)
    ones_pos = [i for i, b in enumerate(v) if b == 1]
    assert len(ones_pos) == x
    return sum(3**(x-1-i) * 2**ones_pos[i] for i in range(x))


def all_parity_vectors_aperiodic(k, x):
    """Vecteurs de parité apériodiques de longueur k avec x uns."""
    for positions in combinations(range(k), x):
        v = tuple(1 if i in positions else 0 for i in range(k))
        is_aperiodic = True
        for period in range(1, k):
            if k % period == 0 and period < k:
                if v == v[:period] * (k // period):
                    is_aperiodic = False
                    break
        if is_aperiodic:
            yield v


def main():
    print("=" * 72)
    print("R172 — SYSTÈME SUR-DÉTERMINÉ PAR LES ROTATIONS")
    print("=" * 72)

    # ═══════════════════════════════════════════════════════════════
    # TEST 1 : Pour quels v existe-t-il une paire de Knight ?
    # ═══════════════════════════════════════════════════════════════
    print("\n" + "=" * 60)
    print("TEST 1 : EXISTENCE DE PAIRES DE KNIGHT")
    print("=" * 60)

    for k in range(3, 16):
        for x in range(1, k):
            d = 2**k - 3**x
            if d <= 0:
                continue

            total = 0
            with_pair = 0
            without_pair = 0
            without_examples = []

            for v in all_parity_vectors_aperiodic(k, x):
                total += 1
                has_pair, v_prime, w_prime = has_knight_pair(v)

                if has_pair:
                    with_pair += 1
                else:
                    without_pair += 1
                    if len(without_examples) < 3:
                        without_examples.append(v)

            if total == 0:
                continue

            pct = 100 * with_pair / total
            marker = "✅" if without_pair == 0 else "❌"
            print(f"  k={k:2d}, x={x:2d}: d={d:>8d}, "
                  f"{marker} {with_pair}/{total} ({pct:.0f}%) have Knight pair"
                  f"{'  SANS: ' + str([''.join(str(b) for b in v) for v in without_examples]) if without_pair > 0 and without_pair <= 5 else ''}")

    # ═══════════════════════════════════════════════════════════════
    # TEST 2 : Pour les vecteurs SANS paire, quelle est la structure ?
    # ═══════════════════════════════════════════════════════════════
    print("\n\n" + "=" * 60)
    print("TEST 2 : ANALYSE DES VECTEURS SANS PAIRE DE KNIGHT")
    print("=" * 60)

    print("""
Un vecteur v = 1·u·0 a son partner 0·u·1 dans la même orbite
ssi la rotation qui amène le dernier 0 au début produit le partner.

Conditions : v contient le sous-mot "10" à la position (0, k-1),
et le mot "01" obtenu par swap est une rotation de v.

Ceci est lié à la STRUCTURE PALINDROMIQUE de u (cf. Christoffel).
""")

    # Analyse détaillée pour k=8
    k = 8
    for x in range(2, k):
        d = 2**k - 3**x
        if d <= 0:
            continue

        print(f"\n  k={k}, x={x}, d={d}:")

        for v in all_parity_vectors_aperiodic(k, x):
            has_pair, _, _ = has_knight_pair(v)
            if not has_pair:
                v_str = ''.join(str(b) for b in v)
                g_val = compute_g(v, x)

                # Analyser TOUTES les identités disponibles
                orbit = all_rotations(v)

                # Pour chaque rotation 1u0, calculer le residue de 3g(1u0)-g(0u1) mod d
                identities = []
                for rot in sorted(orbit):
                    if rot[0] == 1 and rot[-1] == 0:
                        u = rot[1:-1]
                        w = (0,) + u + (1,)
                        g_rot = compute_g(rot, x)
                        g_w = compute_g(w, x)
                        diff = 3 * g_rot - g_w
                        # Devrait toujours être 3^x - 2^{k-1}
                        expected = 3**x - 2**(k-1)
                        assert diff == expected, f"Identity failed! diff={diff}, expected={expected}"

                        w_in_orbit = w in orbit
                        identities.append((rot, w, g_rot, g_w, w_in_orbit))

                # Chercher d'AUTRES types de contradictions
                # Si g(v) ≡ 0 mod d pour toutes les rotations,
                # alors g(w) = 3g(v') - (3^x - 2^{k-1})
                # g(w) mod d = -(3^x - 2^{k-1}) mod d = -2^{k-1} mod d
                # MAIS si w est PAS une rotation, on ne peut rien conclure.

                # NOUVELLE IDÉE : regarder les g-values mod d pour TOUTES rotations
                g_residues = set()
                for rot in orbit:
                    g_residues.add(compute_g(rot, x) % d)

                print(f"    {v_str}: g={g_val}, g%d={g_val%d}, "
                      f"#orbite={len(orbit)}, #residues_mod_d={len(g_residues)}, "
                      f"0∈residues={'YES' if 0 in g_residues else 'NO'}")

                if 0 in g_residues:
                    # Cycle candidate! Check if ALL rotations have g ≡ 0 mod d
                    all_zero = all(compute_g(rot, x) % d == 0 for rot in orbit)
                    print(f"      ⚠️ CYCLE CANDIDATE! all_rot≡0: {all_zero}")

    # ═══════════════════════════════════════════════════════════════
    # TEST 3 : IDENTITÉ GÉNÉRALISÉE MULTI-SWAP
    # ═══════════════════════════════════════════════════════════════
    print("\n\n" + "=" * 60)
    print("TEST 3 : IDENTITÉS MULTI-POSITION")
    print("=" * 60)

    print("""
Au lieu de swapper (position 0, position k-1), essayons de swapper
des bits à d'AUTRES positions.

Pour v et v' différant en positions i et j (swap 0↔1) :
g(v) - g(v') = ?
Si v_i=1,v_j=0 → v'_i=0,v'_j=1 (swap de ces deux bits) :
  g(v) a un terme 3^{r_i} · 2^i (position i a un 1)
  g(v') a un terme 3^{r'_j} · 2^j (position j a un 1 dans v')

  MAIS les rangs changent aussi quand on swap les bits !
  C'est pourquoi le boundary swap est spécial : les bits aux extrémités
  n'affectent pas les rangs intermédiaires.
""")

    # Compute: for boundary swap, why do ranks not change?
    # v = (1, u_1, ..., u_{k-2}, 0): ones at positions {0} ∪ {inner}
    # w = (0, u_1, ..., u_{k-2}, 1): ones at positions {inner} ∪ {k-1}
    # For v: rank of position 0 = 0 (it's the first 1), inner bits have ranks 1..x-1
    # For w: inner bits have ranks 0..x-2, position k-1 has rank x-1
    # So: rank of inner bit in v = rank_in_v = rank_in_w + 1
    # The 3-exponent for inner bit at rank r in v is 3^{x-1-r}
    # The 3-exponent for same inner bit at rank r-1 in w is 3^{x-1-(r-1)} = 3^{x-r}
    # So the coefficient in w is 3 times the coefficient in v for each inner bit.
    # This is why 3g(v) - g(w) cancels the inner terms!

    # GENERALIZATION: swap at positions i < j (not necessarily boundaries)
    # This changes the ranks of bits BETWEEN i and j.
    # The identity becomes more complex.

    # Let's try: swap bits at positions i and i+1 (ADJACENT swap)
    # v has bit pattern ..., v_i, v_{i+1}, ...
    # v' has ..., v_{i+1}, v_i, ...
    # If v_i = 1, v_{i+1} = 0: swap creates ..., 0, 1, ...

    # Effect on g: position i had a 1 (rank r), position i+1 had a 0
    # After swap: position i has 0, position i+1 has 1 (rank r)
    # g(v) has term 3^{x-1-r} · 2^i
    # g(v') has term 3^{x-1-r} · 2^{i+1} = 2 · 3^{x-1-r} · 2^i
    # So g(v') - g(v) = 3^{x-1-r} · 2^i (just the difference of this one term)
    # = (2-1) · 3^{x-1-r} · 2^i = 3^{x-1-r} · 2^i

    # Wait, but swapping adjacent bits (1,0) → (0,1) doesn't change ranks of OTHER bits!
    # Because the 1 that was at position i (rank r among all 1s) moves to position i+1
    # Its rank stays the same (it's still the r-th 1 from the left).
    # The ranks of all other 1s are unchanged.

    # So: g(v') - g(v) = 3^{x-1-r} · 2^{i+1} - 3^{x-1-r} · 2^i = 3^{x-1-r} · 2^i

    print("ADJACENT SWAP IDENTITY:")
    print("If v and v' differ by swapping adjacent bits (v_i=1, v_{i+1}=0)→(0,1):")
    print("  g(v') - g(v) = 3^{x-1-r} · 2^i")
    print("  where r = rank of position i among 1s in v")
    print()

    # This means: any parity vector can be transformed into any other
    # with the same number of 1s via adjacent transpositions,
    # and the g-value changes by known amounts at each step.

    # The TOTAL change from circuit v_c = 1^x 0^{k-x} to any v is:
    # g(v) - g(v_c) = Σ (changes from adjacent swaps)

    # For cycle: g(v) ≡ 0 mod d means g(v_c) + Δ ≡ 0 mod d
    # where Δ = g(v) - g(v_c) is a sum of terms 3^a · 2^b

    # g(v_c) = 3^x - 2^x (known). So:
    # 3^x - 2^x + Δ ≡ 0 mod d
    # Δ ≡ -(3^x - 2^x) ≡ 2^x - 3^x mod d
    # Since 3^x = 2^k - d: Δ ≡ 2^x - 2^k + d ≡ 2^x - 2^k mod d

    # So the constraint is: Δ ≡ 2^x - 2^k mod d
    # where Δ is a sum of terms ±3^a · 2^b determined by the transpositions.

    # This is a STRUCTURED SUBSET SUM problem mod d.

    # Can we prove this is impossible?

    # ═══════════════════════════════════════════════════════════════
    # TEST 4 : VÉRIFICATION — 0 EST-IL DANS L'IMAGE DE g MOD d ?
    # ═══════════════════════════════════════════════════════════════
    print("\n" + "=" * 60)
    print("TEST 4 : IMAGE DE g MOD d")
    print("=" * 60)

    for k in range(3, 14):
        for x in range(2, k):
            d = 2**k - 3**x
            if d <= 0 or d == 1:
                continue

            residues = set()
            total = 0
            for v in all_parity_vectors_aperiodic(k, x):
                total += 1
                g = compute_g(v, x)
                residues.add(g % d)

            if total == 0:
                continue

            has_zero = 0 in residues
            coverage = len(residues) / d * 100
            missing = d - len(residues)

            marker = "⚠️" if has_zero else "✅"
            print(f"  k={k:2d}, x={x}: d={d:>8d}, #vectors={total:>6d}, "
                  f"#residues={len(residues):>6d}/{d} ({coverage:.1f}%), "
                  f"missing={missing}, {marker} 0∈image={'YES' if has_zero else 'NO'}")


if __name__ == '__main__':
    main()
