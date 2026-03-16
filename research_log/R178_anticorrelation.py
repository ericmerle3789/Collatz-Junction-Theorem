#!/usr/bin/env python3
"""
R178c — L'ANTI-CORRÉLATION COMME MÉCANISME UNIVERSEL

CONTEXTE R178b :
- C1 (ord>S ⟹ résistant) VIOLÉE
- C3 (∃ p|d avec ord>S) VIOLÉE
- Mais g(v) ≢ 0 mod d semble TOUJOURS vrai !

FOCUS : Les cas "NO RESISTANT PRIME" — comment d ∤ g(v) survit-il
quand CHAQUE premier p|d est individuellement passable ?

RÉPONSE POSSIBLE : L'anti-corrélation entre divisibilités empêche
le passage SIMULTANÉ de tous les premiers.

Question formelle : Pour tout v apériodique, le vecteur de divisibilités
(1_{p_1|g}, 1_{p_2|g}, ..., 1_{p_r|g}) n'est JAMAIS (1,1,...,1).
"""

from itertools import combinations
from math import gcd
from collections import defaultdict


def multiplicative_order(a, n):
    if gcd(a, n) != 1:
        return None
    order = 1
    current = a % n
    while current != 1:
        current = (current * a) % n
        order += 1
        if order > n:
            return None
    return order


def prime_factors_set(n):
    if n <= 1:
        return set()
    factors = set()
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.add(d)
            n //= d
        d += 1
    if n > 1:
        factors.add(n)
    return factors


def compute_g(positions, x):
    return sum(3**(x-1-j) * 2**positions[j] for j in range(x))


def all_aperiodic_vectors(S, x):
    for positions in combinations(range(S), x):
        v = tuple(1 if i in positions else 0 for i in range(S))
        is_periodic = False
        for period in range(1, S):
            if S % period == 0 and period < S:
                if v == v[:period] * (S // period):
                    is_periodic = True
                    break
        if not is_periodic:
            yield positions


def main():
    print("=" * 80)
    print("R178c — L'ANTI-CORRÉLATION COMME MÉCANISME UNIVERSEL")
    print("=" * 80)

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 1 : Identification de TOUS les cas "no resistant prime"
    # ═══════════════════════════════════════════════════════════════════════
    print("\n" + "═" * 70)
    print("PARTIE 1 : CAS SANS PREMIER RÉSISTANT")
    print("═" * 70)

    anomalous_cases = []

    for S in range(3, 25):
        for x in range(2, min(S, 12)):
            d = 2**S - 3**x
            if d <= 1:
                continue

            primes = sorted(prime_factors_set(d))
            if not primes or len(primes) < 2:  # Need multiple primes
                continue

            # Skip if any prime is too large
            if max(primes) > 5 * 10**6:
                continue

            # Check resistance for each prime
            all_passable = True
            for p in primes:
                resistant = True
                for positions in all_aperiodic_vectors(S, x):
                    g = compute_g(positions, x)
                    if g % p == 0:
                        resistant = False
                        break
                if resistant:
                    all_passable = False
                    break

            if all_passable:
                anomalous_cases.append((S, x, d, primes))
                print(f"  S={S:2d}, x={x:2d}: d={d:>10d} = "
                      f"{'·'.join(str(p) for p in primes)}")

    print(f"\n  Total : {len(anomalous_cases)} cas anomaux trouvés")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 2 : Analyse détaillée de l'anti-corrélation
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 2 : STRUCTURE DE L'ANTI-CORRÉLATION")
    print("═" * 70)
    print("Pour chaque cas anomal, on examine le CRT : quel est le 'gap' ?")
    print("g(v) mod p₁ et g(v) mod p₂ sont-ils corrélés ?\n")

    for S, x, d, primes in anomalous_cases[:15]:  # Limit for output
        print(f"\n  --- S={S}, x={x}, d={d} = {'·'.join(str(p) for p in primes)} ---")

        # Build divisibility map
        div_sets = {p: [] for p in primes}
        residue_map = {}  # v -> (g mod p1, g mod p2, ...)
        total = 0

        for positions in all_aperiodic_vectors(S, x):
            total += 1
            g = compute_g(positions, x)
            residues = tuple(g % p for p in primes)
            residue_map[positions] = residues

            for i, p in enumerate(primes):
                if residues[i] == 0:
                    div_sets[p].append(positions)

        # Statistics per prime
        for p in primes:
            pct = 100 * len(div_sets[p]) / total if total > 0 else 0
            o = multiplicative_order(2, p)
            print(f"    p={p}: {len(div_sets[p])}/{total} vectors ({pct:.1f}%), "
                  f"ord_p(2)={o}")

        # Pairwise correlation
        if len(primes) >= 2:
            for i in range(len(primes)):
                for j in range(i+1, len(primes)):
                    p1, p2 = primes[i], primes[j]
                    s1 = set(range(len(div_sets[p1])))
                    s2 = set(range(len(div_sets[p2])))

                    # Count joint divisibility
                    joint = 0
                    for positions, res in residue_map.items():
                        if res[i] == 0 and res[j] == 0:
                            joint += 1

                    expected = len(div_sets[p1]) * len(div_sets[p2]) / total if total > 0 else 0
                    ratio = joint / expected if expected > 0 else float('inf')
                    print(f"    p₁={p1}, p₂={p2}: joint={joint}, "
                          f"expected={expected:.1f}, ratio={ratio:.3f}"
                          f"{' ← MUTUALLY EXCLUSIVE!' if joint == 0 else ''}")

        # Verify g ≡ 0 mod d indeed never happens
        count_zero = 0
        for positions, res in residue_map.items():
            if all(r == 0 for r in res):
                count_zero += 1
                g = compute_g(positions, x)
                print(f"    ⚠️ FOUND d|g : v={positions}, g={g}, g/d={g//d}")

        if count_zero == 0:
            print(f"    ✅ Confirmé : d ∤ g(v) pour tout v (anti-corrélation)")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 3 : Le spectre CRT — résidus joints
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 3 : LE SPECTRE CRT — QUELS RÉSIDUS JOINTS SONT ATTEINTS ?")
    print("═" * 70)

    for S, x, d, primes in anomalous_cases[:8]:
        if len(primes) > 3:
            continue  # Too many primes to display

        print(f"\n  --- S={S}, x={x}, d={d} = {'·'.join(str(p) for p in primes)} ---")

        # Image of g in Z/p₁ × Z/p₂ × ...
        image = defaultdict(int)
        total = 0

        for positions in all_aperiodic_vectors(S, x):
            total += 1
            g = compute_g(positions, x)
            res = tuple(g % p for p in primes)
            image[res] += 1

        # Count total possible residue tuples
        total_possible = 1
        for p in primes:
            total_possible *= p

        n_reached = len(image)
        zero_tuple = tuple(0 for _ in primes)

        print(f"    #vecteurs = {total}, #résidus joints atteints = {n_reached}/{total_possible}")
        print(f"    (0,...,0) atteint : {zero_tuple in image}")

        # Specifically check: which residues with r₁=0 are reached?
        if len(primes) == 2:
            p1, p2 = primes
            zero_in_p1 = [(r, image[(0, r)]) for r in range(p2) if (0, r) in image]
            zero_in_p2 = [(r, image[(r, 0)]) for r in range(p1) if (r, 0) in image]
            print(f"    g≡0 mod {p1}: reached residues mod {p2} = "
                  f"{[r for r, c in zero_in_p1]}")
            print(f"    g≡0 mod {p2}: reached residues mod {p1} = "
                  f"{[r for r, c in zero_in_p2]}")

            # What's the "missing" residue?
            if zero_in_p1:
                missing_p2 = set(range(p2)) - set(r for r, c in zero_in_p1)
                # Is 0 in the missing set?
                if 0 in missing_p2:
                    print(f"    → 0 mod {p2} is MISSING when g≡0 mod {p1} ✓")
            if zero_in_p2:
                missing_p1 = set(range(p1)) - set(r for r, c in zero_in_p2)
                if 0 in missing_p1:
                    print(f"    → 0 mod {p1} is MISSING when g≡0 mod {p2} ✓")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 4 : Le mécanisme structurel de l'exclusion mutuelle
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 4 : POURQUOI l'exclusion mutuelle ?")
    print("═" * 70)
    print("""
Quand p₁, p₂ | d et les deux ont petit ord_p(2) :

  2^{ord_p₁(2)} ≡ 1 mod p₁  et  2^{ord_p₂(2)} ≡ 1 mod p₂

  g(v) mod p₁ et g(v) mod p₂ sont des fonctions DIFFÉRENTES
  de v — elles "voient" des aspects différents du vecteur.

  L'exclusion mutuelle signifie :
  {v : p₁|g(v)} ∩ {v : p₂|g(v)} = ∅

  POURQUOI ? La relation g(v) = Σ 3^{x-1-j} · 2^{e_j} impose :

  g(v) ≡ 0 mod p₁ ⟹ certain pattern de e_j mod ord_p₁(2)
  g(v) ≡ 0 mod p₂ ⟹ certain pattern de e_j mod ord_p₂(2)

  Si lcm(ord_p₁, ord_p₂) > S, ces deux contraintes sur {e_j}
  ne peuvent pas être satisfaites simultanément !
""")

    # Test: Is lcm(ord1, ord2) > S the key condition?
    print("  TEST : lcm(ord_p₁, ord_p₂) > S ⟹ exclusion mutuelle ?\n")

    for S, x, d, primes in anomalous_cases:
        if len(primes) < 2:
            continue

        ords = {}
        for p in primes:
            ords[p] = multiplicative_order(2, p)

        # Check all pairs
        for i in range(len(primes)):
            for j in range(i+1, len(primes)):
                p1, p2 = primes[i], primes[j]
                o1, o2 = ords[p1], ords[p2]
                if o1 is None or o2 is None:
                    continue
                lcm_ords = o1 * o2 // gcd(o1, o2)

                # Check actual joint divisibility
                joint = 0
                total = 0
                for positions in all_aperiodic_vectors(S, x):
                    total += 1
                    g = compute_g(positions, x)
                    if g % p1 == 0 and g % p2 == 0:
                        joint += 1

                exclusive = joint == 0
                lcm_big = lcm_ords > S

                marker = ""
                if lcm_big and exclusive:
                    marker = "✅ lcm>S ⟹ exclusive (CONFIRMED)"
                elif lcm_big and not exclusive:
                    marker = "❌ lcm>S but NOT exclusive (VIOLATION!)"
                elif not lcm_big and exclusive:
                    marker = "⚠️ lcm≤S but still exclusive (STRONGER than needed)"
                else:
                    marker = "ℹ️ lcm≤S and not exclusive (normal)"

                print(f"  S={S:2d}, x={x}: p₁={p1}(ord={o1}), p₂={p2}(ord={o2}), "
                      f"lcm={lcm_ords}, lcm>S={lcm_big}, "
                      f"joint={joint}/{total}, {marker}")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 5 : Vérification de la conjecture LCM
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 5 : CONJECTURE LCM GÉNÉRALISÉE")
    print("═" * 70)
    print("""
CONJECTURE LCM : Pour d = 2^S - 3^x composite, les facteurs premiers p|d
satisfont TOUJOURS au moins une des conditions :
(A) ∃ p|d avec ord_p(2) > S (→ résistant par arc)
(B) Pour toute paire (p₁,p₂) avec p₁p₂|d, lcm(ord_p₁(2),ord_p₂(2)) > S
    (→ anti-corrélation)

Cela suffit car :
- (A) ⟹ d ∤ g (car ce p résiste)
- (B) ⟹ les divisibilités par différents premiers sont mutuellement exclusives
        ⟹ pas de v avec tous les premiers divisant g(v) simultanément
        ⟹ d ∤ g
""")

    # Test on ALL cases
    for S in range(3, 25):
        for x in range(2, min(S, 12)):
            d = 2**S - 3**x
            if d <= 1:
                continue

            primes = sorted(prime_factors_set(d))
            if len(primes) < 2:
                continue  # Single prime = needs different argument
            if max(primes) > 10**6:
                continue

            ords = {}
            skip = False
            for p in primes:
                o = multiplicative_order(2, p)
                if o is None:
                    skip = True
                    break
                ords[p] = o
            if skip:
                continue

            # Check condition A
            has_high_ord = any(o > S for o in ords.values())

            # Check condition B: for EVERY pair, lcm > S
            all_pairs_lcm_big = True
            min_lcm_ratio = float('inf')
            for i in range(len(primes)):
                for j in range(i+1, len(primes)):
                    p1, p2 = primes[i], primes[j]
                    lcm_ij = ords[p1] * ords[p2] // gcd(ords[p1], ords[p2])
                    min_lcm_ratio = min(min_lcm_ratio, lcm_ij / S)
                    if lcm_ij <= S:
                        all_pairs_lcm_big = False

            satisfies = has_high_ord or all_pairs_lcm_big

            if not satisfies:
                print(f"  ❌ S={S:2d}, x={x}: d={d} = {'·'.join(str(p) for p in primes)}, "
                      f"NO high-ord AND min_lcm/S={min_lcm_ratio:.2f}")
                for p in primes:
                    print(f"     p={p}, ord={ords[p]}")
            elif not has_high_ord:  # Relies on B only
                print(f"  ⚠️ S={S:2d}, x={x}: d={d} = {'·'.join(str(p) for p in primes)}, "
                      f"NO high-ord but lcm>S saves it (min_lcm/S={min_lcm_ratio:.2f})")

    print("\n\n" + "═" * 70)
    print("SYNTHÈSE R178c")
    print("═" * 70)


if __name__ == '__main__':
    main()
