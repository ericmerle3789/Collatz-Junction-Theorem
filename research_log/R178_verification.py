#!/usr/bin/env python3
"""
R178d — VÉRIFICATION CRUCIALE : d | g(v) arrive-t-il vraiment ?

BUG DÉTECTÉ dans R178c : le code vérifiait la divisibilité par les
facteurs PREMIERS de d, mais PAS par les puissances premières.

Exemple : d = 1805 = 5·19². Le code vérifiait 5|g ET 19|g (= 95|g),
mais il faut vérifier 5|g ET 19²|g (= 1805|g).

Ce script vérifie DIRECTEMENT si d | g(v) pour des vecteurs apériodiques.
"""

from itertools import combinations
from math import gcd


def compute_g(positions, x):
    return sum(3**(x-1-j) * 2**positions[j] for j in range(x))


def prime_factorization(n):
    """Return dict {p: exponent} for prime factorization."""
    if n <= 1:
        return {}
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
    print("R178d — VÉRIFICATION : d | g(v) se produit-il ?")
    print("=" * 80)

    # ═══════════════════════════════════════════════════════════════════════
    # TEST DIRECT : d | g(v) pour chaque (S, x)
    # ═══════════════════════════════════════════════════════════════════════
    print("\nTest direct g(v) mod d == 0 pour vecteurs apériodiques :\n")

    found_any = False

    for S in range(3, 25):
        for x in range(2, min(S, 12)):
            d = 2**S - 3**x
            if d <= 1:
                continue

            factors = prime_factorization(d)
            is_squarefree = all(e == 1 for e in factors.values())

            count_zero = 0
            total = 0

            for positions in all_aperiodic_vectors(S, x):
                total += 1
                if total > 50000:
                    break
                g = compute_g(positions, x)
                if g % d == 0:
                    count_zero += 1
                    n_min = g // d
                    if count_zero <= 3:
                        print(f"  ⚠️ S={S}, x={x}: d={d}"
                              f" ({'·'.join(f'{p}^{e}' if e>1 else str(p) for p,e in sorted(factors.items()))})"
                              f" | g({positions})={g}, n_min={n_min}"
                              f" {'[squarefree]' if is_squarefree else '[NOT squarefree]'}")
                        found_any = True

            if count_zero > 0:
                print(f"  → S={S}, x={x}: {count_zero}/{total} "
                      f"vecteurs avec d|g ({100*count_zero/total:.2f}%)")
            elif S <= 16:
                # Only print "clean" for small S to keep output manageable
                pass

    if not found_any:
        print("  ✅ Aucun cas d | g(v) trouvé !")

    # ═══════════════════════════════════════════════════════════════════════
    # FOCUS : le cas S=11, x=5, d=1805 (fausse alerte dans R178c)
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("FOCUS : S=11, x=5, d=1805")
    print("═" * 70)

    S, x = 11, 5
    d = 2**S - 3**x  # = 1805
    factors = prime_factorization(d)
    print(f"  d = {d} = {'·'.join(f'{p}^{e}' if e>1 else str(p) for p,e in sorted(factors.items()))}")

    for positions in all_aperiodic_vectors(S, x):
        g = compute_g(positions, x)
        r5 = g % 5
        r19 = g % 19
        r19sq = g % (19**2)
        rd = g % d

        if r5 == 0 and r19 == 0:
            print(f"  v={positions}: g={g}, "
                  f"g%5={r5}, g%19={r19}, g%361={r19sq}, g%1805={rd}"
                  f" {'← d|g !' if rd == 0 else ''}")

    # ═══════════════════════════════════════════════════════════════════════
    # CORRECTED resistance analysis : use prime POWERS
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("ANALYSE DE RÉSISTANCE CORRIGÉE (puissances premières)")
    print("═" * 70)
    print("On vérifie si p^a | g(v) (pas juste p | g(v))\n")

    anomalous_count = 0

    for S in range(3, 22):
        for x in range(2, min(S, 10)):
            d = 2**S - 3**x
            if d <= 1:
                continue

            factors = prime_factorization(d)
            prime_powers = {p: p**e for p, e in factors.items()}

            if len(factors) < 2:
                continue

            # For each prime power p^a || d, check if p^a | g(v) for some v
            pp_passable = {}
            for p, e in factors.items():
                pa = p**e
                passable = False
                for positions in all_aperiodic_vectors(S, x):
                    g = compute_g(positions, x)
                    if g % pa == 0:
                        passable = True
                        break
                pp_passable[p] = passable

            all_pp_passable = all(pp_passable.values())

            if all_pp_passable:
                anomalous_count += 1
                pp_str = ", ".join(f"{p}^{e}:{'💀' if pp_passable[p] else '🛡️'}"
                                   for p, e in sorted(factors.items()))

                # Verify d ∤ g(v) for all v
                any_d_div_g = False
                for positions in all_aperiodic_vectors(S, x):
                    g = compute_g(positions, x)
                    if g % d == 0:
                        any_d_div_g = True
                        break

                status = "❌ d|g EXISTS!" if any_d_div_g else "✅ d∤g (anti-corr saves)"
                print(f"  S={S:2d}, x={x}: d={d:>10d} = "
                      f"{'·'.join(f'{p}^{e}' if e>1 else str(p) for p,e in sorted(factors.items()))}"
                      f" | ALL pp passable | {status}")

    print(f"\n  Total cas 'all prime-powers passable': {anomalous_count}")

    # ═══════════════════════════════════════════════════════════════════════
    # OVERALL STATISTICS
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("STATISTIQUE GLOBALE : d | g(v) se produit-il ?")
    print("═" * 70)

    n_cases = 0
    n_d_divides = 0

    for S in range(3, 23):
        for x in range(2, min(S, 10)):
            d = 2**S - 3**x
            if d <= 1:
                continue

            n_cases += 1
            found = False
            count = 0
            for positions in all_aperiodic_vectors(S, x):
                count += 1
                if count > 100000:
                    break
                g = compute_g(positions, x)
                if g % d == 0:
                    found = True
                    break

            if found:
                n_d_divides += 1

    print(f"  Cas testés : {n_cases}")
    print(f"  Cas avec d | g(v) : {n_d_divides}")
    print(f"  Cas SANS d | g(v) : {n_cases - n_d_divides}")

    if n_d_divides == 0:
        print("\n  🎯 g(v) ≡ 0 mod d n'arrive JAMAIS pour les vecteurs apériodiques !")
        print("  C'est ce qu'on veut prouver universellement.")
    else:
        print(f"\n  ⚠️ {n_d_divides} cas avec d | g(v) — analyser en détail")


if __name__ == '__main__':
    main()
