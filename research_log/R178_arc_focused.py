#!/usr/bin/env python3
"""
R178b — FOCUSED ARC ARGUMENT

KEY QUESTION from R178a: There are violations of ord_p(2) > S for the LARGEST
prime factor. But the R175 claim was about the RESISTANT prime.

This script answers the PRECISE question:
1. For each (S,x), is there ALWAYS a prime p|d with ord_p(2) > S?
2. When ord_p(2) ≤ S, does wrapping allow p|g(v)?
3. When ord_p(2) > S (no wrapping), is p ALWAYS resistant?

If the answer to all 3 is YES, the structure is:
  ord > S → no wrapping → resistant → at least one always exists → g ≢ 0 mod d
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
    print("R178b — FOCUSED ARC ARGUMENT")
    print("=" * 80)

    # ═══════════════════════════════════════════════════════════════════════
    # For each (S,x), classify EVERY prime factor of d
    # ═══════════════════════════════════════════════════════════════════════

    print("\n" + "═" * 70)
    print("CLASSIFICATION COMPLÈTE DE CHAQUE PREMIER p | d")
    print("═" * 70)
    print("Pour chaque p | d : ord_p(2), résistance (p ∤ g(v) ∀ v), wrapping\n")

    universal_results = []  # Will track if there's always a "high-ord resistant" prime

    for S in range(3, 22):  # Limit for tractability
        for x in range(2, min(S, 10)):
            d = 2**S - 3**x
            if d <= 1:
                continue

            primes = sorted(prime_factors_set(d))
            if not primes:
                continue

            # For each prime, compute:
            # 1. ord_p(2)
            # 2. Whether p | g(v) for some aperiodic v (resistance)
            # 3. Whether ord > S (no wrapping)

            prime_info = []
            skip = False

            for p in primes:
                if p > 5 * 10**6:
                    skip = True
                    break

                o = multiplicative_order(2, p)
                if o is None:
                    skip = True
                    break

                # Check resistance: is there any v with p | g(v)?
                is_resistant = True
                for positions in all_aperiodic_vectors(S, x):
                    g = compute_g(positions, x)
                    if g % p == 0:
                        is_resistant = False
                        break

                high_ord = o > S
                prime_info.append({
                    'p': p, 'ord': o, 'resistant': is_resistant,
                    'high_ord': high_ord
                })

            if skip:
                continue

            # Key properties
            has_high_ord_resistant = any(
                pi['high_ord'] and pi['resistant'] for pi in prime_info
            )
            has_any_resistant = any(pi['resistant'] for pi in prime_info)
            all_high_ord_are_resistant = all(
                pi['resistant'] for pi in prime_info if pi['high_ord']
            )
            all_low_ord_are_passable = all(
                not pi['resistant'] for pi in prime_info if not pi['high_ord']
            )

            universal_results.append({
                'S': S, 'x': x, 'd': d,
                'has_high_ord_resistant': has_high_ord_resistant,
                'has_any_resistant': has_any_resistant,
                'all_high_ord_are_resistant': all_high_ord_are_resistant,
                'all_low_ord_are_passable': all_low_ord_are_passable,
                'primes': prime_info
            })

            # Print details
            info_strs = []
            for pi in prime_info:
                symbol = "🛡️" if pi['resistant'] else "💀"
                ord_sym = "H" if pi['high_ord'] else "L"
                info_strs.append(
                    f"p={pi['p']}(ord={pi['ord']},{ord_sym},{symbol})"
                )

            status = ""
            if has_high_ord_resistant:
                status = "✅ high-ord resistant exists"
            elif has_any_resistant:
                status = "⚠️ resistant exists but with LOW ord!"
            else:
                status = "❌ NO RESISTANT PRIME!"

            print(f"  S={S:2d}, x={x:2d}: d={d:>10d} | "
                  f"{' '.join(info_strs)} | {status}")

    # ═══════════════════════════════════════════════════════════════════════
    # GLOBAL STATISTICS
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("STATISTIQUES GLOBALES")
    print("═" * 70)

    total = len(universal_results)
    n_high_ord_resistant = sum(1 for r in universal_results if r['has_high_ord_resistant'])
    n_any_resistant = sum(1 for r in universal_results if r['has_any_resistant'])
    n_all_high_resistant = sum(1 for r in universal_results if r['all_high_ord_are_resistant'])
    n_all_low_passable = sum(1 for r in universal_results if r['all_low_ord_are_passable'])

    print(f"  Total cases tested: {total}")
    print(f"  Has HIGH-ORD resistant prime: {n_high_ord_resistant}/{total} "
          f"({100*n_high_ord_resistant/total:.1f}%)")
    print(f"  Has ANY resistant prime: {n_any_resistant}/{total} "
          f"({100*n_any_resistant/total:.1f}%)")
    print(f"  ALL high-ord primes are resistant: {n_all_high_resistant}/{total} "
          f"({100*n_all_high_resistant/total:.1f}%)")
    print(f"  ALL low-ord primes are passable: {n_all_low_passable}/{total} "
          f"({100*n_all_low_passable/total:.1f}%)")

    # ═══════════════════════════════════════════════════════════════════════
    # KEY CONJECTURE CHECK
    # ═══════════════════════════════════════════════════════════════════════
    print("\n" + "═" * 70)
    print("VÉRIFICATION DES TROIS CONJECTURES")
    print("═" * 70)

    print("\n  CONJECTURE 1: ord_p(2) > S ⟹ p résistant (p ∤ g(v) ∀v)")
    c1_violations = []
    for r in universal_results:
        for pi in r['primes']:
            if pi['high_ord'] and not pi['resistant']:
                c1_violations.append((r['S'], r['x'], pi['p'], pi['ord']))
    if c1_violations:
        print(f"  ❌ VIOLÉE ! {len(c1_violations)} contre-exemples :")
        for S, x, p, o in c1_violations[:10]:
            print(f"    S={S}, x={x}: p={p}, ord={o}")
    else:
        print(f"  ✅ VÉRIFIÉE sur {total} cas — Aucune violation !")

    print("\n  CONJECTURE 2: ord_p(2) ≤ S ⟹ p passable (∃v: p | g(v))")
    c2_violations = []
    for r in universal_results:
        for pi in r['primes']:
            if not pi['high_ord'] and pi['resistant']:
                c2_violations.append((r['S'], r['x'], pi['p'], pi['ord']))
    if c2_violations:
        print(f"  ❌ VIOLÉE ! {len(c2_violations)} contre-exemples :")
        for S, x, p, o in c2_violations[:10]:
            print(f"    S={S}, x={x}: p={p}, ord={o}")
    else:
        print(f"  ✅ VÉRIFIÉE sur {total} cas — Aucune violation !")

    print("\n  CONJECTURE 3: ∀(S,x), ∃ p|d avec ord_p(2) > S")
    c3_violations = []
    for r in universal_results:
        has_high = any(pi['high_ord'] for pi in r['primes'])
        if not has_high:
            c3_violations.append((r['S'], r['x'], r['d'],
                                  [(pi['p'], pi['ord']) for pi in r['primes']]))
    if c3_violations:
        print(f"  ❌ VIOLÉE ! {len(c3_violations)} contre-exemples :")
        for S, x, d, details in c3_violations[:10]:
            print(f"    S={S}, x={x}: d={d}, primes={details}")
    else:
        print(f"  ✅ VÉRIFIÉE sur {total} cas — Aucune violation !")

    # ═══════════════════════════════════════════════════════════════════════
    # COMBINED: If C1+C2+C3 all hold, the proof structure is complete
    # ═══════════════════════════════════════════════════════════════════════
    print("\n" + "═" * 70)
    print("CONCLUSION")
    print("═" * 70)

    if not c1_violations and not c3_violations:
        print("""
  🎯 Si C1 et C3 sont des THÉORÈMES (pas juste conjectures), alors :

  PREUVE :
  1. Par C3 : ∀(S,x), ∃ p | d avec ord_p(2) > S.
  2. Par C1 : Ce p est résistant (p ∤ g(v) ∀v apériodique).
  3. Donc p | d mais p ∤ g(v), donc d ∤ g(v).
  4. Donc corrSum ≢ 0 mod d.
  5. Par le Junction Theorem : aucun k-cycle n'existe. ∎

  RESTE À PROUVER :
  (A) C3 : ∃ p|d avec ord_p(2) > S. Pourquoi toujours ?
  (B) C1 : ord_p(2) > S ⟹ p résistant. Pourquoi ?

  (B) est le plus intéressant — c'est l'"argument d'arc" :
  quand l'ordre est trop grand, les puissances de 2 dans l'expression
  de g(v) ne "wrappent" pas, empêchant la cancellation.
""")
        if not c2_violations:
            print("  BONUS : C2 aussi vérifiée — l'équivalence est PARFAITE :")
            print("    ord_p(2) > S ⟺ p résistant")
            print("  Cela renforce la compréhension de la structure.")
    else:
        if c1_violations:
            print("  C1 violée — l'arc argument ne suffit pas seul.")
        if c3_violations:
            print("  C3 violée — il n'y a pas toujours un premier à grand ordre.")
            print("  Examiner les contre-exemples.")

    # ═══════════════════════════════════════════════════════════════════════
    # Deep analysis of C1: WHY does high ord imply resistance?
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("ANALYSE DE C1 : POURQUOI ord > S ⟹ RÉSISTANCE ?")
    print("═" * 70)
    print("""
Quand ord_p(2) > S et 3 ∈ ⟨2⟩ mod p :

g(v) = Σ_{j=0}^{x-1} 2^{f_j} mod p, f_j = t(x-1-j) + e_j.

Max(f_j) ≤ t(x-1) + (S-1).
Min(f_j) ≥ 0 + 0 = 0.

Si max(f_j) < ord_p(2) : PAS DE WRAPPING.
Condition : t(x-1) + S - 1 < ord_p(2).

Quand il n'y a pas de wrapping, les 2^{f_j} dans F_p* sont DISTINCTS
(car f_j ≠ f_k mod ord implique f_j ≠ f_k tout court).

Somme de puissances distinctes de 2 sans wrapping :
  Σ 2^{f_j} (dans Z) est la valeur même (pas de réduction nécessaire).
  Pour que Σ ≡ 0 mod p : p | Σ dans Z.
  Mais Σ ∈ [x, x · 2^{max_f}].

Pour que p | Σ : Σ ≥ p, i.e., x · 2^{max_f} ≥ p.
Mais p | (2^S - 3^x) et p ≈ d = 2^S - 3^x...

Vérifions la borne : est-ce que la somme dans Z dépasse p ?
""")

    for S in range(5, 18):
        for x in range(2, min(S, 7)):
            d = 2**S - 3**x
            if d <= 1:
                continue

            primes = sorted(prime_factors_set(d))

            for p in primes:
                if p > 10**6:
                    continue
                o = multiplicative_order(2, p)
                if o is None or o <= S:
                    continue

                # Find t
                t = None
                power = 1
                for k in range(1, min(o + 1, p)):
                    power = power * 2 % p
                    if power == 3 % p:
                        t = k
                        break

                if t is None:
                    # 3 not in <2> mod p
                    tag = "3∉⟨2⟩"
                else:
                    max_f = t * (x - 1) + (S - 1)
                    no_wrap = max_f < o
                    tag = f"t={t}, max_f={max_f}, no_wrap={no_wrap}"

                    if no_wrap:
                        # Compute actual sum bounds in Z
                        sum_min = float('inf')
                        sum_max = 0
                        count = 0
                        for positions in all_aperiodic_vectors(S, x):
                            count += 1
                            if count > 5000:
                                break
                            exps = [t*(x-1-j) + positions[j] for j in range(x)]
                            s = sum(2**f for f in exps)
                            sum_min = min(sum_min, s)
                            sum_max = max(sum_max, s)

                        if count > 0:
                            import math
                            ratio_max = sum_max / p
                            ratio_min = sum_min / p
                            print(f"  S={S:2d}, x={x}: p={p:>8d}, ord={o:>6d}, {tag}")
                            print(f"    Σ(Z) ∈ [{sum_min}, {sum_max}], "
                                  f"Σ/p ∈ [{ratio_min:.2f}, {ratio_max:.2f}]")
                            if sum_max < p:
                                print(f"    🎯 Σ < p toujours → SIZE PROOF !")
                            elif sum_min > p:
                                # Could still avoid multiples
                                n_mult = sum_max // p - (sum_min - 1) // p
                                print(f"    Multiples de p dans intervalle: ≤ {n_mult}")


if __name__ == '__main__':
    main()
