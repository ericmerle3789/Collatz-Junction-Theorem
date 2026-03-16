#!/usr/bin/env python3
"""
R175 — L'ANNEAU QUOTIENT Z[2]/(2^S - 3^x) ET L'INVERSIBILITÉ DE g
=====================================================================

IDÉE : Dans l'anneau Z/dZ (où d = 2^S - 3^x), la condition g(v) ≡ 0 mod d
est équivalente à g(v) = 0 dans Z/dZ.

Question : g(v) est-il TOUJOURS inversible dans Z/dZ ?
Si oui : g(v) est une unité, donc jamais zéro → preuve !

Condition d'inversibilité : gcd(g(v), d) = 1.

ATTENTION : g(v) = 0 mod d signifie d | g(v), i.e., gcd(g(v), d) = d.
On veut montrer gcd(g(v), d) < d, voire gcd(g(v), d) = 1.

Explorer : pour chaque (S, x, v), calculer gcd(g(v), d) et voir si c'est
toujours 1 (inversible) ou au moins < d (non-zéro).
"""

from itertools import combinations
from math import gcd, log2, ceil
from collections import Counter


def compute_g(positions, x):
    """g = Σ 3^{x-1-j} · 2^{e_j} where positions = (e_0, ..., e_{x-1}) sorted."""
    return sum(3**(x-1-j) * 2**positions[j] for j in range(x))


def all_aperiodic_vectors(S, x):
    """Generate all aperiodic position tuples (e_0 < ... < e_{x-1})."""
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
    print("=" * 72)
    print("R175 — GCD(g(v), d) : VERS L'INVERSIBILITÉ UNIVERSELLE")
    print("=" * 72)

    # ═══════════════════════════════════════════════════════════════
    # TEST 1 : gcd(g(v), d) pour tous les vecteurs apériodiques
    # ═══════════════════════════════════════════════════════════════
    print("\n" + "=" * 60)
    print("TEST 1 : DISTRIBUTION DE gcd(g(v), d)")
    print("=" * 60)

    for S in range(3, 18):
        for x in range(2, S):
            d = 2**S - 3**x
            if d <= 0 or d == 1:
                continue

            gcd_counter = Counter()
            total = 0
            max_gcd = 0

            for positions in all_aperiodic_vectors(S, x):
                total += 1
                g = compute_g(positions, x)
                gc = gcd(g, d)
                gcd_counter[gc] += 1
                if gc > max_gcd:
                    max_gcd = gc
                    max_gcd_pos = positions

            if total == 0:
                continue

            n_coprime = gcd_counter.get(1, 0)
            n_zero = gcd_counter.get(d, 0)  # gcd = d means d | g

            pct_coprime = 100 * n_coprime / total
            marker = "✅" if n_zero == 0 else "⚠️"

            # Compact display
            if total <= 200 or n_zero > 0 or max_gcd > 1:
                non_trivial = {k: v for k, v in gcd_counter.items() if k > 1}
                print(f"  S={S:2d}, x={x}: d={d:>8d}, #vec={total:>6d}, "
                      f"{marker} coprime={pct_coprime:.1f}%, max_gcd={max_gcd}"
                      f"{'  NON-COPRIME: ' + str(dict(sorted(non_trivial.items()))) if non_trivial else ''}")

    # ═══════════════════════════════════════════════════════════════
    # TEST 2 : Facteurs communs — quels premiers p divisant d
    #          divisent aussi g(v) ?
    # ═══════════════════════════════════════════════════════════════
    print("\n\n" + "=" * 60)
    print("TEST 2 : POUR QUELS p | d A-T-ON p | g(v) ?")
    print("=" * 60)

    def prime_factors(n):
        """Return set of prime factors of n."""
        if n <= 1:
            return set()
        factors = set()
        d_temp = 2
        while d_temp * d_temp <= n:
            while n % d_temp == 0:
                factors.add(d_temp)
                n //= d_temp
            d_temp += 1
        if n > 1:
            factors.add(n)
        return factors

    for S in range(3, 16):
        for x in range(2, S):
            d = 2**S - 3**x
            if d <= 0 or d == 1:
                continue

            primes_of_d = prime_factors(d)
            if not primes_of_d:
                continue

            # For each prime p | d, count how many vectors have p | g(v)
            p_divides_count = {p: 0 for p in primes_of_d}
            total = 0

            for positions in all_aperiodic_vectors(S, x):
                total += 1
                g = compute_g(positions, x)
                for p in primes_of_d:
                    if g % p == 0:
                        p_divides_count[p] += 1

            if total == 0:
                continue

            # How many vectors have ALL primes dividing g?
            n_all_divide = 0
            for positions in all_aperiodic_vectors(S, x):
                g = compute_g(positions, x)
                if all(g % p == 0 for p in primes_of_d):
                    n_all_divide += 1

            info = ", ".join(f"p={p}:{p_divides_count[p]}/{total}" for p in sorted(primes_of_d))
            marker = "✅" if n_all_divide == 0 else "⚠️"
            print(f"  S={S:2d}, x={x}: d={d}, primes={sorted(primes_of_d)}, "
                  f"{marker} all_divide={n_all_divide}, per_prime=[{info}]")

    # ═══════════════════════════════════════════════════════════════
    # TEST 3 : Structure du gcd — est-ce toujours 1 ?
    # ═══════════════════════════════════════════════════════════════
    print("\n\n" + "=" * 60)
    print("TEST 3 : gcd(g(v), d) = 1 UNIVERSELLEMENT ?")
    print("=" * 60)

    all_coprime = True
    counterexamples = []

    for S in range(3, 16):
        for x in range(2, S):
            d = 2**S - 3**x
            if d <= 0 or d == 1:
                continue

            for positions in all_aperiodic_vectors(S, x):
                g = compute_g(positions, x)
                gc = gcd(g, d)
                if gc > 1:
                    all_coprime = False
                    if len(counterexamples) < 20:
                        counterexamples.append((S, x, positions, g, d, gc))

    if all_coprime:
        print("  🏆 RÉSULTAT : gcd(g(v), d) = 1 pour TOUS les (S, x, v) testés !")
        print("  Cela signifie g(v) est TOUJOURS inversible dans Z/dZ.")
        print("  Si cela se prouve universellement → PREUVE DE L'ABSENCE DE CYCLES !")
    else:
        print(f"  ❌ Contre-exemples trouvés ({len(counterexamples)}) :")
        for S, x, pos, g, d, gc in counterexamples:
            v_str = ''.join('1' if i in pos else '0' for i in range(S))
            print(f"    S={S}, x={x}, v={v_str}: g={g}, d={d}, gcd={gc}")
            # Check if g ≡ 0 mod d
            print(f"      g mod d = {g % d}, d | g : {g % d == 0}")

        print(f"\n  NOTE : gcd > 1 ne signifie PAS que d | g.")
        print(f"  Il faut vérifier si gcd = d (i.e., d | g) pour un contre-exemple au théorème.")

        # Verify: among counterexamples, is gcd ever equal to d?
        full_divides = [ce for ce in counterexamples if ce[5] == ce[4]]
        if not full_divides:
            print(f"\n  ✅ AUCUN cas avec gcd = d. Donc 0 ∉ Image(g mod d) confirmé !")
            print(f"  Mais gcd > 1 pour certains vecteurs → g n'est PAS toujours inversible.")
            print(f"  La conjecture d'inversibilité (gcd=1 toujours) est FAUSSE.")
            print(f"  La conjecture de non-annulation (gcd < d toujours) reste VRAIE.")

    # ═══════════════════════════════════════════════════════════════
    # TEST 4 : Quels diviseurs communs apparaissent ?
    # ═══════════════════════════════════════════════════════════════
    if not all_coprime:
        print("\n\n" + "=" * 60)
        print("TEST 4 : ANALYSE DES DIVISEURS COMMUNS")
        print("=" * 60)

        for S in range(3, 16):
            for x in range(2, S):
                d = 2**S - 3**x
                if d <= 0 or d == 1:
                    continue

                gcd_set = set()
                for positions in all_aperiodic_vectors(S, x):
                    g = compute_g(positions, x)
                    gc = gcd(g, d)
                    if gc > 1:
                        gcd_set.add(gc)

                if gcd_set:
                    # For each non-trivial gcd, what fraction of d is it?
                    info = ", ".join(f"{gc}(={gc}/{d})" for gc in sorted(gcd_set))
                    print(f"  S={S:2d}, x={x}: d={d}, non-trivial gcds: {info}")
                    # Key: is d/gcd always > 1? (yes, by definition since gcd < d)
                    # What are the prime factors of these gcds?
                    for gc in sorted(gcd_set):
                        pf = sorted(prime_factors(gc))
                        print(f"    gcd={gc}, prime factors={pf}, d/gcd={d//gc}")


if __name__ == '__main__':
    main()
