#!/usr/bin/env python3
"""
R175b — LE PREMIER RÉSISTANT : Pourquoi gcd(g(v), d) ne peut jamais atteindre d

OBSERVATION de R175 : Pour chaque (S, x), gcd(g(v), d) < d pour tout v.
Quand d a plusieurs facteurs premiers, le gcd peut absorber TOUS sauf un.

QUESTION : Y a-t-il TOUJOURS un premier "résistant" p | d tel que p ∤ g(v)
pour tout v apériodique ?

OU BIEN : pour chaque p | d, il existe un v_p avec p | g(v_p), mais il
n'existe PAS de v tel que p | g(v) pour TOUS les p | d simultanément ?
"""

from itertools import combinations
from math import gcd
from collections import defaultdict


def compute_g(positions, x):
    return sum(3**(x-1-j) * 2**positions[j] for j in range(x))


def prime_factors(n):
    if n <= 1:
        return []
    factors = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.append(d)
            n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors


def prime_factors_set(n):
    return set(prime_factors(n))


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
    print("=" * 72)
    print("R175b — ANALYSE DU PREMIER RÉSISTANT")
    print("=" * 72)

    # ═══════════════════════════════════════════════════════════════
    # TEST 1 : Pour chaque (S, x), identifier le "premier résistant"
    # ═══════════════════════════════════════════════════════════════
    print("\nPour chaque (S,x), quel(s) premier(s) p | d ne divise(nt) JAMAIS g(v) ?")
    print("(Ces premiers 'résistants' empêchent gcd = d)\n")

    for S in range(3, 18):
        for x in range(2, S):
            d = 2**S - 3**x
            if d <= 0 or d == 1:
                continue

            primes = sorted(prime_factors_set(d))
            if len(primes) == 0:
                continue

            # Pour chaque premier p | d, trouver les vecteurs avec p | g(v)
            divisible_by = {p: set() for p in primes}
            all_vectors = []

            for positions in all_aperiodic_vectors(S, x):
                g = compute_g(positions, x)
                all_vectors.append((positions, g))
                for p in primes:
                    if g % p == 0:
                        divisible_by[p].add(len(all_vectors) - 1)

            total = len(all_vectors)
            if total == 0:
                continue

            # Premiers résistants = ceux pour lesquels divisible_by[p] est vide
            resistant = [p for p in primes if len(divisible_by[p]) == 0]
            # Premiers passants = ceux pour lesquels au moins un vecteur satisfait p | g
            passing = [p for p in primes if len(divisible_by[p]) > 0]

            # L'intersection : vecteurs divisibles par TOUS les premiers passants
            if passing:
                intersection = divisible_by[passing[0]]
                for p in passing[1:]:
                    intersection = intersection & divisible_by[p]
                n_all_passing = len(intersection)
            else:
                n_all_passing = total  # No passing primes means... d is prime

            if len(primes) >= 2 or resistant:
                pct_per_prime = ", ".join(
                    f"p={p}:{len(divisible_by[p])*100//total}%"
                    for p in primes
                )
                print(f"  S={S:2d}, x={x}: d={d:>6d} = {'·'.join(str(p) for p in primes)}"
                      f"  resistant={resistant}, "
                      f"per_prime=[{pct_per_prime}], "
                      f"∩(all passing)={n_all_passing}")

    # ═══════════════════════════════════════════════════════════════
    # TEST 2 : Quand d est PREMIER, p = d est toujours résistant
    # ═══════════════════════════════════════════════════════════════
    print("\n\n" + "=" * 60)
    print("TEST 2 : CAS d PREMIER — N₀(d) mod d directement")
    print("=" * 60)

    for S in range(3, 18):
        for x in range(2, S):
            d = 2**S - 3**x
            if d <= 1:
                continue

            primes = prime_factors_set(d)
            if len(primes) != 1 or d not in primes:
                continue  # d is not prime

            # d is prime. Count g(v) ≡ 0 mod d.
            count_zero = 0
            total = 0
            residues = set()

            for positions in all_aperiodic_vectors(S, x):
                total += 1
                g = compute_g(positions, x)
                r = g % d
                residues.add(r)
                if r == 0:
                    count_zero += 1

            if total == 0:
                continue

            print(f"  S={S:2d}, x={x}: d={d} (PRIME), "
                  f"0 ∈ Image: {'YES' if 0 in residues else 'NO'}, "
                  f"#residues={len(residues)}/{d}, "
                  f"coverage={100*len(residues)/d:.1f}%")

    # ═══════════════════════════════════════════════════════════════
    # TEST 3 : Le phénomène de "résistance par corrélation"
    # ═══════════════════════════════════════════════════════════════
    print("\n\n" + "=" * 60)
    print("TEST 3 : CORRÉLATION ENTRE DIVISIBILITÉS")
    print("=" * 60)
    print("Pour d composite : si p₁|g ET p₂|g, ça devrait arriver ~1/p₁p₂ du temps.")
    print("Si c'est MOINS fréquent → corrélation NÉGATIVE (les divisibilités s'excluent).\n")

    for S in range(3, 18):
        for x in range(2, S):
            d = 2**S - 3**x
            if d <= 0 or d == 1:
                continue

            primes = sorted(prime_factors_set(d))
            if len(primes) < 2:
                continue

            # Count vectors divisible by each prime and by pairs
            div_count = {p: 0 for p in primes}
            pair_count = {}
            for i in range(len(primes)):
                for j in range(i+1, len(primes)):
                    pair_count[(primes[i], primes[j])] = 0

            total = 0
            for positions in all_aperiodic_vectors(S, x):
                total += 1
                g = compute_g(positions, x)
                divs = [p for p in primes if g % p == 0]
                for p in divs:
                    div_count[p] += 1
                for i in range(len(divs)):
                    for j in range(i+1, len(divs)):
                        pair_count[(divs[i], divs[j])] += 1

            if total == 0:
                continue

            # Check correlation
            interesting = False
            corr_info = []
            for (p1, p2), joint in pair_count.items():
                expected = div_count[p1] * div_count[p2] / total
                actual = joint
                if expected > 0.5:  # Only report if expected is meaningful
                    ratio = actual / expected if expected > 0 else float('inf')
                    corr_info.append(f"({p1},{p2}): exp={expected:.1f}, actual={actual}, ratio={ratio:.2f}")
                    if ratio < 0.5 or ratio > 2:
                        interesting = True

            if corr_info and (interesting or total < 500):
                print(f"  S={S:2d}, x={x}: d={d} = {'·'.join(str(p) for p in primes)}, n={total}")
                for info in corr_info:
                    print(f"    {info}")

    # ═══════════════════════════════════════════════════════════════
    # TEST 4 : Le "dernier premier" — lequel résiste toujours ?
    # ═══════════════════════════════════════════════════════════════
    print("\n\n" + "=" * 60)
    print("TEST 4 : QUEL PREMIER RÉSISTE ?")
    print("=" * 60)
    print("Pour d composite : on approche d en accumulant des facteurs dans gcd.")
    print("Quel est le DERNIER facteur premier qui n'est jamais atteint ?\n")

    for S in range(3, 18):
        for x in range(2, S):
            d = 2**S - 3**x
            if d <= 0 or d == 1:
                continue

            primes = sorted(prime_factors_set(d))
            if len(primes) < 2:
                continue

            # For each vector, compute the set of primes dividing g
            max_prime_set = set()
            max_gcd_val = 0

            for positions in all_aperiodic_vectors(S, x):
                g = compute_g(positions, x)
                gc = gcd(g, d)
                if gc > max_gcd_val:
                    max_gcd_val = gc
                    max_prime_set = prime_factors_set(gc)

            remaining = set(primes) - max_prime_set
            if remaining:
                print(f"  S={S:2d}, x={x}: d={d} = {'·'.join(str(p) for p in primes)}, "
                      f"max_gcd={max_gcd_val} = {'·'.join(str(p) for p in sorted(prime_factors_set(max_gcd_val))) if max_gcd_val > 1 else '1'}, "
                      f"resistant_primes={sorted(remaining)}")


if __name__ == '__main__':
    main()
