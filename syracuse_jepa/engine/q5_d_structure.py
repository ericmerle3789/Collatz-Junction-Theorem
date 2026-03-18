#!/usr/bin/env python3
"""
Q5 DEEP DIVE — Structure arithmétique de d(k) = 2^S - 3^k
=============================================================

Pourquoi d(k) est-il SPÉCIAL ? Qu'est-ce qui le distingue d'un
nombre arbitraire de même taille ?

d(k) = 2^S - 3^k est un nombre de TYPE CUNNINGHAM (a^n - b^m).
Ces nombres ont une FACTORISATION ALGÉBRIQUE riche :
- Facteurs cyclotomiques
- Diviseurs primitifs (Zsygmondy)
- Connexion aux corps cyclotomiques
- Lien avec ABC

QUESTION CENTRALE : La structure de d(k) FORCE-T-ELLE N₀ = 0 ?

Autrement dit : y a-t-il une propriété de d(k) = 2^S - 3^k
qui empêche STRUCTURELLEMENT qu'un corrSum (somme pondérée de
puissances de 2 avec coefficients en puissances de 3) soit
divisible par d ?

C'est la question Q5 de la carte mentale — "probablement le
chemin le plus sous-exploré".
"""

import sys, os
from math import ceil, log2, comb, gcd, log
from collections import Counter, defaultdict

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


def analyze_d_arithmetic(k_max=30):
    """Analyze the deep arithmetic structure of d(k)."""
    print("Q5: STRUCTURE ARITHMÉTIQUE DE d(k) = 2^S - 3^k")
    print("=" * 65)

    data = []
    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = 2**S - 3**k
        if d <= 0: continue

        # Factorize d
        factors = {}
        n = d
        for p in range(2, min(100000, int(n**0.5) + 2)):
            while n % p == 0:
                factors[p] = factors.get(p, 0) + 1
                n //= p
        if n > 1:
            factors[n] = 1

        # Properties
        n_factors = len(factors)
        smallest_p = min(factors.keys()) if factors else d
        largest_p = max(factors.keys()) if factors else d
        is_prime = (n_factors == 1 and list(factors.values())[0] == 1)
        is_squarefree = all(e == 1 for e in factors.values())

        # Cunningham structure: gcd(S, k)
        g = gcd(S, k)
        a, b = S // g, k // g

        # Phi_d contributions (cyclotomic)
        # d = Π_{m|g} Φ_m(2^a, 3^b)

        # Radical of d: rad(d) = Π p (distinct primes)
        rad_d = 1
        for p in factors:
            rad_d *= p

        # ABC quality: q(d) = log(d) / log(rad(d))
        if rad_d > 1:
            abc_quality = log(d) / log(rad_d)
        else:
            abc_quality = 1.0

        # S-smooth? What's the largest prime factor?
        smoothness = largest_p

        entry = {
            'k': k, 'S': S, 'd': d, 'g': g,
            'n_factors': n_factors,
            'smallest_p': smallest_p,
            'largest_p': largest_p,
            'is_prime': is_prime,
            'is_squarefree': is_squarefree,
            'rad_d': rad_d,
            'abc_quality': abc_quality,
            'smoothness': smoothness,
            'factors': factors,
        }
        data.append(entry)

        if k <= 20 or is_prime:
            print(f"k={k:2d} S={S:2d} g={g}: d={d:>12d} "
                  f"{'PRIME' if is_prime else f'{n_factors} factors'} "
                  f"smallest_p={smallest_p} abc_q={abc_quality:.2f}")

    # PATTERN ANALYSIS
    print(f"\n{'='*65}")
    print("PATTERN ANALYSIS")
    print(f"{'='*65}")

    # 1. When is d prime?
    primes = [e for e in data if e['is_prime']]
    print(f"\nd(k) is prime for k = {[e['k'] for e in primes]}")
    print(f"  ({len(primes)}/{len(data)} values, {100*len(primes)/len(data):.0f}%)")

    # 2. Smallest prime factor distribution
    sp_dist = Counter(e['smallest_p'] for e in data)
    print(f"\nSmallest prime factor distribution:")
    for p, count in sorted(sp_dist.items())[:10]:
        ks = [e['k'] for e in data if e['smallest_p'] == p][:5]
        print(f"  p={p}: {count} times (k={ks})")

    # 3. ABC quality
    print(f"\nABC quality q = log(d)/log(rad(d)):")
    high_q = [e for e in data if e['abc_quality'] > 1.5]
    for e in high_q[:5]:
        print(f"  k={e['k']}: q={e['abc_quality']:.2f} (d={e['d']}, rad={e['rad_d']})")

    # 4. gcd(S,k) pattern
    g_dist = Counter(e['g'] for e in data)
    print(f"\ngcd(S,k) distribution:")
    for g, count in sorted(g_dist.items()):
        print(f"  g={g}: {count} times")

    # 5. KEY: relationship between smallest prime and N₀
    print(f"\n{'='*65}")
    print("KEY QUESTION: Does the smallest prime of d(k) predict anything?")
    print(f"{'='*65}")

    for e in data[:15]:
        k = e['k']
        C = count_cumulative_sequences(k, compute_S(k))
        ratio = C / e['d'] if e['d'] > 0 else 0
        print(f"  k={k:2d}: smallest_p={e['smallest_p']:>6d}, C/d={ratio:.4f}, "
              f"d={'prime' if e['is_prime'] else 'composite'}")

    return data


def explore_cunningham_connection(k_max=20):
    """Explore the Cunningham number structure."""
    print(f"\n{'='*65}")
    print("CUNNINGHAM NUMBERS: d(k) = 2^S - 3^k")
    print(f"{'='*65}")

    print("\nCunningham numbers a^n - b^n have special factorizations:")
    print("- Algebraic: if gcd(n_a, n_b) > 1, factors into cyclotomic parts")
    print("- Zsygmondy: for n > 6, primitive prime divisors exist")
    print("- Aurifeuillean: further factorization for specific forms")
    print()

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = 2**S - 3**k
        if d <= 0: continue
        g = gcd(S, k)

        if g > 1:
            a, b = S // g, k // g
            # d = (2^a)^g - (3^b)^g
            # Factor: Π_{m|g} Φ_m(2^a, 3^b)
            base_2 = 2**a
            base_3 = 3**b
            phi_1 = base_2 - base_3  # Φ_1 = x - y
            remaining = d // phi_1 if phi_1 != 0 and d % phi_1 == 0 else -1

            print(f"k={k:2d}: d = ({2}^{a})^{g} - ({3}^{b})^{g} = "
                  f"{base_2}^{g} - {base_3}^{g}")
            print(f"        Φ₁ = {base_2}-{base_3} = {phi_1}, "
                  f"remaining = {remaining}")

            # Are these factors the same as the prime factorization?
            if phi_1 > 0 and remaining > 0:
                print(f"        d = {phi_1} × {remaining}")


def explore_abc_connection(k_max=20):
    """
    ABC conjecture connection:
    For d = 2^S - 3^k: the equation 2^S = 3^k + d.
    ABC says: max(2^S, 3^k, d) < C · rad(2^S · 3^k · d)^{1+ε}

    Since rad(2^S · 3^k · d) = 2 · 3 · rad(d) = 6 · rad(d):
    d < C · (6 · rad(d))^{1+ε}

    This BOUNDS d in terms of rad(d). If ABC is true with small constants:
    d can't be too "powerful" (too many repeated prime factors).

    For our problem: if d is squarefree (all prime factors appear once),
    then rad(d) = d and the ABC bound is trivial.
    If d has repeated factors: ABC constrains how repeated they can be.
    """
    print(f"\n{'='*65}")
    print("ABC CONJECTURE CONNECTION")
    print(f"{'='*65}")
    print("Equation: 2^S = 3^k + d(k)")
    print("ABC: max(a,b,c) < C·rad(abc)^{1+ε}")
    print()

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = 2**S - 3**k
        if d <= 0: continue

        a, b, c = 3**k, d, 2**S
        # rad(a·b·c) = rad(3^k · d · 2^S) = 2 · 3 · rad(d)
        # Compute rad(d)
        factors = {}
        n = d
        for p in range(2, min(100000, int(n**0.5) + 2)):
            while n % p == 0:
                factors[p] = factors.get(p, 0) + 1
                n //= p
        if n > 1:
            factors[n] = 1

        rad_d = 1
        for p in factors:
            rad_d *= p

        rad_abc = 6 * rad_d
        quality = log(c) / log(rad_abc) if rad_abc > 1 else 0

        is_sqfree = all(e == 1 for e in factors.values())

        if k <= 15 or quality > 1.2:
            print(f"k={k:2d}: d={d:>10d}, rad(d)={rad_d:>10d}, "
                  f"q={quality:.3f}, sqfree={is_sqfree}")


if __name__ == '__main__':
    data = analyze_d_arithmetic()
    explore_cunningham_connection()
    explore_abc_connection()
