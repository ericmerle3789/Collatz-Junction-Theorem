#!/usr/bin/env python3
"""
Q5 + ORDERING: Cunningham structure meets corrSum ordering
=============================================================

d(k) = 2^S - 3^k est un nombre de Cunningham.
corrSum = Σ 3^{k-1-i} · 2^{σ_i} est une somme de PRODUITS de puissances de 2 et 3.

La connexion : d encode la relation 2^S = 3^k (mod d), et corrSum
est une somme de termes 3^a · 2^b. Les MÊMES bases.

INSIGHT PROFOND : corrSum mod d = Σ 3^{k-1-i} · 2^{σ_i} mod (2^S - 3^k).

Utilisant 2^S ≡ 3^k mod d :
- 2^{σ_i} pour σ_i < S : pas de réduction (σ_i < S)
- Le lien : les puissances de 2 et 3 dans corrSum sont LIÉES
  par la même relation qui définit d.

Si on écrit chaque terme en base ρ = 2/3 :
3^{k-1-i} · 2^{σ_i} = 3^{k-1} · (2/3)^{σ_i} · 3^{σ_i - i}
                      = 3^{k-1} · ρ^{σ_i} · 3^{δ_i}
                      = 3^{k-1} · (3ρ)^{δ_i} · ρ^i   (car 3ρ = 2)
                      = 3^{k-1} · 2^{δ_i} · ρ^i

Donc corrSum = 3^{k-1} · Σ 2^{δ_i} · ρ^i = 3^{k-1} · F(ρ,δ).

F(ρ,δ) = Σ_{i=0}^{k-1} 2^{δ_i} · ρ^i est un POLYNÔME en ρ avec
coefficients 2^{δ_i} (puissances de 2).

La relation Cunningham : ρ^S = 2^S · 3^{-S} = 3^{k-S} mod d.
Donc ρ est une RACINE de X^S - 3^{k-S} dans Z/dZ.

Le polynôme minimal de ρ dans Z/dZ divise X^S - 3^{k-S}.

Si X^S - 3^{k-S} est IRRÉDUCTIBLE mod un premier p | d :
alors ρ a ordre S dans (Z/pZ)*, et F(ρ,δ) a des propriétés
spéciales liées à cette irréductibilité.

QUESTION CONCRÈTE : F(ρ,δ) = 0 ssi ρ est racine de F.
Mais F a coefficients 2^{δ_i} — des puissances de la BASE de ρ (via 3ρ=2).
Les coefficients et le point d'évaluation sont ALGÉBRIQUEMENT LIÉS.

C'est comme évaluer X + X² + X³ à X = x : la structure est auto-référentielle.
Pour F(ρ,δ) = Σ (3ρ)^{δ_i} · ρ^i = Σ ρ^{i+δ_i} · 3^{δ_i}

Avec σ_i = i + δ_i : F = Σ ρ^{σ_i} · 3^{δ_i}.

Pour F = 0 : Σ ρ^{σ_i} · 3^{δ_i} = 0 mod d.

Les exposants de ρ sont les positions σ_i (strictement croissantes).
Les coefficients sont 3^{δ_i} (puissances de 3, faiblement croissantes).

C'est une ÉVALUATION DIAGONALE : le coefficient du terme ρ^{σ_i}
dépend de la position σ_i via δ_i = σ_i - i.

Cette dépendance position↔coefficient est la SOURCE de l'obstruction.
"""

import sys, os
from math import ceil, log2, gcd
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)
from syracuse_jepa.engine.symbolic_objects import ModularInt


def analyze_diagonal_structure(k_max=10):
    """Analyze the diagonal structure F = Σ ρ^{σ_i} · 3^{δ_i}."""
    print("DIAGONAL STRUCTURE: F = Σ ρ^{σ_i} · 3^{δ_i}")
    print("=" * 65)
    print("Each term's coefficient 3^{δ_i} depends on its position σ_i via δ_i = σ_i - i.")
    print("This position↔coefficient coupling is the ordering obstruction.\n")

    for k in [3, 5, 7]:
        S = compute_S(k)
        d = compute_d(k)
        inv3 = pow(3, -1, d)
        rho = (2 * inv3) % d

        C = count_cumulative_sequences(k, S)
        if C > 5000: continue

        print(f"k={k}, S={S}, d={d}, ρ={rho}")

        # For each σ: decompose F into diagonal terms
        for sigma in list(enumerate_cumulative_sequences(k, S))[:3]:
            deltas = [sigma[i] - i for i in range(k)]
            terms = []
            for i in range(k):
                rho_power = pow(rho, sigma[i], d)
                three_power = pow(3, deltas[i], d)
                term = (rho_power * three_power) % d
                terms.append(term)

            F_val = sum(terms) % d
            # Verify: this should equal corrSum / 3^{k-1} mod d
            cs = corrsum_cumulative(sigma, k)
            inv_3km1 = pow(pow(3, k-1), -1, d)
            expected = (cs * inv_3km1) % d

            match = (F_val == expected)
            print(f"  σ={sigma}, δ={deltas}")
            print(f"    F = {' + '.join(str(t) for t in terms)} ≡ {F_val} (expected {expected}) {'✓' if match else '✗'}")

        # KEY: What happens with the UNORDERED version?
        # Unordered: same multiset of (σ_i, δ_i) but δ NOT increasing
        # The diagonal coupling is BROKEN
        print(f"\n  DIAGONAL vs ANTI-DIAGONAL:")
        print(f"  Ordered: σ increasing → δ increasing → 3^δ increasing → coeff GROWS with position")
        print(f"  Reversed: large δ at small σ → 3^δ LARGE at EARLY positions")
        print(f"  The ordering forces: late positions get LARGE 3-coefficients")
        print(f"  But late positions have LARGE ρ-exponents (ρ^σ for large σ)")
        print(f"  Since |ρ| < 1 in R: large ρ-exponent means SMALL real contribution")
        print(f"  So ordered: large coeff × small base = moderate term")
        print(f"  Reversed: large coeff × large base = DOMINANT term")
        print(f"  The BALANCE is different → different sum mod d\n")


def explore_self_referential_polynomials(k_max=8):
    """
    F(ρ,δ) = Σ (3ρ)^{δ_i} · ρ^i with 3ρ = 2.
    So F = Σ 2^{δ_i} · ρ^i.

    This is a polynomial in ρ with POWER-OF-2 coefficients.
    The "self-referential" aspect: 2 = 3ρ, so the coefficients
    are POWERS of a linear function of the variable.

    If we substitute X = ρ:
    F(X) = Σ (3X)^{δ_i} · X^i = Σ 3^{δ_i} · X^{i+δ_i} = Σ 3^{δ_i} · X^{σ_i}

    F = 0 is: Σ 3^{δ_i} · X^{σ_i} = 0 at X = ρ = 2/3 mod d.

    This polynomial has k NON-CONSECUTIVE terms (at positions σ_0,...,σ_{k-1}).
    It's a LACUNARY polynomial.

    Descartes' rule for lacunary polynomials over finite fields:
    a polynomial with m terms has at most m-1 roots... wait, not over F_p.
    Over F_p: a polynomial of degree n has at most n roots.
    But with only k terms: can it have FEWER roots?

    YES: a k-term polynomial can have at most q·(k-1) roots in F_q
    by Strassmann's theorem (p-adic) or by Stepanov's method.

    For our F with k terms and d prime: at most k-1 roots.
    Since k << d for k ≥ 18: most elements are NOT roots.
    Probability ρ is a root: ≤ (k-1)/d → 0.
    """
    print("SELF-REFERENTIAL LACUNARY POLYNOMIALS")
    print("=" * 65)
    print("F = Σ 3^{δ_i} · X^{σ_i} evaluated at X = 2/3 mod d")
    print("This has k terms (lacunary). At most k-1 roots over F_p.\n")

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue

        # Is d prime?
        is_prime = all(d % p != 0 for p in range(2, min(10000, int(d**0.5)+2)))

        if is_prime:
            max_roots = k - 1
            ratio = max_roots / d
            print(f"k={k}: d={d} PRIME. F has k={k} terms → ≤ {max_roots} roots.")
            print(f"  Probability ρ is root: ≤ {ratio:.6f}")
            print(f"  This is {'VERY small' if ratio < 0.01 else 'small' if ratio < 0.1 else 'moderate'}")
        else:
            # For composite d: use CRT. F = 0 mod d iff F = 0 mod p for ALL p|d.
            factors = {}
            n = d
            for p in range(2, min(100000, n)):
                while n % p == 0:
                    factors[p] = factors.get(p, 0) + 1
                    n //= p
            if n > 1:
                factors[n] = 1

            print(f"k={k}: d={d} composite = {' · '.join(f'{p}^{e}' for p,e in factors.items())}")
            for p in sorted(factors.keys()):
                max_roots_p = k - 1
                ratio_p = max_roots_p / p
                print(f"  mod p={p}: ≤ {max_roots_p} roots, prob ≤ {ratio_p:.4f}")

    print(f"\nKEY: For k ≥ 68 and d prime: prob ≤ 67/{d} which is ASTRONOMICALLY small.")
    print("But 'probability ≠ proof'. The algebraic dependence ρ = 2/3 and 2^S ≡ 3^k")
    print("creates correlations that defeat probabilistic arguments.")
    print()
    print("HOWEVER: the LACUNARITY gives a structural handle.")
    print("A lacunary polynomial with k terms and large gaps between exponents")
    print("has RIGID root structure over finite fields.")
    print("If we can characterize the roots of F mod p for primes p | d:")
    print("and show ρ = 2/3 is never among them:")
    print("that would be the proof.")


if __name__ == '__main__':
    analyze_diagonal_structure()
    explore_self_referential_polynomials()
