#!/usr/bin/env python3
"""
R176 — LE CAS d PREMIER : POURQUOI g(v) ≢ 0 mod p ?

Pour p = 2^S - 3^x premier, on a dans F_p :
  2^S = 3^x    (car p | 2^S - 3^x)

Donc le sous-groupe ⟨2⟩ et le sous-groupe ⟨3⟩ dans F_p* sont RELIÉS.

g(v) = Σ_{j=0}^{x-1} 3^{x-1-j} · 2^{e_j} mod p

IDÉE CLÉ : Dans F_p, posons α = 2, β = 3. On a β^x = α^S.
Donc β = α^{S/x}... seulement si S/x est entier, ce qui n'est pas le cas en général
car x·log₂3 < S ≤ 2x et log₂3 est irrationnel.

MAIS dans F_p* (groupe cyclique d'ordre p-1), on peut écrire :
  β = α^t   pour un unique t ∈ {1,...,p-1}
  car α = 2 est un générateur de ⟨2⟩ ⊂ F_p*.

Condition : β^x = α^S dans F_p*, donc α^{tx} = α^S, i.e., tx ≡ S mod ord_p(2).

EXPLORATION :
1. Pour chaque p = 2^S - 3^x premier, calculer ord_p(2), ord_p(3), et t.
2. Réécrire g(v) en termes de puissances de α seules :
   g(v) = Σ α^{t(x-1-j) + e_j}
3. Analyser cette somme dans le groupe cyclique ⟨α⟩.
"""

from itertools import combinations
from math import gcd
from sympy import isprime, factorint, primitive_root, discrete_log, Mod
import sys


def compute_g_mod(positions, x, p):
    """g(v) mod p."""
    result = 0
    for j in range(x):
        result = (result + pow(3, x-1-j, p) * pow(2, positions[j], p)) % p
    return result


def multiplicative_order(a, n):
    """Compute ord_n(a), the multiplicative order of a mod n."""
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
    print("R176 — LE CAS d PREMIER : STRUCTURE DANS F_p")
    print("=" * 72)

    # ═══════════════════════════════════════════════════════════════
    # TEST 1 : Structure de F_p pour p = 2^S - 3^x premier
    # ═══════════════════════════════════════════════════════════════
    print("\n" + "=" * 60)
    print("TEST 1 : ORDRES DE 2 ET 3 DANS F_p*")
    print("=" * 60)

    prime_cases = []
    for S in range(3, 25):
        for x in range(2, S):
            d = 2**S - 3**x
            if d <= 1:
                continue
            if isprime(d):
                prime_cases.append((S, x, d))

    for S, x, p in prime_cases:
        o2 = multiplicative_order(2, p)
        o3 = multiplicative_order(3, p)

        # 2^S ≡ 3^x mod p, so o2 | S·k for appropriate k, etc.
        # More precisely: 2^S = 3^x in F_p, so ord(2) | any m with 2^m ≡ 1
        # and S must satisfy 2^S ≡ 3^x (not necessarily 1)

        # Compute t such that 3 ≡ 2^t mod p
        if o2 and (p-1) % o2 == 0:
            # 2 generates a subgroup of order o2
            # 3 is in this subgroup iff o3 | o2
            three_in_gen2 = (o3 is not None and o2 is not None and o2 % o3 == 0)
        else:
            three_in_gen2 = False

        # If 3 ∈ ⟨2⟩, find t with 3 = 2^t mod p
        t = None
        if three_in_gen2:
            # Brute force for small p
            if p < 200000:
                power = 1
                for k in range(1, o2 + 1):
                    power = power * 2 % p
                    if power == 3 % p:
                        t = k
                        break

        print(f"  S={S:2d}, x={x}: p={p:>8d}, ord_p(2)={o2}, ord_p(3)={o3}, "
              f"3∈⟨2⟩={three_in_gen2}"
              f"{f', t={t} (3=2^t)' if t is not None else ''}")

        # If 3 ∈ ⟨2⟩, then g(v) = Σ 2^{t(x-1-j)+e_j} = sum of powers of 2
        if t is not None:
            print(f"    → g(v) = Σ 2^{{t(x-1-j)+e_j}} mod p = sum of {x} powers of 2 in F_p*")
            # The exponents are: t(x-1-j) + e_j for j=0,...,x-1
            # With e_0 < e_1 < ... < e_{x-1}
            # The question becomes: can x distinct elements of ⟨2⟩ sum to 0 in F_p?

    # ═══════════════════════════════════════════════════════════════
    # TEST 2 : Quand 3 ∈ ⟨2⟩, les exposants
    # ═══════════════════════════════════════════════════════════════
    print("\n\n" + "=" * 60)
    print("TEST 2 : STRUCTURE DES EXPOSANTS QUAND 3 ∈ ⟨2⟩")
    print("=" * 60)

    for S, x, p in prime_cases[:15]:
        o2 = multiplicative_order(2, p)
        if o2 is None:
            continue

        # Find t
        t = None
        power = 1
        for k in range(1, min(o2 + 1, p)):
            power = power * 2 % p
            if power == 3 % p:
                t = k
                break

        if t is None:
            continue

        print(f"\n  S={S}, x={x}, p={p}, o2={o2}, t={t}")
        print(f"  3 = 2^{t} mod {p}")
        print(f"  Verification: 2^{t} mod {p} = {pow(2, t, p)}")
        print(f"  2^S mod p = {pow(2, S, p)}, 3^x mod p = {pow(3, x, p)}")

        # For each vector, compute the exponent set
        # g(v) = Σ 2^{t(x-1-j) + e_j} mod p
        # Exponent of 2 for term j: f_j = t(x-1-j) + e_j (mod o2)
        # g(v) = 0 mod p iff Σ 2^{f_j} = 0 in F_p

        # The map j → f_j = t(x-1-j) + e_j is:
        # - Decreasing in the t-component: t(x-1), t(x-2), ..., t, 0
        # - Increasing in the e-component: e_0, e_1, ..., e_{x-1}
        # THIS IS THE ANTI-CORRELATION expressed in exponent space!

        # The exponent f_j = -t·j + t(x-1) + e_j
        # = (decreasing linear in j) + (increasing in j)
        # = "competition" between -t·j and e_j

        # For "balanced" vectors (e_j ≈ j·S/x): f_j ≈ -t·j + (x-1)t + j·S/x
        # = t(x-1) + j(S/x - t)
        # If S/x > t: f_j is increasing → all exponents distinct → sum of x DISTINCT powers of 2
        # If S/x < t: f_j is decreasing → still distinct → sum of x distinct powers of 2
        # If S/x = t: f_j = t(x-1) constant → all terms equal → g = x · 2^{t(x-1)}

        ratio = S / x
        print(f"  S/x = {ratio:.3f}, t = {t}, S/x vs t: {'>' if ratio > t else '<' if ratio < t else '='}")

        # Check: compute actual exponents for first few vectors
        count = 0
        for positions in all_aperiodic_vectors(S, x):
            count += 1
            if count > 5:
                break

            exponents = [(t * (x-1-j) + positions[j]) % o2 for j in range(x)]
            g_val = sum(pow(2, t*(x-1-j) + positions[j], p) for j in range(x)) % p
            g_check = compute_g_mod(positions, x, p)

            # Are exponents distinct mod o2?
            exp_set = set(exponents)
            all_distinct = len(exp_set) == x

            print(f"    v={''.join('1' if i in positions else '0' for i in range(S))}: "
                  f"exponents(mod {o2})={exponents}, "
                  f"distinct={all_distinct}, "
                  f"g={g_val}, verify={g_check}")

    # ═══════════════════════════════════════════════════════════════
    # TEST 3 : La question réduite — somme de puissances distinctes
    # ═══════════════════════════════════════════════════════════════
    print("\n\n" + "=" * 60)
    print("TEST 3 : SOMME DE x PUISSANCES DISTINCTES DE 2 DANS F_p")
    print("=" * 60)
    print("""
Si 3 ∈ ⟨2⟩ dans F_p*, alors g(v) = 0 mod p se réduit à :
  Σ_{j=0}^{x-1} 2^{f_j} ≡ 0 mod p
  avec f_j = t(x-1-j) + e_j, et les f_j PAS nécessairement distincts mod o_p(2).

QUESTION : Parmi les x éléments 2^{f_0}, ..., 2^{f_{x-1}} de ⟨2⟩ ⊂ F_p*,
leur somme peut-elle être 0 ?

C'est un problème de SUBSET SUM dans un sous-groupe cyclique de F_p*.
""")

    # For each prime case, check if the exponents f_j are always distinct
    for S, x, p in prime_cases[:20]:
        o2 = multiplicative_order(2, p)
        if o2 is None:
            continue

        t = None
        power = 1
        for k in range(1, min(o2 + 1, p)):
            power = power * 2 % p
            if power == 3 % p:
                t = k
                break

        if t is None:
            continue

        # Count vectors where exponents are all distinct mod o2
        total = 0
        all_distinct_count = 0
        collision_count = 0

        for positions in all_aperiodic_vectors(S, x):
            total += 1
            exponents = [(t * (x-1-j) + positions[j]) % o2 for j in range(x)]
            if len(set(exponents)) == x:
                all_distinct_count += 1
            else:
                collision_count += 1

        pct = 100 * all_distinct_count / total if total > 0 else 0
        print(f"  S={S:2d}, x={x}: p={p:>8d}, o2={o2:>6d}, t={t:>4d}, "
              f"distinct_exp={all_distinct_count}/{total} ({pct:.0f}%)")

    # ═══════════════════════════════════════════════════════════════
    # TEST 4 : L'obstruction par la taille des exposants
    # ═══════════════════════════════════════════════════════════════
    print("\n\n" + "=" * 60)
    print("TEST 4 : TAILLE DES EXPOSANTS f_j = t(x-1-j) + e_j")
    print("=" * 60)
    print("""
Les exposants f_j vivent dans {0, ..., t(x-1) + S - 1}.
Leur SOMME est : Σ f_j = t·x(x-1)/2 + Σ e_j.
La RÉDUCTION mod o2 peut créer des collisions.

Mais AVANT réduction mod o2 : f_j est la "compétition" entre
le terme -t·j (décroissant) et e_j (croissant).

Si t < S/x (≈ log₂3 ≈ 1.585) : le terme e_j domine, f_j est CROISSANT.
Si t > S/x : le terme -t·j domine, f_j pourrait être DÉCROISSANT.
""")

    for S, x, p in prime_cases[:15]:
        o2 = multiplicative_order(2, p)
        if o2 is None:
            continue

        t = None
        power = 1
        for k in range(1, min(o2 + 1, p)):
            power = power * 2 % p
            if power == 3 % p:
                t = k
                break

        if t is None:
            continue

        # Theoretical analysis
        # Max f_j (before mod): t(x-1) + (S-1) ≈ t·x + S
        max_f = t * (x - 1) + (S - 1)
        # If max_f < o2, no reduction needed → exponents are "natural"
        needs_reduction = max_f >= o2

        # What fraction of S/x is t?
        ratio_t = t / (S / x)

        print(f"  S={S:2d}, x={x}: p={p:>8d}, o2={o2:>6d}, t={t:>4d}, "
              f"max_f={max_f:>6d}, mod_needed={needs_reduction}, "
              f"t/(S/x)={ratio_t:.3f}")


if __name__ == '__main__':
    main()
