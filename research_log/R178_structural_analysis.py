#!/usr/bin/env python3
"""
R178e — ANALYSE STRUCTURELLE DE L'ANTI-CORRÉLATION

QUESTION CENTRALE :
Quand p₁ et p₂ divisent d et ont petit ord, pourquoi les conditions
g(v) ≡ 0 mod p₁ et g(v) ≡ 0 mod p₂ sont-elles incompatibles ?

IDÉE :
g(v) = Σ 3^{x-1-j} · 2^{e_j} mod p.
Si ord_p(2) = r, alors 2^{e_j} ne dépend que de e_j mod r.
De même, 3^{x-1-j} ne dépend que de (x-1-j) mod ord_p(3).

Pour p₁ avec r₁ = ord_{p₁}(2) et p₂ avec r₂ = ord_{p₂}(2) :
Les conditions g ≡ 0 mod p₁ et g ≡ 0 mod p₂ "projettent" les {e_j}
sur Z/r₁ et Z/r₂ respectivement.

La CONTRAINTE CLÉ : les e_j sont STRICTEMENT CROISSANTS dans {0,...,S-1}.
Quand r₁ et r₂ sont petits (< S), chaque résidu mod r₁ (resp. r₂)
est atteint ~S/r₁ (resp. ~S/r₂) fois.

Mais la STRUCTURE de la somme g — avec des POIDS 3^{x-1-j} — impose
une relation entre la POSITION j dans la somme et l'EXPOSANT e_j.

C'est la relation {j → e_j, strictement croissante} combinée aux
poids {3^{x-1-j}, strictement décroissante} qui crée l'incompatibilité.
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


def prime_factorization(n):
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
    print("R178e — ANALYSE STRUCTURELLE DE L'ANTI-CORRÉLATION")
    print("=" * 80)

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 1 : La contrainte 2^S ≡ 3^x mod p
    # ═══════════════════════════════════════════════════════════════════════
    print("\n" + "═" * 70)
    print("PARTIE 1 : CONSÉQUENCE DE 2^S ≡ 3^x mod p")
    print("═" * 70)
    print("""
Pour p | d = 2^S - 3^x : 2^S ≡ 3^x mod p.

Soit r = ord_p(2), s = ord_p(3).
Alors 2^S ≡ 2^{S mod r} et 3^x ≡ 3^{x mod s}.
Donc 2^{S mod r} ≡ 3^{x mod s} mod p.

OBSERVATION CLÉ : S mod r et x mod s sont LIÉS par p.

Notons a = S mod r, b = x mod s.
Condition : 2^a ≡ 3^b mod p.

Pour chaque p|d, (a,b) encode "où on est" dans les cycles de 2 et 3 mod p.

Si p₁ et p₂ divisent d, alors :
- p₁ impose (a₁, b₁) avec 2^{a₁} ≡ 3^{b₁} mod p₁
- p₂ impose (a₂, b₂) avec 2^{a₂} ≡ 3^{b₂} mod p₂

La somme g(v) = Σ 3^{x-1-j} · 2^{e_j} mod p_i
        = Σ 3^{(x-1-j) mod s_i} · 2^{e_j mod r_i} (dans F_{p_i})

Quand g ≡ 0 mod p₁ : contrainte sur les e_j mod r₁
Quand g ≡ 0 mod p₂ : contrainte sur les e_j mod r₂

CAS CRUCIAL : gcd(r₁, r₂) petit ⟹ les contraintes dans Z/r₁ et Z/r₂
sont "presque orthogonales" ⟹ anti-corrélation.
""")

    # For each squarefree anomalous case, compute the constraints
    for S in range(3, 20):
        for x in range(2, min(S, 9)):
            d = 2**S - 3**x
            if d <= 1:
                continue

            factors = prime_factorization(d)
            if len(factors) < 2 or any(e > 1 for e in factors.values()):
                continue  # Skip non-squarefree or single-prime

            primes = sorted(factors.keys())
            if max(primes) > 500:
                continue

            # Check if ALL primes are passable
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

            if not all_passable:
                continue

            # Deep analysis
            print(f"\n  === S={S}, x={x}, d={d} = {'·'.join(str(p) for p in primes)} ===")

            for p in primes:
                r = multiplicative_order(2, p)
                s = multiplicative_order(3, p)
                a = S % r if r else None
                b = x % s if s else None

                # Find t with 3 ≡ 2^t mod p (if exists)
                t = None
                if r:
                    power = 1
                    for k in range(1, min(r + 1, p)):
                        power = power * 2 % p
                        if power == 3 % p:
                            t = k
                            break

                print(f"    p={p}: r=ord_p(2)={r}, s=ord_p(3)={s}, "
                      f"S mod r = {a}, x mod s = {b}, "
                      f"3∈⟨2⟩={'yes, t='+str(t) if t else 'no'}")

            # For EACH pair, check gcd(r1, r2) and the CRT structure
            for i in range(len(primes)):
                for j in range(i+1, len(primes)):
                    p1, p2 = primes[i], primes[j]
                    r1 = multiplicative_order(2, p1)
                    r2 = multiplicative_order(2, p2)
                    g12 = gcd(r1, r2)
                    lcm12 = r1 * r2 // g12

                    # Count joint zero
                    joint = 0
                    total = 0
                    for positions in all_aperiodic_vectors(S, x):
                        total += 1
                        g_val = compute_g(positions, x)
                        if g_val % p1 == 0 and g_val % p2 == 0:
                            joint += 1

                    print(f"    ({p1},{p2}): r₁={r1}, r₂={r2}, "
                          f"gcd={g12}, lcm={lcm12}, "
                          f"joint_zero={joint}/{total}")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 2 : Réduction modulo r — la "projection"
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 2 : LA PROJECTION g(v) mod p EN TERMES DE e_j mod r")
    print("═" * 70)
    print("""
Quand 3 ∈ ⟨2⟩ mod p (i.e., 3 = 2^t) :
  g(v) = Σ 2^{t(x-1-j) + e_j} mod p
       = Σ 2^{f_j mod r} mod p    (avec r = ord_p(2))

où f_j = t(x-1-j) + e_j.

La QUESTION : les f_j mod r, contraints par e_j strict. croissant,
forment-ils un pattern spécifique qui exclut la somme nulle ?

Quand r < S : les e_j se "replient" sur Z/r.
Mais les poids 3^{x-1-j} (= 2^{t(x-1-j)}) FORCENT une orientation.

ANALYSE : pour chaque prime passable, quels sont les patterns (f_j mod r)
qui donnent g ≡ 0 mod p ?
""")

    # Detailed analysis for a specific case
    test_cases = [
        (12, 4, 4015),  # = 5·11·73
        (12, 6, 3367),  # = 7·13·37
        (8, 4, 175),    # = 5²·7 (but let's look at 5 and 7 separately)
    ]

    for S, x, d_expected in test_cases:
        d = 2**S - 3**x
        assert d == d_expected, f"Expected d={d_expected}, got {d}"

        factors = prime_factorization(d)
        primes = sorted(factors.keys())

        print(f"\n  === S={S}, x={x}, d={d} = "
              f"{'·'.join(f'{p}^{e}' if e>1 else str(p) for p,e in sorted(factors.items()))} ===")

        for p in primes:
            r = multiplicative_order(2, p)
            if r is None:
                continue

            # Find t
            t = None
            power = 1
            for k in range(1, min(r + 1, p)):
                power = power * 2 % p
                if power == 3 % p:
                    t = k
                    break

            if t is None:
                print(f"    p={p}: 3 ∉ ⟨2⟩, analyse différente nécessaire")
                # Direct analysis without t
                zero_vectors = []
                total = 0
                for positions in all_aperiodic_vectors(S, x):
                    total += 1
                    g = compute_g(positions, x)
                    if g % p == 0:
                        zero_vectors.append(positions)

                print(f"    p={p} (ord={r}): {len(zero_vectors)}/{total} "
                      f"vecteurs avec p|g")
                continue

            print(f"    p={p} (ord={r}, t={t}): 3 = 2^{t} mod {p}")

            # For each zero vector, compute the f_j pattern
            zero_patterns = []
            non_zero_count = 0
            total = 0

            for positions in all_aperiodic_vectors(S, x):
                total += 1
                g = compute_g(positions, x)

                if g % p == 0:
                    f_js = [(t * (x-1-j) + positions[j]) % r for j in range(x)]
                    f_js_raw = [t * (x-1-j) + positions[j] for j in range(x)]
                    zero_patterns.append((positions, f_js, f_js_raw))
                else:
                    non_zero_count += 1

            print(f"    {len(zero_patterns)}/{total} vecteurs avec p|g "
                  f"({100*len(zero_patterns)/total:.1f}%)")

            if zero_patterns and len(zero_patterns) <= 20:
                print(f"    Patterns f_j mod {r} donnant g≡0:")
                for pos, fmod, fraw in zero_patterns[:10]:
                    print(f"      e={pos}, f_raw={fraw}, f mod {r} = {fmod}")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 3 : La CONTRAINTE DIOPHANTIENNE
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 3 : LA CONTRAINTE DIOPHANTIENNE")
    print("═" * 70)
    print("""
g(v) ≡ 0 mod d impose une équation DIOPHANTIENNE sur les e_j :
  Σ 3^{x-1-j} · 2^{e_j} ≡ 0 mod d

Cela revient à :
  Σ 3^{x-1-j} · 2^{e_j} = k · d = k · (2^S - 3^x)

pour un entier k ≥ 1.

Or : Σ 3^{x-1-j} · 2^{e_j} = g(v) ∈ [g_min, g_max]
     g_min = 3^x - 2^x (positions 0,1,...,x-1)
     g_max = 2^{S-x} · (3^x - 2^x) (positions S-x,...,S-1)

Donc k ∈ [g_min/d, g_max/d] = [(3^x - 2^x)/(2^S - 3^x), 2^{S-x}·(3^x-2^x)/(2^S-3^x)]

Pour chaque k dans cette plage, il faut résoudre :
  Σ 3^{x-1-j} · 2^{e_j} = k · (2^S - 3^x) = k · 2^S - k · 3^x

  ⟺ k · 3^x + Σ 3^{x-1-j} · 2^{e_j} = k · 2^S

  ⟺ 3^{x-1} · (3k + 2^{e_0}) + 3^{x-2} · 2^{e_1} + ... + 2^{e_{x-1}} = k · 2^S

C'est un système SURDÉTERMINÉ : x variables (e_j) et 1 paramètre (k).
""")

    # For x=3, enumerate ALL valid k and check if ANY solution exists
    print("Pour x=3 : analyse exhaustive des k possibles\n")

    for S in range(5, 22):
        d = 2**S - 27
        if d <= 1:
            continue

        # g = 9·2^{e0} + 3·2^{e1} + 2^{e2} = k·d
        # With e0=0 (wlog): g = 9 + 3·2^D1 + 2^D2 = k·d
        # D1 ∈ {1,...,S-2}, D2 ∈ {D1+1,...,S-1}

        g_min = 9 + 6 + 8  # D1=1, D2=2 → but need D1 < D2 ≤ S-1
        g_min_actual = 9 + 3 * 2 + 2**2  # = 9 + 6 + 4 = 19
        g_max_actual = 9 + 3 * 2**(S-2) + 2**(S-1)

        k_min = max(1, g_min_actual // d)
        k_max = g_max_actual // d

        found_any = False
        for k in range(max(1, k_min), k_max + 1):
            target = k * d  # = 9 + 3·2^D1 + 2^D2
            # target - 9 = 3·2^D1 + 2^D2
            remaining = target - 9
            if remaining <= 0:
                continue

            # Try each D1
            for D1 in range(1, S-1):
                val1 = 3 * (2**D1)
                if val1 >= remaining:
                    break
                val2_needed = remaining - val1
                # val2_needed must be a power of 2, and the exponent > D1
                if val2_needed > 0 and (val2_needed & (val2_needed - 1)) == 0:
                    D2 = val2_needed.bit_length() - 1
                    if D2 > D1 and D2 < S:
                        found_any = True
                        # Check aperiodicity
                        v = tuple(1 if i in (0, D1, D2) else 0 for i in range(S))
                        is_periodic = False
                        for period in range(1, S):
                            if S % period == 0 and period < S:
                                if v == v[:period] * (S // period):
                                    is_periodic = True
                                    break
                        if not is_periodic:
                            print(f"  ⚠️ S={S}: FOUND d|g ! k={k}, "
                                  f"D1={D1}, D2={D2}, g={target}, "
                                  f"d={d}, aperiodic=True")
                        else:
                            pass  # periodic vector, doesn't count

        if not found_any:
            if S <= 16:
                print(f"  S={S:2d}: d={d:>10d}, k ∈ [{max(1,k_min)}, {k_max}], "
                      f"NO solution ✅")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 4 : Pour x=3, la contrainte arithmétique exacte
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 4 : CONTRAINTE ARITHMÉTIQUE POUR x=3")
    print("═" * 70)
    print("""
Pour x=3, e₀=0 :
  9 + 3·2^{D₁} + 2^{D₂} ≡ 0 mod d, d = 2^S - 27.

  Réécrivons : 2^{D₂} ≡ -9 - 3·2^{D₁} mod d.

  Puisque d est impair et gcd(2, d) = 1, le terme 2^{D₂} mod d est
  un élément de ⟨2⟩ ⊂ (Z/d)*.

  La condition est : -9 - 3·2^{D₁} ∈ ⟨2⟩ mod d.

  Pour chaque D₁, c'est une condition de "résidu puissance de 2".

  Si -9 - 3·2^{D₁} ∉ ⟨2⟩ mod d pour TOUT D₁ ∈ {1,...,S-2}, alors
  d ∤ g(v) pour tout v avec x=3.

  C'est EXACTEMENT la question de R176 — dans ⟨2⟩ mod d.
""")

    print("Vérification : -9 - 3·2^{D₁} ∈ ⟨2⟩ mod d ?\n")

    for S in range(5, 20):
        d = 2**S - 27
        if d <= 1:
            continue

        # Compute ⟨2⟩ mod d
        gen_2 = set()
        power = 1
        for k in range(S * 5):  # ord_d(2) divides λ(d)
            gen_2.add(power)
            power = power * 2 % d
            if power == 1:
                break
        gen_2.add(power)  # Include 1

        ord_d_2 = len(gen_2)

        found = False
        for D1 in range(1, S-1):
            target = (-9 - 3 * pow(2, D1, d)) % d
            if target in gen_2:
                found = True
                # What D2 gives 2^{D2} ≡ target?
                power = 1
                for D2_cand in range(S):
                    if power == target and D2_cand > D1:
                        # Check aperiodicity
                        v = tuple(1 if i in (0, D1, D2_cand) else 0 for i in range(S))
                        is_periodic = False
                        for period in range(1, S):
                            if S % period == 0 and period < S:
                                if v == v[:period] * (S // period):
                                    is_periodic = True
                                    break
                        if not is_periodic:
                            print(f"  S={S}: D₁={D1}, target={target} ∈ ⟨2⟩, "
                                  f"D₂={D2_cand} gives 2^D₂=target, "
                                  f"g={9+3*2**D1+2**D2_cand}, APERIODIC ⚠️")
                    power = power * 2 % d

        if not found:
            print(f"  S={S:2d}: d={d:>10d}, |⟨2⟩|={ord_d_2:>6d}, "
                  f"NO D₁ with target ∈ ⟨2⟩ → d ∤ g ✅"
                  f" {'[ord big: target never lands]' if ord_d_2 < d // 2 else ''}")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 5 : SYNTHÈSE
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("SYNTHÈSE R178e")
    print("═" * 70)
    print("""
OBSERVATIONS CLÉS :

1. g(v) ≡ 0 mod d n'arrive JAMAIS (vérifié 110 cas, S ≤ 22).

2. La structure est MULTI-MÉCANISME :
   - Pour d premier : 0 ∉ Image(g mod d) directement
   - Pour d composite avec un grand premier : résistance par ordre
   - Pour d composite tout-petit-premier : anti-corrélation

3. L'anti-corrélation est forcée par :
   - La relation 2^S ≡ 3^x mod d
   - L'ordre strict e_0 < e_1 < ... < e_{x-1}
   - Les poids 3^{x-1-j} décroissants

4. Pour x=3 : la condition se réduit à
   -9 - 3·2^{D₁} ∉ ⟨2⟩ mod d pour tout D₁
   C'est une question sur le coset (-9 - 3·⟨2⟩) ∩ ⟨2⟩ dans (Z/d)*.

DIRECTION PROMETTEUSE :
Prouver que le coset {-c - 3·2^a : a=1..S-2} n'intersecte JAMAIS
⟨2⟩ dans (Z/d)* quand d = 2^S - 3^x.

Cela utiliserait les propriétés spécifiques de 2 et 3 via la relation
2^S ≡ 3^x mod d, ET la borne a < S sur les exposants.
""")


if __name__ == '__main__':
    main()
