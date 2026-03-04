#!/usr/bin/env python3
"""
TEST DES PETITS k — Validation du framework sur k=1,2,3
=========================================================

k=1 : Le cycle trivial 1 -> 4 -> 2 -> 1 (DOIT exister, N_0 = 1)
  - Composition : (a_0) avec a_0 = 0 seulement (k=1 position)
  - S = ceil(log2(3)) = 2
  - d = 2^2 - 3^1 = 1
  - corrSum = 3^0 * 2^0 = 1 = 1*d = 1*1 => N_0(1) = 1 ✓

k=2 : Pas de cycle de longueur 2 (N_0 = 0)
  - S = ceil(2*log2(3)) = 4
  - d = 2^4 - 3^2 = 16 - 9 = 7
  - Compositions (a_0, a_1) avec 0 <= a_0 < a_1 <= 3
  - C = C(3,1) = 3 : (0,1), (0,2), (0,3)
  - corrSum = 3*2^{a_0} + 2^{a_1}
    (0,1): 3*1 + 2 = 5. 5 % 7 = 5 ≠ 0
    (0,2): 3*1 + 4 = 7. 7 % 7 = 0 ← MAIS attendons...

  CORRECTION : (0,2) donne corrSum = 7 = 1*d. Mais cela correspond a
  n_0 = corrSum/d = 7/7 = 1. Donc l'entier serait n_0 = 1, qui devrait
  verifier le cycle. Verifions : 1 -> 4 -> 2 -> 1 est de longueur k=1,
  pas k=2. Que se passe-t-il ?

  En fait, pour k=2 : n_0*d = corrSum, et n_0 DOIT etre impair et >= 1.
  Ici n_0 = 1 (impair ✓). Mais le cycle correspondant a n_0=1 avec k=2
  est 1 -> 4 -> 2 -> 1 -> 4 -> 2 -> 1, qui est le cycle trivial
  PARCOURU 2 FOIS. Ce n'est pas un nouveau cycle.

  Steiner exclut cela comment ? Par la condition que la composition
  doit etre PRIMITIVE (pas un multiple d'une composition plus courte).

k=3 : d = 2^5 - 3^3 = 32 - 27 = 5, N_0(5) = 0
  - C = C(4,2) = 6 compositions
  - Testons toutes
"""

import math
from collections import defaultdict


def compute_params(k):
    S = math.ceil(k * math.log2(3))
    d = (1 << S) - 3**k
    C = math.comb(S - 1, k - 1)
    return S, d, C


def enumerate_compositions(S, k):
    """Enumere toutes les compositions (a_0,...,a_{k-1}) avec 0 <= a_0 < a_1 < ... < a_{k-1} <= S-1."""
    from itertools import combinations
    return list(combinations(range(S), k))


def corrsum(composition, k):
    """Calcule corrSum = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{a_j}"""
    return sum(3**(k-1-j) * 2**a for j, a in enumerate(composition))


def test_k(k_val):
    S, d, C = compute_params(k_val)
    print(f"\n{'='*60}")
    print(f"k = {k_val}, S = {S}, d = {d}, C = {C}")
    print(f"{'='*60}")

    if d <= 0:
        print(f"  d <= 0 : pas de sens")
        return

    comps = enumerate_compositions(S, k_val)
    print(f"  Nombre de compositions : {len(comps)} (= C({S-1},{k_val-1}) = {C})")

    hits = []
    for comp in comps:
        cs = corrsum(comp, k_val)
        if cs % d == 0:
            n0 = cs // d
            hits.append((comp, cs, n0))

    print(f"  N_0({d}) = {len(hits)}")
    if hits:
        for comp, cs, n0 in hits:
            print(f"    Composition {comp}: corrSum = {cs} = {n0} * {d}")

    # Test Double Peeling
    if d > 0:
        print(f"\n  --- Double Peeling ---")
        inv3 = pow(3, -1, d) if d > 1 else 0

        # Forward depuis c_0 = 1
        fwd = [{(1, 0): 1}]
        for step in range(1, k_val):
            current = fwd[-1]
            nl = defaultdict(int)
            for (state, last_pos), count in current.items():
                for p in range(last_pos + 1, S):
                    ns = (3 * state + pow(2, p, d)) % d
                    nl[(ns, p)] += count
            fwd.append(dict(nl))

        # Backward depuis c_{k-1} = 0
        bwd = [{(0, S): 1}]
        for step in range(1, k_val):
            current = bwd[-1]
            nl = defaultdict(int)
            for (state, first_pos), count in current.items():
                for p in range(1, first_pos):
                    prev = ((state - pow(2, p, d)) * inv3) % d
                    nl[(prev, p)] += count
            bwd.append(dict(nl))

        # Test de compatibilite a chaque point de RDV
        for j in range(1, k_val - 1):  # j de 1 a k-2
            bwd_idx = k_val - 1 - j  # fwd j steps + bwd (k-1-j) steps = k-1 total
            if j >= len(fwd) or bwd_idx >= len(bwd):
                continue

            fwd_layer = fwd[j]
            bwd_layer = bwd[bwd_idx]

            compatible = 0
            for (fs, fp), fc in fwd_layer.items():
                for (bs, bp), bc in bwd_layer.items():
                    if fs == bs and fp < bp:
                        compatible += fc * bc

            print(f"    RDV j={j}: fwd_size={len(fwd_layer)}, "
                  f"bwd_size={len(bwd_layer)}, compatible={compatible}")


def test_k1_detailed():
    """Test detaille pour k=1 : le cycle trivial."""
    print(f"\n{'*'*60}")
    print(f"k=1 : LE CYCLE TRIVIAL 1 -> 4 -> 2 -> 1")
    print(f"{'*'*60}")

    k = 1
    S, d, C = compute_params(k)
    print(f"  S={S}, d={d}, C={C}")
    print(f"  Composition unique : (0)")
    print(f"  corrSum = 3^0 * 2^0 = 1")
    print(f"  corrSum mod d = 1 mod 1 = 0 ✓")
    print(f"  n_0 = corrSum/d = 1/1 = 1 (impair ✓)")

    # Verification du cycle
    n = 1
    print(f"\n  Cycle de Collatz depuis n={n} :")
    seq = [n]
    current = n
    for i in range(10):
        if current % 2 == 1:
            current = 3 * current + 1
        else:
            current = current // 2
        seq.append(current)
        if current == n and i > 0:
            break
    print(f"    {' -> '.join(map(str, seq))}")

    # Nombre d'etapes impaires dans un cycle complet
    current = 1
    odd_steps = 0
    even_steps = 0
    path = [1]
    while True:
        if current % 2 == 1:
            current = 3 * current + 1
            odd_steps += 1
        else:
            current = current // 2
            even_steps += 1
        path.append(current)
        if current == 1:
            break

    print(f"\n  Cycle complet : {' -> '.join(map(str, path))}")
    print(f"  Etapes impaires (k) = {odd_steps}")
    print(f"  Etapes paires (S) = {even_steps}")
    print(f"  => k={odd_steps}, S={even_steps} dans notre framework")

    # Pour k=1 (1 etape impaire) :
    # n -> 3n+1 -> (3n+1)/2^s = n (retour)
    # Donc 3n+1 = n * 2^s
    # n(3 - 2^s) = -1
    # Pour s=2 : n(3-4) = -1 => n = 1 ✓


def test_k2_detailed():
    """Test detaille pour k=2."""
    print(f"\n{'*'*60}")
    print(f"k=2 : PAS DE CYCLE DE LONGUEUR 2")
    print(f"{'*'*60}")

    k = 2
    S, d, C = compute_params(k)
    print(f"  S={S}, d={d}, C={C}")

    comps = enumerate_compositions(S, k)
    for comp in comps:
        cs = corrsum(comp, k)
        print(f"  Composition {comp}: corrSum = {cs}, mod {d} = {cs % d}")

    # (0,2) donne corrSum = 7 = d, n_0 = 1
    # MAIS n_0 = 1 avec k=2 signifie :
    # 1 fait 2 etapes impaires et 4 etapes paires pour revenir a 1
    # 1 -> 4 -> 2 -> 1 -> 4 -> 2 -> 1 (cycle trivial repete 2x)
    print(f"\n  La composition (0,2) donne n_0 = 1, mais c'est le cycle trivial")
    print(f"  parcouru 2 fois. Un vrai cycle de longueur k=2 necessiterait")
    print(f"  un n_0 DIFFERENT de tout entier ayant un cycle plus court.")
    print(f"  Steiner exige des compositions PRIMITIVES.")


if __name__ == "__main__":
    test_k1_detailed()
    test_k2_detailed()

    for k in [1, 2, 3, 4, 5, 6]:
        test_k(k)
