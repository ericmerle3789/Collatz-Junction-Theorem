#!/usr/bin/env python3
"""
R172 — LA FORMULE DU PRODUIT : OBSTRUCTION ARCHIMÉDIENNE
==========================================================

Pour un k-cycle (k = total steps, x = odd steps) :
  ∏_{i=1}^{x} (3 + 1/m_i) = 2^k

où m_i ≥ 1 sont les valeurs impaires du cycle (entiers positifs).
Pour un cycle NON-TRIVIAL (apériodique), les m_i doivent être DISTINCTS.

Bornes : 3^x < 2^k ≤ 4^x, soit x·log₂3 < k ≤ 2x.

QUESTION : Pour quels (x, k) cette équation a-t-elle des solutions
avec des m_i entiers positifs distincts ?

Si aucun (x, k) avec x ≥ 2 n'a de solution → preuve que pas de cycle !
"""

from fractions import Fraction
from itertools import combinations
import math


def find_product_solutions(x, k, max_m=10000):
    """
    Cherche toutes les solutions de ∏(3 + 1/m_i) = 2^k
    avec x facteurs, m_i entiers positifs distincts.

    Méthode : backtracking avec élagage.
    """
    target = Fraction(2**k)
    solutions = []

    def backtrack(remaining_x, current_product, min_m, chosen):
        if remaining_x == 0:
            if current_product == target:
                solutions.append(tuple(chosen))
            return

        # Élagage : produit restant doit être dans [3^remaining_x, 4^remaining_x]
        remaining_product = target / current_product
        if remaining_product <= 3**remaining_x:
            return  # Produit actuel trop grand
        if remaining_product > Fraction(4**remaining_x):
            return  # Produit actuel trop petit

        # Le prochain facteur (3 + 1/m) doit satisfaire :
        # remaining_product / (4^{remaining_x - 1}) ≤ 3 + 1/m ≤ remaining_product / 3^{remaining_x - 1}
        lower_factor = remaining_product / Fraction(4**(remaining_x - 1))
        upper_factor = remaining_product / Fraction(3**(remaining_x - 1))

        # 3 + 1/m = factor → m = 1/(factor - 3)
        # factor ∈ (3, 4] → m ∈ [1, ∞)

        if upper_factor <= 3:
            return  # Pas de m valide

        # m_max : from lower_factor ≤ 3 + 1/m → 1/m ≥ lower_factor - 3
        if lower_factor > 3:
            m_max = int(1 / (lower_factor - 3))
        else:
            m_max = max_m

        # m_min : from 3 + 1/m ≤ upper_factor → 1/m ≤ upper_factor - 3 → m ≥ 1/(upper_factor - 3)
        if upper_factor - 3 > 0:
            m_min_raw = Fraction(1) / (upper_factor - 3)
            m_min = max(min_m, int(m_min_raw) if m_min_raw == int(m_min_raw) else int(m_min_raw) + 1)
        else:
            m_min = min_m

        m_max = min(m_max, max_m)

        for m in range(m_min, m_max + 1):
            factor = Fraction(3 * m + 1, m)
            new_product = current_product * factor
            if new_product > target:
                break  # m increasing → factor decreasing → product decreasing... wait
                # Actually factor = 3 + 1/m DECREASES as m increases
                # So new_product DECREASES as m increases
                # So if new_product > target at this m, we need larger m
                continue
            if remaining_x == 1 and new_product != target:
                continue
            backtrack(remaining_x - 1, new_product, m + 1, chosen + [m])

    backtrack(x, Fraction(1), 1, [])
    return solutions


def main():
    print("=" * 72)
    print("R172 — LA FORMULE DU PRODUIT : OBSTRUCTION ARCHIMÉDIENNE")
    print("=" * 72)

    print("""
FORMULE : ∏_{i=1}^{x} (3 + 1/m_i) = 2^k
Conditions : m_i ∈ Z⁺, m_i distincts deux à deux.
""")

    # Pour chaque (x, k) admissible, chercher des solutions
    max_x = 15  # Nombre max d'odd steps à tester

    for x in range(1, max_x + 1):
        k_min = math.ceil(x * math.log2(3)) + 1  # k > x·log₂3
        # Actually k_min: need 3^x < 2^k, so k > x·log₂3
        while 2**k_min <= 3**x:
            k_min += 1
        k_max = 2 * x  # k ≤ 2x

        print(f"\n{'='*50}")
        print(f"x = {x} : k ∈ [{k_min}, {k_max}]")
        print(f"{'='*50}")

        if k_min > k_max:
            print(f"  Aucun k admissible !")
            continue

        for k in range(k_min, k_max + 1):
            target = 2**k
            d = target - 3**x
            print(f"\n  k={k}: 2^k={target}, d={d}")

            # Chercher des solutions
            max_m = min(10000, max(100, x * 3**(x-1) // max(1, d) * 3))
            solutions = find_product_solutions(x, k, max_m=max_m)

            if solutions:
                for sol in solutions[:5]:
                    # Vérification
                    prod = Fraction(1)
                    for m in sol:
                        prod *= Fraction(3*m + 1, m)
                    assert prod == Fraction(2**k)

                    # Vérifier si c'est un cycle trivial (tous m_i = 1, ou periodique)
                    is_trivial = all(m == 1 for m in sol)
                    distinct = len(set(sol)) == len(sol)

                    print(f"    ✅ SOLUTION : m = {sol}, "
                          f"{'TRIVIAL' if is_trivial else 'NON-TRIVIAL'}, "
                          f"{'distinct' if distinct else 'NON-DISTINCT'}")

                if len(solutions) > 5:
                    print(f"    ... et {len(solutions)-5} autres solutions")
            else:
                print(f"    ❌ Aucune solution (max_m={max_m})")

    # ═══════════════════════════════════════════════════════════════
    # ANALYSE THÉORIQUE
    # ═══════════════════════════════════════════════════════════════
    print("\n\n" + "=" * 72)
    print("ANALYSE THÉORIQUE")
    print("=" * 72)

    print("""
Observations :

1. Pour x=1 : (3+1/m) = 2^k.
   k=2: 3+1/m = 4 → m=1. C'est le cycle trivial {1}.

2. Pour x=2 : (3+1/m₁)(3+1/m₂) = 2^k.
   k=4: produit max = 4²=16 = 2^4. Solution: m₁=m₂=1 (non-distinct).
   k=3: 3² = 9 > 8 = 2³. IMPOSSIBLE (produit min > cible).

3. Pour x≥2, k=2x: produit = 4^x ne se réalise que si tous m_i=1 (non-distinct).
   Pour un cycle NON-TRIVIAL (m_i distincts), k < 2x.

4. La question clé : existe-t-il (x, k) avec x≥2 et k<2x tel que
   ∏(3+1/m_i) = 2^k avec m_i distincts ?

THÉORÈME VISÉ : Pour tout x ≥ 2 et tout k ∈ (x·log₂3, 2x) :
  L'équation ∏_{i=1}^{x}(3 + 1/m_i) = 2^k n'a PAS de solution
  avec m_1 < m_2 < ... < m_x entiers positifs.
""")

    # Test supplémentaire : pour x grand, vérifier que la contrainte est très serrée
    print("\nBORNES SUR m_1 (le plus petit m) :")
    for x in range(2, 12):
        k_min = math.ceil(x * math.log2(3)) + 1
        while 2**k_min <= 3**x:
            k_min += 1

        for k in range(k_min, min(k_min + 3, 2*x)):
            # Si m_1 = 1 : 4 · ∏_{i=2}^x (3+1/m_i) = 2^k
            # ∏_{i=2}^x (3+1/m_i) = 2^k / 4 = 2^{k-2}
            # Pour cela : 3^{x-1} < 2^{k-2} ≤ 4^{x-1}
            # i.e. (x-1)·log₂3 < k-2 ≤ 2(x-1)
            # i.e. k > (x-1)·log₂3 + 2 and k ≤ 2x

            sub_target = Fraction(2**k, 4)  # = 2^{k-2}
            # Need sub_target in (3^{x-1}, 4^{x-1}]
            lb = 3**(x-1)
            ub = 4**(x-1)

            feasible_m1_1 = lb < sub_target <= ub

            # Si m_1 = 2 : (7/2) · ∏ = 2^k → ∏ = 2^{k+1}/7
            sub_target_2 = Fraction(2**(k+1), 7)
            feasible_m1_2 = Fraction(lb) < sub_target_2 <= Fraction(ub)

            print(f"  x={x}, k={k}: d={2**k-3**x}, "
                  f"m₁=1 feasible: {feasible_m1_1}, "
                  f"m₁=2 feasible: {feasible_m1_2}")


if __name__ == '__main__':
    main()
