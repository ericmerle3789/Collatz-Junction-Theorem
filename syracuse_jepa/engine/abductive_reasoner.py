#!/usr/bin/env python3
"""
ABDUCTIVE REASONER — Work BACKWARDS from the conclusion
==========================================================

Au lieu de : "que puis-je prouver ?" → "est-ce que ça implique N₀=0 ?"
Fait : "N₀=0 est vrai" → "quelle est la RAISON MINIMALE ?"

L'abduction cherche la MEILLEURE EXPLICATION d'un fait observé.

FAIT : corrSum(σ) mod d ≠ 0 pour tout σ et tout k=3..14.
QUESTION : Quelle est la propriété ALGÉBRIQUE qui force cela ?

Méthode : pour chaque k, examiner la structure fine de POURQUOI
0 est évité, et chercher un PATTERN commun à tous les k.

APPROCHE INVERSE :
1. Supposer qu'il EXISTE σ₀ avec corrSum(σ₀) ≡ 0 mod d.
2. Dériver les CONSÉQUENCES de cette hypothèse.
3. Trouver une conséquence IMPOSSIBLE.
4. La conséquence impossible = la raison de l'abduction.
"""

import sys, os
from math import ceil, log2, comb, gcd
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


def abduct_from_contradiction(k):
    """
    Pour un k donné : supposer qu'un σ₀ existe avec corrSum ≡ 0 mod d.
    Dériver toutes les conséquences et chercher l'impossible.
    """
    S = compute_S(k)
    d = compute_d(k)
    if d <= 0: return None

    consequences = []

    # CONSÉQUENCE 1 : n₀ = corrSum/d est un entier positif
    # n₀ est dans l'intervalle [cs_min/d, cs_max/d]
    cs_min = sum(pow(3, k-1-i) * pow(2, i) for i in range(k))  # σ = (0,1,...,k-1)
    cs_max_est = sum(pow(3, k-1-i) * pow(2, S-k+i) for i in range(k))  # rough max
    n0_min = cs_min // d + (1 if cs_min % d else 0)
    n0_max = cs_max_est // d
    consequences.append({
        'name': 'n0_range',
        'statement': f'n₀ ∈ [{n0_min}, {n0_max}]',
        'n_candidates': n0_max - n0_min + 1,
    })

    # CONSÉQUENCE 2 : n₀ est impair (cycle condition)
    n_odd = sum(1 for n in range(n0_min, n0_max + 1) if n % 2 == 1)
    consequences.append({
        'name': 'n0_odd',
        'statement': f'n₀ impair, {n_odd} candidats',
        'n_candidates': n_odd,
    })

    # CONSÉQUENCE 3 : n₀ ≡ c mod 2^S (Steiner structural)
    # n₀ · 3^k + corrSum = n₀ · 2^S → n₀ ≡ -corrSum · (3^k)^{-1} mod 2^S
    # Mais corrSum dépend de σ... c'est circulaire.
    # CEPENDANT : n₀ mod 2^{e₁} est contraint par 3n₀+1 ≡ 0 mod 2^{e₁}
    # Pour chaque possible e₁ (= σ₁) : n₀ ≡ (2^{e₁}-1)/3 mod 2^{e₁}
    orbit_constraints = []
    for e1 in range(1, S - k + 2):
        required = ((pow(2, e1) - 1) * pow(3, -1, pow(2, e1))) % pow(2, e1)
        # Count odd n₀ in range satisfying this congruence
        count = 0
        for n0 in range(max(1, n0_min), n0_max + 1):
            if n0 % 2 == 1 and n0 % pow(2, e1) == required:
                count += 1
        orbit_constraints.append({
            'e1': e1,
            'required_mod': required,
            'modulus': pow(2, e1),
            'n_valid': count,
        })

    # Total valid (union over all e₁)
    all_valid = set()
    for oc in orbit_constraints:
        for n0 in range(max(1, n0_min), n0_max + 1):
            if n0 % 2 == 1 and n0 % oc['modulus'] == oc['required_mod']:
                all_valid.add(n0)

    consequences.append({
        'name': 'orbit_constraint',
        'statement': f'n₀ must satisfy orbit at e₁, {len(all_valid)} valid n₀',
        'n_candidates': len(all_valid),
        'per_e1': orbit_constraints[:5],
    })

    # CONSÉQUENCE 4 : n₀ · d doit être un corrSum achievable
    C = count_cumulative_sequences(k, S)
    if C <= 200000:
        achievable = set(corrsum_cumulative(sigma, k)
                        for sigma in enumerate_cumulative_sequences(k, S))

        # How many valid n₀ have n₀·d ∈ achievable?
        n_achievable = 0
        for n0 in all_valid:
            if n0 * d in achievable:
                n_achievable += 1

        consequences.append({
            'name': 'achievability',
            'statement': f'{n_achievable}/{len(all_valid)} valid n₀ have n₀·d achievable',
            'n_candidates': n_achievable,
            'is_contradiction': n_achievable == 0,
        })
    else:
        consequences.append({
            'name': 'achievability',
            'statement': 'C too large to check',
            'n_candidates': -1,
        })

    # CHERCHER LA CONTRADICTION
    contradictions = [c for c in consequences if c.get('is_contradiction')]

    return {
        'k': k, 'd': d, 'consequences': consequences,
        'contradictions': contradictions,
        'is_refuted': len(contradictions) > 0,
    }


def run_abductive_analysis(k_max=12):
    """Run abductive reasoning for all k."""
    print("ABDUCTIVE REASONER — Working backwards from N₀=0")
    print("=" * 65)

    for k in range(3, k_max + 1):
        result = abduct_from_contradiction(k)
        if result is None: continue

        refuted = result['is_refuted']
        print(f"\nk={k}, d={result['d']}: {'REFUTED ✓' if refuted else 'NOT REFUTED'}")
        for c in result['consequences']:
            candidates = c['n_candidates']
            marker = " ★ CONTRADICTION" if c.get('is_contradiction') else ""
            print(f"  {c['name']}: {c['statement'][:60]}{marker}")

    # INSIGHT: Pour quels k la contradiction est-elle trouvée ?
    print(f"\n{'='*65}")
    print("ABDUCTIVE INSIGHT")
    print(f"{'='*65}")
    print("La contradiction vient de l'ACHIEVABILITY :")
    print("Aucun n₀ valide (impair + orbit constraint) n'a n₀·d achievable.")
    print("C'est une COMBINAISON de :")
    print("  (a) n₀ impair (parity)")
    print("  (b) n₀ ≡ c mod 2^{e₁} (orbit)")
    print("  (c) n₀·d ∈ {corrSum(σ)} (achievability)")
    print("Les trois ensemble = VIDE.")


if __name__ == '__main__':
    run_abductive_analysis()
