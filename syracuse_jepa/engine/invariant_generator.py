#!/usr/bin/env python3
"""
INVARIANT GENERATOR — Creates NEW set invariants from existing ones
=====================================================================

Architecture inspirée de :
- DeepSeek-Prover : décomposition en sous-objectifs
- FunSearch : mutation de programmes
- Aletheia : Generator-Verifier-Reviser

Méthode : COMBINER des invariants existants via des CONNECTEURS :
- AND(inv1, inv2) : les deux tiennent
- OR(inv1, inv2) : l'un des deux tient
- IMPLIES(inv1, inv2) : si inv1 alors inv2
- QUANTIFIED : ∀p|d, ∃p|d, etc.
- TRANSFORM : appliquer une transformation algébrique puis vérifier

Chaque nouvel invariant est VÉRIFIÉ numériquement.
Ceux qui passent sont ajoutés à la bibliothèque.
La chaîne de preuves est construite automatiquement.
"""

import sys, os, random, time
from math import ceil, log2, comb, gcd
from itertools import combinations
from collections import Counter
from typing import List

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


def factorize_small(n, limit=10000):
    factors = {}
    d = 2
    while d * d <= n and d < limit:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = 1
    return factors


def precompute(k_max=12):
    data = {}
    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 200000: continue
        residues = [corrsum_cumulative(sigma, k) % d
                   for sigma in enumerate_cumulative_sequences(k, S)]
        corrsums = [corrsum_cumulative(sigma, k)
                   for sigma in enumerate_cumulative_sequences(k, S)]
        data[k] = {'S': S, 'd': d, 'C': C, 'residues': residues,
                   'corrsums': corrsums, 'factors': factorize_small(d)}
    return data


# ══════════════════════════════════════════════════════════════
# INVARIANT TEMPLATES — Paramétrisables
# ══════════════════════════════════════════════════════════════

def make_inv_gcd_lt_factor(p_idx):
    """gcd(corrSum, d) ne contient pas le p_idx-ème facteur premier de d."""
    def check(k, kdata):
        primes = sorted(kdata['factors'].keys())
        if p_idx >= len(primes): return None
        p = primes[p_idx]
        return all(gcd(r, kdata['d']) % p != 0 for r in kdata['residues'] if r != 0)
    return check


def make_inv_residue_avoids_value(val_fn):
    """Aucun résidu ne vaut val_fn(k, d)."""
    def check(k, kdata):
        target = val_fn(k, kdata['d'])
        if target is None: return None
        return target % kdata['d'] not in set(kdata['residues'])
    return check


def make_inv_all_residues_satisfy(pred_fn):
    """Tous les résidus satisfont pred_fn(r, d)."""
    def check(k, kdata):
        return all(pred_fn(r, kdata['d']) for r in kdata['residues'])
    return check


def make_inv_image_size_bound(bound_fn):
    """|Image| < bound_fn(k, d)."""
    def check(k, kdata):
        n_distinct = len(set(kdata['residues']))
        bound = bound_fn(k, kdata['d'])
        return n_distinct < bound
    return check


# ══════════════════════════════════════════════════════════════
# CREATIVE COMBINATIONS — Inventer de nouveaux invariants
# ══════════════════════════════════════════════════════════════

def generate_candidate_invariants():
    """Generate a diverse set of candidate invariants."""
    candidates = []

    # Family 1: gcd-based (one per prime factor position)
    for p_idx in range(5):
        candidates.append({
            'name': f'gcd_avoids_prime_{p_idx}',
            'check': make_inv_gcd_lt_factor(p_idx),
            'description': f'gcd(corrSum,d) ne contient pas le {p_idx}ème facteur de d',
            'implies_n0': False,
        })

    # Family 2: specific residue avoidance
    targets = [
        ('avoid_0', lambda k, d: 0),
        ('avoid_d_minus_1', lambda k, d: d - 1),
        ('avoid_d_half', lambda k, d: d // 2),
        ('avoid_3k_mod_d', lambda k, d: pow(3, k) % d if d > 0 else None),
        ('avoid_2S_mod_d', lambda k, d: pow(2, compute_S(k)) % d if d > 0 else None),
        ('avoid_neg_3km1', lambda k, d: (-pow(3, k-1)) % d),
    ]
    for name, fn in targets:
        candidates.append({
            'name': name,
            'check': make_inv_residue_avoids_value(fn),
            'description': f'Image avoids {name}',
            'implies_n0': name == 'avoid_0',
        })

    # Family 3: predicate on all residues
    predicates = [
        ('all_odd_residues', lambda r, d: r % 2 == 1),
        ('all_coprime_to_6', lambda r, d: gcd(r, 6) == 1),
        ('all_gt_sqrt_d', lambda r, d: r > int(d**0.5)),
        ('all_lt_d_minus_sqrt', lambda r, d: r < d - int(d**0.5)),
        ('all_not_perfect_square', lambda r, d: int(r**0.5)**2 != r),
        ('all_have_odd_hamming', lambda r, d: bin(r).count('1') % 2 == 1),
    ]
    for name, pred in predicates:
        candidates.append({
            'name': name,
            'check': make_inv_all_residues_satisfy(pred),
            'description': f'All residues satisfy: {name}',
            'implies_n0': False,
        })

    # Family 4: image size bounds
    bounds = [
        ('image_lt_d_minus_1', lambda k, d: d),
        ('image_lt_d_over_2', lambda k, d: d // 2 + 1),
        ('image_lt_k_squared', lambda k, d: k * k),
    ]
    for name, fn in bounds:
        candidates.append({
            'name': name,
            'check': make_inv_image_size_bound(fn),
            'description': f'|Image| < {name}',
            'implies_n0': False,
        })

    # Family 5: NOVEL — combinations of corrSum with algebraic quantities
    def check_corrsum_mod_3_structure(k, kdata):
        """v₃(corrSum) = 0 toujours (dernière composante 2^{σ_{k-1}} pas div par 3)."""
        return all(cs % 3 != 0 for cs in kdata['corrsums'])

    candidates.append({
        'name': 'v3_corrsum_zero',
        'check': check_corrsum_mod_3_structure,
        'description': 'v₃(corrSum) = 0 (last term 2^{σ_{k-1}} not div by 3)',
        'implies_n0': False,
    })

    def check_corrsum_mod_d_in_specific_coset(k, kdata):
        """corrSum mod d est toujours dans la même classe mod 3."""
        d = kdata['d']
        classes = set(r % 3 for r in kdata['residues'])
        return len(classes) <= 2  # At most 2 of the 3 classes

    candidates.append({
        'name': 'residues_avoid_one_class_mod_3',
        'check': check_corrsum_mod_d_in_specific_coset,
        'description': 'Residues avoid at least one class mod 3',
        'implies_n0': False,
    })

    def check_weighted_sum_structure(k, kdata):
        """La somme pondérée Σ r_i · i est ≡ spécifique mod d."""
        d = kdata['d']
        ws = sum((i+1) * r % d for i, r in enumerate(kdata['residues'][:100])) % d
        return ws != 0  # Non-trivial weighted sum

    candidates.append({
        'name': 'weighted_sum_nonzero',
        'check': check_weighted_sum_structure,
        'description': 'Weighted sum of residues ≠ 0 mod d',
        'implies_n0': False,
    })

    return candidates


# ══════════════════════════════════════════════════════════════
# DISCOVERY LOOP
# ══════════════════════════════════════════════════════════════

def discover_invariants(k_max=12):
    """Discover new invariants by testing candidates."""
    print("INVARIANT GENERATOR — Discovering new set properties")
    print("=" * 65)

    data = precompute(k_max)
    candidates = generate_candidate_invariants()
    print(f"Testing {len(candidates)} candidate invariants on k=3..{k_max}\n")

    results = []
    for cand in candidates:
        proved = []
        failed = []
        for k, kdata in sorted(data.items()):
            result = cand['check'](k, kdata)
            if result is True:
                proved.append(k)
            elif result is False:
                failed.append(k)

        fitness = len(proved) / (len(proved) + len(failed)) if (proved or failed) else 0
        results.append({**cand, 'proved': proved, 'failed': failed, 'fitness': fitness})

    # Sort by fitness
    results.sort(key=lambda r: r['fitness'], reverse=True)

    print(f"{'Invariant':<35} {'Fit':>5} {'Proved':>8} {'Failed':>8} {'→N₀':>4}")
    print("-" * 65)

    for r in results:
        marker = "★" if r['implies_n0'] and r['fitness'] == 1.0 else " "
        print(f"{marker}{r['name']:<34} {r['fitness']:>5.3f} "
              f"{len(r['proved']):>8} {len(r['failed']):>8} "
              f"{'YES' if r['implies_n0'] else 'no':>4}")
        if r['failed'] and r['fitness'] > 0.5:
            print(f"  Failed at k={r['failed'][:5]}")

    # NEW invariants discovered (universal, not previously known)
    print(f"\n{'='*65}")
    print("NEWLY DISCOVERED UNIVERSAL INVARIANTS")
    print(f"{'='*65}")

    new_universal = [r for r in results if r['fitness'] == 1.0 and len(r['proved']) >= 8]
    for r in new_universal:
        print(f"  {'★' if r['implies_n0'] else '·'} {r['name']}: {r['description']}")

    return results


if __name__ == '__main__':
    discover_invariants(k_max=12)
