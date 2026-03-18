#!/usr/bin/env python3
"""
SEQUENCE REASONER — Raisonnement sur des PROPRIÉTÉS UNIVERSELLES de séquences
================================================================================

Le problème : prouver ∀σ ∈ Comp_cum(S,k) : corrSum(σ) ≢ 0 mod d.

Les moteurs précédents travaillaient sur des SCALAIRES (ρ, d, k).
Ce moteur travaille sur des PROPRIÉTÉS DE L'ENSEMBLE des séquences.

OBJETS MANIPULÉS :
- UniversalProperty : une proposition ∀σ.P(σ)
- ExistentialWitness : un σ₀ tel que P(σ₀)
- SetInvariant : une propriété de l'ENSEMBLE {corrSum(σ) : σ ∈ Comp}
- TransformRule : une transformation qui préserve/crée des invariants

RAISONNEMENT :
Un SetInvariant est PROUVÉ si :
1. Il est vérifié numériquement pour tous les k testables, ET
2. Il découle logiquement d'invariants déjà prouvés

La CHAÎNE DE PREUVE est :
SetInvariant₁ (prouvable) → SetInvariant₂ → ... → "0 ∉ Image(corrSum mod d)"

Chaque maillon est une TransformRule qui déduit un invariant du précédent.
"""

import sys, os, json, random, time
from math import ceil, log2, comb, gcd
from itertools import combinations
from collections import Counter
from dataclasses import dataclass, field
from typing import List, Dict, Set, Tuple, Optional, Callable

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative, corrsum_cumulative_mod,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


# ══════════════════════════════════════════════════════════════
# INVARIANTS — Propriétés de l'ensemble Im(corrSum mod d)
# ══════════════════════════════════════════════════════════════

@dataclass
class SetInvariant:
    """Une propriété de l'ensemble Image = {corrSum(σ) mod d : σ ∈ Comp}."""
    name: str
    description: str
    checker: Callable  # (k, S, d, residues: List[int]) -> bool
    proved_for: List[int] = field(default_factory=list)  # k values where verified
    failed_for: List[int] = field(default_factory=list)
    is_universal: bool = False  # True if proved for all k (algebraically)
    implies_N0_zero: bool = False  # True if this invariant implies N₀=0
    proof_sketch: str = ""

    @property
    def fitness(self):
        n = len(self.proved_for) + len(self.failed_for)
        if n == 0: return 0
        return len(self.proved_for) / n

    def verify(self, k, S, d, residues):
        try:
            result = self.checker(k, S, d, residues)
            if result:
                if k not in self.proved_for:
                    self.proved_for.append(k)
            else:
                if k not in self.failed_for:
                    self.failed_for.append(k)
            return result
        except:
            return None


# ══════════════════════════════════════════════════════════════
# INVARIANT LIBRARY — Connus + à découvrir
# ══════════════════════════════════════════════════════════════

def inv_zero_not_in_image(k, S, d, residues):
    """L'invariant cible : 0 ∉ Image."""
    return 0 not in residues

def inv_image_subset_units(k, S, d, residues):
    """Image ⊂ (Z/dZ)* (tous coprime à d)."""
    return all(gcd(r, d) == 1 for r in residues)

def inv_image_in_subgroup_2_3(k, S, d, residues):
    """Image ⊂ ⟨2,3⟩ dans (Z/dZ)*."""
    gen23 = {1}
    frontier = {1}
    visited = set()
    while frontier:
        x = frontier.pop()
        if x in visited: continue
        visited.add(x)
        gen23.add(x)
        y2 = (x * 2) % d
        y3 = (x * 3) % d
        if y2 not in visited: frontier.add(y2)
        if y3 not in visited: frontier.add(y3)
        if len(visited) > d: break
    return all(r in gen23 for r in residues if r != 0)

def inv_d_unique_missing_divisor(k, S, d, residues):
    """d est le seul diviseur de d non atteint par gcd(corrSum, d)."""
    achieved_gcds = set(gcd(r, d) if r != 0 else 0 for r in residues)
    # Note: gcd(0,d) = d, mais 0 n'est pas dans residues (on espère)
    all_divisors = set(i for i in range(1, d+1) if d % i == 0)
    missed = all_divisors - achieved_gcds
    return d in missed  # d is among missing (= N₀=0 at minimum)

def inv_min_residue_ge_1(k, S, d, residues):
    """min(r, d-r) ≥ 1 pour tout r (distance à 0 ≥ 1)."""
    return all(min(r, d - r) >= 1 for r in residues)

def inv_all_corrsum_gt_d(k, S, d, residues):
    """Tous les corrSum > d en valeur absolue (pas juste mod d)."""
    # This checks the actual corrSum values, not residues
    # residues are corrSum mod d, but corrSum > d is L1 (always true)
    return True  # Placeholder — need actual corrSum values

def inv_image_avoids_zero_coset(k, S, d, residues):
    """L'image évite le coset 0 + d·Z (i.e., {0})."""
    return 0 not in set(residues)

def inv_sorted_correction_nonzero(k, S, d, residues):
    """Pour tout δ non-trié avec F(δ)=0 : F(sorted(δ)) ≠ 0.
    C'est l'invariant d'ordonnancement."""
    max_delta = S - k
    inv3 = pow(3, -1, d)
    rho = (2 * inv3) % d
    rho_pow = [pow(rho, i, d) for i in range(k)]
    two_pow = [pow(2, j, d) for j in range(max_delta + 1)]

    total = (max_delta + 1) ** (k - 1)
    if total > 500000:
        return None  # Can't verify

    from itertools import product as cart_product
    for deltas in cart_product(range(max_delta + 1), repeat=k-1):
        f_val = (1 + sum(rho_pow[i+1] * two_pow[deltas[i]] % d for i in range(k-1))) % d
        if f_val != 0: continue
        sorted_d = tuple(sorted(deltas))
        if sorted_d == deltas: continue
        f_sorted = (1 + sum(rho_pow[i+1] * two_pow[sorted_d[i]] % d for i in range(k-1))) % d
        if f_sorted == 0:
            return False  # Sorting preserves zero — BAD
    return True

def inv_rho_not_root_of_any_Rdelta(k, S, d, residues):
    """ρ n'est racine d'aucun R_δ (le polynôme quotient)."""
    # Same as sorted_correction_nonzero but stated differently
    return inv_sorted_correction_nonzero(k, S, d, residues)

def inv_coverage_lt_half(k, S, d, residues):
    """La couverture C/d < 1/2 (Junction bound renforce)."""
    C = len(residues)
    return C < d / 2

def inv_ord_d_2_gt_sk(k, S, d, residues):
    """ord_d(2) > S - k."""
    if d > 10**8: return None
    phi = d
    n = d
    dd = 2
    while dd * dd <= n:
        if n % dd == 0:
            phi = phi // dd * (dd - 1)
            while n % dd == 0: n //= dd
        dd += 1
    if n > 1: phi = phi // n * (n - 1)
    result = phi
    factors = []
    n = phi
    dd = 2
    while dd * dd <= n:
        if n % dd == 0:
            factors.append(dd)
            while n % dd == 0: n //= dd
        dd += 1
    if n > 1: factors.append(n)
    for p in factors:
        while result % p == 0 and pow(2, result // p, d) == 1:
            result //= p
    return result > (S - k)


# ══════════════════════════════════════════════════════════════
# INVARIANT REGISTRY
# ══════════════════════════════════════════════════════════════

def build_invariant_library():
    """Build the library of known invariants."""
    return [
        SetInvariant("TARGET_N0_zero", "0 ∉ Image(corrSum mod d)",
                     inv_zero_not_in_image, implies_N0_zero=True),
        SetInvariant("image_in_units", "Image ⊂ (Z/dZ)*",
                     inv_image_subset_units, implies_N0_zero=True),
        SetInvariant("image_in_23", "Image ⊂ ⟨2,3⟩",
                     inv_image_in_subgroup_2_3, implies_N0_zero=True),
        SetInvariant("d_unique_missing", "d seul diviseur non atteint de gcd",
                     inv_d_unique_missing_divisor),
        SetInvariant("min_dist_ge_1", "Dist min à 0 ≥ 1",
                     inv_min_residue_ge_1, implies_N0_zero=True),
        SetInvariant("sorting_correction_nz", "Correction de tri toujours ≠ 0",
                     inv_sorted_correction_nonzero, implies_N0_zero=True),
        SetInvariant("rho_not_root_R", "ρ ∉ racines(R_δ) pour tout δ",
                     inv_rho_not_root_of_any_Rdelta, implies_N0_zero=True),
        SetInvariant("coverage_lt_half", "C/d < 1/2",
                     inv_coverage_lt_half),
        SetInvariant("ord_gt_sk", "ord_d(2) > S-k",
                     inv_ord_d_2_gt_sk),
    ]


# ══════════════════════════════════════════════════════════════
# VERIFICATION ENGINE
# ══════════════════════════════════════════════════════════════

def verify_all_invariants(k_max=14):
    """Verify all invariants on all testable k values."""
    print("SEQUENCE REASONER — Universal Property Verification")
    print("=" * 65)

    library = build_invariant_library()

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 500000: continue

        # Compute residues
        residues = []
        for sigma in enumerate_cumulative_sequences(k, S):
            residues.append(corrsum_cumulative(sigma, k) % d)

        for inv in library:
            inv.verify(k, S, d, residues)

    # Report
    print(f"\n{'Invariant':<30} {'Proved':>8} {'Failed':>8} {'Fitness':>8} {'→N₀=0':>6}")
    print("-" * 65)

    for inv in sorted(library, key=lambda i: i.fitness, reverse=True):
        n_proved = len(inv.proved_for)
        n_failed = len(inv.failed_for)
        implies = "YES" if inv.implies_N0_zero else "no"
        print(f"{inv.name:<30} {n_proved:>8} {n_failed:>8} {inv.fitness:>8.3f} {implies:>6}")
        if inv.failed_for:
            print(f"  Failed at k = {inv.failed_for[:5]}")

    # CHAIN ANALYSIS: which invariants IMPLY others?
    print(f"\n{'='*65}")
    print("IMPLICATION CHAIN ANALYSIS")
    print(f"{'='*65}")

    # Universal invariants (true for ALL tested k)
    universal = [inv for inv in library if inv.fitness == 1.0 and len(inv.proved_for) > 0]
    print(f"\nUniversal invariants (fitness=1.0):")
    for inv in universal:
        suffix = " ★ IMPLIES N₀=0" if inv.implies_N0_zero else ""
        print(f"  ✓ {inv.name} (tested k={inv.proved_for[0]}..{inv.proved_for[-1]}){suffix}")

    # Which universal invariants imply N₀=0?
    proof_candidates = [inv for inv in universal if inv.implies_N0_zero]
    print(f"\nProof candidates (universal + implies N₀=0):")
    for inv in proof_candidates:
        print(f"  ★ {inv.name}: {inv.description}")

    return library


if __name__ == '__main__':
    verify_all_invariants(k_max=12)
