#!/usr/bin/env python3
"""
Teleological Study — Working Backwards from the Proof Structure
═══════════════════════════════════════════════════════════════

    "L'information qui vient du futur" — si la preuve existe,
    quelles propriétés DOIVENT être vraies ?

Découverte CCE Cycle 1: les paires (k,p) avec N₀(p)=0 ont
systématiquement q/k >> 1, tandis que les non-évitantes ont q/k ~ 1.

Ce module:
1. Scanne TOUS les (k,p) jusqu'à k=80 pour classifier avoidance
2. Cherche le SEUIL MINIMAL q/k qui garantit N₀(p) = 0
3. Connecte au résultat LDS : k₀(p) ≥ c·q (R196-R197)
4. Identifie les cas LIMITES (near-miss) pour comprendre le mécanisme

CONNEXION AU GAP 1.35x:
  Si q/k > τ est suffisant pour avoidance, et si tout p|d(k)
  a un tel q, alors la preuve est complète. Le gap 1.35x se réduit
  à prouver que les facteurs premiers de d(k) ont des ordres assez grands.
"""

import math
import cmath
from dataclasses import dataclass
from typing import List, Dict, Tuple, Optional
from collections import defaultdict

from syracuse_jepa.pipeline.analyst import compute_S, compute_d, factorize, multiplicative_order
from syracuse_jepa.pipeline.spectral import count_compositions_with_residue


@dataclass
class AvoidancePair:
    """A (k, p) pair with its avoidance data."""
    k: int
    p: int
    q: int                    # ord_p(2)
    q_over_k: float           # the teleological ratio
    n0: int                   # N₀(p) exact count
    n_total: int
    avoids: bool              # N₀(p) == 0
    is_primitive_root: bool   # q == p - 1
    rho_free: float           # max |S(a)|/q
    R_bound: float            # q * rho^{k-1}
    fcq_proves: bool          # R_bound < 1


@dataclass
class ThresholdAnalysis:
    """Analysis of the q/k threshold for avoidance."""
    n_pairs: int
    n_avoiding: int
    n_non_avoiding: int
    min_avoiding_qk: float    # minimum q/k among avoiding pairs
    max_non_avoiding_qk: float # maximum q/k among non-avoiding pairs
    separation_gap: float     # min_avoiding - max_non_avoiding
    has_clean_separation: bool # no overlap between avoiding and non-avoiding
    threshold: float          # proposed threshold
    confidence: str
    exceptions: List[AvoidancePair]  # pairs that violate the threshold


def compute_rho_free(p: int) -> float:
    """Compute the free FCQ spectral radius for prime p."""
    q = multiplicative_order(2, p)
    omega = cmath.exp(2j * cmath.pi / p)
    powers = [pow(2, j, p) for j in range(q)]

    max_rho = 0
    for a in range(1, p):
        S_a = sum(omega ** (a * pw % p) for pw in powers)
        rho_a = abs(S_a) / q
        max_rho = max(max_rho, rho_a)

    return max_rho


def scan_avoidance_pairs(k_max: int = 50, max_prime: int = 200) -> List[AvoidancePair]:
    """
    Scan all (k, p) pairs where p | d(k) and p <= max_prime.
    For each, compute exact N₀(p), ord_p(2), q/k ratio, FCQ bound.
    """
    pairs = []
    rho_cache = {}

    print(f"  Scanning k=3..{k_max}, primes <= {max_prime}...")

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 1:
            continue

        factors = factorize(d)
        small_primes = sorted(set(p for p, _ in factors if p <= max_prime))

        for p in small_primes:
            q = multiplicative_order(2, p)

            # Compute rho (cached)
            if p not in rho_cache:
                rho_cache[p] = compute_rho_free(p)
            rho = rho_cache[p]

            # FCQ bound
            R_bound = q * rho ** (k - 1) if rho < 1 else float('inf')
            fcq_proves = R_bound < 1

            # Exact N₀(p) — skip for very large k*p combinations
            if k * p <= 20000:
                n0, n_total = count_compositions_with_residue(k, S, p, target_r=0)
            else:
                n0, n_total = -1, -1  # too expensive

            avoids = (n0 == 0) if n0 >= 0 else fcq_proves

            pair = AvoidancePair(
                k=k, p=p, q=q,
                q_over_k=q / k,
                n0=n0, n_total=n_total,
                avoids=avoids,
                is_primitive_root=(q == p - 1),
                rho_free=rho,
                R_bound=R_bound,
                fcq_proves=fcq_proves,
            )
            pairs.append(pair)

        if k <= 30 or k % 10 == 0:
            n_avoids = sum(1 for pair in pairs if pair.k == k and pair.avoids)
            n_primes_k = sum(1 for pair in pairs if pair.k == k)
            print(f"    k={k:3d}: {n_primes_k} primes, {n_avoids} avoiding")

    print(f"  Total: {len(pairs)} (k,p) pairs scanned")
    return pairs


def analyze_threshold(pairs: List[AvoidancePair]) -> ThresholdAnalysis:
    """
    Analyze the q/k threshold that separates avoiding from non-avoiding pairs.

    The teleological question: what value of q/k GUARANTEES avoidance?
    """
    # Only use pairs with exact N₀
    exact_pairs = [p for p in pairs if p.n0 >= 0]
    avoiding = [p for p in exact_pairs if p.avoids]
    non_avoiding = [p for p in exact_pairs if not p.avoids]

    if not avoiding or not non_avoiding:
        return ThresholdAnalysis(
            n_pairs=len(exact_pairs),
            n_avoiding=len(avoiding),
            n_non_avoiding=len(non_avoiding),
            min_avoiding_qk=0, max_non_avoiding_qk=0,
            separation_gap=0, has_clean_separation=False,
            threshold=0, confidence="insufficient_data",
            exceptions=[]
        )

    # Key quantities
    avoid_qk = sorted(p.q_over_k for p in avoiding)
    nonavoid_qk = sorted(p.q_over_k for p in non_avoiding)

    min_avoid = min(avoid_qk)
    max_nonavoid = max(nonavoid_qk)

    gap = min_avoid - max_nonavoid
    clean = gap > 0

    # Find exceptions (avoiding with low q/k or non-avoiding with high q/k)
    threshold = (min_avoid + max_nonavoid) / 2 if clean else max_nonavoid
    exceptions = []
    for p in exact_pairs:
        if p.avoids and p.q_over_k < threshold:
            exceptions.append(p)
        if not p.avoids and p.q_over_k > threshold:
            exceptions.append(p)

    # Confidence
    if clean and len(avoiding) >= 10:
        confidence = "strong"
    elif clean:
        confidence = "moderate"
    else:
        confidence = "weak_overlap"

    return ThresholdAnalysis(
        n_pairs=len(exact_pairs),
        n_avoiding=len(avoiding),
        n_non_avoiding=len(non_avoiding),
        min_avoiding_qk=min_avoid,
        max_non_avoiding_qk=max_nonavoid,
        separation_gap=gap,
        has_clean_separation=clean,
        threshold=threshold,
        confidence=confidence,
        exceptions=exceptions,
    )


def study_near_misses(pairs: List[AvoidancePair]) -> List[dict]:
    """
    Study pairs near the threshold boundary.
    These are the most informative: they reveal the MECHANISM of avoidance.
    """
    exact_pairs = [p for p in pairs if p.n0 >= 0]
    if not exact_pairs:
        return []

    # Sort by distance from N₀=0
    # For avoiding pairs: how "barely" do they avoid? (look at smallest gap)
    # For non-avoiding: how close to 0 is N₀/N?
    near_misses = []

    for pair in exact_pairs:
        if pair.avoids:
            # Avoiding: record the minimal non-zero count for r ≠ 0
            # (this tells us how "tight" the avoidance is)
            near_misses.append({
                "k": pair.k, "p": pair.p, "q": pair.q,
                "q_over_k": pair.q_over_k,
                "avoids": True,
                "n0": 0,
                "proximity": 0,  # distance from failing
                "rho": pair.rho_free,
            })
        else:
            if pair.n_total > 0:
                fraction = pair.n0 / pair.n_total
                near_misses.append({
                    "k": pair.k, "p": pair.p, "q": pair.q,
                    "q_over_k": pair.q_over_k,
                    "avoids": False,
                    "n0": pair.n0,
                    "proximity": fraction,
                    "rho": pair.rho_free,
                })

    # Sort non-avoiding by proximity to 0 (smallest fraction first)
    non_avoiding_sorted = sorted(
        [m for m in near_misses if not m["avoids"]],
        key=lambda x: x["proximity"]
    )

    return non_avoiding_sorted[:20]  # top 20 nearest misses


def study_primitive_root_effect(pairs: List[AvoidancePair]) -> dict:
    """
    Study whether being a primitive root (q = p-1) correlates with avoidance.
    Known: ρ_p = 1/(p-1) when 2 is primitive root → FCQ always works eventually.
    But: how much does this help in practice?
    """
    prim_root_pairs = [p for p in pairs if p.is_primitive_root and p.n0 >= 0]
    non_prim_pairs = [p for p in pairs if not p.is_primitive_root and p.n0 >= 0]

    prim_avoid_rate = (sum(1 for p in prim_root_pairs if p.avoids) / len(prim_root_pairs)
                       if prim_root_pairs else 0)
    non_prim_avoid_rate = (sum(1 for p in non_prim_pairs if p.avoids) / len(non_prim_pairs)
                           if non_prim_pairs else 0)

    return {
        "n_primitive_root": len(prim_root_pairs),
        "n_non_primitive": len(non_prim_pairs),
        "prim_avoid_rate": prim_avoid_rate,
        "non_prim_avoid_rate": non_prim_avoid_rate,
        "advantage_ratio": (prim_avoid_rate / non_prim_avoid_rate
                           if non_prim_avoid_rate > 0 else float('inf')),
    }


def run_teleological_study(k_max: int = 40, max_prime: int = 100) -> dict:
    """Full teleological study."""
    print()
    print("╔" + "═" * 68 + "╗")
    print("║  TELEOLOGICAL STUDY — Working Backwards from the Future          ║")
    print("║  'Si la preuve existe, quelles propriétés DOIVENT être vraies?'  ║")
    print("╚" + "═" * 68 + "╝")
    print()

    # Phase 1: Scan all pairs
    print("┌─ PHASE 1: SCAN ───────────────────────────────────────────┐")
    pairs = scan_avoidance_pairs(k_max, max_prime)
    print(f"└─ {len(pairs)} pairs scanned ──────────────────────────────┘\n")

    # Phase 2: Threshold analysis
    print("┌─ PHASE 2: THRESHOLD ANALYSIS ─────────────────────────────┐")
    threshold = analyze_threshold(pairs)
    print(f"  Total pairs with exact N₀: {threshold.n_pairs}")
    print(f"  Avoiding: {threshold.n_avoiding}, Non-avoiding: {threshold.n_non_avoiding}")
    print(f"  Min avoiding q/k:     {threshold.min_avoiding_qk:.4f}")
    print(f"  Max non-avoiding q/k: {threshold.max_non_avoiding_qk:.4f}")
    print(f"  Separation gap:       {threshold.separation_gap:.4f}")
    print(f"  Clean separation:     {threshold.has_clean_separation}")
    print(f"  Proposed threshold:   {threshold.threshold:.4f}")
    print(f"  Confidence:           {threshold.confidence}")
    if threshold.exceptions:
        print(f"  Exceptions: {len(threshold.exceptions)}")
        for exc in threshold.exceptions[:5]:
            print(f"    k={exc.k}, p={exc.p}, q/k={exc.q_over_k:.2f}, "
                  f"avoids={exc.avoids}, N₀={exc.n0}")
    print(f"└─ Threshold analysis complete ─────────────────────────────┘\n")

    # Phase 3: Near misses
    print("┌─ PHASE 3: NEAR MISSES ────────────────────────────────────┐")
    near_misses = study_near_misses(pairs)
    if near_misses:
        print(f"  Top near-misses (closest to avoidance without achieving it):")
        for nm in near_misses[:10]:
            print(f"    k={nm['k']:3d}, p={nm['p']:5d}, q={nm['q']:4d}, "
                  f"q/k={nm['q_over_k']:.2f}, N₀/N={nm['proximity']:.6f}")
    print(f"└─ {len(near_misses)} near misses analyzed ─────────────────┘\n")

    # Phase 4: Primitive root effect
    print("┌─ PHASE 4: PRIMITIVE ROOT EFFECT ──────────────────────────┐")
    prim = study_primitive_root_effect(pairs)
    print(f"  Primitive root pairs: {prim['n_primitive_root']} "
          f"(avoid rate: {prim['prim_avoid_rate']:.2%})")
    print(f"  Non-primitive pairs:  {prim['n_non_primitive']} "
          f"(avoid rate: {prim['non_prim_avoid_rate']:.2%})")
    print(f"  Advantage ratio: {prim['advantage_ratio']:.2f}x")
    print(f"└─ Primitive root analysis complete ────────────────────────┘\n")

    # Phase 5: Distribution of q/k values
    print("┌─ PHASE 5: q/k DISTRIBUTION ───────────────────────────────┐")
    exact_pairs = [p for p in pairs if p.n0 >= 0]
    avoid_qk = sorted(p.q_over_k for p in exact_pairs if p.avoids)
    nonavoid_qk = sorted(p.q_over_k for p in exact_pairs if not p.avoids)

    if avoid_qk:
        print(f"  Avoiding q/k:     min={min(avoid_qk):.3f}, "
              f"median={avoid_qk[len(avoid_qk)//2]:.3f}, "
              f"mean={sum(avoid_qk)/len(avoid_qk):.3f}, "
              f"max={max(avoid_qk):.3f}")
    if nonavoid_qk:
        print(f"  Non-avoiding q/k: min={min(nonavoid_qk):.3f}, "
              f"median={nonavoid_qk[len(nonavoid_qk)//2]:.3f}, "
              f"mean={sum(nonavoid_qk)/len(nonavoid_qk):.3f}, "
              f"max={max(nonavoid_qk):.3f}")

    # Histogram
    print(f"\n  q/k histogram (avoiding vs non-avoiding):")
    bins = [0, 0.5, 1, 1.5, 2, 3, 5, 10, 50]
    for i in range(len(bins) - 1):
        lo, hi = bins[i], bins[i + 1]
        n_a = sum(1 for q in avoid_qk if lo <= q < hi)
        n_na = sum(1 for q in nonavoid_qk if lo <= q < hi)
        bar_a = "█" * min(n_a, 40)
        bar_na = "░" * min(n_na, 40)
        print(f"    [{lo:5.1f}, {hi:5.1f}) avoid={n_a:4d} |{bar_a}")
        print(f"    {'':13s} nona ={n_na:4d} |{bar_na}")
    print(f"└─ Distribution analysis complete ──────────────────────────┘\n")

    # Synthesis
    print("╔" + "═" * 68 + "╗")
    print("║  TELEOLOGICAL SYNTHESIS                                          ║")
    print("╠" + "═" * 68 + "╣")

    if threshold.has_clean_separation:
        print(f"║  CLEAN SEPARATION at q/k = {threshold.threshold:.3f}")
        print(f"║  → All avoiding pairs have q/k ≥ {threshold.min_avoiding_qk:.3f}")
        print(f"║  → All non-avoiding have q/k ≤ {threshold.max_non_avoiding_qk:.3f}")
        print(f"║  → GAP = {threshold.separation_gap:.3f}")
        print(f"║")
        print(f"║  IMPLICATION: If we can prove ord_p(2)/k > {threshold.threshold:.3f}")
        print(f"║  for SOME p|d(k), avoidance follows.")
        print(f"║  This connects to LDS (R196): k₀(p) ≥ c·q with c ≥ 1/25")
    else:
        print(f"║  NO CLEAN SEPARATION — q/k overlap between [")
        print(f"║  {threshold.min_avoiding_qk:.3f}, {threshold.max_non_avoiding_qk:.3f}]")
        print(f"║  → The threshold is NECESSARY but not SUFFICIENT")
        print(f"║  → Additional structure needed (primitive root? orbit structure?)")

    print("╚" + "═" * 68 + "╝")

    return {
        "n_pairs": len(pairs),
        "threshold": threshold.threshold,
        "clean_separation": threshold.has_clean_separation,
        "separation_gap": threshold.separation_gap,
        "min_avoiding_qk": threshold.min_avoiding_qk,
        "max_non_avoiding_qk": threshold.max_non_avoiding_qk,
        "confidence": threshold.confidence,
        "prim_root_advantage": prim["advantage_ratio"],
        "n_near_misses": len(near_misses),
        "near_misses": near_misses[:5],
    }


if __name__ == '__main__':
    import json
    import sys

    k_max = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    result = run_teleological_study(k_max, max_prime=100)

    with open('syracuse_jepa/pipeline/teleological_results.json', 'w') as f:
        json.dump(result, f, indent=2, ensure_ascii=False, default=str)
    print(f"\nSaved to teleological_results.json")
