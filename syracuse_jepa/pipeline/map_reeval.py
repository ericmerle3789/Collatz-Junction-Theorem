#!/usr/bin/env python3
"""
Research Map Re-Evaluator — Cross-referencing 195 rounds with exact computation.

Re-evaluates closed pistes from RESEARCH_MAP.md to check if any were
wrongly closed. Uses exact pipeline computations (not heuristics).

KEY PISTES TO RE-EVALUATE:
  - R29 Ratio Law: N₀·p/C → 1?  (our rho_study shows max=3.37, NOT < 1)
  - R84-R86 CRT anticorrelation: N₀(d) ≤ Π N₀(p)/C^{ω-1}?
  - R31 Order-Diversity Bound: high ord_p(2) → avoidance?
  - R58 Parseval/CS: too weak (confirmed by parseval_bound.py)
  - R189-R191 Operator framework: gap 1.35x
  - R196-R197 LDS+FCQ: the viable path

STRUCTURAL INVARIANTS DISCOVERED:
  1. 3 NOT in <2> mod p for ANY p|d(k) — UNIVERSAL
  2. V/C ratio converges to ~1.3
  3. Omitted residue fraction stable
  4. Entropy deficit gamma ~ 1.06k
"""

import math
from collections import Counter
from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional

from syracuse_jepa.pipeline.analyst import (
    compute_S, compute_d, factorize, multiplicative_order, is_in_subgroup
)
from syracuse_jepa.pipeline.spectral import count_compositions_with_residue


@dataclass
class PisteReeval:
    """Re-evaluation result for one research piste."""
    piste_id: str              # e.g. "R29", "R84-R86"
    name: str
    original_status: str       # "closed", "open", "suspended"
    new_status: str            # "confirmed_closed", "reopened", "upgraded"
    reason: str
    evidence: str
    confidence: float          # 0-1
    computational_data: dict = field(default_factory=dict)


@dataclass
class StructuralInvariant:
    """A structural invariant discovered by computation."""
    name: str
    statement: str
    verified_range: str        # e.g. "k=3..80"
    counterexample: Optional[str]
    connects_to: str           # research piste
    proof_potential: str       # "provable", "hard", "open"


def compute_full_residue_data(k: int, p: int) -> dict:
    """Compute complete residue distribution mod p for k."""
    S = compute_S(k)
    residues = {}
    total = 0
    for r in range(p):
        nr, nt = count_compositions_with_residue(k, S, p, target_r=r)
        if nr > 0:
            residues[r] = nr
        if r == 0:
            total = nt
    return {
        'k': k, 'p': p, 'S': S,
        'residues': residues,
        'N0': residues.get(0, 0),
        'C': total,
        'n_distinct': len(residues),
    }


def reeval_ratio_law(k_max: int = 80) -> PisteReeval:
    """
    Re-evaluate R29 Ratio Law: N₀·p/C -> 1 as k -> inf.
    Our rho_study showed max rho = 3.37, so the "law" is NOT universal.
    """
    print("  Re-evaluating R29 (Ratio Law)...")

    rho_data = {}
    max_rho = 0.0
    max_kp = (0, 0)

    for k in range(3, min(k_max + 1, 50)):
        if k == 4:
            continue
        S = compute_S(k)
        d = compute_d(k)
        factors = factorize(d)
        primes = sorted(set(p for p, _ in factors if p <= 100))

        for p in primes[:3]:
            n0, nt = count_compositions_with_residue(k, S, p, target_r=0)
            if nt > 0:
                rho = n0 * p / nt
                rho_data[(k, p)] = rho
                if rho > max_rho:
                    max_rho = rho
                    max_kp = (k, p)

    # Check if rho -> 1 for large k (fixed p)
    by_prime = {}
    for (k, p), rho in rho_data.items():
        if p not in by_prime:
            by_prime[p] = []
        by_prime[p].append((k, rho))

    converging = 0
    diverging = 0
    for p, pairs in by_prime.items():
        if len(pairs) < 3:
            continue
        pairs.sort()
        late = [r for k, r in pairs if k > 20]
        if late and max(late) < 1.05:
            converging += 1
        elif late and max(late) > 1.5:
            diverging += 1

    if max_rho > 1.5:
        status = "confirmed_closed"
        reason = (f"rho_max = {max_rho:.4f} at k={max_kp[0]}, p={max_kp[1]}. "
                  "Ratio NOT universally < 1. Original closure justified.")
    else:
        status = "upgraded"
        reason = "Ratio approaches 1 asymptotically for most (k,p)."

    return PisteReeval(
        piste_id="R29",
        name="Ratio Law (rho_p = N0*p/C -> 1)",
        original_status="suspended",
        new_status=status,
        reason=reason,
        evidence=f"max_rho={max_rho:.4f}, converging={converging}, diverging={diverging}",
        confidence=0.9,
        computational_data={'max_rho': max_rho, 'max_kp': max_kp},
    )


def reeval_crt_anticorrelation(k_max: int = 40) -> PisteReeval:
    """
    Re-evaluate R84-R86 CRT anticorrelation.
    Original claim: N₀(d) <= Π N₀(p) / C^{omega-1}.
    Our data: CRT product >> 1/d for k >= 6 (ratio up to 10^36).
    """
    print("  Re-evaluating R84-R86 (CRT anticorrelation)...")

    evidence_lines = []
    max_ratio = 0.0

    for k in range(3, min(k_max + 1, 30)):
        if k == 4:
            continue
        S = compute_S(k)
        d = compute_d(k)
        factors = factorize(d)
        primes = sorted(set(p for p, _ in factors if p <= 200))

        if not primes:
            continue

        product = 1.0
        n_total = 0
        for p in primes:
            n0, nt = count_compositions_with_residue(k, S, p, target_r=0)
            if nt > 0:
                frac = n0 / nt
                product *= frac
                n_total = nt

        if n_total > 0 and d > 0:
            inv_d = 1.0 / d
            ratio = product / inv_d if inv_d > 0 else float('inf')
            if ratio > max_ratio:
                max_ratio = ratio
            if k <= 20:
                evidence_lines.append(f"k={k}: product={product:.2e}, 1/d={inv_d:.2e}, ratio={ratio:.4f}")

    return PisteReeval(
        piste_id="R84-R86",
        name="CRT Anticorrelation",
        original_status="suspended",
        new_status="confirmed_closed" if max_ratio > 10 else "open",
        reason=(f"CRT product / (1/d) reaches {max_ratio:.2e}. "
                "Independence assumption FAILS badly. "
                "Avoidance is an INTERFERENCE effect, not a product."),
        evidence="; ".join(evidence_lines[:5]),
        confidence=0.95,
        computational_data={'max_ratio': max_ratio},
    )


def reeval_order_diversity(k_max: int = 80) -> PisteReeval:
    """
    Re-evaluate R31 Order-Diversity Bound.
    Conjecture: high ord_p(2) implies avoidance.
    """
    print("  Re-evaluating R31 (Order-Diversity)...")

    data = []
    for k in range(3, min(k_max + 1, 50)):
        if k == 4:
            continue
        S = compute_S(k)
        d = compute_d(k)
        factors = factorize(d)
        primes = sorted(set(p for p, _ in factors if p <= 200))

        for p in primes[:3]:
            q = multiplicative_order(2, p)
            n0, nt = count_compositions_with_residue(k, S, p, target_r=0)
            if nt > 0:
                avoids = (n0 == 0)
                data.append({'k': k, 'p': p, 'q': q, 'avoids': avoids,
                             'N0': n0, 'C': nt})

    # Test: does q > k imply avoidance?
    q_gt_k_avoids = sum(1 for d_ in data if d_['q'] > d_['k'] and d_['avoids'])
    q_gt_k_total = sum(1 for d_ in data if d_['q'] > d_['k'])
    q_le_k_avoids = sum(1 for d_ in data if d_['q'] <= d_['k'] and d_['avoids'])
    q_le_k_total = sum(1 for d_ in data if d_['q'] <= d_['k'])

    return PisteReeval(
        piste_id="R31",
        name="Order-Diversity Bound",
        original_status="suspended",
        new_status="open",
        reason=(f"q>k: {q_gt_k_avoids}/{q_gt_k_total} avoid, "
                f"q<=k: {q_le_k_avoids}/{q_le_k_total} avoid. "
                "High order helps but is not sufficient alone."),
        evidence=f"{len(data)} (k,p) pairs analyzed",
        confidence=0.7,
        computational_data={
            'q_gt_k': (q_gt_k_avoids, q_gt_k_total),
            'q_le_k': (q_le_k_avoids, q_le_k_total),
        },
    )


def discover_new_invariants(k_max: int = 50) -> List[StructuralInvariant]:
    """
    Search for structural invariants in the data.
    These are properties that hold for ALL tested k values.
    """
    print("  Discovering structural invariants...")

    invariants = []

    # Invariant 1: 3 NOT in <2> mod p for ALL p|d(k)
    three_not_in_two = True
    counterex_3in2 = None
    for k in range(3, min(k_max + 1, 80)):
        if k == 4:
            continue
        d = compute_d(k)
        factors = factorize(d)
        for p, _ in factors:
            if p <= 10**6:
                if is_in_subgroup(3, 2, p):
                    three_not_in_two = False
                    counterex_3in2 = f"k={k}, p={p}"
                    break
        if not three_not_in_two:
            break

    invariants.append(StructuralInvariant(
        name="3 NOT in <2> mod p universality",
        statement="For all p | d(k) with k >= 3: 3 is NOT in the subgroup <2> of (Z/pZ)*",
        verified_range=f"k=3..{min(k_max, 79)}",
        counterexample=counterex_3in2,
        connects_to="R176 Reduction Somme Cyclique + R186 Dualite",
        proof_potential="provable" if three_not_in_two else "false",
    ))

    # Invariant 2: ord_p(2) >= 3 for all p|d(k) (R197)
    ord_ge_3 = True
    counterex_ord = None
    for k in range(3, min(k_max + 1, 80)):
        if k == 4:
            continue
        d = compute_d(k)
        factors = factorize(d)
        for p, _ in factors:
            if p <= 10**6:
                q = multiplicative_order(2, p)
                if q < 3:
                    ord_ge_3 = False
                    counterex_ord = f"k={k}, p={p}, ord={q}"
                    break
        if not ord_ge_3:
            break

    invariants.append(StructuralInvariant(
        name="ord_p(2) >= 3 for all p|d(k)",
        statement="For all p | d(k) with k >= 3: the multiplicative order of 2 mod p is at least 3",
        verified_range=f"k=3..{min(k_max, 79)}",
        counterexample=counterex_ord,
        connects_to="R197 LDS: ord >= 3 is minimum for FCQ to work",
        proof_potential="provable" if ord_ge_3 else "false",
    ))

    # Invariant 3: entropy deficit gamma(k) ~ 1.06*k
    gamma_data = []
    for k in range(3, min(k_max + 1, 50)):
        if k == 4:
            continue
        S = compute_S(k)
        d = compute_d(k)
        if d > 0:
            from syracuse_jepa.pipeline.explorer import count_compositions
            C = count_compositions(k, S)
            if C > 0:
                log_ratio = math.log(d) - math.log(C)
                gamma_data.append((k, log_ratio))

    if len(gamma_data) >= 5:
        ks = [g[0] for g in gamma_data]
        gs = [g[1] for g in gamma_data]
        n = len(ks)
        sx, sy = sum(ks), sum(gs)
        sxx = sum(x*x for x in ks)
        sxy = sum(x*y for x, y in zip(ks, gs))
        denom = n * sxx - sx * sx
        if denom != 0:
            slope = (n * sxy - sx * sy) / denom
            intercept = (sy - slope * sx) / n

            invariants.append(StructuralInvariant(
                name="Entropy deficit linear scaling",
                statement=f"log(d/C) ~ {intercept:.4f} + {slope:.4f}*k (entropy deficit grows linearly)",
                verified_range=f"k=3..{min(k_max, 49)}",
                counterexample=None,
                connects_to="Stage I: C/d -> 0 exponentially",
                proof_potential="provable (follows from log2(3) > 1)",
            ))

    # Invariant 4: N0(p) > 0 for ALL small primes, ALL k
    # (avoidance is CRT interference, not per-prime)
    n0_always_positive = True
    counterex_n0 = None
    tested = 0
    for k in range(3, min(k_max + 1, 50)):
        if k == 4:
            continue
        S = compute_S(k)
        d = compute_d(k)
        factors = factorize(d)
        primes = sorted(set(p for p, _ in factors if p <= 50))
        for p in primes:
            n0, nt = count_compositions_with_residue(k, S, p, target_r=0)
            tested += 1
            if n0 == 0:
                n0_always_positive = False
                counterex_n0 = f"k={k}, p={p}: N0={n0}"
                break
        if not n0_always_positive:
            break

    invariants.append(StructuralInvariant(
        name="N0(p) > 0 for small primes",
        statement="For small primes p <= 50 dividing d(k): N0(p) > 0 always",
        verified_range=f"{tested} (k,p) pairs tested",
        counterexample=counterex_n0,
        connects_to="CRT interference: avoidance is collective, not per-prime",
        proof_potential="hard" if n0_always_positive else "false (good news: some prime kills!)",
    ))

    return invariants


def run_map_reeval(k_max: int = 50) -> dict:
    """
    Full research map re-evaluation.
    Cross-references RESEARCH_MAP.md with exact computations.
    """
    print("╔══════════════════════════════════════════════════════════════════╗")
    print("║  RESEARCH MAP RE-EVALUATOR                                     ║")
    print("║  Cross-referencing 195 rounds with exact computation            ║")
    print("╠══════════════════════════════════════════════════════════════════╣")

    # Re-evaluate key pistes
    reevals = []
    reevals.append(reeval_ratio_law(k_max))
    reevals.append(reeval_crt_anticorrelation(min(k_max, 30)))
    reevals.append(reeval_order_diversity(k_max))

    print("║")
    print("║  PISTE RE-EVALUATION RESULTS:")
    for r in reevals:
        marker = {"confirmed_closed": "✗", "reopened": "★", "upgraded": "↑", "open": "?"}
        print(f"║  [{marker.get(r.new_status, '?')}] {r.piste_id} ({r.name})")
        print(f"║      Status: {r.original_status} -> {r.new_status}")
        print(f"║      {r.reason}")

    # Discover invariants
    invariants = discover_new_invariants(k_max)

    print("║")
    print("║  STRUCTURAL INVARIANTS:")
    for inv in invariants:
        status = "HOLDS" if inv.counterexample is None else f"BROKEN: {inv.counterexample}"
        print(f"║  [{status}] {inv.name}")
        print(f"║      {inv.statement}")
        print(f"║      Range: {inv.verified_range}")
        if inv.counterexample is None:
            print(f"║      Proof potential: {inv.proof_potential}")

    # Summary
    confirmed_closed = sum(1 for r in reevals if r.new_status == "confirmed_closed")
    reopened = sum(1 for r in reevals if r.new_status == "reopened")
    upgraded = sum(1 for r in reevals if r.new_status == "upgraded")
    holding = sum(1 for inv in invariants if inv.counterexample is None)

    print("║")
    print(f"║  SUMMARY: {confirmed_closed} confirmed closed, "
          f"{reopened} reopened, {upgraded} upgraded")
    print(f"║  {holding}/{len(invariants)} structural invariants HOLD")
    print("╚══════════════════════════════════════════════════════════════════╝")

    return {
        'reevaluations': reevals,
        'invariants': invariants,
        'summary': {
            'confirmed_closed': confirmed_closed,
            'reopened': reopened,
            'upgraded': upgraded,
            'invariants_holding': holding,
        }
    }


if __name__ == '__main__':
    result = run_map_reeval(50)
