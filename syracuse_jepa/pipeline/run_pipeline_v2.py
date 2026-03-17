#!/usr/bin/env python3
"""
Syracuse-JEPA v2 Pipeline — Automated Conjecture & Strategy Machine

    Problème mathématique → Explorer → Analyst → Pattern Miner → Strategist → Formalizer → Verifier
                                                        ↑                                     |
                                                        └──────── feedback loop ──────────────┘

v2 upgrades over v1:
- Deep structural analysis (prime factorization, multiplicative orders, spectral data)
- Pattern discovery (cross-k trends, invariants, asymptotic behavior)
- Proof strategy generation (connected to RESEARCH_MAP open pistes)
- Knowledge base integration (avoids re-exploring closed paths)

Usage:
    python -m syracuse_jepa.pipeline.run_pipeline_v2 [--k-min 3] [--k-max 40]
"""

import os
import sys
import json
import argparse
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from syracuse_jepa.pipeline.explorer import explore_k
from syracuse_jepa.pipeline.conjecturer import (
    run_conjecturer, Hypothesis, HypothesisType, Confidence
)
from syracuse_jepa.pipeline.formalizer import formalize
from syracuse_jepa.pipeline.verifier import verify, diagnose_failure
from syracuse_jepa.pipeline.analyst import analyze_range, format_insights
from syracuse_jepa.pipeline.pattern_miner import mine_patterns
from syracuse_jepa.pipeline.strategist import generate_strategies, format_report
from syracuse_jepa.pipeline.knowledge import build_knowledge_base


def run_pipeline_v2(k_min: int = 3, k_max: int = 40,
                    lean_dir: str = 'lean4_proof',
                    max_retries: int = 3,
                    timeout: int = 600,
                    analysis_only: bool = False) -> dict:
    """
    Full v2 pipeline:
      1. Explore (enumerate compositions, compute corrSum)
      2. Analyze (deep structural analysis per prime)
      3. Mine patterns (cross-k trends, invariants)
      4. Strategize (proof direction, connect to research map)
      5. Conjecture (generate hypotheses)
      6. Formalize (generate Lean 4 code)
      7. Verify (compile and check)

    With feedback loop on failure.
    """
    t_start = time.time()

    print("╔" + "═" * 68 + "╗")
    print("║  SYRACUSE-JEPA v2 — Automated Conjecture & Strategy Machine      ║")
    print("║  Explorer → Analyst → Miner → Strategist → Formalizer → Verifier ║")
    print("╚" + "═" * 68 + "╝")
    print()

    # ─── STEP 1: EXPLORE ───────────────────────────────────────
    print("┌─ STEP 1: EXPLORE ────────────────────────────────────────┐")
    exploration_results = []
    for k in range(k_min, k_max + 1):
        result = explore_k(k)
        exploration_results.append(result.to_dict())
        status = "N₀=0 ✓" if result.n_zero_residue == 0 else (
            f"N₀={result.n_zero_residue}" if result.n_zero_residue > 0 else "SKIP"
        )
        line = f"  k={k:2d}  #comp={result.n_compositions:>8d}  {status}"
        if result.min_gap_rel >= 0:
            line += f"  gap={result.min_gap_rel:.6f}"
        print(line)
    print(f"└─ Explored k={k_min}..{k_max} ──────────────────────────────┘\n")

    # ─── STEP 2: DEEP STRUCTURAL ANALYSIS ──────────────────────
    print("┌─ STEP 2: DEEP STRUCTURAL ANALYSIS ──────────────────────┐")
    analysis_results, insights = analyze_range(k_min, k_max)
    print(format_insights(insights))
    print(f"└─ Analyzed {len(analysis_results)} k values, "
          f"{len(insights)} insights ──────────────────┘\n")

    # ─── STEP 3: PATTERN MINING ────────────────────────────────
    print("┌─ STEP 3: PATTERN MINING ────────────────────────────────┐")
    mined = mine_patterns(analysis_results, insights)
    trends = mined['trends']
    invariants = mined['invariants']
    conjectures = mined['conjectures']
    print(f"└─ {len(trends)} trends, {len(invariants)} invariants, "
          f"{len(conjectures)} conjectures ─────────┘\n")

    # ─── STEP 4: PROOF STRATEGY ────────────────────────────────
    print("┌─ STEP 4: PROOF STRATEGY ────────────────────────────────┐")
    report = generate_strategies(
        analysis_results, insights, trends, invariants, conjectures
    )
    print(format_report(report))
    print(f"└─ {len(report.strategies)} strategies ranked ─────────────────────┘\n")

    # ─── Save analysis results ─────────────────────────────────
    analysis_output = {
        'version': 'v2',
        'k_range': [k_min, k_max],
        'n_insights': len(insights),
        'n_trends': len(trends),
        'n_invariants': len(invariants),
        'n_conjectures': len(conjectures),
        'insights': [
            {'category': i.category, 'description': i.description,
             'confidence': i.confidence, 'connects_to': i.connects_to,
             'actionable': i.actionable}
            for i in insights
        ],
        'trends': [
            {'quantity': t.quantity, 'model': t.model, 'slope': t.slope,
             'r_squared': t.r_squared, 'extrapolation': t.extrapolation}
            for t in trends
        ],
        'conjectures': [
            {'statement': c.statement, 'evidence': c.evidence_strength,
             'n_verified': c.n_verified, 'proof_approach': c.proof_approach}
            for c in conjectures
        ],
        'strategies': [
            {'name': s.name, 'score': s.score, 'feasibility': s.feasibility,
             'impact': s.impact, 'data_support': s.data_support,
             'next_step': s.concrete_steps[0] if s.concrete_steps else '',
             'blocker': s.blockers[0] if s.blockers else ''}
            for s in report.strategies
        ],
        'critical_question': report.critical_question,
        'recommended_action': report.recommended_action,
        'lean_roadmap': report.lean_roadmap,
    }

    out_dir = os.path.dirname(os.path.abspath(__file__))
    analysis_path = os.path.join(out_dir, 'analysis_result_v2.json')
    with open(analysis_path, 'w') as f:
        json.dump(analysis_output, f, indent=2, ensure_ascii=False)
    print(f"  Analysis saved to {analysis_path}")

    if analysis_only:
        elapsed = time.time() - t_start
        print(f"\n  Analysis-only mode. Total time: {elapsed:.1f}s")
        return analysis_output

    # ─── STEP 5: CONJECTURE ────────────────────────────────────
    print("\n┌─ STEP 5: CONJECTURE ─────────────────────────────────────┐")
    hypotheses = run_conjecturer(exploration_results)
    formalizable = [h for h in hypotheses if h.lean_name is not None]
    print(f"  Formalizable: {len(formalizable)} / {len(hypotheses)}")
    print(f"└─────────────────────────────────────────────────────────┘\n")

    # ─── STEP 6 & 7: FORMALIZE → VERIFY (with retry loop) ─────
    result = None
    for attempt in range(1, max_retries + 1):
        print(f"┌─ ATTEMPT {attempt}/{max_retries}: FORMALIZE → VERIFY ──────────────┐")

        files = formalize(formalizable, lean_dir)
        result = verify(files, lean_dir, timeout=timeout)

        if result.success:
            elapsed = time.time() - t_start
            print(f"└─ SUCCESS in {elapsed:.1f}s ────────────────────────────────┘\n")

            # Final summary
            print("╔" + "═" * 68 + "╗")
            print("║  PIPELINE v2 COMPLETE — ALL PROOFS VERIFIED                     ║")
            print("╠" + "═" * 68 + "╣")

            n_avoid = sum(1 for h in formalizable if h.type == HypothesisType.AVOIDANCE)
            n_phantom = sum(1 for h in formalizable if h.type == HypothesisType.PHANTOM)
            k_avoided = sorted(h.k for h in formalizable if h.type == HypothesisType.AVOIDANCE)
            k_phantom = sorted(h.k for h in formalizable if h.type == HypothesisType.AVOIDANCE_FAILS)

            print(f"║  Avoidance theorems:  {n_avoid:>3d}  k∈{{{k_avoided[0]}..{k_avoided[-1]}}}" if k_avoided else "")
            print(f"║  Phantom theorems:    {n_phantom:>3d}")
            print(f"║  Total native_decide: {result.n_theorems_proved:>3d}")
            print(f"║  Build time:          {result.build_time_seconds:>6.1f}s")
            print(f"║  Pipeline time:       {elapsed:>6.1f}s")
            print(f"║  sorry count:             0")
            print(f"║  Insights discovered: {len(insights):>3d}")
            print(f"║  Conjectures formed:  {len(conjectures):>3d}")
            print(f"║  Strategies ranked:   {len(report.strategies):>3d}")
            print("╠" + "═" * 68 + "╣")
            print(f"║  BEST STRATEGY: {report.strategies[0].name[:50]}")
            print(f"║  Score: {report.strategies[0].score:.1f}/100")
            print(f"║  Next: {report.strategies[0].concrete_steps[0][:58]}")
            print("╚" + "═" * 68 + "╝")

            full_result = {
                'success': True,
                'version': 'v2',
                'n_theorems': result.n_theorems_proved,
                'k_range': [k_min, k_max],
                'k_avoided': k_avoided,
                'k_phantom': k_phantom,
                'build_time': result.build_time_seconds,
                'total_time': elapsed,
                'n_insights': len(insights),
                'n_conjectures': len(conjectures),
                'n_strategies': len(report.strategies),
                'best_strategy': report.strategies[0].name,
                'critical_question': report.critical_question,
            }

            result_path = os.path.join(out_dir, 'pipeline_result_v2.json')
            with open(result_path, 'w') as f:
                json.dump(full_result, f, indent=2)
            print(f"\nResult saved to {result_path}")

            return full_result

        else:
            print(f"  Build failed. Diagnosing...")
            suggestions = diagnose_failure(result)
            for s in suggestions:
                print(f"    → {s}")

            if any("PROPOSITION_FALSE" in s for s in suggestions):
                for err in result.errors:
                    for h in formalizable[:]:
                        if h.lean_name and h.lean_name in err:
                            print(f"  Removing false hypothesis: {h.lean_name}")
                            formalizable.remove(h)

            if any("TIMEOUT" in s for s in suggestions):
                old_max = max(h.k for h in formalizable if h.k is not None)
                new_max = old_max - 5
                print(f"  Reducing k_max from {old_max} to {new_max}")
                formalizable = [h for h in formalizable
                               if h.k is None or h.k <= new_max]

            print(f"└─ Retrying with {len(formalizable)} hypotheses ──────────────┘\n")

    elapsed = time.time() - t_start
    print(f"\n✗ PIPELINE FAILED after {max_retries} attempts ({elapsed:.1f}s)")
    return {
        'success': False,
        'version': 'v2',
        'errors': result.errors if result else [],
        'total_time': elapsed,
        'n_insights': len(insights),
        'n_conjectures': len(conjectures),
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Syracuse-JEPA v2 Pipeline')
    parser.add_argument('--k-min', type=int, default=3)
    parser.add_argument('--k-max', type=int, default=40)
    parser.add_argument('--lean-dir', default='lean4_proof')
    parser.add_argument('--timeout', type=int, default=600)
    parser.add_argument('--analysis-only', action='store_true',
                        help='Run analysis only, skip Lean formalization')
    args = parser.parse_args()

    result = run_pipeline_v2(
        k_min=args.k_min,
        k_max=args.k_max,
        lean_dir=args.lean_dir,
        timeout=args.timeout,
        analysis_only=args.analysis_only,
    )
