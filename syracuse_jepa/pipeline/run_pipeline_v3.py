#!/usr/bin/env python3
"""
Syracuse-JEPA v3 Pipeline — Full Discovery & Proof Machine

    Explorer → Analyst → Pattern Miner → Strategist
                                            ↓
    Spectral → Prover → Discovery → Genius → Red Team → Formalizer → Verifier
                            ↑                                           |
                            └──────────── feedback loop ───────────────┘

v3 upgrades over v2:
- Spectral Engine: DP-based N₀(p) for k up to 200+ via CRT
- Prover: Steiner n_min argument extends to k ≤ ~120
- Discovery: Jardinier (root-cause) + Innovateur (new quantities)
- Genius: Proof gaps, hard cases, asymptotic oracle, contradictions
- Red Team: 6 audit suites, cross-validation, falsification

Usage:
    python -m syracuse_jepa.pipeline.run_pipeline_v3 [--k-min 3] [--k-max 40]
    python -m syracuse_jepa.pipeline.run_pipeline_v3 --analysis-only
    python -m syracuse_jepa.pipeline.run_pipeline_v3 --full-scan --k-max 200
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
from syracuse_jepa.pipeline.spectral import extended_avoidance_scan
from syracuse_jepa.pipeline.prover import extended_proof_scan, generate_proof_certificate
from syracuse_jepa.pipeline.discovery import run_discovery
from syracuse_jepa.pipeline.genius import run_genius
from syracuse_jepa.pipeline.redteam import run_full_audit


def run_pipeline_v3(k_min: int = 3, k_max: int = 40,
                    lean_dir: str = 'lean4_proof',
                    max_retries: int = 3,
                    timeout: int = 600,
                    analysis_only: bool = False,
                    full_scan: bool = False) -> dict:
    """
    Full v3 pipeline — 10 stages:
      1. Explore (enumerate, corrSum)
      2. Analyze (deep structural per prime)
      3. Mine patterns (cross-k trends, invariants)
      4. Strategize (proof directions, research map)
      5. Spectral (DP-based avoidance for large k)
      6. Prover (Steiner n_min extension)
      7. Discovery (root-cause + new quantities)
      8. Genius (proof gaps, hard cases, oracle, contradictions)
      9. Red Team (cross-validation, falsification)
     10. Formalize + Verify (Lean 4)
    """
    t_start = time.time()

    print("╔" + "═" * 68 + "╗")
    print("║  SYRACUSE-JEPA v3 — Full Discovery & Proof Machine              ║")
    print("║  10 stages: Explore→Analyze→Mine→Strategy→Spectral→             ║")
    print("║             Prove→Discover→Genius→RedTeam→Verify                ║")
    print("╚" + "═" * 68 + "╝")
    print()

    # ─── STAGE 1: EXPLORE ──────────────────────────────────────
    print("┌─ STAGE 1/10: EXPLORE ─────────────────────────────────────┐")
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

    # ─── STAGE 2: DEEP STRUCTURAL ANALYSIS ────────────────────
    print("┌─ STAGE 2/10: DEEP STRUCTURAL ANALYSIS ────────────────────┐")
    analysis_results, insights = analyze_range(k_min, k_max)
    print(format_insights(insights))
    print(f"└─ {len(analysis_results)} k values, {len(insights)} insights ─────────┘\n")

    # ─── STAGE 3: PATTERN MINING ──────────────────────────────
    print("┌─ STAGE 3/10: PATTERN MINING ──────────────────────────────┐")
    mined = mine_patterns(analysis_results, insights)
    trends = mined['trends']
    invariants = mined['invariants']
    conjectures = mined['conjectures']
    print(f"└─ {len(trends)} trends, {len(invariants)} invariants, "
          f"{len(conjectures)} conjectures ─────────┘\n")

    # ─── STAGE 4: PROOF STRATEGY ──────────────────────────────
    print("┌─ STAGE 4/10: PROOF STRATEGY ──────────────────────────────┐")
    report = generate_strategies(
        analysis_results, insights, trends, invariants, conjectures
    )
    print(format_report(report))
    print(f"└─ {len(report.strategies)} strategies ranked ──────────────────────┘\n")

    # ─── STAGE 5: SPECTRAL ENGINE ─────────────────────────────
    spectral_k_max = 200 if full_scan else min(k_max + 10, 60)
    print(f"┌─ STAGE 5/10: SPECTRAL ENGINE (k≤{spectral_k_max}) ──────────────┐")
    spectral_results = extended_avoidance_scan(k_min, spectral_k_max, max_prime=500)
    n_spectral_proved = sum(1 for r in spectral_results if r.get('proved'))
    print(f"└─ {n_spectral_proved}/{len(spectral_results)} proved via CRT ──────────┘\n")

    # ─── STAGE 6: PROVER (Steiner extension) ──────────────────
    prover_k_max = 200 if full_scan else 120
    print(f"┌─ STAGE 6/10: PROVER — Steiner n_min (k≤{prover_k_max}) ─────────┐")
    prover_results = extended_proof_scan(k_min, prover_k_max)
    n_steiner = sum(1 for r in prover_results
                    if r.get('proved_N0_zero') and r.get('method', '').startswith('steiner'))
    print(f"└─ {n_steiner} proved via Steiner ──────────────────────────┘\n")

    # ─── STAGE 7: DISCOVERY ENGINE ────────────────────────────
    print("┌─ STAGE 7/10: DISCOVERY — Jardinier + Innovateur ──────────┐")
    roots, innovations = run_discovery(k_max)
    print(f"└─ {len(roots)} root causes, {len(innovations)} new quantities ─────┘\n")

    # ─── STAGE 8: GENIUS ENGINE ───────────────────────────────
    print("┌─ STAGE 8/10: GENIUS — Proof Gaps + Hard Cases + Oracle ───┐")
    genius_results = run_genius(k_max)
    n_gaps = len(genius_results['gaps'])
    n_hard = len(genius_results['hard_cases'])
    n_preds = len(genius_results['predictions'])
    n_contras = len(genius_results['contradictions'])
    n_proved_contras = sum(1 for c in genius_results['contradictions'] if c.is_proved_impossible)
    print(f"└─ {n_gaps} gaps, {n_hard} hard cases, {n_preds} predictions, "
          f"{n_proved_contras}/{n_contras} contradictions proved ─┘\n")

    # ─── STAGE 9: RED TEAM AUDIT ──────────────────────────────
    print("┌─ STAGE 9/10: RED TEAM AUDIT ──────────────────────────────┐")
    audit_results = run_full_audit()
    n_pass = sum(1 for r in audit_results if r.status == "PASS")
    n_fail = sum(1 for r in audit_results if r.status == "FAIL")
    n_warn = sum(1 for r in audit_results if r.status == "WARNING")
    print(f"└─ {n_pass} PASS, {n_fail} FAIL, {n_warn} WARNING ─────────────────┘\n")

    if n_fail > 0:
        print("  ⚠ RED TEAM FAILURES DETECTED — pipeline integrity compromised")
        for r in audit_results:
            if r.status == "FAIL":
                print(f"    FAIL: {r.check_name}: {r.details[:60]}")
        print()

    # ─── Save full analysis ───────────────────────────────────
    out_dir = os.path.dirname(os.path.abspath(__file__))
    analysis_output = {
        'version': 'v3',
        'k_range': [k_min, k_max],
        'stages_completed': 9,
        'exploration': {
            'n_k_values': len(exploration_results),
        },
        'analysis': {
            'n_insights': len(insights),
            'insights': [
                {'category': i.category, 'description': i.description,
                 'confidence': i.confidence, 'connects_to': i.connects_to}
                for i in insights
            ],
        },
        'patterns': {
            'n_trends': len(trends),
            'n_invariants': len(invariants),
            'n_conjectures': len(conjectures),
        },
        'strategies': {
            'n_strategies': len(report.strategies),
            'top_strategy': report.strategies[0].name if report.strategies else None,
            'top_score': report.strategies[0].score if report.strategies else 0,
            'critical_question': report.critical_question,
            'recommended_action': report.recommended_action,
        },
        'spectral': {
            'k_max_scanned': spectral_k_max,
            'n_proved': n_spectral_proved,
            'n_total': len(spectral_results),
        },
        'prover': {
            'k_max_scanned': prover_k_max,
            'n_steiner_proved': n_steiner,
        },
        'discovery': {
            'n_root_causes': len(roots),
            'n_innovations': len(innovations),
            'innovations': [inn.name for inn in innovations],
        },
        'genius': {
            'n_proof_gaps': n_gaps,
            'n_hard_cases': n_hard,
            'hardest_k': genius_results['hard_cases'][0].k if genius_results['hard_cases'] else None,
            'hardest_score': genius_results['hard_cases'][0].difficulty_score if genius_results['hard_cases'] else 0,
            'n_predictions': n_preds,
            'n_contradictions': n_contras,
            'n_proved_contradictions': n_proved_contras,
        },
        'redteam': {
            'n_pass': n_pass,
            'n_fail': n_fail,
            'n_warning': n_warn,
        },
    }

    analysis_path = os.path.join(out_dir, 'analysis_result_v3.json')
    with open(analysis_path, 'w') as f:
        json.dump(analysis_output, f, indent=2, ensure_ascii=False)
    print(f"  Analysis saved to {analysis_path}")

    if analysis_only:
        elapsed = time.time() - t_start
        _print_summary(analysis_output, elapsed, None, report, genius_results)
        return analysis_output

    # ─── STAGE 10: FORMALIZE + VERIFY ─────────────────────────
    print("\n┌─ STAGE 10/10: FORMALIZE → VERIFY ────────────────────────┐")
    hypotheses = run_conjecturer(exploration_results)
    formalizable = [h for h in hypotheses if h.lean_name is not None]
    print(f"  Formalizable: {len(formalizable)} / {len(hypotheses)}")

    result = None
    for attempt in range(1, max_retries + 1):
        print(f"  Attempt {attempt}/{max_retries}...")
        files = formalize(formalizable, lean_dir)
        result = verify(files, lean_dir, timeout=timeout)

        if result.success:
            elapsed = time.time() - t_start
            _print_summary(analysis_output, elapsed, result, report, genius_results)

            full_result = {**analysis_output,
                          'success': True,
                          'n_theorems': result.n_theorems_proved,
                          'build_time': result.build_time_seconds,
                          'total_time': elapsed}

            result_path = os.path.join(out_dir, 'pipeline_result_v3.json')
            with open(result_path, 'w') as f:
                json.dump(full_result, f, indent=2)
            print(f"\nResult saved to {result_path}")
            return full_result

        # Retry logic
        suggestions = diagnose_failure(result)
        for s in suggestions:
            print(f"    → {s}")

        if any("PROPOSITION_FALSE" in s for s in suggestions):
            for err in result.errors:
                for h in formalizable[:]:
                    if h.lean_name and h.lean_name in err:
                        print(f"  Removing: {h.lean_name}")
                        formalizable.remove(h)

        if any("TIMEOUT" in s for s in suggestions):
            old_max = max(h.k for h in formalizable if h.k is not None)
            new_max = old_max - 5
            formalizable = [h for h in formalizable if h.k is None or h.k <= new_max]

    print(f"└─ VERIFY FAILED after {max_retries} attempts ─────────────┘\n")

    elapsed = time.time() - t_start
    return {**analysis_output, 'success': False, 'total_time': elapsed}


def _print_summary(analysis: dict, elapsed: float, verify_result, report, genius):
    """Print the final summary box."""
    print()
    print("╔" + "═" * 68 + "╗")
    print("║  SYRACUSE-JEPA v3 — PIPELINE COMPLETE                          ║")
    print("╠" + "═" * 68 + "╣")

    if verify_result and verify_result.success:
        print(f"║  Lean theorems proved: {verify_result.n_theorems_proved:>5d}")
        print(f"║  Build time:           {verify_result.build_time_seconds:>8.1f}s")

    sp = analysis.get('spectral', {})
    pr = analysis.get('prover', {})
    ge = analysis.get('genius', {})
    rd = analysis.get('redteam', {})

    print(f"║  Spectral CRT proofs:  {sp.get('n_proved', 0):>5d} / {sp.get('n_total', 0)}")
    print(f"║  Steiner proofs:       {pr.get('n_steiner_proved', 0):>5d}")
    print(f"║  Insights discovered:  {analysis.get('analysis', {}).get('n_insights', 0):>5d}")
    print(f"║  Conjectures formed:   {analysis.get('patterns', {}).get('n_conjectures', 0):>5d}")
    print(f"║  Proof gaps identified:{ge.get('n_proof_gaps', 0):>5d}")
    print(f"║  Contradictions proved:{ge.get('n_proved_contradictions', 0):>5d} / {ge.get('n_contradictions', 0)}")
    print(f"║  Red Team:             {rd.get('n_pass', 0)} PASS, {rd.get('n_fail', 0)} FAIL")
    print(f"║  Pipeline time:        {elapsed:>8.1f}s")

    print("╠" + "═" * 68 + "╣")

    if report and report.strategies:
        s = report.strategies[0]
        print(f"║  BEST STRATEGY: {s.name[:52]}")
        print(f"║  Score: {s.score:.1f}/100")
        if s.concrete_steps:
            print(f"║  Next: {s.concrete_steps[0][:58]}")

    if genius and genius.get('hard_cases'):
        hc = genius['hard_cases'][0]
        print(f"║  HARDEST k: {hc.k} (difficulty {hc.difficulty_score}/10)")
        print(f"║    → {hc.vulnerability[:58]}")

    if report:
        print(f"║  CRITICAL Q: {report.critical_question[:54]}")

    print("╚" + "═" * 68 + "╝")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Syracuse-JEPA v3 Pipeline')
    parser.add_argument('--k-min', type=int, default=3)
    parser.add_argument('--k-max', type=int, default=40)
    parser.add_argument('--lean-dir', default='lean4_proof')
    parser.add_argument('--timeout', type=int, default=600)
    parser.add_argument('--analysis-only', action='store_true',
                        help='Run stages 1-9 only, skip Lean verification')
    parser.add_argument('--full-scan', action='store_true',
                        help='Scan k up to 200 for spectral/prover stages')
    args = parser.parse_args()

    run_pipeline_v3(
        k_min=args.k_min,
        k_max=args.k_max,
        lean_dir=args.lean_dir,
        timeout=args.timeout,
        analysis_only=args.analysis_only,
        full_scan=args.full_scan,
    )
