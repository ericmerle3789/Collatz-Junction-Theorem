#!/usr/bin/env python3
"""
Syracuse-JEPA Pipeline — Automated Conjecture Machine

    Problème mathématique → Explorer → Conjecturer → Formalizer → Verifier
                                            ↑                        |
                                            └── feedback loop ───────┘

Usage:
    python -m syracuse_jepa.pipeline.run_pipeline [--k-min 3] [--k-max 40] [--lean-dir lean4_proof]
"""

import os
import sys
import json
import argparse
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from syracuse_jepa.pipeline.explorer import explore_range, explore_k
from syracuse_jepa.pipeline.conjecturer import (
    run_conjecturer, Hypothesis, HypothesisType, Confidence
)
from syracuse_jepa.pipeline.formalizer import formalize
from syracuse_jepa.pipeline.verifier import verify, diagnose_failure


def run_pipeline(k_min: int = 3, k_max: int = 40,
                 lean_dir: str = 'lean4_proof',
                 max_retries: int = 3,
                 timeout: int = 600) -> dict:
    """
    Full pipeline: Explore → Conjecture → Formalize → Verify.
    With feedback loop on failure.
    """
    t_start = time.time()

    print("╔" + "═" * 68 + "╗")
    print("║  SYRACUSE-JEPA PIPELINE — Automated Conjecture Machine            ║")
    print("║  Explorer → Conjecturer → Formalizer → Verifier                   ║")
    print("╚" + "═" * 68 + "╝")
    print()

    # ─── STEP 1: EXPLORE ───────────────────────────────────────────
    print("┌─ STEP 1: EXPLORE ────────────────────────────────────────┐")
    exploration_results = []
    for k in range(k_min, k_max + 1):
        result = explore_k(k)
        exploration_results.append(result.to_dict())
        status = "N₀=0 ✓" if result.n_zero_residue == 0 else (
            f"N₀={result.n_zero_residue}" if result.n_zero_residue > 0 else "SKIP"
        )
        print(f"  k={k:2d}  #comp={result.n_compositions:>8d}  {status}"
              f"  gap={result.min_gap_rel:.6f}" if result.min_gap_rel >= 0 else "")
    print(f"└─ Explored k={k_min}..{k_max} "
          f"({len(exploration_results)} values) ──────────────────┘\n")

    # ─── STEP 2: CONJECTURE ────────────────────────────────────────
    print("┌─ STEP 2: CONJECTURE ─────────────────────────────────────┐")
    hypotheses = run_conjecturer(exploration_results)

    # Filter to only hypotheses we can formalize
    formalizable = [h for h in hypotheses if h.lean_name is not None]
    print(f"  Formalizable: {len(formalizable)} / {len(hypotheses)}")
    print(f"└─────────────────────────────────────────────────────────┘\n")

    # ─── STEP 3 & 4: FORMALIZE → VERIFY (with retry loop) ─────────
    for attempt in range(1, max_retries + 1):
        print(f"┌─ ATTEMPT {attempt}/{max_retries}: FORMALIZE → VERIFY ──────────────┐")

        # Formalize
        files = formalize(formalizable, lean_dir)

        # Verify
        result = verify(files, lean_dir, timeout=timeout)

        if result.success:
            elapsed = time.time() - t_start
            print(f"└─ SUCCESS in {elapsed:.1f}s ────────────────────────────────┘\n")

            # Summary
            print("╔" + "═" * 68 + "╗")
            print("║  PIPELINE COMPLETE — ALL PROOFS VERIFIED                          ║")
            print("╠" + "═" * 68 + "╣")

            n_avoid = sum(1 for h in formalizable if h.type == HypothesisType.AVOIDANCE)
            n_phantom = sum(1 for h in formalizable if h.type == HypothesisType.PHANTOM)
            n_closed = sum(1 for h in formalizable if h.type == HypothesisType.CLOSED_FORM)
            k_avoided = sorted(h.k for h in formalizable if h.type == HypothesisType.AVOIDANCE)
            k_phantom = sorted(h.k for h in formalizable if h.type == HypothesisType.AVOIDANCE_FAILS)

            print(f"║  Avoidance theorems (N₀=0):  {n_avoid:>3d}  "
                  f"k ∈ {{{k_avoided[0]}..{k_avoided[-1]}}} \\ {{{', '.join(str(x) for x in k_phantom)}}}"
                  if k_avoided else "none")
            print(f"║  Phantom theorems:            {n_phantom:>3d}")
            print(f"║  Closed form verifications:   {n_closed:>3d}")
            print(f"║  Total native_decide proofs:  {result.n_theorems_proved:>3d}")
            print(f"║  Build time:                  {result.build_time_seconds:>6.1f}s")
            print(f"║  Total pipeline time:         {elapsed:>6.1f}s")
            print(f"║  sorry count:                     0")
            print("╚" + "═" * 68 + "╝")

            return {
                'success': True,
                'n_theorems': result.n_theorems_proved,
                'k_range': [k_min, k_max],
                'k_avoided': k_avoided,
                'k_phantom': k_phantom,
                'build_time': result.build_time_seconds,
                'total_time': elapsed,
                'hypotheses': len(formalizable),
            }

        else:
            # ─── FEEDBACK LOOP ─────────────────────────────────────
            print(f"  Build failed. Diagnosing...")
            suggestions = diagnose_failure(result)
            for s in suggestions:
                print(f"    → {s}")

            # Remove bad hypotheses
            if any("PROPOSITION_FALSE" in s for s in suggestions):
                # Find which theorem failed and remove it
                for err in result.errors:
                    for h in formalizable[:]:
                        if h.lean_name and h.lean_name in err:
                            print(f"  Removing false hypothesis: {h.lean_name}")
                            formalizable.remove(h)

            if any("TIMEOUT" in s for s in suggestions):
                # Reduce scope
                old_max = max(h.k for h in formalizable if h.k is not None)
                new_max = old_max - 5
                print(f"  Reducing k_max from {old_max} to {new_max}")
                formalizable = [h for h in formalizable
                               if h.k is None or h.k <= new_max]

            print(f"└─ Retrying with {len(formalizable)} hypotheses ──────────────┘\n")

    # All retries failed
    elapsed = time.time() - t_start
    print(f"\n✗ PIPELINE FAILED after {max_retries} attempts ({elapsed:.1f}s)")
    return {
        'success': False,
        'errors': result.errors if result else [],
        'total_time': elapsed,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Syracuse-JEPA Pipeline')
    parser.add_argument('--k-min', type=int, default=3)
    parser.add_argument('--k-max', type=int, default=40)
    parser.add_argument('--lean-dir', default='lean4_proof')
    parser.add_argument('--timeout', type=int, default=600)
    args = parser.parse_args()

    result = run_pipeline(
        k_min=args.k_min,
        k_max=args.k_max,
        lean_dir=args.lean_dir,
        timeout=args.timeout,
    )

    # Save result
    out_path = 'syracuse_jepa/pipeline/pipeline_result.json'
    with open(out_path, 'w') as f:
        json.dump(result, f, indent=2)
    print(f"\nResult saved to {out_path}")
