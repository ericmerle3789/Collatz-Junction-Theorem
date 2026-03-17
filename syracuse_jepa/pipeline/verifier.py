"""
Verifier — Lean 4 Compilation & Feedback Loop

Writes generated Lean files, runs `lake build`, parses results.
Returns structured feedback for the Conjecturer to retry on failure.
"""

import os
import subprocess
import re
from dataclasses import dataclass
from typing import List, Dict, Optional


@dataclass
class VerificationResult:
    success: bool
    n_theorems_attempted: int
    n_theorems_proved: int
    errors: List[str]
    build_time_seconds: float
    lean_output: str

    def summary(self) -> str:
        if self.success:
            return (f"✓ ALL {self.n_theorems_proved} theorems verified "
                    f"in {self.build_time_seconds:.1f}s")
        else:
            return (f"✗ FAILED: {len(self.errors)} errors "
                    f"({self.n_theorems_proved}/{self.n_theorems_attempted} proved)")


def write_lean_files(files: Dict[str, str]) -> None:
    """Write generated Lean files to disk."""
    for path, content in files.items():
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, 'w') as f:
            f.write(content)
        print(f"  Wrote: {path}")


def run_lake_build(lean_dir: str, timeout: int = 600) -> VerificationResult:
    """
    Run `lake build` in the Lean project directory.
    Returns structured result.
    """
    import time
    t0 = time.time()

    try:
        result = subprocess.run(
            ['lake', 'build'],
            cwd=lean_dir,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        elapsed = time.time() - t0
        output = result.stdout + result.stderr

        # Parse errors
        errors = []
        for line in output.split('\n'):
            if 'error:' in line.lower():
                errors.append(line.strip())

        # Count theorems from the Theorems.lean file
        theorems_file = os.path.join(lean_dir, 'CorrSumAvoidance', 'Theorems.lean')
        n_attempted = 0
        if os.path.exists(theorems_file):
            with open(theorems_file) as f:
                n_attempted = f.read().count('native_decide')

        success = result.returncode == 0 and len(errors) == 0
        n_proved = n_attempted if success else max(0, n_attempted - len(errors))

        return VerificationResult(
            success=success,
            n_theorems_attempted=n_attempted,
            n_theorems_proved=n_proved,
            errors=errors,
            build_time_seconds=elapsed,
            lean_output=output,
        )

    except subprocess.TimeoutExpired:
        elapsed = time.time() - t0
        return VerificationResult(
            success=False,
            n_theorems_attempted=0,
            n_theorems_proved=0,
            errors=[f"TIMEOUT after {timeout}s"],
            build_time_seconds=elapsed,
            lean_output="",
        )


def verify(files: Dict[str, str], lean_dir: str,
           timeout: int = 600) -> VerificationResult:
    """
    Full verification: write files, build, return result.
    """
    print("=" * 70)
    print("  VERIFIER — Compiling Lean 4 proofs")
    print("=" * 70)

    # Write files
    write_lean_files(files)

    # Build
    print(f"  Running: lake build (timeout={timeout}s)")
    result = run_lake_build(lean_dir, timeout)

    # Report
    print(f"  {result.summary()}")
    if not result.success:
        for err in result.errors[:10]:
            print(f"    ERROR: {err}")

    return result


def diagnose_failure(result: VerificationResult) -> List[str]:
    """
    Analyze a failed build and suggest fixes for the Conjecturer.
    Returns list of suggestions.
    """
    suggestions = []

    for err in result.errors:
        if 'native_decide' in err and 'failed' in err.lower():
            # native_decide failed = the proposition is FALSE
            suggestions.append("PROPOSITION_FALSE: A native_decide theorem evaluated to false. "
                             "The hypothesis is WRONG — remove it.")
        elif 'timeout' in err.lower():
            suggestions.append("TIMEOUT: Lean compilation took too long. "
                             "Reduce k_max or split into separate files.")
        elif 'unknown identifier' in err.lower():
            suggestions.append("SYNTAX_ERROR: Unknown identifier. "
                             "Check that Basic.lean exports all needed definitions.")
        elif 'type mismatch' in err.lower():
            suggestions.append("TYPE_ERROR: Type mismatch in theorem statement. "
                             "Check that values are correct Nat literals.")
        else:
            suggestions.append(f"UNKNOWN: {err}")

    return suggestions
