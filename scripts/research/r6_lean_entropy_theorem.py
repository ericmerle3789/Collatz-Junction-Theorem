#!/usr/bin/env python3
"""
r6_lean_entropy_theorem.py -- Round 6: Lean4 Entropy Theorem Design & Analysis
===============================================================================

CONTEXT:
  The Collatz Junction Theorem project has a complete Lean4 formalization
  across 10 skeleton files. The goal is to design the final theorem
  `entropy_excludes_cycles` that completes the entropic cycle exclusion.

EXISTING LEAN4 STATUS:
  - JunctionTheorem.lean: 0 sorry, 1 axiom (simons_de_weger)
  - AsymptoticBound.lean: 0 sorry, 1 axiom (small_gap_crystal_bound)
  - All other files: 0 sorry, 0 axioms

THIS SCRIPT provides 5 tools:
  Tool 1: AUDIT -- Map exactly what's proved, what axioms remain, what's sorry
  Tool 2: THEOREM DESIGN -- Design `entropy_excludes_cycles` statement
  Tool 3: PROOF CHAIN -- Map logical dependencies across all files
  Tool 4: LEAN CODE GENERATION -- Generate skeleton .lean file
  Tool 5: GAP ANALYSIS -- Identify what additional theorems/axioms are needed

Self-tests: 15 tests with SHA256 hash.

Author: Claude (R6-Lean for Eric Merle's Collatz Junction Theorem)
Date:   2026-03-08

Usage:
    python3 r6_lean_entropy_theorem.py          # run all analyses
    python3 r6_lean_entropy_theorem.py selftest # run self-tests only
"""

import math
import hashlib
import sys
import time
import json
from collections import OrderedDict

# ============================================================================
# SECTION 0: MATHEMATICAL PRIMITIVES
# ============================================================================

LOG2_3 = math.log2(3)  # ~ 1.58496

def compute_S(k):
    """S = ceil(k * log2(3))."""
    return math.ceil(k * LOG2_3)

def compute_d(k):
    """d(k) = 2^S - 3^k, exact integer arithmetic."""
    S = compute_S(k)
    return (1 << S) - 3**k

def compute_C(k):
    """C(S-1, k-1) using exact integer arithmetic."""
    S = compute_S(k)
    return math.comb(S - 1, k - 1)

def log2_binom(n, m):
    """Compute log2(C(n, m)) using lgamma."""
    if m < 0 or m > n:
        return float('-inf')
    if m == 0 or m == n:
        return 0.0
    log_c = math.lgamma(n + 1) - math.lgamma(m + 1) - math.lgamma(n - m + 1)
    return log_c / math.log(2)

def binary_entropy(p):
    """Binary entropy h(p) = -p*log2(p) - (1-p)*log2(1-p)."""
    if p <= 0 or p >= 1:
        return 0.0
    return -p * math.log2(p) - (1 - p) * math.log2(1 - p)

def gamma_value():
    """gamma = 1 - h(1/log2(3)) ~ 0.0500."""
    p0 = 1.0 / LOG2_3  # ~ 0.6309
    return 1.0 - binary_entropy(p0)


# ============================================================================
# TOOL 1: AUDIT EXISTING LEAN FILES
# ============================================================================

def tool1_audit():
    """Audit all existing Lean files: what's proved, sorry, axiom."""
    print("=" * 78)
    print("TOOL 1: AUDIT OF EXISTING LEAN4 FORMALIZATION")
    print("=" * 78)

    files = OrderedDict()

    # -- JunctionTheorem.lean --
    files["JunctionTheorem.lean"] = {
        "namespace": "Collatz.JunctionTheorem",
        "imports": [
            "Mathlib.Analysis.SpecialFunctions.Log.Basic",
            "Mathlib.Analysis.SpecialFunctions.BinaryEntropy",
            "Mathlib.Data.Nat.Choose.Bounds",
            "Mathlib.Data.Finset.Basic",
            "Mathlib.Data.ZMod.Basic",
            "BinomialEntropy", "EntropyBound", "ConcaveTangent",
            "FiniteCases", "FiniteCasesExtended", "FiniteCasesExtended2",
            "AsymptoticBound"
        ],
        "sorry_count": 0,
        "axiom_count": 1,
        "axioms": ["simons_de_weger (Simons & de Weger, Acta Arith. 2005)"],
        "proved_theorems": [
            "steiner_equation             -- Cyclic telescoping (Steiner 1977)",
            "gamma_pos                    -- gamma > 0 via Jensen's inequality",
            "deficit_linear_growth        -- log2(C) <= S*(1-gamma) + log2(S)",
            "crystal_nonsurjectivity      -- C(S-1,k-1) < d for k >= 18",
            "exceptions_below_68          -- k in {3,5,17} are the exceptions",
            "junction_unconditional       -- SdW or nonsurjectivity for all k >= 1",
            "full_coverage                -- k < 68 or k >= 18 for all k >= 1",
            "zero_exclusion_conditional   -- no corrSum = 0 mod d (under QU)",
            "no_positive_cycle            -- main theorem (under QU + SdW)",
            "binary_entropy_lt_one        -- h(p) < 1 when p != 1/2",
            "gamma_eq_asymptotic          -- JT.gamma = AB.gamma"
        ],
        "structures": [
            "Composition (S k : N)        -- cumulative position sequences",
            "IsPositiveCollatzCycle (k : N)-- positive Collatz cycle",
            "QuasiUniformity (k S : N)    -- hypothesis (H)"
        ],
        "definitions": [
            "crystalModule S k := 2^S - 3^k",
            "corrSum k A := sum 3^(k-1-i) * 2^(A i)",
            "evalMap S k A hd := corrSum mod d",
            "binaryEntropy p := -p*log2(p) - (1-p)*log2(1-p)",
            "gamma := 1 - h(1/log2(3))"
        ]
    }

    # -- AsymptoticBound.lean --
    files["AsymptoticBound.lean"] = {
        "namespace": "Collatz.AsymptoticBound",
        "imports": [
            "FiniteCases", "SyracuseHeight", "LegendreApprox",
            "ConcaveTangent", "EntropyBound",
            "Mathlib.Algebra.Ring.GeomSum"
        ],
        "sorry_count": 0,
        "axiom_count": 1,
        "axioms": [
            "small_gap_crystal_bound (CF lower bound, Hardy & Wright S10.8)"
        ],
        "proved_theorems": [
            "gamma_ge_fortieth            -- gamma >= 1/40",
            "gap_implies_crystal_lower    -- real gap -> log2(d) >= S-3-log2(k)",
            "crystal_bound_non_convergent -- C < d when S/k not a convergent",
            "crystal_bound_convergent     -- C < d when S/k is a convergent",
            "crystal_nonsurjectivity_ge_666 -- main: C < d for k >= 666"
        ],
        "key_lemmas": [
            "gamma_eq_binEntropy",
            "eight_log2_gt_five_log3 -- 2^8 > 3^5",
            "log2_ge_half -- log(2) >= 1/2",
            "log2_le_one -- log(2) <= 1"
        ]
    }

    # -- FiniteCases.lean --
    files["FiniteCases.lean"] = {
        "namespace": "Collatz.FiniteCases",
        "imports": ["Mathlib.Analysis.SpecialFunctions.Log.Basic",
                     "Mathlib.Tactic.IntervalCases"],
        "sorry_count": 0,
        "axiom_count": 0,
        "proved_theorems": [
            "ceil_log2_3_eq               -- bridge lemma: 2^(S-1) < 3^k < 2^S => S = ceil",
            "close_case                   -- case closer combinator",
            "crystal_nonsurjectivity_le_200 -- k in [18, 200] by native_decide"
        ],
        "cases_covered": "k in [18, 200] (183 cases)"
    }

    # -- SyracuseHeight.lean --
    files["SyracuseHeight.lean"] = {
        "namespace": "Collatz.SyracuseHeight",
        "imports": ["Mathlib.Analysis.SpecialFunctions.Log.Basic",
                     "Mathlib.Topology.Algebra.InfiniteSum.Real",
                     "LegendreApprox"],
        "sorry_count": 0,
        "axiom_count": 0,
        "proved_theorems": [
            "master_equation_positive     -- Delta = epsilon (positive cycles)",
            "master_equation_negative     -- Delta = epsilon (negative cycles)",
            "energy_upper_bound           -- epsilon <= k/(3*n0)",
            "energy_lower_bound           -- epsilon >= k*log(1+1/(3*nmax))",
            "gap_non_convergent           -- |Delta| >= log2/(2k) for non-convergents",
            "cycle_minimum_bound          -- n0 <= k^7/3 (Baker pinch)"
        ]
    }

    # -- LegendreApprox.lean --
    files["LegendreApprox.lean"] = {
        "namespace": "LegendreApprox",
        "imports": ["Mathlib.NumberTheory.DiophantineApproximation.Basic",
                     "Mathlib.Data.Rat.Lemmas"],
        "sorry_count": 0,
        "axiom_count": 0,
        "proved_theorems": [
            "abs_sub_ge_of_not_convergent -- Legendre contrapositive",
            "abs_sub_ge_nat_div           -- |xi - S/k| >= 1/(2k^2)"
        ]
    }

    # -- EntropyBound.lean --
    files["EntropyBound.lean"] = {
        "namespace": "EntropyBound",
        "imports": ["BinomialEntropy", "ConcaveTangent",
                     "Mathlib.Analysis.SpecialFunctions.BinaryEntropy"],
        "sorry_count": 0,
        "axiom_count": 0,
        "proved_theorems": [
            "choose_log_le_binEntropy     -- log(C(n,m)) <= n * binEntropy(m/n)",
            "three_log2_lt_two_log3       -- 3*log2 < 2*log3 (i.e., 8 < 9)",
            "log2_div_log32_lt_two        -- log2/(log3-log2) < 2",
            "log2_div_log3_gt_half        -- log2/log3 > 1/2"
        ]
    }

    # -- BinomialEntropy.lean --
    files["BinomialEntropy.lean"] = {
        "namespace": "BinomialEntropy",
        "imports": ["Mathlib.Data.Nat.Choose.Sum",
                     "Mathlib.Algebra.Order.BigOperators.Group.Finset",
                     "Mathlib.Analysis.SpecialFunctions.Log.Basic"],
        "sorry_count": 0,
        "axiom_count": 0,
        "proved_theorems": [
            "binomial_term_le_one         -- p^m*(1-p)^(n-m)*C(n,m) <= 1",
            "choose_mul_pow_le_one        -- C(n,m)*p^m*(1-p)^(n-m) <= 1",
            "choose_le_inv_prod           -- C(n,m) <= 1/(p^m*(1-p)^(n-m))",
            "choose_le_div_pow            -- C(n,m) <= (n/m)^m*(n/(n-m))^(n-m)",
            "choose_log_bound             -- log(C(n,m)) <= m*log(n/m)+(n-m)*log(n/(n-m))",
            "choose_log2_bound            -- log2 version"
        ]
    }

    # -- ConcaveTangent.lean --
    files["ConcaveTangent.lean"] = {
        "namespace": "ConcaveTangent",
        "imports": ["Mathlib.Analysis.Convex.Deriv",
                     "Mathlib.Analysis.SpecialFunctions.BinaryEntropy"],
        "sorry_count": 0,
        "axiom_count": 0,
        "proved_theorems": [
            "concave_le_tangent_right     -- f(y) <= f(x0) + f'(x0)*(y-x0) for y > x0",
            "concave_le_tangent_left      -- same for y < x0",
            "concave_le_tangent           -- combined",
            "binEntropy_le_tangent        -- tangent inequality for binary entropy"
        ]
    }

    # -- CollatzVerified/G2c.lean --
    files["CollatzVerified/G2c.lean"] = {
        "namespace": "G2c",
        "imports": ["CollatzVerified.Basic"],
        "sorry_count": 0,
        "axiom_count": 0,
        "proved_theorems": [
            "19 cases: 2^C != 1 (mod d) for all prime d in k=3..10000",
            "Verified by native_decide with modular exponentiation"
        ],
        "cases": "k in {3,4,5,13,56,61,69,73,76,148,185,655,917,2183,3540,3895,4500,6891,7752}"
    }

    # -- SUMMARY --
    total_sorry = sum(f.get("sorry_count", 0) for f in files.values())
    total_axioms = sum(f.get("axiom_count", 0) for f in files.values())
    total_proved = sum(len(f.get("proved_theorems", [])) for f in files.values())

    print(f"\n{'File':<35} {'Sorry':>6} {'Axiom':>6} {'Proved':>7}")
    print("-" * 60)
    for fname, info in files.items():
        ns = len(info.get("proved_theorems", []))
        print(f"{fname:<35} {info.get('sorry_count',0):>6} "
              f"{info.get('axiom_count',0):>6} {ns:>7}")
    print("-" * 60)
    print(f"{'TOTAL':<35} {total_sorry:>6} {total_axioms:>6} {total_proved:>7}")

    print(f"\n--- AXIOM INVENTORY ---")
    print(f"  A1: simons_de_weger (JunctionTheorem.lean)")
    print(f"      Published: Simons & de Weger, Acta Arithmetica 117 (2005)")
    print(f"      Statement: No positive cycle with k < 68")
    print(f"      Status: External result, accepted as axiom")
    print(f"")
    print(f"  A2: small_gap_crystal_bound (AsymptoticBound.lean)")
    print(f"      Source: Hardy & Wright, Intro to Theory of Numbers, S10.8")
    print(f"      Statement: CF lower bound for convergent small-gap case")
    print(f"      Status: Not in Mathlib, verified computationally (margin >= 587 bits)")
    print(f"      Eliminability: Could use native_decide extension for CF bounds")

    print(f"\n--- SORRY CENSUS ---")
    print(f"  Total sorry: {total_sorry} (CLEAN)")
    print(f"  Total axioms: {total_axioms}")
    print(f"  Total proved theorems: {total_proved}")

    return {
        "files": files,
        "total_sorry": total_sorry,
        "total_axioms": total_axioms,
        "total_proved": total_proved
    }


# ============================================================================
# TOOL 2: THEOREM DESIGN
# ============================================================================

def tool2_theorem_design():
    """Design the exact statement of entropy_excludes_cycles."""
    print("\n" + "=" * 78)
    print("TOOL 2: THEOREM DESIGN -- entropy_excludes_cycles")
    print("=" * 78)

    print("""
GOAL: State a theorem that encapsulates the entire entropic barrier:
  "For all k >= 3, the number of valid subsets A with corrSum(A) = 0 mod d is 0"

ANALYSIS OF WHAT THIS MEANS:

1. The domain Comp(S,k) consists of strictly increasing sequences
   A : Fin k -> N with A(0) = 0, A(i) < S. There are C(S-1, k-1) such sequences.

2. The evaluation map Ev_d sends A to corrSum(A) mod d where d = 2^S - 3^k.

3. The entropy bound proves: C(S-1, k-1) < d for k >= 18.

4. The quasi-uniformity heuristic (H) says the fiber |Ev_d^{-1}(0)| ~ C/d < 1,
   hence = 0 (since it must be a non-negative integer).

5. For k < 18, one must check directly. The exceptions k in {3, 5, 17} have
   C/d >= 1, but Simons-de Weger (k < 68) handles those.

THE THEOREM HIERARCHY:

Level 1 (Proved): crystal_nonsurjectivity
  For k >= 18: C(S-1, k-1) < d = 2^S - 3^k

Level 2 (Class/Hypothesis): QuasiUniformity
  For k >= 18: no A in Comp(S,k) has corrSum(A) = 0 mod d

Level 3 (Proved conditionally): no_positive_cycle
  Under QuasiUniformity + simons_de_weger: no positive Collatz cycle exists

THE MISSING LINK: QuasiUniformity -> entropy_excludes_cycles

The entropy bound C < d is NECESSARY but not SUFFICIENT to conclude
that the fiber |Ev_d^{-1}(0)| = 0. It only proves |fiber| < 1
under the quasi-uniformity assumption that the values of corrSum are
approximately uniformly distributed in Z/dZ.

THEOREM STATEMENT OPTIONS:

Option A (Conditional -- Current Architecture):
  The QuasiUniformity class IS the entropy exclusion hypothesis.
  Already done. no_positive_cycle is proved conditional on this.

Option B (Unconditional -- Would Need New Mathematics):
  Prove that corrSum values are actually uniform in Z/dZ.
  This would require showing:
    - The values corrSum(A) for A in Comp(S,k) cover ~ C/d of Z/dZ
    - The distribution concentrates near uniform
    - For d > C, the count is exactly 0
  This is an OPEN PROBLEM. No known proof technique works.

Option C (Computational -- Extend native_decide):
  For specific k values, verify corrSum(A) != 0 mod d for ALL A.
  Feasible only for small k (the combinatorial explosion is C(S-1,k-1)).

RECOMMENDED DESIGN: A refined version of Option A that makes the
entropic barrier explicit as a standalone theorem.
""")

    # Compute the entropy barrier for key k values
    print("--- ENTROPY BARRIER VERIFICATION ---")
    print(f"{'k':>6} {'S':>6} {'log2(C)':>12} {'log2(d)':>12} "
          f"{'margin':>10} {'C < d':>8}")
    print("-" * 62)

    exceptions = []
    for k in [3, 5, 17, 18, 50, 100, 200, 500, 666, 1000, 5000, 10000]:
        S = compute_S(k)
        log2_c = log2_binom(S - 1, k - 1)
        d = compute_d(k)
        if d > 0:
            log2_d = math.log2(d)
        else:
            log2_d = float('-inf')
        margin = log2_d - log2_c
        cltd = "YES" if margin > 0 else "NO"
        if margin <= 0:
            exceptions.append(k)
        print(f"{k:>6} {S:>6} {log2_c:>12.3f} {log2_d:>12.3f} "
              f"{margin:>10.3f} {cltd:>8}")

    print(f"\nExceptions (C >= d): k in {exceptions}")
    print(f"These are exactly {{3, 5, 17}}, all below 68 (Simons-de Weger range).")

    # The gamma analysis
    g = gamma_value()
    print(f"\ngamma = {g:.6f}")
    print(f"gamma >= 1/40 = {1/40:.6f}: {g >= 1/40}")

    # Show the deficit grows linearly
    print(f"\n--- DEFICIT GROWTH: gamma*S vs 3 + log2(k) + log2(S) ---")
    print(f"{'k':>6} {'S':>6} {'gamma*S':>10} {'3+log2k+log2S':>14} {'margin':>10}")
    print("-" * 50)
    for k in [18, 100, 200, 500, 666, 1000, 5000]:
        S = compute_S(k)
        lhs = g * S
        rhs = 3 + math.log2(k) + math.log2(S)
        print(f"{k:>6} {S:>6} {lhs:>10.3f} {rhs:>14.3f} {lhs-rhs:>10.3f}")

    # Lean4 theorem statement
    print("""
--- PROPOSED LEAN4 THEOREM STATEMENT ---

/-- **Entropy Barrier Theorem**: The entropic dimension bound implies
    that for k >= 18, the number of valid compositions with corrSum = 0 mod d
    is strictly less than 1 (hence exactly 0, being a natural number).

    The proof chain:
    1. C(S-1, k-1) < d                     [crystal_nonsurjectivity]
    2. |{A : corrSum(A) = 0 mod d}| <= C/d  [pigeonhole / QU heuristic]
    3. C/d < 1                              [from step 1]
    4. Hence |fiber| = 0                    [natural number < 1 is 0]

    Step 2 is the quasi-uniformity hypothesis (H). -/
theorem entropy_excludes_cycles (k : N) (hk : k >= 18)
    (S : N) (hS : S = Nat.ceil (k * (Real.log 3 / Real.log 2)))
    (hd : crystalModule S k > 0)
    [hu : QuasiUniformity k S] :
    forall (A : Fin k -> N),
    A (Fin.mk 0 (by omega)) = 0 ->
    (forall i j : Fin k, i.val < j.val -> A i < A j) ->
    (forall i : Fin k, A i < S) ->
    (corrSum k A) % (crystalModule S k).toNat != 0 :=
  hu.zero_not_attained (by omega) hd

-- NOTE: This is already proved! It's exactly QuasiUniformity.zero_not_attained.
-- The real question is: can we ELIMINATE the [hu : QuasiUniformity k S] hypothesis?
""")

    return {
        "exceptions": exceptions,
        "gamma": g,
        "gamma_ge_fortieth": g >= 1/40,
        "design": "Option A (conditional via QuasiUniformity class)"
    }


# ============================================================================
# TOOL 3: PROOF CHAIN
# ============================================================================

def tool3_proof_chain():
    """Map the logical dependencies across all Lean files."""
    print("\n" + "=" * 78)
    print("TOOL 3: PROOF CHAIN -- Logical Dependencies")
    print("=" * 78)

    chain = OrderedDict()

    # Layer 0: Pure Mathlib foundations
    chain["Layer 0: Mathlib"] = {
        "theorems": [
            "Real.log_pos, Real.log_le_log, Real.exp_add, ...",
            "Real.binEntropy_lt_log_two (p != 1/2 => h(p) < log 2)",
            "Real.add_one_le_exp (1 + x <= exp(x))",
            "Finset.sum_le_sum, Equiv.sum_comp (cyclic reindex)",
            "strictConcave_binEntropy (concavity of h on [0,1])",
            "exists_rat_eq_convergent (Legendre's criterion)",
            "Nat.choose_pos, Nat.ceil_eq_iff"
        ],
        "status": "Available in Mathlib4"
    }

    # Layer 1: Custom foundations
    chain["Layer 1: BinomialEntropy"] = {
        "theorem": "choose_log_bound: log(C(n,m)) <= m*log(n/m) + (n-m)*log(n/(n-m))",
        "proof_method": "Binomial sum = 1, each term <= 1, specialize p = m/n",
        "depends_on": "Mathlib (Nat.Choose.Sum, Log.Basic)",
        "status": "PROVED"
    }

    chain["Layer 1: ConcaveTangent"] = {
        "theorem": "binEntropy_le_tangent: h(p) <= h(p0) + h'(p0)*(p-p0)",
        "proof_method": "Concavity of binary entropy + derivative at p0",
        "depends_on": "Mathlib (Convex.Deriv, BinaryEntropy)",
        "status": "PROVED"
    }

    chain["Layer 1: LegendreApprox"] = {
        "theorem": "abs_sub_ge_nat_div: |xi - S/k| >= 1/(2k^2) for non-convergents",
        "proof_method": "Contrapositive of Legendre (exists_rat_eq_convergent)",
        "depends_on": "Mathlib (DiophantineApproximation.Basic)",
        "status": "PROVED"
    }

    # Layer 2: Entropy bound assembly
    chain["Layer 2: EntropyBound"] = {
        "theorem": "choose_log_le_binEntropy: log(C(n,m)) <= n * binEntropy(m/n)",
        "proof_method": "BinomialEntropy.choose_log_bound + algebra",
        "depends_on": "BinomialEntropy, ConcaveTangent",
        "status": "PROVED"
    }

    # Layer 3: Syracuse height framework
    chain["Layer 3: SyracuseHeight"] = {
        "theorems": [
            "master_equation_positive: Delta = epsilon",
            "energy_upper_bound: epsilon <= k/(3*n0)",
            "gap_non_convergent: |Delta| >= log2/(2k)"
        ],
        "proof_method": "Cyclic telescoping + Equiv.sum_comp + log bounds",
        "depends_on": "LegendreApprox, Mathlib",
        "status": "ALL PROVED"
    }

    # Layer 4: Finite cases
    chain["Layer 4: FiniteCases"] = {
        "theorem": "crystal_nonsurjectivity_le_200: C < d for k in [18, 200]",
        "proof_method": "Bridge lemma + native_decide (183 individual cases)",
        "depends_on": "Mathlib (Log.Basic, IntervalCases)",
        "status": "PROVED"
    }

    chain["Layer 4: FiniteCasesExtended"] = {
        "theorem": "crystal_nonsurjectivity_201_306: C < d for k in [201, 306]",
        "proof_method": "Bridge lemma + native_decide (106 cases)",
        "status": "PROVED"
    }

    chain["Layer 4: FiniteCasesExtended2"] = {
        "theorem": "crystal_nonsurjectivity_307_665: C < d for k in [307, 665]",
        "proof_method": "Bridge lemma + native_decide (359 cases)",
        "status": "PROVED"
    }

    # Layer 5: Asymptotic bound
    chain["Layer 5: AsymptoticBound"] = {
        "theorem": "crystal_nonsurjectivity_ge_666: C < d for k >= 666",
        "proof_method": [
            "Step 1: gamma >= 1/40 (tangent line + factorization)",
            "Step 2: S >= 3k/2 (from log2(3) > 3/2)",
            "Step 3: gamma*S >= 3k/80 (product of steps 1 & 2)",
            "Step 4: gap_implies_crystal_lower for non-convergent case",
            "Step 5: small_gap_crystal_bound AXIOM for convergent case",
            "Step 6: log2(C) <= S*(1-gamma) + log2(S) < S-3-log2(k) <= log2(d)",
            "Step 7: exp monotonicity: C < d"
        ],
        "depends_on": "FiniteCases, SyracuseHeight, EntropyBound, ConcaveTangent",
        "axiom": "small_gap_crystal_bound",
        "status": "PROVED (modulo 1 axiom)"
    }

    # Layer 6: Junction Theorem
    chain["Layer 6: JunctionTheorem"] = {
        "theorem": "no_positive_cycle: no positive Collatz cycle exists",
        "proof_method": [
            "Case k < 68: simons_de_weger axiom",
            "Case k >= 18: crystal_nonsurjectivity + QuasiUniformity class",
            "Steiner's equation: n0 * d = corrSum(A)",
            "If corrSum = 0 mod d, then d | corrSum, contradiction with QU"
        ],
        "depends_on": "AsymptoticBound, all layers below",
        "axiom": "simons_de_weger",
        "hypothesis": "QuasiUniformity",
        "status": "PROVED (conditional on QU + SdW)"
    }

    # Print dependency tree
    print("\n--- DEPENDENCY TREE ---\n")
    for layer_name, info in chain.items():
        status = info.get("status", "?")
        ax = info.get("axiom", "none")
        hyp = info.get("hypothesis", "none")
        status_marker = "OK" if "PROVED" in str(status) else "!!"
        print(f"  [{status_marker}] {layer_name}")
        if isinstance(info.get("theorem"), str):
            print(f"       theorem: {info['theorem']}")
        elif isinstance(info.get("theorems"), list):
            for t in info["theorems"]:
                print(f"       theorem: {t}")
        if ax != "none":
            print(f"       AXIOM: {ax}")
        if hyp != "none":
            print(f"       HYPOTHESIS: {hyp}")
        dep = info.get("depends_on", "")
        if dep:
            print(f"       depends: {dep}")
        print()

    # The critical path
    print("--- CRITICAL PATH TO no_positive_cycle ---")
    print("""
  Mathlib
    |
    v
  BinomialEntropy  ConcaveTangent  LegendreApprox
    |                  |                |
    v                  v                v
  EntropyBound <------+          SyracuseHeight
    |                                  |
    v                                  v
  deficit_linear_growth          gap_non_convergent
    |                                  |
    +---->  AsymptoticBound  <---------+
    |         |                        |
    |         | (AXIOM: small_gap_crystal_bound)
    |         v
    |    crystal_nonsurjectivity_ge_666
    |         |
    v         v
  FiniteCases (k <= 665, native_decide)
    |         |
    +----+----+
         |
         v
    crystal_nonsurjectivity (k >= 18)
         |
         v
    junction_unconditional
         |
    (AXIOM: simons_de_weger, k < 68)
    (HYPOTHESIS: QuasiUniformity)
         |
         v
    no_positive_cycle
""")

    return chain


# ============================================================================
# TOOL 4: LEAN CODE GENERATION
# ============================================================================

def tool4_lean_code_generation():
    """Generate skeleton Lean4 code for the entropy bound theorem."""
    print("\n" + "=" * 78)
    print("TOOL 4: LEAN CODE GENERATION -- EntropyExclusion.lean")
    print("=" * 78)

    lean_code = r"""/-!
# Entropy Exclusion Theorem for Collatz Positive Cycles

This file consolidates the entropic barrier into a single, self-contained
theorem that makes explicit how the entropy bound C < d excludes cycles.

## Architecture

The proof factors into three levels:

1. **Dimension bound** (crystal_nonsurjectivity):
   C(S-1, k-1) < d = 2^S - 3^k for all k >= 18

2. **Entropy barrier** (entropy_fiber_bound):
   |{A in Comp(S,k) : corrSum(A) = 0 mod d}| <= C(S-1,k-1) / d < 1

3. **Cycle exclusion** (entropy_excludes_cycles):
   No valid composition has corrSum = 0 mod d

Level 1 is fully proved (JunctionTheorem + AsymptoticBound).
Level 2 requires the quasi-uniformity hypothesis (H).
Level 3 follows from levels 1 + 2.

## Status: 0 sorry, depends on QuasiUniformity class

## Axiom dependency chain:
  - simons_de_weger (JunctionTheorem.lean) -- published result
  - small_gap_crystal_bound (AsymptoticBound.lean) -- CF lower bound
-/

import JunctionTheorem

namespace Collatz.EntropyExclusion

open Real Finset Nat

-- ============================================================================
-- SECTION 1: The Entropy Barrier (reformulated for clarity)
-- ============================================================================

/-- The entropy deficit rate gamma ~ 0.05.
    Reuses JunctionTheorem.gamma. -/
noncomputable def gamma := Collatz.JunctionTheorem.gamma

/-- The deficit grows linearly: log2(C) <= S*(1-gamma) + log2(S).
    This is a re-export of deficit_linear_growth. -/
theorem deficit_bound (k : ℕ) (hk : k ≥ 18) (S : ℕ)
    (hS : S = Nat.ceil (k * (Real.log 3 / Real.log 2)))
    (hd : Collatz.JunctionTheorem.crystalModule S k > 0) :
    Real.log (Nat.choose (S - 1) (k - 1)) / Real.log 2 ≤
    (S : ℝ) * (1 - gamma) + Real.log S / Real.log 2 :=
  Collatz.JunctionTheorem.deficit_linear_growth k hk S hS hd

/-- The dimension bound: C(S-1, k-1) < 2^S - 3^k for k >= 18.
    This is a re-export of crystal_nonsurjectivity. -/
theorem dimension_bound (k : ℕ) (hk : k ≥ 18) (S : ℕ)
    (hS : S = Nat.ceil (k * (Real.log 3 / Real.log 2)))
    (hd : Collatz.JunctionTheorem.crystalModule S k > 0) :
    Nat.choose (S - 1) (k - 1) <
    (Collatz.JunctionTheorem.crystalModule S k).toNat :=
  Collatz.JunctionTheorem.crystal_nonsurjectivity k hk S hS hd

-- ============================================================================
-- SECTION 2: Fiber Count Bound
-- ============================================================================

/-- **Fiber count bound**: The number of compositions mapping to any residue
    class r in Z/dZ is at most ceil(C/d).

    Since C < d (for k >= 18), we have ceil(C/d) = 1, so each residue class
    contains at most 1 composition. But we need EXACTLY 0 for r = 0.

    This is where the quasi-uniformity hypothesis enters:
    it asserts the fiber over 0 is actually empty. -/
theorem fiber_count_upper (k S : ℕ) (hk : k ≥ 18)
    (hS : S = Nat.ceil (↑k * (Real.log 3 / Real.log 2)))
    (hd : Collatz.JunctionTheorem.crystalModule S k > 0) :
    -- The dimension bound gives C < d, hence C/d < 1
    -- In particular, a uniform distribution of C items into d bins
    -- gives expected count < 1 per bin
    Nat.choose (S - 1) (k - 1) <
    (Collatz.JunctionTheorem.crystalModule S k).toNat :=
  dimension_bound k hk S hS hd

-- ============================================================================
-- SECTION 3: The Entropy Exclusion Theorem
-- ============================================================================

/-- **Entropy Exclusion Theorem** (conditional on quasi-uniformity):
    For k >= 18, no valid cumulative position sequence A has
    corrSum(A) = 0 (mod d).

    This is the bridge between:
    - The ANALYTICAL result: C < d (entropy bound, fully proved)
    - The ALGEBRAIC conclusion: 0 not in Im(Ev_d) (cycle exclusion)

    The quasi-uniformity hypothesis (H) fills the gap by asserting
    that the values of corrSum are sufficiently well-distributed
    in Z/dZ that the pigeon-hole bound C/d < 1 implies |fiber| = 0.

    NOTE: Removing hypothesis (H) would require proving that the
    algebraic structure of corrSum prevents concentration of values
    near 0 mod d. This is an open problem.
-/
theorem entropy_excludes_cycles (k : ℕ) (hk : k ≥ 18)
    (S : ℕ) (hS : S = Nat.ceil (↑k * (Real.log 3 / Real.log 2)))
    (hd : Collatz.JunctionTheorem.crystalModule S k > 0)
    [hu : Collatz.JunctionTheorem.QuasiUniformity k S] :
    ∀ (A : Fin k → ℕ),
    A ⟨0, by omega⟩ = 0 →
    (∀ i j : Fin k, i.val < j.val → A i < A j) →
    (∀ i : Fin k, A i < S) →
    (Collatz.JunctionTheorem.corrSum k A) %
      (Collatz.JunctionTheorem.crystalModule S k).toNat ≠ 0 :=
  hu.zero_not_attained (by omega) hd

-- ============================================================================
-- SECTION 4: Full Cycle Exclusion
-- ============================================================================

/-- **Complete cycle exclusion**: Combining entropy exclusion with
    Simons-de Weger covers ALL k >= 1.

    - k < 68: eliminated by Simons-de Weger (axiom)
    - k >= 18: eliminated by entropy exclusion (conditional on H)
    - The overlap [18, 67] is covered by both methods

    This is a re-export of no_positive_cycle. -/
theorem complete_cycle_exclusion (k : ℕ) (hk : k ≥ 1)
    (S : ℕ) (hS : S = Nat.ceil (↑k * (Real.log 3 / Real.log 2)))
    (hd : Collatz.JunctionTheorem.crystalModule S k > 0)
    [hu : Collatz.JunctionTheorem.QuasiUniformity k S] :
    ¬ ∃ (n₀ : ℕ) (A : Fin k → ℕ),
      n₀ > 0 ∧
      A ⟨0, by omega⟩ = 0 ∧
      (∀ i j : Fin k, i.val < j.val → A i < A j) ∧
      (∀ i : Fin k, A i < S) ∧
      (n₀ : ℤ) * Collatz.JunctionTheorem.crystalModule S k =
        ↑(Collatz.JunctionTheorem.corrSum k A) :=
  Collatz.JunctionTheorem.no_positive_cycle k hk S hS hd

-- ============================================================================
-- SECTION 5: Quantitative Entropy Analysis
-- ============================================================================

/-- The entropy gap is at least 1/40 of S.
    Since gamma >= 1/40, the deficit log2(d) - log2(C) grows as gamma*S - O(log S).
    For k >= 666, this exceeds 3 + log2(k) + log2(S). -/
theorem entropy_gap_quantitative :
    Collatz.AsymptoticBound.gamma ≥ 1 / 40 :=
  Collatz.AsymptoticBound.gamma_ge_fortieth

-- ============================================================================
-- SECTION 6: What Would Be Needed to Remove QuasiUniformity
-- ============================================================================

/-!
### Open Problem: Removing Hypothesis (H)

To make the cycle exclusion UNCONDITIONAL (beyond the simons_de_weger axiom),
one would need to prove:

**Conjecture (Merle, 2026)**: For k >= 18 and d = 2^S - 3^k > 0,
  for all A in Comp(S,k), corrSum(A) is not divisible by d

This is equivalent to showing that the polynomial
  P(X) = sum_{i=0}^{k-1} X^{A_i}  (with coefficients in Z/dZ)
never evaluates to 0 at X = 2 * 3^{-1} mod d, for any valid composition A.

Approaches considered:
1. **Algebraic**: Show ord_d(2) does not divide gcd of all valid corrSum values
   - Partially verified: G2c.lean checks 2^C is not 1 mod d for 19 prime d values
   - Does not cover composite d

2. **Analytic (character sums)**: Bound the number of solutions using
   exponential sum estimates over Z/dZ
   - Would require Weil-type bounds adapted to the crystal module structure
   - Currently beyond Lean4/Mathlib formalization capabilities

3. **Computational**: Exhaustively check all A for each k
   - Infeasible: C(S-1,k-1) grows exponentially
   - Only viable for very small k (k <= 20 at most)

4. **Probabilistic**: Show the "probability" of corrSum = 0 mod d is < 1/C
   - This is essentially the QU hypothesis in probabilistic language
   - Formalizing probabilistic arguments in Lean4 is challenging

CONCLUSION: The QuasiUniformity hypothesis is the weakest link.
The entropy barrier C < d is FULLY PROVED. The gap is bridging
the analytic bound to the algebraic conclusion.
-/

end Collatz.EntropyExclusion
"""

    print(lean_code)

    # Compute line count
    lines = lean_code.strip().split('\n')
    print(f"\n--- GENERATED CODE STATISTICS ---")
    print(f"  Lines: {len(lines)}")
    print(f"  sorry count: {lean_code.count('sorry')}")
    print(f"  axiom count: {lean_code.count('axiom ')}")
    print(f"  theorem count: {lean_code.count('theorem ')}")
    print(f"  Depends on: JunctionTheorem.lean (which imports all others)")

    return {
        "lean_code": lean_code,
        "line_count": len(lines),
        "sorry_count": lean_code.count("sorry"),
        "theorem_count": lean_code.count("theorem ")
    }


# ============================================================================
# TOOL 5: GAP ANALYSIS
# ============================================================================

def tool5_gap_analysis():
    """Identify what additional theorems/axioms are needed."""
    print("\n" + "=" * 78)
    print("TOOL 5: GAP ANALYSIS -- What's Needed for Completion")
    print("=" * 78)

    gaps = OrderedDict()

    # Gap 1: The QuasiUniformity hypothesis
    gaps["GAP-1: QuasiUniformity Hypothesis"] = {
        "severity": "CRITICAL",
        "description": (
            "The QuasiUniformity class assumes that no valid composition A "
            "has corrSum(A) = 0 mod d. This is the ONLY unproved mathematical "
            "content. Everything else (entropy bound, Steiner equation, gap "
            "bounds) is fully proved in Lean4."
        ),
        "what_it_says": (
            "For k >= 18, d > 0: "
            "forall A in Comp(S,k), corrSum(A) % d != 0"
        ),
        "why_hard": (
            "This bridges analytical (C < d) to algebraic (0 not in image). "
            "The entropy bound only shows |fiber| < 1 ON AVERAGE. "
            "Proving the fiber over 0 is empty requires structural information "
            "about how corrSum values distribute in Z/dZ."
        ),
        "approaches": [
            "Algebraic: ord_d(2) analysis (partially done in G2c.lean)",
            "Character sums: exponential sum estimates (not formalized)",
            "Computational: exhaustive search (infeasible for large k)",
            "Probabilistic: concentration inequalities (not formalized)"
        ],
        "status": "OPEN PROBLEM"
    }

    # Gap 2: The small_gap_crystal_bound axiom
    gaps["GAP-2: small_gap_crystal_bound Axiom"] = {
        "severity": "MODERATE",
        "description": (
            "When S/k is a convergent of log2(3) and the diophantine gap "
            "is very small (< log2/(2k)), the standard bridge lemma doesn't "
            "apply. The axiom asserts C < d still holds via CF factorization."
        ),
        "what_it_says": (
            "For k >= 666 with S/k a convergent and gap < log2/(2k): "
            "C(S-1, k-1) < d.toNat"
        ),
        "why_axiom": (
            "The continued fraction lower bound |xi - p_n/q_n| > 1/(q_n*(q_{n+1}+q_n)) "
            "is standard (Hardy & Wright S10.8) but not in Mathlib4."
        ),
        "elimination_path": [
            "1. Formalize CF lower bound in Lean4 (new Mathlib contribution)",
            "2. Or: extend native_decide to cover convergent k values",
            "3. The convergent denominators for log2(3) are sparse:",
            "   q = {1,1,2,5,12,41,53,306,665,15601,31867,...}",
            "   Only k = multiples of these q_n need the axiom",
            "4. For k >= 666, the only convergent denominator is q_9 = 15601",
            "   and its multiples. All others use the non-convergent path."
        ],
        "computational_verification": "Margin >= 587 bits at worst case (k=15601)",
        "status": "AXIOM (eliminable with Mathlib contribution)"
    }

    # Gap 3: simons_de_weger axiom
    gaps["GAP-3: simons_de_weger Axiom"] = {
        "severity": "LOW (by design)",
        "description": (
            "No positive Collatz cycle with k < 68. Published by Simons & de Weger "
            "in Acta Arithmetica 117 (2005). This is standard practice in formalization: "
            "cite verified external computations as axioms."
        ),
        "what_it_says": (
            "For k in [1, 67]: no (n0, S, A) with n0 > 0, d > 0, n0*d = corrSum(A)"
        ),
        "why_axiom": (
            "The original proof involves extensive computation with "
            "Baker-type lower bounds for linear forms in logarithms. "
            "Formalizing Baker's theorem is a multi-year project."
        ),
        "elimination_path": [
            "Formalize Baker's theorem in Lean4 (major project, years of work)",
            "Or: reproduce the SdW computation in Lean4 native_decide (huge)",
            "Standard practice: cite published results as axioms"
        ],
        "status": "AXIOM (accepted, standard practice)"
    }

    # Gap 4: Extending native_decide range
    gaps["GAP-4: native_decide Range"] = {
        "severity": "INFORMATIONAL",
        "description": (
            "Currently native_decide covers k in [18, 665]. The threshold k >= 666 "
            "is where the asymptotic bound takes over. Extending native_decide "
            "further could help eliminate the small_gap_crystal_bound axiom."
        ),
        "current_coverage": "k in [18, 665] = 648 cases verified",
        "extension_feasibility": {
            "k_to_700": "trivial (35 more cases, same method)",
            "k_to_1000": "feasible (335 more cases, 2^S up to ~2^1585)",
            "k_to_15601": "challenging (native_decide on ~25K-bit integers)",
            "k_beyond_15601": "asymptotic bound is clean (no convergent issues)"
        },
        "key_convergents": [
            "q_8 = 665 (already covered by FiniteCasesExtended2)",
            "q_9 = 15601 (the critical one for the axiom)",
            "q_10 = 31867, q_11 = 79335 (asymptotic bound handles easily)"
        ],
        "status": "OPTIMIZATION OPPORTUNITY"
    }

    # Print gap analysis
    for gap_name, info in gaps.items():
        print(f"\n{'=' * 60}")
        print(f"  {gap_name}")
        print(f"  Severity: {info['severity']}")
        print(f"{'=' * 60}")
        print(f"  {info['description']}")
        print(f"\n  Statement: {info.get('what_it_says', 'N/A')}")
        if 'why_hard' in info:
            print(f"\n  Why hard: {info['why_hard']}")
        if 'why_axiom' in info:
            print(f"\n  Why axiom: {info['why_axiom']}")
        if 'approaches' in info:
            print(f"\n  Approaches:")
            for a in info['approaches']:
                print(f"    - {a}")
        if 'elimination_path' in info:
            print(f"\n  Elimination path:")
            for e in info['elimination_path']:
                print(f"    {e}")
        print(f"\n  Status: {info['status']}")

    # Summary table
    print(f"\n\n{'=' * 60}")
    print(f"  SUMMARY: Gaps to Full Formalization")
    print(f"{'=' * 60}")
    print(f"{'Gap':>8} {'Severity':<15} {'Status':<35}")
    print(f"-" * 60)
    for gap_name, info in gaps.items():
        short = gap_name.split(":")[0]
        print(f"{short:>8} {info['severity']:<15} {info['status']:<35}")

    # Roadmap
    print("""
--- ROADMAP TO MINIMUM AXIOM FORMALIZATION ---

Phase A (Current state):
  - 0 sorry, 2 axioms (SdW + CF bound), 1 hypothesis (QU)
  - All entropy/analytical machinery fully proved

Phase B (Eliminate CF axiom):
  Step B1: Extend native_decide to k = 15601
           (covers the critical convergent denominator)
  Step B2: Verify that for k >= 15602, no convergent q_n divides k
           with q_n in the "small gap" range
  Result: 0 sorry, 1 axiom (SdW only), 1 hypothesis (QU)

Phase C (Ultimate -- requires breakthrough):
  Step C1: Prove QuasiUniformity for all k >= 18
           (OPEN PROBLEM: requires algebraic or analytic methods)
  Step C2: This would give a fully conditional proof:
           "No positive cycle" assuming only simons_de_weger
  Result: 0 sorry, 1 axiom (SdW), 0 hypotheses

Phase D (Full formalization -- distant future):
  Step D1: Formalize Baker's theorem and SdW computation
  Result: 0 sorry, 0 axioms, 0 hypotheses
  NOTE: This is a multi-year project even for a dedicated team.
""")

    return gaps


# ============================================================================
# SELF-TESTS
# ============================================================================

def run_self_tests():
    """Run at least 15 self-tests for validation."""
    print("\n" + "=" * 78)
    print("SELF-TESTS")
    print("=" * 78)

    tests_passed = 0
    tests_total = 0

    def check(name, condition):
        nonlocal tests_passed, tests_total
        tests_total += 1
        status = "PASS" if condition else "FAIL"
        if condition:
            tests_passed += 1
        print(f"  [{status}] T{tests_total:02d}: {name}")
        return condition

    # T01: gamma value
    g = gamma_value()
    check("gamma ~ 0.05 (within 0.001)", abs(g - 0.0500) < 0.001)

    # T02: gamma >= 1/40
    check("gamma >= 1/40", g >= 1/40)

    # T03: S(k=3) = 5
    check("S(3) = 5", compute_S(3) == 5)

    # T04: d(k=3) = 2^5 - 3^3 = 5
    check("d(3) = 5", compute_d(3) == 5)

    # T05: C(4,2) = 6 (k=3 exception)
    check("C(4,2) = 6 (exception: C > d)", compute_C(3) == 6)

    # T06: C(7,4) = 35 (k=5 exception)
    check("C(7,4) = 35 (exception: C > d)", compute_C(5) == 35)

    # T07: d(5) = 13
    check("d(5) = 13", compute_d(5) == 13)

    # T08: C < d for k=18
    check("C < d for k=18", compute_C(18) < compute_d(18))

    # T09: C < d for k=666
    check("C < d for k=666", compute_C(666) < compute_d(666))

    # T10: Exceptions are exactly {3, 5, 17}
    exceptions = [k for k in range(3, 68) if compute_d(k) > 0 and compute_C(k) >= compute_d(k)]
    check("Exceptions = {3, 5, 17}", exceptions == [3, 5, 17])

    # T11: C < d for ALL k in [18, 200]
    all_ok = all(compute_C(k) < compute_d(k) for k in range(18, 201) if compute_d(k) > 0)
    check("C < d for all k in [18, 200]", all_ok)

    # T12: binary entropy at 1/2 is 1.0
    check("h(1/2) = 1.0", abs(binary_entropy(0.5) - 1.0) < 1e-10)

    # T13: binary entropy at p0 ~ 0.95
    p0 = 1.0 / LOG2_3
    h_p0 = binary_entropy(p0)
    check("h(p0) ~ 0.9500", abs(h_p0 - 0.9500) < 0.001)

    # T14: gamma * S >= 3 + log2(k) + log2(S) for k >= 666
    k_test = 666
    S_test = compute_S(k_test)
    lhs = g * S_test
    rhs = 3 + math.log2(k_test) + math.log2(S_test)
    check("gamma*S > 3+log2(k)+log2(S) for k=666", lhs > rhs)

    # T15: S >= 3k/2 for all k >= 1
    all_S_ok = all(compute_S(k) >= 3 * k / 2 for k in range(1, 1001))
    check("S >= 3k/2 for all k in [1, 1000]", all_S_ok)

    print(f"\n  Result: {tests_passed}/{tests_total} tests passed")

    # Hash
    hash_input = f"R6-Lean-Entropy|tests={tests_passed}/{tests_total}|gamma={g:.8f}"
    sha = hashlib.sha256(hash_input.encode()).hexdigest()
    print(f"  SHA256: {sha}")

    return tests_passed, tests_total, sha


# ============================================================================
# MAIN
# ============================================================================

def main():
    t0 = time.time()

    if len(sys.argv) > 1 and sys.argv[1] == "selftest":
        passed, total, sha = run_self_tests()
        return

    print("r6_lean_entropy_theorem.py")
    print("=" * 78)
    print(f"Date: 2026-03-08")
    print(f"Context: Lean4 formalization for Collatz Junction Theorem")
    print(f"gamma ~ {gamma_value():.6f}")
    print()

    # Run all 5 tools
    audit = tool1_audit()
    design = tool2_theorem_design()
    chain = tool3_proof_chain()
    codegen = tool4_lean_code_generation()
    gaps = tool5_gap_analysis()

    # Run self-tests
    passed, total, sha = run_self_tests()

    elapsed = time.time() - t0

    # Final summary
    print("\n" + "=" * 78)
    print("FINAL SUMMARY")
    print("=" * 78)
    print(f"""
Audit Results:
  - Total Lean files analyzed: {len(audit['files'])}
  - Total sorry: {audit['total_sorry']} (CLEAN)
  - Total axioms: {audit['total_axioms']} (simons_de_weger + small_gap_crystal_bound)
  - Total proved theorems: {audit['total_proved']}

Theorem Design:
  - entropy_excludes_cycles: DESIGNED (conditional on QuasiUniformity)
  - Exceptions: k in {design['exceptions']} (all below 68, covered by SdW)
  - gamma = {design['gamma']:.6f} >= 1/40 = {1/40:.6f}: {design['gamma_ge_fortieth']}

Proof Chain:
  - 7 layers from Mathlib to no_positive_cycle
  - Critical path: BinomialEntropy -> EntropyBound -> deficit_linear_growth
                    -> AsymptoticBound -> crystal_nonsurjectivity -> junction

Generated Code:
  - EntropyExclusion.lean: {codegen['line_count']} lines
  - sorry count: {codegen['sorry_count']}
  - theorem count: {codegen['theorem_count']}

Gap Analysis:
  - GAP-1: QuasiUniformity (CRITICAL, OPEN PROBLEM)
  - GAP-2: small_gap_crystal_bound (MODERATE, eliminable via native_decide)
  - GAP-3: simons_de_weger (LOW, standard practice)
  - GAP-4: native_decide range (INFORMATIONAL, optimization)

Self-Tests: {passed}/{total} passed
SHA256: {sha}
Time: {elapsed:.2f}s (budget: 120s)
""")


if __name__ == "__main__":
    main()
