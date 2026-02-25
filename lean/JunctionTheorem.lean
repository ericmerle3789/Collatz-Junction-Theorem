import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Choose.Bounds
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal

/-!
# Junction Theorem for Collatz Positive Cycles

## Overview

This file formalizes the **Junction Theorem** for the nonexistence of
nontrivial positive Collatz cycles, as presented in:

  E. Merle, "Entropic Barriers and Nonsurjectivity in the 3x+1 Problem:
  The Junction Theorem", 2026.

The theorem combines two complementary obstructions:

  **(A)** Simons–de Weger (2005): no positive cycle with k < 68
  **(B)** Crystal nonsurjectivity: for k ≥ 18 with d > 0, C(S−1, k−1) < d

The overlap [18, 67] ensures every k ≥ 1 is covered.

## Status

**SKELETON** — all proofs are `sorry` (except `full_coverage`, proved by `omega`).

Each theorem includes:
  - Difficulty rating: ★ (trivial) to ★★★★★ (research-level)
  - Proof strategy sketch
  - Required Mathlib dependencies

## Key Constant

  γ = 1 − h(1/log₂ 3) ≈ 0.0500

where h is binary Shannon entropy. This is the bits-per-step deficit
that prevents the modular evaluation map from being surjective.

## References

- [Steiner1977] R.P. Steiner, "A theorem on the Syracuse problem", 1977
- [SimonsDeWeger2005] D. Simons, B. de Weger, "Theoretical and computational
  bounds for m-cycles of the 3n+1 problem", Acta Arith. 117, 2005
- [Tao2022] T. Tao, "Almost all orbits of the Collatz map attain almost
  bounded values", Forum Math. Pi 10, 2022
-/

namespace Collatz.JunctionTheorem

open Real Finset Nat

-- ============================================================================
-- PART A: Core Definitions
-- ============================================================================

/-- A composition of S − k into k nonnegative parts with A₀ = 0.

Represents the step structure of a Collatz cycle: k odd steps and
S total steps (so S − k even steps). The constraint A₀ = 0 comes
from Steiner's normalization choosing n₀ as the cycle minimum. -/
structure Composition (S k : ℕ) where
  /-- The sequence of gap lengths between consecutive odd steps -/
  A : Fin k → ℕ
  /-- First gap is zero (Steiner normalization) -/
  hA0 : k > 0 → A ⟨0, by omega⟩ = 0
  /-- Gaps sum to S − k (total even steps) -/
  hSum : Finset.univ.sum A = S - k
  /-- More total steps than odd steps -/
  hSgtk : S > k

/-- The crystal module d = 2^S − 3^k.

This integer governs the modular arithmetic of Collatz cycles.
A cycle exists only if d > 0 and d divides the corrective sum.
Named "crystal" because the prime factorization of d determines
the lattice of modular obstructions. -/
def crystalModule (S k : ℕ) : ℤ := (2 : ℤ) ^ S - (3 : ℤ) ^ k

/-- The corrective sum (Steiner's formula).

  corrSum(A) = Σᵢ 3^{k−1−i} · 2^{Aᵢ}

This is the total arithmetic correction accumulated over one
traversal of a Collatz cycle. -/
def corrSum (k : ℕ) (A : Fin k → ℕ) : ℕ :=
  Finset.univ.sum fun i => 3 ^ (k - 1 - i.val) * 2 ^ (A i)

/-- The evaluation map Ev_d : Comp(S, k) → ℤ/dℤ.

Sends a composition A to corrSum(A) mod d. The existence of a
positive cycle is equivalent to 0 ∈ Im(Ev_d). -/
def evalMap (S k : ℕ) (A : Fin k → ℕ) (hd : crystalModule S k > 0) :
    ZMod (crystalModule S k).toNat :=
  ↑(corrSum k A)

/-- Binary Shannon entropy: h(p) = −p log₂ p − (1−p) log₂(1−p). -/
noncomputable def binaryEntropy (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) : ℝ :=
  -(p * Real.log p / Real.log 2 +
    (1 - p) * Real.log (1 - p) / Real.log 2)

/-- The entropy-module gap constant.

  γ = 1 − h(1/log₂ 3)

Numerically: γ ≈ 0.0500444728. This measures the per-bit deficit
between the growth rate of compositions and the crystal module. -/
noncomputable def gamma : ℝ :=
  1 - binaryEntropy (1 / (Real.log 3 / Real.log 2))
    (by positivity)
    (by
      rw [div_lt_one (by positivity)]
      · exact Real.log_lt_log (by positivity) (by norm_num))

-- ============================================================================
-- PART B: Steiner's Equation
-- ============================================================================

/-- **Steiner's equation** (1977).

If n₀ is the minimum element of a positive Collatz cycle with
k odd steps and S total steps, then:

  n₀ · (2^S − 3^k) = corrSum(A₀, …, A_{k−1})

- Difficulty: ★★
- Strategy: induction on cycle steps, accumulating corrections
- Dependencies: basic Collatz iteration properties -/
theorem steiner_equation (n₀ : ℕ) (hn : n₀ > 0) (S k : ℕ)
    (A : Fin k → ℕ) (hcycle : True /- placeholder: "forms a cycle" -/) :
    (n₀ : ℤ) * crystalModule S k = ↑(corrSum k A) := by
  sorry

-- ============================================================================
-- PART C: The Nonsurjectivity Theorem (Unconditional Core)
-- ============================================================================

/-- **Theorem 1**: Crystal nonsurjectivity.

For k ≥ 18 with S = ⌈k · log₂ 3⌉ and d = 2^S − 3^k > 0:

  C(S−1, k−1) < d

The number of admissible compositions is strictly less than the
crystal module, so the evaluation map Ev_d cannot be surjective.

- Difficulty: ★★★
- Strategy:
    1. Stirling bounds: log₂ C(n,m) ≤ n · h(m/n) + O(log n)
    2. Entropy gap: h(1/log₂ 3) = 1 − γ < 1
    3. For k ∈ [18, 500]: certified numerical computation
    4. For k ≥ 500: asymptotic Stirling argument
- Dependencies: `Nat.choose_le_pow_of_lt_half_left`, Stirling in Mathlib -/
theorem crystal_nonsurjectivity (k : ℕ) (hk : k ≥ 18)
    (S : ℕ) (hS : S = Nat.ceil (k * (Real.log 3 / Real.log 2)))
    (hd : crystalModule S k > 0) :
    Nat.choose (S - 1) (k - 1) < (crystalModule S k).toNat := by
  sorry

/-- The three exceptions where C/d ≥ 1.

  - k = 3:  C(4, 2) / d = 6/5 = 1.20
  - k = 5:  C(7, 4) / d = 35/13 ≈ 2.69
  - k = 17: C(26, 16) / d ≈ 1.046

All satisfy k < 68, hence covered by Simons–de Weger.

- Difficulty: ★ (direct computation)
- Strategy: `decide` or `native_decide` -/
theorem exceptions_below_68 :
    ∀ k ∈ ({3, 5, 17} : Finset ℕ),
    let S := Nat.ceil (k * (Real.log 3 / Real.log 2))
    Nat.choose (S - 1) (k - 1) ≥ (crystalModule S k).toNat
    ∧ k < 68 := by
  sorry

-- ============================================================================
-- PART D: Simons–de Weger (External Result)
-- ============================================================================

/-- **Simons–de Weger theorem** (2005).

No nontrivial positive Collatz cycle has length k < 68.

This is accepted as an axiom, justified by:
- Published in Acta Arithmetica 117(1), 2005
- Uses Baker's theory + LLL reduction
- Independently verified by multiple researchers
- The computation is reproducible

- Difficulty: ★★★★★ (formalizing the full proof is a major project)
- Alternative: `native_decide` for individual small k values -/
axiom simons_de_weger :
    ∀ k : ℕ, k ≥ 1 → k < 68 →
    ¬ ∃ (n₀ S : ℕ) (A : Fin k → ℕ),
      n₀ > 0 ∧ crystalModule S k > 0 ∧
      (n₀ : ℤ) * crystalModule S k = ↑(corrSum k A)

-- ============================================================================
-- PART E: The Junction Theorem
-- ============================================================================

/-- **Theorem 2**: Junction (unconditional part).

For every k ≥ 1:
  - If k < 68: no cycle exists (Simons–de Weger)
  - If k ≥ 18 and d > 0: Ev_d is not surjective

The overlap [18, 67] ensures complete coverage.

- Difficulty: ★★ (combination of previous results)
- Strategy: case split on k < 68 vs k ≥ 18 -/
theorem junction_unconditional (k : ℕ) (hk : k ≥ 1) :
    (k < 68 → ¬ ∃ (n₀ S : ℕ) (A : Fin k → ℕ),
      n₀ > 0 ∧ crystalModule S k > 0 ∧
      (n₀ : ℤ) * crystalModule S k = ↑(corrSum k A))
    ∧
    (k ≥ 18 → ∀ S : ℕ,
      S = Nat.ceil (k * (Real.log 3 / Real.log 2)) →
      crystalModule S k > 0 →
      Nat.choose (S - 1) (k - 1) < (crystalModule S k).toNat) := by
  constructor
  · intro hlt
    exact simons_de_weger k hk hlt
  · intro hge S hS hd
    exact crystal_nonsurjectivity k hge S hS hd

/-- **Corollary**: Full coverage of all cycle lengths.

Every k ≥ 1 satisfies k < 68 or k ≥ 18, so at least one
obstruction from the Junction Theorem applies.

- Difficulty: ★ (arithmetic)
- Strategy: `omega` -/
theorem full_coverage (k : ℕ) (hk : k ≥ 1) : k < 68 ∨ k ≥ 18 := by
  omega

-- ============================================================================
-- PART F: Quasi-Uniformity Hypothesis and Conditional Results
-- ============================================================================

/-- The quasi-uniformity hypothesis (H).

For large primes p | d, the evaluation map Ev_p distributes corrSum
approximately uniformly among attainable residues. Formally, for any
nontrivial character χ of 𝔽_p×:

  |Σ_A χ(corrSum(A))| ≤ C(S−1, k−1) · p^{−1/2 + ε}

This is analogous to the Weil bound for exponential sums, adapted to
the Horner-type structure of corrSum. We state it as a hypothesis
(not an axiom) for full transparency. -/
class QuasiUniformity (k S : ℕ) where
  /-- Bound on character sums of corrSum -/
  character_bound : ∀ (p : ℕ) (hp : Nat.Prime p)
    (hdiv : p ∣ (crystalModule S k).toNat), True -- placeholder

/-- **Theorem 3**: Conditional zero-exclusion.

Under hypothesis (H), 0 ∉ Im(Ev_d) for k ≥ 18, hence no positive
cycle exists for any k.

The argument: if C/d < 1, at most C residues are attainable. Under (H),
these are spread quasi-uniformly, so P(0 ∈ Im) ≤ C/d → 0 exponentially.

- Difficulty: ★★ (given H)
- Strategy: Poisson model + (H) gives P(0 ∈ Im) ≤ C/d < 1 -/
theorem zero_exclusion_conditional (k : ℕ) (hk : k ≥ 18)
    (S : ℕ) (hS : S = Nat.ceil (k * (Real.log 3 / Real.log 2)))
    (hd : crystalModule S k > 0)
    [QuasiUniformity k S] :
    ¬ ∃ (A : Fin k → ℕ),
      (Finset.univ.sum A = S - k) ∧
      (corrSum k A) % (crystalModule S k).toNat = 0 := by
  sorry

/-- **Main Theorem** (conditional on H + Simons–de Weger axiom).

There is no nontrivial positive Collatz cycle.

- Difficulty: ★★ (combination)
- Strategy: k < 68 → Simons–de Weger; k ≥ 18 → zero_exclusion -/
theorem no_positive_cycle
    (k : ℕ) (hk : k ≥ 1)
    (S : ℕ) (hS : S = Nat.ceil (k * (Real.log 3 / Real.log 2)))
    (hd : crystalModule S k > 0)
    [inst : ∀ k S, QuasiUniformity k S] :
    ¬ ∃ (n₀ : ℕ) (A : Fin k → ℕ),
      n₀ > 0 ∧
      (Finset.univ.sum A = S - k) ∧
      (n₀ : ℤ) * crystalModule S k = ↑(corrSum k A) := by
  sorry

-- ============================================================================
-- PART G: The Entropy-Module Gap
-- ============================================================================

/-- γ > 0: the entropy-module gap is strictly positive.

Since 1/log₂ 3 ≈ 0.631 ≠ 1/2, we have h(1/log₂ 3) < 1, hence γ > 0.

- Difficulty: ★★
- Strategy: compute h at the specific point using Mathlib real analysis
- Dependencies: `Real.log_lt_log`, properties of binary entropy -/
theorem gamma_pos : gamma > 0 := by
  sorry

/-- The deficit grows linearly: log₂(C/d) ≈ −γ · S + O(log S).

This is the quantitative heart of the nonsurjectivity theorem.

- Difficulty: ★★★
- Strategy: Stirling approximation gives log C ≈ S · h(k/S),
  and log d ≈ S − log(a_{n+1}). The difference is −γS + correction.
- Dependencies: Stirling bounds in Mathlib -/
theorem deficit_linear_growth (k : ℕ) (hk : k ≥ 18) (S : ℕ)
    (hS : S = Nat.ceil (k * (Real.log 3 / Real.log 2))) :
    Real.log (Nat.choose (S - 1) (k - 1)) / Real.log 2 ≤
    (S : ℝ) * (1 - gamma) + Real.log S / Real.log 2 := by
  sorry

-- ============================================================================
-- PART H: Sorry Census
-- ============================================================================

/-!
### Summary of all `sorry` and `axiom` in this file

| ID  | Statement                  | Type   | Difficulty | Resolution path               |
|-----|----------------------------|--------|------------|-------------------------------|
| S1  | steiner_equation           | sorry  | ★★        | Induction on cycle steps      |
| S2  | crystal_nonsurjectivity    | sorry  | ★★★       | Stirling + certified numerics |
| S3  | exceptions_below_68        | sorry  | ★          | `decide` / `native_decide`    |
| A1  | simons_de_weger            | axiom  | ★★★★★     | External (published, 2005)    |
| S4  | zero_exclusion_conditional | sorry  | ★★        | Poisson model under (H)       |
| S5  | no_positive_cycle          | sorry  | ★★        | Combines S1–S4 + A1          |
| S6  | gamma_pos                  | sorry  | ★★        | Numerical/analytic bound      |
| S7  | deficit_linear_growth      | sorry  | ★★★       | Stirling approximation        |

### Critical path to "zero sorry" (excluding axiom A1)

  1. **S3** (exceptions) — easiest, direct `decide` / `native_decide`
  2. **S6** (γ > 0) — needs Mathlib real analysis
  3. **S1** (Steiner) — standard induction on cycle
  4. **S7** (deficit growth) — Stirling bounds from Mathlib
  5. **S2** (nonsurjectivity) — combines S7 + certified numerics for [18, 500]
  6. **S4** (0-exclusion) — needs (H) formalized as character sum bound
  7. **S5** (main theorem) — combines all of the above
-/

end Collatz.JunctionTheorem
