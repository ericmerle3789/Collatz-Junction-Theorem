import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Finset.Basic

/-!
# Syracuse Height and the Master Equation

## Overview

This file defines the **Syracuse Height** H(n) and the **Master Equation**
relating the Diophantine gap to the fractional energy along a Collatz cycle.

This formalization accompanies:

  E. Merle, "Entropic Barriers and Nonsurjectivity in the 3x+1 Problem:
  The Junction Theorem", 2026.

## Architecture

The Master Equation is the logarithmic form of Steiner's equation.
It decomposes the cycle constraint into:

  - **Diophantine gap** Δ(k, S) = S·ln(2) − k·ln(3), measuring how
    well S/k approximates log₂ 3
  - **Fractional energy** ε = Σ log(1 + 1/(3·nᵢ)), measuring the
    cumulative "+1" correction

For a cycle to exist: Δ = ε (the gap must exactly match the energy).

## Status

**SKELETON** — all proofs are `sorry`. Each theorem includes a difficulty
assessment and proof strategy note.

## References

- [Steiner1977] R.P. Steiner, "A theorem on the Syracuse problem", 1977
- [Lagarias1985] J.C. Lagarias, "The 3x+1 problem and its generalizations", 1985
-/

namespace Collatz.SyracuseHeight

open Real Finset

-- ============================================================================
-- PART A: Definitions
-- ============================================================================

/-- The Diophantine gap for cycle parameters (k, S).

  Δ(k, S) = S · ln(2) − k · ln(3)

For positive cycles: Δ > 0 (since 2^S > 3^k).
For negative cycles: Δ < 0.
The magnitude |Δ| measures the "slack" in the exponential balance. -/
noncomputable def diophantineGap (k S : ℕ) : ℝ :=
  S * Real.log 2 - k * Real.log 3

/-- The fractional energy of an orbit segment.

  ε({n₀, …, n_{k−1}}) = Σᵢ log(1 + 1/(3·nᵢ))

This measures the cumulative effect of the "+1" in the 3n+1 map.
For large nᵢ, each term ≈ 1/(3·nᵢ) → 0.
For small nᵢ, each term is significant.

The energy is only defined for positive orbit elements. -/
noncomputable def fractionalEnergy {k : ℕ}
    (orbit : Fin k → ℕ) (hpos : ∀ i, orbit i > 0) : ℝ :=
  Finset.univ.sum fun i =>
    Real.log (1 + 1 / (3 * (orbit i : ℝ)))

/-- The Syracuse Height for cycle parameters (k, S) given fractional energy.

  H_{k,S}(ε) = |Δ(k,S)| − |ε|

If H > 0 for all valid (k, S) pairs, then the orbit cannot close
into a cycle: the gap is always too large for the energy to match. -/
noncomputable def syracuseHeight (k S : ℕ) (energy : ℝ) : ℝ :=
  |diophantineGap k S| - |energy|

-- ============================================================================
-- PART B: The Master Equation
-- ============================================================================

/-- **Master Equation** (positive cycles).

If {n₀, …, n_{k−1}} form a positive Collatz cycle with parameters (k, S),
then the Diophantine gap exactly equals the fractional energy:

  Δ(k, S) = Σᵢ log(1 + 1/(3·nᵢ))

This is the logarithmic reformulation of Steiner's equation. It follows
from taking log of the cycle recurrence nᵢ₊₁ = (3·nᵢ + 1) / 2^{aᵢ}
and summing over the cycle (the log(nᵢ) terms telescope).

- Difficulty: ★★
- Strategy: take `Real.log` of `hcycle`, sum over i, telescope
- Dependencies: `Real.log_mul`, `Real.log_pow`, `Finset.sum_congr` -/
theorem master_equation_positive
    (k : ℕ) (hk : k ≥ 1)
    (orbit : Fin k → ℕ) (hpos : ∀ i, orbit i > 0)
    (exponents : Fin k → ℕ) (hexp : ∀ i, exponents i ≥ 1)
    (S : ℕ) (hS : S = Finset.univ.sum exponents)
    (hcycle : ∀ i : Fin k,
      orbit ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩ * 2 ^ (exponents i) =
      3 * orbit i + 1) :
    diophantineGap k S = fractionalEnergy orbit hpos := by
  sorry

/-- **Master Equation** (negative cycles, absolute value form).

For negative integers, the map sends n → (3n+1)/2^a with n < 0,
so |3n+1| = 3|n| − 1 (since n is odd negative). This gives:

  Δ(k, S) = Σᵢ log(1 − 1/(3·|nᵢ|))

Note: the energy terms are now *negative*, matching the negative gap.

- Difficulty: ★★
- Strategy: same telescoping, but with |3n+1| = 3|n| − 1
- Dependencies: same as positive case -/
theorem master_equation_negative
    (k : ℕ) (hk : k ≥ 1)
    (orbit_abs : Fin k → ℕ) (hpos : ∀ i, orbit_abs i ≥ 2)
    (exponents : Fin k → ℕ)
    (S : ℕ) (hS : S = Finset.univ.sum exponents)
    (hcycle_neg : ∀ i : Fin k,
      orbit_abs ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩ * 2 ^ (exponents i) =
      3 * orbit_abs i - 1) :
    diophantineGap k S =
      Finset.univ.sum fun i =>
        Real.log (1 - 1 / (3 * (orbit_abs i : ℝ))) := by
  sorry

-- ============================================================================
-- PART C: Energy Bounds
-- ============================================================================

/-- **Upper bound on fractional energy** (positive cycles).

If n₀ is the minimum of the cycle, then each nᵢ ≥ n₀, so:

  ε ≤ k · log(1 + 1/(3·n₀)) ≤ k/(3·n₀)

using log(1 + x) ≤ x. This gives the "energy pinch":
the energy is at most k/(3·n₀).

- Difficulty: ★
- Strategy: monotonicity of log(1 + 1/(3x)) and log(1+x) ≤ x
- Dependencies: `Real.log_le_sub_one_of_le` -/
theorem energy_upper_bound {k : ℕ}
    (orbit : Fin k → ℕ) (hpos : ∀ i, orbit i > 0)
    (n₀ : ℕ) (hn₀ : n₀ > 0) (hmin : ∀ i, orbit i ≥ n₀) :
    fractionalEnergy orbit hpos ≤ k / (3 * (n₀ : ℝ)) := by
  sorry

/-- **Lower bound on fractional energy** (positive cycles).

The energy is at least k · log(1 + 1/(3·n_max)) where n_max is
the cycle maximum. Combined with the upper bound, this sandwiches
the energy between k/(3·n_max) and k/(3·n₀).

- Difficulty: ★
- Strategy: same monotonicity argument, reversed -/
theorem energy_lower_bound {k : ℕ}
    (orbit : Fin k → ℕ) (hpos : ∀ i, orbit i > 0)
    (n_max : ℕ) (hmax : ∀ i, orbit i ≤ n_max) (hn_max : n_max > 0) :
    fractionalEnergy orbit hpos ≥ k * Real.log (1 + 1 / (3 * (n_max : ℝ))) := by
  sorry

-- ============================================================================
-- PART D: Diophantine Gap and Continued Fractions
-- ============================================================================

/-- **Gap lower bound for non-convergent k**.

If k is not a convergent denominator of log₂ 3, then by Legendre's
theorem (contrapositive), for all integers S:

  |S/k − log₂ 3| ≥ 1/(2k²)

Multiplying by k·ln(2):

  |Δ(k, S)| ≥ ln(2)/(2k)

This is much larger than Baker's bound for convergent k.

- Difficulty: ★★★
- Strategy: contrapositive of Legendre's criterion for convergents
- Dependencies: `Mathlib.NumberTheory.DiophantineApproximation` -/
theorem gap_non_convergent (k S : ℕ) (hk : k ≥ 2)
    (hS : 2 ^ S > 3 ^ k)
    (hnc : True /- placeholder: k is not a convergent denominator -/) :
    |diophantineGap k S| ≥ Real.log 2 / (2 * k) := by
  sorry

/-- **Convergent denominators of log₂ 3** (first 12).

The denominators of the convergents p_n/q_n of log₂ 3:
  q = [1, 1, 2, 5, 12, 41, 53, 306, 665, 15601, 31867, 79335, ...]

These are the "dangerous" values of k where the Diophantine gap
can be very small (of order 1/q_{n+1}). -/
def convergentDenominators_12 : List ℕ :=
  [1, 1, 2, 5, 12, 41, 53, 306, 665, 15601, 31867, 79335]

-- ============================================================================
-- PART E: The Cycle Minimum Bound (Baker Pinch)
-- ============================================================================

/-- **Baker Pinch** (cycle minimum bound).

Combining Baker's lower bound |Δ| ≥ C/k^α with the energy upper
bound ε ≤ k/(3n₀), the Master Equation Δ = ε gives:

  n₀ ≤ k^{α+1} / (3C)

For the best known Baker constants (α = 6), this yields n₀ ≤ k⁷/3.
The result of Simons–de Weger uses α = 6.

- Difficulty: ★★
- Strategy: combine Master Equation + energy bound + Baker bound
- Dependencies: Baker's theorem (external) -/
theorem cycle_minimum_bound
    (k : ℕ) (hk : k ≥ 1) (S : ℕ)
    (orbit : Fin k → ℕ) (hpos : ∀ i, orbit i > 0)
    (n₀ : ℕ) (hn₀ : n₀ > 0) (hmin : ∀ i, orbit i ≥ n₀)
    (hcycle : True /- placeholder for cycle condition -/)
    (hbaker : |diophantineGap k S| ≥ 1 / (k : ℝ) ^ 6)
    (hmaster : diophantineGap k S = fractionalEnergy orbit hpos) :
    (n₀ : ℝ) ≤ (k : ℝ) ^ 7 / 3 := by
  sorry

-- ============================================================================
-- PART F: Summary
-- ============================================================================

/-!
### Sorry Census

| ID | Statement                   | Difficulty | Resolution path                    |
|----|-----------------------------|------------|------------------------------------|
| S1 | master_equation_positive    | ★★        | Log telescoping                    |
| S2 | master_equation_negative    | ★★        | Same with sign flip                |
| S3 | energy_upper_bound          | ★          | Monotonicity + log(1+x) ≤ x       |
| S4 | energy_lower_bound          | ★          | Monotonicity (reversed)            |
| S5 | gap_non_convergent          | ★★★       | Legendre contrapositive (Mathlib)  |
| S6 | cycle_minimum_bound         | ★★        | Combine Master + energy + Baker    |

### Relationship to Junction Theorem

The Syracuse Height framework provides an alternative viewpoint on
the same phenomenon:

- For **non-convergent k**: the large gap |Δ| directly forces n₀
  to be small (bounded by ~k²), well within computational reach.

- For **convergent k** (the "dangerous" cases): the gap is small
  (~1/q_{n+1}), so the energy must also be small, but this is only
  possible if n₀ is extremely large — which then must be reconciled
  with the modular constraint d | corrSum(A).

The Junction Theorem (see `JunctionTheorem.lean`) resolves this
tension by showing the modular constraint becomes impossible:
the number of compositions is too small relative to d.
-/

end Collatz.SyracuseHeight
