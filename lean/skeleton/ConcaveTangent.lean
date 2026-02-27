import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Tangent Line Inequality for Concave Functions

For a concave function f differentiable at x₀:
  f(x) ≤ f(x₀) + f'(x₀) · (x - x₀)

Applied to binary entropy h₂ at any interior point of [0,1].

## Main results

* `ConcaveTangent.concave_le_tangent` — general tangent line bound
* `ConcaveTangent.binEntropy_le_tangent` — h₂(p) ≤ h₂(p₀) + h₂'(p₀)·(p - p₀)
-/

open Real Set

namespace ConcaveTangent

variable {S : Set ℝ} {f : ℝ → ℝ} {f' x₀ y : ℝ}

-- Helper: simplify a⁻¹ * b * a = b when a ≠ 0
private lemma inv_mul_mul_cancel {a b : ℝ} (ha : a ≠ 0) :
    a⁻¹ * b * a = b := by
  rw [mul_comm a⁻¹ b, mul_assoc, inv_mul_cancel₀ ha, mul_one]

/-- Tangent line bound for concave f, case y > x₀. -/
theorem concave_le_tangent_right
    (hfc : ConcaveOn ℝ S f) (hx₀ : x₀ ∈ S) (hy : y ∈ S) (hxy : x₀ < y)
    (hf' : HasDerivAt f f' x₀) :
    f y ≤ f x₀ + f' * (y - x₀) := by
  have hslope := hfc.neg.le_slope_of_hasDerivAt hx₀ hy hxy hf'.neg
  simp only [slope, vsub_eq_sub, smul_eq_mul, Pi.neg_apply] at hslope
  have hpos : (0 : ℝ) < y - x₀ := sub_pos.mpr hxy
  have hmul := mul_le_mul_of_nonneg_right hslope hpos.le
  rw [inv_mul_mul_cancel (ne_of_gt hpos)] at hmul
  linarith

/-- Tangent line bound for concave f, case y < x₀. -/
theorem concave_le_tangent_left
    (hfc : ConcaveOn ℝ S f) (hx₀ : x₀ ∈ S) (hy : y ∈ S) (hxy : y < x₀)
    (hf' : HasDerivAt f f' x₀) :
    f y ≤ f x₀ + f' * (y - x₀) := by
  have hslope := hfc.neg.slope_le_of_hasDerivAt hy hx₀ hxy hf'.neg
  simp only [slope, vsub_eq_sub, smul_eq_mul, Pi.neg_apply] at hslope
  have hpos : (0 : ℝ) < x₀ - y := sub_pos.mpr hxy
  have hmul := mul_le_mul_of_nonneg_right hslope hpos.le
  rw [inv_mul_mul_cancel (ne_of_gt hpos)] at hmul
  linarith

/-- Combined tangent line bound for y ≠ x₀. -/
theorem concave_le_tangent
    (hfc : ConcaveOn ℝ S f) (hx₀ : x₀ ∈ S) (hy : y ∈ S) (hne : y ≠ x₀)
    (hf' : HasDerivAt f f' x₀) :
    f y ≤ f x₀ + f' * (y - x₀) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact concave_le_tangent_left hfc hx₀ hy h hf'
  · exact concave_le_tangent_right hfc hx₀ hy h hf'

/-- Binary entropy tangent line inequality:
    h₂(p) ≤ h₂(p₀) + (log(1-p₀) - log(p₀)) · (p - p₀). -/
theorem binEntropy_le_tangent (p p₀ : ℝ)
    (hp : p ∈ Icc (0 : ℝ) 1) (hp₀ : p₀ ∈ Ioo (0 : ℝ) 1) (hne : p ≠ p₀) :
    binEntropy p ≤ binEntropy p₀ + (log (1 - p₀) - log p₀) * (p - p₀) :=
  concave_le_tangent strictConcave_binEntropy.concaveOn
    (Ioo_subset_Icc_self hp₀) hp hne
    (hasDerivAt_binEntropy (ne_of_gt hp₀.1) (ne_of_lt hp₀.2))

end ConcaveTangent
