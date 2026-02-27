import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Data.Rat.Lemmas

/-!
# Legendre Approximation Bound

From the contrapositive of Legendre's theorem (already in Mathlib):
if q is not a convergent of ξ, then |ξ - q| ≥ 1/(2·q.den²).

## Main results

* `LegendreApprox.abs_sub_ge_of_not_convergent` — Legendre contrapositive (general)
* `LegendreApprox.abs_sub_ge_nat_div` — specialized for S/k with k as denominator bound
-/

open Real

namespace LegendreApprox

-- ============================================================================
-- PART A: Legendre Contrapositive
-- ============================================================================

/-- **Contrapositive of Legendre's theorem**: if a rational q is not
    a convergent of ξ, then |ξ - q| ≥ 1/(2·q.den²).

    Follows directly from `Real.exists_rat_eq_convergent`. -/
theorem abs_sub_ge_of_not_convergent (ξ : ℝ) (q : ℚ)
    (hnc : ∀ n, q ≠ ξ.convergent n) :
    1 / (2 * (q.den : ℝ) ^ 2) ≤ |ξ - ↑q| := by
  by_contra h
  push_neg at h
  obtain ⟨n, hn⟩ := exists_rat_eq_convergent h
  exact absurd hn (hnc n)

-- ============================================================================
-- PART B: Denominator Bound for Integer Ratios
-- ============================================================================

/-- The denominator of the reduced form of S/k divides k. -/
lemma divInt_den_dvd_nat (S k : ℕ) (_hk : 0 < k) :
    (Rat.divInt (↑S) (↑k)).den ∣ k := by
  have h := Rat.den_dvd (↑S : ℤ) (↑k : ℤ)
  exact_mod_cast h

-- ============================================================================
-- PART C: Specialized Bound for Natural Number Ratios
-- ============================================================================

/-- For natural numbers S, k with k ≥ 1, if S/k (as a rational) is not
    a convergent of ξ, then |ξ - S/k| ≥ 1/(2k²). -/
theorem abs_sub_ge_nat_div (ξ : ℝ) (S k : ℕ) (hk : 0 < k)
    (hnc : ∀ n, Rat.divInt (↑S) (↑k) ≠ ξ.convergent n) :
    1 / (2 * (k : ℝ) ^ 2) ≤ |ξ - (S : ℝ) / k| := by
  set q : ℚ := Rat.divInt (↑S) (↑k) with hq_def
  -- Step 1: (q : ℝ) = S / k
  have hq_cast : (q : ℝ) = (S : ℝ) / k := by
    rw [hq_def, Rat.cast_divInt, Int.cast_natCast, Int.cast_natCast]
  -- Step 2: q.den ≤ k (from q.den | k)
  have hden_dvd : q.den ∣ k := divInt_den_dvd_nat S k hk
  have hden_le : (q.den : ℝ) ≤ k :=
    Nat.cast_le.mpr (Nat.le_of_dvd hk hden_dvd)
  -- Step 3: Legendre contrapositive gives |ξ - q| ≥ 1/(2·q.den²)
  have hleg := abs_sub_ge_of_not_convergent ξ q hnc
  rw [hq_cast] at hleg
  -- Step 4: 1/(2k²) ≤ 1/(2·q.den²) since q.den ≤ k
  have hden_pos : (0 : ℝ) < q.den := Nat.cast_pos.mpr q.pos
  calc 1 / (2 * (k : ℝ) ^ 2)
      ≤ 1 / (2 * (q.den : ℝ) ^ 2) := by
        apply div_le_div_of_nonneg_left one_pos.le
          (mul_pos two_pos (sq_pos_of_pos hden_pos))
          (mul_le_mul_of_nonneg_left (sq_le_sq' (by linarith) hden_le) two_pos.le)
    _ ≤ |ξ - (S : ℝ) / k| := hleg

end LegendreApprox
