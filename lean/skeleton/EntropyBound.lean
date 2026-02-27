import BinomialEntropy
import ConcaveTangent
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Entropy bound for binomial coefficients via tangent line

## Main results

* `EntropyBound.choose_log_le_binEntropy` — log(C(n,m)) ≤ n · binEntropy(m/n)
* `EntropyBound.log2_div_log32_lt_two` — log 2 / (log 3 - log 2) < 2 (i.e., 8 < 9)
-/

open Real

namespace EntropyBound

-- ============================================================================
-- PART A: log(C(n,m)) ≤ n · binEntropy(m/n)
-- ============================================================================

/-- log(C(n,m)) ≤ n · binEntropy(m/n) for 0 < m < n. -/
theorem choose_log_le_binEntropy (n m : ℕ) (hm0 : 0 < m) (hmn : m < n) :
    log (n.choose m : ℝ) ≤ (n : ℝ) * binEntropy ((m : ℝ) / n) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
  have hnm : (0 : ℝ) < ↑(n - m) := Nat.cast_pos.mpr (by omega)
  have hexpand : (n : ℝ) * binEntropy ((m : ℝ) / n) =
      (m : ℝ) * log ((n : ℝ) / m) + ↑(n - m) * log ((n : ℝ) / ↑(n - m)) := by
    unfold binEntropy
    have h1mp : 1 - (m : ℝ) / n = ↑(n - m) / n := by
      rw [Nat.cast_sub (le_of_lt hmn)]; field_simp
    rw [h1mp]; simp only [inv_div]; field_simp
  rw [hexpand]
  exact BinomialEntropy.choose_log_bound n m hm0 hmn

-- ============================================================================
-- PART B: Key numerical fact: 3 · log 2 < 2 · log 3 (i.e., 8 < 9)
-- ============================================================================

/-- 3 · log 2 < 2 · log 3, equivalently log(8) < log(9). -/
lemma three_log2_lt_two_log3 :
    3 * log 2 < 2 * log 3 := by
  have h1 : log ((2 : ℝ) ^ 3) < log ((3 : ℝ) ^ 2) :=
    log_lt_log (by positivity) (by norm_num : (2:ℝ)^3 < 3^2)
  rw [log_pow, log_pow] at h1; push_cast at h1; linarith

/-- log 2 / (log 3 - log 2) < 2.
    This says p₀/(1-p₀) < 2 where p₀ = log 2 / log 3. -/
lemma log2_div_log32_lt_two :
    log 2 / (log 3 - log 2) < 2 := by
  have hlog2 : (0 : ℝ) < log 2 := log_pos (by norm_num)
  have hlog32 : (0 : ℝ) < log 3 - log 2 := by linarith [three_log2_lt_two_log3]
  rw [div_lt_iff₀ hlog32]; linarith [three_log2_lt_two_log3]

/-- log 2 / log 3 > 1/2, because 4 > 3 so log 4 > log 3, i.e., 2 log 2 > log 3. -/
lemma log2_div_log3_gt_half :
    log 2 / log 3 > 1 / 2 := by
  have hlog3 : (0 : ℝ) < log 3 := log_pos (by norm_num)
  rw [gt_iff_lt, div_lt_div_iff₀ (by norm_num : (0:ℝ) < 2) hlog3]
  have h : log ((3:ℝ)) < log ((2:ℝ) ^ 2) :=
    log_lt_log (by positivity) (by norm_num : (3:ℝ) < 2^2)
  rw [log_pow] at h; push_cast at h; linarith

end EntropyBound
