import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Entropy Bound on Binomial Coefficients

Proves the classical bound: for 0 ≤ p ≤ 1 and m ≤ n,
  C(n,m) · p^m · (1-p)^{n-m} ≤ 1

From this we derive:
  C(n,m) ≤ (n/m)^m · (n/(n-m))^{n-m}
  log(C(n,m)) ≤ m·log(n/m) + (n-m)·log(n/(n-m))

## Main results

* `BinomialEntropy.binomial_term_le_one` — each binomial term ≤ 1
* `BinomialEntropy.choose_mul_pow_le_one` — C(n,m)·p^m·(1-p)^{n-m} ≤ 1
* `BinomialEntropy.choose_le_inv_prod` — C(n,m) ≤ 1/(p^m·(1-p)^{n-m})
* `BinomialEntropy.choose_le_div_pow` — C(n,m) ≤ (n/m)^m·(n/(n-m))^{n-m}
* `BinomialEntropy.choose_log_bound` — log(C(n,m)) ≤ m·log(n/m) + (n-m)·log(n/(n-m))
-/

open Finset Real

namespace BinomialEntropy

-- ============================================================================
-- PART A: Core Binomial Bound
-- ============================================================================

/-- The binomial expansion (p + (1-p))^n = 1, rearranged. -/
lemma binomial_sum_eq_one (n : ℕ) (p : ℝ) :
    ∑ k ∈ range (n + 1), p ^ k * (1 - p) ^ (n - k) * (n.choose k : ℝ) = 1 := by
  have h := add_pow p (1 - p) n
  have h1 : p + (1 - p) = 1 := by ring
  rw [h1, one_pow] at h
  exact h.symm

/-- Each term in the binomial expansion is non-negative for 0 ≤ p ≤ 1. -/
lemma binomial_term_nonneg (n k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ p ^ k * (1 - p) ^ (n - k) * (n.choose k : ℝ) :=
  mul_nonneg (mul_nonneg (pow_nonneg hp0 k) (pow_nonneg (sub_nonneg.mpr hp1) (n - k)))
    (Nat.cast_nonneg' _)

/-- **Core bound**: each term of the binomial sum is at most 1.
    Since ∑ terms = 1 and all terms ≥ 0, each individual term ≤ 1. -/
theorem binomial_term_le_one (n m : ℕ) (hm : m ≤ n) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p ^ m * (1 - p) ^ (n - m) * (n.choose m : ℝ) ≤ 1 :=
  calc p ^ m * (1 - p) ^ (n - m) * (n.choose m : ℝ)
      ≤ ∑ k ∈ range (n + 1), p ^ k * (1 - p) ^ (n - k) * (n.choose k : ℝ) :=
        Finset.single_le_sum (fun k _ => binomial_term_nonneg n k p hp0 hp1)
          (Finset.mem_range.mpr (by omega))
    _ = 1 := binomial_sum_eq_one n p

-- ============================================================================
-- PART B: Division Form
-- ============================================================================

/-- Multiplication form: C(n,m) · p^m · (1-p)^{n-m} ≤ 1. -/
theorem choose_mul_pow_le_one (n m : ℕ) (hm : m ≤ n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (n.choose m : ℝ) * (p ^ m * (1 - p) ^ (n - m)) ≤ 1 := by
  have h := binomial_term_le_one n m hm p hp0 hp1
  nlinarith [show p ^ m * (1 - p) ^ (n - m) * (↑(n.choose m) : ℝ) =
    ↑(n.choose m) * (p ^ m * (1 - p) ^ (n - m)) from by ring]

/-- Division form: C(n,m) ≤ 1 / (p^m · (1-p)^{n-m}) for 0 < p < 1. -/
theorem choose_le_inv_prod (n m : ℕ) (hm : m ≤ n)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (n.choose m : ℝ) ≤ 1 / (p ^ m * (1 - p) ^ (n - m)) := by
  have hq : 0 < 1 - p := by linarith
  have hprod : 0 < p ^ m * (1 - p) ^ (n - m) :=
    mul_pos (pow_pos hp0 m) (pow_pos hq (n - m))
  rw [le_div_iff₀ hprod]
  exact choose_mul_pow_le_one n m hm p (le_of_lt hp0) (le_of_lt hp1)

-- ============================================================================
-- PART C: Specialization at p = m/n
-- ============================================================================

/-- Setting p = m/n: C(n,m) ≤ (n/m)^m · (n/(n-m))^{n-m}. -/
theorem choose_le_div_pow (n m : ℕ) (hm0 : 0 < m) (hmn : m < n) :
    (n.choose m : ℝ) ≤ ((n : ℝ) / m) ^ m * ((n : ℝ) / ↑(n - m)) ^ (n - m) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
  have hnm : (0 : ℝ) < ↑(n - m) := Nat.cast_pos.mpr (by omega)
  set prod := ((m : ℝ) / n) ^ m * (↑(n - m) / n) ^ (n - m) with hprod_def
  have hprod_pos : 0 < prod :=
    mul_pos (pow_pos (div_pos hm hn) m) (pow_pos (div_pos hnm hn) (n - m))
  -- C(n,m) * prod ≤ 1 (from binomial_term_le_one with p = m/n)
  have hterm : (↑(n.choose m) : ℝ) * prod ≤ 1 := by
    have h1p : 1 - (m : ℝ) / n = ↑(n - m) / n := by
      rw [Nat.cast_sub (le_of_lt hmn)]; field_simp
    have h := choose_mul_pow_le_one n m (le_of_lt hmn) ((m : ℝ) / n)
      (le_of_lt (div_pos hm hn))
      (le_of_lt (by rw [div_lt_one hn]; exact Nat.cast_lt.mpr hmn))
    rw [h1p] at h; exact h
  -- target * prod = 1 (algebraic identity)
  set target := ((n : ℝ) / m) ^ m * ((n : ℝ) / ↑(n - m)) ^ (n - m) with htarget_def
  have htarget_pos : 0 < target :=
    mul_pos (pow_pos (div_pos hn hm) m) (pow_pos (div_pos hn hnm) (n - m))
  have hmul_one : target * prod = 1 := by
    rw [htarget_def, hprod_def]
    have h1 : ((n : ℝ) / m) ^ m * ((m : ℝ) / n) ^ m = 1 := by
      rw [← mul_pow, div_mul_div_comm, mul_comm (n : ℝ) m, div_self (ne_of_gt (mul_pos hm hn))]
      exact one_pow m
    have h2 : ((n : ℝ) / ↑(n - m)) ^ (n - m) * (↑(n - m) / n) ^ (n - m) = 1 := by
      rw [← mul_pow, div_mul_div_comm, mul_comm (n : ℝ) ↑(n - m),
        div_self (ne_of_gt (mul_pos hnm hn))]
      exact one_pow (n - m)
    nlinarith [show target * prod =
      (((n : ℝ) / m) ^ m * ((m : ℝ) / n) ^ m) *
      (((n : ℝ) / ↑(n - m)) ^ (n - m) * (↑(n - m) / n) ^ (n - m)) from by ring]
  -- Conclude: C(n,m) ≤ target = 1 / prod
  rw [show target = 1 / prod from by
    rw [eq_comm, div_eq_iff (ne_of_gt hprod_pos)]; linarith]
  exact (le_div_iff₀ hprod_pos).mpr hterm

-- ============================================================================
-- PART D: Logarithmic Form
-- ============================================================================

/-- Log bound: log(C(n,m)) ≤ m·log(n/m) + (n-m)·log(n/(n-m)) for 0 < m < n. -/
theorem choose_log_bound (n m : ℕ) (hm0 : 0 < m) (hmn : m < n) :
    Real.log (n.choose m : ℝ) ≤
    (m : ℝ) * Real.log ((n : ℝ) / m) +
    ((n - m : ℕ) : ℝ) * Real.log ((n : ℝ) / ↑(n - m)) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
  have hnm : (0 : ℝ) < ↑(n - m) := Nat.cast_pos.mpr (by omega)
  have hchoose_pos : (0 : ℝ) < (n.choose m : ℝ) := by
    exact_mod_cast Nat.choose_pos (le_of_lt hmn)
  have h := choose_le_div_pow n m hm0 hmn
  have hrhs_pos : 0 < ((n : ℝ) / m) ^ m * ((n : ℝ) / ↑(n - m)) ^ (n - m) :=
    mul_pos (pow_pos (div_pos hn hm) m) (pow_pos (div_pos hn hnm) (n - m))
  have hlog := Real.log_le_log hchoose_pos h
  have hlog_expand : Real.log (((n : ℝ) / m) ^ m * ((n : ℝ) / ↑(n - m)) ^ (n - m)) =
      (m : ℝ) * Real.log ((n : ℝ) / m) +
      ((n - m : ℕ) : ℝ) * Real.log ((n : ℝ) / ↑(n - m)) := by
    rw [Real.log_mul (ne_of_gt (pow_pos (div_pos hn hm) m))
        (ne_of_gt (pow_pos (div_pos hn hnm) (n - m))),
        Real.log_pow, Real.log_pow]
  linarith

-- ============================================================================
-- PART E: Log₂ Entropy Form
-- ============================================================================

/-- Log₂ bound: log₂(C(n,m)) ≤ m·log₂(n/m) + (n-m)·log₂(n/(n-m)).
    This equals n·h₂(m/n) where h₂ is the binary entropy function. -/
theorem choose_log2_bound (n m : ℕ) (hm0 : 0 < m) (hmn : m < n) :
    Real.log (n.choose m : ℝ) / Real.log 2 ≤
    (m : ℝ) * (Real.log ((n : ℝ) / m) / Real.log 2) +
    ((n - m : ℕ) : ℝ) * (Real.log ((n : ℝ) / ↑(n - m)) / Real.log 2) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h := choose_log_bound n m hm0 hmn
  have hdiv := div_le_div_of_nonneg_right h (le_of_lt hlog2)
  linarith [show (↑m * Real.log (↑n / ↑m) + ↑↑(n - m) * Real.log (↑n / ↑↑(n - m))) / Real.log 2 =
    ↑m * (Real.log (↑n / ↑m) / Real.log 2) +
    ↑↑(n - m) * (Real.log (↑n / ↑↑(n - m)) / Real.log 2)
    from by rw [add_div, mul_div_assoc, mul_div_assoc]]

end BinomialEntropy
