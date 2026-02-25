import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Finset.Basic

/-!
# Syracuse Height and the Master Equation

Formalizes the **Syracuse Height** H(n) and the **Master Equation**
relating the Diophantine gap to the fractional energy along a Collatz cycle.

## Status

Energy bounds and cycle minimum bound fully proved and verified by `lake build`.
Master equations need cyclic sum cancellation argument.
Gap bound for non-convergents needs Legendre's criterion (not in Mathlib).

## Sorry Census (3 sorry remaining)

| ID | Statement              | Status    | Note                          |
|----|------------------------|-----------|-------------------------------|
| S1 | master_equation_pos    | sorry     | Cyclic sum cancellation       |
| S2 | master_equation_neg    | sorry     | Same structure, sign flipped  |
| S3 | energy_upper_bound     | ✓ proved  | log(1+x) ≤ x + monotonicity  |
| S4 | energy_lower_bound     | ✓ proved  | Monotonicity of log(1+1/3x)  |
| S5 | gap_non_convergent     | sorry     | Needs Legendre (not in Mathlib)|
| S6 | cycle_minimum_bound    | ✓ proved  | Cross-multiply + nlinarith    |
-/

namespace Collatz.SyracuseHeight

open Real Finset

-- ============================================================================
-- PART A: Definitions
-- ============================================================================

/-- The Diophantine gap Δ(k, S) = S·ln(2) − k·ln(3). -/
noncomputable def diophantineGap (k S : ℕ) : ℝ :=
  S * Real.log 2 - k * Real.log 3

/-- The fractional energy ε = Σᵢ log(1 + 1/(3·nᵢ)). -/
noncomputable def fractionalEnergy {k : ℕ}
    (orbit : Fin k → ℕ) (hpos : ∀ i, orbit i > 0) : ℝ :=
  Finset.univ.sum fun i =>
    Real.log (1 + 1 / (3 * (orbit i : ℝ)))

/-- The Syracuse Height H = |Δ| − |ε|. -/
noncomputable def syracuseHeight (k S : ℕ) (energy : ℝ) : ℝ :=
  |diophantineGap k S| - |energy|

-- ============================================================================
-- PART B: Auxiliary Lemmas
-- ============================================================================

/-- log(1 + x) ≤ x for all x > -1. Follows from exp(x) ≥ 1 + x. -/
private lemma log_one_add_le {x : ℝ} (hx : -1 < x) : Real.log (1 + x) ≤ x := by
  have h1 : (0 : ℝ) < 1 + x := by linarith
  have h2 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  calc Real.log (1 + x)
      ≤ Real.log (Real.exp x) := Real.log_le_log h1 h2
    _ = x := Real.log_exp x

/-- log(1 + 1/(3n)) is positive for n > 0. -/
private lemma log_one_add_inv_pos {n : ℕ} (hn : n > 0) :
    0 < Real.log (1 + 1 / (3 * (n : ℝ))) := by
  apply Real.log_pos
  have : (0 : ℝ) < 3 * (n : ℝ) := by positivity
  linarith [div_pos (one_pos) this]

/-- log(1 + 1/(3a)) ≤ log(1 + 1/(3b)) when b ≤ a (monotone decreasing). -/
private lemma log_one_add_inv_antitone {a b : ℕ} (ha : a > 0) (hab : b ≤ a)
    (hb : b > 0) :
    Real.log (1 + 1 / (3 * (a : ℝ))) ≤ Real.log (1 + 1 / (3 * (b : ℝ))) := by
  apply Real.log_le_log
  · have : (0 : ℝ) < 3 * (a : ℝ) := by positivity
    linarith [div_pos one_pos this]
  · have ha3 : (0 : ℝ) < 3 * (a : ℝ) := by positivity
    have hb3 : (0 : ℝ) < 3 * (b : ℝ) := by positivity
    have : (b : ℝ) ≤ (a : ℝ) := Nat.cast_le.mpr hab
    have : 3 * (b : ℝ) ≤ 3 * (a : ℝ) := by linarith
    have : 1 / (3 * (a : ℝ)) ≤ 1 / (3 * (b : ℝ)) := by
      apply div_le_div_of_nonneg_left zero_le_one hb3 (by linarith)
    linarith

/-- 1/(3n) > -1 for n > 0 (needed for log_one_add_le). -/
private lemma inv_3n_gt_neg_one {n : ℕ} (hn : n > 0) :
    -1 < 1 / (3 * (n : ℝ)) := by
  have : (0 : ℝ) < 3 * (n : ℝ) := by positivity
  linarith [div_pos one_pos this]

-- ============================================================================
-- PART C: The Master Equation
-- ============================================================================

/-- **Master Equation** (positive cycles).

If {n₀, …, n_{k−1}} form a positive Collatz cycle then
Δ(k, S) = Σᵢ log(1 + 1/(3·nᵢ)).

Proof by telescoping: each cycle step gives
  log(n_{i+1}) + aᵢ·log 2 = log 3 + log(nᵢ) + log(1 + 1/(3nᵢ))
Summing over i and using cyclicity (Σ log nᵢ cancels). -/
theorem master_equation_positive
    (k : ℕ) (hk : k ≥ 1)
    (orbit : Fin k → ℕ) (hpos : ∀ i, orbit i > 0)
    (exponents : Fin k → ℕ) (hexp : ∀ i, exponents i ≥ 1)
    (S : ℕ) (hS : S = Finset.univ.sum exponents)
    (hcycle : ∀ i : Fin k,
      orbit ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩ * 2 ^ (exponents i) =
      3 * orbit i + 1) :
    diophantineGap k S = fractionalEnergy orbit hpos := by
  unfold diophantineGap fractionalEnergy
  have hk_pos : 0 < k := by omega
  -- Define the cyclic shift permutation σ(i) = (i+1) % k
  let σ : Equiv.Perm (Fin k) := {
    toFun := fun i => ⟨(i.val + 1) % k, Nat.mod_lt _ hk_pos⟩
    invFun := fun i => ⟨(i.val + (k - 1)) % k, Nat.mod_lt _ hk_pos⟩
    left_inv := fun ⟨i, hi⟩ => by
      simp only [Fin.mk.injEq]
      by_cases h : i + 1 < k
      · rw [Nat.mod_eq_of_lt h]
        have : i + 1 + (k - 1) = i + k := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
      · have hik : i + 1 = k := by omega
        rw [show (i + 1) % k = 0 from by rw [hik, Nat.mod_self]]
        rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega : k - 1 < k)]
        omega
    right_inv := fun ⟨i, hi⟩ => by
      simp only [Fin.mk.injEq]
      by_cases h : i = 0
      · rw [h, Nat.zero_add, Nat.mod_eq_of_lt (by omega : k - 1 < k)]
        have : k - 1 + 1 = k := by omega
        rw [this, Nat.mod_self]
      · have hi_pos : 0 < i := by omega
        have : i + (k - 1) = (i - 1) + k := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i - 1 < k)]
        have : i - 1 + 1 = i := by omega
        rw [this, Nat.mod_eq_of_lt hi]
  }
  -- Step 1: The log of each cycle step
  have hstep : ∀ i : Fin k,
      Real.log ↑(orbit (σ i)) + ↑(exponents i) * Real.log 2 =
      Real.log 3 + Real.log ↑(orbit i) +
      Real.log (1 + 1 / (3 * (orbit i : ℝ))) := by
    intro i
    have hni := hpos i
    have hn_pos : (0 : ℝ) < orbit i := Nat.cast_pos.mpr hni
    have h3n_pos : (0 : ℝ) < 3 * ↑(orbit i) := by positivity
    have hσi_pos : (0 : ℝ) < orbit (σ i) := Nat.cast_pos.mpr (hpos (σ i))
    have hc := hcycle i
    -- log(orbit(σ i) * 2^aᵢ) = log(3·nᵢ + 1)
    have hlog_eq : Real.log (↑(orbit (σ i)) * (2 : ℝ) ^ exponents i) =
        Real.log (3 * ↑(orbit i) + 1) := by
      congr 1; exact_mod_cast hc
    -- LHS: log(a * b) = log a + log b, then log(2^n) = n * log 2
    rw [Real.log_mul (ne_of_gt hσi_pos)
        (ne_of_gt (by positivity : (0 : ℝ) < (2 : ℝ) ^ exponents i)),
        Real.log_pow] at hlog_eq
    -- RHS: 3n+1 = 3n·(1 + 1/(3n)), then log of product
    have hrhs : Real.log (3 * ↑(orbit i) + 1) =
        Real.log 3 + Real.log ↑(orbit i) +
        Real.log (1 + 1 / (3 * (orbit i : ℝ))) := by
      rw [show (3 : ℝ) * ↑(orbit i) + 1 =
          3 * ↑(orbit i) * (1 + 1 / (3 * ↑(orbit i))) from by field_simp]
      rw [Real.log_mul (ne_of_gt h3n_pos)
          (ne_of_gt (by positivity : (0 : ℝ) < 1 + 1 / (3 * ↑(orbit i)))),
          Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hn_pos)]
    linarith [hlog_eq, hrhs]
  -- Step 2: Sum both sides of hstep, split sums, extract constants
  have hsum : (∑ i, Real.log ↑(orbit (σ i))) +
      (∑ i, ↑(exponents i) * Real.log 2) =
      ↑k * Real.log 3 + (∑ i, Real.log ↑(orbit i)) +
      ∑ i, Real.log (1 + 1 / (3 * (orbit i : ℝ))) := by
    have h := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.card_fin] at h
    linarith
  -- Step 3: Cyclic cancellation — Σ f(σ(i)) = Σ f(i)
  have hcyc : (∑ i, Real.log ↑(orbit (σ i))) =
      ∑ i, Real.log ↑(orbit i) :=
    Equiv.sum_comp σ fun i => Real.log ↑(orbit i)
  -- Step 4: S = Σ exponents
  have hS_eq : (∑ i : Fin k, ↑(exponents i) * Real.log 2) =
      ↑S * Real.log 2 := by
    rw [← Finset.sum_mul]; congr 1
    rw [hS]; push_cast; rfl
  -- Combine: substitute hcyc and hS_eq into hsum, cancel Σ log(orbit i)
  linarith

/-- **Master Equation** (negative cycles). Same telescoping with sign flip. -/
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
  unfold diophantineGap
  have hk_pos : 0 < k := by omega
  -- Define the cyclic shift permutation σ(i) = (i+1) % k
  let σ : Equiv.Perm (Fin k) := {
    toFun := fun i => ⟨(i.val + 1) % k, Nat.mod_lt _ hk_pos⟩
    invFun := fun i => ⟨(i.val + (k - 1)) % k, Nat.mod_lt _ hk_pos⟩
    left_inv := fun ⟨i, hi⟩ => by
      simp only [Fin.mk.injEq]
      by_cases h : i + 1 < k
      · rw [Nat.mod_eq_of_lt h]
        have : i + 1 + (k - 1) = i + k := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
      · have hik : i + 1 = k := by omega
        rw [show (i + 1) % k = 0 from by rw [hik, Nat.mod_self]]
        rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega : k - 1 < k)]
        omega
    right_inv := fun ⟨i, hi⟩ => by
      simp only [Fin.mk.injEq]
      by_cases h : i = 0
      · rw [h, Nat.zero_add, Nat.mod_eq_of_lt (by omega : k - 1 < k)]
        have : k - 1 + 1 = k := by omega
        rw [this, Nat.mod_self]
      · have hi_pos : 0 < i := by omega
        have : i + (k - 1) = (i - 1) + k := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i - 1 < k)]
        have : i - 1 + 1 = i := by omega
        rw [this, Nat.mod_eq_of_lt hi]
  }
  -- Step 1: The log of each cycle step
  have hstep : ∀ i : Fin k,
      Real.log ↑(orbit_abs (σ i)) + ↑(exponents i) * Real.log 2 =
      Real.log 3 + Real.log ↑(orbit_abs i) +
      Real.log (1 - 1 / (3 * (orbit_abs i : ℝ))) := by
    intro i
    have hni := hpos i  -- orbit_abs i ≥ 2
    have hn_pos : (0 : ℝ) < orbit_abs i := by positivity
    have h3n_pos : (0 : ℝ) < 3 * ↑(orbit_abs i) := by positivity
    have hσi_pos : (0 : ℝ) < orbit_abs (σ i) :=
      Nat.cast_pos.mpr (by have := hpos (σ i); omega)
    have hc := hcycle_neg i
    have h3n_ge1 : 1 ≤ 3 * orbit_abs i := by omega
    -- 1 - 1/(3n) > 0 since n ≥ 2
    have h1sub_pos : (0 : ℝ) < 1 - 1 / (3 * ↑(orbit_abs i)) := by
      rw [show (1 : ℝ) - 1 / (3 * ↑(orbit_abs i)) =
          (3 * ↑(orbit_abs i) - 1) / (3 * ↑(orbit_abs i)) from by field_simp]
      apply div_pos _ h3n_pos
      have : (2 : ℝ) ≤ ↑(orbit_abs i) := Nat.cast_le.mpr hni
      linarith
    -- log(orbit_abs(σ i) * 2^aᵢ) = log(3·nᵢ - 1)
    have hlog_eq : Real.log (↑(orbit_abs (σ i)) * (2 : ℝ) ^ exponents i) =
        Real.log (3 * ↑(orbit_abs i) - 1) := by
      congr 1
      have hsub_cast : (↑(3 * orbit_abs i - 1) : ℝ) = 3 * ↑(orbit_abs i) - 1 := by
        rw [Nat.cast_sub h3n_ge1]; push_cast; ring
      rw [← hsub_cast]; exact_mod_cast hc
    -- LHS: log(a * b) = log a + log b, then log(2^n) = n * log 2
    rw [Real.log_mul (ne_of_gt hσi_pos)
        (ne_of_gt (by positivity : (0 : ℝ) < (2 : ℝ) ^ exponents i)),
        Real.log_pow] at hlog_eq
    -- RHS: 3n-1 = 3n·(1 - 1/(3n)), then log of product
    have hrhs : Real.log (3 * ↑(orbit_abs i) - 1) =
        Real.log 3 + Real.log ↑(orbit_abs i) +
        Real.log (1 - 1 / (3 * (orbit_abs i : ℝ))) := by
      rw [show (3 : ℝ) * ↑(orbit_abs i) - 1 =
          3 * ↑(orbit_abs i) * (1 - 1 / (3 * ↑(orbit_abs i))) from by field_simp]
      rw [Real.log_mul (ne_of_gt h3n_pos) (ne_of_gt h1sub_pos),
          Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hn_pos)]
    linarith [hlog_eq, hrhs]
  -- Step 2: Sum both sides of hstep, split sums, extract constants
  have hsum : (∑ i, Real.log ↑(orbit_abs (σ i))) +
      (∑ i, ↑(exponents i) * Real.log 2) =
      ↑k * Real.log 3 + (∑ i, Real.log ↑(orbit_abs i)) +
      ∑ i, Real.log (1 - 1 / (3 * (orbit_abs i : ℝ))) := by
    have h := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.card_fin] at h
    linarith
  -- Step 3: Cyclic cancellation — Σ f(σ(i)) = Σ f(i)
  have hcyc : (∑ i, Real.log ↑(orbit_abs (σ i))) =
      ∑ i, Real.log ↑(orbit_abs i) :=
    Equiv.sum_comp σ fun i => Real.log ↑(orbit_abs i)
  -- Step 4: S = Σ exponents
  have hS_eq : (∑ i : Fin k, ↑(exponents i) * Real.log 2) =
      ↑S * Real.log 2 := by
    rw [← Finset.sum_mul]; congr 1
    rw [hS]; push_cast; rfl
  -- Combine: substitute hcyc and hS_eq into hsum, cancel Σ log(orbit_abs i)
  linarith

-- ============================================================================
-- PART D: Energy Bounds (fully proved)
-- ============================================================================

/-- **Upper bound**: ε ≤ k/(3·n₀). Uses log(1+x) ≤ x and monotonicity. -/
theorem energy_upper_bound {k : ℕ}
    (orbit : Fin k → ℕ) (hpos : ∀ i, orbit i > 0)
    (n₀ : ℕ) (hn₀ : n₀ > 0) (hmin : ∀ i, orbit i ≥ n₀) :
    fractionalEnergy orbit hpos ≤ k / (3 * (n₀ : ℝ)) := by
  unfold fractionalEnergy
  -- Each term: log(1 + 1/(3·nᵢ)) ≤ 1/(3·nᵢ) ≤ 1/(3·n₀)
  have hn₀_pos : (0 : ℝ) < n₀ := Nat.cast_pos.mpr hn₀
  have h3n₀_pos : (0 : ℝ) < 3 * n₀ := by positivity
  -- Each term is ≤ 1/(3·n₀)
  have hterm : ∀ i ∈ Finset.univ,
      Real.log (1 + 1 / (3 * (orbit i : ℝ))) ≤ 1 / (3 * (n₀ : ℝ)) := by
    intro i _
    have hni := hpos i
    have hni_ge := hmin i
    have hni_pos : (0 : ℝ) < orbit i := Nat.cast_pos.mpr hni
    -- Step 1: log(1 + 1/(3nᵢ)) ≤ 1/(3nᵢ) by log(1+x) ≤ x
    have hle1 : Real.log (1 + 1 / (3 * (orbit i : ℝ))) ≤ 1 / (3 * (orbit i : ℝ)) :=
      log_one_add_le (inv_3n_gt_neg_one hni)
    -- Step 2: 1/(3nᵢ) ≤ 1/(3n₀) since nᵢ ≥ n₀
    have hle2 : 1 / (3 * (orbit i : ℝ)) ≤ 1 / (3 * (n₀ : ℝ)) := by
      apply div_le_div_of_nonneg_left zero_le_one h3n₀_pos
      have : (n₀ : ℝ) ≤ (orbit i : ℝ) := Nat.cast_le.mpr hni_ge
      linarith
    linarith
  -- Sum the bound: Σ (1/(3n₀)) = k/(3n₀)
  calc Finset.univ.sum (fun i => Real.log (1 + 1 / (3 * (orbit i : ℝ))))
      ≤ Finset.univ.sum (fun _ => 1 / (3 * (n₀ : ℝ))) := Finset.sum_le_sum hterm
    _ = ↑(Finset.univ.card) * (1 / (3 * (n₀ : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = k * (1 / (3 * (n₀ : ℝ))) := by rw [Finset.card_fin]
    _ = k / (3 * (n₀ : ℝ)) := by ring

/-- **Lower bound**: ε ≥ k · log(1 + 1/(3·n_max)). -/
theorem energy_lower_bound {k : ℕ}
    (orbit : Fin k → ℕ) (hpos : ∀ i, orbit i > 0)
    (n_max : ℕ) (hmax : ∀ i, orbit i ≤ n_max) (hn_max : n_max > 0) :
    fractionalEnergy orbit hpos ≥ k * Real.log (1 + 1 / (3 * (n_max : ℝ))) := by
  unfold fractionalEnergy
  -- Each term: log(1 + 1/(3nᵢ)) ≥ log(1 + 1/(3n_max)) since nᵢ ≤ n_max
  have hterm : ∀ i ∈ Finset.univ,
      Real.log (1 + 1 / (3 * (n_max : ℝ))) ≤
      Real.log (1 + 1 / (3 * (orbit i : ℝ))) := by
    intro i _
    exact log_one_add_inv_antitone hn_max (hmax i) (hpos i)
  rw [ge_iff_le]
  calc ↑k * Real.log (1 + 1 / (3 * (n_max : ℝ)))
      = ↑(Finset.univ.card) * Real.log (1 + 1 / (3 * (n_max : ℝ))) := by
        rw [Finset.card_fin]
    _ = Finset.univ.sum (fun _ => Real.log (1 + 1 / (3 * (n_max : ℝ)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Finset.univ.sum (fun i => Real.log (1 + 1 / (3 * (orbit i : ℝ)))) :=
        Finset.sum_le_sum hterm

-- ============================================================================
-- PART E: Diophantine Gap and Continued Fractions
-- ============================================================================

/-- Convergent denominators of log₂ 3 (first 12). -/
def convergentDenominators_12 : List ℕ :=
  [1, 1, 2, 5, 12, 41, 53, 306, 665, 15601, 31867, 79335]

/-- **Gap lower bound for non-convergent k**.

**Status**: sorry — requires Legendre's criterion for continued fractions,
which is not yet in Mathlib.

**Proof strategy** (not yet formalized):
  By the contrapositive of Legendre's criterion for convergents:
  if k is not a convergent denominator of α, then |α - p/q| ≥ 1/(2q²).
  Applied to α = log₂3, p = S, q = k:
    |log₂3 - S/k| ≥ 1/(2k²)
  Multiplying by k·ln 2: |Δ(k,S)| = k·|S·ln2/k - ln3| ≥ ln2/(2k).
  (Requires: Mathlib.NumberTheory.ContinuedFractions.Legendre, not yet available.) -/
theorem gap_non_convergent (k S : ℕ) (hk : k ≥ 2)
    (hS : 2 ^ S > 3 ^ k)
    (hnc : True /- placeholder: k is not a convergent denominator -/) :
    |diophantineGap k S| ≥ Real.log 2 / (2 * k) := by
  sorry

-- ============================================================================
-- PART F: Cycle Minimum Bound (fully proved from hypotheses)
-- ============================================================================

/-- **Baker Pinch**: combining Master Equation + energy bound + Baker bound
gives n₀ ≤ k⁷/3.

Proof: From Δ = ε and ε ≤ k/(3n₀) and |Δ| ≥ 1/k⁶:
  1/k⁶ ≤ |Δ| = ε ≤ k/(3n₀)
  n₀ ≤ k⁷/3 -/
theorem cycle_minimum_bound
    (k : ℕ) (hk : k ≥ 1) (S : ℕ)
    (orbit : Fin k → ℕ) (hpos : ∀ i, orbit i > 0)
    (n₀ : ℕ) (hn₀ : n₀ > 0) (hmin : ∀ i, orbit i ≥ n₀)
    (hcycle : True /- placeholder for cycle condition -/)
    (hbaker : |diophantineGap k S| ≥ 1 / (k : ℝ) ^ 6)
    (hmaster : diophantineGap k S = fractionalEnergy orbit hpos) :
    (n₀ : ℝ) ≤ (k : ℝ) ^ 7 / 3 := by
  -- From master equation: |Δ| = |ε| = ε (energy is positive)
  have henergy_pos : 0 ≤ fractionalEnergy orbit hpos := by
    unfold fractionalEnergy
    apply Finset.sum_nonneg
    intro i _
    exact le_of_lt (log_one_add_inv_pos (hpos i))
  -- Energy = |Δ| ≥ 1/k⁶
  have h_energy_eq : fractionalEnergy orbit hpos = |diophantineGap k S| := by
    rw [hmaster, abs_of_nonneg henergy_pos]
  -- Energy ≤ k/(3n₀) by upper bound
  have h_energy_le := energy_upper_bound orbit hpos n₀ hn₀ hmin
  -- Combine: 1/k⁶ ≤ |Δ| = ε ≤ k/(3n₀)
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hn₀_pos : (0 : ℝ) < n₀ := Nat.cast_pos.mpr hn₀
  have h3n₀_pos : (0 : ℝ) < 3 * n₀ := by positivity
  -- 1/k⁶ ≤ k/(3n₀)
  have hineq : 1 / (k : ℝ) ^ 6 ≤ k / (3 * (n₀ : ℝ)) := by
    calc 1 / (k : ℝ) ^ 6 ≤ |diophantineGap k S| := hbaker
      _ = fractionalEnergy orbit hpos := h_energy_eq.symm
      _ ≤ k / (3 * (n₀ : ℝ)) := h_energy_le
  -- Cross-multiply: 1·(3·n₀) ≤ k⁶·k = k⁷
  have hk6_pos : (0:ℝ) < (k:ℝ)^6 := by positivity
  -- From 1/k^6 ≤ k/(3n₀), multiply both sides by k^6 * (3n₀) > 0
  have hmul := mul_le_mul_of_nonneg_left hineq (le_of_lt (mul_pos hk6_pos h3n₀_pos))
  have lhs_eq : (k:ℝ)^6 * (3 * ↑n₀) * (1 / (k:ℝ)^6) = 3 * ↑n₀ := by
    field_simp
  have rhs_eq : (k:ℝ)^6 * (3 * ↑n₀) * (↑k / (3 * ↑n₀)) = (k:ℝ)^7 := by
    field_simp
  have h2 : 3 * (n₀ : ℝ) ≤ (k : ℝ) ^ 7 := by nlinarith
  linarith

-- ============================================================================
-- PART G: Summary
-- ============================================================================

/-!
### Sorry Census (3 sorry remaining, verified by lake build)

| ID | Statement              | Status     | Resolution path                    |
|----|------------------------|------------|------------------------------------|
| S1 | master_equation_pos    | sorry      | Cyclic sum bijection in Finset     |
| S2 | master_equation_neg    | sorry      | Same as S1 with sign flip          |
| S3 | energy_upper_bound     | ✓ proved   | log(1+x) ≤ x + Finset.sum_le_sum  |
| S4 | energy_lower_bound     | ✓ proved   | Monotonicity + Finset.sum_le_sum   |
| S5 | gap_non_convergent     | sorry      | Legendre's criterion (not Mathlib) |
| S6 | cycle_minimum_bound    | ✓ proved   | Cross-multiply + nlinarith         |

All energy bounds (S3, S4) and cycle minimum bound (S6) fully proved and verified.
-/

end Collatz.SyracuseHeight
