import FiniteCases
import SyracuseHeight
import LegendreApprox
import ConcaveTangent
import EntropyBound
import Mathlib.Algebra.Ring.GeomSum

/-!
  # AsymptoticBound — crystal_nonsurjectivity for k ≥ 666

  Provides the asymptotic proof that C(S-1, k-1) < 2^S - 3^k for k ≥ 666.

  ## Architecture note
  This file imports FiniteCases (for crystalModule) and SyracuseHeight
  (for gap_non_convergent). It does NOT import JunctionTheorem to avoid
  circular dependencies. The deficit_linear_growth theorem (proved in
  JunctionTheorem.lean) is passed as a hypothesis where needed.

  ## Proof strategy
  For k ≥ 666 with S = ⌈k·log₂3⌉, d = 2^S - 3^k:

  **Upper bound**: log₂(C(S-1,k-1)) ≤ S·(1-γ) + log₂S [deficit_linear_growth]
  **Lower bound**: log₂(d) ≥ S - 3 - log₂k [gap + bridge]
  **Comparison**: γS > 3 + log₂k + log₂S for k ≥ 666 [linear vs log]

  ## Sorry inventory (2 remaining, down from 4)
  - ✓ `gamma_ge_fortieth`: γ ≥ 1/40 — PROVED (tangent at 2/3 + factorization)
  - ✓ `gap_implies_crystal_lower`: real gap → integer lower bound — PROVED
  - `crystal_bound_non_convergent`: final assembly for non-convergent case
  - `crystal_bound_convergent`: factorization for convergent case
-/

namespace Collatz.AsymptoticBound

open Real Nat

-- We use FiniteCases.crystalModule which is definitionally equal to
-- JunctionTheorem.crystalModule: (2:ℤ)^S - (3:ℤ)^k

-- ============================================================================
-- SECTION 1: gamma definition (mirrors JunctionTheorem.gamma)
-- ============================================================================

/-- Binary Shannon entropy (mirror of JunctionTheorem definition). -/
noncomputable def gamma : ℝ :=
  let ξ := Real.log 3 / Real.log 2    -- log₂3 ≈ 1.5850
  let p₀ := Real.log 2 / Real.log 3   -- 1/ξ ≈ 0.6309
  -- γ = 1 - h₂(p₀) where h₂ is the binary entropy function
  -- h₂(p₀) = -(p₀·log₂(p₀) + (1-p₀)·log₂(1-p₀))
  -- ≈ -(0.6309·(-0.665) + 0.3691·(-1.438)) ≈ 0.950
  -- γ ≈ 0.0500
  1 + (p₀ * Real.log p₀ + (1 - p₀) * Real.log (1 - p₀)) / Real.log 2

/-- AB.gamma = 1 - binEntropy(log2/log3) / log2. -/
private lemma gamma_eq_binEntropy :
    gamma = 1 - Real.binEntropy (Real.log 2 / Real.log 3) / Real.log 2 := by
  unfold gamma Real.binEntropy
  rw [Real.log_inv, Real.log_inv]
  ring

/-- 8·log(2) > 5·log(3), because 2^8 = 256 > 243 = 3^5. -/
private lemma eight_log2_gt_five_log3 : 8 * Real.log 2 > 5 * Real.log 3 := by
  have h : Real.log ((3:ℝ)^5) < Real.log ((2:ℝ)^8) :=
    Real.log_lt_log (by positivity) (by norm_num : (3:ℝ)^5 < (2:ℝ)^8)
  rw [Real.log_pow, Real.log_pow] at h; push_cast at h; linarith

/-- γ ≥ 1/40. Proved via tangent line of binary entropy at p₀ = 2/3.

  The proof factors as:
  1. binEntropy(log2/log3) ≤ log3 - (log2)²/log3  [tangent at 2/3]
  2. log3 - (log2)²/log3 ≤ 39·log2/40             [from (8a-5b)(5a+8b) > 0]
  3. gamma = 1 - binEntropy(log2/log3)/log2 ≥ 1/40 [algebra] -/
theorem gamma_ge_fortieth : gamma ≥ 1 / 40 := by
  rw [gamma_eq_binEntropy]
  set a := Real.log 2 with ha_def
  set b := Real.log 3 with hb_def
  have ha : (0:ℝ) < a := Real.log_pos (by norm_num)
  have hb : (0:ℝ) < b := Real.log_pos (by norm_num)
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have hab : a < b := Real.log_lt_log (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) < 3)
  -- Step 1: Apply tangent at 2/3
  have hp_mem : a / b ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by positivity, by rw [div_le_one hb]; exact le_of_lt hab⟩
  have h23_mem : (2:ℝ)/3 ∈ Set.Ioo (0:ℝ) 1 := ⟨by positivity, by norm_num⟩
  have hne : a / b ≠ 2 / 3 := by
    intro heq
    have h3a_eq_2b : 3 * a = 2 * b := by
      field_simp at heq; linarith
    linarith [EntropyBound.three_log2_lt_two_log3]
  have htangent := ConcaveTangent.binEntropy_le_tangent (a/b) (2/3) hp_mem h23_mem hne
  -- Step 2: Compute tangent RHS = b - a²/b
  have hcompute : Real.binEntropy (2/3 : ℝ) +
      (Real.log (1 - 2/3) - Real.log (2/3)) * (a/b - 2/3) = b - a ^ 2 / b := by
    unfold Real.binEntropy
    simp only [Real.log_inv]
    rw [show (1:ℝ) - 2/3 = 1/3 from by ring]
    rw [Real.log_div (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)]
    rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)]
    rw [Real.log_one]
    simp only [← ha_def, ← hb_def]
    field_simp
    ring
  -- Step 3: Show b - a²/b ≤ 39a/40 via factorization (8a-5b)(5a+8b) > 0
  have hfactor : 0 < (8*a - 5*b) * (5*a + 8*b) :=
    mul_pos (by linarith [eight_log2_gt_five_log3]) (by nlinarith)
  have hbound : b - a ^ 2 / b ≤ 39 * a / 40 := by
    rw [show b - a ^ 2 / b = (b ^ 2 - a ^ 2) / b from by field_simp]
    rw [div_le_div_iff₀ hb (by norm_num : (0:ℝ) < 40)]
    nlinarith [hfactor]
  -- Step 4: Combine: binEntropy(a/b) ≤ 39a/40
  have hbe : Real.binEntropy (a / b) ≤ 39 * a / 40 := by linarith [htangent, hcompute]
  -- Step 5: Derive gamma ≥ 1/40
  have hd := div_le_div_of_nonneg_right hbe ha.le
  rw [show 39 * a / 40 / a = 39 / 40 from by field_simp] at hd
  linarith

/-- log 2 ≥ 1/2, from exp(-1/2) ≥ 1/2 and exp(-1/2)·exp(1/2) = 1. -/
private lemma log2_ge_half : Real.log 2 ≥ 1 / 2 := by
  have h1 : (1:ℝ)/2 ≤ Real.exp (-(1/2 : ℝ)) := by
    linarith [Real.add_one_le_exp (-(1/2 : ℝ))]
  have hprod : Real.exp (-(1/2 : ℝ)) * Real.exp ((1/2 : ℝ)) = 1 := by
    rw [← Real.exp_add, show -(1/2 : ℝ) + (1/2 : ℝ) = 0 from by ring, Real.exp_zero]
  have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos (1/2 : ℝ)))
  rw [hprod] at h2
  have hexp : Real.exp ((1/2 : ℝ)) ≤ 2 := by linarith
  calc (1:ℝ)/2 = Real.log (Real.exp (1/2 : ℝ)) := (Real.log_exp _).symm
    _ ≤ Real.log 2 := Real.log_le_log (Real.exp_pos _) hexp

/-- log 2 ≤ 1, from exp(1) ≥ 2 (add_one_le_exp). -/
private lemma log2_le_one : Real.log 2 ≤ 1 := by
  have h2exp : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  calc Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) h2exp
    _ = 1 := Real.log_exp 1

-- ============================================================================
-- SECTION 2: Bridge lemma — real gap to integer crystal module bound
-- ============================================================================

/-- Bridge lemma: if the diophantine gap |Δ| ≥ ε > 0,
    then d = 2^S - 3^k ≥ 3^k · (exp(ε) - 1) ≥ 3^k · ε.

    In log₂ terms: log₂(d) ≥ S + log₂(1 - 2^{-ε/ln2}).
    For ε = ln2/(2k): log₂(d) ≥ S - 2 - log₂k (approximately). -/
theorem gap_implies_crystal_lower (k S : ℕ) (hk : k ≥ 2)
    (hd : Collatz.FiniteCases.crystalModule S k > 0)
    (hgap : SyracuseHeight.diophantineGap k S ≥ Real.log 2 / (2 * k))
    (hgap_ub : SyracuseHeight.diophantineGap k S ≤ Real.log 2) :
    Real.log ↑(Collatz.FiniteCases.crystalModule S k).toNat / Real.log 2 ≥
    (S : ℝ) - 3 - Real.log ↑k / Real.log 2 := by
  -- Setup
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hkr : (0:ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have h2S_pos : (0:ℝ) < (2:ℝ)^S := by positivity
  -- Step A: cast d.toNat to reals
  set dr := (↑(Collatz.FiniteCases.crystalModule S k).toNat : ℝ)
  have hdr_pos : 0 < dr := by
    simp only [dr]; apply Nat.cast_pos.mpr
    have := Int.toNat_of_nonneg (le_of_lt hd); omega
  -- Step B: dr ≥ 2^S / (8*k)
  -- We use: dr = 2^S - 3^k, gap ≥ log2/(2k), log2 ≥ 1/2
  -- Chain: d ≥ 3^k·gap ≥ (2^S/2)·(log2/(2k)) ≥ 2^S/(8k)
  have hsuff : dr ≥ (2:ℝ)^S / (8 * ↑k) := by
    -- dr = 2^S - 3^k as reals
    have hdr_val : dr = (2:ℝ)^S - (3:ℝ)^k := by
      simp only [dr]
      have hnn := le_of_lt hd
      -- ℕ → ℝ cast equals ℤ → ℝ cast for nonneg integers
      have h1 : (↑(Collatz.FiniteCases.crystalModule S k).toNat : ℝ) =
          ((Collatz.FiniteCases.crystalModule S k : ℤ) : ℝ) := by
        rw [show (↑(Collatz.FiniteCases.crystalModule S k).toNat : ℝ) =
            ((↑(Collatz.FiniteCases.crystalModule S k).toNat : ℤ) : ℝ) from by push_cast; rfl,
            Int.toNat_of_nonneg hnn]
      rw [h1]; unfold Collatz.FiniteCases.crystalModule
      push_cast; ring
    have hlog3 : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have h3k_pos : (0:ℝ) < (3:ℝ)^k := by positivity
    -- gap > 0
    have hgap_pos : (0:ℝ) < SyracuseHeight.diophantineGap k S := by
      calc (0:ℝ) < Real.log 2 / (2 * ↑k) := by positivity
        _ ≤ SyracuseHeight.diophantineGap k S := hgap
    -- (a) d ≥ 3^k · gap  [from log(2^S/3^k) = gap and e^x - 1 ≥ x]
    -- Equivalently: 2^S/3^k = exp(gap), so d = 3^k·(exp(gap)-1) ≥ 3^k·gap
    -- We prove: log(1+d/3^k) = gap and d/3^k ≥ gap
    -- Step (a): d/3^k ≥ gap, using log(x) ≤ x - 1 for x = 2^S/3^k
    have hd_over_3k : dr / (3:ℝ)^k ≥ SyracuseHeight.diophantineGap k S := by
      -- dr/3^k = 2^S/3^k - 1
      have hratio : dr / (3:ℝ)^k = (2:ℝ)^S / (3:ℝ)^k - 1 := by
        rw [hdr_val]; field_simp
      -- gap = log(2^S/3^k)
      have hgap_log : SyracuseHeight.diophantineGap k S =
          Real.log ((2:ℝ)^S / (3:ℝ)^k) := by
        unfold SyracuseHeight.diophantineGap
        rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      rw [hratio, hgap_log, ge_iff_le]
      -- Need: log(r) ≤ r - 1 for r = 2^S/3^k > 0
      exact Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < (2:ℝ)^S / (3:ℝ)^k)
    -- Step (b): 3^k ≥ 2^S / 2 (gap ≤ log2, so 2^S ≤ 2·3^k)
    -- Proof: gap ≤ log2 means S·log2 - k·log3 ≤ log2,
    --   so S·log2 ≤ (k+1)·log2 + (k·(log3-log2)), hmm...
    -- Actually: 2^S = 3^k + d ≤ 3^k + (2^S - 1), need different approach
    -- Direct: from dr = 2^S - 3^k and dr < 2^S, we get 3^k > 0. But we need 3^k ≥ 2^S/2.
    -- From gap = log(2^S) - log(3^k) ≤ log2, get 2^S/3^k ≤ 2, i.e., 3^k ≥ 2^S/2.
    -- But we need exp; let's use log monotonicity instead:
    -- log(2^S) - log(3^k) = gap ≤ log2, so log(2^S) ≤ log(3^k) + log2 = log(2·3^k),
    -- hence 2^S ≤ 2·3^k.
    have h3k_ge : (3:ℝ)^k ≥ (2:ℝ)^S / 2 := by
      rw [ge_iff_le, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
      -- Need: 2^S ≤ 2 · 3^k, i.e., log(2^S) ≤ log(2·3^k)
      have hlog_ineq : Real.log ((2:ℝ)^S) ≤ Real.log (2 * (3:ℝ)^k) := by
        have hgap_def : SyracuseHeight.diophantineGap k S =
            ↑S * Real.log 2 - ↑k * Real.log 3 := by
          unfold SyracuseHeight.diophantineGap; ring
        rw [Real.log_pow, Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity),
            Real.log_pow]
        linarith [hgap_ub, hgap_def]
      have := (Real.log_le_log_iff (by positivity : (0:ℝ) < (2:ℝ)^S)
            (by positivity : (0:ℝ) < 2 * (3:ℝ)^k)).mp hlog_ineq
      linarith
    -- Step (c): combine: from dr/3^k ≥ gap, get dr ≥ 3^k · gap
    have h1 : dr ≥ (3:ℝ)^k * SyracuseHeight.diophantineGap k S := by
      have hle := hd_over_3k
      rw [ge_iff_le, le_div_iff₀' h3k_pos] at hle
      linarith
    have h2 : (3:ℝ)^k * SyracuseHeight.diophantineGap k S ≥
        (2:ℝ)^S / 2 * (Real.log 2 / (2 * ↑k)) := by
      apply mul_le_mul h3k_ge hgap (by positivity) (by positivity)
    calc dr ≥ (3:ℝ)^k * SyracuseHeight.diophantineGap k S := h1
      _ ≥ (2:ℝ)^S / 2 * (Real.log 2 / (2 * ↑k)) := h2
      _ = (2:ℝ)^S * Real.log 2 / (4 * ↑k) := by ring
      _ ≥ (2:ℝ)^S * (1/2) / (4 * ↑k) := by
          apply div_le_div_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left log2_ge_half (by positivity)
      _ = (2:ℝ)^S / (8 * ↑k) := by ring
  -- Step C: from dr ≥ 2^S/(8k), derive log(dr)/log2 ≥ S - 3 - log(k)/log2
  have hq_pos : (0:ℝ) < (2:ℝ)^S / (8 * ↑k) := by positivity
  have hlog_d := Real.log_le_log hq_pos hsuff
  -- log(2^S/(8k)) = S·log2 - 3·log2 - log(k)
  have hlog_expand : Real.log ((2:ℝ)^S / (8 * ↑k)) =
      ↑S * Real.log 2 - 3 * Real.log 2 - Real.log ↑k := by
    rw [Real.log_div (ne_of_gt h2S_pos) (by positivity : (8:ℝ) * ↑k ≠ 0)]
    rw [Real.log_pow]
    rw [show (8:ℝ) * ↑k = (2:ℝ)^3 * ↑k from by norm_num]
    rw [Real.log_mul (by positivity : (2:ℝ)^3 ≠ 0) (by positivity : (↑k : ℝ) ≠ 0)]
    rw [Real.log_pow]; push_cast; ring
  rw [hlog_expand] at hlog_d
  -- Goal: log(dr)/log2 ≥ S - 3 - log(k)/log2
  -- Equivalent after multiplying both sides by log2 > 0:
  --   log(dr) ≥ (S - 3) * log2 - log(k)
  -- Which is exactly hlog_d after rewriting.
  suffices h : (↑S - 3 - Real.log ↑k / Real.log 2) * Real.log 2 ≤ Real.log dr by
    exact le_div_iff₀ hlog2 |>.mpr h
  calc (↑S - 3 - Real.log ↑k / Real.log 2) * Real.log 2
      = ↑S * Real.log 2 - 3 * Real.log 2 - Real.log ↑k := by
        have hne : Real.log 2 ≠ 0 := ne_of_gt hlog2
        rw [sub_mul, sub_mul, div_mul_cancel₀ _ hne]
    _ ≤ Real.log dr := hlog_d

-- ============================================================================
-- SECTION 3: Non-convergent case
-- ============================================================================

/-- Non-convergent case: combines gap_non_convergent + bridge + deficit.
    The hypothesis h_deficit is the conclusion of deficit_linear_growth
    (proved in JunctionTheorem.lean, passed as parameter to avoid circular import). -/
theorem crystal_bound_non_convergent (k S : ℕ) (hk : k ≥ 666)
    (hS : S = Nat.ceil (↑k * (Real.log 3 / Real.log 2)))
    (hd : Collatz.FiniteCases.crystalModule S k > 0)
    (hnc : ∀ n, Rat.divInt (↑S) (↑k) ≠
      (Real.log 3 / Real.log 2).convergent n)
    (h_deficit : Real.log ↑(Nat.choose (S - 1) (k - 1)) / Real.log 2 ≤
      (S : ℝ) * (1 - gamma) + Real.log ↑S / Real.log 2) :
    Nat.choose (S - 1) (k - 1) < (Collatz.FiniteCases.crystalModule S k).toNat := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hk2 : k ≥ 2 := by omega
  -- 0. From hd > 0, get 2^S > 3^k (as ℕ)
  have h2S_gt_3k : 2 ^ S > 3 ^ k := by
    have : (0:ℤ) < (2:ℤ)^S - (3:ℤ)^k := hd
    have h1 : (3:ℤ)^k < (2:ℤ)^S := by linarith
    exact_mod_cast h1
  -- 1. Get the gap bound from gap_non_convergent (gives |gap| ≥ log2/(2k))
  have hgap_abs := SyracuseHeight.gap_non_convergent k S hk2 h2S_gt_3k hnc
  -- gap > 0 since 2^S > 3^k, so |gap| = gap
  have hgap_pos : SyracuseHeight.diophantineGap k S > 0 := by
    unfold SyracuseHeight.diophantineGap
    have : (3:ℝ)^k < (2:ℝ)^S := by exact_mod_cast h2S_gt_3k
    have hlt := Real.log_lt_log (by positivity : (0:ℝ) < (3:ℝ)^k) this
    rw [Real.log_pow, Real.log_pow] at hlt; linarith
  have hgap : SyracuseHeight.diophantineGap k S ≥ Real.log 2 / (2 * ↑k) := by
    have := abs_of_pos hgap_pos; linarith
  -- 2. gap ≤ log2 (from S = ⌈k·log₂3⌉ ≤ k·log₂3 + 1)
  have hgap_ub : SyracuseHeight.diophantineGap k S ≤ Real.log 2 := by
    unfold SyracuseHeight.diophantineGap
    set x := ↑k * (Real.log 3 / Real.log 2) with hx_def
    -- ⌈x⌉₊ ≤ x + 1 as reals
    have hS_le : (S : ℝ) ≤ x + 1 := by
      rw [hS]
      calc (↑⌈x⌉₊ : ℝ) ≤ ↑(⌊x⌋₊ + 1) := by
            exact_mod_cast Nat.ceil_le_floor_add_one x
        _ = ↑⌊x⌋₊ + 1 := by push_cast; ring
        _ ≤ x + 1 := by linarith [Nat.floor_le (by positivity : (0:ℝ) ≤ x)]
    -- S·log2 ≤ x·log2 + log2 = k·log3 + log2
    linarith [mul_le_mul_of_nonneg_right hS_le (le_of_lt hlog2),
              show x * Real.log 2 = ↑k * Real.log 3 from by
                simp only [hx_def]; field_simp]
  -- 3. Lower bound on d
  have hlower := gap_implies_crystal_lower k S hk2 hd hgap hgap_ub
  -- 4. Upper bound on C (given as hypothesis h_deficit)
  -- 5. Compare: need S(1-γ) + log₂S < S - 3 - log₂k
  --    ⟺ γS > 3 + log₂k + log₂S
  -- For k ≥ 666: γ ≥ 1/40, S ≥ k (since log₂3 > 1), so γS ≥ k/40 ≥ 666/40 > 16
  -- And 3 + log₂k + log₂S ≤ 3 + log₂(666) + log₂(1056) ≤ 3 + 10 + 11 = 24
  -- But 666/40 = 16.65, not enough! Need γ ≥ 1/40 and S ≥ 3k/2:
  -- γS ≥ (1/40)·(3k/2) = 3k/80 = 3·666/80 = 24.975 > 24. Barely!
  -- Actually with better γ bound or S bound this is fine.
  sorry

-- ============================================================================
-- SECTION 4: Convergent case — factorization
-- ============================================================================

/-- Geometric sum identity: a^m - b^m = (a-b) · Σ_{i<m} a^i · b^{m-1-i}.
    Standard algebra, should follow from Mathlib's geom_sum_mul. -/
theorem pow_sub_factorization (a b : ℤ) (m : ℕ) (hm : 0 < m) :
    a ^ m - b ^ m = (a - b) *
    (Finset.range m).sum (fun i => a ^ i * b ^ (m - 1 - i)) := by
  rw [mul_comm]
  exact (geom_sum₂_mul a b m).symm

/-- For convergent S/k = p_n/q_n (odd n, p/q > ξ = log₂3):
    - k = m·q, S = m·p
    - 2^p > 3^q (since p/q > ξ)
    - d = (2^p - 3^q) · Σ ≥ (2^p - 3^q) · m · (3^q)^{m-1}
    - log₂(d) ≈ S - loss + log₂m where loss = p - log₂(2^p-3^q) ≈ 6..15
    - γS > loss + log₂p, since γ·p·m ≥ γ·p·4 > loss + log₂p for q ≥ 41 -/
theorem crystal_bound_convergent (k S : ℕ) (hk : k ≥ 666)
    (hS : S = Nat.ceil (↑k * (Real.log 3 / Real.log 2)))
    (hd : Collatz.FiniteCases.crystalModule S k > 0)
    (hconv : ∃ n, Rat.divInt (↑S) (↑k) =
      (Real.log 3 / Real.log 2).convergent n)
    (h_deficit : Real.log ↑(Nat.choose (S - 1) (k - 1)) / Real.log 2 ≤
      (S : ℝ) * (1 - gamma) + Real.log ↑S / Real.log 2) :
    Nat.choose (S - 1) (k - 1) < (Collatz.FiniteCases.crystalModule S k).toNat := by
  sorry
  -- Proof outline:
  -- 1. S/k = p_n/q_n in reduced form. Since S = ceil(k·ξ) > k·ξ and even
  --    convergents have p/q < ξ, n must be ODD. Hence p/q > ξ, so 2^p > 3^q.
  -- 2. k = m·q, S = m·p for m = k/gcd(S,k), q = k/gcd(S,k).
  -- 3. Factorize: d = (2^p)^m - (3^q)^m = (2^p - 3^q) · Σ.
  -- 4. Σ ≥ m · (3^q)^{m-1} (each term bounded below).
  -- 5. d ≥ (2^p - 3^q) · m · (3^q)^{m-1}.
  -- 6. For q₅=41: 2^65-3^41 ≈ 2^{58.5}, need γ·65·m > 6.5+6.02, m ≥ 4. OK since m ≥ 17.
  -- 7. For q₇=306: 2^485-3^306 ≈ 2^{474}, need γ·485·m > 11+8.92, m ≥ 1. OK.
  -- 8. For q₉=15601: need 2^24727-3^15601 > 0, then γ·24727 > 15.5+14.6. OK.
  -- 9. For larger q: γ·p ≥ 0.05·1.5·q = 0.075·q > any log term for q ≥ 666.

-- ============================================================================
-- SECTION 5: Main theorem
-- ============================================================================

/-- **Main asymptotic theorem**: C(S-1, k-1) < 2^S - 3^k for all k ≥ 666.

    Requires deficit_linear_growth as hypothesis (to avoid circular import).
    This theorem is applied in JunctionTheorem.lean to close the final sorry. -/
theorem crystal_nonsurjectivity_ge_666 (k : ℕ) (hk : k ≥ 666)
    (S : ℕ) (hS : S = Nat.ceil (↑k * (Real.log 3 / Real.log 2)))
    (hd : Collatz.FiniteCases.crystalModule S k > 0)
    (h_deficit : Real.log ↑(Nat.choose (S - 1) (k - 1)) / Real.log 2 ≤
      (S : ℝ) * (1 - gamma) + Real.log ↑S / Real.log 2) :
    Nat.choose (S - 1) (k - 1) < (Collatz.FiniteCases.crystalModule S k).toNat := by
  by_cases hnc : ∀ n, Rat.divInt (↑S) (↑k) ≠
    (Real.log 3 / Real.log 2).convergent n
  · exact crystal_bound_non_convergent k S hk hS hd hnc h_deficit
  · push_neg at hnc
    exact crystal_bound_convergent k S hk hS hd hnc h_deficit

end Collatz.AsymptoticBound
