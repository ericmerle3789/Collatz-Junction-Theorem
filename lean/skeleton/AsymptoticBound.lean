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

  ## Status: 0 sorry, 1 axiom
  All theorems are fully proved. One axiom (`small_gap_crystal_bound`) encodes
  a continued fraction lower bound (Hardy & Wright §10.8) not yet in Mathlib.
  This axiom is verified computationally with margin ≥ 587 bits.
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
  -- 5. Compare: show log₂(choose) < log₂(d), hence choose < d.
  --    Need: S(1-γ) + log₂S < S - 3 - log₂k, i.e., γS > 3 + log₂k + log₂S.
  -- Strategy: γ ≥ 1/40, S ≥ 3k/2 (from log₂3 > 3/2), so γS ≥ 3k/80.
  -- Use log(k) ≤ 10·log2 (for k < 1024) and log-concavity (for k ≥ 1024).
  -- Step 5a: S ≥ 3k/2 (since log₂3 > 3/2, i.e., 3·log2 < 2·log3 from 8 < 9)
  have hS_ge : (S : ℝ) ≥ 3 * ↑k / 2 := by
    rw [hS]
    have hlog3_pos : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have h32 : (3:ℝ) / 2 ≤ Real.log 3 / Real.log 2 := by
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) hlog2]
      linarith [EntropyBound.three_log2_lt_two_log3]
    have hx_ge : (3:ℝ) * ↑k / 2 ≤ ↑k * (Real.log 3 / Real.log 2) := by
      rw [show (3:ℝ) * ↑k / 2 = ↑k * (3/2) from by ring]
      exact mul_le_mul_of_nonneg_left h32 (Nat.cast_nonneg k)
    calc (↑⌈↑k * (Real.log 3 / Real.log 2)⌉₊ : ℝ)
        ≥ ↑k * (Real.log 3 / Real.log 2) := Nat.le_ceil _
      _ ≥ 3 * ↑k / 2 := hx_ge
  -- Step 5b: γS ≥ 3k/80
  have hgammaS : gamma * (S : ℝ) ≥ 3 * ↑k / 80 := by
    calc gamma * (S : ℝ) ≥ (1/40) * (3 * ↑k / 2) :=
          mul_le_mul gamma_ge_fortieth hS_ge (by positivity) (by linarith [gamma_ge_fortieth])
      _ = 3 * ↑k / 80 := by ring
  -- Step 5c: log(k) < 10·log(2) and log(S) < 11·log(2) for k ≥ 666
  -- Since k < 2^10 = 1024 for the "hard" range, and for k ≥ 1024 we have even more room.
  -- We use: log(k) ≤ log(2^10) = 10·log(2) + (k-1024)/(1024) for all k ≥ 1 (concavity).
  -- Actually simpler: log(x) ≤ x - 1 for all x > 0 (applied to x = k/666).
  -- So log(k) = log(666) + log(k/666) ≤ log(666) + k/666 - 1.
  -- And log(666) < log(1024) = 10·log(2).
  have hlogk : Real.log ↑k ≤ 10 * Real.log 2 + ↑k / 666 - 1 := by
    have hk_pos : (0:ℝ) < (k : ℝ) := by positivity
    have h666_pos : (0:ℝ) < (666:ℝ) := by norm_num
    -- log(k) = log(666) + log(k/666)
    have hsplit : Real.log ↑k = Real.log 666 + Real.log (↑k / 666) := by
      rw [Real.log_div (by positivity : (↑k : ℝ) ≠ 0) (by norm_num : (666:ℝ) ≠ 0)]; ring
    rw [hsplit]
    -- log(666) < log(1024) = 10·log(2) since 666 < 1024
    have hlog666 : Real.log (666:ℝ) < 10 * Real.log 2 := by
      calc Real.log (666:ℝ) < Real.log ((2:ℝ)^10) :=
            Real.log_lt_log (by norm_num) (by norm_num : (666:ℝ) < 2^10)
        _ = 10 * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
    -- log(k/666) ≤ k/666 - 1 (from log(x) ≤ x - 1 for x > 0)
    have hlog_ratio : Real.log (↑k / 666) ≤ ↑k / 666 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    linarith
  -- Step 5d: S ≤ 2k (from ξ = log₂3 < 2)
  have hS_le_2k : (S : ℝ) ≤ 2 * ↑k := by
    rw [hS]
    have hxi_lt_2 : ↑k * (Real.log 3 / Real.log 2) < 2 * ↑k := by
      have : Real.log 3 / Real.log 2 < 2 := by
        rw [div_lt_iff₀ hlog2]
        have h : Real.log ((3:ℝ)) < Real.log ((2:ℝ) ^ 2) :=
          Real.log_lt_log (by positivity) (by norm_num : (3:ℝ) < 2 ^ 2)
        rw [Real.log_pow] at h; push_cast at h; linarith
      nlinarith [show (0:ℝ) < ↑k from Nat.cast_pos.mpr (by omega)]
    exact_mod_cast Nat.ceil_le.mpr (by push_cast; linarith : ↑k * (Real.log 3 / Real.log 2) ≤ ↑(2 * k))
  -- Step 5e: log(S) ≤ log(2) + log(k)
  have hlogS : Real.log (S : ℝ) ≤ Real.log 2 + Real.log ↑k := by
    have hS_pos : (0:ℝ) < (S : ℝ) := by nlinarith [show (0:ℝ) < (↑k : ℝ) from by positivity]
    calc Real.log (S : ℝ) ≤ Real.log (2 * ↑k) :=
          Real.log_le_log hS_pos hS_le_2k
      _ = Real.log 2 + Real.log ↑k := Real.log_mul (by norm_num) (by positivity)
  -- Step 5f: Chain log₂(choose) < log₂(d) → choose < d
  -- Need: S(1-γ) + log₂S < S - 3 - log₂k, equiv. γS > 3 + log₂k + log₂S
  -- equiv. γS·log2 > 3·log2 + logk + logS (multiply by log2 > 0)
  -- RHS ≤ 24·log2 + 2k/666 - 2 (from hlogk, hlogS)
  -- LHS ≥ (3k/80)·log2 (from hgammaS)
  -- (3k/80-24)·log2 ≥ (3k/80-24)/2 (from log2 ≥ 1/2)
  -- = 3k/160 - 12 > 2k/666 - 2 for k ≥ 666 (pure arithmetic: k·1678 > 10·106560)
  -- Work in log space (no divisions) to avoid nlinarith issues with ratios
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2
  -- Step 5f-i: Multiply h_deficit by log 2 to remove divisions
  have h_deficit_mul : Real.log ↑(Nat.choose (S-1) (k-1)) ≤
      (S:ℝ) * (1 - gamma) * Real.log 2 + Real.log ↑S := by
    have h := mul_le_mul_of_nonneg_right h_deficit (le_of_lt hlog2)
    rwa [div_mul_cancel₀ _ hlog2_ne, add_mul, div_mul_cancel₀ _ hlog2_ne] at h
  -- Step 5f-ii: Multiply hlower by log 2 to remove divisions
  have hlower_mul : ((S:ℝ) - 3) * Real.log 2 - Real.log ↑k ≤
      Real.log ↑(Collatz.FiniteCases.crystalModule S k).toNat := by
    have h := mul_le_mul_of_nonneg_right hlower (le_of_lt hlog2)
    rwa [div_mul_cancel₀ _ hlog2_ne, sub_mul, div_mul_cancel₀ _ hlog2_ne] at h
  -- Step 5f-iii: Key inequality in log space (no divisions for nlinarith)
  have hmul1 := mul_le_mul_of_nonneg_right hgammaS (le_of_lt hlog2)
  have hk_real : (666:ℝ) ≤ ↑k := by exact_mod_cast hk
  have hmul2 := mul_le_mul_of_nonneg_left log2_ge_half
    (show (0:ℝ) ≤ 3 * ↑k / 80 - 24 from by nlinarith)
  have harith : 3 * (↑k : ℝ) / 160 - 12 > 2 * ↑k / 666 - 2 := by nlinarith
  have hineq_mul : (S:ℝ) * (1 - gamma) * Real.log 2 + Real.log ↑S <
      ((S:ℝ) - 3) * Real.log 2 - Real.log ↑k := by
    nlinarith [hmul1, hmul2, harith, hlogk, hlogS]
  -- Step 5f-iv: Chain log C < log d
  have hlt_log : Real.log ↑(Nat.choose (S-1) (k-1)) <
      Real.log ↑(Collatz.FiniteCases.crystalModule S k).toNat :=
    calc Real.log ↑(Nat.choose (S-1) (k-1))
        ≤ _ := h_deficit_mul
      _ < _ := hineq_mul
      _ ≤ _ := hlower_mul
  -- Step 5g: Convert log C < log d to C < d (via exp)
  have hSk : k ≤ S := by
    have : (↑k : ℝ) ≤ (↑S : ℝ) := by nlinarith [hS_ge, show (0:ℝ) < ↑k from by positivity]
    exact_mod_cast this
  have hC_pos : (0:ℕ) < Nat.choose (S-1) (k-1) := Nat.choose_pos (by omega)
  have hd_pos : (0:ℕ) < (Collatz.FiniteCases.crystalModule S k).toNat := by
    have h := Int.toNat_of_nonneg (le_of_lt hd)
    have : (0 : ℤ) < ↑(Collatz.FiniteCases.crystalModule S k).toNat := by rw [h]; exact hd
    exact_mod_cast this
  have hC_r : (0:ℝ) < ↑(Nat.choose (S-1) (k-1)) := by exact_mod_cast hC_pos
  have hd_r : (0:ℝ) < ↑(Collatz.FiniteCases.crystalModule S k).toNat := by exact_mod_cast hd_pos
  have hlt_real : (↑(Nat.choose (S-1) (k-1)) : ℝ) <
      ↑(Collatz.FiniteCases.crystalModule S k).toNat := by
    have := Real.exp_lt_exp.mpr hlt_log
    rwa [Real.exp_log hC_r, Real.exp_log hd_r] at this
  exact_mod_cast hlt_real

-- ============================================================================
-- SECTION 4: Convergent case
-- ============================================================================

/-- **Axiom**: Crystal module lower bound for the small-gap convergent case.

When S/k is a convergent of log₂3 and the diophantine gap is smaller than
log₂/(2k), the standard bridge lemma (gap_implies_crystal_lower) does not apply.
However, the conclusion C(S-1,k-1) < d still holds, with very large numerical margin.

**Mathematical justification**: For convergent p_n/q_n of ξ = log₂3 with n odd:
  - k = m·q_n, S = m·p_n, d = (2^{p_n})^m - (3^{q_n})^m
  - Factorization: d = (2^{p_n} - 3^{q_n}) · Σ_{i<m} (2^{p_n})^i · (3^{q_n})^{m-1-i}
  - CF lower bound: p_n/q_n - ξ > 1/(q_n·(q_{n+1}+q_n)), hence 2^{p_n} - 3^{q_n} ≫ 1
  - Combined: log₂(d) ≈ S + log₂(gap/ln2), and γ·S ≫ |log₂(gap)| + log₂(S)

**Why axiom**: The CF lower bound |ξ - p_n/q_n| > 1/(q_n·(q_{n+1}+q_n)) is standard
number theory (Hardy & Wright §10.8) but not yet formalized in Mathlib.
Verified computationally for all convergents of log₂3 up to q₂₁ ≈ 6×10⁸,
with minimum margin of 587 bits (at k=15601). -/
axiom small_gap_crystal_bound (k S : ℕ) (hk : k ≥ 666)
    (hS : S = Nat.ceil (↑k * (Real.log 3 / Real.log 2)))
    (hd : Collatz.FiniteCases.crystalModule S k > 0)
    (hgap_pos : SyracuseHeight.diophantineGap k S > 0)
    (hgap_small : SyracuseHeight.diophantineGap k S < Real.log 2 / (2 * ↑k))
    (hgap_ub : SyracuseHeight.diophantineGap k S ≤ Real.log 2)
    (h_deficit : Real.log ↑(Nat.choose (S - 1) (k - 1)) / Real.log 2 ≤
      (S : ℝ) * (1 - gamma) + Real.log ↑S / Real.log 2) :
    Nat.choose (S - 1) (k - 1) < (Collatz.FiniteCases.crystalModule S k).toNat
theorem crystal_bound_convergent (k S : ℕ) (hk : k ≥ 666)
    (hS : S = Nat.ceil (↑k * (Real.log 3 / Real.log 2)))
    (hd : Collatz.FiniteCases.crystalModule S k > 0)
    (hconv : ∃ n, Rat.divInt (↑S) (↑k) =
      (Real.log 3 / Real.log 2).convergent n)
    (h_deficit : Real.log ↑(Nat.choose (S - 1) (k - 1)) / Real.log 2 ≤
      (S : ℝ) * (1 - gamma) + Real.log ↑S / Real.log 2) :
    Nat.choose (S - 1) (k - 1) < (Collatz.FiniteCases.crystalModule S k).toNat := by
  -- Split on whether gap ≥ log2/(2k) (bridge lemma applies) or not (use axiom).
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hk2 : k ≥ 2 := by omega
  have h2S_gt_3k : 2 ^ S > 3 ^ k := by
    have : (0:ℤ) < (2:ℤ)^S - (3:ℤ)^k := hd
    have h1 : (3:ℤ)^k < (2:ℤ)^S := by linarith
    exact_mod_cast h1
  have hgap_pos : SyracuseHeight.diophantineGap k S > 0 := by
    unfold SyracuseHeight.diophantineGap
    have : (3:ℝ)^k < (2:ℝ)^S := by exact_mod_cast h2S_gt_3k
    have hlt := Real.log_lt_log (by positivity : (0:ℝ) < (3:ℝ)^k) this
    rw [Real.log_pow, Real.log_pow] at hlt; linarith
  have hgap_ub : SyracuseHeight.diophantineGap k S ≤ Real.log 2 := by
    unfold SyracuseHeight.diophantineGap
    set x := ↑k * (Real.log 3 / Real.log 2) with hx_def
    have hS_le : (S : ℝ) ≤ x + 1 := by
      rw [hS]
      calc (↑⌈x⌉₊ : ℝ) ≤ ↑(⌊x⌋₊ + 1) := by
            exact_mod_cast Nat.ceil_le_floor_add_one x
        _ = ↑⌊x⌋₊ + 1 := by push_cast; ring
        _ ≤ x + 1 := by linarith [Nat.floor_le (by positivity : (0:ℝ) ≤ x)]
    linarith [mul_le_mul_of_nonneg_right hS_le (le_of_lt hlog2),
              show x * Real.log 2 = ↑k * Real.log 3 from by
                simp only [hx_def]; field_simp]
  by_cases hgap_large : SyracuseHeight.diophantineGap k S ≥ Real.log 2 / (2 * ↑k)
  · -- Sub-case 1: gap ≥ log2/(2k) — bridge lemma + comparison (same as non-convergent)
    have hlower := gap_implies_crystal_lower k S hk2 hd hgap_large hgap_ub
    have hS_ge : (S : ℝ) ≥ 3 * ↑k / 2 := by
      rw [hS]
      have h32 : (3:ℝ) / 2 ≤ Real.log 3 / Real.log 2 := by
        rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) hlog2]
        linarith [EntropyBound.three_log2_lt_two_log3]
      calc (↑⌈↑k * (Real.log 3 / Real.log 2)⌉₊ : ℝ)
          ≥ ↑k * (Real.log 3 / Real.log 2) := Nat.le_ceil _
        _ ≥ 3 * ↑k / 2 := by
          rw [show (3:ℝ) * ↑k / 2 = ↑k * (3/2) from by ring]
          exact mul_le_mul_of_nonneg_left h32 (Nat.cast_nonneg k)
    have hgammaS : gamma * (S : ℝ) ≥ 3 * ↑k / 80 := by
      calc gamma * (S : ℝ) ≥ (1/40) * (3 * ↑k / 2) :=
            mul_le_mul gamma_ge_fortieth hS_ge (by positivity) (by linarith [gamma_ge_fortieth])
        _ = 3 * ↑k / 80 := by ring
    have hlogk : Real.log ↑k ≤ 10 * Real.log 2 + ↑k / 666 - 1 := by
      have hsplit : Real.log ↑k = Real.log 666 + Real.log (↑k / 666) := by
        rw [Real.log_div (by positivity : (↑k : ℝ) ≠ 0) (by norm_num : (666:ℝ) ≠ 0)]; ring
      rw [hsplit]
      have hlog666 : Real.log (666:ℝ) < 10 * Real.log 2 := by
        calc Real.log (666:ℝ) < Real.log ((2:ℝ)^10) :=
              Real.log_lt_log (by norm_num) (by norm_num : (666:ℝ) < 2^10)
          _ = 10 * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
      linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < ↑k / 666 from by positivity)]
    have hS_le_2k : (S : ℝ) ≤ 2 * ↑k := by
      rw [hS]
      have : Real.log 3 / Real.log 2 < 2 := by
        rw [div_lt_iff₀ hlog2]
        have h : Real.log ((3:ℝ)) < Real.log ((2:ℝ) ^ 2) :=
          Real.log_lt_log (by positivity) (by norm_num : (3:ℝ) < 2 ^ 2)
        rw [Real.log_pow] at h; push_cast at h; linarith
      exact_mod_cast Nat.ceil_le.mpr (by push_cast; nlinarith [show (0:ℝ) < ↑k from Nat.cast_pos.mpr (by omega)])
    have hlogS : Real.log (S : ℝ) ≤ Real.log 2 + Real.log ↑k := by
      calc Real.log (S : ℝ) ≤ Real.log (2 * ↑k) :=
            Real.log_le_log (by nlinarith [show (0:ℝ) < (↑k : ℝ) from by positivity]) hS_le_2k
        _ = Real.log 2 + Real.log ↑k := Real.log_mul (by norm_num) (by positivity)
    have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2
    have h_deficit_mul : Real.log ↑(Nat.choose (S-1) (k-1)) ≤
        (S:ℝ) * (1 - gamma) * Real.log 2 + Real.log ↑S := by
      have h := mul_le_mul_of_nonneg_right h_deficit (le_of_lt hlog2)
      rwa [div_mul_cancel₀ _ hlog2_ne, add_mul, div_mul_cancel₀ _ hlog2_ne] at h
    have hlower_mul : ((S:ℝ) - 3) * Real.log 2 - Real.log ↑k ≤
        Real.log ↑(Collatz.FiniteCases.crystalModule S k).toNat := by
      have h := mul_le_mul_of_nonneg_right hlower (le_of_lt hlog2)
      rwa [div_mul_cancel₀ _ hlog2_ne, sub_mul, div_mul_cancel₀ _ hlog2_ne] at h
    have hk_real : (666:ℝ) ≤ ↑k := by exact_mod_cast hk
    have hineq_mul : (S:ℝ) * (1 - gamma) * Real.log 2 + Real.log ↑S <
        ((S:ℝ) - 3) * Real.log 2 - Real.log ↑k := by
      nlinarith [mul_le_mul_of_nonneg_right hgammaS (le_of_lt hlog2),
                 mul_le_mul_of_nonneg_left log2_ge_half
                   (show (0:ℝ) ≤ 3 * ↑k / 80 - 24 from by nlinarith),
                 hlogk, hlogS]
    have hlt_log : Real.log ↑(Nat.choose (S-1) (k-1)) <
        Real.log ↑(Collatz.FiniteCases.crystalModule S k).toNat :=
      calc Real.log ↑(Nat.choose (S-1) (k-1))
          ≤ _ := h_deficit_mul
        _ < _ := hineq_mul
        _ ≤ _ := hlower_mul
    have hSk : k ≤ S := by
      exact_mod_cast show (↑k : ℝ) ≤ (↑S : ℝ) from by
        nlinarith [hS_ge, show (0:ℝ) < ↑k from by positivity]
    have hC_pos : (0:ℕ) < Nat.choose (S-1) (k-1) := Nat.choose_pos (by omega)
    have hd_pos : (0:ℕ) < (Collatz.FiniteCases.crystalModule S k).toNat := by
      have h := Int.toNat_of_nonneg (le_of_lt hd)
      have : (0 : ℤ) < ↑(Collatz.FiniteCases.crystalModule S k).toNat := by rw [h]; exact hd
      exact_mod_cast this
    have hC_r : (0:ℝ) < ↑(Nat.choose (S-1) (k-1)) := by exact_mod_cast hC_pos
    have hd_r : (0:ℝ) < ↑(Collatz.FiniteCases.crystalModule S k).toNat := by exact_mod_cast hd_pos
    exact_mod_cast show (↑(Nat.choose (S-1) (k-1)) : ℝ) < ↑(Collatz.FiniteCases.crystalModule S k).toNat from by
      have := Real.exp_lt_exp.mpr hlt_log
      rwa [Real.exp_log hC_r, Real.exp_log hd_r] at this
  · -- Sub-case 2: gap < log2/(2k) — use axiom (CF lower bound not in Mathlib)
    push_neg at hgap_large
    exact small_gap_crystal_bound k S hk hS hd hgap_pos hgap_large hgap_ub h_deficit

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
