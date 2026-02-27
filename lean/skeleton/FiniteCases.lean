import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite Case Verification for Crystal Nonsurjectivity

Proves C(S-1, k-1) < 2^S - 3^k for k ∈ [18, 200] by direct computation.

## Method

The **bridge lemma** `ceil_log2_3_eq` converts the real-valued ceiling
`S = ⌈k·log₂3⌉` into decidable integer conditions `2^(S-1) < 3^k < 2^S`.
Then `native_decide` verifies `C(S-1,k-1) < 2^S - 3^k` for each case.

The `close_case` combinator packages the three `native_decide` calls
(two for determining S, one for the binomial comparison) into a single
reusable proof step.

## Compilation Note

This file uses `native_decide` on integers up to ~2^317. Compilation
requires `lake build` with native code generation enabled (the default).
Expected compilation time: 2-5 minutes depending on hardware.
-/

namespace Collatz.FiniteCases

open Real Nat

def crystalModule (S k : ℕ) : ℤ := (2 : ℤ) ^ S - (3 : ℤ) ^ k

-- ============================================================================
-- Bridge Lemma
-- ============================================================================

/-- `2^(S-1) < 3^k < 2^S` implies `S = ⌈k · log₂(3)⌉`. -/
theorem ceil_log2_3_eq (k S : ℕ) (hk : 0 < k) (hS : 0 < S)
    (h_lo : (2 : ℤ) ^ (S - 1) < (3 : ℤ) ^ k)
    (h_hi : (3 : ℤ) ^ k < (2 : ℤ) ^ S) :
    S = Nat.ceil (↑k * (Real.log 3 / Real.log 2)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hval : (0 : ℝ) < ↑k * (Real.log 3 / Real.log 2) := by positivity
  have hup : ↑k * (Real.log 3 / Real.log 2) < (↑S : ℝ) := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hlog2]
    have := Real.log_lt_log (by positivity : (0:ℝ) < (3:ℝ)^k)
      (by exact_mod_cast h_hi : (3:ℝ)^k < (2:ℝ)^S)
    rwa [Real.log_pow, Real.log_pow] at this
  have hdn : (↑S - 1 : ℝ) < ↑k * (Real.log 3 / Real.log 2) := by
    rw [show (↑S - 1 : ℝ) = ((S - 1 : ℕ) : ℝ) from by push_cast; omega]
    rw [div_mul_eq_mul_div, lt_div_iff₀ hlog2]
    have := Real.log_lt_log (by positivity : (0:ℝ) < (2:ℝ)^(S-1))
      (by exact_mod_cast h_lo : (2:ℝ)^(S-1) < (3:ℝ)^k)
    rwa [Real.log_pow, Real.log_pow] at this
  symm; rw [Nat.ceil_eq_iff hval]
  exact ⟨by linarith, le_of_lt hup⟩

-- ============================================================================
-- Case Closer
-- ============================================================================

/-- Given concrete `k₀, S₀` with three `native_decide`-verified conditions,
prove nonsurjectivity for any `S = ⌈k₀·log₂3⌉`. -/
theorem close_case (k₀ S₀ : ℕ) (hk₀ : 0 < k₀) (hS₀ : 0 < S₀)
    (h_lo : (2 : ℤ) ^ (S₀ - 1) < (3 : ℤ) ^ k₀)
    (h_hi : (3 : ℤ) ^ k₀ < (2 : ℤ) ^ S₀)
    (h_lt : Nat.choose (S₀ - 1) (k₀ - 1) < ((2 : ℤ) ^ S₀ - (3 : ℤ) ^ k₀).toNat)
    (S : ℕ) (hS : S = Nat.ceil (↑k₀ * (Real.log 3 / Real.log 2)))
    (hd : crystalModule S k₀ > 0) :
    Nat.choose (S - 1) (k₀ - 1) < (crystalModule S k₀).toNat := by
  have : S = S₀ := by rw [hS]; exact (ceil_log2_3_eq k₀ S₀ hk₀ hS₀ h_lo h_hi).symm
  subst this; exact h_lt

-- ============================================================================
-- Master Theorem
-- ============================================================================

/-- Crystal nonsurjectivity for k ∈ [18, 200]. -/
theorem crystal_nonsurjectivity_le_200 (k : ℕ) (hk : k ≥ 18) (hk_le : k ≤ 200)
    (S : ℕ) (hS : S = Nat.ceil (↑k * (Real.log 3 / Real.log 2)))
    (hd : crystalModule S k > 0) :
    Nat.choose (S - 1) (k - 1) < (crystalModule S k).toNat := by
  interval_cases k
  · exact close_case 18 29 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 19 31 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 20 32 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 21 34 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 22 35 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 23 37 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 24 39 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 25 40 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 26 42 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 27 43 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 28 45 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 29 46 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 30 48 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 31 50 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 32 51 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 33 53 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 34 54 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 35 56 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 36 58 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 37 59 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 38 61 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 39 62 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 40 64 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 41 65 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 42 67 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 43 69 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 44 70 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 45 72 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 46 73 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 47 75 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 48 77 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 49 78 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 50 80 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 51 81 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 52 83 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 53 85 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 54 86 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 55 88 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 56 89 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 57 91 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 58 92 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 59 94 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 60 96 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 61 97 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 62 99 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 63 100 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 64 102 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 65 104 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 66 105 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 67 107 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 68 108 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 69 110 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 70 111 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 71 113 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 72 115 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 73 116 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 74 118 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 75 119 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 76 121 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 77 123 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 78 124 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 79 126 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 80 127 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 81 129 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 82 130 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 83 132 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 84 134 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 85 135 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 86 137 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 87 138 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 88 140 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 89 142 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 90 143 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 91 145 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 92 146 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 93 148 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 94 149 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 95 151 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 96 153 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 97 154 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 98 156 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 99 157 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 100 159 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 101 161 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 102 162 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 103 164 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 104 165 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 105 167 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 106 169 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 107 170 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 108 172 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 109 173 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 110 175 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 111 176 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 112 178 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 113 180 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 114 181 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 115 183 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 116 184 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 117 186 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 118 188 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 119 189 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 120 191 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 121 192 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 122 194 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 123 195 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 124 197 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 125 199 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 126 200 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 127 202 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 128 203 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 129 205 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 130 207 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 131 208 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 132 210 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 133 211 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 134 213 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 135 214 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 136 216 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 137 218 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 138 219 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 139 221 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 140 222 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 141 224 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 142 226 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 143 227 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 144 229 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 145 230 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 146 232 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 147 233 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 148 235 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 149 237 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 150 238 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 151 240 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 152 241 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 153 243 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 154 245 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 155 246 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 156 248 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 157 249 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 158 251 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 159 253 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 160 254 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 161 256 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 162 257 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 163 259 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 164 260 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 165 262 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 166 264 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 167 265 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 168 267 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 169 268 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 170 270 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 171 272 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 172 273 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 173 275 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 174 276 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 175 278 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 176 279 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 177 281 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 178 283 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 179 284 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 180 286 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 181 287 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 182 289 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 183 291 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 184 292 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 185 294 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 186 295 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 187 297 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 188 298 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 189 300 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 190 302 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 191 303 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 192 305 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 193 306 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 194 308 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 195 310 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 196 311 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 197 313 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 198 314 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 199 316 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd
  · exact close_case 200 317 (by omega) (by omega) (by native_decide) (by native_decide) (by native_decide) S (by convert hS using 2; push_cast; ring) hd

end Collatz.FiniteCases