import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Fin
import BinomialEntropy

/-!
# Junction Theorem for Collatz Positive Cycles

Formalizes the **Junction Theorem** (Merle, 2026) combining:
  **(A)** Simons–de Weger (2005): no positive cycle with k < 68
  **(B)** Crystal nonsurjectivity: for k ≥ 18 with d > 0, C(S−1, k−1) < d

## Sorry Census (2 sorry remaining)

| ID  | Statement                  | Status    | Note                              |
|-----|----------------------------|-----------|-----------------------------------|
| S1  | steiner_equation           | ✓ proved  | Cyclic telescoping + linear_comb  |
| S2  | crystal_nonsurjectivity    | sorry     | Entropy tools ready, needs gap    |
| S3  | exceptions_below_68        | ✓ proved  | native_decide computation         |
| A1  | simons_de_weger            | axiom     | External published result (2005)  |
| S4  | zero_exclusion_conditional | ✓ proved  | From QuasiUniformity class        |
| S5  | no_positive_cycle          | ✓ proved  | Int/Nat dvd bridge via Mathlib    |
| S6  | gamma_pos                  | ✓ proved  | From binEntropy_lt_log_two        |
| S7  | deficit_linear_growth      | sorry     | Concavity of h₂ + deriv bound    |
| H1  | binary_entropy_lt_one      | ✓ proved  | Via Mathlib binEntropy_lt_log_two |
-/

namespace Collatz.JunctionTheorem

open Real Finset Nat

-- ============================================================================
-- PART A: Core Definitions
-- ============================================================================

/-- A composition of S − k into k nonneg parts with A₀ = 0. -/
structure Composition (S k : ℕ) where
  A : Fin k → ℕ
  hA0 : (hk : k > 0) → A ⟨0, hk⟩ = 0
  hSum : Finset.univ.sum A = S - k
  hSgtk : S > k

/-- The crystal module d = 2^S − 3^k. -/
def crystalModule (S k : ℕ) : ℤ := (2 : ℤ) ^ S - (3 : ℤ) ^ k

/-- The corrective sum corrSum(A) = Σᵢ 3^{k−1−i} · 2^{Aᵢ}. -/
def corrSum (k : ℕ) (A : Fin k → ℕ) : ℕ :=
  Finset.univ.sum fun i => 3 ^ (k - 1 - i.val) * 2 ^ (A i)

/-- The evaluation map Ev_d : Comp(S, k) → ℤ/dℤ. -/
def evalMap (S k : ℕ) (A : Fin k → ℕ) (hd : crystalModule S k > 0) :
    ZMod (crystalModule S k).toNat :=
  ↑(corrSum k A)

/-- Binary Shannon entropy: h(p) = −p log₂ p − (1−p) log₂(1−p). -/
noncomputable def binaryEntropy (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) : ℝ :=
  -(p * Real.log p / Real.log 2 +
    (1 - p) * Real.log (1 - p) / Real.log 2)

/-- The entropy-module gap γ = 1 − h(1/log₂ 3) ≈ 0.0500. -/
private lemma log2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
private lemma log3_pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num : (1:ℝ) < 3)

private lemma log2_div_log3_pos : (0 : ℝ) < Real.log 2 / Real.log 3 :=
  div_pos log2_pos log3_pos

private lemma log2_div_log3_lt_one : Real.log 2 / Real.log 3 < 1 := by
  rw [div_lt_one log3_pos]
  exact Real.log_lt_log (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) < 3)

noncomputable def gamma : ℝ :=
  1 - binaryEntropy (1 / (Real.log 3 / Real.log 2))
    (by rw [one_div, inv_div]; exact log2_div_log3_pos)
    (by rw [one_div, inv_div]; exact log2_div_log3_lt_one)

-- ============================================================================
-- PART B: Positive Collatz Cycle Definition
-- ============================================================================

/-- A positive Collatz cycle of length k. Each odd step applies
    n ↦ (3n+1)/2^{aᵢ}. -/
structure IsPositiveCollatzCycle (k : ℕ) where
  orbit : Fin k → ℕ
  exponents : Fin k → ℕ
  hk : k ≥ 1
  hpos : ∀ i, orbit i > 0
  hexp : ∀ i, exponents i ≥ 1
  S : ℕ
  hS : S = Finset.univ.sum exponents
  hcycle : ∀ i : Fin k,
    orbit ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩ * 2 ^ (exponents i) =
    3 * orbit i + 1

-- ============================================================================
-- PART C: Steiner's Equation
-- ============================================================================

/-- **Steiner's equation** (1977): n₀ · (2^S − 3^k) = corrSum(A).

For a proper Collatz cycle, this follows by induction on the number
of odd steps, accumulating the telescoping product.

The key identity at each step i:
  n_{i+1} · 2^{aᵢ} = 3·nᵢ + 1
After k steps, multiplying through:
  n₀ · 2^S = 3^k · n₀ + Σᵢ 3^{k−1−i} · 2^{Aᵢ}
where Aᵢ = Σ_{j<i} aⱼ is the cumulative exponent. -/
theorem steiner_equation (k : ℕ) (cyc : IsPositiveCollatzCycle k)
    (cumA : Fin k → ℕ)
    (hcumA : ∀ i : Fin k, cumA i =
      (Finset.filter (fun j : Fin k => j.val < i.val) Finset.univ).sum
      cyc.exponents)
    (n₀ : ℕ) (hn₀ : n₀ = cyc.orbit ⟨0, by have := cyc.hk; omega⟩) :
    (n₀ : ℤ) * crystalModule cyc.S k = ↑(corrSum k cumA) := by
  unfold crystalModule corrSum
  have hk_pos : 0 < k := by have := cyc.hk; omega
  -- Reduce to: n₀ * 2^S = n₀ * 3^k + corrSum
  suffices hsuff : (↑n₀ : ℤ) * (2 : ℤ) ^ cyc.S =
      ↑n₀ * (3 : ℤ) ^ k +
      ↑(Finset.univ.sum fun i : Fin k => 3 ^ (k - 1 - i.val) * 2 ^ cumA i) by
    push_cast at hsuff ⊢; linarith
  -- ===== Auxiliary: cumA properties =====
  have hcumA0 : cumA ⟨0, hk_pos⟩ = 0 := by
    rw [hcumA]; apply Finset.sum_eq_zero
    intro ⟨j, _⟩ hj; simp at hj
  have hcumA_succ : ∀ m (hm1 : m + 1 < k),
      cumA ⟨m + 1, hm1⟩ = cumA ⟨m, by omega⟩ + cyc.exponents ⟨m, by omega⟩ := by
    intro m hm1; rw [hcumA, hcumA]
    have hfilt : Finset.filter (fun j : Fin k => j.val < m + 1) Finset.univ =
        insert ⟨m, by omega⟩ (Finset.filter (fun j : Fin k => j.val < m) Finset.univ) := by
      ext ⟨j, hj⟩; simp [Finset.mem_filter, Finset.mem_insert, Fin.ext_iff]; omega
    rw [hfilt, Finset.sum_insert (by simp [Finset.mem_filter])]
    ring
  have hcumA_last : cumA ⟨k - 1, by omega⟩ + cyc.exponents ⟨k - 1, by omega⟩ = cyc.S := by
    rw [hcumA, cyc.hS]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin k => j.val < k - 1)]
    congr 1
    have : Finset.filter (fun j : Fin k => ¬j.val < k - 1) Finset.univ =
        {⟨k - 1, by omega⟩} := by
      ext ⟨j, hj⟩; simp [Finset.mem_filter, Finset.mem_singleton, Fin.ext_iff]; omega
    rw [this, Finset.sum_singleton]
  -- ===== Define telescoping function =====
  let f : ℕ → ℤ := fun m =>
    if hm : m < k then
      ↑(cyc.orbit ⟨m, hm⟩) * (3 : ℤ) ^ (k - m) * (2 : ℤ) ^ (cumA ⟨m, hm⟩)
    else ↑n₀ * (2 : ℤ) ^ cyc.S
  have hf0 : f 0 = ↑n₀ * (3 : ℤ) ^ k := by
    simp only [f, dif_pos hk_pos, hcumA0, pow_zero, mul_one, Nat.sub_zero, hn₀]
  have hfk : f k = ↑n₀ * (2 : ℤ) ^ cyc.S := by
    simp only [f, dif_neg (lt_irrefl k)]
  -- ===== Step identity =====
  have hstep_f : ∀ i (hi : i < k),
      f (i + 1) - f i = (3 : ℤ) ^ (k - 1 - i) * (2 : ℤ) ^ (cumA ⟨i, hi⟩) := by
    intro i hi
    have hfi : f i = ↑(cyc.orbit ⟨i, hi⟩) * (3 : ℤ) ^ (k - i) *
        (2 : ℤ) ^ (cumA ⟨i, hi⟩) := dif_pos hi
    have hcyc_z : (↑(cyc.orbit ⟨(i + 1) % k, Nat.mod_lt _ hk_pos⟩) : ℤ) *
        (2 : ℤ) ^ cyc.exponents ⟨i, by omega⟩ =
        3 * ↑(cyc.orbit ⟨i, hi⟩) + 1 := by exact_mod_cast cyc.hcycle ⟨i, by omega⟩
    have h3split : (3 : ℤ) ^ (k - i) = 3 * (3 : ℤ) ^ (k - 1 - i) := by
      rw [show k - i = (k - 1 - i) + 1 from by omega, pow_succ]; ring
    -- Prove f(i+1) = f(i) + step, then subtract
    suffices heq : f (i + 1) = f i + (3 : ℤ) ^ (k - 1 - i) * (2 : ℤ) ^ (cumA ⟨i, hi⟩) by
      linarith
    by_cases hi1 : i + 1 < k
    · -- Case i + 1 < k
      have hfi1 : f (i + 1) = ↑(cyc.orbit ⟨i + 1, hi1⟩) * (3 : ℤ) ^ (k - (i + 1)) *
          (2 : ℤ) ^ (cumA ⟨i + 1, hi1⟩) := dif_pos hi1
      have horb : cyc.orbit ⟨i + 1, hi1⟩ = cyc.orbit ⟨(i + 1) % k, Nat.mod_lt _ hk_pos⟩ := by
        congr 1; exact Fin.ext (Nat.mod_eq_of_lt hi1).symm
      rw [hfi1, hfi, hcumA_succ i hi1, pow_add, horb,
          show k - (i + 1) = k - 1 - i from by omega, h3split]
      linear_combination (3 : ℤ) ^ (k - 1 - i) * (2 : ℤ) ^ (cumA ⟨i, by omega⟩) * hcyc_z
    · -- Case i + 1 = k (i.e., i = k - 1)
      have hik : i = k - 1 := by omega
      subst hik
      have hfk1 : f (k - 1 + 1) = f k := by congr 1; omega
      rw [hfk1, hfk, hfi, show cyc.S = cumA ⟨k - 1, by omega⟩ +
          cyc.exponents ⟨k - 1, by omega⟩ from hcumA_last.symm, pow_add, h3split,
          show k - 1 - (k - 1) = 0 from by omega]
      simp only [pow_zero, one_mul, mul_one]
      have horb0 : (cyc.orbit ⟨(k - 1 + 1) % k, Nat.mod_lt _ hk_pos⟩ : ℤ) = ↑n₀ := by
        have hfin : (⟨(k - 1 + 1) % k, Nat.mod_lt _ hk_pos⟩ : Fin k) = ⟨0, hk_pos⟩ :=
          Fin.ext (show (k - 1 + 1) % k = 0 by
            rw [show k - 1 + 1 = k from by omega, Nat.mod_self])
        rw [hfin, hn₀]
      rw [horb0] at hcyc_z
      linear_combination (2 : ℤ) ^ (cumA ⟨k - 1, by omega⟩) * hcyc_z
  -- ===== Telescoping via Finset.sum_range_sub + Fin.sum_univ_eq_sum_range =====
  suffices hfin : (↑(Finset.univ.sum fun i : Fin k =>
      3 ^ (k - 1 - i.val) * 2 ^ cumA i) : ℤ) =
      ↑n₀ * (2 : ℤ) ^ cyc.S - ↑n₀ * (3 : ℤ) ^ k by linarith
  calc Finset.univ.sum (fun i : Fin k => (3 : ℤ) ^ (k - 1 - i.val) * (2 : ℤ) ^ (cumA i))
      = Finset.univ.sum (fun i : Fin k => f (↑i + 1) - f ↑i) :=
        Finset.sum_congr rfl (fun ⟨i, hi⟩ _ => (hstep_f i hi).symm)
    _ = (Finset.range k).sum (fun i => f (i + 1) - f i) :=
        Fin.sum_univ_eq_sum_range (fun i => f (i + 1) - f i) k
    _ = f k - f 0 := Finset.sum_range_sub f k
    _ = ↑n₀ * (2 : ℤ) ^ cyc.S - ↑n₀ * (3 : ℤ) ^ k := by rw [hfk, hf0]

-- ============================================================================
-- PART D: The Nonsurjectivity Theorem
-- ============================================================================

/-- **Theorem 1**: Crystal nonsurjectivity.
For k ≥ 18 with S = ⌈k · log₂ 3⌉ and d > 0: C(S−1, k−1) < d.

**Status**: sorry — the entropy bound tools are now available (BinomialEntropy.lean),
but the final comparison requires quantitative analysis not yet formalized.

**Available tools** (from BinomialEntropy.lean):
  - `choose_le_div_pow`: C(n,m) ≤ (n/m)^m · (n/(n-m))^{n-m}
  - `choose_log2_bound`: log₂(C(n,m)) ≤ m·log₂(n/m) + (n-m)·log₂(n/(n-m))

**Available tools** (from Mathlib):
  - `strictConcave_binEntropy`: h₂ is strictly concave on [0,1]
  - `deriv_binEntropy`: h₂'(p) = log(1-p) - log(p)

**Remaining gap**: Comparing the entropy bound at p=(k-1)/(S-1) with 2^S−3^k
requires either (a) concavity + derivative evaluation at p₀ = log₂/log₃,
or (b) certified numerics for a finite range of k. -/
theorem crystal_nonsurjectivity (k : ℕ) (hk : k ≥ 18)
    (S : ℕ) (hS : S = Nat.ceil (k * (Real.log 3 / Real.log 2)))
    (hd : crystalModule S k > 0) :
    Nat.choose (S - 1) (k - 1) < (crystalModule S k).toNat := by
  sorry

-- ============================================================================
-- PART E: Exceptions — Direct Computation
-- ============================================================================

/-- Helper: 2^4 < 3^3 (i.e., 16 < 27). -/
private lemma pow2_4_lt_pow3_3 : (2 : ℤ) ^ 4 < (3 : ℤ) ^ 3 := by norm_num

/-- Helper: 3^3 < 2^5 (i.e., 27 < 32). -/
private lemma pow3_3_lt_pow2_5 : (3 : ℤ) ^ 3 < (2 : ℤ) ^ 5 := by norm_num

/-- The three exceptions where C/d ≥ 1, all below k = 68.
Computed with exact integer arithmetic. -/
theorem exceptions_below_68 :
    -- k = 3, S = 5: C(4,2) = 6 ≥ d = 5, and 3 < 68
    (Nat.choose 4 2 ≥ ((2:ℤ)^5 - (3:ℤ)^3).toNat ∧ 3 < 68) ∧
    -- k = 5, S = 8: C(7,4) = 35 ≥ d = 13, and 5 < 68
    (Nat.choose 7 4 ≥ ((2:ℤ)^8 - (3:ℤ)^5).toNat ∧ 5 < 68) ∧
    -- k = 17, S = 27: C(26,16) = 5311735 ≥ d = 5077565, and 17 < 68
    (Nat.choose 26 16 ≥ ((2:ℤ)^27 - (3:ℤ)^17).toNat ∧ 17 < 68) := by
  refine ⟨⟨?_, by omega⟩, ⟨?_, by omega⟩, ⟨?_, by omega⟩⟩
  -- k = 3: C(4,2) = 6, d = 2^5 - 3^3 = 32 - 27 = 5
  · native_decide
  -- k = 5: C(7,4) = 35, d = 2^8 - 3^5 = 256 - 243 = 13
  · native_decide
  -- k = 17: C(26,16) = 5311735, d = 2^27 - 3^17 = 5077565
  · native_decide

-- ============================================================================
-- PART F: Simons–de Weger (External Axiom)
-- ============================================================================

/-- **Simons–de Weger theorem** (2005). No positive cycle with k < 68.
Accepted as axiom (published Acta Arithmetica 117, independently verified). -/
axiom simons_de_weger :
    ∀ k : ℕ, k ≥ 1 → k < 68 →
    ¬ ∃ (n₀ S : ℕ) (A : Fin k → ℕ),
      n₀ > 0 ∧ crystalModule S k > 0 ∧
      (n₀ : ℤ) * crystalModule S k = ↑(corrSum k A)

-- ============================================================================
-- PART G: The Junction Theorem
-- ============================================================================

/-- **Theorem 2**: Junction (unconditional).
For every k ≥ 1, either SdW eliminates (k < 68) or Ev_d is non-surjective (k ≥ 18). -/
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

/-- Full coverage: every k ≥ 1 satisfies k < 68 or k ≥ 18. -/
theorem full_coverage (k : ℕ) (hk : k ≥ 1) : k < 68 ∨ k ≥ 18 := by
  omega

-- ============================================================================
-- PART H: Quasi-Uniformity Hypothesis (H)
-- ============================================================================

/-- The quasi-uniformity hypothesis (H).
Strengthened to give a concrete count bound: for k ≥ 18 with d > 0,
the number of compositions A with corrSum(A) ≡ 0 (mod d) is < 1,
hence exactly 0.

This encodes the consequence of character sum bounds: under (H),
#{A : corrSum(A) ≡ 0 mod d} ≈ C/d < 1, hence = 0. -/
class QuasiUniformity (k S : ℕ) where
  /-- No composition achieves corrSum ≡ 0 (mod d) -/
  zero_not_attained :
    crystalModule S k > 0 →
    ∀ (A : Fin k → ℕ), Finset.univ.sum A = S - k →
    (corrSum k A) % (crystalModule S k).toNat ≠ 0

/-- **Theorem 3**: Under (H), 0 ∉ Im(Ev_d). -/
theorem zero_exclusion_conditional (k : ℕ) (hk : k ≥ 18)
    (S : ℕ) (hS : S = Nat.ceil (k * (Real.log 3 / Real.log 2)))
    (hd : crystalModule S k > 0)
    [hu : QuasiUniformity k S] :
    ¬ ∃ (A : Fin k → ℕ),
      (Finset.univ.sum A = S - k) ∧
      (corrSum k A) % (crystalModule S k).toNat = 0 := by
  intro ⟨A, hsum, hmod⟩
  exact hu.zero_not_attained hd A hsum hmod

/-- **Main Theorem** (conditional on H + Simons–de Weger).
No nontrivial positive Collatz cycle exists. -/
theorem no_positive_cycle
    (k : ℕ) (hk : k ≥ 1)
    (S : ℕ) (hS : S = Nat.ceil (k * (Real.log 3 / Real.log 2)))
    (hd : crystalModule S k > 0)
    [hu : QuasiUniformity k S] :
    ¬ ∃ (n₀ : ℕ) (A : Fin k → ℕ),
      n₀ > 0 ∧
      (Finset.univ.sum A = S - k) ∧
      (n₀ : ℤ) * crystalModule S k = ↑(corrSum k A) := by
  intro ⟨n₀, A, hn₀, hsum, hsteiner⟩
  rcases full_coverage k hk with hlt | hge
  · -- k < 68: Simons–de Weger eliminates
    exact simons_de_weger k hk hlt ⟨n₀, S, A, hn₀, hd, hsteiner⟩
  · -- k ≥ 18: zero_exclusion says corrSum(A) ≢ 0 (mod d)
    -- But Steiner says n₀ * d = corrSum(A), so d | corrSum(A), contradiction
    have hmod : (corrSum k A) % (crystalModule S k).toNat = 0 := by
      -- From n₀ * d = corrSum(A): d divides corrSum(A)
      rw [← Nat.dvd_iff_mod_eq_zero]
      -- Goal: d.toNat ∣ corrSum k A
      -- Lift to ℤ using natCast_dvd_natCast
      rw [← Int.natCast_dvd_natCast]
      -- Goal: ↑(d.toNat) ∣ ↑(corrSum k A) in ℤ
      have hd_nn : 0 ≤ crystalModule S k := le_of_lt hd
      rw [Int.toNat_of_nonneg hd_nn]
      -- Goal: d ∣ ↑(corrSum k A)
      exact ⟨↑n₀, by linarith⟩
    exact absurd ⟨A, hsum, hmod⟩ (zero_exclusion_conditional k hge S hS hd)

-- ============================================================================
-- PART I: The Entropy-Module Gap
-- ============================================================================

/-- Key helper: log₂ 3 ≠ 2, equivalently 3 ≠ 4.
This ensures 1/log₂3 ≠ 1/2, so binary entropy < 1. -/
private lemma log_two_div_log_three_ne_half :
    Real.log 2 / Real.log 3 ≠ 1 / 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num : (1:ℝ) < 3)
  intro h
  -- If log 2 / log 3 = 1/2, then 2 * log 2 = log 3
  have h1 : 2 * Real.log 2 = Real.log 3 := by
    have := (div_eq_iff (ne_of_gt hlog3)).mp h
    linarith
  -- 2 * log 2 = log(2²) = log 4
  have h2 : Real.log ((2 : ℝ) ^ 2) = Real.log 3 := by
    rw [Real.log_pow]; push_cast; linarith
  -- log is injective on (0, ∞), so 2² = 3, i.e., 4 = 3
  have h3 : (2 : ℝ) ^ 2 = 3 :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity : (0:ℝ) < 2^2))
      (Set.mem_Ioi.mpr (by positivity : (0:ℝ) < 3)) h2
  -- Contradiction: 4 ≠ 3
  norm_num at h3

/-- Binary entropy h(p) < 1 when p ≠ 1/2.

Proof via Jensen's inequality for the strictly concave function log:
  p · log(1/p) + (1−p) · log(1/(1−p))
    < log(p · 1/p + (1−p) · 1/(1−p))    [strict Jensen, since 1/p ≠ 1/(1-p)]
    = log(1 + 1)
    = log 2

Dividing by log 2: h(p) < 1. -/
private lemma binary_entropy_lt_one (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hne : p ≠ 1/2) :
    binaryEntropy p hp0 hp1 < 1 := by
  unfold binaryEntropy
  -- Our binaryEntropy = -(p·log p/log 2 + (1-p)·log(1-p)/log 2)
  --                    = (p·log(1/p) + (1-p)·log(1/(1-p))) / log 2
  --                    = Real.binEntropy p / log 2
  -- By Mathlib's binEntropy_lt_log_two: binEntropy p < log 2 ↔ p ≠ 2⁻¹
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- Show our expression = binEntropy / log 2
  have hconv : -(p * Real.log p / Real.log 2 +
      (1 - p) * Real.log (1 - p) / Real.log 2) =
      Real.binEntropy p / Real.log 2 := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv]
    ring
  rw [hconv, div_lt_one hlog2]
  exact Real.binEntropy_lt_log_two.mpr (by rwa [ne_eq, ← one_div])

/-- γ > 0: the entropy-module gap is strictly positive. -/
theorem gamma_pos : gamma > 0 := by
  unfold gamma
  -- gamma = 1 - binaryEntropy(log 2 / log 3, ...)
  -- Since log 2 / log 3 ≠ 1/2 (because 3 ≠ 4), we have h(p) < 1, hence γ > 0
  have p_ne : (1 : ℝ) / (Real.log 3 / Real.log 2) ≠ 1 / 2 := by
    rw [one_div, inv_div]
    exact log_two_div_log_three_ne_half
  have hlt := binary_entropy_lt_one _
    (by rw [one_div, inv_div]; exact log2_div_log3_pos)
    (by rw [one_div, inv_div]; exact log2_div_log3_lt_one) p_ne
  linarith

/-- The deficit log₂(C/d) ≈ −γ·S grows linearly.

**Status**: sorry — the entropy bound is available (BinomialEntropy.lean), but
the concavity analysis to bound h₂ at (k-1)/(S-1) requires evaluation of
log(log(3/2)/log(2)) and comparison with binEntropy(log₂/log₃).

**Proof sketch** (tools available, final step needs quantitative comparison):
  (1) From `choose_log2_bound`: log₂(C) ≤ (S-1)·h₂((k-1)/(S-1))
  (2) By `strictConcave_binEntropy`: h₂(p) ≤ h₂(p₀) + h₂'(p₀)·(p−p₀)
      where p₀ = log₂/log₃ and h₂'(p₀) = log(1−p₀) − log(p₀) < 0
  (3) Therefore: (S-1)·h₂(p) ≤ S·h₂(p₀) + (h₂'(p₀)·A − h₂(p₀))
      where A = (k-1) − (S-1)·p₀ ∈ [−1, p₀−1]
  (4) The correction h₂'(p₀)·A − h₂(p₀) < 0 (verified numerically),
      so the bound holds without even needing the log₂(S) slack. -/
theorem deficit_linear_growth (k : ℕ) (hk : k ≥ 18) (S : ℕ)
    (hS : S = Nat.ceil (k * (Real.log 3 / Real.log 2)))
    (hd : crystalModule S k > 0) :
    Real.log (Nat.choose (S - 1) (k - 1)) / Real.log 2 ≤
    (S : ℝ) * (1 - gamma) + Real.log S / Real.log 2 := by
  sorry

-- ============================================================================
-- PART J: Sorry Census
-- ============================================================================

/-!
### Final Sorry Census (2 sorry remaining in this file, down from original 13)

| ID  | Statement                  | Type   | Difficulty | Status                |
|-----|----------------------------|--------|------------|-----------------------|
| S1  | steiner_equation           | proved | ★★★       | Telescoping+lin_comb ✓|
| S2  | crystal_nonsurjectivity    | sorry  | ★★★★     | Entropy+gap analysis  |
| S3  | exceptions_below_68        | proved | ★          | native_decide ✓       |
| A1  | simons_de_weger            | axiom  | —          | Published result      |
| S4  | zero_exclusion_conditional | proved | ★          | From QU class ✓       |
| S5  | no_positive_cycle          | proved | ★★        | Int/Nat dvd bridge ✓  |
| S6  | gamma_pos                  | proved | ★★        | binEntropy_lt_log_two✓|
| S7  | deficit_linear_growth      | sorry  | ★★★       | Concavity+deriv bound |
| H1  | binary_entropy_lt_one      | proved | ★★        | Mathlib BinaryEntropy✓|

### Remaining sorry's (this file):
  - crystal_nonsurjectivity: BinomialEntropy tools available; needs concavity
    analysis at p=(k-1)/(S-1) + comparison with 2^S - 3^k
  - deficit_linear_growth: BinomialEntropy + strictConcave_binEntropy available;
    needs evaluation of h₂'(log₂/log₃) and bound on correction term

### Mathematical tools now available:
  - BinomialEntropy.lean: choose_le_div_pow, choose_log_bound, choose_log2_bound
  - LegendreApprox.lean: abs_sub_ge_of_not_convergent, abs_sub_ge_nat_div
  - Mathlib: strictConcave_binEntropy, deriv_binEntropy, deriv2_binEntropy

### Axiom (unchanged):
  - simons_de_weger: published external result (Acta Arith. 2005)
-/

end Collatz.JunctionTheorem
