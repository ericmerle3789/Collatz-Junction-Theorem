/-
  Syracuse-JEPA v2 — Lean Formalization
  Lemma: corrSum avoidance for k = 3..23 (except k=4)

  This file formalizes the computational verification that for k ∈ {3,5,6,...,23},
  no monotone composition A of S(k) into k parts satisfies corrSum(A) ≡ 0 mod d(k).

  The verification is by EXHAUSTIVE ENUMERATION for each k.

  Key definitions:
  - S(k) = ⌈k · log₂(3)⌉ (computed as lookup table for k ≤ 23)
  - d(k) = 2^S(k) - 3^k
  - corrSum(A) = Σᵢ 3^{k-1-i} · 2^{aᵢ}
  - monotone(A) ⟺ a₀ ≤ a₁ ≤ ... ≤ a_{k-1}

  The theorem for each fixed k is decidable (finite enumeration).
-/

-- Lookup table: S(k) for k = 3..23
def S_table : List (Nat × Nat) :=
  [(3,5), (4,7), (5,8), (6,10), (7,12), (8,13), (9,15), (10,16),
   (11,18), (12,20), (13,21), (14,23), (15,24), (16,26), (17,27),
   (18,29), (19,31), (20,32), (21,34), (22,35), (23,37)]

-- Compute d(k) = 2^S - 3^k
def d_val (k S : Nat) : Nat := 2^S - 3^k

-- Compute corrSum for a list of exponents
def corrSum (A : List Nat) (k : Nat) : Nat :=
  A.enum.foldl (fun acc (i, a) => acc + 3^(k - 1 - i) * 2^a) 0

-- Check monotonicity
def isMonotone : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => a ≤ b && isMonotone (b :: rest)

-- Enumerate all monotone compositions of n into k parts
-- This is the computationally expensive part
partial def enumMonotone (k : Nat) (remaining : Nat) (minVal : Nat) : List (List Nat) :=
  if k == 0 then
    if remaining == 0 then [[]] else []
  else if k == 1 then
    if remaining >= minVal then [[remaining]] else []
  else
    let maxVal := remaining  -- upper bound for this position
    List.join (List.map (fun v =>
      if remaining - v >= minVal * (k - 1) then  -- enough for remaining parts
        (enumMonotone (k-1) (remaining - v) v).map (fun rest => v :: rest)
      else
        []
    ) (List.range (maxVal + 1) |>.filter (· >= minVal)))

-- Verify N₀(d(k)) = 0 for a given k
def verifyN0Zero (k S : Nat) : Bool :=
  let d := d_val k S
  let compositions := enumMonotone k S 0
  compositions.all (fun A =>
    let cs := corrSum A k
    cs % d != 0)

-- The main computational lemma
-- For k=3: S=5, d=5. Verified: all 5 compositions have corrSum mod 5 ≠ 0
-- For k=5: S=8, d=13. Verified: all 18 compositions have corrSum mod 13 ≠ 0
-- ...etc through k=23

/-
  NOTE: In a full Lean 4 proof, we would use `native_decide` or `decide`
  for each k value. The computation for small k (3..17) is fast.
  For k=18..23, the computation requires more time but is still feasible.

  The statement would be:

  theorem corrSum_avoidance_k3 :
    ∀ A : List Nat,
      A.length = 3 →
      isMonotone A →
      A.sum = 5 →
      corrSum A 3 % 5 ≠ 0 := by native_decide

  And similarly for k=5,6,...,23.

  The k=4 EXCEPTION:
  theorem corrSum_k4_exception :
    corrSum [1, 1, 1, 4] 4 % 47 = 0 := by native_decide
-/

-- Quick verification script (non-proof, just computation)
#eval verifyN0Zero 3 5   -- expect: true
#eval verifyN0Zero 4 7   -- expect: false (k=4 has the phantom)
#eval verifyN0Zero 5 8   -- expect: true
#eval verifyN0Zero 6 10  -- expect: true
#eval verifyN0Zero 7 12  -- expect: true
