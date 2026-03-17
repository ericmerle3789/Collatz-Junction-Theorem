/-
  CorrSum Avoidance — Core Definitions

  For the Collatz Junction Theorem, we need:
  • corrSum(A, k) = Σᵢ 3^{k-1-i} · 2^{Aᵢ}
  • S(k) = ⌈k · log₂(3)⌉  (hardcoded table)
  • d(k) = 2^{S(k)} - 3^k
  • Monotone compositions: non-decreasing sequences summing to S(k)

  The key claim: for k ≠ 4, no monotone composition A of S(k) into k parts
  satisfies corrSum(A,k) ≡ 0 (mod d(k)).
-/

namespace CorrSumAvoidance

/-- corrSum helper: given list A and current power-of-3 exponent,
    compute Σ 3^exp · 2^(Aᵢ) with exp decreasing. -/
def corrSumGo : List Nat → Nat → Nat
  | [], _ => 0
  | a :: rest, pow3 => 3 ^ pow3 * 2 ^ a + corrSumGo rest (pow3 - 1)

/-- corrSum(A, k) = Σᵢ₌₀^{k-1} 3^{k-1-i} · 2^{Aᵢ} -/
def corrSum (A : List Nat) (k : Nat) : Nat :=
  corrSumGo A (k - 1)

/-- Sum of a list of natural numbers -/
def listSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + listSum xs

/-- Check if a list is monotone (non-decreasing) -/
def isMonotone : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => a ≤ b && isMonotone (b :: rest)

/-- Enumerate all monotone compositions of `total` into `parts` parts,
    with each part ≥ `minVal`.
    Returns a list of lists, each of length `parts` and summing to `total`. -/
def enumMonotone : Nat → Nat → Nat → List (List Nat)
  | 0, total, _ => if total == 0 then [[]] else []
  | parts + 1, total, minVal =>
    if parts == 0 then
      -- Exactly 1 part
      if total ≥ minVal then [[total]] else []
    else
      -- parts + 1 ≥ 2: first element ranges from minVal to total/(parts+1)
      let k := parts + 1
      let maxFirst := total / k
      if maxFirst < minVal then []
      else
        ((List.range (maxFirst - minVal + 1)).map fun i =>
          let v := i + minVal
          (enumMonotone parts (total - v) v).map (v :: ·)).flatten

/-- S(k) = ⌈k · log₂(3)⌉ for k = 0..40.
    Computed as the smallest S such that 2^S > 3^k, i.e., 2^S ≥ 3^k + 1. -/
def S_table : Nat → Nat
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 5
  | 4 => 7
  | 5 => 8
  | 6 => 10
  | 7 => 12
  | 8 => 13
  | 9 => 15
  | 10 => 16
  | 11 => 18
  | 12 => 20
  | 13 => 21
  | 14 => 23
  | 15 => 24
  | 16 => 26
  | 17 => 27
  | 18 => 29
  | 19 => 31
  | 20 => 32
  | 21 => 34
  | 22 => 35
  | 23 => 37
  | 24 => 39
  | 25 => 40
  | 26 => 42
  | 27 => 43
  | 28 => 45
  | 29 => 46
  | 30 => 48
  | 31 => 50
  | 32 => 51
  | 33 => 53
  | 34 => 54
  | 35 => 56
  | 36 => 58
  | 37 => 59
  | 38 => 61
  | 39 => 62
  | 40 => 64
  | _ => 0  -- beyond our table

/-- d(k) = 2^{S(k)} - 3^k. Precondition: 2^{S(k)} > 3^k for k ≥ 1. -/
def d_val (k : Nat) : Nat :=
  2 ^ (S_table k) - 3 ^ k

/-- Check that ALL monotone compositions of S into k parts
    have corrSum not divisible by d. Returns true iff N₀ = 0. -/
def checkAvoidance (k : Nat) : Bool :=
  let s := S_table k
  let d := d_val k
  if d == 0 then false  -- degenerate
  else
    (enumMonotone k s 0).all fun A => corrSum A k % d != 0

/-- Check that a SPECIFIC composition gives corrSum ≡ 0 mod d -/
def checkPhantom (A : List Nat) (k : Nat) : Bool :=
  let d := d_val k
  d != 0 && corrSum A k % d == 0

end CorrSumAvoidance
