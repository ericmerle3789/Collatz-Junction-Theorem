/-
  CorrSum Avoidance Theorems — Verified by native_decide

  MAIN RESULT (Residue Avoidance Lemma):
  For k ∈ {3, 5, 6, ..., 40},
  no monotone composition A of S(k) into k parts satisfies
    corrSum(A, k) ≡ 0 (mod d(k))

  EXCEPTION (Phantom k=4):
  The composition A = (1, 1, 1, 4) satisfies
    corrSum(A, 4) = 94 = 2 · 47 = 2 · d(4)

  This is proved by exhaustive enumeration compiled to native code.
-/

import CorrSumAvoidance.Basic

open CorrSumAvoidance

-- ═══════════════════════════════════════════════════════════════
--  PART 1: Residue Avoidance — N₀(d(k)) = 0
-- ═══════════════════════════════════════════════════════════════

/-- k=3: S=5, d=5, 5 compositions. No corrSum ≡ 0 mod 5. -/
theorem avoidance_k3 : checkAvoidance 3 = true := by native_decide

/-- k=5: S=8, d=13, 18 compositions. No corrSum ≡ 0 mod 13. -/
theorem avoidance_k5 : checkAvoidance 5 = true := by native_decide

/-- k=6: S=10, d=295, 35 compositions. No corrSum ≡ 0 mod 295. -/
theorem avoidance_k6 : checkAvoidance 6 = true := by native_decide

/-- k=7: S=12, d=1909, 65 compositions. No corrSum ≡ 0 mod 1909. -/
theorem avoidance_k7 : checkAvoidance 7 = true := by native_decide

/-- k=8: S=13, d=1631, 89 compositions. No corrSum ≡ 0 mod 1631. -/
theorem avoidance_k8 : checkAvoidance 8 = true := by native_decide

/-- k=9: S=15, d=13085, 157 compositions. No corrSum ≡ 0 mod 13085. -/
theorem avoidance_k9 : checkAvoidance 9 = true := by native_decide

/-- k=10: S=16, d=6487, 212 compositions. No corrSum ≡ 0 mod 6487. -/
theorem avoidance_k10 : checkAvoidance 10 = true := by native_decide

/-- k=11: S=18, d=84997, 355 compositions. No corrSum ≡ 0 mod 84997. -/
theorem avoidance_k11 : checkAvoidance 11 = true := by native_decide

/-- k=12: S=20, d=517135, 582 compositions. No corrSum ≡ 0 mod 517135. -/
theorem avoidance_k12 : checkAvoidance 12 = true := by native_decide

/-- k=13: S=21, d=502829, 747 compositions. No corrSum ≡ 0 mod 502829. -/
theorem avoidance_k13 : checkAvoidance 13 = true := by native_decide

/-- k=14: S=23, d=3605639, 1188 compositions. No corrSum ≡ 0 mod 3605639. -/
theorem avoidance_k14 : checkAvoidance 14 = true := by native_decide

/-- k=15: S=24, d=2428309, 1508 compositions. No corrSum ≡ 0 mod 2428309. -/
theorem avoidance_k15 : checkAvoidance 15 = true := by native_decide

/-- k=16: S=26, d=24062143, 2339 compositions. -/
theorem avoidance_k16 : checkAvoidance 16 = true := by native_decide

/-- k=17: S=27, d=5077565, 2913 compositions. -/
theorem avoidance_k17 : checkAvoidance 17 = true := by native_decide

/-- k=18: S=29, d=149450423, 4426 compositions. -/
theorem avoidance_k18 : checkAvoidance 18 = true := by native_decide

/-- k=19: S=31, d=985222181, 6647 compositions. -/
theorem avoidance_k19 : checkAvoidance 19 = true := by native_decide

/-- k=20: S=32, d=808182895, 8154 compositions. -/
theorem avoidance_k20 : checkAvoidance 20 = true := by native_decide

/-- k=21: S=34, d=6719515981, 9934 compositions. -/
theorem avoidance_k21 : checkAvoidance 21 = true := by native_decide

/-- k=22: S=35, d=2978678759, 11868 compositions. -/
theorem avoidance_k22 : checkAvoidance 22 = true := by native_decide

/-- k=23: S=37, d=43295774645, 14124 compositions. -/
theorem avoidance_k23 : checkAvoidance 23 = true := by native_decide

/-- k=24: S=39, d=304505373637, 16769 compositions. -/
theorem avoidance_k24 : checkAvoidance 24 = true := by native_decide

/-- k=25: S=40, d=99632527277, 19628 compositions. -/
theorem avoidance_k25 : checkAvoidance 25 = true := by native_decide

/-- k=26: S=42, d=1856180682775, 52490 compositions. -/
theorem avoidance_k26 : checkAvoidance 26 = true := by native_decide

/-- k=27: S=43, d=1170495537221, 62577 compositions. -/
theorem avoidance_k27 : checkAvoidance 27 = true := by native_decide

/-- k=28: S=45, d=12307579633871, 88219 compositions. -/
theorem avoidance_k28 : checkAvoidance 28 = true := by native_decide

/-- k=29: S=46, d=1738366812781, 104643 compositions. -/
theorem avoidance_k29 : checkAvoidance 29 = true := by native_decide

/-- k=30: S=48, d=75583844616007, 146061 compositions. -/
theorem avoidance_k30 : checkAvoidance 30 = true := by native_decide

/-- k=31: S=50, d=508226510558677, 202629 compositions. -/
theorem avoidance_k31 : checkAvoidance 31 = true := by native_decide

/-- k=32: S=51, d=398779624833407, 238346 compositions. -/
theorem avoidance_k32 : checkAvoidance 32 = true := by native_decide

/-- k=33: S=53, d=3448138688185469, 327844 compositions. -/
theorem avoidance_k33 : checkAvoidance 33 = true := by native_decide

/-- k=34: S=54, d=1337216809815415, 384068 compositions. -/
theorem avoidance_k34 : checkAvoidance 34 = true := by native_decide

/-- k=35: S=56, d=22026048938928229, 524109 compositions. -/
theorem avoidance_k35 : checkAvoidance 35 = true := by native_decide

/-- k=36: S=58, d=138135740854712623, 711714 compositions. -/
theorem avoidance_k36 : checkAvoidance 36 = true := by native_decide

/-- k=37: S=59, d=126176846412426125, 828314 compositions. -/
theorem avoidance_k37 : checkAvoidance 37 = true := by native_decide

/-- k=38: S=61, d=954991291540701863, 1116997 compositions. -/
theorem avoidance_k38 : checkAvoidance 38 = true := by native_decide

/-- k=39: S=62, d=559130865408411637, 1295648 compositions. -/
theorem avoidance_k39 : checkAvoidance 39 = true := by native_decide

/-- k=40: S=64, d=6289078614652622815, 1735867 compositions. -/
theorem avoidance_k40 : checkAvoidance 40 = true := by native_decide

-- ═══════════════════════════════════════════════════════════════
--  PART 2: The Phantom — k=4 exception
-- ═══════════════════════════════════════════════════════════════

/-- k=4 phantom: A=(1,1,1,4) gives corrSum = 94 = 2·d(4) = 2·47.
    This is the ONLY known case where corrSum ≡ 0 mod d. -/
theorem phantom_k4 : checkPhantom [1, 1, 1, 4] 4 = true := by native_decide

/-- k=4 avoidance FAILS: there exists a composition with corrSum ≡ 0 mod d(4). -/
theorem avoidance_k4_fails : checkAvoidance 4 = false := by native_decide

-- ═══════════════════════════════════════════════════════════════
--  PART 3: Exact corrSum values (spot checks)
-- ═══════════════════════════════════════════════════════════════

/-- Verify corrSum([1,1,1,4], 4) = 94 -/
theorem corrsum_phantom_value : corrSum [1, 1, 1, 4] 4 = 94 := by native_decide

/-- Verify d(4) = 47 -/
theorem d4_value : d_val 4 = 47 := by native_decide

/-- Verify d(3) = 5 -/
theorem d3_value : d_val 3 = 5 := by native_decide

/-- Verify 94 = 2 * 47 -/
theorem phantom_is_2d : corrSum [1, 1, 1, 4] 4 = 2 * d_val 4 := by native_decide

-- ═══════════════════════════════════════════════════════════════
--  PART 4: Almost-flat closed form verification
-- ═══════════════════════════════════════════════════════════════

/-- For almost-flat A = (v,...,v, v+1,...,v+1) with (k-r) copies of v and r of v+1:
    corrSum = 2^v · ((3^k - 1)/2 + (3^r - 1)/2)
    Verify for k=5, v=1, r=3: A=(1,1,2,2,2) -/
theorem almost_flat_k5 :
    corrSum [1, 1, 2, 2, 2] 5 = 2 ^ 1 * ((3 ^ 5 - 1) / 2 + (3 ^ 3 - 1) / 2) := by
  native_decide

/-- Verify for k=7, v=1, r=5: A=(1,1,2,2,2,2,2) -/
theorem almost_flat_k7 :
    corrSum [1, 1, 2, 2, 2, 2, 2] 7 = 2 ^ 1 * ((3 ^ 7 - 1) / 2 + (3 ^ 5 - 1) / 2) := by
  native_decide
