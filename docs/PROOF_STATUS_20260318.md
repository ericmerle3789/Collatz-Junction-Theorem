# CORRECTED PROOF STATUS — 18 Mars 2026
## After Critical Audit of corrSum Formula

### Executive Summary

A critical audit revealed that `lean4_proof/Basic.lean` (Range Exclusion) uses
INDIVIDUAL exponents in corrSum, while Steiner's equation (1977) requires
CUMULATIVE exponents. The Range Exclusion argument and Path B (FCQ prime-by-prime)
are INVALID for the correct formula. The Junction Theorem (nonsurjectivity)
and Steiner equation (Lean skeleton) remain VALID.

---

## What IS Proved (Solid, Lean-formalized)

### 1. Steiner's Equation (JunctionTheorem.lean, lines 124-225)
**PROVED** in Lean with full proof term. Cumulative exponents correctly used.
```
theorem steiner_equation : n₀ · (2^S - 3^k) = Σ 3^{k-1-i} · 2^{cumA_i}
```

### 2. Crystal Nonsurjectivity (JunctionTheorem.lean, lines 475-522)
**PROVED** for k ≥ 18: C(S-1, k-1) < (2^S - 3^k).
- k ∈ [18, 665]: native_decide (648 cases) ✓
- k ≥ 666: entropy-deficit argument via tangent line bound ✓
- 2 sorry's remain in AsymptoticBound.lean (convergent/non-convergent assembly)

### 3. Simons-de Weger (axiom)
**AXIOM** in Lean: No positive cycle with k < 68. Published (Acta Arith. 2005).

### 4. Junction Theorem (unconditional)
**PROVED**: For every k ≥ 1, at least one residue mod d is not attained
by the evaluation map Ev_d. (Union of SdW region and counting bound.)

### 5. Conditional No-Cycle Theorem (JunctionTheorem.lean, lines 627-655)
**PROVED**: Under QuasiUniformity (H), no nontrivial positive Collatz cycle exists.

---

## What is NOT Proved

### Hypothesis H: "0 is the missed residue"

The Junction Theorem says |Im(Ev_d)| < d for k ≥ 18, so at least one
residue is missed. H says 0 is among the missed ones.

**H is EQUIVALENT to the Collatz positive-cycle conjecture.**

### Verification status of H
- k = 3..14: N0_cumulative = 0 verified EXHAUSTIVELY (brute force) ✓
- k = 3..67: N0_cumulative = 0 by SdW (no cycles for k < 68) ✓
- k ≥ 68: OPEN (neither computationally nor theoretically resolved)

---

## What is INVALID (Must Be Retracted)

### 1. Range Exclusion (lean4_proof/Basic.lean)
**INVALID**: Uses individual exponents. The correct (cumulative) range
is Ω(2^{0.585k}) = exponentially larger than d. Range Exclusion
fundamentally cannot work with the correct formula.

### 2. Path B (FCQ/Spectral, PROOF_ASSEMBLY §4)
**PARTIALLY INVALID**: The spectral contraction ρ_p < 1 is valid
mathematics, but N0(p) > 0 for almost all small primes p | d with
cumulative exponents. The prime-by-prime approach does not yield N0(d) = 0.

### 3. Baker-LMN closing (PROOF_ASSEMBLY §10)
**INVALID**: Relied on Range Exclusion which uses the wrong formula.

### 4. PROOF_ASSEMBLY claims of "unconditional for all k"
**INVALID**: The unconditional claim was based on Range Exclusion.
Only the conditional result (under H) is valid.

---

## Key Numerical Findings (18 Mars 2026)

### The phantom at k=4 disappears
With cumulative exponents: N0(d(4)) = 0. The "phantom" composition (1,1,1,4)
with individual exponents has corrSum_indiv = 94 = 2·47 = 2d, but this is
NOT the correct Steiner corrSum.

### N0_cumulative = 0 for k=3..14 (exhaustive)
Verified by complete enumeration of all C(S-1,k-1) cumulative sequences.

### CRT interference mechanism
For composite d = p₁·p₂·...·p_r, individual primes give N0(p_i) > 0,
but N0(d) = 0 due to anti-correlation (CRT interference).
- k=6, d=295=5·59: N0(5)=36, N0(59)=6, N0(295)=0
- k=12, d=5·59·1753: pairwise intersections non-empty, triple = 0

### k=5 is the Rosetta Stone
For k=5, d=13: 35 sequences cover 12/13 residues. 0 is the UNIQUE missed
residue. This case is small enough for complete algebraic analysis.

---

## Corrected Lean File Status

| File | Status | Note |
|------|--------|------|
| lean/skeleton/JunctionTheorem.lean | **VALID** | Cumulative exponents ✓ |
| lean/skeleton/FiniteCases.lean | **VALID** | native_decide on C < d ✓ |
| lean/skeleton/AsymptoticBound.lean | **VALID** | 2 sorry's remain |
| lean4_proof/Basic.lean | **INVALID** | Individual exponents (wrong) |
| lean4_proof/RangeExclusion.lean | **INVALID** | Based on wrong corrSum |
| lean4_proof/Theorems.lean | **INVALID** | Uses wrong checkAvoidance |

---

## Research Directions for H

### Direction 1: Exponential Sum Bound
N0 = C/d + (1/d)Σ_{a≠0} G(a). If |G(a)| bounded by the geometric
structure of corrSum (mixed 2/3 terms), N0 could be forced to 0.

### Direction 2: CRT Interference Theory
Formalize why the intersection of zero-sets mod different primes
is always empty. Possibly via sieve theory or additive combinatorics.

### Direction 3: Orbit Constraint Extension
Extend Simons-de Weger analysis using the counting bound C < d
as additional leverage for k ≥ 68.

### Direction 4: Algebraic Structure of Im(Ev_d)
Prove Im(Ev_d) lies in a specific coset of Z/dZ not containing 0.
The relation 2^S ≡ 3^k mod d might force this algebraically.

---

## Files Updated/Created This Session

| File | Purpose |
|------|---------|
| scripts/verify_audit_corrsum.py | Numerical verification of audit |
| scripts/dp_n0_numpy.py | DP computation of N0 mod p |
| scripts/crt_analysis.py | CRT interference analysis |
| scripts/k5_deep_analysis.py | Deep analysis of k=5 case |
| research_log/FINDING_20260318_audit_confirmed.md | Audit confirmation |
| research_log/FINDING_20260318_prime_approach_fails.md | FCQ failure |
| research_log/FINDING_20260318_crt_patterns.md | CRT patterns |
| research_log/FINDING_20260318_k5_structure.md | k=5 algebraic analysis |
| research_log/EXPLORATION_structural_H.md | Structural approach notes |
| research_log/EXPLORATION_crt_interference.md | CRT theory notes |
| docs/PROOF_STATUS_20260318.md | This file |
