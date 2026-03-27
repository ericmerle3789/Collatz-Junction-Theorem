# Changelog

## v4 — March 27, 2026

**Title:** Cyclic Shift Obstructions for Non-Trivial Collatz Cycles

### Major additions
- **Rotation Obstruction Theorem** (Section 5): The shift recurrence identity reduces all k cyclic constraints to a single algebraic condition: 3^{2k} ≡ 1 (mod d(k)). This is the paper's main contribution.
- **Coprime Decomposition** (Section 5.3): Factorization of d(k) via GCD identity.
- **Computational verification** extended to k ≤ 50,000 (direct modular exponentiation).
- **Blocking primes** table for k ≤ 50 with explicit ord_p(3) data.
- **Baker–Wüstholz asymptotic argument** (Section 7): Effective bound for large k via multiplicative order lower bounds.
- **Character sum / spectral analysis** (Section 8): Transfer matrix rank-1 property for nontrivial characters.
- **Mellin–Fourier bridge** (Section 9): Connecting additive (compositions) and multiplicative (divisibility) structures.
- **ABC conditional result** (Section 12): Clearly marked as conditional on ABC conjecture.
- **Lean formalization**: 280 theorems, 0 sorry, 0 axiom, covering k ≤ 5,258.
- **Baker–LMN bound** (Section 10): Covers k ≥ 5,259 via nonsurjectivity.

### Architecture
The proof combines three pillars:
1. Algebraic obstruction (Rotation Theorem)
2. Computational verification (k ≤ 50,000 + Lean certified k ≤ 5,258)
3. Asymptotic argument (Baker–Wüstholz / Baker–LMN)

### Known gap
The effective Baker constant K_0 is large (potentially > 10^6). Computation covers k ≤ 50,000, providing a safety margin but not an explicit closure. The result is complete *modulo explicit computation of K_0*.

### Status
Preprint. The main theorem is stated as unconditional but qualified in Remark 4.2 regarding K_0.
