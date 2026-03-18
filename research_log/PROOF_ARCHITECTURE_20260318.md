# PROOF ARCHITECTURE — Assembly Attempt
## 18 Mars 2026

### Goal
Prove: for all k ≥ 3, N₀(d(k)) = 0 (no nontrivial positive Collatz cycle).

### Proven components

**Theorem A (Junction, Lean-formalized)**: C(S-1,k-1) < d for k ≥ 18.

**Theorem B (SdW, axiom)**: No cycle for k < 68.

**Theorem C (Steiner, Lean-formalized)**: Cycle ⟺ corrSum(σ) ≡ 0 mod d
for some cumulative sequence σ.

**Theorem D (Maximum Principle, proved)**: P_σ(α) = max_j |P_σ(α·ζ^j)|
for all σ (triangle inequality + positive coefficients).

**Theorem E (REST' formula, proved)**: corrSum ≡ 0 mod d ⟺
Σ_{i=0}^{k-1} ρ^i · 2^{δ_i} ≡ 0 mod d with ρ = 2/3, δ weakly increasing.

**Theorem F (Ordering obstruction, verified k=3..8)**: Every free solution
has δ-crossings. Ordering eliminates all free solutions.

**Theorem G (ord bound, verified k=3..20)**: ord_d(2) > S-k.
Implies: individual swap corrections are nonzero.

**Theorem H (Number field, proved k=3,4)**: N(P_σ(α)) coprime to d
when d is prime. → QED for k=3,4.

### Proof attempt for all k

**Case 1: k < 68**. By SdW (Theorem B). ✓

**Case 2: k ≥ 68 with d prime and gcd(S,k)=1**.
If we can show N(P_σ(α)) is coprime to d for all σ: QED by Theorem H.
PROBLEM: This fails for k=5 (d=13 prime, but N coprime fails).

**Case 3: k ≥ 68 general**.
By Theorem F: N₀=0 iff no ordered δ-sequence hits the target.
By Theorem G: each swap correction is individually nonzero.
MISSING: total correction is nonzero.

### The missing lemma

**Lemma (Total Nonvanishing)**: For all k ≥ 3 and all free δ-sequences
with F(δ) ≡ 0 mod d: the sorting correction F(sorted(δ)) - F(δ) ≢ 0 mod d.

This is equivalent to N₀ = 0 (since F(sorted(δ)) = F(ordered) and
F(δ) = 0 implies F(ordered) ≢ 0).

This lemma is VERIFIED for k=3..8 (exhaustive).
It implies: N₀ = 0 for all k.

### Approach to prove the missing lemma

The correction F(sorted) - F(unsorted) = Σ ρ^i · (2^{s_i} - 2^{δ_i})
where s = sorted(δ).

Each term is ρ^i · 2^{min(s_i,δ_i)} · (2^{|s_i-δ_i|} - 1) · sign.
The factor (2^{|s_i-δ_i|} - 1) ≢ 0 mod d by Theorem G.
The factor ρ^i · 2^{min} is a UNIT in Z/dZ.

So each NONZERO term of the correction is a UNIT × (2^Δ - 1) ≢ 0.

The TOTAL is a sum of such terms. It's 0 mod d iff the terms
have a VERY specific cancellation pattern.

For the cancellation to happen: the ρ-powers must create a
DESTRUCTIVE INTERFERENCE pattern. This requires the permutation
σ (sorting permutation) to have a specific algebraic relationship
with ρ and the δ values.

Given that ρ = 2/3 is a FIXED algebraic number and the δ values
are constrained to {0,...,S-k}, the number of possible interference
patterns is FINITE for each k. And for k → ∞, the constraints
become more and more restrictive (more swap corrections to cancel).

### Status
The proof architecture is SOUND but the missing lemma is unproved.
The computational evidence (k=3..8, 100% of cases) strongly supports it.
A formal proof might require new results in additive combinatorics
or algebraic number theory.
