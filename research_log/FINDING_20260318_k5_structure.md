# k=5 DEEP STRUCTURE: 0 is the UNIQUE missed residue
## 18 Mars 2026

### The Fact
For k=5, S=8, d=13 (prime):
- 35 cumulative sequences
- 12/13 residues hit (92% coverage)
- The ONE missed residue is 0 (= Collatz cycle residue)

### Algebraic Reformulation

corrSum ≡ 0 mod d iff Σ_{j=0}^{k-1} γ^j · α^{δ_j} = 0 in Z/pZ

where:
- α = 2 mod p, β = 3 mod p, γ = α/β = 2·3^{-1} mod p
- δ_j = σ_j - j (weakly increasing, δ_0 = 0)
- Constraint: α^S = β^k (from p | d)

For k=5, p=13: γ = 5, ord_13(γ) = 4

### Key Constraint
The relation γ^k = α^{k-S} creates an algebraic coupling.
For k=5: γ^5 = γ^4·γ = 1·5 = 5 = α^{-3} = 2^{-3} mod 13.

### Exponential Sum Approach (Lead)

N0 = C/d + (1/d) Σ_{a=1}^{d-1} G(a) where G(a) = Σ_σ e(a·corrSum(σ)/d)

If |G(a)| ≤ B < 1 - C/d for all a ≠ 0, then N0 = 0.

For k → ∞: C/d → 0 exponentially, so need B → 0 or at least B < 1.

LEAD: Bound |G(a)| using the geometric structure of corrSum.
The weights and bases are BOTH geometric (in 3 and 2 respectively),
with coupling α^S = β^k. This might give enough cancellation.

### Orbit Constraint Approach (Lead)

If n₀ = corrSum/d exists, the orbit (n₀,...,n_{k-1}) gives:
- n_i ≡ (2^{e_i} - 1)/3 · n_0 + ... (tower of 2-adic constraints)
- These constrain n₀ mod 2^S severely

Combined with the counting bound C < d, the set of "admissible" n₀
might be empty for k ≥ 68.

### CRT Interference (Lead)

For composite d = Π p_i^{a_i}: the sets S_p = {σ : corrSum ≡ 0 mod p}
have non-empty pairwise intersections but EMPTY total intersection.
This is because the corrSum structure creates ANTI-CORRELATION between
the prime conditions.

### Status
- Finding is solid, computationally verified
- Three promising theoretical leads identified
- None yet yields a complete proof for all k
- This is equivalent to the full positive-cycle Collatz conjecture
