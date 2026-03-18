# CRT Interference: The Key Mechanism
## Session 18 Mars 2026

### The Phenomenon

For k=6, d=295=5·59:
- N0(5) = 36 (28.6% of 126 sequences)
- N0(59) = 6 (4.8% of 126 sequences)
- N0(295) = 0 (0% — ZERO)

Expected overlap if independent: 36 · 6 / 126 ≈ 1.7 sequences.
Actual overlap: 0. The conditions corrSum ≡ 0 mod 5 AND corrSum ≡ 0 mod 59
are ANTI-CORRELATED for cumulative sequences.

### Why this might always happen

Hypothesis: For ALL k ≥ 3, the sets
S_p = {σ ∈ Comp(S,k) : corrSum(σ) ≡ 0 mod p}
for different primes p | d(k) have EMPTY INTERSECTION.

This would prove N0(d) = 0 for all k.

### Mathematical structure

For p | d, we have 2^S ≡ 3^k mod p. This creates a COUPLING between
the constraints mod different primes.

Specifically: d = 2^S - 3^k is a FIXED number with specific factorization.
The corrSum is a SPECIFIC weighted sum. The weights 3^{k-1-i} and bases 2^{σ_i}
create algebraic dependencies between residues mod different primes.

### Approach: Inclusion-Exclusion over prime factors

N0(d) = Σ_{T ⊆ factors} (-1)^{|T|+1} · N0(∏_{p∈T} p^{a_p})

If we can bound the alternating sum to show it equals 0...

### Approach: Kloosterman-type argument

The number N0(d) can be expressed as:
N0(d) = (1/d) Σ_{a=0}^{d-1} Σ_σ ω^{a·corrSum(σ)}

where ω = e^{2πi/d}. The main term (a=0) gives C/d < 1.
If we can show |Σ_{a≠0} (...)| < 1 - C/d, then N0 = 0.

### Approach: Exponential sum bound

For each a ≠ 0 mod d:
|Σ_σ ω^{a·corrSum(σ)}| = |Σ_{T⊂{1,...,S-1}, |T|=k-1} Π_{j∈T, ranked} ω^{a·3^{k-1-rank(j)}·2^j}|

The inner product is NOT separable because the weight depends on rank.
But for large d, the oscillation should cancel most of the sum.

### Approach: Orbit constraints (most promising?)

If corrSum = n₀ · d, then n₀ = corrSum/d is the smallest element of a k-cycle.
The orbit elements satisfy:
n_{i+1} = (3·n_i + 1) / 2^{e_{i+1}}

Additional constraints:
1. All n_i are DISTINCT positive odd integers
2. n₀ is the SMALLEST
3. 3·n_i + 1 ≡ 0 mod 2^{e_{i+1}} for each i
4. The e_i are the individual exponents: e_i = σ_i - σ_{i-1}

These give a TOWER of congruence conditions on n₀.
For k ≥ 18, the counting bound C < d means that MOST residues
don't correspond to valid n₀. The orbit constraints might force 0
to be among the invalid ones.

### Key question to investigate computationally

For k=6..14 (where we have exact data):
- What are the corrSum values that are multiples of INDIVIDUAL prime factors?
- What is the "distance" of these from being multiples of d?
- Is there a pattern in how the CRT interference works?

### TODO
1. Compute exact corrSum distributions mod d for k=3..14
2. Analyze CRT interference patterns
3. Check if orbit constraints add any new information
4. Develop exponential sum bounds for cumulative case
