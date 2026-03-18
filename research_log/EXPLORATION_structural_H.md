# Structural Analysis: Why does 0 avoid Im(Ev_d)?
## Session 18 Mars 2026

### Setup

corrSum(σ) = Σ_{i=0}^{k-1} 3^{k-1-i} · 2^{σ_i}

where σ = (0, σ_1, ..., σ_{k-1}), 0 < σ_1 < ... < σ_{k-1} < S, S = ⌈k·log₂3⌉, d = 2^S - 3^k.

**Question**: Why is corrSum(σ) ≢ 0 (mod d) for all valid σ?

### Key algebraic structure

In Z/dZ, we have 2^S = 3^k (since d = 2^S - 3^k).

So corrSum mod d = Σ 3^{k-1-i} · 2^{σ_i} mod d.

Write α = 2 in Z/dZ and β = 3 in Z/dZ. Then:
corrSum = β^{k-1} · α^0 + β^{k-2} · α^{σ_1} + ... + β^0 · α^{σ_{k-1}}
        = Σ β^{k-1-i} · α^{σ_i}

The constraint is α^S = β^k in Z/dZ.

### Observation 1: corrSum as evaluation of a polynomial

Define P(X) = Σ_{i=0}^{k-1} β^{k-1-i} · X^{σ_i} ∈ (Z/dZ)[X].

Then corrSum = P(α) where α = 2 mod d.

If α generates a large subgroup of (Z/dZ)*, this polynomial evaluation cannot easily be zero.

### Observation 2: factoring corrSum

corrSum = β^{k-1} + Σ_{i=1}^{k-1} β^{k-1-i} · α^{σ_i}
        = β^{k-1} + α^{σ_1} · (β^{k-2} + Σ_{i=2}^{k-1} β^{k-1-i} · α^{σ_i - σ_1})

This gives a "nested" structure where the inner sum has the same form with smaller k.

### Observation 3: corrSum and n₀

If corrSum = n₀ · d, then n₀ = corrSum / d. Since corrSum ≥ 3^k - 2^k and d ≈ 3^k · δ:
n₀ ≥ (3^k - 2^k) / (3^k · (2^δ - 1)) ≈ 1/δ · (1 - (2/3)^k)

For δ small (approaching 0 when {k·log₂3} → 0), n₀ can be very large.

For δ close to 1 (when {k·log₂3} → 1): n₀ ≈ 1/(2^δ-1) ≈ 1.

### Observation 4: Parity constraint

If a cycle exists with n₀, then n₀ must be ODD (since we start from an odd number).

corrSum = n₀ · d = n₀ · (2^S - 3^k).

Since 3^k is odd and 2^S is even: d = 2^S - 3^k is odd.
So corrSum = n₀ · d where d is odd.

The first term of corrSum is 3^{k-1} · 2^0 = 3^{k-1} (odd).
All other terms 3^{k-1-i} · 2^{σ_i} with σ_i ≥ 1 are even.
So corrSum = 3^{k-1} + (even) = odd.

Therefore corrSum is always odd, d is always odd, so n₀ = corrSum/d would be odd/odd.
This is consistent (no contradiction from parity alone).

### Observation 5: 2-adic valuation

v₂(corrSum) = 0 (since the σ_0=0 term contributes 3^{k-1}, which is odd).
v₂(d) = 0 (since 3^k is odd and 2^S is even, d is odd).
So v₂(n₀) = 0 — n₀ is odd. Consistent, no contradiction.

### Observation 6: 3-adic valuation

v₃(corrSum) = ? The last term is 3^0 · 2^{σ_{k-1}} = 2^{σ_{k-1}} which is not divisible by 3.
So v₃(corrSum) = 0.

v₃(d) = v₃(2^S - 3^k) = v₃(2^S - 0) ... wait, 3^k ≡ 0 mod 3, and 2^S ≢ 0 mod 3.
So d ≡ 2^S mod 3 ≢ 0 mod 3. Thus v₃(d) = 0.

So v₃(n₀) = 0. Also consistent.

### Observation 7: Small prime analysis (p | d)

For a prime p | d: 2^S ≡ 3^k ≡ 0 (mod p)... wait no, d = 2^S - 3^k ≡ 0 mod p.
So 2^S ≡ 3^k mod p. This means 2^S · 3^{-k} ≡ 1 mod p.

Define q = ord_p(2·3^{-1}) = ord_p(2/3 mod p). Then S must be "compatible" with q.

Actually, 2^S ≡ 3^k mod p. Let q = ord_p(2). Then 2^S = 2^{qQ+r} where S = qQ + r.
So 2^r ≡ 3^k · 2^{-qQ} ≡ 3^k mod p.

The corrSum mod p becomes:
Σ 3^{k-1-i} · 2^{σ_i} mod p

This sum depends on σ_i mod q (where q = ord_p(2)).

### Key idea for proof

If we can show that for SOME prime p | d(k), the character sum bound gives N0(p) = 0,
then N0(d) = 0.

The FCQ approach:
N0(p) ≤ C(S-1,k-1) · max_{a≠0} |Σ_{j=0}^{q-1} ω^{a·2^j}|^{k-1} / q^{k-1}

Wait, but this bound needs to be adapted for cumulative (ordered) sequences, not independent choices.

### TODO: Adapt FCQ bound to cumulative sequences
### TODO: Compute spectral radii for actual primes dividing d(k)
### TODO: Check if there's a direct algebraic argument using 2^S = 3^k mod d
