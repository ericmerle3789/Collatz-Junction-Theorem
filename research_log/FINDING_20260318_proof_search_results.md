# PROOF SEARCH LOOP — Results
## 18 Mars 2026

### 10 Lemmas Tested on 727,869 sequences (k=3..14)

| Lemma | True? | Implications |
|-------|-------|-------------|
| L1: corrSum > d | ✓ TRUE | n₀ ≥ 1 if divisible |
| L2: corrSum ≢ 0 mod d | ✓ TRUE | = THE TARGET |
| L3: gcd(corrSum,d) = 1 | ✗ FALSE | coprime approach fails |
| L4: corrSum mod d is odd | ✗ FALSE | parity not sufficient |
| L5: rest ≢ -base mod d | ✓ TRUE | = L2 reformulation, structural |
| L6: frac > 0.001/√d | ✓ TRUE | fractional part bounded away |
| L7: orbit kills at e₁ | ✓ TRUE | orbit always fails (vacuous since L2) |
| L8: ≢ 0 mod largest p^a | ✗ FALSE | can hit prime power factors |
| L9: v₂(3n₀+1) < σ₁ | ✗ FALSE | not always true |
| L10: in (Z/dZ)* | ✗ FALSE | not always coprime |

### Key Insight: L5 as Proof Path

L5 says: writing corrSum = 3^{k-1} + REST(σ),
REST(σ) mod d never equals -(3^{k-1}) mod d.

This splits the problem:
- FIXED part: 3^{k-1} mod d (determined by k)
- VARIABLE part: REST(σ) = Σ_{i≥1} 3^{k-1-i}·2^{σ_i} mod d

For L2: corrSum ≡ 0 mod d ⟺ REST ≡ -3^{k-1} mod d.
So L5 = L2 rephrased. But the rephrasing reveals:

**The image of REST (over all valid σ) avoids one specific residue.**

REST is a weighted sum of 2^{σ_i} for σ₁ < ... < σ_{k-1} in {1,...,S-1},
with weights 3^{k-2}, 3^{k-3}, ..., 1.

The forbidden value is -3^{k-1} mod d.

### Proof Strategy

To prove L5 for all k:
1. Show that REST mod d always misses the target -3^{k-1} mod d
2. This is a WEIGHTED SUBSET SUM problem in Z/dZ
3. The weights are geometric (powers of 3)
4. The values are geometric (powers of 2)
5. The modulus has the algebraic relation 2^S ≡ 3^k mod d

The coupling 2^S = 3^k mod d ties the values to the weights.
This is the ALGEBRAIC OBSTRUCTION.
