# FINDING: Near-Miss Residuals = ±1 or ±2
## 18 Mars 2026

### The Pattern

For k=3..12, the closest corrSum to a multiple of d has residual:

| k | d | min |residual| | n₀ nearest | residual factors |
|---|---|------------------|-------------|-----------------|
| 3 | 5 | 1 | 4 | 1 |
| 4 | 47 | 2 | 3 | 2 |
| 5 | 13 | 1 | 20 | 1 |
| 6 | 295 | 4 | 3 | 2² |
| 7 | 1909 | 2 | 3 | 2 |
| 8 | 1631 | 1 | 6 | 1 |
| 9 | 13085 | 2 | 15 | 2 |
| 10 | 6487 | 1 | 84 | 1 |
| 11 | 84997 | 1 | 16 | 1 |
| 12 | 517135 | 1 | 4 | 1 |

### Key Observation

The residual is almost always ±1 or ±2. NEVER 0.

gcd(residual, d) = 1 in ALL cases. The residual is COPRIME to d.

### Why This Matters

If we could prove that for ALL k and ALL σ:
  corrSum(σ) mod d ∈ {1, 2, ..., d-1}  (never 0)
  AND the nearest miss has |residual| ≥ 1

This is a Diophantine statement about:
  Σ 3^{k-1-i} · 2^{σ_i} ≢ 0 (mod 2^S - 3^k)

The "±1" residuals suggest a connection to Catalan-Mihailescu:
  2^a - 3^b = ±1 has only the solutions (a,b) = (1,1), (2,1), (3,2).

### GCD Analysis

corrSum is ALWAYS coprime to d when d is prime (k=3,4,5,13).
For composite d, gcd(corrSum, d) can be a proper divisor but NEVER d itself.

### Potential Proof Path

If corrSum and d share the structure of "almost-Catalan" equations:
  corrSum = Σ 3^{k-1-i} · 2^{σ_i} ≈ q · (2^S - 3^k) ± small

The "±small" could be bounded below by 1 using Baker-type arguments
on linear forms in 2 and 3 logarithms.

This connects to the FUNCTIONAL EQUATION paradigm:
P(2) mod (2^S - 3^k) is never 0 because the polynomial P has
structure incompatible with the modulus.
