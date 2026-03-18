# CRT Interference Patterns — Key Data
## 18 Mars 2026

### Core Data Table

| k | d | factors | C | C/d | coverage | N0(d) | 0 missed |
|---|---|---------|---|-----|----------|-------|----------|
| 3 | 5 | 5 | 6 | 1.20 | 80% | 0 | ✓ |
| 4 | 47 | 47 | 20 | 0.43 | 38% | 0 | ✓ |
| 5 | 13 | 13 | 35 | 2.69 | 92% | 0 | ✓ |
| 6 | 295 | 5·59 | 126 | 0.43 | 36% | 0 | ✓ |
| 7 | 1909 | 23·83 | 462 | 0.24 | 22% | 0 | ✓ |
| 8 | 1631 | 7·233 | 792 | 0.49 | 40% | 0 | ✓ |
| 9 | 13085 | 5·2617 | 3003 | 0.23 | 21% | 0 | ✓ |
| 10 | 6487 | 13·499 | 5005 | 0.77 | 54% | 0 | ✓ |
| 11 | 84997 | 11·7727 | 19448 | 0.23 | 21% | 0 | ✓ |
| 12 | 517135 | 5·59·1753 | 75582 | 0.15 | 14% | 0 | ✓ |
| 13 | 502829 | prime | 125970 | 0.25 | 23% | 0 | ✓ |
| 14 | 3605639 | 79·45641 | 497420 | 0.14 | 13% | 0 | ✓ |

### Key Observations

1. **k=5 is remarkable**: C/d = 2.69 (MORE sequences than residues),
   yet 0 is the ONE residue not hit out of 13. 12/13 = 92% coverage.
   This is NOT a counting argument — it's STRUCTURAL.

2. **k=4 phantom GONE**: With cumulative exponents, N0(47)=0.
   The "phantom" at k=4 was an artifact of the individual exponent formula.

3. **CRT interference for composite d**:
   - k=6: N0(5)=36, N0(59)=6, expected overlap 1.7, actual 0
   - k=10: N0(13)=410, N0(499)=35, expected overlap 2.87, actual 0
   - k=12: Pairwise overlaps exist (300, 36, 6) but triple = 0

4. **Heuristic product rule**: N0(d) ≈ C · Π (N0(p_i)/C)
   works reasonably (gives ~1.7 for k=6, actual 0).

### Why 0 is special: Steiner's equation

corrSum ≡ 0 mod d is EXACTLY the Collatz cycle equation.
0 is not "any residue" — it's the residue that would correspond
to the existence of a positive cycle. The algebraic structure of
Steiner's equation (3^k ≡ 2^S mod d) creates a coupling that
prevents 0 from being attained.

### Leads for proof

1. **k=5 case study**: With only 13 residues, understand algebraically
   WHY the image of Ev_d avoids 0. This is a small enough system
   to analyze completely.

2. **Large sieve approach**: Bound Σ |character sums|² to control
   the concentration of corrSum at 0 mod d.

3. **Orbit constraints**: corrSum ≡ 0 mod d implies specific
   arithmetic conditions on the orbit that may be contradictory.

4. **Baker-type argument on n₀**: If n₀ = corrSum/d exists,
   Baker's theorem constrains |n₀·d - corrSum| in ways that
   might be incompatible.
