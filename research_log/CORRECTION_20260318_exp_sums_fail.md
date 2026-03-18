# CORRECTION: Exponential Sum Bounds Fail for N0=0
## 18 Mars 2026

### Error
I incorrectly claimed max|G| < d-C was sufficient for N0=0.
The correct condition is (d-1)·max|G| < d-C, i.e., max|G| < (d-C)/(d-1) ≈ 1.
Since max|G| ≈ 0.2·C >> 1, the L∞ bound FAILS.

### L2 (Parseval) also fails
The L2 bound requires (d-C)² > (d-1)·Δ where Δ = d·Σcount² - C².
Since only ~14-25% of residues are hit, the collision count is large,
making Δ ≈ 6·C² and (d-1)·Δ ≈ 6·C²·d >> d² ≈ (d-C)².

### Why standard exponential sum bounds fail
The evaluation map Im(Ev_d) covers only 13-25% of Z/dZ.
This extreme non-uniformity defeats both L∞ and L2 approaches.
The non-uniformity is EXPECTED: C < d means the image is sparse.
Standard equidistribution arguments require the image to be "dense" (C >> d).

### Status
Proving N0(d) = 0 for all k ≥ 68 remains OPEN.
This is equivalent to the positive-cycle Collatz conjecture.

### What is publishable
The Junction Theorem (C < d for k ≥ 18) is a valid, formalized result.
Combined with SdW (k < 68): "for every k ≥ 1, the evaluation map Ev_d
is non-surjective." This is a new result worth publishing on its own.
