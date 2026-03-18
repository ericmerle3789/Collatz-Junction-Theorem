# SESSION SUMMARY — 18 Mars 2026
## Autonomous Session: Junction Theorem + Audit Verification

### Mission
Resolve the nontriviality of Collatz (no positive cycles for all k).

### Critical Audit Finding (CONFIRMED)
The corrSum in `lean4_proof/Basic.lean` uses INDIVIDUAL exponents (wrong).
Steiner's equation requires CUMULATIVE exponents.
- Verified numerically for k=3..14 (exhaustive brute force)
- Range Exclusion is INVALID (cumulative range is Ω(2^{0.585k}) vs d)
- FCQ prime-by-prime is INEFFECTIVE (N0(p) > 0 for almost all p)
- The phantom at k=4 disappears with the correct formula

### Approaches Explored and Their Status

| Approach | Result | Why |
|----------|--------|-----|
| Range Exclusion | DEAD | Wrong formula; correct range too wide |
| FCQ/Spectral per prime | DEAD | N0(p)>0 for most primes with cumulative formula |
| CRT interference | OBSERVED | N0(d)=0 despite N0(p)>0, but no proof |
| Exponential sums L∞ | FAILS | Need max|G| < 1, but max|G| ≈ 0.2C >> 1 |
| Exponential sums L2 | FAILS | Collision count too high (sparse image) |
| Orbit constraints | OPEN | Standard SdW approach, limited to k<68 |

### What IS Proved (Honest Assessment)

1. **Junction Theorem** (Lean-formalized): C(S-1,k-1) < d for k ≥ 18
   - Implies: Ev_d is non-surjective for k ≥ 18
   - Combined with SdW: non-surjective for ALL k ≥ 1

2. **Steiner equation** (Lean-proved with cumulative exponents)

3. **Conditional no-cycle** (Lean-proved): Under hypothesis H, no positive cycles

4. **N0_cumulative = 0 for k < 68** (by SdW)

### What is NOT Proved

**Hypothesis H**: 0 ∈ missed residues of Ev_d for k ≥ 68.
This is EQUIVALENT to the positive-cycle Collatz conjecture.

### Key Discoveries

1. **k=5 Rosetta Stone**: 35 sequences cover 12/13 residues mod 13.
   0 is the UNIQUE missed residue. Small enough for complete algebraic analysis.

2. **CRT anti-correlation**: For composite d, individual prime conditions
   on corrSum ≡ 0 are anti-correlated. The mechanism is unexplained.

3. **The gap is FUNDAMENTAL**: Standard analytic number theory tools
   (L∞, L2 exponential sums, large sieve) cannot bridge the gap between
   "at least one residue is missed" and "0 is missed."

### Files Created

| File | Purpose |
|------|---------|
| scripts/verify_audit_corrsum.py | Audit verification |
| scripts/dp_n0_fast.py | DP N0 computation |
| scripts/dp_n0_numpy.py | Numpy-optimized DP |
| scripts/crt_analysis.py | CRT interference |
| scripts/k5_deep_analysis.py | k=5 algebraic analysis |
| scripts/exp_sums_small.py | Exponential sums (FFT) |
| scripts/exp_sums_extended.py | Extended exp sums |
| scripts/verify_proof_condition.py | Proof condition check |
| docs/PROOF_STATUS_20260318.md | Corrected proof status |
| research_log/FINDING_*.md | 4 finding documents |
| research_log/EXPLORATION_*.md | 2 exploration documents |
| research_log/CORRECTION_*.md | Retraction of false claim |

### Honest Conclusion

Proving the absence of ALL nontrivial positive Collatz cycles is equivalent
to a major open problem. The Junction Theorem is a significant partial result
that can be published independently. It proves non-surjectivity of the
evaluation map, which is new and non-trivial.

The full resolution requires a fundamentally new idea — not just
computation or standard analytic tools. Possible directions:
- Algebraic structure of Im(Ev_d) (why 0 is specifically avoided)
- Connection to arithmetic dynamics (heights, Lehmer's conjecture)
- p-adic methods (ultrametric structure of the orbit space)
- Information-theoretic arguments (entropy of the Collatz map)

### What to Tell Eric

The audit was correct. The corrSum formula error invalidates Range Exclusion
and the "unconditional for all k" claim. The Junction Theorem (nonsurjectivity)
is valid and publishable. The full cycle absence requires proving H, which is
equivalent to the Collatz positive-cycle conjecture — a major open problem.
I explored 6 approaches; all hit fundamental barriers for k ≥ 68.
The k=5 case (Rosetta Stone) and CRT interference are promising research leads.
