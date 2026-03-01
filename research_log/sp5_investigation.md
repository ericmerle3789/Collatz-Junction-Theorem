# SP5 Investigation: Condition (Q) Direct Route

**Date**: March 2026
**Methodology**: GPS (3-level systematic research protocol)
**Status**: Investigation complete — 3/5 feasibility

---

## Problem Statement

**SP5**: Prove Condition (Q) for all k >= 18 and all primes p | d(k):

    |p * N_0(p) - C| <= 0.041 * C

where d(k) = 2^S - 3^k, C = C(S-1, k-1), and N_0(p) counts the compositions
A of S into k parts with corrSum(A) = 0 mod p.

Condition (Q) is a quantitative sufficient condition for Hypothesis (H).

---

## Deliverables Produced

| # | Deliverable | Description |
|---|-------------|-------------|
| O1 | Formalization | Complete problem setup and algebraic framework |
| O2 | Literature review | 15 references, connections to character sums |
| O3 | Experimental results | 5 experiments, 25+ test cases, 0 failures |
| O4 | Theoretical analysis | Multi-scale decomposition, Theorems A-B |
| O5 | Double verification | 7 independent tests, 1 bug found and fixed |
| O6 | Synthesis | Final assessment and strategic recommendations |

---

## Key Results

### Verified Computationally

- **Condition (Q) holds for all k in [18, 28]** and all primes p | d(k)
  tested (25 cases, 0 failures)
- Worst case: k=22, p=7 (ratio = 0.013, margin = 3.2x above threshold)
- Phase uniformity confirmed by Rayleigh test in all cases

### Theorems

**Proposition A (Approximate Coset Symmetry)** — Verified:
N_r(p) is approximately constant on orbits of multiplication by 2 in Z/pZ.
Exact when ord_p(2) | (S-1), approximate otherwise (boundary effects < 2.2%).
For p=7: reduces the problem from 7 to 3 quasi-equal values.

**Multi-scale decomposition**:
- Regime I (full coverage): trivial when ord_p(2) | (S-1)
- Regime II (p=7): coset mixing + cancellation (margin 3.2x-22.9x)
- Regime III (large p > 10): Cauchy-Schwarz suffices (95% of cases, margin 7x-2800x)

**Decay for p=7**: ratio ~ k^{-6.3} (verified k=22..38)

### Erratum (O5)

A formula indexation error was found and corrected during double verification:
- **Incorrect**: corrSum = sum 3^j * 2^{a_{k-1-j}} (reversed weights)
- **Correct**: corrSum = sum_{m=0}^{k-2} 3^m * 2^{a_{m+1}} (ascending order)

No impact on any conclusion (structure invariant under weight permutation).

---

## Architecture of Proof (Proposed)

```
For each k >= 18, for each prime p | d(k):

  IF ord_p(2) | (S-1):               [Regime I — Trivial]
    -> Uniform distribution by complete symmetry
    -> (Q) satisfied with margin >> 10x

  ELSE IF p > 10 and CS bound works:  [Regime III — Cauchy-Schwarz]
    -> |sum T(t)| <= sqrt((p-1) * p * Var(N_r))
    -> Bound Var(N_r) via Parseval
    -> (Q) satisfied (verified for all tested p > 10)

  ELSE (p=7, small ord_p(2)):         [Regime II — Residual]
    For k <= 40: Direct DP verification
    For k >= 41: Decay argument (ratio(k) << 0.041)
```

---

## What Remains

| Component | Difficulty | Approach |
|-----------|-----------|----------|
| Extend DP to k=29..40 | 1/5 | Computation (feasible) |
| CS bound for p > 10 (general) | 2/5 | Universal Var(N_r) bound |
| Formal decay for p=7, k >= 41 | 3/5 | Local CLT, 4th moment |
| Gap at k=22, p=7 (CS fails) | 4/5 | Phase cancellation |

**Residual lock**: Prove |p * N_0(7) - C| / C -> 0 as k -> infinity
with rate at least k^{-1}.

---

## Recommendation

**Hybrid strategy SP3+SP5** (feasibility 3.5/5):
- S-Hybrid 1: Direct verification k <= 40 + asymptotic decay k >= 41
- Avoids the open locks V1, V2 of SP3 entirely
- Sole residual lock: p=7 decay formalization

See `scripts/verify_condition_q.py` for reproducible verification.
