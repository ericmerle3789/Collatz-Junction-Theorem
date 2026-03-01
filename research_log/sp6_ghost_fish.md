# SP6 Investigation: Ghost Fish and the Three-Mesh Net

**Date:** 2026-03-01
**Phase:** SP6 (continuation of SP5 investigation)
**Method:** GPS Protocol (6 phases, ~30 experiments, 15 discoveries)
**Status:** Completed, feasibility elevated 3.5/5 → 4/5

---

## Context

Phase SP5 established three proof regimes for Condition (Q):
1. **Affine Transport** (Phases 4--5): covers p ≤ 97
2. **Convolution contraction**: covers primes with small ρ_p
3. **Open**: 17 "hard" primes with small ord_p(2) and large ρ_p

The 17 hard primes (Mersenne-type) resisted convolution because their
geometric orbit structure prevents cancellation in character sums
(ρ_p ≈ 0.6--0.96 instead of the heuristic 1/√m).

**The question**: can these primes actually divide d(k) = 2^S − 3^k
in the "danger zone" [18, k_min), where convolution has not yet kicked in?

---

## Discovery D13: Ghost Fish (sp6_ghost_fish.py)

Among the 17 hard primes identified in SP5:
- **16/17** never divide d(k) for any k ∈ [18, 300)
- **1/17** (p = 2113, ord = 44) appears at k = 24, but k_min = 19,
  so k = 24 > k_min and convolution already covers it

**Zero dangerous pairs (k, p).**

The hard primes are "ghosts": theoretically menacing but absent
from the waters where they would be needed to produce a cycle.

## Discovery D14: Ghost Fish LARGE (sp6_ghost_fish_large.py)

Six large primes (p > 10^6) with ord_p(2) ≤ 60 tested:
all are ghosts in [18, 5000).

Key insight — **anti-correlation**: small ord_p(2) implies large
ord_p(3), which makes d(k) ≡ 0 (mod p) rare. Expected number of
hits E ∈ [10^{−2}, 10^{−17}].

## The Tunnel (sp6_tunnel_factors.py)

Factored d(k) for k ∈ [18, 45]: 69 distinct prime factors found.
- 18 have ord_p(2) ≤ 60
- Only one (p = 2113) fails convolution at k = 18
- All small primes dividing d(k) pass convolution (p = 7: ρ = 0.25,
  p = 73: ρ = 0.31)
- Median ord_p(2) among factors: 4848

## The Three-Mesh Net (sp6_three_mesh_net.py)

**Exhaustive test**: all primes dividing 2^m − 1 for m = 1..100.

| Mesh | Coverage | Method |
|------|----------|--------|
| Affine Transport | 24 primes | p ≤ 97, unconditional |
| Convolution PASS | 72 primes | (p−1)·ρ^{17} < 0.041 at k = 18 |
| Ghost Fish | 72 primes | convolution fails but danger zone empty |
| **Total** | **168/168** | **Zero failures** |

All factorizations of 2^m − 1 (m ≤ 100) are complete; no residual
cofactor remains.

Extreme case: M_89 = 2^89 − 1 (25 digits), ρ = 0.962,
k_min = 1688, zone width = 1670 values checked → ghost.

## Discovery D15: Two Barriers Theorem (sp6_mersenne_direct.py)

For every known Mersenne prime M_q = 2^q − 1 with q ≤ 127:
direct verification confirms the ghost property.

Two independent barriers protect against divisibility:

**Barrier 1 — Size** [rigorous]:
  M_q | d(k) implies d(k) ≥ M_q = 2^q − 1.
  Since d(k) < 2·3^k, we get k ≥ q·log_3(2) ≈ 0.63q.

**Barrier 2 — Density** [heuristic]:
  M_q | d(k) iff 3^k ∈ {2^0, 2^1, ..., 2^{q−1}} mod M_q.
  Density ≤ q/(M_q − 1) ≈ q/2^q per value of k.

**Expected hits** in the danger zone [k_size, k_min):
  E ≤ (k_min − k_size) × q/(M_q − 1) ≤ C·q³/2^q → 0

| q | E (expected) |
|---|-------------|
| 13 | ~0.17 (verified directly) |
| 31 | ~10^{−5} |
| 61 | < 10^{−14} |
| 127 | < 10^{−34} |
| 521 | < 10^{−140} |

---

## Anti-Hallucination Audit

**Rigorous:**
- ρ < 1 for all p (character orthogonality)
- Convolution bound: |p·N₀ − C|/C ≤ (p−1)·ρ^{k−1}
- Affine Transport for p ≤ 97
- Ghost Fish verified for 168 primes (m ≤ 100)
- Ghost Fish verified for Mersenne q ≤ 127 (direct computation)
- Size barrier (d(k) < 2·3^k)

**Heuristic:**
- ρ ≈ 1/√m (unproved; Weil gives ρ ≤ √p/m, too weak for Mersenne)
- Density barrier (equidistribution of 3^k mod M_q)
- Ghost Fish for Mersenne q > 127 (E < 10^{−30} but not verified)
- Ghost Fish for non-Mersenne primes with ord > 100

**Precise theoretical gap:**
  For an unknown prime p with ord_p(2) = m and p very large
  (possibly an undiscovered Mersenne), prove that
  3^k ∉ {2^0, ..., 2^{m−1}} mod p for all k ∈ [18, k_min(p)).
  This gap is super-exponentially small in probability but
  nonzero in mathematical certainty.

---

## Conclusion

The three-mesh net covers ALL 168 tested primes with zero exceptions
across ~35,000 individual verifications. The feasibility of
establishing Condition (Q) for all k ≥ 18 is elevated to **4/5**
(from 3.5/5), with potential to reach 4.5/5 if the Ghost Fish
theorem is formalized or the computation extended to m ≤ 300.

**Scripts:** sp6_ghost_fish.py, sp6_ghost_fish_large.py,
sp6_tunnel_factors.py, sp6_three_mesh_net.py, sp6_mersenne_direct.py
