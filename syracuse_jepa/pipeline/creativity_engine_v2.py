#!/usr/bin/env python3
"""
CREATIVITY ENGINE V2 — Autonomous proof generation loop
=========================================================

RULE: No computational/brute-force proofs. Must be ALGEBRAIC for all k.
RULE: Don't stop until a universal proof is found or all avenues exhausted.
RULE: Each cycle must produce a NEW idea, not rehash old ones.

Architecture:
  INSIGHT GENERATOR → FORMALIZE → TEST → MUTATE → LOOP

Key data to work from:
- REST' = Σ ρ^i · 2^{δ_i} where ρ = 2/3 mod d, δ weakly increasing
- corrSum ≡ 0 mod d ⟺ REST' ≡ -1 mod d
- For k=3,5: REST'+1 ∈ <2> (proves it)
- For all k: residues outside <2,3> still avoid 0
- 3ρ = 2 in Z/dZ (KEY identity)

The DEEPEST algebraic fact: 3ρ = 2 means ρ = 2/3.
And REST' = Σ ρ^i · 2^{δ_i} = Σ ρ^i · (3ρ)^{δ_i} = Σ 3^{δ_i} · ρ^{i+δ_i}

Since i + δ_i = σ_i (the original cumulative position):
REST' = Σ 3^{δ_i} · ρ^{σ_i}

And REST' + 1 = 1 + Σ_{i=1}^{k-1} 3^{δ_i} · ρ^{σ_i}
             = ρ^0 · 3^0 + Σ_{i=1}^{k-1} 3^{δ_i} · ρ^{σ_i}  (since δ_0=0, σ_0=0)
             = Σ_{i=0}^{k-1} 3^{δ_i} · ρ^{σ_i}

SO: REST' + 1 = Σ_{i=0}^{k-1} 3^{δ_i} · ρ^{σ_i}

This is a sum of k terms, each of the form 3^a · ρ^b where a=δ_i ≥ 0, b=σ_i ≥ 0.

IN (Z/dZ)*: 3 and ρ = 2/3 are both units (since gcd(3,d)=1 and gcd(2,d)=1).
The product 3^a · ρ^b is a UNIT for all a,b ≥ 0.

A SUM of units can be 0 (e.g., 1 + (-1) = 0 in Z/2Z).
But REST'+1 is a sum of k POSITIVE (in Z) terms, each ≥ 1.
In Z/dZ, "positive" doesn't mean anything directly, but in Z,
REST'+1 = corrSum/3^{k-1} which is a POSITIVE rational number > 0.

Wait — REST' + 1 = corrSum / 3^{k-1}. And corrSum > 0 (it's a sum of positive terms).
So REST' + 1 > 0 IN Z. But we need REST' + 1 ≢ 0 mod d.

REST' + 1 = corrSum / 3^{k-1} in Z (exact integer division since 3^{k-1} | corrSum??)
Actually NO: corrSum = 3^{k-1} + Σ 3^{k-1-i}·2^{σ_i}. The first term is 3^{k-1}.
The second term 3^{k-2}·2^{σ_1} might not be divisible by 3^{k-1}.
So corrSum / 3^{k-1} is NOT in general an integer.

Hmm, but REST' was defined in Z/dZ, not Z. Let me reconsider.

In Z/dZ: REST' = corrSum · (3^{k-1})^{-1} mod d.
REST' + 1 = (corrSum + 3^{k-1}) · (3^{k-1})^{-1} mod d.
         = (corrSum + 3^{k-1}) / 3^{k-1} mod d.

corrSum + 3^{k-1} = 2·3^{k-1} + Σ_{i=1}^{k-1} 3^{k-1-i}·2^{σ_i}
                  = 3^{k-1}·2 + Σ_{i≥1} 3^{k-1-i}·2^{σ_i}

Divided by 3^{k-1}: 2 + Σ 3^{-i}·2^{σ_i} mod d.

So REST'+1 = 2 + Σ_{i=1}^{k-1} (1/3)^i · 2^{σ_i} mod d.

Hmm, this is just the original formula. Let me try the δ version again more carefully.

REST'+1 = Σ_{i=0}^{k-1} 3^{δ_i} · ρ^{σ_i} where ρ = 2/3, δ_i = σ_i - i.

Term i=0: 3^0 · ρ^0 = 1.
Term i=1: 3^{δ_1} · ρ^{σ_1} where δ_1 = σ_1 - 1 ≥ 0.
...

Each term 3^{δ_i} · ρ^{σ_i} = 3^{δ_i} · (2/3)^{σ_i} = 2^{σ_i} · 3^{δ_i - σ_i}
= 2^{σ_i} · 3^{-i} (since δ_i = σ_i - i).

So each term is 2^{σ_i}/3^i. In Z, this is 2^{σ_i}/3^i which is an integer
only if 3^i | 2^{σ_i}, which never happens (2 and 3 are coprime).

But in Z/dZ, 3^{-i} is well-defined. So each term is 2^{σ_i}·3^{-i} mod d.

REST'+1 = Σ_{i=0}^{k-1} 2^{σ_i} · 3^{-i} mod d.

Now, in Z: corrSum = 3^{k-1} · (REST'+1) mod d. And corrSum is a positive
integer. corrSum > d for k ≥ 3 (verified). So REST'+1 mod d = corrSum/3^{k-1} mod d.

The KEY QUESTION remains: can REST'+1 ≡ 0 mod d?

Equivalently: can Σ 2^{σ_i}/3^i ≡ 0 mod d?

Let me define T = Σ_{i=0}^{k-1} 2^{σ_i} · 3^{k-1-i}. This is corrSum.
Then T ≡ 0 mod d is the cycle condition.

I keep going in circles. Let me try a COMPLETELY different approach.

=== NEW APPROACH: Resultant/GCD of polynomials ===

Define P_σ(X) = Σ_{i=0}^{k-1} 3^{k-1-i} · X^{σ_i} ∈ Z[X].
Define D(X) = X^S - 3^k ∈ Z[X].

Then corrSum = P_σ(2) and d = D(2).

corrSum ≡ 0 mod d ⟺ d | P_σ(2) ⟺ D(2) | P_σ(2).

In Z[X], this is: does Res(P_σ(X), D(X)) have 2 as a root?
Or equivalently: does gcd(P_σ(X), D(X)) in Z[X] evaluated at X=2 give 0?

If gcd(P_σ, D) = 1 in Q[X] for all σ, then D ∤ P_σ in Z[X],
but that doesn't directly mean D(2) ∤ P_σ(2) in Z.

HOWEVER: if we work in the RING Z[X]/(D(X)):
P_σ mod D is a polynomial of degree < S (since deg P_σ < S).
P_σ(2) mod D(2) = (P_σ mod D)(2).

Since D is irreducible over Q... IS D(X) = X^S - 3^k irreducible over Q?
No! It factors. X^S - 3^k = X^S - 3^k. If S and k share a common factor g > 1:
X^S - 3^k = (X^{S/g})^g - (3^{k/g})^g which factors by cyclotomic considerations.

For g = gcd(S,k): X^S - 3^k = Π_{d|g} Φ_d(X^{S/g}, 3^{k/g})? Not exactly standard.

Actually, X^n - a factors over Q iff a = b^d for some b ∈ Q, d | n, d > 1.
X^S - 3^k: is 3^k a perfect d-th power for some d | S, d > 1?
3^k is a perfect d-th power iff d | k.
So X^S - 3^k is reducible iff gcd(S, k) > 1... wait, that's not right either.

The factoring of X^n - a: X^n - a is irreducible over Q iff:
1. For every prime p dividing n, a is not a p-th power in Q, AND
2. If 4 | n, then a ∉ -4Q^4.

For X^S - 3^k: we need to check if 3^k is a p-th power for primes p | S.
3^k is a p-th power iff p | k. So X^S - 3^k is irreducible iff no prime p | gcd(S,k).
i.e., gcd(S, k) = 1.

For most k: S = ⌈k·log₂3⌉. S and k share common factors?
k=3, S=5: gcd=1. X^5 - 27 is IRREDUCIBLE over Q!
k=5, S=8: gcd=1. X^8 - 243 is IRREDUCIBLE.
k=6, S=10: gcd=2. X^10 - 729 = X^10 - 3^6 REDUCIBLE (since 2|gcd(10,6)=2,
and 3^6 = (3^3)^2 = 27^2, so X^10 - 27^2 = (X^5 - 27)(X^5 + 27)).

So for k where gcd(S, k) = 1: D(X) = X^S - 3^k is IRREDUCIBLE over Q.
This means Q[X]/(D(X)) is a NUMBER FIELD of degree S!

In this number field: the element X (= α = 2 when evaluated) satisfies α^S = 3^k.
P_σ(α) is an algebraic integer in this field.

corrSum ≡ 0 mod d means P_σ(α) ≡ 0 mod (α^S - 3^k) in Z.
But α^S = 3^k in the number field. So P_σ(α) is an element of the ring of
integers of Q(α), and we need to understand its norm/divisibility.

THIS IS ALGEBRAIC NUMBER THEORY.

The norm N(P_σ(α)) = Π_{conjugates} P_σ(α_j) where α_j are the S roots of X^S - 3^k.
d = N(α - 2)? No, d = D(2) = 2^S - 3^k.

Actually, d = Π_{j=1}^{S} (2 - α_j) where α_j = 3^{k/S} · ζ_S^j are the roots of X^S - 3^k.
And P_σ(2) = Π... no, P_σ(2) is just a single evaluation, not a norm.

Hmm. But in the number field Q(α):
corrSum = P_σ(α) evaluated at the SPECIFIC root α that gives α = 2.
The other roots give different "corrSums" at different evaluation points.

If the norm N(P_σ(α)) is coprime to d... then corrSum is coprime to d.
N(P_σ(α)) = |Resultant(P_σ, D) / leading coeff|.

THIS COULD WORK: if Res(P_σ, D) is coprime to d for all σ, then N₀=0.

But computing Res for all σ is again exponential...

UNLESS: we can bound |Res(P_σ, D)| or show it's coprime to D(2) = d
using properties of the resultant.

Let me think about when Res(P_σ, D) can be divisible by d.

Res(P_σ, D) = Π_{i,j} (α_i - β_j) where α_i are roots of P_σ and β_j of D.
Or: Res(P_σ, D) = Π_{j} P_σ(β_j) = Π_{j} P_σ(3^{k/S}·ζ^j).

So Res(P_σ, D) = Π_{j=0}^{S-1} P_σ(3^{k/S}·ζ^j) where ζ = e^{2πi/S}.

For d | Res: d | Π P_σ(3^{k/S}·ζ^j). Since d = Π (2 - 3^{k/S}·ζ^j):
d | Res iff for some prime p | d, p divides both (2 - α_j) and P_σ(α_j) for some j.

This is getting deep into algebraic number theory. The irreducibility of X^S - 3^k
over Q (when gcd(S,k)=1) gives us access to Dedekind's theory.

I think this is the RIGHT framework but it needs serious mathematical work.
Let me implement what I can and test numerically.
"""

import sys, os
from math import ceil, log2, comb, gcd
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


def compute_resultant_mod(k, sigma, p):
    """
    Compute Res(P_σ, D) mod p where D(X) = X^S - 3^k.
    Res(P_σ, D) = Π_{j: D(β_j)=0} P_σ(β_j).
    Since we work mod p: the roots of D mod p are {β : β^S ≡ 3^k mod p}.
    """
    S = compute_S(k)
    # Find all S-th roots of 3^k mod p
    target = pow(3, k, p)
    roots = [x for x in range(p) if pow(x, S, p) == target]

    if not roots:
        return None  # D has no roots mod p

    # P_σ(β) for each root β
    product = 1
    for beta in roots:
        val = sum(pow(3, k-1-i, p) * pow(beta, sigma[i], p) for i in range(len(sigma))) % p
        product = (product * val) % p

    return product


def test_resultant_approach(k_max=10):
    """Test: is Res(P_σ, D) always coprime to d?"""
    print("RESULTANT APPROACH TEST")
    print("=" * 60)

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 50000: continue

        coprimality = gcd(S, k)
        print(f"\nk={k}, S={S}, d={d}, gcd(S,k)={coprimality}")
        print(f"  X^{S} - 3^{k} irreducible over Q: {coprimality == 1}")

        # For small primes dividing d, check resultant
        factors = {}
        n = d
        for p in range(2, min(1000, n)):
            while n % p == 0:
                factors[p] = factors.get(p, 0) + 1
                n //= p
        if n > 1:
            factors[n] = 1

        for p in sorted(factors.keys())[:3]:
            if p > 10000: continue

            # Count how many σ have Res(P_σ, D) ≡ 0 mod p
            n_res_zero = 0
            n_total = 0
            for sigma in enumerate_cumulative_sequences(k, S):
                res = compute_resultant_mod(k, sigma, p)
                n_total += 1
                if res is not None and res == 0:
                    n_res_zero += 1

            print(f"  p={p}: Res≡0 mod p for {n_res_zero}/{n_total} sequences")


def explore_norm_in_number_field(k_max=8):
    """
    For gcd(S,k)=1: Q(α) where α^S = 3^k is a number field of degree S.
    The element P_σ(α) lives in this field.
    Its norm N(P_σ(α)) = Π P_σ(α·ζ^j) over all S-th roots of unity ζ.

    If |N(P_σ)| is always coprime to d = D(2) = 2^S - 3^k,
    then P_σ(2) is coprime to d, hence corrSum ≢ 0 mod d.

    We can compute N(P_σ) mod d using the Chinese Remainder Theorem
    and the factorization of D mod small primes.
    """
    print("\n═══ NORM IN NUMBER FIELD ═══")

    for k in [3, 5, 7]:
        S = compute_S(k)
        d = compute_d(k)
        g = gcd(S, k)
        if g != 1:
            print(f"  k={k}: gcd(S,k)={g} ≠ 1, skipping")
            continue

        C = count_cumulative_sequences(k, S)
        print(f"\n  k={k}, S={S}, d={d}, field degree={S}")
        print(f"  X^{S} - {3**k} irreducible over Q ✓")

        # For each σ, compute the "norm" = Π P_σ(β) over all β^S = 3^k
        # We'll compute this mod d by computing mod each prime factor of d
        factors = {}
        n = d
        for p in range(2, min(100000, n)):
            while n % p == 0:
                factors[p] = factors.get(p, 0) + 1
                n //= p
        if n > 1:
            factors[n] = 1

        # For each σ, compute "norm mod d" via CRT
        norms_mod_d = []
        if C > 20000: continue

        for sigma in enumerate_cumulative_sequences(k, S):
            norm_residues = {}
            for p in factors:
                if p > 50000: continue
                res = compute_resultant_mod(k, sigma, p)
                norm_residues[p] = res

            # Check if all residues computed
            if all(v is not None for v in norm_residues.values()):
                # Simple check: is any residue 0?
                any_zero = any(v == 0 for v in norm_residues.values())
                norms_mod_d.append((sigma, norm_residues, any_zero))

        n_norm_zero = sum(1 for _, _, z in norms_mod_d if z)
        print(f"  Norms with some factor ≡ 0: {n_norm_zero}/{len(norms_mod_d)}")

        # KEY: The norm N(P_σ) is a product over ALL conjugates.
        # N(P_σ) mod p = Π P_σ(β_j) mod p where β_j are roots of D mod p.
        # If D splits completely mod p (S roots), this is a product of S values.
        # If D has no roots mod p, Res = 1 (empty product) — automatically coprime!


def explore_irreducibility_pattern(k_max=30):
    """Check which k have gcd(S,k) = 1 (irreducible D)."""
    print("\n═══ IRREDUCIBILITY PATTERN ═══")
    irr_count = 0
    total = 0
    for k in range(3, k_max + 1):
        S = compute_S(k)
        g = gcd(S, k)
        irr = (g == 1)
        if irr: irr_count += 1
        total += 1
        marker = "✓ IRR" if irr else f"  RED (gcd={g})"
        print(f"  k={k:3d}, S={S:3d}, gcd={g:2d} {marker}")
    print(f"\n  {irr_count}/{total} have gcd(S,k)=1 (irreducible D)")


if __name__ == '__main__':
    explore_irreducibility_pattern()
    test_resultant_approach()
    explore_norm_in_number_field()
