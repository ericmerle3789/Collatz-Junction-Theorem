#!/usr/bin/env python3
"""
R127 — Factorisation algébrique de d(k) et vérification DP structurée.

Axe A : contournement de (H_k) par factorisation algébrique + CRT computationnel.
Protocole : computationnel STRUCTURÉ (forme fermée + certification finie).

Auteur: Campagne R126-R130
Date: 14 mars 2026
"""

import math
from functools import reduce
from collections import defaultdict

# ============================================================
# PARTIE 1 : Calcul de d(k) et factorisation algébrique
# ============================================================

def compute_S(k):
    """S = ceil(k * log2(3))"""
    return math.ceil(k * math.log2(3))

def compute_d(k):
    """d(k) = 2^S - 3^k"""
    S = compute_S(k)
    return 2**S - 3**k, S

def trial_factor(n, bound=10**6):
    """Trial division up to bound. Returns list of (prime, exponent)."""
    factors = []
    d = 2
    temp = abs(n)
    while d <= min(bound, int(math.isqrt(temp)) + 1):
        exp = 0
        while temp % d == 0:
            temp //= d
            exp += 1
        if exp > 0:
            factors.append((d, exp))
        d += 1 if d == 2 else 2
    if temp > 1:
        factors.append((temp, 1))  # remaining factor (possibly composite)
    return factors

def multiplicative_order(a, n):
    """Compute ord_n(a) = smallest r>0 with a^r ≡ 1 mod n."""
    if math.gcd(a, n) > 1:
        return None
    r = 1
    power = a % n
    while power != 1:
        power = (power * a) % n
        r += 1
        if r > n:
            return None
    return r

# ============================================================
# PARTIE 2 : DP pour N_0(m)
# ============================================================

def count_N0_dp(k, S, m):
    """
    Count N_0(m) = #{compositions A=(a_0,...,a_{k-1}), sum=S, a_i>=1 :
                     corrSum(A) ≡ 0 mod m}

    corrSum(A) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{b_j}
    where b_j = sum_{i=j+1}^{k-1} a_i = S - (a_0 + ... + a_j)

    DP state: (step j, partial_sum s, corrSum_mod_m c)
    Transition: choose a_j >= 1, with s + a_j <= S - (k-1-j)
    """
    # Precompute powers of 2 and 3 mod m
    pow2 = [1] * (S + 1)
    for i in range(1, S + 1):
        pow2[i] = (pow2[i-1] * 2) % m

    pow3 = [1] * k
    for i in range(1, k):
        pow3[i] = (pow3[i-1] * 3) % m

    # DP: for each step j, store set of reachable (s, c)
    # Use dict: s -> set of c values
    current = defaultdict(set)
    current[0].add(0)  # initial state: s=0, c=0

    for j in range(k):
        next_states = defaultdict(set)
        coeff_3 = pow3[k - 1 - j]  # 3^{k-1-j} mod m

        for s, c_set in current.items():
            # a_j ranges from 1 to S - s - (k-1-j)
            max_a = S - s - (k - 1 - j)
            for a_j in range(1, max_a + 1):
                new_s = s + a_j
                # b_j = S - new_s (but computed incrementally)
                # contribution = 3^{k-1-j} * 2^{S - new_s} mod m
                exponent = S - new_s
                contribution = (coeff_3 * pow2[exponent]) % m

                for c in c_set:
                    new_c = (c + contribution) % m
                    next_states[new_s].add(new_c)

        current = next_states

    # Count compositions reaching c ≡ 0 mod m
    # At the end, s must equal S
    if S in current:
        return 1 if 0 in current[S] else 0  # Just check existence
    return 0

def count_N0_dp_full(k, S, m):
    """
    Full count of N_0(m) (not just existence).
    Returns the actual number of compositions with corrSum ≡ 0 mod m.
    """
    pow2 = [1] * (S + 1)
    for i in range(1, S + 1):
        pow2[i] = (pow2[i-1] * 2) % m

    pow3 = [1] * k
    for i in range(1, k):
        pow3[i] = (pow3[i-1] * 3) % m

    # DP: state (s, c) -> count
    current = defaultdict(lambda: defaultdict(int))
    current[0][0] = 1

    for j in range(k):
        next_states = defaultdict(lambda: defaultdict(int))
        coeff_3 = pow3[k - 1 - j]

        for s, c_dict in current.items():
            max_a = S - s - (k - 1 - j)
            for a_j in range(1, max_a + 1):
                new_s = s + a_j
                exponent = S - new_s
                contribution = (coeff_3 * pow2[exponent]) % m

                for c, count in c_dict.items():
                    new_c = (c + contribution) % m
                    next_states[new_s][new_c] += count

        current = next_states

    if S in current:
        return current[S].get(0, 0)
    return 0

# ============================================================
# PARTIE 3 : Exécution
# ============================================================

print("=" * 70)
print("R127 — FACTORISATION ALGÉBRIQUE + DP STRUCTURÉ")
print("=" * 70)

# 3a. Calcul de d(k) et gcd(S,k)
print("\n--- TABLEAU d(k) ET STRUCTURE ---\n")
print(f"{'k':>3} {'S':>3} {'gcd':>4} {'d(k)':>25} {'Petit facteur f1':>20}")
print("-" * 80)

favorable_k = []
for k in range(22, 42):
    d, S = compute_d(k)
    g = math.gcd(S, k)
    if g > 1:
        s, m_val = S // g, k // g
        f1 = 2**s - 3**m_val
        print(f"{k:>3} {S:>3} {g:>4} {d:>25} {f1:>20}")
        favorable_k.append((k, S, g, f1, d))
    else:
        print(f"{k:>3} {S:>3} {g:>4} {d:>25} {'—':>20}")

# 3b. Factorisation des petits facteurs
print("\n--- FACTORISATION DES PETITS FACTEURS ---\n")
for k, S, g, f1, d in favorable_k:
    factors = trial_factor(f1)
    print(f"k={k}: f1 = {f1} = {' × '.join(f'{p}^{e}' if e>1 else str(p) for p,e in factors)}")

    # Vérification : produit des facteurs
    product = reduce(lambda x, y: x * y, [p**e for p, e in factors])
    assert product == f1, f"Factorisation incorrecte pour k={k}"

    # Ordres multiplicatifs
    for p, e in factors:
        if p <= 10**7:  # Only for small primes
            r = multiplicative_order(2, p)
            g_p = (p - 1) // r if r else None
            print(f"  p={p}: ord_p(2) = {r}, g = {g_p}")

# 3c. DP sur les petits facteurs
print("\n--- DP STRUCTURÉ : VÉRIFICATION N_0(f1) ---\n")

for k, S, g, f1, d in favorable_k:
    if f1 <= 2000:  # Only for very small factors
        print(f"k={k}, S={S}, f1={f1}: Computing N_0({f1})...")
        # Use existence check first
        exists = count_N0_dp(k, S, f1)
        if exists:
            # Full count
            n0 = count_N0_dp_full(k, S, f1)
            print(f"  N_0({f1}) = {n0} > 0. Modulus INUTILE.")
        else:
            print(f"  *** N_0({f1}) = 0 ! k={k} FERMÉ par facteur algébrique ! ***")
    else:
        # For larger factors, try individual primes
        factors = trial_factor(f1, bound=10**6)
        small_primes = [(p, e) for p, e in factors if p <= 10**5]
        if small_primes:
            print(f"k={k}, S={S}, f1={f1}: Testing small prime factors...")
            for p, e in small_primes:
                print(f"  Testing p={p}...")
                exists = count_N0_dp(k, S, p)
                if not exists:
                    print(f"  *** N_0({p}) = 0 ! k={k} FERMÉ ! ***")
                else:
                    print(f"  N_0({p}) > 0. Modulus inutile.")
        else:
            print(f"k={k}, S={S}, f1={f1}: No small prime factors ≤ 10^5. Skipped.")

# 3d. Trial division de d(k) pour tous k, puis DP sur petits premiers
print("\n--- TRIAL DIVISION DE d(k) POUR TOUS k ---\n")

for k in range(22, 42):
    d, S = compute_d(k)
    factors = trial_factor(d, bound=10**4)  # Small bound for speed
    small_primes = [(p, e) for p, e in factors if p <= 10**4]
    if small_primes:
        primes_str = ', '.join(f'{p}' for p, e in small_primes)
        print(f"k={k}: d(k) has small primes: {primes_str}")
        for p, e in small_primes:
            r = multiplicative_order(2, p)
            print(f"  p={p}: ord_p(2) = {r}")
    else:
        print(f"k={k}: d(k) = {d}, no prime factor ≤ 10^4")

print("\n--- DP SUR PETITS PREMIERS DE d(k) ---\n")

results = {}
for k in range(22, 42):
    d, S = compute_d(k)
    factors = trial_factor(d, bound=10**4)
    small_primes = [(p, e) for p, e in factors if p <= 500]  # Very small for speed

    for p, e in small_primes:
        print(f"k={k}, p={p}: DP mod {p}...", end=" ")
        exists = count_N0_dp(k, S, p)
        if not exists:
            print(f"*** N_0({p}) = 0 ! k={k} potentiellement FERMÉ ! ***")
            results[k] = (p, "CLOSED")
        else:
            print(f"N_0({p}) > 0")
            if k not in results:
                results[k] = (p, "OPEN")

print("\n" + "=" * 70)
print("RÉSUMÉ")
print("=" * 70)
for k in range(22, 42):
    if k in results:
        p, status = results[k]
        print(f"k={k}: {status} (tested p={p})")
    else:
        print(f"k={k}: NO SMALL PRIME FOUND")
