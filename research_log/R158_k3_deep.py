"""
R158 — DEEP INVESTIGATION: k=3 mixed energy (6-tuples)

N_cross > 0 detected for p=89 (r=11)! First non-trivial collision in 157 rounds.
Need to understand:
1. Growth rate of N_cross with r
2. Which primes give N_cross > 0 vs = 0
3. What are the actual non-trivial collisions?
4. Connection to |S_H|
5. Does this resist the kill switches?
"""

from collections import defaultdict
import math, cmath

def ord_mod(base, p):
    r, x = 1, base % p
    while x != 1:
        x = (x * base) % p
        r += 1
    return r

def primitive_root(p):
    if p == 2: return 1
    phi = p - 1
    factors = set()
    n = phi
    for d in range(2, int(n**0.5) + 2):
        while n % d == 0:
            factors.add(d)
            n //= d
    if n > 1: factors.add(n)
    for g in range(2, p):
        if all(pow(g, phi // f, p) != 1 for f in factors):
            return g
    return None

def compute_max_SH(p, r):
    """Compute max|S_H(t)| for t=1,...,p-2."""
    g = primitive_root(p)
    dlog = {}
    x = 1
    for i in range(p - 1):
        dlog[x] = i
        x = (x * g) % p

    pow2 = [1] * r
    for a in range(1, r):
        pow2[a] = (pow2[a-1] * 2) % p
    h_vals = [(1 - pow2[a]) % p for a in range(1, r)]

    max_sq = 0
    for t in range(1, p - 1):
        S = 0
        for h in h_vals:
            if h == 0: continue
            phase = 2 * math.pi * t * r * dlog[h] / (p - 1)
            S += cmath.exp(1j * phase)
        sq = abs(S) ** 2
        max_sq = max(max_sq, sq)

    return math.sqrt(max_sq)

def k3_energy_with_examples(p, r, show_examples=True):
    """Compute k=3 mixed energy and show non-trivial collision examples."""
    pow2 = [1] * r
    for a in range(1, r):
        pow2[a] = (pow2[a-1] * 2) % p
    h = {a: (1 - pow2[a]) % p for a in range(1, r)}

    triple_groups = defaultdict(list)
    indices = list(range(1, r))

    for a1 in indices:
        for a2 in indices:
            for a3 in indices:
                s = (a1 + a2 + a3) % r
                prod = (h[a1] * h[a2] % p * h[a3]) % p
                triple_groups[(s, prod)].append((a1, a2, a3))

    E_mixed = 0
    E_trivial = 0
    N_cross = 0
    examples = []

    for key, triples in triple_groups.items():
        n = len(triples)
        E_mixed += n * n

        for i, t1 in enumerate(triples):
            s1 = sorted(t1)
            for j, t2 in enumerate(triples):
                s2 = sorted(t2)
                if s1 == s2:
                    E_trivial += 1
                elif show_examples and len(examples) < 20:
                    examples.append((t1, t2, key))

    N_cross = E_mixed - E_trivial
    return E_mixed, E_trivial, N_cross, examples

# ==================================================================
# SYSTEMATIC SCAN: all primes up to 500 with r ≤ 30
# ==================================================================

print("=" * 90)
print("SCAN SYSTÉMATIQUE: E_mixed^{(3)} pour primes avec r ≤ 30")
print("=" * 90)

from sympy import isprime  # Use sympy for primality test
# Fallback if sympy not available
try:
    from sympy import isprime
except ImportError:
    def isprime(n):
        if n < 2: return False
        if n == 2: return True
        if n % 2 == 0: return False
        for i in range(3, int(n**0.5) + 1, 2):
            if n % i == 0: return False
        return True

results = []
print(f"\n{'p':>6} {'r':>4} {'(r-1)^3':>8} {'E_mixed':>10} {'E_triv':>10} {'N_cross':>10} {'N_cross/n³':>12} {'max|SH|':>8} {'√r':>6} {'ratio':>8}")
print("-" * 90)

for p in range(3, 600):
    if not isprime(p): continue
    r = ord_mod(2, p)
    if r > 30 or r < 5: continue

    E_mixed, E_trivial, N_cross, _ = k3_energy_with_examples(p, r, show_examples=False)
    n = r - 1

    try:
        max_SH = compute_max_SH(p, r)
        sqrt_r = math.sqrt(r)
        ratio = max_SH / sqrt_r
    except:
        max_SH = float('nan')
        ratio = float('nan')

    results.append((p, r, n, E_mixed, E_trivial, N_cross, max_SH, ratio))
    marker = " ***" if N_cross > 0 else ""
    print(f"{p:>6} {r:>4} {n**3:>8} {E_mixed:>10} {E_trivial:>10} {N_cross:>10} {N_cross/n**3:>12.6f} {max_SH:>8.2f} {sqrt_r:>6.2f} {ratio:>8.4f}{marker}")

# ==================================================================
# DETAILED EXAMPLES for primes with N_cross > 0
# ==================================================================

print("\n" + "=" * 90)
print("EXEMPLES DÉTAILLÉS: collisions non triviales")
print("=" * 90)

for p, r, n, E_mixed, E_trivial, N_cross, max_SH, ratio in results:
    if N_cross == 0: continue

    print(f"\np = {p}, r = {r}, N_cross = {N_cross}")
    _, _, _, examples = k3_energy_with_examples(p, r, show_examples=True)

    seen = set()
    for t1, t2, key in examples[:10]:
        sig = (tuple(sorted(t1)), tuple(sorted(t2)))
        if sig in seen or sig[::-1] in seen: continue
        seen.add(sig)

        s_mod_r, prod_mod_p = key
        # Verify
        pow2 = [1] * r
        for a in range(1, r):
            pow2[a] = (pow2[a-1] * 2) % p
        h = lambda a: (1 - pow2[a]) % p

        h1 = [h(a) for a in t1]
        h2 = [h(a) for a in t2]
        e1_1 = sum(pow2[a] for a in t1) % p  # e₁ of {2^a}
        e1_2 = sum(pow2[a] for a in t2) % p

        print(f"  Triple 1: {t1} → h-values: {h1}, sum_indices={sum(t1)%r}, prod_h={h1[0]*h1[1]*h1[2]%p}")
        print(f"  Triple 2: {t2} → h-values: {h2}, sum_indices={sum(t2)%r}, prod_h={h2[0]*h2[1]*h2[2]%p}")
        print(f"  e₁(2^a): {e1_1} vs {e1_2}")
        print(f"  Sorted triples: {sorted(t1)} vs {sorted(t2)} — genuinely different!")
        print()

# ==================================================================
# CORRELATION ANALYSIS: N_cross vs max|S_H|/√r
# ==================================================================

print("\n" + "=" * 90)
print("ANALYSE DE CORRÉLATION: N_cross vs max|S_H|/√r")
print("=" * 90)

positive_results = [(p, r, N_cross, ratio) for p, r, n, E_mixed, E_trivial, N_cross, max_SH, ratio in results]

# Group by N_cross > 0 vs = 0
ncross_pos = [(p, r, N_cross, ratio) for p, r, N_cross, ratio in positive_results if N_cross > 0]
ncross_zero = [(p, r, N_cross, ratio) for p, r, N_cross, ratio in positive_results if N_cross == 0]

print(f"\nPrimes avec N_cross > 0: {len(ncross_pos)}")
if ncross_pos:
    avg_ratio_pos = sum(r for _, _, _, r in ncross_pos) / len(ncross_pos)
    print(f"  Ratio moyen max|SH|/√r: {avg_ratio_pos:.4f}")

print(f"\nPrimes avec N_cross = 0: {len(ncross_zero)}")
if ncross_zero:
    avg_ratio_zero = sum(r for _, _, _, r in ncross_zero) / len(ncross_zero)
    print(f"  Ratio moyen max|SH|/√r: {avg_ratio_zero:.4f}")

# ==================================================================
# ALGEBRAIC STRUCTURE: what determines N_cross > 0?
# ==================================================================

print("\n" + "=" * 90)
print("STRUCTURE ALGÉBRIQUE: qu'est-ce qui détermine N_cross > 0 ?")
print("=" * 90)

print(f"\n{'p':>6} {'r':>4} {'p mod r':>7} {'(p-1)/r':>7} {'gcd(r,6)':>8} {'N_cross':>10}")
print("-" * 50)
for p, r, n, E_mixed, E_trivial, N_cross, max_SH, ratio in results:
    print(f"{p:>6} {r:>4} {p%r:>7} {(p-1)//r:>7} {math.gcd(r,6):>8} {N_cross:>10}")

# ==================================================================
# KEY QUESTION: algebraic analysis of when N_cross > 0
# ==================================================================

print("\n" + "=" * 90)
print("QUESTION CLÉ: Quand N_cross > 0 ?")
print("=" * 90)

print("\nHypothèse 1: N_cross > 0 ⟺ r ≥ 11 (assez d'espace)")
print("  Contre-exemple: r=13 (p=8191) a N_cross=?")

# Check p=8191 specially
p = 8191
r = ord_mod(2, p)
print(f"  p=8191, r={r}")
if r <= 30:
    E_mixed, E_trivial, N_cross, _ = k3_energy_with_examples(p, r, show_examples=False)
    print(f"  N_cross = {N_cross}")
    if N_cross > 0:
        print("  → Hypothèse 1 compatible")
    else:
        print("  → Hypothèse 1 COMPATIBLE (r=13, mais N_cross=0 possible pour specific arithmetic)")

# Test more primes with r in range 10-20
print("\nTest spécifique: primes avec r = 10..20")
for p in range(3, 2000):
    if not isprime(p): continue
    r = ord_mod(2, p)
    if r < 10 or r > 20: continue
    if any(pp == p for pp, _, _, _, _, _, _, _ in results): continue

    E_mixed, E_trivial, N_cross, _ = k3_energy_with_examples(p, r, show_examples=False)
    n = r - 1
    try:
        max_SH = compute_max_SH(p, r)
        sqrt_r = math.sqrt(r)
        ratio = max_SH / sqrt_r
    except:
        max_SH = float('nan')
        ratio = float('nan')

    marker = " ***" if N_cross > 0 else ""
    print(f"  p={p:>6}, r={r:>3}, N_cross={N_cross:>8}, N_cross/n³={N_cross/n**3:.6f}, max|SH|/√r={ratio:.4f}{marker}")
