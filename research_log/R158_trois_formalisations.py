"""
R158 — TROIS FORMALISATIONS DU "+" (MÉCANISME DE COUPLAGE)

Formalisation 1: Transport optimal W₁(H, H-1) sur Z/pZ
Formalisation 2: Défaut d'homomorphisme Δ(a,b) de φ(a)=1-2^a
Formalisation 3: k-énergie mixte E_mixed^{(3)} avec 6-tuples

Pour chaque: calcul numérique + diagnostic de connexion au verrou |S_H|≤√r
"""

import math
from itertools import permutations
from collections import defaultdict

def ord_mod(base, p):
    r, x = 1, base % p
    while x != 1:
        x = (x * base) % p
        r += 1
    return r

def modinv(a, p):
    return pow(a, p - 2, p)

def compute_SH(p, r):
    """Compute all |S_H(t)|² for t=1,...,p-2."""
    # S_H(t) = Σ_{a=1}^{r-1} χ^{tr}(1-2^a)
    # where χ = primitive character of order p-1
    # Using DLog: χ(x) = exp(2πi·dlog(x)/(p-1))

    # First compute discrete log table
    g = primitive_root(p)
    dlog = {}
    x = 1
    for i in range(p - 1):
        dlog[x] = i
        x = (x * g) % p

    # Compute h(a) = 1-2^a mod p for a=1,...,r-1
    h_vals = []
    pow2 = 2
    for a in range(1, r):
        h_vals.append((1 - pow2) % p)
        pow2 = (pow2 * 2) % p

    # S_H(t) = Σ_a exp(2πi·t·r·dlog(h(a))/(p-1))
    import cmath
    SH_sq = []
    max_SH_sq = 0
    for t in range(1, p - 1):
        S = 0
        for h in h_vals:
            if h == 0:
                continue
            phase = 2 * math.pi * t * r * dlog[h] / (p - 1)
            S += cmath.exp(1j * phase)
        sq = abs(S) ** 2
        SH_sq.append(sq)
        max_SH_sq = max(max_SH_sq, sq)

    return SH_sq, max_SH_sq

def primitive_root(p):
    """Find a primitive root mod p."""
    if p == 2:
        return 1
    phi = p - 1
    # Factor phi
    factors = set()
    n = phi
    for d in range(2, int(n**0.5) + 2):
        while n % d == 0:
            factors.add(d)
            n //= d
    if n > 1:
        factors.add(n)

    for g in range(2, p):
        ok = True
        for f in factors:
            if pow(g, phi // f, p) == 1:
                ok = False
                break
        if ok:
            return g
    return None

# ==================================================================
# FORMALISATION 1: TRANSPORT OPTIMAL W₁(H, H-1)
# ==================================================================

def wasserstein_H_Hminus1(p, r):
    """
    Compute W₁ between H={2^a: a=0,...,r-1} and H-1={2^a-1: a=0,...,r-1}
    on (Z/pZ, additive distance min(|x-y|, p-|x-y|)).

    Uses Hungarian algorithm approximation for small sets.
    For small r, brute force over sorted matching.
    """
    # Build H and H-1
    H = []
    Hminus1 = []
    pow2 = 1
    for a in range(r):
        H.append(pow2)
        Hminus1.append((pow2 - 1) % p)
        pow2 = (pow2 * 2) % p

    # Sort both sets
    H_sorted = sorted(H)
    Hm1_sorted = sorted(Hminus1)

    # Cost function: circular distance on Z/pZ
    def circ_dist(x, y):
        d = abs(x - y)
        return min(d, p - d)

    # For small r, compute optimal matching by trying sorted shifts
    # (This is optimal for circular Wasserstein)
    min_cost = float('inf')
    for shift in range(r):
        cost = sum(circ_dist(H_sorted[i], Hm1_sorted[(i + shift) % r]) for i in range(r))
        min_cost = min(min_cost, cost)

    # Also compute the "natural" matching: 2^a ↔ 2^a-1
    natural_cost = sum(1 for _ in range(r))  # |2^a - (2^a-1)| = 1 always

    return min_cost, natural_cost, H, Hminus1

# ==================================================================
# FORMALISATION 2: DÉFAUT D'HOMOMORPHISME
# ==================================================================

def homomorphism_defect(p, r):
    """
    φ(a) = 1 - 2^a mod p
    Defect: Δ(a,b) = φ(a+b) / (φ(a) · φ(b)) in F_p*

    If φ were a group homomorphism (Z/rZ,+) → (F_p*,×), Δ=1 everywhere.
    The defect measures deviation from homomorphism.

    Key statistics:
    - Distribution of Δ(a,b)
    - "Defect energy" = #{(a₁,b₁,a₂,b₂): Δ(a₁,b₁)=Δ(a₂,b₂)}
    - Average |Δ-1|
    """
    pow2 = [1] * r
    for a in range(1, r):
        pow2[a] = (pow2[a-1] * 2) % p

    phi = lambda a: (1 - pow2[a % r]) % p

    # Compute all Δ(a,b) for a,b ∈ {1,...,r-1}
    delta_values = {}
    delta_count = defaultdict(int)
    zero_defects = 0  # cases where φ(a)=0 or φ(b)=0

    for a in range(1, r):
        for b in range(1, r):
            ab = (a + b) % r
            if ab == 0:
                continue  # φ(0) = 0, skip

            phi_a = phi(a)
            phi_b = phi(b)
            phi_ab = phi(ab)

            if phi_a == 0 or phi_b == 0:
                zero_defects += 1
                continue

            # Δ = φ(a+b) / (φ(a)·φ(b)) mod p
            denom = (phi_a * phi_b) % p
            delta = (phi_ab * modinv(denom, p)) % p
            delta_values[(a, b)] = delta
            delta_count[delta] += 1

    # Statistics
    n_pairs = len(delta_values)
    n_delta_1 = delta_count.get(1, 0)  # How many Δ=1?
    n_distinct = len(delta_count)

    # Defect energy (multiplicative energy of Δ values)
    defect_energy = sum(c * c for c in delta_count.values())

    # If Δ were uniform: energy ≈ n_pairs²/(p-1)
    # If Δ ≡ 1: energy = n_pairs²

    return {
        'n_pairs': n_pairs,
        'n_delta_1': n_delta_1,
        'frac_delta_1': n_delta_1 / max(n_pairs, 1),
        'n_distinct': n_distinct,
        'defect_energy': defect_energy,
        'energy_ratio': defect_energy / max(n_pairs, 1),  # vs n_pairs (trivial)
        'uniform_energy': n_pairs**2 / (p - 1) if p > 1 else 0,
        'zero_defects': zero_defects,
        'delta_count': dict(sorted(delta_count.items(), key=lambda x: -x[1])[:10])
    }

# ==================================================================
# FORMALISATION 3: k-ÉNERGIE MIXTE AVEC 6-TUPLES (k=3)
# ==================================================================

def k_energy_mixed_k3(p, r):
    """
    E_mixed^{(3)} = #{(a₁,...,a₆) ∈ {1,...,r-1}^6 :
        a₁+a₂+a₃ ≡ a₄+a₅+a₆ mod r           [ADD]
        AND (1-2^a₁)(1-2^a₂)(1-2^a₃) = (1-2^a₄)(1-2^a₅)(1-2^a₆) [MULT]}

    Key insight: For k=3, the Vieta argument requires 3 elementary symmetric
    functions to determine a triple. We only have 2 constraints (e₁ via ADD,
    and e₂-e₃ via MULT combined with ADD). So N_cross MIGHT be > 0!

    Method: group triples by (sum mod r, product mod p), count collisions.
    """
    pow2 = [1] * r
    for a in range(1, r):
        pow2[a] = (pow2[a-1] * 2) % p

    h = {a: (1 - pow2[a]) % p for a in range(1, r)}

    # Group triples by (sum mod r, product mod p)
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

    for key, triples in triple_groups.items():
        n = len(triples)
        E_mixed += n * n

        # Count trivial: (a4,a5,a6) is a permutation of (a1,a2,a3)
        for t1 in triples:
            s1 = sorted(t1)
            for t2 in triples:
                s2 = sorted(t2)
                if s1 == s2:
                    E_trivial += 1

    N_cross = E_mixed - E_trivial

    return E_mixed, E_trivial, N_cross

def k_energy_analysis(p, r, E_mixed, E_trivial, N_cross):
    """Analyze the k=3 energy results."""
    n = r - 1  # number of indices

    # Trivial expected: each triple has at most 6 permutations in the group
    # E_trivial ≈ (number of triples) × (avg permutations per triple)
    # Total triples: n^3

    return {
        'E_mixed': E_mixed,
        'E_trivial': E_trivial,
        'N_cross': N_cross,
        'ratio_Ncross_to_Etrivial': N_cross / max(E_trivial, 1),
        'E_mixed_over_n3': E_mixed / n**3 if n > 0 else 0,
        'E_mixed_over_n4': E_mixed / n**4 if n > 0 else 0,
        'N_cross_over_n3': N_cross / n**3 if n > 0 else 0,
        'N_cross_over_n4': N_cross / n**4 if n > 0 else 0,
    }

# ==================================================================
# MAIN
# ==================================================================

print("=" * 90)
print("R158 — TROIS FORMALISATIONS DU '+' (MÉCANISME DE COUPLAGE)")
print("=" * 90)

# Test primes: use small ones for k=3 energy (O(r^3) memory)
test_primes_small = [31, 89, 127]
test_primes_medium = [31, 89, 127, 257, 521, 1031, 8191]

# ---- FORMALISATION 1 ----
print("\n" + "=" * 90)
print("FORMALISATION 1: TRANSPORT OPTIMAL W₁(H, H-1)")
print("=" * 90)

for p in test_primes_medium:
    r = ord_mod(2, p)
    min_cost, natural_cost, H, Hminus1 = wasserstein_H_Hminus1(p, r)

    # Compare with max|S_H|
    try:
        SH_sq, max_SH_sq = compute_SH(p, r)
        max_SH = math.sqrt(max_SH_sq)
        sqrt_r = math.sqrt(r)
        ratio = max_SH / sqrt_r
    except:
        max_SH = None
        ratio = None

    print(f"\np = {p}, r = {r}")
    print(f"  W₁(H, H-1) optimal = {min_cost}")
    print(f"  W₁ naturel (h↔h-1) = {natural_cost} (toujours r, car |2^a-(2^a-1)|=1)")
    print(f"  W₁/r = {min_cost/r:.4f}")
    print(f"  W₁/p = {min_cost/p:.6f}")
    if max_SH is not None:
        print(f"  max|S_H| = {max_SH:.3f}, √r = {sqrt_r:.3f}, ratio = {ratio:.4f}")

    # Key test: does W₁ correlate with max|S_H|/√r ?
    # If W₁ is large, H and H-1 are "far apart" → coupling is weak → S_H small?

# ---- FORMALISATION 2 ----
print("\n" + "=" * 90)
print("FORMALISATION 2: DÉFAUT D'HOMOMORPHISME Δ(a,b) = φ(a+b)/(φ(a)φ(b))")
print("=" * 90)

for p in test_primes_medium:
    r = ord_mod(2, p)
    result = homomorphism_defect(p, r)

    print(f"\np = {p}, r = {r}")
    print(f"  Paires (a,b) testées: {result['n_pairs']}")
    print(f"  Δ = 1 dans {result['n_delta_1']} cas ({result['frac_delta_1']:.4f})")
    print(f"  Valeurs distinctes de Δ: {result['n_distinct']}")
    print(f"  Énergie du défaut: {result['defect_energy']}")
    print(f"  Énergie / n_pairs: {result['energy_ratio']:.2f} (trivial: n_pairs={result['n_pairs']})")
    print(f"  Énergie uniforme attendue: {result['uniform_energy']:.2f}")
    print(f"  Ratio énergie/uniforme: {result['defect_energy']/max(result['uniform_energy'],1):.2f}")
    print(f"  Top-10 valeurs de Δ: {result['delta_count']}")

# ---- FORMALISATION 3 ----
print("\n" + "=" * 90)
print("FORMALISATION 3: k-ÉNERGIE MIXTE E_mixed^{(3)} AVEC 6-TUPLES")
print("=" * 90)
print("(Seuls petits premiers car O(r³) en mémoire)")

for p in test_primes_small:
    r = ord_mod(2, p)
    if r > 30:
        print(f"\np = {p}, r = {r} — SKIP (r trop grand pour 6-tuples brute force)")
        continue

    print(f"\np = {p}, r = {r}")
    print(f"  Calcul en cours... ({(r-1)**3} triples à indexer)")

    E_mixed, E_trivial, N_cross = k_energy_mixed_k3(p, r)
    analysis = k_energy_analysis(p, r, E_mixed, E_trivial, N_cross)

    print(f"  E_mixed^(3)  = {E_mixed}")
    print(f"  E_trivial    = {E_trivial}")
    print(f"  **N_cross    = {N_cross}**")
    print(f"  N_cross / E_trivial = {analysis['ratio_Ncross_to_Etrivial']:.4f}")
    print(f"  E_mixed / (r-1)³    = {analysis['E_mixed_over_n3']:.4f}")
    print(f"  E_mixed / (r-1)⁴    = {analysis['E_mixed_over_n4']:.6f}")
    print(f"  N_cross / (r-1)³    = {analysis['N_cross_over_n3']:.4f}")
    print(f"  N_cross / (r-1)⁴    = {analysis['N_cross_over_n4']:.6f}")

    if N_cross > 0:
        print(f"\n  *** N_cross > 0 ! LA DÉGÉNÉRESCENCE DE VIETA EST BRISÉE ***")
        print(f"  *** C'est la première formalisation avec des collisions non triviales ***")
    else:
        print(f"\n  N_cross = 0 — dégénéré comme T177")

# ---- ALGEBRAIC ANALYSIS FOR k=3 ----
print("\n" + "=" * 90)
print("ANALYSE ALGÉBRIQUE: POURQUOI k=3 DEVRAIT ÉCHAPPER À VIETA")
print("=" * 90)
print("""
Pour k=2 (4-tuples T177):
  Contrainte ADD: e₁(x₃,x₄) = e₁(x₁,x₂)      [1 equation]
  Contrainte MULT: e₁-e₂ fixed (via expansion)    [donne e₂ quand e₁ fixé]
  → 2 equations pour 2 inconnues (e₁,e₂) → déterminé → N_cross=0

Pour k=3 (6-tuples):
  Contrainte ADD: e₁(x₄,x₅,x₆) = e₁(x₁,x₂,x₃)        [1 equation]
  Contrainte MULT: 1-e₁+e₂-e₃ = constant                  [1 equation]
  Combined: e₂-e₃ = constant (puisque e₁ déjà fixé)        [1 equation]
  → 2 equations pour 3 inconnues (e₁,e₂,e₃) → 1 degré de liberté → N_cross PEUT être > 0!

C'est la différence fondamentale: au-delà des paires, Vieta ne suffit plus
à déterminer le multiensemble.
""")

print("=" * 90)
print("VERDICT GLOBAL")
print("=" * 90)
