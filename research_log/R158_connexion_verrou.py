"""
R158 — CONNEXION AU VERROU: E_mixed^{(3)} aide-t-il à borner |S_H| ?

N_cross > 0 pour la première fois en 157 rounds. MAIS:
- Question critique: est-ce que ça aide à prouver |S_H(t)| ≤ √r ?
- La connexion doit passer par le moment 6 de B(s,t).

Test décisif: distribution de |B(s,t)|² sur les modes s
Si S_H(t) = B(0,t) est anomaliquement petit par rapport aux autres modes,
l'objet bilinéaire serait exploitable.
"""

import math, cmath
from collections import defaultdict

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

def compute_B_st(p, r, t):
    """
    Compute B(s,t) for all s = 0,...,r-1.
    B(s,t) = Σ_{a=1}^{r-1} e^{2πisa/r} · χ^{tr}(1-2^a)
    where χ is a character of order p-1.
    """
    g = primitive_root(p)
    dlog = {}
    x = 1
    for i in range(p - 1):
        dlog[x] = i
        x = (x * g) % p

    pow2 = [1] * r
    for a in range(1, r):
        pow2[a] = (pow2[a-1] * 2) % p

    h_vals = {}
    for a in range(1, r):
        h_vals[a] = (1 - pow2[a]) % p

    B_values = []
    for s in range(r):
        B = 0
        for a in range(1, r):
            hv = h_vals[a]
            if hv == 0:
                continue
            # Additive character: e^{2πi s a / r}
            add_phase = 2 * math.pi * s * a / r
            # Multiplicative character: χ^{tr}(h) = e^{2πi t r dlog(h)/(p-1)}
            mult_phase = 2 * math.pi * t * r * dlog[hv] / (p - 1)
            B += cmath.exp(1j * (add_phase + mult_phase))
        B_values.append(B)

    return B_values

# ==================================================================
# TEST 1: Distribution de |B(s,t)|² pour les modes s
# ==================================================================

print("=" * 90)
print("TEST 1: DISTRIBUTION DE |B(s,t)|² PAR MODE s")
print("=" * 90)
print("Si S_H(t) = B(0,t) est anomaliquement petit → objet exploitable")
print("Si B(0,t) est typique → pas d'information nouvelle")

test_cases = [(29, 28), (89, 11), (19, 18), (47, 23)]

for p, expected_r in test_cases:
    r = ord_mod(2, p)
    assert r == expected_r, f"r mismatch: {r} vs {expected_r}"
    g = primitive_root(p)

    print(f"\n{'='*60}")
    print(f"p = {p}, r = {r}")
    print(f"{'='*60}")

    # For several t values, compute B(s,t) and check s=0 rank
    max_SH_sq = 0
    s0_rank_sum = 0
    n_tests = 0

    for t in range(1, min(p - 1, 50)):
        B = compute_B_st(p, r, t)
        Bsq = [abs(b)**2 for b in B]

        SH_sq = Bsq[0]  # B(0,t) = S_H(t)
        max_SH_sq = max(max_SH_sq, SH_sq)

        # Rank of s=0 among all modes
        rank = sum(1 for x in Bsq if x >= SH_sq)  # rank 1 = largest

        s0_rank_sum += rank
        n_tests += 1

        if t <= 5:
            sorted_sq = sorted(Bsq, reverse=True)
            print(f"  t={t}: |B(0,t)|²={SH_sq:.2f}, "
                  f"max|B(s,t)|²={max(Bsq):.2f}, "
                  f"mean={sum(Bsq)/r:.2f}, "
                  f"rank(s=0)={rank}/{r}")
            print(f"    Top-5 modes: {[f'{x:.1f}' for x in sorted_sq[:5]]}")

    avg_rank = s0_rank_sum / n_tests
    print(f"\n  Résumé sur {n_tests} valeurs de t:")
    print(f"  max|S_H|² = {max_SH_sq:.2f}")
    print(f"  √r = {math.sqrt(r):.2f}, r = {r}")
    print(f"  max|S_H| = {math.sqrt(max_SH_sq):.2f}")
    print(f"  max|S_H|/√r = {math.sqrt(max_SH_sq)/math.sqrt(r):.4f}")
    print(f"  Rang moyen de s=0: {avg_rank:.1f} / {r}")
    print(f"  Si s=0 est typique: rang moyen ≈ {r/2}")
    print(f"  Si s=0 est anomaliquement petit: rang moyen >> {r/2}")

# ==================================================================
# TEST 2: E_mixed^{(3)} comme fraction de E^×_3(H-1)
# ==================================================================

print("\n" + "=" * 90)
print("TEST 2: E_mixed^{(3)} vs E^×_3(H-1) (énergie multiplicative seule)")
print("=" * 90)
print("E_mixed^{(3)} ≤ E^×_3(H-1) par définition (contrainte supplémentaire)")
print("Si E_mixed / E_mult est petit → la contrainte additive est sélective")

for p in [11, 17, 23, 29, 89]:
    r = ord_mod(2, p)
    if r > 30: continue

    pow2 = [1] * r
    for a in range(1, r):
        pow2[a] = (pow2[a-1] * 2) % p
    h = {a: (1 - pow2[a]) % p for a in range(1, r)}

    # E^×_3: only multiplicative constraint
    mult_groups = defaultdict(int)
    for a1 in range(1, r):
        for a2 in range(1, r):
            for a3 in range(1, r):
                prod = (h[a1] * h[a2] % p * h[a3]) % p
                mult_groups[prod] += 1
    E_mult_3 = sum(c * c for c in mult_groups.values())

    # E_mixed^{(3)}: both constraints
    mixed_groups = defaultdict(int)
    for a1 in range(1, r):
        for a2 in range(1, r):
            for a3 in range(1, r):
                s = (a1 + a2 + a3) % r
                prod = (h[a1] * h[a2] % p * h[a3]) % p
                mixed_groups[(s, prod)] += 1
    E_mixed_3 = sum(c * c for c in mixed_groups.values())

    # Additive energy only
    add_groups = defaultdict(int)
    for a1 in range(1, r):
        for a2 in range(1, r):
            for a3 in range(1, r):
                s = (a1 + a2 + a3) % r
                add_groups[s] += 1
    E_add_3 = sum(c * c for c in add_groups.values())

    n = r - 1
    print(f"\np = {p}, r = {r}")
    print(f"  E_add^(3)   = {E_add_3:>10} (énergie additive seule)")
    print(f"  E_mult^(3)  = {E_mult_3:>10} (énergie multiplicative seule)")
    print(f"  E_mixed^(3) = {E_mixed_3:>10} (les deux)")
    print(f"  E_mixed / E_mult = {E_mixed_3/E_mult_3:.4f}")
    print(f"  E_mixed / E_add  = {E_mixed_3/E_add_3:.4f}")
    print(f"  Independent prediction: E_add*E_mult/n^6 = {E_add_3*E_mult_3/n**6:.0f}")
    print(f"  E_mixed / independent = {E_mixed_3 * n**6 / (E_add_3 * E_mult_3):.4f}")

# ==================================================================
# TEST 3: La question fatale — le moment 6 aide-t-il ?
# ==================================================================

print("\n" + "=" * 90)
print("TEST 3: LE MOMENT 6 AIDE-T-IL À BORNER max|S_H| ?")
print("=" * 90)
print("""
Pour borner max|S_H| via le moment 2k:
  max|S_H|^{2k} ≤ Σ_t |S_H(t)|^{2k} = M_{2k}

Pour le moment 6 (k=3):
  M₆ = Σ_t |S_H(t)|^6 = (p-1) · E^×_3(H-1) [par orthogonalité]

  max|S_H| ≤ M₆^{1/6} = ((p-1) · E^×_3(H-1))^{1/6}

Borne triviale: E^×_3(H-1) ≤ (r-1)^3 · (r-1)^2 = (r-1)^5
  → max|S_H| ≤ (p · r^5)^{1/6} ≈ p^{1/6} · r^{5/6}

Pour battre √r: on aurait besoin de p^{1/6} · r^{5/6} < √r
  → p^{1/6} < r^{-1/3}  → IMPOSSIBLE pour p >> r.

DONC: le moment 6 seul NE PEUT PAS battre √r quand p >> r.
C'est un fait structurel: le moment 2k donne max|S_H| ~ r^{1/2} × p^{1/2k}.
Pour p ~ e^r (notre régime), le facteur p^{1/2k} = e^{r/2k} EXPLOSE.
""")

# Verify numerically
for p in [29, 89]:
    r = ord_mod(2, p)
    max_SH = 0

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

    M6 = 0
    for t in range(1, p - 1):
        S = 0
        for hv in h_vals:
            if hv == 0: continue
            phase = 2 * math.pi * t * r * dlog[hv] / (p - 1)
            S += cmath.exp(1j * phase)
        sq = abs(S) ** 2
        M6 += sq ** 3
        max_SH = max(max_SH, math.sqrt(sq))

    bound_M6 = M6 ** (1/6)
    sqrt_r = math.sqrt(r)

    print(f"p = {p}, r = {r}")
    print(f"  max|S_H| = {max_SH:.3f}")
    print(f"  √r = {sqrt_r:.3f}")
    print(f"  M₆^{1/6} = {bound_M6:.3f}")
    print(f"  M₆^{1/6} / max|S_H| = {bound_M6/max_SH:.3f}")
    print(f"  M₆^{1/6} / √r = {bound_M6/sqrt_r:.3f}")
    print()

# ==================================================================
# VERDICT FINAL
# ==================================================================

print("=" * 90)
print("VERDICT FINAL SUR LES 3 FORMALISATIONS")
print("=" * 90)
print("""
FORMALISATION 1 (Transport optimal W₁):
  W₁(H, H-1) = r TOUJOURS (matching naturel h↔h-1 avec distance 1 est optimal).
  VERDICT: [MORT] — objet constant, aucune information.

FORMALISATION 2 (Défaut d'homomorphisme Δ):
  Δ(a,b) = φ(a+b)/(φ(a)·φ(b)) est quasi-uniforme sur F_p* pour grand r.
  Énergie du défaut ≈ énergie uniforme. Δ = 1 dans 0% des cas (sauf r pair).
  Aucune connexion établie avec |S_H|.
  VERDICT: [INDÉTERMINÉ → MORT] — objet bien défini mais non exploitable.

FORMALISATION 3 (k-énergie mixte E_mixed^{(3)}, 6-tuples):
  N_cross > 0 pour 17/20 premiers testés — PREMIÈRE collision non triviale en 157 rounds!
  N_cross croît ~ r⁴ (confirmé sur r = 5..30).
  L'argument de Vieta (T175/T176/T177) NE s'applique PAS car 2 contraintes < 3 sym. fonctions.
  MAIS: la connexion au verrou est BLOQUÉE:
    - Le moment 6 donne max|S_H| ≤ (p·E^×_3)^{1/6} qui EXPLOSE quand p >> r
    - Le mode s=0 de B(s,t) n'est PAS anomaliquement petit (rang moyen ≈ r/2)
    - E_mixed^{(3)} ≤ E^×_3(H-1), donc borner E_mixed ne borne PAS E^×_3
  VERDICT: [SEMI-RÉEL] — objet non dégénéré (progrès réel) mais sans chemin vers |S_H| ≤ √r.

RÉSUMÉ: 1 mort, 1 mort, 1 semi-réel.
Le progrès est réel (première formalisation qui échappe à Vieta)
mais INSUFFISANT (pas de connexion au verrou).
""")
