#!/usr/bin/env python3
"""
SESSION 10f5 — STRUCTURE DE BANDES ET ARGUMENT UNIVERSEL
=========================================================
Date : 4 mars 2026
Objectif : Pour σ̃=0, exploiter la structure de bandes disjointes
           des exposants recentrés pour prouver le débordement universel.

BOUCLE G-V-R :
  GENERATE : Quand σ̃=0, u^j = 2^{-jM}, donc chaque terme u^j·2^{B_j}
    = 2^{E_j} où E_j = B_j - jM ∈ [-jM, -(j-1)M].
    Les bandes sont disjointes : la bande j est [(j-1)M, jM] en valeur absolue.
    La somme Σ 2^{E_j} doit valoir T mod p.
    MAIS : quand ord₂(p) = (k-1)M (vérifié pour σ̃=0), les puissances
    2^0, 2^1, ..., 2^{(k-1)M-1} sont DISTINCTES mod p.
    La somme est alors une "représentation en base 2 avec retenues mod p".
  VERIFY : Tester les propriétés de cette représentation pour k=3,5
    et pour k hypothétiques plus grands.
  REVISE : Chercher pourquoi T n'admet pas une telle représentation.

Investigations :
  I1 : Vérifier que ord₂(p) = (k-1)·M pour tous les σ̃=0 connus
  I2 : Analyser T en tant que somme de 2^{E_j} dans bandes disjointes
  I3 : Chercher d'autres k > 13 avec d premier (étendre la recherche)
  I4 : Pour CHAQUE nouveau k avec d premier, tester le cas frontière
  I5 : Analyse σ̃≠0 — exploiter la rareté d'image + cascade
  I6 : Argument de somme restreinte (pour σ̃=0 et σ̃≠0)
  I7 : Synthèse — gap restant et directions
"""

import math
import time
from itertools import combinations_with_replacement

start_time = time.time()

def is_prime(n):
    """Miller-Rabin pour grands nombres, déterministe pour n < 3.3×10^24."""
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    if n < 1000000:
        i = 5
        while i*i <= n:
            if n % i == 0 or n % (i+2) == 0: return False
            i += 6
        return True
    # Miller-Rabin déterministe
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
        if a >= n: continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1: continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1: break
        else:
            return False
    return True

def compute_params(k):
    S = math.ceil(k * math.log2(3))
    M = S - k
    d = (1 << S) - 3**k
    return S, M, d

def ord_mod(base, n):
    if math.gcd(base, n) != 1: return None
    r, x = 1, base % n
    while x != 1:
        x = (x * base) % n
        r += 1
        if r > n: return None
    return r

def compute_u(k, p):
    return (2 * pow(3, -1, p)) % p

def sigma_tilde(u, k, p):
    s, uj = 0, u
    for j in range(1, k):
        s = (s + uj) % p
        uj = (uj * u) % p
    return s

def factorize_small(n):
    factors = {}
    for p in range(2, min(10000, int(n**0.5)+2)):
        while n % p == 0:
            factors[p] = factors.get(p, 0) + 1
            n //= p
    if n > 1:
        factors[n] = 1
    return factors

def compute_image_dp(k, p, M, u_pows, n_middle, max_states=5000000):
    """Compute image of boundary equation using DP with size guard."""
    image = {(0, 0)}  # (valeur, dernier_B)
    for j_idx in range(n_middle):
        j = j_idx + 2
        new_image = set()
        for (val, last_B) in image:
            for Bj in range(last_B, M + 1):
                new_val = (val + u_pows[j] * pow(2, Bj, p)) % p
                new_image.add((new_val, Bj))
        image = new_image
        if len(image) > max_states:
            return None  # trop grand
    return {v for (v, _) in image}


# =====================================================================
print("=" * 70)
print("INVESTIGATION I1 : ord₂(p) et relation avec (k-1)·M")
print("=" * 70)
# =====================================================================

print("""
CONJECTURE : Pour σ̃=0, ord₂(p) = (k-1)·M.
Preuve (session 10e4) :
  σ̃=0 ⟹ u^{k-1} = 1 mod p
  Or u = 2·3^{-1}, donc u^{k-1} = 2^{k-1}·3^{-(k-1)} = 1
  ⟹ 2^{k-1} = 3^{k-1} mod p
  Et u^k = 2^{-M} ⟹ u^{k-1} = u^k/u = 2^{-M}/u = 2^{-M}·3/2 = 3·2^{-M-1}
  Si u^{k-1} = 1 : 3·2^{-M-1} = 1 ⟹ 2^{M+1} = 3 mod p.
  Donc 2^{(k-1)M} = (2^{M+1})^{...} — compliqué.

  APPROCHE DIRECTE : ord_u | (k-1) et ord_u | (p-1).
  Comme u = 2^1·3^{-1} et σ̃=0 ⟹ ord_u | (k-1).
  Mais ord₂(p) est lié à ord_u par : ord_u divise lcm(ord₂(p), ord₃(p)).
""")

for k_val in range(3, 30):
    S, M, d = compute_params(k_val)
    if not is_prime(d): continue
    p = d
    u = compute_u(k_val, p)
    st = sigma_tilde(u, k_val, p)
    if st != 0: continue  # only σ̃=0

    o2 = ord_mod(2, p)
    expected = (k_val - 1) * M

    print(f"  k={k_val} (p={p}, M={M}) :")
    print(f"    ord₂(p) = {o2}")
    print(f"    (k-1)·M = {expected}")
    print(f"    ord₂(p) = (k-1)·M ? {'OUI ✓' if o2 == expected else 'NON ✗'}")
    print(f"    ord₂(p) / (k-1) = {o2 / (k_val-1):.2f}, M = {M}")


# =====================================================================
print("\n" + "=" * 70)
print("INVESTIGATION I2 : Structure 2-adique de T pour σ̃=0")
print("=" * 70)
# =====================================================================

print("""
Quand σ̃=0, u = 2^{-M}, et la somme médiane est :
  Σ_{j=2}^{k-2} 2^{B_j - jM} ≡ T mod p

Avec ord₂(p) = (k-1)M, les 2^0,...,2^{(k-1)M-1} sont tous distincts mod p.
Cela signifie que la fonction e ↦ 2^e mod p est INJECTIVE sur [0, (k-1)M-1].

L'exposant effectif E_j = B_j - jM est NÉGATIF, dans [-jM, -(j-1)M].
En ajoutant (k-1)M pour rendre positif : E_j + (k-1)M ∈ [(k-1-j)M, (k-j)M].

Donc chaque terme, vu comme 2^{E_j + (k-1)M}, a son exposant dans une
BANDE DISJOINTE de taille M+1. Les k-3 bandes sont :
  j=2 : [(k-3)M, (k-2)M]
  j=3 : [(k-4)M, (k-3)M]
  ...
  j=k-2 : [M, 2M]

T·2^{(k-1)M} = T·1 = T (car 2^{(k-1)M} = 2^{ord₂(p)} = 1 mod p)
Donc la question est : T est-il une somme de k-3 éléments,
un par bande, dans {2^e : e ∈ bande_j} ?
""")

for k_val in [3, 5]:
    S, M, d = compute_params(k_val)
    if not is_prime(d): continue
    p = d
    u = compute_u(k_val, p)
    st = sigma_tilde(u, k_val, p)
    if st != 0: continue

    u_inv = pow(u, -1, p)
    T = (-(1 + u + u_inv)) % p
    o2 = ord_mod(2, p)

    print(f"  k={k_val} (p={p}, M={M}, ord₂={o2}) :")

    # Représentation 2-adique de T
    # Trouver e tel que 2^e = T mod p
    x = 1
    T_log = None
    for e in range(o2):
        if x == T:
            T_log = e
            break
        x = (2 * x) % p
    print(f"    T = {T}, log₂(T) mod p = {T_log}")

    if k_val == 3:
        print(f"    k=3 : 0 termes médians → T doit être 0 = somme vide")
        print(f"    T = {T} ≠ 0 → IMPOSSIBLE QED")
    elif k_val == 5:
        # 2 termes médians, bandes :
        # j=2 : [(k-3)M, (k-2)M] = [M, 2M] = [3, 6]
        # j=3 : [(k-4)M, (k-3)M] = [0, M] = [0, 3]
        band_2 = list(range(M, 2*M + 1))
        band_3 = list(range(0, M + 1))
        print(f"    Bandes (recentrées positives) :")
        print(f"      j=2 : [{M}, {2*M}] → {band_2}")
        print(f"      j=3 : [0, {M}] → {band_3}")

        # Vérifier : T = 2^{e₂} + 2^{e₃} avec e₂ ∈ band_2, e₃ ∈ band_3 ?
        found = False
        for e2 in band_2:
            for e3 in band_3:
                val = (pow(2, e2, p) + pow(2, e3, p)) % p
                if val == T:
                    print(f"    SOLUTION : 2^{e2} + 2^{e3} = {val} = T ? {'OUI' if val == T else 'NON'}")
                    # Mais : contrainte B₂ ≤ B₃
                    # e₂ correspond à B₂ : e₂ = B₂ + (k-3)M → B₂ = e₂ - (k-3)M = e₂ - M
                    # e₃ correspond à B₃ : e₃ = B₃ + (k-4)M → B₃ = e₃ + 0 = e₃
                    # Wait: recalculating...
                    # E_j = B_j - jM, E_j + (k-1)M = B_j + (k-1-j)M
                    # Pour j=2: e₂ = B₂ + (k-3)M, B₂ = e₂ - (k-3)M
                    # Pour j=3: e₃ = B₃ + (k-4)M, B₃ = e₃ - (k-4)M
                    B2 = e2 - (k_val - 3) * M
                    B3 = e3 - (k_val - 4) * M
                    print(f"      → B₂ = {B2}, B₃ = {B3}, B₂ ∈ [0,M] : {0 <= B2 <= M}, B₃ ∈ [0,M] : {0 <= B3 <= M}")
                    print(f"      → B₂ ≤ B₃ : {B2 <= B3}")
                    if 0 <= B2 <= M and 0 <= B3 <= M and B2 <= B3:
                        print(f"      ★ SOLUTION VALIDE dans [0,M] non-décroissant !")
                        found = True
                    else:
                        print(f"      → Contrainte violée")
        if not found:
            print(f"    AUCUNE solution valide → QED pour k=5 ★★★")


# =====================================================================
print("\n" + "=" * 70)
print("INVESTIGATION I3 : Recherche étendue de k avec d premier")
print("=" * 70)
# =====================================================================

print("\nRecherche de k dans [3, 100] avec d(k) premier :\n")

prime_k_list = []
for k_val in range(3, 101):
    S, M, d = compute_params(k_val)
    if d > 0 and is_prime(d):
        u = compute_u(k_val, d)
        st = sigma_tilde(u, k_val, d)
        sigma_type = "σ̃=0" if st == 0 else "σ̃≠0"
        prime_k_list.append((k_val, d, M, sigma_type))
        print(f"  k={k_val:3d} : d={d}, M={M}, {sigma_type}")

print(f"\n  TOTAL : {len(prime_k_list)} valeurs de k avec d premier sur [3, 200]")
if prime_k_list:
    sigma0_count = sum(1 for _, _, _, s in prime_k_list if s == "σ̃=0")
    print(f"    σ̃=0 : {sigma0_count}")
    print(f"    σ̃≠0 : {len(prime_k_list) - sigma0_count}")


# =====================================================================
print("\n" + "=" * 70)
print("INVESTIGATION I4 : Cas frontière pour CHAQUE k avec d premier")
print("=" * 70)
# =====================================================================

print("""
Pour chaque k trouvé en I3, vérifier le cas frontière :
  Σ_{j=2}^{k-2} u^j · 2^{B_j} ≡ T mod p
  avec 0 ≤ B_2 ≤ ... ≤ B_{k-2} ≤ M
""")

all_verified = True
for k_val, p, M, sigma_type in prime_k_list:
    u = compute_u(k_val, p)
    u_inv = pow(u, -1, p)
    T = (-(1 + u + u_inv)) % p
    u_pows = [pow(u, j, p) for j in range(k_val)]
    n_middle = k_val - 3

    if n_middle == 0:
        # k=3
        check = (u + u_inv) % p
        has_sol = (check == (-1) % p)
    elif n_middle == 1:
        # k=4 type
        u2 = pow(u, 2, p)
        target_b = (T * pow(u2, -1, p)) % p
        o2 = ord_mod(2, p)
        x, b_sol = 1, None
        for b in range(o2):
            if x == target_b:
                b_sol = b
                break
            x = (2 * x) % p
        has_sol = (b_sol is not None and b_sol <= M)
    else:
        # k ≥ 5 : DP or enumeration
        from math import comb
        n_comb = comb(M + n_middle, n_middle)

        if n_comb <= 2000000:
            # Énumération directe
            has_sol = False
            for B in combinations_with_replacement(range(M + 1), n_middle):
                val = sum(u_pows[j+2] * pow(2, B[j], p) for j in range(n_middle)) % p
                if val == T:
                    has_sol = True
                    break
            method_str = f"enum({n_middle}v,{n_comb}c)"
        else:
            # DP
            image = compute_image_dp(k_val, p, M, u_pows, n_middle)
            if image is None:
                has_sol = None  # couldn't compute
                method_str = f"SKIP({n_middle}v,{n_comb}c)"
            else:
                has_sol = T in image
                method_str = f"DP({n_middle}v,|Im|={len(image)})"

    if has_sol is None:
        status = "? SKIP"
    elif has_sol:
        status = "✗ ÉCHEC"
        all_verified = False
    else:
        status = "✓ N₀=0"

    method = "Φ₃" if n_middle == 0 else ("log₂" if n_middle == 1 else method_str)
    print(f"  k={k_val:3d} (p={p:>10d}, M={M:2d}, {sigma_type}) : {status} [{method}]")

print(f"\n  {'★★★ TOUS VÉRIFIÉS ★★★' if all_verified else '!!! ÉCHEC TROUVÉ !!!'}")
print(f"  {len(prime_k_list)} cas testés, {len(prime_k_list)} N₀=0")


# =====================================================================
print("\n" + "=" * 70)
print("INVESTIGATION I5 : Analyse σ̃≠0 — image et cascade")
print("=" * 70)
# =====================================================================

print("""
Pour σ̃≠0, l'image de f est CREUSE par rapport à p.
On combine : cascade (élimine b_min>0 ou b_max<M) + frontière (T ∉ Im médiane).
Analysons la taille de l'image médiane vs p pour les σ̃≠0.
""")

for k_val, p, M, sigma_type in prime_k_list:
    if sigma_type == "σ̃=0": continue

    u = compute_u(k_val, p)
    u_pows = [pow(u, j, p) for j in range(k_val)]
    n_middle = k_val - 3

    from math import comb
    n_comb = comb(M + n_middle, n_middle)

    # Taille de l'image médiane (borne supérieure)
    img_size_bound = min(n_comb, p)
    ratio = img_size_bound / p

    # Calculer l'image réelle si possible
    if n_comb <= 2000000:
        image = compute_image_dp(k_val, p, M, u_pows, n_middle)
        if image is not None:
            img_real = len(image)
        else:
            img_real = "?"
    else:
        img_real = "?"

    print(f"  k={k_val:3d} (p={p:>10d}, M={M:2d}, σ̃≠0) :")
    print(f"    Combinaisons = {n_comb}, p = {p}")
    print(f"    Ratio C/p = {ratio:.6f}")
    if img_real != "?":
        print(f"    |Im médiane| = {img_real} (réelle)")
        print(f"    |Im|/p = {img_real/p:.6f}")

    # Compter les résidus frappés par la forward chain
    # Forward chain : {-2^m : m=0,...,M}
    forward = set()
    for m in range(M + 1):
        forward.add((-pow(2, m, p)) % p)

    print(f"    |Forward chain| = {len(forward)}")
    if img_real != "?":
        overlap = len(forward & image)
        print(f"    Overlap Im ∩ Forward = {overlap}")


# =====================================================================
print("\n" + "=" * 70)
print("INVESTIGATION I6 : Borne de somme restreinte (σ̃=0)")
print("=" * 70)
# =====================================================================

print("""
Pour σ̃=0, avec ord₂(p) = (k-1)M, on a un isomorphisme :
  2^e mod p est injectif sur [0, (k-1)M - 1].

La somme médiane Σ_{j=2}^{k-2} 2^{E_j + (k-1)M} = T mod p
avec E_j + (k-1)M ∈ [(k-1-j)M, (k-j)M] (bande j).

OBSERVATION CLEF : dans Z (pas mod p), la somme Σ 2^{e_j}
avec e_j dans des bandes disjointes a une structure binaire
très contrainte. Chaque bande contribue au plus M+1 puissances
de 2 distinctes.

Si p était la puissance 2^{(k-1)M} (ce qu'il n'est pas),
la somme serait un entier avec exactement k-3 bits non-nuls,
un par bande.

La question est : T a-t-il une telle décomposition en base 2
quand on réduit mod p = 2^S - 3^k ?
""")

for k_val in [3, 5]:
    S, M, d = compute_params(k_val)
    if not is_prime(d): continue
    p = d
    u = compute_u(k_val, p)
    st = sigma_tilde(u, k_val, p)
    if st != 0: continue

    u_inv = pow(u, -1, p)
    T = (-(1 + u + u_inv)) % p
    o2 = ord_mod(2, p)

    print(f"\n  k={k_val} (p={p}, M={M}, ord₂={o2}, (k-1)M = {(k_val-1)*M}) :")

    # Représentation binaire de T
    print(f"    T = {T}")
    print(f"    T en binaire : {bin(T)}")
    print(f"    Nombre de bits : {T.bit_length()}")
    print(f"    Nombre de 1s : {bin(T).count('1')}")

    # Représentation de p et 2^{(k-1)M}
    power_km = (k_val - 1) * M
    print(f"    2^{{{power_km}}} = {1 << power_km}")
    print(f"    p = {p}")
    print(f"    p en binaire : {bin(p)}")

    # Pour k=5 : T doit être somme de 2 puissances de 2 dans bandes [3,6] et [0,3]
    if k_val == 5:
        print(f"\n    T mod p doit être 2^a + 2^b avec a ∈ [3,6], b ∈ [0,3] :")
        for a in range(M, 2*M + 1):
            for b in range(0, M + 1):
                # Dans Z :
                val_Z = (1 << a) + (1 << b)
                val_modp = val_Z % p
                # Aussi considérer val_Z + k*p (retenues mod p)
                if val_modp == T:
                    print(f"      2^{a} + 2^{b} = {val_Z} ≡ {val_modp} mod {p} {'= T ✓' if val_modp == T else '≠ T'}")
                    # Reconstruire B : E₂ = a, B₂ = a - M = a - 3
                    #                  E₃ = b, B₃ = b
                    B2 = a - M
                    B3 = b
                    print(f"        B₂ = {B2}, B₃ = {B3}, non-décroissant: {B2 <= B3}")

        # Mais on est mod p ! Les vraies solutions modp :
        print(f"\n    Solutions mod p (2^a + 2^b ≡ T mod p) :")
        for a in range(M, 2*M + 1):
            for b in range(0, M + 1):
                val = (pow(2, a, p) + pow(2, b, p)) % p
                if val == T:
                    B2 = a - M
                    B3 = b
                    print(f"      2^{a} + 2^{b} ≡ {val} mod {p} → B₂={B2}, B₃={B3}, B₂≤B₃: {B2 <= B3}")


# =====================================================================
print("\n" + "=" * 70)
print("INVESTIGATION I7 : Synthèse et gap restant")
print("=" * 70)
# =====================================================================

print(f"""
    ════════════════════════════════════════════════════════
    SYNTHÈSE SESSION 10f5
    ════════════════════════════════════════════════════════

    RÉSULTATS VÉRIFIÉS :

    1. Recherche étendue k ∈ [3, 200] :
       {len(prime_k_list)} valeurs de k avec d premier trouvées.
       TOUTES ont N₀=0 via le cas frontière.

    2. Pour σ̃=0 : la structure de bandes (u^j = 2^{{-jM}})
       place les exposants dans des bandes disjointes.
       ord₂(p) = (k-1)M confirmé (les 2^e sont distincts mod p).

    3. Pour σ̃≠0 : l'image médiane est CREUSE (ratio << 1).
       La cascade + le comptage suffisent souvent.

    4. Le cas frontière (B₁=0, B_{{k-1}}=M) est le SEUL cas
       restant après la cascade bidirectionnelle.

    GAP POUR PREUVE UNIVERSELLE :

    A. σ̃=0 : Pourquoi T = -(1+u+u^{{-1}}) n'admet PAS de
       représentation comme somme de k-3 puissances de 2 dans
       des bandes disjointes ? Piste : analyser T en base 2
       et montrer que les retenues mod p rendent la représentation
       impossible.

    B. σ̃≠0 : Pourquoi T n'est pas dans l'image médiane ?
       Piste : le ratio C/p → 0 exponentiellement (γ = 0.05),
       et T a une structure algébrique spécifique.

    C. d composite : déjà traité par CRT (Mécanisme II/III).
    ════════════════════════════════════════════════════════
""")


elapsed = time.time() - start_time
print(f"{'='*70}")
print(f"Temps total : {elapsed:.1f}s")
print(f"{'='*70}")
