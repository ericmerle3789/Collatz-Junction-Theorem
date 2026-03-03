#!/usr/bin/env python3
"""
VÉRIFICATION CRITIQUE : M₁₇ | d(7710) ?
=========================================
L'analyse montre que pour M₁₇ = 131071 (q=17), n₃ = 7710 et β₀ = 15.
La condition de congruence ⌈n₃·θ⌉ mod q = β₀ mod q est SATISFAITE.
Cela impliquerait M₁₇ | d(7710).

Mais L12 rapporte "0 cas" de divisibilité pour k ≤ 50000.
Il y a une contradiction. Ce script tranche.
"""

import math

theta = math.log2(3)  # 1.5849625007211562

# ─── Vérification 1 : n₃ pour M₁₇ ───

p17 = 131071
q17 = 17

# Build ⟨2⟩ mod p17
gen2 = {}
x = 1
for j in range(q17):
    gen2[x] = j  # 2^j → discrete log j
    x = (x * 2) % p17

print(f"⟨2⟩ mod {p17} = {sorted(gen2.keys())}")
print(f"|⟨2⟩| = {len(gen2)}")

# Find n₃ = min j ≥ 1 : 3^j ∈ ⟨2⟩
y = 1
n3 = None
beta0 = None
for j in range(1, p17):
    y = (y * 3) % p17
    if y in gen2:
        n3 = j
        beta0 = gen2[y]
        print(f"\nn₃ = {j}")
        print(f"3^{j} mod {p17} = {y}")
        print(f"dlog₂(3^{j}) = {gen2[y]}")
        print(f"Vérification : 2^{gen2[y]} mod {p17} = {pow(2, gen2[y], p17)}")
        print(f"3^{j} mod {p17} = {y}")
        print(f"Match : {pow(2, gen2[y], p17) == y}")
        break

# ─── Vérification 2 : ⌈n₃·θ⌉ et congruence ───

print(f"\n{'='*60}")
print(f"VÉRIFICATION CONGRUENCE")
print(f"{'='*60}")

k = n3
k_theta = k * theta
ceil_k_theta = math.ceil(k_theta)
ceil_mod_q = ceil_k_theta % q17
j_beta_mod_q = beta0 % q17

print(f"\nk = n₃ = {k}")
print(f"k·θ = {k_theta:.15f}")
print(f"{{k·θ}} = {k_theta - math.floor(k_theta):.15f}")
print(f"⌈k·θ⌉ = {ceil_k_theta}")
print(f"⌈k·θ⌉ mod q = {ceil_mod_q}")
print(f"β₀ mod q = {j_beta_mod_q}")
print(f"Condition de congruence satisfaite : {ceil_mod_q == j_beta_mod_q}")

# ─── Vérification 3 : d(k) mod M₁₇ DIRECTE ───

print(f"\n{'='*60}")
print(f"VÉRIFICATION d(k) mod M_q DIRECTE")
print(f"{'='*60}")

d_k_mod_p = (pow(2, ceil_k_theta, p17) - pow(3, k, p17)) % p17

print(f"\n2^{{⌈kθ⌉}} mod p = pow(2, {ceil_k_theta}, {p17}) = {pow(2, ceil_k_theta, p17)}")
print(f"3^k mod p = pow(3, {k}, {p17}) = {pow(3, k, p17)}")
print(f"d({k}) mod {p17} = {d_k_mod_p}")
print(f"M₁₇ | d({k}) : {'OUI ⚠️' if d_k_mod_p == 0 else 'NON ✓'}")

# ─── Vérification 4 : Impact sur (Q) ───

if d_k_mod_p == 0:
    print(f"\n{'='*60}")
    print(f"IMPACT SUR CONDITION (Q)")
    print(f"{'='*60}")

    rho = 0.8135
    val = (p17 - 1) * rho**(k - 17)
    log_val = math.log(p17 - 1) + (k - 17) * math.log(rho)

    print(f"\n(p-1)·ρ^(k-17) = {p17-1} × {rho}^{k-17}")
    print(f"log₁₀ de cette valeur = {log_val / math.log(10):.1f}")
    print(f"Seuil = 0.041")
    print(f"(Q) satisfaite : {'OUI' if log_val < math.log(0.041) else 'NON'}")
    print(f"Marge : facteur 10^{(math.log(0.041) - log_val)/math.log(10):.0f}")

# ─── Vérification 5 : Contrôle pour d'autres Mersenne ───

print(f"\n{'='*60}")
print(f"VÉRIFICATION SYSTÉMATIQUE pour chaque Mersenne")
print(f"{'='*60}")

for q in [5, 7, 13, 17, 19]:
    p = (1 << q) - 1
    # Vérifier primalité
    is_pr = True
    for i in range(2, int(p**0.5) + 1):
        if p % i == 0:
            is_pr = False
            break
    if not is_pr:
        continue

    # Find n₃
    gen2_set = set()
    gen2_map = {}
    x = 1
    for j in range(q):
        gen2_set.add(x)
        gen2_map[x] = j
        x = (x * 2) % p

    y = 1
    for j in range(1, p):
        y = (y * 3) % p
        if y in gen2_set:
            n3_val = j
            b0 = gen2_map[y]
            break

    # Check d(n₃) mod p
    k_val = n3_val
    ceil_kt = math.ceil(k_val * theta)
    d_mod = (pow(2, ceil_kt, p) - pow(3, k_val, p)) % p

    # Check d(j·n₃) for j = 1, ..., 10
    divides_list = []
    for jj in range(1, 11):
        kk = jj * n3_val
        if kk > 200000:
            break
        ck = math.ceil(kk * theta)
        dd = (pow(2, ck, p) - pow(3, kk, p)) % p
        if dd == 0:
            divides_list.append(jj)

    k_crit = 17 + (q * math.log(2) + 3.19) / abs(math.log(0.83))
    danger_divs = [jj for jj in divides_list if jj * n3_val <= k_crit]

    print(f"\nq={q}, p=M_{q}={p}, n₃={n3_val}, β₀={b0}")
    print(f"  d(n₃) mod p = {d_mod} → {'DIVISE' if d_mod == 0 else 'ne divise pas'}")
    print(f"  k_crit ≈ {k_crit:.1f}")
    print(f"  j où M_q | d(j·n₃) (j≤10) : {divides_list if divides_list else 'aucun'}")
    print(f"  j dans fenêtre de danger : {danger_divs if danger_divs else 'aucun'}")
    if divides_list:
        for jj in divides_list:
            kk = jj * n3_val
            log_val = math.log(p - 1) + (kk - 17) * math.log(0.83)
            qsat = log_val < math.log(0.041)
            print(f"    k={kk}: log₁₀((p-1)ρ^(k-17)) = {log_val/math.log(10):.1f}, (Q) satisfaite: {'OUI' if qsat else 'NON'}")

# ─── Vérification 6 : Le check L12 original ───

print(f"\n{'='*60}")
print(f"VÉRIFICATION L12 : M₁₇ | d(k) pour k = 18..100")
print(f"{'='*60}")

p17 = 131071
count = 0
for k in range(18, 101):
    ck = math.ceil(k * theta)
    d = (pow(2, ck, p17) - pow(3, k, p17)) % p17
    if d == 0:
        print(f"  k={k}: d(k) ≡ 0 (mod {p17}) ⚠️")
        count += 1

if count == 0:
    print(f"  Aucun k dans [18, 100] avec M₁₇ | d(k) ✓")
    print(f"  (Normal car n₃ = {n3} >> 100)")

print(f"\n{'='*60}")
print(f"CONCLUSION")
print(f"{'='*60}")
