#!/usr/bin/env python3
"""
R177 — PREUVE POUR x = 2 : LA CONDITION 2^Δ ≡ -1 mod p

Pour x = 2 et p = 2^S - 9 premier (d = 2^S - 3^2 = 2^S - 9) :

g(v) = 3·2^{e_0} + 2^{e_1} = 2^{e_0}(3 + 2^{e_1-e_0})

Puisque p est impair : p | g ⟺ p | (3 + 2^Δ) où Δ = e_1 - e_0 ∈ {1,...,S-2}
(On peut prendre e_0 = 0 wlog car gcd(2^{e_0}, p) = 1.)

Condition : 2^Δ ≡ -3 mod p.

Puisque 3 ≡ 2^t mod p (quand 3 ∈ ⟨2⟩) : 2^Δ ≡ -2^t mod p, i.e., 2^{Δ-t} ≡ -1 mod p.

-1 ≡ 2^{o₂/2} mod p (quand o₂ = ord_p(2) est pair).

Donc : Δ - t ≡ o₂/2 mod o₂, i.e., Δ ≡ t + o₂/2 mod o₂.

Puisque Δ ∈ {1,...,S-2} et o₂ >> S (typiquement), il faut que
t + o₂/2 mod o₂ ∈ {1,...,S-2}.

C'EST CETTE CONDITION QUI ÉCHOUE TOUJOURS. PROUVONS-LE.
"""

from sympy import isprime


def multiplicative_order(a, n):
    if n <= 1:
        return None
    order = 1
    current = a % n
    if current == 0:
        return None
    while current != 1:
        current = (current * a) % n
        order += 1
        if order > n:
            return None
    return order


def main():
    print("=" * 72)
    print("R177 — PREUVE DU CAS x = 2 PAR LA MÉTHODE CYCLIQUE")
    print("=" * 72)

    print("""
THÉORÈME (x=2) : Pour tout S ≥ 4, si p = 2^S - 9 est premier,
alors g(v) ≢ 0 mod p pour tout vecteur de parité v avec x=2.

PREUVE : g(v) = 3·2^{e_0} + 2^{e_1} = 2^{e_0}(3 + 2^Δ) avec Δ = e_1 - e_0 ∈ {1,...,S-2}.
p | g ⟺ 2^Δ ≡ -3 mod p (car p est impair, p ∤ 2^{e_0}).

CAS 1 : 3 ∈ ⟨2⟩ mod p. Alors 3 = 2^t pour un t, et la condition est
2^{Δ-t} ≡ -1 mod p, i.e., Δ ≡ t + o₂/2 mod o₂.

La clé : Δ ∈ {1,...,S-2} mais t + o₂/2 mod o₂ ≥ ??? Vérifions :
""")

    # TEST pour tous les p = 2^S - 9 premiers
    print("S | p=2^S-9 | prime? | o₂ | t | target=t+o₂/2 mod o₂ | in {1,...,S-2}? | -3 is power of 2?")
    print("-" * 100)

    for S in range(4, 50):
        p = 2**S - 9
        if p <= 1:
            continue
        if not isprime(p):
            continue

        o2 = multiplicative_order(2, p)
        if o2 is None:
            continue

        # Find t with 2^t ≡ 3 mod p
        t = None
        power = 1
        for k in range(1, o2 + 1):
            power = power * 2 % p
            if power == 3 % p:
                t = k
                break

        three_in_gen2 = t is not None

        # Check if -3 is a power of 2 mod p
        minus3 = (-3) % p
        is_power_of_2 = False
        power = 1
        for k in range(o2):
            if power == minus3:
                is_power_of_2 = True
                break
            power = power * 2 % p

        if three_in_gen2:
            # Target exponent for Δ
            if o2 % 2 == 0:
                target = (t + o2 // 2) % o2
                in_range = 1 <= target <= S - 2
            else:
                # -1 is NOT a power of 2 when o2 is odd
                target = "N/A (o₂ odd → -1 ∉ ⟨2⟩)"
                in_range = False

            print(f"  S={S:2d} | p={p:>14d} | ✅ | o₂={o2:>8d} | t={t:>6d} | "
                  f"target={target!s:>12s} | in_range={in_range!s:>5s} | "
                  f"-3∈⟨2⟩={is_power_of_2}")
        else:
            # 3 not in ⟨2⟩ — need different analysis
            print(f"  S={S:2d} | p={p:>14d} | ✅ | o₂={o2:>8d} | 3∉⟨2⟩ | "
                  f"{'':>12s} | {'':>5s} | -3∈⟨2⟩={is_power_of_2}")

    # Now the GENERAL case for x=2 (not just d = 2^S - 9)
    print("\n\n" + "=" * 72)
    print("CAS GÉNÉRAL x = 2 : d = 2^S - 9 (pas nécessairement premier)")
    print("=" * 72)

    print("""
Pour x=2 et d quelconque :
g(v) = 3 + 2^Δ pour Δ = 1,...,S-2 (avec e₀=0).
On veut : d ∤ (3 + 2^Δ) pour tout Δ ∈ {1,...,S-2}.

Preuve directe : g = 3 + 2^Δ.
- g ≥ 3 + 2 = 5 (pour Δ ≥ 1)
- g ≤ 3 + 2^{S-2} = 3 + 2^{S-2}
- d = 2^S - 9

Pour d | g : d ≤ g, donc 2^S - 9 ≤ 3 + 2^{S-2}, i.e., 2^S - 2^{S-2} ≤ 12,
i.e., 3·2^{S-2} ≤ 12, i.e., 2^{S-2} ≤ 4, i.e., S ≤ 4.

Pour S = 4 : d = 7, g ∈ {5, 7, 11}. 7 | 7 = oui ! Δ = 2 donne g = 7.
MAIS le vecteur est (0, 2) i.e., v = 1010.
Vérifions : c'est le vecteur de parité du cycle 1 → 4 → 2 → 1 ?
Non, pour le cycle trivial x=1. Pour x=2 : n₁ = g/d = 7/7 = 1.
Mais 3·1 + 1 = 4 = 2^2 · 1 → n₂ = 1. MAIS n₁ = n₂ = 1 → non distinct !
C'est le cycle trivial {1} déguisé.

MAIS ATTENTION : le vecteur v = 1010 est PÉRIODIQUE (période 2) !
Donc il est exclu des vecteurs APÉRIODIQUES.

Pour S = 4, vecteurs apériodiques avec x=2 :
v = 1100 (positions 0,1) : g = 3 + 2 = 5. 5 mod 7 ≠ 0. ✓
v = 1010 (positions 0,2) : PÉRIODIQUE → exclu
v = 1001 (positions 0,3) : g = 3 + 8 = 11. 11 mod 7 ≠ 0. ✓
v = 0110 (positions 1,2) : g = 6 + 4 = 10. 10 mod 7 ≠ 0. ✓
v = 0101 (positions 1,3) : PÉRIODIQUE → exclu (si k pair)
Wait, v=0101 has period 2 only if k=4 and period divides k...
v = 0101 is periodic (10)² written as (01)². Yes, period 2.
v = 0011 (positions 2,3) : g = 12 + 8 = 20. Wait no.

Let me recalculate properly.
""")

    # Explicit verification for small S
    print("VÉRIFICATION EXHAUSTIVE POUR x=2, S PETIT :\n")
    from itertools import combinations

    for S in range(4, 20):
        d = 2**S - 9
        if d <= 0:
            continue

        found = False
        for positions in combinations(range(S), 2):
            e0, e1 = positions
            # Check aperiodicity
            v = tuple(1 if i in positions else 0 for i in range(S))
            is_periodic = False
            for period in range(1, S):
                if S % period == 0 and period < S:
                    if v == v[:period] * (S // period):
                        is_periodic = True
                        break
            if is_periodic:
                continue

            g = 3**(1) * 2**e0 + 2**e1  # x=2, so 3^{x-1-0}=3, 3^{x-1-1}=1
            if g % d == 0:
                found = True
                print(f"  S={S}, d={d}: FOUND g=0 ! v={v}, g={g}, g/d={g//d}")
                break

        if not found and S <= 15:
            # Count max g / d
            max_g = 3 * 2**(S-2) + 2**(S-1)  # rough upper bound
            print(f"  S={S:2d}, d={d:>8d}: ✅ NO solution. max_g ≈ {3 + 2**(S-2)}, "
                  f"{'d > max_g → TRIVIALLY IMPOSSIBLE' if d > 3 + 2**(S-2) else 'd ≤ max_g but still no solution'}")

    print("""
PREUVE COMPLÈTE POUR x = 2 :

Pour x = 2, S ≥ 5 : d = 2^S - 9 et g(v) = 3·2^{e₀} + 2^{e₁}.

Avec e₀ = 0 (wlog car gcd(2^{e₀}, d) = 1 puisque d est impair) :
g = 3 + 2^Δ, Δ ∈ {1, ..., S-2}.

g_max = 3 + 2^{S-2}.
d = 2^S - 9 = 4·2^{S-2} - 9.

Pour S ≥ 5 : d = 4·2^{S-2} - 9 > 3 + 2^{S-2} = g_max
⟺ 3·2^{S-2} > 12 ⟺ 2^{S-2} > 4 ⟺ S > 4. ✓

Donc pour S ≥ 5 : g < d, donc d ∤ g (car g > 0). ∎

Pour S = 4 : d = 7, g ∈ {5, 11} (vecteurs apériodiques). 7 ∤ 5 et 7 ∤ 11. ✓

Pour S = 3 : impossible car 2^3 = 8 < 9 = 3^2 → d < 0.

DONC : Pour x = 2, N₀(d) = 0 pour tout S ≥ 3. ∎
(Ceci est bien connu — Steiner 1977 — mais notre preuve est élémentaire.)
""")

    # ═══════════════════════════════════════════════════════════════
    # Extension : pourquoi g < d pour x petit par rapport à S ?
    # ═══════════════════════════════════════════════════════════════
    print("=" * 72)
    print("EXTENSION : BORNE g < d POUR x PETIT ?")
    print("=" * 72)

    print("""
Pour x quelconque :
g_max = max g(v) = Σ_{j=0}^{x-1} 3^{x-1-j} · 2^{S-x+j}  (positions S-x,...,S-1)
     = 2^{S-x} · Σ_{j=0}^{x-1} 3^{x-1-j} · 2^j
     = 2^{S-x} · (3^x - 2^x)/(3-2) = 2^{S-x} · (3^x - 2^x)

d = 2^S - 3^x.

g_max < d ⟺ 2^{S-x} · (3^x - 2^x) < 2^S - 3^x
           ⟺ (3^x - 2^x) / 2^x < 1 - 3^x/2^S
           ⟺ (3/2)^x - 1 < 1 - (3/2)^x · (2^x/2^S)    ... (complex)

Pour S = 2x (borne supérieure) : d = 4^x - 3^x, g_max = (3^x - 2^x).
g_max < d ⟺ 3^x - 2^x < 4^x - 3^x ⟺ 2·3^x < 4^x + 2^x
⟺ 2 < (4/3)^x + (2/3)^x.
Pour x = 1 : 2 < 4/3 + 2/3 = 2. FAUX (égalité).
Pour x = 2 : 2 < 16/9 + 4/9 = 20/9 ≈ 2.22. VRAI.
Pour x ≥ 2 : (4/3)^x → ∞, donc toujours vrai.

Donc pour S = 2x et x ≥ 2 : g_max < d. ✓ (Pas de cycle pour S = 2x.)
""")

    # Compute the "crossover S" where g_max = d for each x
    print("Pour chaque x, trouver le S_cross tel que g_max(S) = d(S) :")
    for x in range(2, 20):
        S_min = int(x * 1.585) + 1
        while 2**S_min <= 3**x:
            S_min += 1

        found_cross = None
        for S in range(S_min, 2*x + 1):
            d = 2**S - 3**x
            # g_max = 2^{S-x} * (3^x - 2^x)
            g_max = (2**(S-x)) * (3**x - 2**x)
            if g_max >= d:
                found_cross = S
                g_over_d = g_max / d
                break

        if found_cross is None:
            print(f"  x={x:2d}: g_max < d for ALL valid S → NO CYCLE (pure size argument!)")
        else:
            print(f"  x={x:2d}: g_max ≥ d first at S={found_cross} "
                  f"(g_max/d = {g_over_d:.2f}). "
                  f"Size argument fails for S ∈ [{found_cross}, ...]. "
                  f"Range: S ∈ [{S_min}, {2*x}]")


if __name__ == '__main__':
    main()
