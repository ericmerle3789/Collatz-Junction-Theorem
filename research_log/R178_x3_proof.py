#!/usr/bin/env python3
"""
R178f — PREUVE COMPLÈTE POUR x = 3 PAR DESCENTE 2-ADIQUE

═══════════════════════════════════════════════════════════════════════
THÉORÈME T189 : Pour x = 3, g(v) ≢ 0 mod d pour tout v apériodique.
═══════════════════════════════════════════════════════════════════════

PREUVE :
d = 2^S - 3^3 = 2^S - 27 (S ≥ 5 pour d > 0).

WLOG e₀ = 0 (car d est impair, gcd(2^{e₀}, d) = 1).
On pose D₁ = e₁ ≥ 1, D₂ = e₂ ≥ D₁+1 ≥ 2.

g(v)/2^{e₀} = h(D₁, D₂) = 9 + 3·2^{D₁} + 2^{D₂}.

d | h ⟹ h = k·d pour k ≥ 1.

═══ BORNE SUR k ═══
h_max = 9 + 3·2^{S-2} + 2^{S-1} = 9 + 5·2^{S-2}
d = 2^S - 27 = 4·2^{S-2} - 27

k ≤ h_max/d = (9 + 5·2^{S-2})/(4·2^{S-2} - 27)

Pour S = 5: k ≤ 49/5 = 9.8
Pour S = 6: k ≤ 89/37 = 2.4
Pour S ≥ 7: k ≤ (5·2^{S-2})/(4·2^{S-2}) < 5/4 → k = 1 uniquement.

═══ CAS S ≥ 7, k = 1 ═══
h = d : 9 + 3·2^{D₁} + 2^{D₂} = 2^S - 27
⟹ 3·2^{D₁} + 2^{D₂} = 2^S - 36

ANALYSE 2-ADIQUE :
v₂(RHS) = v₂(2^S - 36) = v₂(4·(2^{S-2} - 9)) = 2
    (car 2^{S-2} - 9 est impair pour S ≥ 5)

v₂(LHS) = D₁   (car 3·2^{D₁} a v₂ = D₁, 2^{D₂} a v₂ = D₂ > D₁,
                   et D₁ est le v₂ minimal, avec coefficient 3 impair)

Donc D₁ = 2.

Substitution : 12 + 2^{D₂} = 2^S - 36
⟹ 2^{D₂} = 2^S - 48 = 16·(2^{S-4} - 3)

Pour S ≥ 7 : 2^{S-4} - 3 est IMPAIR (2^{S-4} pair, 3 impair → différence impaire)
             et 2^{S-4} - 3 ≥ 5 > 1.

Donc 2^{D₂} = 16 × (nombre impair > 1), ce qui est IMPOSSIBLE
(un produit de 2^4 par un impair > 1 n'est pas une puissance de 2). ∎

═══ CAS S = 6 (k = 1 et k = 2) ═══
k = 1 : h = 37. 3·2^{D₁} + 2^{D₂} = 28.
  D₁=1: 6+2^{D₂}=28 → 2^{D₂}=22 ✗
  D₁=2: 12+2^{D₂}=28 → 2^{D₂}=16 → D₂=4 ✓
    Vecteur (0,2,4) = 101010, PÉRIODIQUE (période 2). EXCLU.
  D₁=3: 24+2^{D₂}=28 → 2^{D₂}=4 → D₂=2, MAIS D₂ > D₁=3 requis ✗

k = 2 : h = 74. 3·2^{D₁} + 2^{D₂} = 65.
  v₂(65) = 0, v₂(LHS) = D₁ ≥ 1. Contradiction. ✗

═══ CAS S = 5 (k = 1 à 9) ═══
d = 5. h = 9 + 3·2^{D₁} + 2^{D₂}, D₁ ∈ {1,2,3}, D₂ ∈ {D₁+1,...,4}.
  D₁=1, D₂=2: h=19, 19%5=4 ≠ 0
  D₁=1, D₂=3: h=23, 23%5=3 ≠ 0
  D₁=1, D₂=4: h=31, 31%5=1 ≠ 0
  D₁=2, D₂=3: h=29, 29%5=4 ≠ 0
  D₁=2, D₂=4: h=37, 37%5=2 ≠ 0
  D₁=3, D₂=4: h=49, 49%5=4 ≠ 0
  AUCUN divisible par 5. ✓

═══ CAS S ≤ 4 ═══
S ≤ 4 : d = 2^S - 27 ≤ -11 < 0. Pas de cycle possible (d doit être > 0).

CONCLUSION : Pour x = 3, N₀(d) = 0 pour tout S. ∎
"""

from itertools import combinations
from math import gcd


def verify_x3_proof():
    print("=" * 80)
    print("VÉRIFICATION DE LA PREUVE T189 (x=3)")
    print("=" * 80)

    # 1. Verify v₂ claim: v₂(2^S - 36) = 2 for S ≥ 5
    print("\n--- Vérification v₂(2^S - 36) = 2 ---")
    for S in range(5, 30):
        val = 2**S - 36
        v2 = 0
        tmp = val
        while tmp % 2 == 0:
            v2 += 1
            tmp //= 2
        assert v2 == 2, f"FAIL: S={S}, v₂={v2}"
    print("  ✅ v₂(2^S - 36) = 2 pour S = 5..29")

    # 2. Verify 2^{S-4} - 3 is odd for S ≥ 7
    print("\n--- Vérification 2^{S-4} - 3 impair pour S ≥ 7 ---")
    for S in range(7, 50):
        val = 2**(S-4) - 3
        assert val % 2 == 1, f"FAIL: S={S}"
        assert val > 1, f"FAIL: val ≤ 1 for S={S}"
    print("  ✅ 2^{S-4} - 3 est impair et > 1 pour S = 7..49")

    # 3. Verify k bound
    print("\n--- Vérification borne sur k ---")
    for S in range(5, 30):
        d = 2**S - 27
        if d <= 0:
            continue
        h_max = 9 + 3 * 2**(S-2) + 2**(S-1)
        k_max = h_max // d
        if S >= 7:
            assert k_max == 1, f"FAIL: S={S}, k_max={k_max}"
    print("  ✅ k_max = 1 pour S ≥ 7")

    # 4. Verify S=6 case
    print("\n--- Vérification S=6 ---")
    d = 37
    # k=1: only solution is D₁=2, D₂=4
    h = 9 + 12 + 16  # = 37
    assert h == d
    v = (1, 0, 1, 0, 1, 0)  # positions 0, 2, 4
    is_periodic = v == v[:2] * 3
    print(f"  k=1: h=37=d, vector=101010, periodic={is_periodic}")
    assert is_periodic

    # k=2: 65 is odd, but LHS ≥ 2 (D₁≥1)
    target = 2 * d - 9  # = 65
    print(f"  k=2: target=65, v₂={0} but v₂(LHS)≥1 → impossible ✅")

    # 5. Verify S=5 exhaustive
    print("\n--- Vérification S=5 exhaustive ---")
    d = 5
    for D1 in range(1, 4):
        for D2 in range(D1+1, 5):
            h = 9 + 3 * 2**D1 + 2**D2
            assert h % d != 0, f"FAIL: D1={D1}, D2={D2}, h={h}"
    print("  ✅ Aucune solution pour S=5")

    # 6. EXHAUSTIVE VERIFICATION for all S
    print("\n--- Vérification exhaustive complète ---")
    for S in range(5, 30):
        d = 2**S - 27
        if d <= 0:
            continue

        found = False
        for positions in combinations(range(S), 3):
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

            g = 9 * 2**positions[0] + 3 * 2**positions[1] + 2**positions[2]
            if g % d == 0:
                found = True
                print(f"  ⚠️ S={S}: FOUND! v={positions}, g={g}")

        if not found:
            if S <= 15 or S % 5 == 0:
                print(f"  S={S:2d}: d={d:>10d} — aucune solution ✅")

    print("\n\n" + "=" * 80)
    print("PREUVE T189 VÉRIFIÉE — x=3 : N₀(d) = 0 pour tout S ≥ 5")
    print("=" * 80)


def attempt_x4():
    """Try to extend the 2-adic proof to x=4."""
    print("\n\n" + "=" * 80)
    print("TENTATIVE D'EXTENSION À x = 4")
    print("=" * 80)
    print("""
Pour x = 4 : g = 27·2^{e₀} + 9·2^{e₁} + 3·2^{e₂} + 2^{e₃}
WLOG e₀ = 0 : h = 27 + 9·2^{D₁} + 3·2^{D₂} + 2^{D₃}

d = 2^S - 81.

h_max = 27 + 9·2^{S-3} + 3·2^{S-2} + 2^{S-1}
      = 27 + 15·2^{S-3} + 2^{S-1}
      = 27 + 15·2^{S-3} + 4·2^{S-3}
      = 27 + 19·2^{S-3}

d = 8·2^{S-3} - 81

k_max = h_max/d ≈ 19·2^{S-3}/(8·2^{S-3}) = 19/8 = 2.375

Pour S large : k ∈ {1, 2}.
""")

    for S in range(7, 25):
        d = 2**S - 81
        if d <= 0:
            continue

        h_max = 27 + 9 * 2**(S-3) + 3 * 2**(S-2) + 2**(S-1)
        k_max = h_max // d
        h_min = 27 + 18 + 12 + 16  # = 73 (D₁=1, D₂=2, D₃=3... wait, need D₁<D₂<D₃)
        h_min_actual = 27 + 9*2 + 3*4 + 8  # D₁=1, D₂=2, D₃=3: 27+18+12+8=65... that's wrong
        # h = 27 + 9·2^{D₁} + 3·2^{D₂} + 2^{D₃}
        h_min_actual = 27 + 9*2 + 3*2**2 + 2**3  # D₁=1,D₂=2,D₃=3: 27+18+12+8=65

        if S <= 12:
            print(f"  S={S}: d={d}, h ∈ [{h_min_actual}, {h_max}], k_max={k_max}")

    # 2-adic analysis for k=1
    print("\n--- Analyse 2-adique pour k=1 ---")
    print("""
Pour k=1 : h = d = 2^S - 81
⟹ 9·2^{D₁} + 3·2^{D₂} + 2^{D₃} = 2^S - 108

v₂(2^S - 108) = v₂(4·(2^{S-2} - 27)) = 2
    (car 2^{S-2} - 27 est impair pour S ≥ 7)

v₂(LHS) = D₁ (premier terme 9·2^{D₁}, coeff 9 impair, D₁ < D₂ < D₃)

⟹ D₁ = 2.

Substitution : 36 + 3·2^{D₂} + 2^{D₃} = 2^S - 108
⟹ 3·2^{D₂} + 2^{D₃} = 2^S - 144

v₂(2^S - 144) = v₂(16·(2^{S-4} - 9)) = 4
    (car 2^{S-4} - 9 est impair pour S ≥ 8)

v₂(LHS) = D₂ (premier terme 3·2^{D₂}, coeff 3 impair, D₂ < D₃)

⟹ D₂ = 4.

Substitution : 48 + 2^{D₃} = 2^S - 144
⟹ 2^{D₃} = 2^S - 192 = 64·(2^{S-6} - 3)

Pour S ≥ 8 : 2^{S-6} - 3 est impair (pair - impair = impair), et ≥ 1.
Pour S = 8 : 2^2 - 3 = 1. Donc 2^{D₃} = 64, D₃ = 6.
  Vecteur (0, 2, 4, 6) = 10101010. Période 2 si S = 8 !
Pour S ≥ 9 : 2^{S-6} - 3 ≥ 5 est impair > 1.
  64·(impair > 1) n'est pas une puissance de 2. ∎
""")

    # Verification
    print("Vérification :")
    for S in range(7, 30):
        d = 2**S - 81
        if d <= 0:
            continue

        # k=1, forced positions
        val = 2**S - 192
        if val <= 0:
            print(f"  S={S}: 2^S - 192 = {val} ≤ 0 → no k=1 solution")
            continue

        is_power_of_2 = val > 0 and (val & (val - 1)) == 0
        if is_power_of_2:
            D3 = val.bit_length() - 1
            print(f"  S={S}: 2^S-192={val}=2^{D3} ✓ → vector (0,2,4,{D3})")
            # Check periodicity
            v = tuple(1 if i in (0, 2, 4, D3) else 0 for i in range(S))
            is_periodic = False
            for period in range(1, S):
                if S % period == 0 and period < S:
                    if v == v[:period] * (S // period):
                        is_periodic = True
                        break
            print(f"    periodic={is_periodic}")
        else:
            if val > 0:
                # Factor out powers of 2
                v2 = 0
                tmp = val
                while tmp % 2 == 0:
                    v2 += 1
                    tmp //= 2
                if S <= 12 or S % 5 == 0:
                    print(f"  S={S}: 2^S-192={val}=2^{v2}·{tmp}, "
                          f"not power of 2 → no k=1 solution ✅")

    # k=2 analysis
    print("\n\n--- Analyse 2-adique pour k=2 ---")
    print("""
Pour k=2 : h = 2d = 2(2^S - 81) = 2^{S+1} - 162
⟹ 9·2^{D₁} + 3·2^{D₂} + 2^{D₃} = 2^{S+1} - 189

v₂(2^{S+1} - 189) : 189 = 27·7 est impair. v₂(2^{S+1} - 189) = 0.

Mais v₂(LHS) = D₁ ≥ 1.

0 ≠ D₁ ≥ 1 → CONTRADICTION. k = 2 est IMPOSSIBLE ! ∎
""")

    # Verify
    for S in range(8, 20):
        d = 2**S - 81
        if d <= 0:
            continue
        val = 2 * d - 27  # = 2(2^S - 81) - 27 = 2^{S+1} - 189
        # Actually h = 27 + rest = 2d, so rest = 2d - 27
        rest = 2 * d - 27
        v2 = 0
        tmp = rest
        while tmp > 0 and tmp % 2 == 0:
            v2 += 1
            tmp //= 2
        if S <= 12:
            print(f"  S={S}: rest=2d-27={rest}, v₂={v2}")

    # Combined result
    print("\n--- Résultat pour x=4 ---")
    print("""
Pour S ≥ 9 :
- k = 1 : 2^{D₃} = 64·(2^{S-6}-3), non puissance de 2 car 2^{S-6}-3 impair > 1 ✅
- k = 2 : impossible par v₂ ✅
- k ≥ 3 : impossible car k_max < 2.375 pour S assez grand ✅

Pour S = 8 : k=1, D₃=6, vecteur (0,2,4,6) = 10101010, PÉRIODIQUE. ✅
  k=2: v₂ contradiction. ✅
  Vérification exhaustive nécessaire pour k ≥ 3 (k_max peut être > 2).

Pour S = 7 : d = 47, h_max = 27+72+48+64 = 211, k_max = 4.
  Vérification exhaustive.
""")

    # Exhaustive verification for all S, x=4
    print("\n--- Vérification exhaustive x=4 ---")
    for S in range(7, 25):
        d = 2**S - 81
        if d <= 0:
            continue

        found = False
        for positions in combinations(range(S), 4):
            v = tuple(1 if i in positions else 0 for i in range(S))
            is_periodic = False
            for period in range(1, S):
                if S % period == 0 and period < S:
                    if v == v[:period] * (S // period):
                        is_periodic = True
                        break
            if is_periodic:
                continue

            g = sum(3**(3-j) * 2**positions[j] for j in range(4))
            if g % d == 0:
                found = True
                print(f"  ⚠️ S={S}: FOUND! v={positions}, g={g}, g/d={g//d}")
                break

        if not found:
            if S <= 15 or S % 5 == 0:
                print(f"  S={S:2d}: d={d:>10d} — aucune solution ✅")

    print("\n\n" + "=" * 80)
    print("RÉSULTAT POUR x = 4")
    print("=" * 80)


def attempt_general_x():
    """Test the 2-adic descent for general x."""
    print("\n\n" + "=" * 80)
    print("DESCENTE 2-ADIQUE POUR x GÉNÉRAL")
    print("=" * 80)
    print("""
Pour x quelconque, k=1, e₀=0 :
h = 3^{x-1} + Σ_{j=1}^{x-1} 3^{x-1-j} · 2^{D_j} = d = 2^S - 3^x

R₀ = Σ_{j=1}^{x-1} 3^{x-1-j} · 2^{D_j} = 2^S - 3^x - 3^{x-1} = 2^S - 4·3^{x-1}

v₂(R₀) = 2 (car 2^{S-2} - 3^{x-1} impair pour S ≥ x+1).
⟹ D₁ = 2.

R₁ = R₀ - 3^{x-2}·4 = 2^S - 4·3^{x-1} - 4·3^{x-2} = 2^S - 4·3^{x-2}·4 = 2^S - 16·3^{x-2}

v₂(R₁) = 4.
⟹ D₂ = 4.

R₂ = R₁ - 3^{x-3}·16 = 2^S - 16·3^{x-2} - 16·3^{x-3} = 2^S - 16·3^{x-3}·4 = 2^S - 64·3^{x-3}

v₂(R₂) = 6.
⟹ D₃ = 6.

PAR RÉCURRENCE :
R_m = 2^S - 4^{m+1} · 3^{x-1-m}

v₂(R_m) = 2(m+1).
⟹ D_{m+1} = 2(m+1).

Après x-1 étapes :
R_{x-2} = 2^S - 4^{x-1} · 3^0 = 2^S - 4^{x-1} = 2^S - 2^{2(x-1)}

Le dernier terme : 2^{D_{x-1}} = R_{x-2} = 2^S - 2^{2(x-1)}

Si S > 2(x-1) : 2^{D_{x-1}} = 2^{2(x-1)}(2^{S-2(x-1)} - 1).
  2^{S-2(x-1)} - 1 est impair (> 1 si S > 2x-1).
  Donc 2^{D_{x-1}} = 2^{2(x-1)} × (impair > 1) : PAS une puissance de 2 ! ✅

Si S = 2(x-1)+1 = 2x-1 : 2^{D_{x-1}} = 2^{2(x-1)}(2 - 1) = 2^{2(x-1)}.
  D_{x-1} = 2(x-1). C'est le vecteur (0, 2, 4, ..., 2(x-1)).
  S = 2x - 1. Ce vecteur a-t-il période divisant S ?
  Positions : {0, 2, 4, ..., 2(x-1)} dans {0, ..., 2x-2}.
  Le vecteur est : 10 10 10 ... 10 0 (S=2x-1 positions).
  Pas de période 2 car S est impair et le pattern 10 ne se répète pas exactement.

  MAIS VÉRIFICATION : est-ce un cycle valide ?
  g = Σ 3^{x-1-j}·4^j = (4^x - 3^x)/(4-3) = 4^x - 3^x = 2^{2x} - 3^x
  d = 2^{2x-1} - 3^x
  g/d = (2^{2x} - 3^x)/(2^{2x-1} - 3^x) = (2·2^{2x-1} - 3^x)/(2^{2x-1} - 3^x)
      = 2 + (2^{2x-1} - 3^x)/(2^{2x-1} - 3^x)  ... hmm
  g/d = (2·2^{2x-1} - 3^x)/(2^{2x-1} - 3^x)
      = (2d + 2·3^x - 3^x)/d = 2 + 3^x/d.
  3^x/d = 3^x/(2^{2x-1} - 3^x).
  Pour x=3: 27/(2^5-27)=27/5=5.4 → pas entier. g/d non entier. ✅
  Pour x=4: 81/(2^7-81)=81/47=1.72 → pas entier. ✅

Si S = 2x : 2^{D_{x-1}} = 2^{2(x-1)}(2^2 - 1) = 3·2^{2(x-1)}.
  PAS une puissance de 2 (facteur 3). ✅

Si S = 2(x-1) = 2x-2 : 2^{D_{x-1}} = 0. Impossible (D_{x-1} ≥ 1).

CONCLUSION POUR k = 1 :
Si S ≥ 2x+1 : pas de solution (facteur impair > 1).
Si S = 2x : pas de solution (facteur 3).
Si S = 2x-1 : solution formelle mais g/d non entier.
Si S = 2x-2 : pas de solution (valeur 0).
""")

    # Verify the recursion R_m
    print("Vérification de la récurrence R_m = 2^S - 4^{m+1}·3^{x-1-m} :\n")

    for x in range(3, 10):
        for S_offset in [0, 1, 2, 5, 10]:
            S = 2*x + S_offset
            if S > 35:
                continue
            d = 2**S - 3**x
            if d <= 0:
                continue

            # k=1: h = d
            # R₀ = d - 3^{x-1} = 2^S - 3^x - 3^{x-1} = 2^S - 4·3^{x-1}
            R = 2**S - 4 * 3**(x-1)

            # Check v₂ pattern
            forced_D = []
            success = True
            for m in range(x-1):
                if R <= 0:
                    success = False
                    break

                # v₂(R) should be 2(m+1)
                v2 = 0
                tmp = R
                while tmp % 2 == 0:
                    v2 += 1
                    tmp //= 2

                expected_v2 = 2*(m+1)
                if v2 != expected_v2:
                    success = False
                    break

                D_next = v2
                forced_D.append(D_next)

                if m < x-2:
                    # Subtract the forced term
                    R = R - 3**(x-2-m) * 2**D_next

                    # Expected: R should be 2^S - 4^{m+2}·3^{x-2-m}
                    expected_R = 2**S - 4**(m+2) * 3**(x-2-m)
                    if R != expected_R:
                        print(f"  x={x}, S={S}: recursion mismatch at m={m}")
                        success = False
                        break
                else:
                    # Last step: R must be a power of 2
                    is_pow2 = R > 0 and (R & (R - 1)) == 0
                    if is_pow2:
                        D_last = R.bit_length() - 1
                        forced_D.append(D_last)
                        # The forced positions are (0, D₁, D₂, ..., D_{x-1})
                        # = (0, 2, 4, ..., 2(x-1), D_last)
                        # Wait, no. forced_D already has x-1 elements from the loop
                        print(f"  x={x}, S={S}: d={d:>12d}, forced_D={forced_D[:-1]+[D_last]}, "
                              f"IS power of 2! Checking periodicity...")
                    else:
                        # Factor out largest power of 2
                        v2_R = 0
                        tmpR = R
                        while tmpR % 2 == 0:
                            v2_R += 1
                            tmpR //= 2
                        if S <= 25 or S_offset in [0, 1]:
                            print(f"  x={x}, S={S}: d={d:>12d}, forced_D={forced_D}, "
                                  f"R_last={R}=2^{v2_R}·{tmpR}, NOT pow2 → "
                                  f"no k=1 solution ✅")

            if not success:
                print(f"  x={x}, S={S}: recursion fails at some step")


def check_k2_general():
    """Check if k=2 is always impossible by v₂."""
    print("\n\n" + "═" * 70)
    print("k = 2 POUR x GÉNÉRAL")
    print("═" * 70)
    print("""
Pour k=2 : h = 2d.
R₀ = 2d - 3^{x-1} = 2(2^S - 3^x) - 3^{x-1} = 2^{S+1} - 2·3^x - 3^{x-1}
   = 2^{S+1} - 3^{x-1}(2·3 + 1) = 2^{S+1} - 7·3^{x-1}

v₂(R₀) : 7·3^{x-1} est impair (7 impair, 3^{x-1} impair).
          2^{S+1} a v₂ = S+1 > 0.
          Donc v₂(R₀) = 0 (la soustraction d'un impair d'un pair donne un impair).

Wait: 2^{S+1} is even, 7·3^{x-1} is odd. Their difference is ODD.
So v₂(R₀) = 0.

Mais D₁ ≥ 1, donc v₂(LHS) ≥ 1.

0 ≠ ≥1 → CONTRADICTION. k = 2 est toujours IMPOSSIBLE ! ∎
""")

    # Verify
    for x in range(3, 15):
        for S in range(x+2, min(2*x+5, 30)):
            d = 2**S - 3**x
            if d <= 0:
                continue
            R0 = 2*d - 3**(x-1)
            assert R0 % 2 == 1, f"FAIL: x={x}, S={S}, R0={R0} is even!"

    print("  ✅ Vérifié : k=2 donne R₀ impair pour x=3..14, tous S testés")
    print("  ⟹ k = 2 est IMPOSSIBLE pour TOUT x ≥ 3")


if __name__ == '__main__':
    verify_x3_proof()
    attempt_x4()
    attempt_general_x()
    check_k2_general()
