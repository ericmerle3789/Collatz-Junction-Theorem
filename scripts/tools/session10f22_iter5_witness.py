#!/usr/bin/env python3
"""
SESSION 10f22 — G-V-R ITERATION 5 : LUMIERE SPECIALE
"Primes témoins" pour les 4 rebelles k=61, 3895, 4500, 6891

IDEE (inspirée par Eric) : Au lieu de regarder la TAILLE du gcd
(argument de taille, qui échoue), regarder la STRUCTURE FINE.

Un prime p est "témoin" pour k si :
  v_p(ord) > v_p(C)
  i.e. p divise l'ordre avec une puissance SUPERIEURE à celle dans C.
  Si un tel p existe, alors ord ∤ C, donc 2^C ≢ 1 mod d.

Pour p | (d-1) avec 2^{(d-1)/p} ≢ 1 mod d (i.e. p ∤ Q) :
  v_p(ord) = v_p(d-1)
  On cherche v_p(d-1) > v_p(C)

Cas spécial k=61 : d a 95 bits, d-1 FACTORISABLE → Q_exact calculable.
"""
import sys
import math
sys.stdout.reconfigure(line_buffering=True)

def ceil_log2_3(k):
    return math.ceil(k * math.log2(3))

try:
    from sympy import isprime, factorint
    check_prime = isprime
    HAS_SYMPY = True
except ImportError:
    def check_prime(n):
        if n < 2: return False
        if n < 4: return True
        if n % 2 == 0: return False
        return pow(2, n-1, n) == 1 and pow(3, n-1, n) == 1
    factorint = None
    HAS_SYMPY = False

def v_p(n, p):
    """Valuation p-adique de n."""
    if n == 0: return float('inf')
    v = 0
    while n % p == 0:
        v += 1
        n //= p
    return v

def v_p_binom(n, k_choose, p):
    """v_p(binom(n, k)) par la formule de Legendre/Kummer."""
    # v_p(n!) = sum floor(n/p^i)
    def v_p_fact(m):
        s = 0; pk = p
        while pk <= m:
            s += m // pk
            pk *= p
        return s
    return v_p_fact(n) - v_p_fact(k_choose) - v_p_fact(n - k_choose)

rebels = [61, 3895, 4500, 6891]

# ================================================================
# W1. RAPPEL : CROSS-CHECK AVEC ITERATION 1
# ================================================================
print("=" * 70)
print("W1. CROSS-CHECK : QUELS REBELLES ONT DEJA UN PETIT PRIME GAGNANT ?")
print("=" * 70)

# D'après iter 1 (I8) : 8 cas sans petit premier gagnant p <= 47 :
# k=61, 148, 185, 655, 917, 2183, 6891, 7752
# => k=3895 et k=4500 NE SONT PAS dans cette liste
# => ils devraient AVOIR un petit premier gagnant !

print("\n  Vérification : pour chaque rebelle, chercher un prime p <= 200")
print("  tel que v_p(ord) > v_p(C) [avec Q_pred].\n")

primes_list = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
               53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107,
               109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167,
               173, 179, 181, 191, 193, 197, 199]

for k in rebels:
    S = ceil_log2_3(k)
    d = pow(2, S) - pow(3, k)
    if d <= 1 or not check_prime(d):
        continue
    dm1 = d - 1
    C_binom_n = S - 1
    C_binom_k = k - 1

    print(f"  k={k}, S={S}, d~2^{d.bit_length()}")

    witnesses_found = []
    for p in primes_list:
        # v_p(d-1)
        vp_dm1 = v_p(dm1, p)
        if vp_dm1 == 0:
            continue  # p ne divise pas d-1, pas utile

        # v_p(C) par Legendre
        vp_C = v_p_binom(C_binom_n, C_binom_k, p)

        # v_p(Q) : est-ce que p | Q ?
        # p | Q ssi p | (d-1) et 2^{(d-1)/p} ≡ 1 mod d
        vp_Q = 0
        for e in range(1, vp_dm1 + 1):
            if pow(2, dm1 // (p**e), d) == 1:
                vp_Q += 1
            else:
                break

        vp_ord = vp_dm1 - vp_Q

        if vp_ord > vp_C:
            witnesses_found.append((p, vp_ord, vp_C, vp_dm1, vp_Q))

    if witnesses_found:
        print(f"    ★ TEMOIN(S) TROUVE(S) :")
        for p, vo, vc, vd, vq in witnesses_found:
            print(f"      p={p}: v_p(ord)={vo} > v_p(C)={vc}"
                  f"  [v_p(d-1)={vd}, v_p(Q)={vq}]")
        print(f"    => k={k} RESOLU par prime témoin p={witnesses_found[0][0]} ✓")
    else:
        print(f"    ⚠ Aucun témoin p <= 199 trouvé.")
    print()

# ================================================================
# W2. CAS k=61 : FACTORISATION COMPLETE DE d-1
# ================================================================
print("=" * 70)
print("W2. CAS k=61 : FACTORISATION COMPLETE DE d-1 (95 bits)")
print("=" * 70)

k = 61
S = ceil_log2_3(k)
d = pow(2, S) - pow(3, k)
dm1 = d - 1
C_val = math.comb(S - 1, k - 1)

print(f"\n  k={k}, S={S}, d={d}")
print(f"  d-1 = {dm1}")
print(f"  d-1 a {dm1.bit_length()} bits ({len(str(dm1))} chiffres)")
print(f"  C = binom({S-1}, {k-1}) ≈ 2^{C_val.bit_length()}")

if HAS_SYMPY:
    print(f"\n  Factorisation de d-1 :")
    f = factorint(dm1)
    print(f"    d-1 = {f}")
    # Calcul de Q exact
    Q_exact = 1
    for p, e in f.items():
        for exp in range(1, e + 1):
            if pow(2, dm1 // (p**exp), d) == 1:
                Q_exact *= p
            else:
                break
    ord_val = dm1 // Q_exact
    print(f"\n  Q_exact = {Q_exact}")
    print(f"  ord = (d-1)/Q = {ord_val}")
    print(f"  ord ~ 2^{ord_val.bit_length()}")
    print(f"  C ~ 2^{C_val.bit_length()}")
    print(f"  C < ord ? {C_val < ord_val}")
    if C_val < ord_val:
        print(f"  ★★★ k=61 PROUVE par factorisation explicite de d-1 ★★★")
        print(f"  (Q={Q_exact}, ord=d-1/{Q_exact}, C < ord)")
else:
    print(f"\n  sympy non disponible, factorisation impossible.")

# ================================================================
# W3. RECHERCHE ETENDUE : PRIMES TEMOINS p <= 10000
# ================================================================
print("\n" + "=" * 70)
print("W3. RECHERCHE ETENDUE : PRIMES TEMOINS p <= 10000")
print("=" * 70)

# Generate primes up to 10000 using sieve
def sieve(n):
    is_p = [True] * (n + 1)
    is_p[0] = is_p[1] = False
    for i in range(2, int(n**0.5) + 1):
        if is_p[i]:
            for j in range(i*i, n + 1, i):
                is_p[j] = False
    return [i for i in range(2, n + 1) if is_p[i]]

big_primes = sieve(10000)
print(f"  Testant {len(big_primes)} primes p <= 10000 pour les rebelles sans témoin.\n")

for k in rebels:
    S = ceil_log2_3(k)
    d = pow(2, S) - pow(3, k)
    if d <= 1 or not check_prime(d):
        continue
    dm1 = d - 1
    C_binom_n = S - 1
    C_binom_k = k - 1

    # Skip if already resolved by small prime
    # (we'll check regardless for completeness)
    print(f"  k={k}, S={S}:")

    best_witness = None
    witnesses_count = 0

    for p in big_primes:
        vp_dm1 = v_p(dm1, p)
        if vp_dm1 == 0:
            continue

        vp_C = v_p_binom(C_binom_n, C_binom_k, p)

        # Quick check: if vp_dm1 <= vp_C, skip detailed Q computation
        if vp_dm1 <= vp_C:
            continue

        # v_p(Q): check if p | Q
        vp_Q = 0
        for e in range(1, vp_dm1 + 1):
            if pow(2, dm1 // (p**e), d) == 1:
                vp_Q += 1
            else:
                break

        vp_ord = vp_dm1 - vp_Q
        if vp_ord > vp_C:
            if best_witness is None:
                best_witness = (p, vp_ord, vp_C, vp_dm1, vp_Q)
            witnesses_count += 1

    if best_witness:
        p, vo, vc, vd, vq = best_witness
        print(f"    ★ PREMIER TEMOIN : p={p}, v_p(ord)={vo} > v_p(C)={vc}")
        print(f"      [v_p(d-1)={vd}, v_p(Q)={vq}]")
        print(f"    Total témoins p <= 10000 : {witnesses_count}")
        print(f"    => k={k} RESOLU par prime témoin ✓")
    else:
        print(f"    ⚠ AUCUN témoin p <= 10000 trouvé.")
    print()

# ================================================================
# W4. SYNTHESE : COMBIEN DE REBELLES RESOLUS ?
# ================================================================
print("=" * 70)
print("W4. SYNTHESE LUMIERE SPECIALE")
print("=" * 70)

# Re-run complete analysis for all 19 cases
all_prime_cases = []
for kk in range(3, 10001):
    SS = ceil_log2_3(kk)
    dd = pow(2, SS) - pow(3, kk)
    if dd > 1 and check_prime(dd):
        all_prime_cases.append((kk, SS, dd))

print(f"\n  Analyse complete pour les {len(all_prime_cases)} d premiers :\n")
print(f"  {'k':>5s} | {'method':>20s} | {'detail':>30s}")
print("  " + "-" * 62)

resolved_size = 0
resolved_witness = 0
resolved_factor = 0
unresolved = 0

for kk, SS, dd in all_prime_cases:
    dm1 = dd - 1
    C_binom_n = SS - 1
    C_binom_k = kk - 1
    g = math.gcd(math.comb(C_binom_n, C_binom_k), dm1)

    if 0 < g < dd.bit_length():
        method = "taille (g<log₂d)"
        detail = f"g={g}, log₂d={dd.bit_length()}"
        resolved_size += 1
    else:
        # Search for witness prime
        found = False
        # Use extended primes for rebels
        search_primes = big_primes if kk in rebels else primes_list

        for p in search_primes:
            vp_dm1 = v_p(dm1, p)
            if vp_dm1 == 0:
                continue
            vp_C = v_p_binom(C_binom_n, C_binom_k, p)
            if vp_dm1 <= vp_C:
                continue
            vp_Q = 0
            for e in range(1, vp_dm1 + 1):
                if pow(2, dm1 // (p**e), dd) == 1:
                    vp_Q += 1
                else:
                    break
            vp_ord = vp_dm1 - vp_Q
            if vp_ord > vp_C:
                method = f"témoin p={p}"
                detail = f"v_p(ord)={vp_ord} > v_p(C)={vp_C}"
                resolved_witness += 1
                found = True
                break

        if not found:
            # Try explicit factoring for small d
            if dd.bit_length() <= 128 and HAS_SYMPY:
                f = factorint(dm1)
                Q_ex = 1
                for p, e in f.items():
                    for exp in range(1, e + 1):
                        if pow(2, dm1 // (p**exp), dd) == 1:
                            Q_ex *= p
                        else:
                            break
                ord_ex = dm1 // Q_ex
                C_val_ex = math.comb(C_binom_n, C_binom_k)
                if C_val_ex < ord_ex:
                    method = "factorisation d-1"
                    detail = f"Q={Q_ex}, C<ord"
                    resolved_factor += 1
                    found = True
                else:
                    method = "??? (C >= ord)"
                    detail = "PROBLEME"
                    unresolved += 1
            else:
                method = "NON RESOLU"
                detail = "Artin"
                unresolved += 1

    print(f"  {kk:5d} | {method:>20s} | {detail:>30s}")

print(f"\n  BILAN :")
print(f"    Par taille (g < log₂d)    : {resolved_size}/19")
print(f"    Par prime témoin           : {resolved_witness}/19")
print(f"    Par factorisation d-1      : {resolved_factor}/19")
print(f"    NON RESOLU (Artin)         : {unresolved}/19")
print(f"    TOTAL RESOLU               : {resolved_size + resolved_witness + resolved_factor}/19")

# ================================================================
# W5. POUR LES NON-RESOLUS : QUELLE TAILLE DE p FAUDRAIT-IL ?
# ================================================================
if unresolved > 0:
    print("\n" + "=" * 70)
    print("W5. ANALYSE DES CAS NON RESOLUS")
    print("=" * 70)

    for kk, SS, dd in all_prime_cases:
        dm1 = dd - 1
        C_binom_n = SS - 1
        C_binom_k = kk - 1
        g = math.gcd(math.comb(C_binom_n, C_binom_k), dm1)

        if g >= dd.bit_length():
            # Check if this rebel is still unresolved
            found_any = False
            for p in big_primes:
                vp_dm1 = v_p(dm1, p)
                if vp_dm1 == 0:
                    continue
                vp_C = v_p_binom(C_binom_n, C_binom_k, p)
                if vp_dm1 <= vp_C:
                    continue
                vp_Q = 0
                for e in range(1, vp_dm1 + 1):
                    if pow(2, dm1 // (p**e), dd) == 1:
                        vp_Q += 1
                    else:
                        break
                if vp_dm1 - vp_Q > vp_C:
                    found_any = True
                    break

            if dd.bit_length() <= 128 and HAS_SYMPY:
                found_any = True  # handled by factoring

            if not found_any:
                print(f"\n  k={kk} (d ~ 2^{dd.bit_length()}):")
                print(f"    gcd = {g} = ", end="")
                # Factor g
                temp = g
                factors = {}
                for p in range(2, min(10000, g + 1)):
                    while temp % p == 0:
                        factors[p] = factors.get(p, 0) + 1
                        temp //= p
                if temp > 1:
                    factors[temp] = factors.get(temp, 0) + 1
                parts = [f"{p}^{e}" if e > 1 else str(p) for p, e in sorted(factors.items())]
                print(" × ".join(parts))

                print(f"    Pour chaque facteur premier p de g :")
                for p in sorted(factors.keys()):
                    if p > 10000:
                        continue
                    vp_dm1 = v_p(dm1, p)
                    vp_C = v_p_binom(C_binom_n, C_binom_k, p)
                    vp_Q = 0
                    for e in range(1, vp_dm1 + 1):
                        if pow(2, dm1 // (p**e), dd) == 1:
                            vp_Q += 1
                        else:
                            break
                    vp_ord = vp_dm1 - vp_Q
                    status = "✓ TEMOIN" if vp_ord > vp_C else "⚠ pas témoin"
                    print(f"      p={p}: v_p(d-1)={vp_dm1}, v_p(C)={vp_C}, "
                          f"v_p(Q)={vp_Q}, v_p(ord)={vp_ord}  {status}")

                # Check: Q_pred with extended list
                print(f"    Q_pred étendu (p <= 10000) :")
                Q_extended = 1
                for p in big_primes:
                    if dm1 % p != 0:
                        continue
                    max_e = v_p(dm1, p)
                    for e in range(1, max_e + 1):
                        if pow(2, dm1 // (p**e), dd) == 1:
                            Q_extended *= p
                        else:
                            break
                print(f"      Q_pred(p<=10000) = {Q_extended}")
                C_val = math.comb(C_binom_n, C_binom_k)
                print(f"      C ~ 2^{C_val.bit_length()}, d-1 ~ 2^{dm1.bit_length()}")
                print(f"      Marge : il faudrait Q < 2^{dm1.bit_length() - C_val.bit_length()}")
                print(f"      Q_extended = {Q_extended} << 2^{dm1.bit_length() - C_val.bit_length()}")
                print(f"      => MORALEMENT résolu (Q << marge) mais pas PROUVÉ")

print("\n" + "=" * 70)
print("FIN ITERATION 5 : LUMIERE SPECIALE")
print("=" * 70)
