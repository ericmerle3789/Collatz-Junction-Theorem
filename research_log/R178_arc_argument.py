#!/usr/bin/env python3
"""
R178 — L'ARGUMENT D'ARC : Quand ord_p(2) > S empêche la somme nulle

CONTEXTE (R175-R176) :
- Pour le premier résistant p | d, on a observé ord_p(2) > S dans 100% des cas
- Quand ord_p(2) > S, les exposants f_j = t(x-1-j) + e_j ne font PAS de wrapping
- Les puissances 2^{f_j} vivent dans un ARC continu de ⟨2⟩ ⊂ F_p*

PROGRAMME R178 :
1. Vérification étendue ord_p(2) > S pour S jusqu'à 50
2. POURQUOI ord_p(2) > S ? Argument théorique
3. Arc span analysis : quelle fraction du groupe est couverte ?
4. Borne sur la somme : si l'arc est trop court, pas de zéro-somme
5. Cas 3 ∉ ⟨2⟩ : que se passe-t-il ?
"""

from itertools import combinations
from math import gcd, log, log2, ceil, floor
from collections import defaultdict
import time
import sys


def multiplicative_order(a, n):
    """Compute ord_n(a) — multiplicative order of a mod n."""
    if gcd(a, n) != 1:
        return None
    order = 1
    current = a % n
    while current != 1:
        current = (current * a) % n
        order += 1
        if order > n:
            return None
    return order


def prime_factors_set(n):
    """Return set of prime factors of n."""
    if n <= 1:
        return set()
    factors = set()
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.add(d)
            n //= d
        d += 1
    if n > 1:
        factors.add(n)
    return factors


def is_prime(n):
    """Simple primality test."""
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True


def largest_prime_factor(n):
    """Return largest prime factor of n."""
    if n <= 1:
        return None
    lpf = None
    d = 2
    while d * d <= n:
        while n % d == 0:
            lpf = d
            n //= d
        d += 1
    if n > 1:
        lpf = n
    return lpf


def compute_g(positions, x):
    """g(v) = Σ 3^{x-1-j} · 2^{e_j}"""
    return sum(3**(x-1-j) * 2**positions[j] for j in range(x))


def all_aperiodic_vectors(S, x):
    """Generate all aperiodic binary vectors with x ones among S positions."""
    for positions in combinations(range(S), x):
        v = tuple(1 if i in positions else 0 for i in range(S))
        is_periodic = False
        for period in range(1, S):
            if S % period == 0 and period < S:
                if v == v[:period] * (S // period):
                    is_periodic = True
                    break
        if not is_periodic:
            yield positions


def main():
    print("=" * 80)
    print("R178 — L'ARGUMENT D'ARC")
    print("Quand ord_p(2) > S empêche corrSum ≡ 0 mod d")
    print("=" * 80)

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 1 : Vérification étendue de ord_p(2) > S
    # ═══════════════════════════════════════════════════════════════════════
    print("\n" + "═" * 70)
    print("PARTIE 1 : VÉRIFICATION ord_p(2) > S POUR LE PLUS GRAND PREMIER p|d")
    print("═" * 70)
    print("\nPour chaque (S, x) avec d = 2^S - 3^x > 0, on prend p = plus grand")
    print("premier de d et on vérifie ord_p(2) > S.\n")

    results_part1 = []
    violations = []

    max_S = 40  # Extend as far as feasible

    for S in range(3, max_S + 1):
        for x in range(2, S):
            d = 2**S - 3**x
            if d <= 1:
                continue

            p = largest_prime_factor(d)
            if p is None or p <= 1:
                continue

            # For large p, multiplicative_order can be slow
            # Skip if p > 10^8 (would take too long)
            if p > 10**8:
                results_part1.append((S, x, d, p, None, None, "SKIP (p too large)"))
                continue

            o2 = multiplicative_order(2, p)
            if o2 is None:
                continue

            status = "✅ ord > S" if o2 > S else "❌ ord ≤ S"
            ratio = o2 / S

            results_part1.append((S, x, d, p, o2, ratio, status))

            if o2 <= S:
                violations.append((S, x, d, p, o2))

    # Print results
    for S, x, d, p, o2, ratio, status in results_part1:
        if isinstance(status, str) and "SKIP" in status:
            if S <= 30:  # Only print skips for reasonable S
                print(f"  S={S:2d}, x={x:2d}: d={d:>15d}, p_max={p:>15d}, {status}")
        else:
            print(f"  S={S:2d}, x={x:2d}: d={d:>15d}, p_max={p:>15d}, "
                  f"ord_p(2)={o2:>8d}, ratio={ratio:.2f}, {status}")

    n_tested = sum(1 for r in results_part1 if "SKIP" not in str(r[6]))
    n_pass = sum(1 for r in results_part1 if r[6] == "✅ ord > S")
    n_fail = len(violations)

    print(f"\n  RÉSUMÉ : {n_pass}/{n_tested} satisfont ord_p(2) > S ({100*n_pass/n_tested:.1f}%)")
    if violations:
        print(f"  ⚠️ VIOLATIONS :")
        for S, x, d, p, o2 in violations:
            print(f"    S={S}, x={x}: d={d}, p={p}, ord={o2}")
    else:
        print(f"  🎯 AUCUNE VIOLATION — ord_p(2) > S est UNIVERSEL dans cette plage !")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 2 : POURQUOI ord_p(2) > S ? Argument théorique
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 2 : POURQUOI ord_p(2) > S ?")
    print("═" * 70)
    print("""
ARGUMENT :
Si p | (2^S - 3^x), alors 2^S ≡ 3^x mod p.

CAS A : ord_p(2) | S.
  Alors 2^S ≡ 1 mod p, donc 3^x ≡ 1 mod p, donc ord_p(3) | x.
  Cela signifie p | (2^{S/k} - 1) pour k = S/ord_p(2).
  Mais p | (2^S - 3^x), avec 3^x ≡ 1.
  Donc p | (2^S - 1). Mais aussi p | (2^{ord} - 1) avec ord | S.
  Donc p | gcd(2^S - 1, 2^{ord} - 1) = 2^{gcd(S,ord)} - 1 = 2^{ord} - 1.

  ⟹ p est un facteur de 2^{ord} - 1, un nombre de Mersenne.
  Si ord < S, alors p | 2^{S/k} - 1 pour k ≥ 2, donc p ≤ 2^{S/2} - 1.

  Mais p = plus grand premier de d ≈ 2^S. Contradiction si d n'a pas
  trop de petits facteurs premiers.

CAS B : ord_p(2) ∤ S.
  Alors 2^S ≢ 1 mod p. On écrit S = q·ord + r, 0 < r < ord.
  2^S = (2^{ord})^q · 2^r ≡ 2^r mod p.
  Donc 2^r ≡ 3^x mod p, avec 0 < r < ord ≤ S.

  Si ord ≤ S : possible, mais r < ord ≤ S, et 2^r = 3^x en F_p.

  MAIS : pour que ord ≤ S ET p soit grand (p ≈ d ≈ 2^S), on a besoin
  que p | (2^{ord} - 1) avec ord ≤ S, ce qui impose p ≤ 2^S - 1.
  C'est toujours vrai car p | d < 2^S.

  La question est plus subtile : ord_p(2) PEUT être ≤ S sans diviser S.

VÉRIFICATION : regardons si ord | S ou pas, et le rapport ord/S.
""")

    for S, x, d, p, o2, ratio, status in results_part1:
        if isinstance(status, str) and "SKIP" in status:
            continue
        divides_S = S % o2 == 0
        # Check if ord divides (p-1)/2, etc.
        print(f"  S={S:2d}, x={x:2d}: ord={o2:>8d}, ord|S={divides_S}, "
              f"ord/S={ratio:.3f}, S/ord={S/o2:.3f}, "
              f"p/d={p/d:.4f}")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 3 : L'ARC — span des exposants et conséquences
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 3 : ANALYSE DE L'ARC")
    print("═" * 70)
    print("""
Quand 3 ∈ ⟨2⟩ mod p et ord_p(2) > S :
  g(v) = Σ_{j} 2^{f_j} mod p, avec f_j = t(x-1-j) + e_j.

  f_min = min(f_j) = t(x-1) + e_0 ≥ t(x-1)         (car e_0 ≥ 0)
  Wait, non : f_j = t(x-1-j) + e_j.
  - Pour j=0: f_0 = t(x-1) + e_0 (grand t-composante, petit e-composante)
  - Pour j=x-1: f_{x-1} = 0 + e_{x-1} = e_{x-1} (pas de t-composante, grand e)

  f_min = min(e_{x-1}, t(x-1) + e_0) — dépend de la compétition t vs S/x
  f_max = max(t(x-1) + e_{S-?}, ...)

  ARC SPAN = f_max - f_min (avant réduction mod ord).
  Si arc_span < ord, pas de wrapping.

  BORNE CRUCIALE :
  Σ 2^{f_j} (dans Z) ≤ x · 2^{f_max}
  Σ 2^{f_j} (dans Z) ≥ x · 2^{f_min}  (si tous distincts)

  Pour que Σ ≡ 0 mod p : Σ = k·p pour un entier k ≥ 1.
  Donc x · 2^{f_min} ≤ k·p ≤ x · 2^{f_max}.
""")

    for S in range(3, 20):
        for x in range(2, min(S, 8)):  # Limit x for tractability
            d = 2**S - 3**x
            if d <= 1:
                continue

            p = largest_prime_factor(d)
            if p <= 1 or p > 10**6:
                continue

            o2 = multiplicative_order(2, p)
            if o2 is None or o2 <= S:
                continue

            # Find t with 3 = 2^t mod p (if exists)
            t = None
            power = 1
            for k in range(1, o2 + 1):
                power = power * 2 % p
                if power == 3 % p:
                    t = k
                    break

            if t is None:
                continue

            # Analyze arc for all aperiodic vectors
            min_arc = float('inf')
            max_arc = 0
            sum_in_Z_min = float('inf')
            sum_in_Z_max = 0
            total_vectors = 0

            for positions in all_aperiodic_vectors(S, x):
                total_vectors += 1

                # Compute exponents f_j (NOT reduced mod o2)
                exponents = [t * (x-1-j) + positions[j] for j in range(x)]

                arc_span = max(exponents) - min(exponents)
                min_arc = min(min_arc, arc_span)
                max_arc = max(max_arc, arc_span)

                # Sum in Z (exact)
                sum_Z = sum(2**f for f in exponents)
                sum_in_Z_min = min(sum_in_Z_min, sum_Z)
                sum_in_Z_max = max(sum_in_Z_max, sum_Z)

            if total_vectors == 0:
                continue

            # How many multiples of p fit in [sum_min, sum_max]?
            k_min = sum_in_Z_min // p + 1
            k_max = sum_in_Z_max // p
            n_multiples = max(0, k_max - k_min + 1)

            max_f_possible = t * (x-1) + (S-1)  # Upper bound on any f_j

            print(f"  S={S:2d}, x={x}: d={d:>8d}, p={p:>8d}, o2={o2:>6d}, t={t:>4d}")
            print(f"    arc: [{min_arc}, {max_arc}], max_f={max_f_possible}, "
                  f"arc/o2={max_arc/o2:.3f}")
            print(f"    Σ(Z): [{sum_in_Z_min:.2e}, {sum_in_Z_max:.2e}]")
            print(f"    multiples of p in range: {n_multiples} "
                  f"(k ∈ [{k_min}, {k_max}])")
            if n_multiples == 0:
                print(f"    🎯 AUCUN multiple de p → preuve par SIZE !")
            else:
                print(f"    ⚠️ {n_multiples} multiples possibles — "
                      f"need finer analysis")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 4 : Le cas clé — quand l'arc est TROP COURT pour contenir 0
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 4 : BORNE DE TAILLE SUR L'ARC")
    print("═" * 70)
    print("""
THÉORÈME (hypothétique) : Si ord_p(2) > S et arc_span < ord_p(2),
alors les 2^{f_j} vivent dans un arc de longueur arc_span du groupe
cyclique d'ordre ord_p(2). Leur somme dans Z est :

  Σ 2^{f_j} ∈ [2^{f_min} · x, 2^{f_max} · x]

Chaque terme est 2^{f_j} mod p, donc dans {1, ..., p-1}.
La somme mod p est dans {0, ..., (x-1)(p-1)}.

Pour que la somme ≡ 0 mod p, il faut Σ = k·p.

OBSERVATION CLÉ : Si tous les f_j sont dans [A, A + arc_span],
alors dans Z :
  Σ 2^{f_j} ∈ [x · 2^A, x · 2^{A + arc_span}]

La "densité" de multiples de p dans cet intervalle est :
  x · 2^{arc_span} · (2-1) / p ≈ x · 2^{arc_span} / p

Si x · 2^{arc_span} < p, il y a AU PLUS UN multiple de p.
Si x · 2^{arc_span} << p, il n'y a AUCUN multiple → g ≢ 0.

Pour x petit et arc_span ~ S, on a 2^{arc_span} ~ 2^S ~ p/ε,
donc il y a ~ x multiples. Pas suffisant pour conclure.

MAIS : les 2^{f_j} ne sont pas QUELCONQUES dans l'intervalle.
Ils sont FIXÉS par les contraintes e_0 < e_1 < ... < e_{x-1}.
""")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 5 : Nouvelle idée — la somme EXACTE vs les multiples de p
    # ═══════════════════════════════════════════════════════════════════════
    print("\n" + "═" * 70)
    print("PARTIE 5 : SOMME EXACTE DANS Z vs MULTIPLES DE p")
    print("═" * 70)
    print("""
Pour x = 3 (le premier cas non-trivial) :
g(v) = 9·2^{e_0} + 3·2^{e_1} + 2^{e_2}, avec e_0 < e_1 < e_2.

g(v) = 2^{e_0} · (9 + 3·2^{Δ1} + 2^{Δ2}) où Δ1=e_1-e_0, Δ2=e_2-e_0.

Puisque gcd(2^{e_0}, d) = 1 (d impair) :
  d | g ⟺ d | (9 + 3·2^{Δ1} + 2^{Δ2})

h(Δ1, Δ2) = 9 + 3·2^{Δ1} + 2^{Δ2} avec 1 ≤ Δ1, Δ1 < Δ2, Δ2 ≤ S-1.

h_min = 9 + 6 + 8 = 23 (Δ1=1, Δ2=2 : impossible car Δ1 < Δ2 et Δ2 ≥ 2)
Wait: e_0 < e_1 < e_2. If e_0=0: Δ1 ≥ 1, Δ2 ≥ 2, and Δ1 < Δ2.

h_min = 9 + 3·2 + 4 = 19 (Δ1=1, Δ2=2)
h_max = 9 + 3·2^{S-2} + 2^{S-1}

d = 2^S - 27 pour x=3.

Pour S ≥ 6 : d = 2^S - 27 > 9 + 3·2^{S-2} + 2^{S-1} ?
  2^S - 27 > 9 + 3·2^{S-2} + 2^{S-1}
  2^S - 2^{S-1} - 3·2^{S-2} > 36
  2^{S-2}(4 - 2 - 3) > 36
  -2^{S-2} > 36 — IMPOSSIBLE !

Donc h_max > d pour tout S ≥ 6. L'argument de taille ne suffit pas pour x=3.
""")

    # Explicit enumeration for x=3
    print("Énumération pour x=3 :")
    for S in range(5, 25):
        d = 2**S - 27
        if d <= 0:
            continue

        # h(Δ1, Δ2) = 9 + 3·2^Δ1 + 2^Δ2
        # with 1 ≤ Δ1 < Δ2 ≤ S-1
        found_zero = False
        n_candidates = 0
        min_residue = d

        for D1 in range(1, S-1):
            for D2 in range(D1+1, S):
                h = 9 + 3 * (2**D1) + 2**D2
                r = h % d
                n_candidates += 1
                if r < min_residue:
                    min_residue = r
                if r == 0:
                    found_zero = True
                    # Verify this comes from valid aperiodic vector
                    # e_0=0, e_1=D1, e_2=D2. Vector has 1s at positions 0, D1, D2.
                    v = tuple(1 if i in (0, D1, D2) else 0 for i in range(S))
                    is_periodic = False
                    for period in range(1, S):
                        if S % period == 0 and period < S:
                            if v == v[:period] * (S // period):
                                is_periodic = True
                                break
                    print(f"  S={S:2d}: d={d:>12d}, h(Δ1={D1},Δ2={D2})={h}, "
                          f"h/d={h/d:.4f}, periodic={is_periodic}")

        if not found_zero:
            print(f"  S={S:2d}: d={d:>12d}, {n_candidates} candidats, "
                  f"min_residue={min_residue} ({min_residue/d:.6f}·d)")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 6 : Structure fine — résidus h mod p pour x=3
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 6 : RÉSIDUS h(Δ1,Δ2) mod p POUR x=3 ET d PREMIER")
    print("═" * 70)

    for S in range(5, 22):
        d = 2**S - 27
        if d <= 1 or not is_prime(d):
            continue

        p = d
        o2 = multiplicative_order(2, p)
        if o2 is None:
            continue

        # Distribution of h mod p
        residues = []
        for D1 in range(1, S-1):
            for D2 in range(D1+1, S):
                h = 9 + 3 * (2**D1) + 2**D2
                residues.append(h % p)

        n = len(residues)
        zero_count = residues.count(0)

        # How spread are the residues?
        unique_res = len(set(residues))

        print(f"  S={S:2d}: p={p:>12d}, ord_p(2)={o2:>8d}, ord/S={o2/S:.1f}, "
              f"#residues={n}, #unique={unique_res}/{p} ({100*unique_res/p:.1f}%), "
              f"zero_count={zero_count}")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 7 : KEY TEST — ord_p(2) > S pour TOUS les facteurs premiers
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 7 : ord_p(2) > S POUR CHAQUE FACTEUR PREMIER (pas juste le max)")
    print("═" * 70)
    print("Si ord_p(2) > S pour TOUS p | d, alors aucun facteur ne divise g(v).\n")

    for S in range(3, 30):
        for x in range(2, min(S, 12)):
            d = 2**S - 3**x
            if d <= 1:
                continue

            primes = sorted(prime_factors_set(d))
            if not primes:
                continue

            # Check ord for ALL primes
            all_ord_gt_S = True
            min_ratio = float('inf')
            details = []
            skip = False

            for p in primes:
                if p > 10**7:
                    skip = True
                    break
                o = multiplicative_order(2, p)
                if o is None:
                    skip = True
                    break
                ratio = o / S
                min_ratio = min(min_ratio, ratio)
                details.append((p, o, ratio))
                if o <= S:
                    all_ord_gt_S = False

            if skip:
                continue

            if len(primes) >= 2 or not all_ord_gt_S:
                status = "✅ ALL ord > S" if all_ord_gt_S else "❌ SOME ord ≤ S"
                primes_str = "·".join(str(p) for p in primes)
                details_str = ", ".join(f"p={p}:ord={o}({r:.1f}x)"
                                       for p, o, r in details)
                print(f"  S={S:2d}, x={x:2d}: d={d:>10d} = {primes_str}, "
                      f"{status}, [{details_str}]")

    # Count overall
    print("\n  RÉSUMÉ PARTIE 7 :")
    all_ok = 0
    some_fail = 0
    for S in range(3, 25):
        for x in range(2, min(S, 10)):
            d = 2**S - 3**x
            if d <= 1:
                continue
            primes = sorted(prime_factors_set(d))
            if not primes:
                continue
            ok = True
            for p in primes:
                if p > 10**7:
                    ok = None
                    break
                o = multiplicative_order(2, p)
                if o is None or o <= S:
                    ok = False
                    break
            if ok is True:
                all_ok += 1
            elif ok is False:
                some_fail += 1

    print(f"  Résultat : {all_ok} cas avec ALL ord > S, {some_fail} cas avec SOME ord ≤ S")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 8 : Quand ord_p(2) ≤ S, que se passe-t-il ?
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 8 : CAS ord_p(2) ≤ S — LE PETIT PREMIER PASSE-T-IL ?")
    print("═" * 70)
    print("Quand un petit premier p | d a ord_p(2) ≤ S, vérifions si p | g(v)\n")

    for S in range(3, 25):
        for x in range(2, min(S, 8)):
            d = 2**S - 3**x
            if d <= 1:
                continue

            primes = sorted(prime_factors_set(d))

            for p in primes:
                if p > 10**5:
                    continue
                o = multiplicative_order(2, p)
                if o is None or o > S:
                    continue

                # ord_p(2) ≤ S — check if p | g(v) for some v
                found_div = False
                total = 0
                div_count = 0

                for positions in all_aperiodic_vectors(S, x):
                    total += 1
                    if total > 10000:
                        break
                    g = compute_g(positions, x)
                    if g % p == 0:
                        div_count += 1
                        found_div = True

                if total > 0:
                    print(f"  S={S:2d}, x={x}: p={p} (ord={o} ≤ S={S}), "
                          f"p|g: {div_count}/{total} = {100*div_count/total:.1f}%"
                          f"{' — WRAPPING ALLOWS DIVISIBILITY !' if found_div else ' — still resistant'}")

    print("\n\n" + "═" * 70)
    print("SYNTHÈSE R178")
    print("═" * 70)


if __name__ == '__main__':
    main()
