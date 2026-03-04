"""
SESSION 7 — OBSTRUCTION PAR FACTEUR PREMIER

IDEE CLE : Si d = p1 * p2 * ... * pr, alors
  corrSum ≡ 0 (mod d) ssi corrSum ≡ 0 (mod pi) pour tout i.

  Si pour UN SEUL facteur premier pi, aucune composition n'a corrSum ≡ 0 (mod pi),
  alors N_0(d) = 0.

  Cela reduirait le probleme a une congruence modulo un SEUL premier !

EXPERIENCE 1 : Pour chaque k, factoriser d et tester N_0(pi) pour chaque pi.
EXPERIENCE 2 : Si un pi bloque toujours, etudier la structure de ce pi.
EXPERIENCE 3 : Tester N_0(m) pour des PETITS moduli m (pas forcement diviseurs de d).
EXPERIENCE 4 : Chercher un modulus universel m tel que N_0(m) = 0 pour tout k.
"""

from math import comb, ceil, log2, gcd
from itertools import combinations
from sympy import factorint, isprime

def compute_params(k):
    S = ceil(k * log2(3))
    d = 2**S - 3**k
    return S, d

def count_zero_mod_m(k, p=1, m=None):
    """
    Compter le nombre de compositions (0, p, p+1, q_3, ..., q_{k-1})
    ordonnees, avec corrSum ≡ 0 (mod m).

    Si m=None, utilise d.
    """
    S, d = compute_params(k)
    if m is None:
        m = d

    prefix = (9 + 5 * pow(2, p)) * pow(3, k-3)

    available = list(range(p + 2, S))
    n_choices = k - 3

    if n_choices < 0 or n_choices > len(available):
        return 0, 0  # n_zero, n_total

    n_total = comb(len(available), n_choices)

    # Si trop de compositions, on ne peut pas enumerer
    if n_total > 2000000:
        return -1, n_total  # -1 = trop grand

    n_zero = 0
    for positions in combinations(available, n_choices):
        suffix = sum(pow(3, k-1-j) * pow(2, q)
                    for j, q in zip(range(3, k), positions))
        cs = prefix + suffix
        if cs % m == 0:
            n_zero += 1

    return n_zero, n_total

def experiment1_prime_factors():
    """Pour chaque k, factoriser d et tester N_0(pi)."""
    print("=" * 70)
    print("EXPERIENCE 1 : N_0 par facteur premier de d")
    print("=" * 70)

    for k in range(5, 16):
        S, d = compute_params(k)
        if d <= 0:
            continue

        factors = factorint(d)
        n_total = comb(S - 3, k - 3)  # pour p=1

        print(f"\n  k={k}, S={S}, d={d} = ", end="")
        print(" × ".join(f"{p}^{e}" if e > 1 else str(p) for p, e in factors.items()))

        if n_total > 2000000:
            print(f"    C = {n_total} — trop grand pour enum complete")
            # Tester juste les petits facteurs premiers
            for prime in sorted(factors.keys()):
                if prime <= 1000:
                    n_zero, _ = count_zero_mod_m(k, p=1, m=prime)
                    print(f"    N_0 mod {prime} = {n_zero}/{n_total}", end="")
                    if n_zero == 0:
                        print(f"  ← BLOQUANT !")
                    else:
                        print(f"  (ratio = {n_zero/n_total:.6f})")
                else:
                    print(f"    p={prime} trop grand pour test")
            continue

        # Tester chaque facteur premier
        blocking_primes = []
        for prime in sorted(factors.keys()):
            n_zero, _ = count_zero_mod_m(k, p=1, m=prime)
            is_blocking = n_zero == 0
            print(f"    N_0 mod {prime} = {n_zero}/{n_total}", end="")
            if is_blocking:
                print(f"  ← BLOQUANT !")
                blocking_primes.append(prime)
            else:
                print(f"  (ratio = {n_zero/n_total:.6f})")

        # Tester aussi d complet
        n_zero_d, _ = count_zero_mod_m(k, p=1, m=d)
        print(f"    N_0 mod d = {n_zero_d}/{n_total} (direct)")

        if blocking_primes:
            print(f"    >>> BLOQUÉ par : {blocking_primes}")
        elif n_zero_d == 0:
            print(f"    >>> N_0(d)=0 mais AUCUN facteur premier ne bloque seul !")

def experiment2_small_moduli():
    """Tester N_0(m) pour des petits moduli m (pas forcement diviseurs de d)."""
    print("\n" + "=" * 70)
    print("EXPERIENCE 2 : N_0 pour petits moduli")
    print("=" * 70)

    moduli = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 17, 19, 23, 29, 31, 37, 41, 43, 47]

    for k in range(5, 12):
        S, d = compute_params(k)
        n_total = comb(S - 3, k - 3)

        print(f"\n  k={k}, S={S}, d={d}")

        blocking = []
        for m in moduli:
            if n_total > 500000:
                break
            n_zero, _ = count_zero_mod_m(k, p=1, m=m)
            if n_zero == 0:
                blocking.append(m)
                print(f"    N_0 mod {m} = 0  ← BLOQUANT")

        if blocking:
            print(f"    Moduli bloquants : {blocking}")
        else:
            print(f"    Aucun petit modulus ne bloque")

def experiment3_universal_modulus():
    """
    Chercher un modulus m qui bloque pour TOUS les k testes.

    Candidats : si m | d(k) pour tout k, ou si corrSum a une propriete
    mod m independante de k.
    """
    print("\n" + "=" * 70)
    print("EXPERIENCE 3 : Recherche de modulus universel")
    print("=" * 70)

    # D'abord, trouver les d(k) et leurs facteurs communs
    print("\n  Facteurs de d(k) :")
    d_values = {}
    for k in range(3, 20):
        S, d = compute_params(k)
        if d > 0:
            d_values[k] = d
            factors = factorint(d)
            fstr = " × ".join(f"{p}^{e}" if e > 1 else str(p) for p, e in factors.items())
            print(f"    k={k}: d={d} = {fstr}")

    # GCD de tous les d(k)
    from functools import reduce
    all_d = [d_values[k] for k in range(3, 20) if k in d_values]
    g = reduce(gcd, all_d)
    print(f"\n  GCD de tous les d(k), k=3..19 : {g}")

    # Tester des moduli candidats
    candidates = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

    for m in candidates:
        results = {}
        all_blocking = True
        for k in range(5, 11):
            S, d = compute_params(k)
            n_total = comb(S - 3, k - 3)
            if n_total > 500000:
                results[k] = "skip"
                continue
            n_zero, _ = count_zero_mod_m(k, p=1, m=m)
            results[k] = n_zero
            if n_zero > 0:
                all_blocking = False

        if all_blocking and all(v == 0 or v == "skip" for v in results.values()):
            print(f"\n  m={m}: POTENTIELLEMENT UNIVERSEL")
            for k, v in results.items():
                print(f"    k={k}: N_0 = {v}")
        else:
            non_blocking = {k: v for k, v in results.items() if v != 0 and v != "skip"}
            if non_blocking:
                # Just show first non-blocking
                k0 = list(non_blocking.keys())[0]
                print(f"  m={m}: non-bloquant (k={k0}: N_0={non_blocking[k0]})")

def experiment4_CRT_analysis():
    """
    Analyse CRT : si d = p*q et N_0(p) > 0 et N_0(q) > 0,
    est-ce que N_0(d) = 0 par "incompatibilite CRT" ?

    Pour k=7 : d = 23*83.
    Quels residus mod 23 et mod 83 sont atteints ?
    L'intersection est-elle vide ?
    """
    print("\n" + "=" * 70)
    print("EXPERIENCE 4 : Analyse CRT")
    print("=" * 70)

    for k in [5, 6, 7, 8]:
        S, d = compute_params(k)
        factors = factorint(d)

        if len(factors) < 2:
            print(f"\n  k={k}: d={d} est premier ou prime power, CRT sans objet")
            continue

        primes = sorted(factors.keys())
        n_total = comb(S - 3, k - 3)

        print(f"\n  k={k}, S={S}, d={d} = {' × '.join(str(p) for p in primes)}")

        if n_total > 500000:
            print(f"    Trop de compositions ({n_total})")
            continue

        prefix = (9 + 5 * pow(2, 1)) * pow(3, k-3)
        available = list(range(3, S))

        # Collecter tous les corrSum mod chaque premier
        residues_per_prime = {p: set() for p in primes}
        corrSums = []

        for positions in combinations(available, k - 3):
            suffix = sum(pow(3, k-1-j) * pow(2, q)
                        for j, q in zip(range(3, k), positions))
            cs = prefix + suffix
            corrSums.append(cs)
            for p in primes:
                residues_per_prime[p].add(cs % p)

        for p in primes:
            residues = sorted(residues_per_prime[p])
            has_zero = 0 in residues
            print(f"    mod {p}: {len(residues)}/{p} residus atteints, "
                  f"0 atteint = {has_zero}")
            if p <= 100:
                print(f"           residus : {residues}")

        # CRT : quelles paires (r_1, r_2) sont atteintes ?
        if len(primes) == 2:
            p1, p2 = primes[0], primes[1]
            pairs = set()
            for cs in corrSums:
                pairs.add((cs % p1, cs % p2))

            # Les paires contenant (0, 0) ?
            zero_pair = (0, 0)
            has_zero_pair = zero_pair in pairs
            print(f"    Paires CRT ({p1},{p2}) atteintes : {len(pairs)}/{p1*p2}")
            print(f"    Paire (0,0) atteinte : {has_zero_pair}")

            # Quelles paires avec r1=0 ?
            zero_first = [(r1, r2) for r1, r2 in pairs if r1 == 0]
            zero_second = [(r1, r2) for r1, r2 in pairs if r2 == 0]
            print(f"    Paires avec r1=0 : {len(zero_first)} -> r2 = {sorted(r2 for _, r2 in zero_first)}")
            print(f"    Paires avec r2=0 : {len(zero_second)} -> r1 = {sorted(r1 for r1, _ in zero_second)}")

def experiment5_residue_pattern():
    """
    Pour chaque premier p | d, analyser le PATTERN des residus atteints.

    Y a-t-il une sous-structure (sous-groupe, coset, etc.) ?
    """
    print("\n" + "=" * 70)
    print("EXPERIENCE 5 : Pattern des residus mod primes")
    print("=" * 70)

    for k in [7, 8, 9]:
        S, d = compute_params(k)
        factors = factorint(d)

        n_total = comb(S - 3, k - 3)
        if n_total > 500000:
            print(f"\n  k={k}: trop de compositions ({n_total})")
            continue

        prefix = (9 + 5 * pow(2, 1)) * pow(3, k-3)
        available = list(range(3, S))

        print(f"\n  k={k}, S={S}, d={d}")

        for prime in sorted(factors.keys()):
            if prime > 200:
                continue

            # Collect residues mod prime
            residues = []
            for positions in combinations(available, k - 3):
                suffix = sum(pow(3, k-1-j) * pow(2, q)
                            for j, q in zip(range(3, k), positions))
                cs = (prefix + suffix) % prime
                residues.append(cs)

            from collections import Counter
            dist = Counter(residues)
            n_residues = len(dist)

            print(f"    mod {prime}: {n_residues}/{prime} residus, 0 atteint = {0 in dist}")

            # Quels residus sont manquants ?
            missing = sorted(set(range(prime)) - set(dist.keys()))
            print(f"      Manquants ({len(missing)}): {missing[:20]}{'...' if len(missing) > 20 else ''}")

            # Distribution des occurrences
            counts = sorted(dist.values())
            if counts:
                print(f"      Occurrences: min={counts[0]}, max={counts[-1]}, "
                      f"mean={sum(counts)/len(counts):.1f}")

            # Le residu 0 est-il manquant ?
            if 0 in missing:
                print(f"      >>> 0 EST MANQUANT mod {prime} !")

                # Analyser pourquoi : est-ce que corrSum mod prime
                # a une structure specifique ?
                # corrSum = prefix + suffix
                # prefix mod prime
                pref_mod = prefix % prime
                print(f"      prefix mod {prime} = {pref_mod}")
                print(f"      Donc suffix doit etre ≡ {(-pref_mod) % prime} mod {prime}")

                suffix_residues = set()
                for positions in combinations(available, k - 3):
                    suffix = sum(pow(3, k-1-j) * pow(2, q)
                                for j, q in zip(range(3, k), positions))
                    suffix_residues.add(suffix % prime)

                suffix_target = (-pref_mod) % prime
                print(f"      suffix mod {prime}: {len(suffix_residues)}/{prime} residus")
                print(f"      target = {suffix_target}, atteint = {suffix_target in suffix_residues}")

def main():
    experiment1_prime_factors()
    experiment2_small_moduli()
    experiment3_universal_modulus()
    experiment4_CRT_analysis()
    experiment5_residue_pattern()

if __name__ == "__main__":
    main()
