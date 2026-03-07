#!/usr/bin/env python3
"""
SESSION 10f26k — COVERING SET ANALYSIS FOR CONVERGENT COMPOSITENESS
====================================================================
QUESTION : Pourquoi d(q_n) = 2^{p_n} - 3^{q_n} est TOUJOURS composite
           quand q_n est un denominateur de convergent de log_2(3) ?

APPROCHE : Pour chaque premier p, analyser quand p | d(q_n).
  p | d(q_n) <=> 2^{p_n} ≡ 3^{q_n} (mod p)

  Soit A = ord_p(2), B = ord_p(3).
  Condition : p_n ≡ ind_2(3^{q_n}) (mod A)
            = q_n * ind_2(3) (mod A)

  Donc p | d(q_n) <=> p_n ≡ q_n * g (mod A)
  ou g = ind_2(3) dans (Z/pZ)* (log discret de 3 base 2 mod p).

PLAN :
  K1. Pour p = 2,3,5,7,13,17,23,..., calculer A, B, g
  K2. Pour chaque convergent (p_n, q_n), verifier p_n mod A vs q_n*g mod A
  K3. Chercher un sous-ensemble S de premiers tel que pour TOUT n,
      au moins un p in S divise d(q_n)
  K4. Si S existe, verifier que le CF de log_2(3) force cette propriete
"""
import math
import sys

print("=" * 72, flush=True)
print("SESSION 10f26k — COVERING SET ANALYSIS", flush=True)
print("=" * 72, flush=True)

# === K1 : Calcul des parametres pour petits premiers ===
print("\n--- K1 : PARAMETRES MULTIPLICATIFS ---\n", flush=True)

def multiplicative_order(a, n):
    """Ordre de a modulo n."""
    if math.gcd(a, n) != 1:
        return None
    order = 1
    current = a % n
    while current != 1:
        current = (current * a) % n
        order += 1
        if order > n:
            return None
    return order

def discrete_log(base, target, mod, order):
    """Log discret de target en base base modulo mod. Baby-step giant-step."""
    if order is None:
        return None
    m = int(math.isqrt(order)) + 1
    # Baby steps: base^j mod mod for j = 0..m-1
    table = {}
    power = 1
    for j in range(m):
        table[power] = j
        power = (power * base) % mod
    # Giant step factor: base^{-m} mod mod
    factor = pow(base, mod - 1 - m, mod)  # base^{-m} = base^{p-1-m}
    gamma = target % mod
    for i in range(m):
        if gamma in table:
            result = i * m + table[gamma]
            if result < order:
                return result
        gamma = (gamma * factor) % mod
    return None

# Petits premiers (excluant 2 et 3 qui divisent 2^S ou 3^k)
test_primes = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
               53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
               101, 103, 107, 109, 113, 127, 131, 137, 139, 149,
               151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199,
               211, 223, 227, 229, 233, 239, 241, 251]

print(f"{'p':>5} {'ord_p(2)':>10} {'ord_p(3)':>10} {'g=ind_2(3)':>12} {'condition':>35}", flush=True)
print("-" * 78, flush=True)

prime_data = []
for p in test_primes:
    A = multiplicative_order(2, p)
    B = multiplicative_order(3, p)
    g = discrete_log(2, 3, p, A)

    # Si g n'existe pas (3 ∉ <2>), construire la table de correspondance
    # hit_set : ensemble des (p_n mod A, q_n mod B) tels que 2^{p_n} ≡ 3^{q_n} (mod p)
    hit_set = set()
    for a in range(A):
        val2 = pow(2, a, p)
        for b in range(B):
            val3 = pow(3, b, p)
            if val2 == val3:
                hit_set.add((a, b))

    if g is not None:
        cond = f"p_n ≡ {g}*q_n (mod {A})"
        g_str = str(g)
    else:
        cond = f"|hit_set|={len(hit_set)}, A={A}, B={B}"
        g_str = "N/A"
    print(f"{p:>5} {A:>10} {B:>10} {g_str:>12} {cond:>35}", flush=True)
    prime_data.append((p, A, B, g, hit_set))

# === K2 : Convergents de log_2(3) ===
print(f"\n\n--- K2 : DIVISIBILITE DES CONVERGENTS ---\n", flush=True)

# CF coefficients de log_2(3) — etendus
# log_2(3) = [1; 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55, 1, 4, 3, 1, 1,
#              15, 1, 9, 2, 5, 3, 32, 1, 2, 2, 5, 1, 1, 1, 6, 3, 2, ...]
cf = [1, 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55, 1, 4, 3, 1, 1,
      15, 1, 9, 2, 5, 3, 32, 1, 2, 2, 5, 1, 1, 1, 6, 3, 2]

# Calculer tous les convergents
convs = []
p_prev, p_curr = 1, cf[0]
q_prev, q_curr = 0, 1
convs.append((0, p_curr, q_curr, cf[0]))

for i in range(1, len(cf)):
    p_next = cf[i] * p_curr + p_prev
    q_next = cf[i] * q_curr + q_prev
    convs.append((i, p_next, q_next, cf[i]))
    p_prev, p_curr = p_curr, p_next
    q_prev, q_curr = q_curr, q_next

log2_3 = math.log2(3)

# Pour chaque convergent, verifier quels premiers divisent d(q_n)
print(f"{'n':>3} {'a_n':>4} {'p_n':>15} {'q_n':>15} {'delta':>12} {'diviseurs':>30}", flush=True)
print("-" * 85, flush=True)

convergent_divisors = []
for idx, pn, qn, an in convs:
    if qn < 4:
        continue
    S = pn  # Pour un convergent, S = p_n (le numerateur)
    # Verifier : S = ceil(q_n * log_2(3))
    S_check = math.ceil(qn * log2_3)
    # Note : pour les grands convergents, S_check peut differer de p_n
    # a cause de la precision flottante. Utiliser p_n directement.
    delta_approx = S - qn * log2_3

    divs = []
    for p, A, B, g, hit_set in prime_data:
        # p | d(q_n) <=> (p_n mod A, q_n mod B) in hit_set
        if (pn % A, qn % B) in hit_set:
            divs.append(p)

    div_str = ", ".join(str(d) for d in divs[:8])
    if len(divs) > 8:
        div_str += f", ... ({len(divs)} total)"

    convergent_divisors.append((idx, pn, qn, an, delta_approx, divs))
    print(f"{idx:>3} {an:>4} {pn:>15} {qn:>15} {delta_approx:>12.3e} {div_str:>30}", flush=True)

# === K3 : Analyse des patterns ===
print(f"\n\n--- K3 : ANALYSE DES PATTERNS DE DIVISIBILITE ---\n", flush=True)

# Pour chaque premier p, lister les indices n ou p | d(q_n)
print("Pour chaque premier, indices n des convergents divises :", flush=True)
print(f"(seulement convergents avec q_n >= 4)\n", flush=True)

useful_primes = []
for p, A, B, g, hit_set in prime_data:
    indices = []
    for idx, pn, qn, an, delta, divs in convergent_divisors:
        if p in divs:
            indices.append(idx)
    if indices:
        coverage = len(indices) / len(convergent_divisors) * 100
        print(f"  p={p:>3} (A={A:>4}): indices {indices}  ({coverage:.0f}%)", flush=True)
        useful_primes.append((p, A, B, g, hit_set, indices, coverage))

# === K4 : Recherche de covering set minimal ===
print(f"\n\n--- K4 : COVERING SET MINIMAL ---\n", flush=True)

# Greedy set cover
all_indices = set(range(len(convergent_divisors)))
covered = set()
covering_set = []

# Trier par couverture decroissante
useful_sorted = sorted(useful_primes, key=lambda x: len(x[5]), reverse=True)

while covered != all_indices and useful_sorted:
    best = None
    best_new = 0
    for p, A, B, g, hs, indices, cov in useful_sorted:
        new_covered = len(set(indices) - covered)
        if new_covered > best_new:
            best = (p, A, B, g, hs, indices, cov)
            best_new = new_covered
    if best is None or best_new == 0:
        break
    covering_set.append(best)
    covered.update(best[5])
    # Remove from list by prime value
    useful_sorted = [x for x in useful_sorted if x[0] != best[0]]

uncovered = all_indices - covered
print(f"Covering set (greedy) :", flush=True)
for p, A, B, g, hit_set, indices, cov in covering_set:
    print(f"  p={p:>3} couvre indices {indices}", flush=True)

if uncovered:
    print(f"\n  INDICES NON COUVERTS : {sorted(uncovered)}", flush=True)
    for uidx in sorted(uncovered):
        idx, pn, qn, an, delta, divs = convergent_divisors[uidx]
        print(f"    n={idx}: (p_n={pn}, q_n={qn}, a_n={an}) -> divs parmi [{', '.join(str(p) for p in test_primes)}]: {divs}", flush=True)
else:
    print(f"\n  TOUS LES CONVERGENTS COUVERTS par {len(covering_set)} premiers !", flush=True)

# === K5 : Structure modulaire du CF ===
print(f"\n\n--- K5 : RECURRENCE CF MODULO PETITS ENTIERS ---\n", flush=True)

# Pour les premiers du covering set, analyser la recurrence
# p_n = a_n * p_{n-1} + p_{n-2}, q_n = a_n * q_{n-1} + q_{n-2}
# Modulo A : p_n mod A = (a_n * p_{n-1} + p_{n-2}) mod A
# Etat : (p_{n-1} mod A, p_{n-2} mod A, q_{n-1} mod A, q_{n-2} mod A)

for p, A, B, g, hit_set, indices, cov in covering_set[:5]:
    print(f"\nPremier p={p}, A=ord_p(2)={A}, B=ord_p(3)={B}:", flush=True)
    print(f"  hit_set = {hit_set}", flush=True)
    print(f"  Recurrence : p_n = a_n*p_{{n-1}} + p_{{n-2}} (mod {A})", flush=True)
    print(f"               q_n = a_n*q_{{n-1}} + q_{{n-2}} (mod {B})", flush=True)
    print(f"  Etat (p_n mod {A}, q_n mod {B}) :", flush=True)

    for idx, pn, qn, an, delta, divs in convergent_divisors:
        pm = pn % A
        qm = qn % B
        hit = "HIT" if (pm, qm) in hit_set else "   "
        print(f"    n={idx:>2}: p_n≡{pm:>3} (mod {A}), q_n≡{qm:>3} (mod {B}) {hit}", flush=True)

# === K6 : Test etendu avec plus de CF ===
print(f"\n\n--- K6 : EXTENSION FRACTIONS CONTINUES ---\n", flush=True)

# Calculer plus de coefficients CF par l'algorithme de Stern-Brocot
# En utilisant mpmath pour la precision
try:
    from mpmath import mp, mpf, log, ceil, floor
    mp.dps = 200  # 200 digits

    log2_3_precise = log(3) / log(2)

    # Calculer CF de log_2(3) avec haute precision
    x = log2_3_precise
    cf_extended = []
    p_prev_m, p_curr_m = mpf(1), None
    q_prev_m, q_curr_m = mpf(0), None

    convs_extended = []
    for i in range(80):  # 80 coefficients
        a = int(floor(x))
        cf_extended.append(a)
        if i == 0:
            p_curr_m = mpf(a)
            q_curr_m = mpf(1)
        else:
            p_next_m = a * p_curr_m + p_prev_m
            q_next_m = a * q_curr_m + q_prev_m
            p_prev_m, p_curr_m = p_curr_m, p_next_m
            q_prev_m, q_curr_m = q_curr_m, q_next_m

        pn_int = int(p_curr_m)
        qn_int = int(q_curr_m)
        convs_extended.append((i, pn_int, qn_int, a))

        frac = x - a
        if frac < mpf(10) ** (-150):
            break
        x = 1 / frac

    print(f"CF etendu ({len(cf_extended)} termes) :", flush=True)
    print(f"  [{', '.join(str(a) for a in cf_extended)}]", flush=True)

    # Identifier les convergents dangereux (delta < 0.015)
    print(f"\nConvergents dangereux etendus (delta < 0.015, q >= 4) :", flush=True)

    dangerous_ext = []
    for idx, pn, qn, an in convs_extended:
        if qn < 4:
            continue
        # delta = p_n - q_n * log_2(3)
        # Pour la precision, utiliser mpmath
        delta_mp = mpf(pn) - qn * log2_3_precise
        delta_float = float(abs(delta_mp))

        if delta_float < 0.015:
            dangerous_ext.append((idx, pn, qn, an, delta_float))

    print(f"{'n':>3} {'a_n':>5} {'q_n':>20} {'delta':>15}", flush=True)
    for idx, pn, qn, an, delta in dangerous_ext:
        print(f"{idx:>3} {an:>5} {qn:>20} {delta:>15.3e}", flush=True)

    # Pour chaque convergent dangereux etendu, trouver un diviseur
    print(f"\nTest divisibilite etendu (premiers <= 251) :", flush=True)

    all_covered_ext = True
    for idx, pn, qn, an, delta in dangerous_ext:
        found = None
        for p, A, B, g, hit_set in prime_data:
            if (pn % A, qn % B) in hit_set:
                found = p
                break
        if found:
            print(f"  n={idx:>3}, q_n={qn:>20}: divise par {found}", flush=True)
        else:
            print(f"  n={idx:>3}, q_n={qn:>20}: PAS DE FACTEUR <= 251 !", flush=True)
            all_covered_ext = False
            # Chercher avec plus de premiers
            for p_big in range(257, 10000, 2):
                # Verifier si p_big est premier
                is_prime = True
                for f in range(2, int(p_big**0.5) + 1):
                    if p_big % f == 0:
                        is_prime = False
                        break
                if not is_prime:
                    continue
                A_big = multiplicative_order(2, p_big)
                g_big = discrete_log(2, 3, p_big, A_big)
                if g_big is not None and (pn % A_big) == (g_big * qn % A_big):
                    print(f"    -> Trouve : divise par {p_big} (A={A_big})", flush=True)
                    found = p_big
                    break
            if not found:
                # Test modulaire direct
                for p_test in [929, 15661, 8022437]:
                    d_mod = (pow(2, pn, p_test) - pow(3, qn, p_test)) % p_test
                    if d_mod == 0:
                        print(f"    -> Trouve (direct) : divise par {p_test}", flush=True)
                        found = p_test
                        break

    if all_covered_ext:
        print(f"\n  TOUS les convergents dangereux etendus sont divises par un premier <= 251", flush=True)

except ImportError:
    print("mpmath non disponible, utilisation precision standard.", flush=True)
    print("Installer : pip install mpmath", flush=True)

# === BILAN ===
print(f"\n{'='*72}", flush=True)
print(f"BILAN K1-K6", flush=True)
print(f"{'='*72}", flush=True)

if not uncovered:
    print(f"\nCOVERING SET TROUVE : {{{', '.join(str(p) for p, _, _, _, _, _, _ in covering_set)}}}", flush=True)
    print(f"  Ce set de {len(covering_set)} premiers couvre tous les {len(convergent_divisors)} convergents testes.", flush=True)
    print(f"\n  QUESTION OUVERTE : ce covering set couvre-t-il TOUS les convergents futurs ?", flush=True)
    print(f"  Pour repondre : analyser la recurrence CF modulo les periodes.", flush=True)
else:
    print(f"\n  {len(uncovered)} convergents non couverts par les {len(test_primes)} premiers testes.", flush=True)

print(f"\n{'='*72}", flush=True)
print(f"FIN SESSION 10f26k (partie 1)", flush=True)
print(f"{'='*72}", flush=True)
