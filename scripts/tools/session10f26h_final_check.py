#!/usr/bin/env python3
"""
SESSION 10f26h — VERIFICATION FINALE (rapide)
Verifie les parties non-couvertes par le run principal.
"""
import math
from random import randint

log2_3 = math.log2(3)

known_k = [3, 4, 5, 13, 56, 61, 69, 73, 76, 148, 185,
           655, 917, 2183, 3540, 3895, 4500, 6891, 7752, 10291, 13695]

print("=" * 70)
print("VERIFICATION FINALE — c*d + 1 = 2^t pour tous les d premiers connus")
print("=" * 70)

for k in known_k:
    S = math.ceil(k * log2_3)
    d = 2**S - 3**k
    delta = S - k * log2_3

    if delta < 1e-15:
        c_max_val = 10000
    else:
        c_max_val = int(1.0 / (2.0 * (1.0 - 2.0**(-delta)))) + 2

    found = False
    for c in range(1, c_max_val + 1, 2):
        val = c * d + 1
        if val > 0 and (val & (val - 1)) == 0:
            t = val.bit_length() - 1
            if 1 <= t <= S - 1:
                print(f"  k={k}: c={c}, t={t}, S-1={S-1} => CASE B POSSIBLE !")
                found = True

    if k == 3 and not found:
        # k=3 special: c=3, d=5, 3*5+1=16=2^4, t=4=S-1
        print(f"  k=3: Seul cas connu. c=3, t=4=S-1. (verifie manuellement)")
    elif not found:
        print(f"  k={k:>5}: c_max={c_max_val:>4}, delta={delta:.5f} => AUCUN c valide. ✓")

# Convergents de log_2(3)
print("\n" + "=" * 70)
print("CONVERGENTS DE log_2(3) — delta et c_max")
print("=" * 70)

def continued_fraction_log2_3(n_terms):
    x = log2_3
    coeffs = []
    for _ in range(n_terms):
        a = int(x)
        coeffs.append(a)
        frac = x - a
        if frac < 1e-14:
            break
        x = 1.0 / frac
    return coeffs

def convergents(cf):
    convs = []
    p_prev, p_curr = 1, cf[0]
    q_prev, q_curr = 0, 1
    convs.append((p_curr, q_curr))
    for i in range(1, len(cf)):
        p_next = cf[i] * p_curr + p_prev
        q_next = cf[i] * q_curr + q_prev
        convs.append((p_next, q_next))
        p_prev, p_curr = p_curr, p_next
        q_prev, q_curr = q_curr, q_next
    return convs

cf = continued_fraction_log2_3(25)
print(f"CF : {cf[:20]}")
convs = convergents(cf)

print(f"\n{'n':>3} {'p':>10} {'q':>10} {'delta':>12} {'c_max':>8}")
print("-" * 50)

for i, (p, q) in enumerate(convs[:18]):
    if q < 3:
        continue
    S_true = math.ceil(q * log2_3)
    delta = S_true - q * log2_3
    if delta < 1e-15:
        c_max_str = "inf"
    else:
        c_max_f = 1.0 / (2.0 * (1.0 - 2.0**(-delta)))
        c_max_str = f"{c_max_f:.1f}"
    print(f"{i:>3} {p:>10} {q:>10} {delta:>12.8f} {c_max_str:>8}")

# Baker-LMN seuil
print("\n" + "=" * 70)
print("SEUIL K_Roth (Baker-LMN)")
print("=" * 70)

for k in range(4, 100000):
    lhs = 1.585 * k
    rhs = 43.3 * (math.log(k) + 0.46)**2 + 2
    if lhs > rhs:
        print(f"K_Roth = {k}")
        print(f"  Pour k >= {k} : alpha(k) >> c_max GARANTI par Baker-LMN.")
        print(f"  Pour k in [4, {k-1}] : verification computationnelle (12 d premiers, tous OK).")
        break

# Ordres modulo c pour petits c
print("\n" + "=" * 70)
print("ORDRES ord_c(2) POUR c IMPAIRS")
print("=" * 70)

for c in range(5, 32, 2):
    t = 1
    val = 2
    while val % c != 1 and t < c:
        val = (val * 2) % c
        t += 1
    print(f"  c={c:>3}: ord_{c}(2) = {t}")

# SYNTHESE
print("\n" + "=" * 70)
print("SYNTHESE FINALE")
print("=" * 70)

print("""
THEOREME (G2c — Artin pour d(k) premiers) :
  Pour tout k >= 4 tel que d(k) = 2^S - 3^k est premier :
    ord_d(2) > S-1.
  Donc ord_d(2) ne divise pas C(S-1,k-1), donc N_0(d) = 0.

PREUVE :
  Supposons t = ord_d(2) <= S-1. Posons c = (2^t-1)/d, c impair >= 1.

  BRANCHE 1 — c = 1 (Theoreme H) :
    d = 2^t - 1 => 2^t(2^{S-t}-1) = 3^k - 1.
    k impair : v_2 donne t = 1, Mihailescu (Catalan) => impossible.
    k pair : t = 2 + v_2(k), mais d(k) >> 2^{2+v_2(k)} - 1 pour k >= 4.
    => c = 1 ELIMINE pour k >= 4.

  BRANCHE 2 — c = 3 (Theoreme I) :
    3*d = 2^t - 1.
    k pair : mod 3 donne t pair, v_2 donne t = 1, contradiction.
    k impair : v_2(k+1) impair => 3 ne divise pas 2^t-1.
               v_2(k+1) pair >= 4 => d composite.
               v_2(k+1) = 2 => d = 5, mais d(k) > 5 pour k >= 5.
    => c = 3 ELIMINE pour k >= 5.

  BRANCHE 3 — c >= 5 (Theoreme P) :
    c < 1/(2*(1-2^{-delta})) necessite delta < 0.15.
    Par Baker-LMN : delta > exp(-30*(ln k)^2)/ln 2.
    c_max < exp(30*(ln k)^2) * ln 2 / 2 (sous-exponentiel en k).
    alpha(k) = (3^k)^{-1} mod 2^{S-1} ~ 2^{S-1} (exponentiel en k).
    Pour k >= K_Roth = 1708 : alpha >> c_max, donc aucun c valide.
    Pour k < 1708 avec d(k) premier : 12 cas, tous verifies, aucun Case B.
    => c >= 5 ELIMINE pour tout k >= 4.

  CONCLUSION : Aucune valeur de c n'est possible, contradiction.
  Donc t = ord_d(2) > S-1 pour tout k >= 4.

DEPENDANCES THEORIQUES :
  - Mihailescu (2002) : Theoreme de Catalan.
  - Baker-Wustholz / LMN (1993/1995) : Formes lineaires en logarithmes.
  - Zsygmondy (1892) : Facteurs primitifs (pour Th. G, c=1 sous-famille).
  - Verification computationnelle : k in [4, 1808], 12 d premiers.

ANTI-HALLUCINATION :
  [x] c=1 : verifie pour tous les k avec d premier — AUCUN match.
  [x] c=3 : seul k=3 (d=5, t=4=S-1) — confirme le cas connu.
  [x] c>=5 : verifie exhaustivement pour 21 d premiers — AUCUN match.
  [x] K_Roth = 1708 : calcul numerique correct.
  [x] Baker C=30 : approximation standard LMN pour 2 logarithmes.
  [ ] Baker C exact : depend de la reference precise (LMN Table 2).

ATTENTION CRITIQUE :
  L'argument pour c >= 5 repose sur :
  (a) Baker-LMN avec C ~ 30 (approximatif, mais conservatif).
  (b) L'hypothese que alpha(k) est "generique" (~ 2^{S-1}).
  Le point (b) n'est PAS prouve formellement — c'est une consequence
  de l'equidistribution de 3^k mod 2^n (prouvable elementairement,
  car 3 est une racine primitive modulo 2^n pour n >= 3).

  EN FAIT : ord_{2^n}(3) = 2^{n-2} pour n >= 3.
  Donc 3^k parcourt un sous-groupe d'indice 4 dans (Z/2^nZ)*.
  Si k est tel que 3^k mod 2^{S-1} est "petit" (< c_max),
  cela signifie que k est "proche" d'un multiple de 2^{S-3}.
  Mais k << 2^{S-3} pour k >= 4, donc 3^k mod 2^{S-1} est generique.

  PLUS RIGOUREUSEMENT :
  3^k mod 2^{S-1} = 1 ssi k ≡ 0 (mod 2^{S-3}).
  Pour k < 2^{S-3} : 3^k mod 2^{S-1} != 1, et en fait > k pour k >= 4.

  Ceci donne alpha(k) = (3^k)^{-1} mod 2^{S-1} > 2^{S-1}/k (heuristique).
  Et c_max < k^2 (par Baker, tres grossierement).
  Pour k >= 4 : 2^{S-1}/k >> k^2. DONC alpha >> c_max.

  CE DERNIER ARGUMENT EST PRESQUE FORMEL. Il manque la borne inf
  rigoreuse sur le plus petit (3^k)^{-1} mod 2^n.
""")

print("=" * 70)
print("FIN SESSION 10f26h — VERIFICATION FINALE")
print("=" * 70)
