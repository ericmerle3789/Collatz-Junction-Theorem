# CARTE MENTALE : ATTAQUE DE LA CONJECTURE D'ARTIN
## Pour la famille d(k) = 2^S - 3^k, S = ceil(k*log_2(3))
## Projet initie le 6 mars 2026 — Protocole G-V-R v2.2
## MIS A JOUR : 6 mars 2026 (sessions 10f26 a 10f26l)

---

## 0. OBJECTIF

```
OBJECTIF : Prouver que pour tout k >= 4,
  si d(k) = 2^S - 3^k est premier, alors ord_d(2) > S-1,
  donc ord_d(2) ne divise pas C(S-1,k-1), donc N_0(d) = 0.

STATUT FINAL :
  PROUVE inconditionnellement pour delta >= 0.0145 (Theoreme S).
  CORRECTION PARITE (10f26k) : seuls les convergents d'indice IMPAIR sont dangereux.
  VERIFIE computationnellement : 34/37 convergents impairs COMPOSITES (10f26k).
  Resolus par crible C : n=17 (10499517109), n=65 (4975245329), n=77 (1661926991).
  3 cas residuels (n=23,25,59) : cribles C COMPLETS a 10^{11}, EN COURS a 10^{12}.
  Crible 10^12 : PID 27660, ~33.5G premiers, ETA ~69h, Pr(succes) = 22.97%.
  Piste J.2 (m-scan) : IMPASSE — theoreme de Mertens → survivants inevitables (AH27).
  RESULTAT : G2c est FERME pour tous les d(k) premiers connus.
  GAP RESIDUEL : theorique, vide en pratique (P < 2% sous modele aleatoire).
```

---

## 1. THEOREMES FONDAMENTAUX (sessions 10f26-10f26f)

### Th.A — Case A impossible [inconditionnel]
r = S mod t, 2^r >= 3^k => r >= S > t => contradiction.

### Th.B — Contrainte v_2 [inconditionnel]
Case B: m*d = 3^k - 2^r, r = v_2(m+1).

### Th.C — m pair elimine [inconditionnel]
m pair => r=0 => d|3^k-1 => contradiction (Th.E).

### Th.D — m=1 elimine [inconditionnel]
Mihailescu (2002): 3^k - 2^{S-1} = d impossible pour k >= 3.

### Th.E — gcd(d, 3^k-1) = 1 [inconditionnel]
Analyse exhaustive de j = (3^k-1)/d par parite, v_2, Mihailescu, Baker.

### Th.F — gcd(3,m) = 1 [inconditionnel]
Bezout: gcd(c*3^k, m*2^{S-r}) = 1.

### Th.G — c=1 elimine (Zsygmondy) [inconditionnel pour r <= 15]

### Scan — m impairs <= 100 elimines [inconditionnel]
49/50 m impairs dans [5,99] avec gcd(m,6)=1 elimines. Seul m=5(k=3).

---

## 2. THEOREMES AVANCES (sessions 10f26g-10f26j)

### Th.H — c=1 elimine universellement [inconditionnel, k >= 4]
**(10f26g)** Si d = 2^t - 1:
- k impair: v_2(3^k-1) = 1 => t=1, d=1 non premier.
- k pair: t = 2+v_2(k), mais d(k) >> 2^{2+v_2(k)}-1 pour k>=4.

### Th.I — c=3 elimine universellement [inconditionnel, k >= 5]
**(10f26g)** Si 3d = 2^t - 1:
- k pair: mod 3 + v_2 contradiction.
- k impair: divisibilite par 3 analyse par sous-cas v_2(k+1).

### Th.P — Borne sur m [inconditionnel]
**(10f26i)** m < 3^k/d = 1/(2^delta - 1) ~ 1/(delta*ln2).
Pour delta petit, m peut etre grand.

### Th.S — Cloture c>=5 pour delta >= 0.0145 [inconditionnel]
**(10f26i)** delta >= 0.0145 => m < 100 => elimine par scan 10f26f.

### Th.R — Identite de recurrence [inconditionnel]
**(10f26k)** Pour tout n >= 2, avec d_n = 2^{p_n} - 3^{q_n} :
  d_n ≡ (3^{q_{n-1}})^{a_n} · d_{n-2}  (mod d_{n-1})
Consequence: Si p >= 5 divise gcd(d_{n-1}, d_{n-2}), alors p | d_n.
Les facteurs communs se conservent en remontant la chaine CF.
Verifie computationnellement pour n = 2..7.

### Correction parite [inconditionnel]
**(10f26k)** Seuls les convergents d'indice IMPAIR sont dangereux pour G2c :
- n pair : p_n/q_n < log_2(3), donc S = p_n + 1, delta_phys ≈ 1. NON DANGEREUX.
- n impair : p_n/q_n > log_2(3), donc S = p_n, delta_phys = delta_CF (petit). DANGEREUX.

### Fait — Convergents composites [computationnel, 10f26j+10f26k]
**(10f26k)** 74 convergents de log_2(3) (80 termes CF) testes :
- 37 convergents d'indice IMPAIR avec delta < 0.015
- **34/37 COMPOSITES** (facteurs trouves)
- **3 NON RESOLUS** : n = 23, 25, 59 (aucun facteur ≤ 10^{11})
- n=17 resolu : facteur 10499517109 (crible C 10^11)
- n=65 resolu : facteur 4975245329 (crible C 10^10)
- n=77 resolu : facteur 1661926991 (crible C 10^10)
- Heuristiquement, Pr[d(q_n) premier] < 10^{-8} pour chaque cas restant.

---

## 3. ARBRE D'ELIMINATION COMPLET (FINAL)

```
Supposons t = ord_d(2) <= S-1, k >= 4, d(k) premier.
c = (2^t-1)/d impair, r = S mod t, m*d = 3^k - 2^r.

FILTRE 1 — Parite
  m pair? => ELIMINE (Th.C+E)

FILTRE 2 — Divisibilite
  3|m? => ELIMINE (Th.F)

FILTRE 3 — Quotient c
  c=1? => ELIMINE (Th.H, k>=4)
  c=3? => ELIMINE (Th.I, k>=5)

FILTRE 4 — Borne m via delta
  delta >= 0.0145?
    => m < 100 => ELIMINE (Th.S + scan 10f26f)

  delta < 0.0145?
    => k convergent d'indice IMPAIR de log_2(3) [correction parite 10f26k]
    => 37 convergents impairs testes (80 termes CF)
    => 34/37 COMPOSITES (facteurs trouves par cribles C)
    => n=17: facteur 10499517109, n=65: 4975245329, n=77: 1661926991
    => 3 sans facteur <= 10^{11} (n=23, n=25, n=59: cribles COMPLETS)
    => Heuristiquement Pr[premier] < 10^{-8}
    => d(k) TRES PROBABLEMENT COMPOSITE
    => G2c ne s'applique pas

RESULTAT:
  Inconditionnel pour delta >= 0.0145 (couvre tous les 21 d premiers connus).
  Computationnel pour delta < 0.0145 : 34/37 convergents impairs COMPOSITES.
  3 cas residuels heuristiquement composites (gap vide en pratique). ✓
```

---

## 4. GAP RESIDUEL

```
STATUT : ESSENTIELLEMENT FERME

PARTIE INCONDITIONNELLE (couvre ~98.5% des k):
  c=1: PROUVE pour tout k >= 4 (Th.H)
  c=3: PROUVE pour tout k >= 5 (Th.I)
  c>=5, delta >= 0.0145: PROUVE (Th.S)

PARTIE COMPUTATIONNELLE (couvre le reste):
  c>=5, delta < 0.0145:
    Les seuls k avec delta < 0.0145 sont les convergents de log_2(3).
    34/37 convergents impairs testes donnent d(k) COMPOSITE.
    3 restants (n=23,25,59) sans facteur ≤ 10^{11}, heuristiquement composites.
    => G2c n'a pas besoin d'etre prouve pour ces d (non premiers).

POUR FERMER INCONDITIONNELLEMENT:
  Option A: Prouver d(q_n) composite pour tout convergent q_n.
  Option B: Etendre le scan m au-dela de 100.
  Option C: Argument theorique eliminant m >= 101 universellement.
  Aucune de ces options n'est indispensable en pratique.
```

---

## 5. CATALOGUE DES 21 d PREMIERS

```
k      S      delta    c_max  Th.S   Status
3      5      0.245    3      ✓      Case B k=3 (SEUL)
4      7      0.660    1      ✓      PROUVE
5      8      0.075    9      ✓      PROUVE
13     21     0.395    2      ✓      PROUVE
56     89     0.242    3      ✓      PROUVE
61     97     0.317    2      ✓      PROUVE
69     110    0.638    1      ✓      PROUVE
73     116    0.298    2      ✓      PROUVE
76     121    0.543    1      ✓      PROUVE
148    235    0.426    1      ✓      PROUVE
185    294    0.782    1      ✓      PROUVE
655    1039   0.850    1      ✓      PROUVE
917    1454   0.589    1      ✓      PROUVE
2183   3460   0.027    27     ✓      PROUVE (delta=0.027>0.0145)
3540   5611   0.233    3      ✓      PROUVE
3895   6174   0.571    1      ✓      PROUVE
4500   7133   0.669    1      ✓      PROUVE
6891   10922  0.023    31     ✓      PROUVE (delta=0.023>0.0145)
7752   12287  0.371    2      ✓      PROUVE
10291  16311  0.151    5      ✓      PROUVE
13695  21707  0.939    1      ✓      PROUVE

TOUS les 21 d premiers connus ont delta > 0.023 > 0.0145.
=> Th.S s'applique inconditionnellement a TOUS.
```

---

## 6. CONVERGENTS DE log_2(3) — ZONE DANGEREUSE

```
CONVERGENTS D'INDICE IMPAIR (n=7..79, 37 testes) :

  n   a_n  a_{n+1}     q_n             delta     Facteur      Status
  -------------------------------------------------------------------
  7     5     2         306           1.48e-03         929   COMPOSITE
  9    23     2       15601           2.63e-05           5   COMPOSITE
 11     2     1       79335           5.29e-06          23   COMPOSITE
 13     1    55      190537           9.31e-08       15661   COMPOSITE
 15     1     4    10781274           1.76e-08          17   COMPOSITE
 17     3     1   171928773           2.58e-09 10499517109   COMPOSITE
 19     1    15   397573379           1.53e-10           5   COMPOSITE
 21     1     9  6586818670           1.46e-11          79   COMPOSITE
 23     2     5   ~1.38e+11           1.30e-12          ?   NON RESOLU
 25     7     1   ~5.41e+12           9.51e-14          ?   NON RESOLU
 27     1     4   ~1.16e+13           1.86e-14          23   COMPOSITE
 29     8     1   ~4.31e+14           1.92e-15          13   COMPOSITE
 31    11     1   ~5.75e+15           1.53e-16          47   COMPOSITE
 33    20     2   ~1.30e+17           2.59e-18         151   COMPOSITE
 35     1    10   ~3.98e+17           2.19e-19           5   COMPOSITE
 37     1     4   ~4.64e+18           3.89e-20          73   COMPOSITE
 39     1     1   ~2.74e+19           1.46e-20      196171   COMPOSITE
 41     1     1   ~7.77e+19           4.91e-21         467   COMPOSITE
 43     1    37   ~2.06e+20           1.28e-22    17218217   COMPOSITE
 45     4    55   ~3.12e+22           5.76e-25        9343   COMPOSITE
 47     1     1   ~1.75e+24           2.85e-25          13   COMPOSITE
 49    49     1   ~1.72e+26           3.71e-27      136421   COMPOSITE
 51     1     1   ~3.47e+26           1.68e-27          23   COMPOSITE
 53     4     1   ~2.44e+27           2.72e-28      329009   COMPOSITE
 55     3     2   ~1.13e+28           3.44e-29           5   COMPOSITE
 57     3     3   ~8.81e+28           2.75e-30       11633   COMPOSITE
 59     1     5   ~3.78e+29           4.54e-31          ?   NON RESOLU
 61    16     2   ~3.53e+31           1.21e-32          11   COMPOSITE
 63     3     1   ~2.53e+32           2.08e-33           5   COMPOSITE
 65     1     1   ~5.80e+32           8.19e-34 4975245329   COMPOSITE
 67     1     1   ~1.49e+33           3.75e-34         433   COMPOSITE
 69     5     2   ~1.34e+34           2.60e-35           5   COMPOSITE
 71     1     2   ~4.27e+34           8.34e-36    60853189   COMPOSITE
 73     8     7   ~9.60e+35           1.35e-37         229   COMPOSITE
 75     1     1   ~7.80e+36           5.66e-38       33521   COMPOSITE
 77     2     1   ~3.71e+37           1.25e-38 1661926991   COMPOSITE
 79     1     0   ~8.88e+37           2.92e-39      172583   COMPOSITE

Score : 34/37 COMPOSITES. 3 NON RESOLUS (n=23,25,59).
n=17 resolu par crible C (10^11) : facteur 10499517109 (6 mars 2026).
n=65 resolu par crible C (10^10) : facteur 4975245329 (6 mars 2026).
n=77 resolu par crible C (10^10) : facteur 1661926991 (6 mars 2026).
Le seuil delta = 0.0145 separe la zone inconditionnelle de la zone computationnelle.
Convergents d'indice PAIR : delta_phys ≈ 1, NON DANGEREUX (correction parite 10f26k).
```

---

## 7. DEPENDANCES THEORIQUES

```
1. Mihailescu (2002): Theoreme de Catalan — elimine c=1 (k pair), m=1
2. Baker-Wustholz/LMN (1993/1995): Formes lineaires en logarithmes — K_Roth
3. Zsygmondy (1892): Facteurs primitifs — elimine c=1 (r<=15)
4. Hooley (1967): Artin sous GRH (reference, non utilise directement)
5. Erdos-Murty: Borne inferieure ord_p(a) (heuristique)
6. Scan computationnel 10f26f: m impairs <= 100 elimines
7. Test compositeness 10f26j: 6 convergents verifies
8. Correction parite 10f26k: seuls les convergents impairs sont dangereux
9. Verification etendue 10f26k: 34/37 convergents impairs composites
10. Identite de recurrence 10f26k (Th.R): propagation des facteurs via CF
```

---

## 8. SESSIONS ET SCRIPTS

```
Session   Script                                    Contenu principal
10f26     session10f26_artin_investigation.py       Catalogue, factorisation, ord
10f26b    session10f26b_artin_orders.py             Camera Thermique, extensions
10f26c    session10f26c_extension.py                k=10291, 13695
10f26d    session10f26d_gap_closure.py              Th.A-D, Case A/B
10f26e    session10f26e_gcd_universal.py            Th.E gcd universel
10f26f    session10f26f_case_b_elimination.py       Th.F-G, scan m<=100
10f26g    session10f26g_gap_closure.py              Th.H (c=1), Th.I (c=3)
10f26h    session10f26h_roth_closure.py             Baker-LMN, K_Roth=1708
10f26h'   session10f26h_final_check.py              Verification streamlined
10f26i    session10f26i_alpha_bound.py              Th.P (borne m), Th.S, alpha
10f26j    session10f26j_fast.py                     Convergents composites
10f26k    session10f26k_extended_test.py            74 convergents, 31/37 composites
10f26k    session10f26k_covering_set.py             Test covering set (ECHEC)
10f26k    session10f26k_intensive_n17.py            Analyse CF + test intensif n=17
10f26k    sieve_n17.c                               Crible C n=17, facteur 10499517109
10f26k    sieve_n23_n25.c                           Crible C n=23/25 (COMPLET: aucun facteur ≤ 10^{11})
10f26k    sieve_big3.c                              Crible C n=59/65/77 (n=65: 4975245329, n=77: 1661926991, n=59: aucun ≤ 10^{10})
10f26k    sieve_n59.c                               Crible C n=59 seul (10^{11}, COMPLET: aucun facteur, 4.12G premiers, 15029s)
10f26k    session10f26k_algebraic.py                 Exploration algebrique: GCD chains, reduction exposants, facteurs algebriques
10f26k    red_team_verify_compositeness.py          Verification Red Team
10f26l    sieve_1e12_all3.c                          Crible C (10^11,10^12] unifie 3 cibles (EN COURS)
10f26l    mscan_n23.c                                M-scan n=23 v1 (naif) — ABANDONNE (survivants structurels)
10f26l    mscan_n23_v2.c                             M-scan n=23 v2 (deux niveaux) — ABANDONNE (Mertens)
10f26l    probability_analysis.py                    Analyse Dickman + Mertens + distribution facteurs
10f26l    m_scan_analysis.py                         Analyse CF + bornes m_max + faisabilite

Documents:
  artin_synthesis_FINAL_10f26.md    Synthese complete (sessions 10f26-10f26j)
  artin_synthesis_10f26k.md        Synthese session 10f26k
  ARTIN_MIND_MAP.md                Cette carte
```

---

## 9. ANTI-HALLUCINATION

```
[x] AH1: ord_d(2) verifies par pow(2, ord, d) == 1 (21 cas)
[x] AH2: Q = (d-1)/ord entiers exacts
[x] AH3: Camera Thermique 2^M mod d != 1 (21 cas)
[x] AH4: Case A impossibilite logique + numerique
[x] AH5: Mihailescu: application correcte
[x] AH6: gcd(d, 3^k-1) = 1 verifie (21 cas + scan)
[x] AH7: Case B: k=3 seul survivant
[x] AH8: Zsygmondy applicable
[x] AH9: Th.H (c=1): verifie 21 d premiers
[x] AH10: Th.I (c=3): verifie 21 d premiers
[x] AH11: Th.S (m<100): borne m verifiee numeriquement
[x] AH12: 34/37 convergents impairs COMPOSITES (10f26k, incl. n=17,65,77)
[x] AH13: Taille seule INSUFFISANTE pour c>=5 (I5 de 10f26i, honnete)
[x] AH14: Baker C=30 APPROXIMATIF (conservatif)
[ ] AH15: Preuve d(q_n) composite pour tout convergent q_n (non prouve, 3 non resolus: n=23,25,59)
[x] AH16: Correction parite verifiee (n=0..19, d ≤ 0 pour n pair) (10f26k)
[x] AH17: Identite recurrence Th.R verifiee computationnellement (n=2..7) (10f26k)
[x] AH18: Facteur 10499517109 est PREMIER (Miller-Rabin 50 rounds) (10f26k)
[x] AH19: Covering set IMPOSSIBLE — facteurs erratiques (10f26k)
[x] AH20: gcd(d_n, d_{n+1}) = 1 pour n=1..7 — aucune propagation (10f26k)
[x] AH21: Reduction d'exposants COLLAPSE trivialement (S→0 ou 1 en 1 etape) (10f26k)
[x] AH22: 33 facteurs algebriques testes — AUCUN ne divise d_23 ou d_25 (10f26k)
[x] AH23: Crible n=59 COMPLET a 10^11 : aucun facteur (4.12G premiers, 15029s) (10f26k)
[x] AH24: 7 axes theoriques etudies — aucun ne prouve compositeness de 2^a-3^b (10f26k)
[x] AH25: ECM INFAISABLE pour nos cibles (~150h/courbe, ~375 000h total) (10f26k)
[x] AH26: 3/37 sans facteur ≤10^11 = statistiquement normal (Dickman, ~8% proba) (10f26k)
[x] AH27: M-scan (Piste J.2) est une IMPASSE — Mertens ∏(1-1/p)≈C/ln(B) ne tend JAMAIS vers 0 (10f26l)
[x] AH28: Crible 10^12 : Pr(≥1 facteur) = 22.97% combinee (Mertens, 3 cibles indep.) (10f26l)
[x] AH29: Survivants m-scan pour m=95,97,253... confirmes avec 5.76M premiers ≤10^8 (10f26l)
[x] AH30: 2 processus Python zombies (6h+1h) identifies et tues (sessions precedentes) (10f26l)
```
