# CARTE MENTALE : PREUVE DE N₀(d) = 0 UNIVERSEL
## Graphe de dependances complet — Mis a jour 4 mars 2026 (session 10e4 — Protocole v2.2 + Architecture 3 cas + σ̃=0 prouve)

---

## 1. OBJETS MATHEMATIQUES FONDAMENTAUX

### 1.1 Parametres
```
k ∈ N, k >= 3     (nombre de pas impairs dans un cycle potentiel)
S = ceil(k*log_2(3))    (hauteur = nombre total de divisions par 2)
theta = S - k*log_2(3)   (residu diophantien, theta in [0,1))
alpha = (k-1)/(S-1)   (ratio -> 1/log_2(3) ~ 0.631 quand k -> inf)
gamma = 1 - h(1/log_2(3)) = 0.05004... (deficit entropique)
```

### 1.2 Objets centraux
```
d(k) = 2^S - 3^k                    MODULE CRISTALLIN
C(k) = binom(S-1, k-1)               NOMBRE DE COMPOSITIONS
Comp(S,k) = {A : 0=A_0<A_1<...<A_{k-1}<S}  ESPACE DES COMPOSITIONS
corrSum(A) = 3^{k-1} + Sum_{j=1}^{k-1} 3^{k-1-j}*2^{A_j}   SOMME CORRECTIVE
Ev_d : Comp(S,k) -> Z/dZ             CARTE D'EVALUATION
N_0(d) = |Ev_d^{-1}(0)|              CIBLE : prouver = 0
```

### 1.3 Objets analytiques
```
T_d(t) = Sum_A e(t*corrSum(A)/d)       SOMME EXPONENTIELLE (Fourier)
R(d) = (1/d)*Sum_{t>=1} T_d(t)         TERME D'ERREUR
N_0(d) = C/d + R(d)                   FORMULE D'INVERSION
T(t) = Sum_A e(t*corrSum(A)/p)         SOMME EXP mod premier p
M(chi) = Sum_{A, corrSum not 0} chi(corrSum)   SOMME MULTIPLICATIVE (Mellin)
```

### 1.4 Objets de l'automate (NOUVEAU)
```
AUTOMATE DE HORNER mod d :
  Etats : Z/dZ = {0, 1, ..., d-1}
  Etat initial : c_0 = 1 (= 2^{A_0} = 2^0 = 1)
  Transition : c -> (3c + 2^p) mod d  pour position p
  Contrainte : positions strictement croissantes p_1 < p_2 < ... < p_{k-1}
  Borne : p in {1, 2, ..., S-1}
  N_0(d) = nombre de chemins de longueur k-1 de l'etat 1 a l'etat 0

COUCHES (layers) :
  L_0 = {(1, 0)}          (etat 1, position initiale 0)
  L_j = {(c_j, p_j)} ou c_j = (3*c_{j-1} + 2^{p_j}) mod d, p_j > p_{j-1}
  |L_{k-1}| = C(k) = binom(S-1, k-1)
  N_0(d) = |{(c, p) in L_{k-1} : c = 0}|
```

### 1.5 Identites cles
```
2^S = 3^k (mod d)                    CONGRUENCE FONDAMENTALE
corrSum(A) = 1 (mod 2)               TOUJOURS IMPAIR  [Lemme 1]
corrSum(A) not 0 (mod 3)             JAMAIS DIVISIBLE PAR 3  [Lemme 2]
corrSum(A) in {1,3} (mod 4)          PARMI 1 ET 3 MOD 4  [Lemme 3 — NOUVEAU]
n_0 = corrSum(A)/d                     ELEMENT MINIMAL DU CYCLE
Sum_{t=0}^{p-1} |T(t)|^2 = p*Sum_r N_r^2  PARSEVAL
Sum_{t=1}^{p-1} T(t) = p*N_0(p) - C    IDENTITE DE COMPTAGE
```

---

## 2. GRAPHE DE DEPENDANCES : CE QUI IMPLIQUE QUOI

```
                    CONJECTURE DE COLLATZ (pas de cycle non trivial)
                              |
                    N_0(d) = 0 pour TOUT k >= 3
                    /                        \
                   /                          \
     k <= 68 : Simons-de Weger          k >= 18 : argument entropique
     (externe, publie 2005)                     |
                                    C(k) < d(k) [Thm Nonsurjectivity]
                                        |                |
                                  gamma > 0 [Prop 3.2]    Approx dioph log_2(3)
                                        |
                                  h(1/log_2(3)) < 1 [calcul]

     ZONE DE JONCTION : k in [18, 68]
     Les DEUX arguments couvrent, MAIS :
     - Simons-de Weger ne dit rien sur H(k) directement
     - C < d dit "au moins un residu manque" mais pas "0 manque"
     ==> LE GAP = prouver que 0 in residus manquants
```

### NOUVEAU : Graphe de la strategie de preuve
```
     N_0(d) = 0 pour TOUT k >= 3
              |
     ---------+---------------------------
     |                                    |
     k petit (3..17)               k grand (>= 18)
     |                                    |
     Mecanisme de blocage         C < d (deficit entropique)
     a 3 composantes :                    +
     |                             Mecanisme de blocage
     +-- (A) Gap algebrique :      RENFORCE le deficit
     |   ord_d(2) > S-1
     |
     +-- (B) Contrainte d'ordre :
     |   p_1 < p_2 < ... < p_{k-1}
     |
     +-- (C) Borne superieure :
         p <= S-1

     INTERACTION : (A)+(B)+(C) filtrent TOUS les chemins vers 0
                   Pour k=5 : 51% par (B), 40% par (A), 9% par transit
                   Pour k>=4 : gap (A) = 40%-100% des blocages
```

---

## 3. BARRIERES IDENTIFIEES

### 3.1 Barriere racine carree (Proposition 5.8 du preprint)
```
Methode spectrale (Fourier, Parseval, moments) :
  |R(d)| <= sqrt(C)
  Or sqrt(C) >> 1 pour tout k >= 3
  ==> Impossible de prouver N_0(d) = 0 par Fourier generique
```

### 3.2 Barriere des primes individuels (Phase A1)
```
Pour k >= 18 : N_0(p) > 0 pour TOUT premier p | d(k)
  ==> Impossible de prouver N_0(d) = 0 en montrant N_0(p) = 0
  ==> DOIT exploiter la structure COMPOSITE de d
RENFORCE (session 3) : Pour k >= 6 composite, TOUS p|d ont N_0(p) > 0
  ==> Echec CRT naif pour TOUT k >= 6
```

### 3.3 Barriere C/d > 1 (k = 3, 5, 17)
```
Pour k=5 : C/d = 2.69 > 1, pourtant N_0(d) = 0
  ==> L'argument probabiliste E[N_0] = C/d < 1 ==> N_0 = 0 ECHOUE
  ==> La preuve DOIT etre STRUCTURELLE, pas probabiliste
```

### 3.4 Vacuite de Theorem Q
```
Hypothese Q : |Sum T(t)| <= 0.041*C
Pour p > 1.041*C : Q ==> N_0(p) = 0 ==> |Sum T(t)| = C >> 0.041*C
  ==> Q est AUTO-CONTRADICTOIRE pour les grands premiers
  ==> Theorem Q = information ZERO
```

### 3.5 NOUVEAU : Barriere des invariants universels
```
RESULTAT (Front 4, session 3) :
  Recherche systematique mod m pour m = 2..50, k = 3..17
  INVARIANTS UNIVERSELS TROUVES :
    mod 2 : residus interdits = {0}          (corrSum impair)
    mod 3 : residus interdits = {0}          (corrSum non divisible par 3)
    mod 4 : residus interdits = {0, 2}       (corrSum in {1,3} mod 4)
    mod 6 : residus interdits = {0,2,3,4}    (consequence de mod 2 et mod 3)
    mod 9 : residus interdits = {0,3,6}      (= multiples de 3, consequence de mod 3)
  TOUS se reduisent a la combinaison de : impair + non divisible par 3

  ==> PAS D'INVARIANT UNIVERSEL AU-DELA DE PARITE + MOD 3
  ==> Le blocage de 0 mod d est SPECIFIQUE a d, pas "universel"
  ==> La preuve DOIT exploiter la structure de d = 2^S - 3^k
```

---

## 4. DONNEES NUMERIQUES CLES

### 4.1 Table N_0(d) verifiee (k = 3..21)
```
k    C              d                C/d      N_0(d)   ANOMALIE
3    6              5                1.20     0        C/d > 1 !
4    20             47               0.43     0
5    35             13               2.69     0        C/d >> 1 !!
6    126            295              0.43     0
7    462            1,909            0.24     0
8    792            1,631            0.49     0
9    3,003          13,085           0.23     0
10   5,005          6,487            0.77     0
11   19,448         84,997           0.23     0
12   75,582         517,135          0.15     0
13   125,970        502,829          0.25     0
14   497,420        3,605,639        0.14     0
15   817,190        2,428,309        0.34     0
16   3,268,760      24,062,143       0.14     0
17   5,311,735      5,077,565        1.05     0        C/d > 1 !
18   21,474,180     149,450,423      0.14     0
19   86,493,225     985,222,181      0.09     0
20   141,120,525    808,182,895      0.17     0
21   573,166,440    6,719,515,981    0.09     0
```

### 4.2 NOUVEAU : Analyse detaillee k=5 (d=13, S=8)
```
35 compositions, corrSum mod 13 :
  Distribution : {1:3, 2:3, 3:3, 4:3, 5:3, 6:3, 7:2, 8:3, 9:3, 11:3, 12:3}
  Residus atteints : {1,2,3,4,5,6,7,8,9,11,12} = 12/13
  SEUL ABSENT : 0
  Residus dans ⟨3⟩ = {1,3,9} : 9 chemins (9/35 = 25.7%)
  Residus dans 2*⟨3⟩ = {2,6,5} : 9 chemins
  Residus dans 4*⟨3⟩ = {4,12,10} : SEULEMENT 5 chemins (10 manque!)
  Residus dans 8*⟨3⟩ = {8,11,7} : 8 chemins

Structure algebrique dans Z/13Z* :
  ord_13(2) = 12 (racine primitive!)
  ord_13(3) = 3
  h = 2/3 mod 13 = 2 * 9 = 5 mod 13, ord(h) = 4
  ⟨3⟩ = {1, 3, 9} sous-groupe d'ordre 3
  Quotient Z/13Z* / ⟨3⟩ = 4 classes laterales
```

### 4.3 NOUVEAU : Mecanisme de blocage quantifie
```
k    d      ord_d(2)  S-1  |avail|  |gap|   gap%    Raisons de blocage
3    5      4         4    4        0       0.0%    75% position, 25% zero-transit
4    47     23        5    5        41      89.1%   principalement gap
5    13     12        7    7        5       41.7%   51% position, 40% gap, 9% zero
6    295    36        9    9        285     97.3%   dominance gap
7    1909   954       10   10       1898    99.5%   dominance gap
8    1631   815       12   12       1618    99.2%   dominance gap
...
(Pour k >= 4, gap% > 40%, rapidement > 90%)

Formule : gap% ~ 1 - (S-1)/(ord_d(2))  quand ord_d(2) >> S-1
Le cas k=3 est SPECIAL : ord_5(2) = 4 = S-1, donc ZERO gap algebrique.
  Le blocage est ENTIEREMENT dû a la contrainte d'ordre.
```

### 4.4 NOUVEAU : Test de la position fantome (k=3..15)
```
THEOREME CONJECTURAL : Pour k >= 4, le residu 2^S mod d = 3^k mod d
  n'est DANS aucune position legale {2^q : q=1,...,S-1} mod d.
  Equivalence : ord_d(2) > S-1

  Verifie pour k=4..15. Le cas k=3 est SPECIAL (ord_5(2) = 4 = S-1).

L'etat fantome -3^{k-1} mod d est atteignable pour k = 3,5,6,7,8,10
  mais PAS pour k = 4,9,11,12,13,14,15.
  ==> L'hypothese naive (etat fantome toujours atteignable) est FAUSSE.
  ==> MAIS le resultat plus fort (residu fantome inaccessible) est VRAI.

DICHOTOMIE :
  k = 3 : Gap zero, blocage par contrainte d'ordre uniquement
  k >= 4 : Gap > 0, blocage principalement algebrique
```

### 4.5 NOUVEAU : Echec CRT pour d compose
```
Pour k >= 6 avec d compose :
  TOUS les facteurs premiers p de d verifient N_0(p) > 0
  Pourtant N_0(d) = 0

Exemple k=6 : d = 295 = 5 * 59
  N_0(5) > 0, N_0(59) > 0, mais N_0(295) = 0
  ==> Les congruences mod 5 et mod 59 sont CORRELEES
  ==> Le CRT naif N_0(d) ~ C * prod(N_0(p_i)/C) est FAUX

==> La preuve doit capturer les CORRELATIONS inter-primes
    induites par la structure specifique d = 2^S - 3^k
```

---

## 5. FRONTS D'ATTAQUE (classes par priorite, avec STATUT)

### FRONT 1 : CAS k=5 (d=13) — ★★★ PARTIELLEMENT RESOLU
```
STATUT : ANALYSE COMPLETE, MECANISME IDENTIFIE
RESULTATS :
  - 35 corrSum mod 13 enumeres : seul 0 absent
  - Automate de Horner corrige : c_0 = 1, transitions avec ordre croissant
  - Mecanisme de blocage a 3 composantes identifie et quantifie
  - Structure algebrique : ord_13(2) = 12, ord_13(3) = 3
MANQUE : Formalisation en theoreme generalisable a tout k
OUTILS CREES : front1_k5_analysis.py, front1_corrected_deep.py,
               front1_blocking_mechanism.py
```

### FRONT 2 : AUTOMATE DE HORNER — ★★★ COMPLETE (session 4)
```
STATUT : ANALYSE COMPLETE, DECOUVERTES MAJEURES
OUTILS CREES : front2_spectral_analysis.py, theorem82_ord_proof.py

RESULTATS CLES :
  1. Matrice de permutation M_p et recurrence f_j(q) = f_j(q-1) + M_q*f_{j-1}(q-1)
     N_0(d) = f_{k-1}(S-1)[0,1] verifie = 0 pour k=3..8.

  2. DECOUVERTE MAJEURE : L'etat 0 n'est PAS universellement inaccessible.
     Il est accessible depuis presque tous les etats initiaux SAUF c_0 = 1.
     Pour k=5 : 0 accessible depuis 12/13 etats, seul {1} exclu.
     => La preuve DOIT exploiter la specificite de c_0 = 1.

  3. Decomposition de Fourier : les orbites de <3> dans Z/dZ
     decomposent l'action de T = Sum M_p en blocs.
     Eigenvalue triviale = S-1, non-triviales ~ sqrt(S-1).

  4. f_{k-1}(S-1) a rang PLEIN (d pour tout k teste).
     Le blocage de 0 n'est PAS un phenomene de rang.

  5. Identite de Fourier : Sum_{t>=1} F(t) = -C (annulation exacte).
```

### FRONT 3 : INDEPENDANCE CRT — ★★☆ ECLAIRE PAR LES DONNEES
```
STATUT : ECLAIRE mais pas formellement attaque
RESULTAT NEGATIF : CRT naif echoue pour k >= 6
  (tous les N_0(p) > 0 pour p | d)
PISTE : Les correlations viennent de la MEME structure (d = 2^S - 3^k)
  qui contraint simultanement tous les residus mod p_i.
  Formaliser : comment d = 2^S - 3^k induit des correlations CRT ?
```

### FRONT 4 : RESIDUS INTERDITS — ★★☆ CLOS (resultat negatif)
```
STATUT : EXPLORE, RESULTAT NEGATIF DEFINITIF
RESULTAT : Aucun invariant universel au-dela de mod 2 et mod 3.
  corrSum in {1,3} mod 4 est le seul nouveau lemme, mais c'est
  une consequence de la parite (mod 4 = raffinement de mod 2).
  mod 9, mod 12, etc. se reduisent tous a mod 2 + mod 3.
==> FRONT FERME. Pas de "chaine de congruences magique".
LEMME NOUVEAU : corrSum(A) in {1, 3} mod 4 pour tout k >= 3.
  Preuve : corrSum = 3^{k-1} + ... + 2^{A_1} + termes pairs.
           Seuls A_0=0 (donne 3^{k-1}) et A_1 (donne 2^{A_1})
           contribuent mod 4. 3^{k-1} in {1,3} mod 4, 2^{A_1} in {0,2} mod 4.
           Total : {1,3} mod 4.
OUTILS CREES : front4_invariants.py
```

### FRONT 5 : DOUBLE PEELING — ★★★ RESULTAT EXTRAORDINAIRE (session 5)
```
STATUT : PROUVE NUMERIQUEMENT POUR k=3..14
OUTILS CREES : why_c0_equals_1.py, double_peeling_proof.py

METHODE :
  Forward  : depuis c_0=1, couches (etat, position_max) pas par pas
  Backward : depuis c_{k-1}=0, couches (etat, position_min) en arriere
             transition inverse : c_prev = (c_next - 2^p) * 3^{-1} mod d
  Rendez-vous : pour chaque etape j, tester si
    il existe un etat s et des positions (p_fwd, p_bwd) avec p_fwd < p_bwd.

RESULTAT : Pour TOUT k de 3 a 14, ZERO paires compatibles !
  Le double peeling PROUVE N_0(d) = 0 pour ces k.

  k    d          S    C          C/d      compatible  PROUVE?
  3    5          5    6          1.200    0           OUI
  4    47         7    20         0.426    0           OUI
  5    13         8    35         2.692    0           OUI
  6    295        10   126        0.427    0           OUI
  7    1909       12   462        0.242    0           OUI
  8    1631       13   792        0.486    0           OUI
  9    13085      15   3003       0.229    0           OUI
  10   6487       16   5005       0.772    0           OUI
  11   84997      18   19448      0.229    0           OUI
  12   517135     20   75582      0.146    0           OUI
  13   502829     21   125970     0.251    0           OUI
  14   3605639    23   497420     0.138    0           OUI

PHENOMENE CLE : Meme quand il y a des MILLIERS d'etats communs
  forward/backward (ex: k=14, 3522 etats communs au RDV j=7),
  les POSITIONS ne sont JAMAIS compatibles (p_fwd >= p_bwd).

  Les "vagues" forward et backward consomment les MEMES positions
  (centrales), ne laissant aucun espace pour se connecter.

QUESTION OUVERTE : Pourquoi les positions sont-elles TOUJOURS incompatibles ?
  C'est la cle pour transformer le resultat numerique en preuve formelle.

PISTES DE FORMALISATION :
  (a) Argument de comptage : les positions centrales sont "doublement occupees"
  (b) Argument entropique : forward et backward couvrent > S/2 positions chacun
  (c) Argument par la structure de d = 2^S - 3^k : les transitions de Horner
      creent un "drift" dans les positions qui empeche la compatibilite
```

---

## 6. REFORMULATIONS DU PROBLEME (6 formulations)

### R1 : Formulation combinatoire
```
Tout k >= 3, tout subset {p_1,...,p_{k-1}} dans {1,...,S-1} :
  3^{k-1} + Sum 3^{k-1-j}*2^{p_j} not= 0  (mod 2^S - 3^k)
```

### R2 : Formulation Collatz (Steiner)
```
Tout k >= 3, il n'existe aucun entier n >= 1 tel que :
  n*(2^S - 3^k) = 3^{k-1} + Sum 3^{k-1-j}*2^{p_j}
pour un choix ordonne 1 <= p_1 < ... < p_{k-1} <= S-1.
```

### R3 : Formulation par chemins (automate) — PRIVILEGIEE
```
Tout k >= 3, dans le graphe dirige sur Z/dZ ou
  c ->_{pos p} (3c + 2^p) mod d,
il n'existe aucun chemin de longueur k-1 de l'etat 1 a l'etat 0
utilisant des positions strictement croissantes dans {1,...,S-1}.
```

### R4 : Formulation par polynome generateur
```
Tout k >= 3, soit P(x) = Sum_{A in Comp} x^{corrSum(A) mod d}.
Alors le coefficient de x^0 dans P(x) est 0.
```

### R5 : Formulation par sous-sommes ponderees
```
Tout k >= 3, dans Z/dZ, la somme ponderee
  Sum_{j=0}^{k-1} 3^{k-1-j}*2^{p_j}
avec 0 = p_0 < p_1 < ... < p_{k-1} <= S-1
ne prend JAMAIS la valeur 0.
Autrement dit : 0 not in Im(Ev_d).
```

### R7 : NOUVELLE (session 5) — Formulation par Double Peeling
```
Tout k >= 3, definissons :
  Forward_j  = couches de l'automate depuis c_0=1 (j pas forward)
  Backward_m = couches de l'automate inverse depuis c_{k-1}=0 (m pas backward)

Pour chaque point de rendez-vous j in {0,...,k-1} :
  Forward_j ∩ Backward_{k-1-j} est VIDE au sens des positions :
    il n'existe aucun (s, p_fwd, p_bwd) tel que
      s in Forward_j  ET  s in Backward_{k-1-j}  ET  p_fwd < p_bwd

Autrement dit : les vagues forward et backward NE PEUVENT PAS se connecter,
car les positions qu'elles utilisent se CHEVAUCHENT toujours.
```

### R6 : NOUVELLE — Formulation par filtration a 3 contraintes
```
Soit Reach(k) l'ensemble des etats atteignables depuis 1 dans
l'automate de Horner apres k-1 pas avec positions croissantes
dans {1,...,S-1}. Alors :

  0 not in Reach(k)

ou Reach(k) est limite par trois filtres :
  (A) Le "gap algebrique" : {2^p mod d : p in {1,...,S-1}} != Z/dZ*
      (quand ord_d(2) > S-1, les puissances de 2 ne couvrent pas tout)
  (B) La contrainte d'ordre : chaque pas reduit les positions disponibles
  (C) La borne S-1 : exclut les grandes puissances de 2

  La TAILLE de Reach(k) est exactement C = binom(S-1, k-1) (en comptant
  les multiplicites), et 0 n'est jamais dans l'image.
```

---

## 7. QUESTIONS OUVERTES HIERARCHISEES (mise a jour)

### Niveau 1 (debloque tout)
- **Q1** : Pourquoi N_0(13) = 0 pour k=5 alors que C/d = 2.69 ?
  **ECLAIRE** : mecanisme de blocage a 3 composantes identifie.
  **RESTE** : formaliser en preuve generalisable.
- **Q2** : L'automate de Horner mod d a-t-il un gap spectral ?
  **RESOLU PARTIELLEMENT (session 4)** : L'automate est inhomogene (M_p differentes).
  f_{k-1}(S-1) a rang PLEIN (d). La decomposition de Fourier par orbites de <3>
  decompose T = Sum M_p en blocs. Eigenvalue triviale = S-1, non-triviales ~ sqrt(S-1).
  Le blocage de 0 n'est PAS un phenomene de rang mais SPECIFIQUE a c_0 = 1.
  **NOUVELLE QUESTION** : Pourquoi c_0 = 1 est-il le SEUL etat bloque ?
- **Q3** : Existe-t-il un invariant de corrSum mod d au-dela de parite et mod 3 ?
  **RESOLU : NON.** Recherche exhaustive mod 2..50 pour k=3..17.
  Seuls invariants universels : impair + non div par 3 + {1,3} mod 4.

### Niveau 2 (renforce la preuve)
- **Q4** : La formule CRT N_0(d) ~ C*prod(N_0(p_i)/C) est-elle exacte ?
  **ECLAIRE : NON pour k >= 6.** Les correlations sont significatives.
- **Q5** : Le Peeling itere donne-t-il N_0(d) <= alpha^r*C ?
  **OUVERT**
- **Q6** : L'energie additive de corrSum est-elle calculable ?
  **OUVERT** mais E2/E2_random ~ 1.24 pour k=5 (mild deviation).

### Niveau 3 (vision long terme)
- **Q7** : Le resultat est-il formalisable en Lean 4 ?
- **Q8** : La methode s'etend-elle aux cycles negatifs ?
- **Q9** : Existe-t-il une preuve "one-line" via un invariant cache ?
  **PARTIELLEMENT RESOLU : Pas d'invariant "simple" (Front 4 clos).**
  Si "one-line" existe, c'est via la structure d = 2^S - 3^k, pas un invariant.

---

## 8. DECOUVERTES ET THEOREMES NOUVEAUX (session 3)

### 8.1 Lemme : corrSum in {1, 3} mod 4
```
ENONCE : Pour tout k >= 3 et toute composition A in Comp(S,k),
  corrSum(A) = 1 ou 3 (mod 4).

PREUVE : corrSum = Sum_{j=0}^{k-1} 3^{k-1-j} * 2^{A_j}
  - Le terme j=0 : 3^{k-1} * 2^0 = 3^{k-1} = 1 ou 3 mod 4
  - Le terme j=1 : 3^{k-2} * 2^{A_1}, avec A_1 >= 1
    Si A_1 = 1 : 3^{k-2} * 2 = 2 mod 4 (contribue +2 mod 4)
    Si A_1 >= 2 : 3^{k-2} * 2^{A_1} = 0 mod 4 (ne contribue pas)
  - Les termes j >= 2 : 3^{k-1-j} * 2^{A_j}, avec A_j >= 2
    Donc 2^{A_j} = 0 mod 4, et ces termes sont 0 mod 4.
  Total : corrSum = 3^{k-1} + (0 ou 2) mod 4 = {1,3} mod 4.
```

### 8.2 THEOREME CONJECTURAL : Inaccessibilite du residu fantome
```
Pour tout k >= 4 avec d = 2^S - 3^k > 0 :
  2^S mod d  NOT IN  {2^q mod d : q = 1,...,S-1}

Equivalence : ord_d(2) > S-1

CONSEQUENCE : La seule position qui produit le residu 3^k mod d
  est la position interdite p = S. La transition directe vers 0
  depuis l'etat -3^{k-1} mod d est STRUCTURELLEMENT impossible.

VERIFIE : k = 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
CAS SPECIAL : k=3 (d=5), ord_5(2) = 4 = S-1, le residu EST accessible
  mais la contrainte d'ordre le bloque.
```

### 8.3 DECOUVERTE (sessions 4+5) : Accessibilite de l'etat 0
```
RESULTAT CORRIGE (session 5 — why_c0_equals_1.py) :

  Le nombre d'etats bloques depend FORTEMENT du ratio C/d :

  k=3 (d=5,   C/d=1.20) : 1/5   bloque   (20%) — seul {1}
  k=4 (d=47,  C/d=0.43) : 29/47 bloques  (62%) — 1 parmi 29
  k=5 (d=13,  C/d=2.69) : 1/13  bloque   (8%)  — seul {1}  [ANOMALIE]
  k=6 (d=295, C/d=0.43) : 189/295 bloques (64%) — 1 parmi 189
  k=7 (d=1909,C/d=0.24) : quasi-totalite bloques

  PATTERN : Quand C/d > 1 (k=3,5,17), presque TOUT atteint 0 sauf 1.
            Quand C/d < 1, la MAJORITE des etats sont bloques.

  FAIT INVARIANT : c_0 = 1 est TOUJOURS bloque, QUEL QUE SOIT C/d.

  CORRECTION de session 4 : "seul c_0=1 est bloque" etait VRAI uniquement
  pour k=3 et k=5 (cas anomaux avec C/d > 1). Pour les k typiques,
  beaucoup d'etats sont bloques.

CONSEQUENCES :
  (a) La question N'EST PLUS "pourquoi 1 est le seul bloque"
  (b) La vraie question : pourquoi 1 est-il TOUJOURS parmi les bloques ?
      Meme quand C/d = 2.69 (k=5), ou 12/13 etats atteignent 0, 1 ne le peut pas.
  (c) L'etat 1 = 2^{A_0} = 2^0 est impose par la structure de Steiner.
  (d) Pour k grand (C/d << 1), le blocage est "generique" (presque tout bloque).
      Seul le regime C/d > 1 est structurellement informatif.

PISTE C (session 5) : corrSum(A) ne peut JAMAIS etre un multiple de d.
  Teste pour k=3..7 : TOUS les n_0 candidats echouent a l'enumeration.
  La partie variable Σ 3^{k-1-j}·2^{A_j} ne peut pas prendre la valeur n_0·d - 3^{k-1}.

PISTE E (session 5) : Double Peeling
  Pour k=6 : Forward (36 etats) ∩ Backward (36 etats) = 2 etats communs,
  MAIS avec contraintes de position : 0 paires compatibles !
  ==> Le double peeling PROUVE N_0 = 0 pour k=6 si formalisable.
```

### 8.4 Theoreme (heuristique) : Mecanisme de blocage a 3 composantes
```
ENONCE CONJECTURAL :
Pour tout k >= 3, avec d = 2^S - 3^k > 0 et S = ceil(k*log_2(3)),
l'etat 0 est inatteignable dans l'automate de Horner
  c_0 = 1, c_j = (3*c_{j-1} + 2^{p_j}) mod d
avec 1 <= p_1 < p_2 < ... < p_{k-1} <= S-1,
en raison de l'interaction de trois contraintes :

  (A) GAP ALGEBRIQUE : ord_d(2) > S-1 pour k >= 4
      ==> les residus {2^p mod d : p = 1,...,S-1} ne couvrent pas Z/dZ*
      ==> certaines transitions de l'automate sont "impossibles"

  (B) CONTRAINTE D'ORDRE : les positions doivent etre strictement croissantes
      ==> a chaque pas, les positions encore disponibles diminuent
      ==> les chemins sont des marches dans un "entonnoir" de positions

  (C) BORNE SUPERIEURE : p <= S-1
      ==> les puissances 2^p sont bornees, excluant les grands residus
      ==> en particulier, 2^S = 3^k mod d n'est PAS disponible

  QUANTIFICATION NUMERIQUE :
    k=3 (d=5) :   0% gap, 75% ordre, 25% zero-transit
    k=5 (d=13) :  40% gap, 51% ordre, 9% zero-transit
    k=7 (d=1909): ~99% gap, ~1% ordre
    Tendance : pour k grand, le gap algebrique domine (>90%)

STATUT : Verifie numeriquement pour k=3..17. Non formalise.
```

### 8.5 Attaque du Theoreme 8.2 : ord_d(2) > S-1 (session 4)
```
RESULTATS de theorem82_ord_proof.py (7 volets) :

VOLET 1 — Reduction diophantienne :
  ord_d(2) <= S-1 <=> il existe s in {1,...,S-1} tel que d | (3^k - 2^s)
  Pour k=4..49 : AUCUN s ne satisfait cette condition.
  CAS UNIQUE : k=3 (d=5), s=1 (3^3 - 2^1 = 25 = 5*5).
  ==> Pour k >= 4, la condition diophantienne est JAMAIS satisfaite.

VOLET 2 — Argument de taille (theta > 0.415) :
  theta = S - k*log_2(3) in [0,1). Pour theta > 0.415 :
    |3^k - 2^s| >= d * (2^theta - 1) > 0.33 * d pour tout s <= S-2.
  Elimine ~58% des k par taille seule.
  Les k "dangereux" sont ceux avec theta petit (proches de convergents de log_2(3)).

VOLET 3 — Equation de Pillai pour r = S-1 :
  d | (2^{S-1} - 1) se reecrit (2q-1)*2^{S-1} + 1 = q*3^k.
  Solutions : (q=1, k=2) et (q=3, k=3) UNIQUEMENT.
  ==> Pour k >= 4, le cas r = S-1 est EXCLU.

VOLET 4 — Near-misses :
  delta(k) = min_s |(3^k - 2^s) mod d| / d
  Pour k >= 4 : delta(k) >= 0.003066 (k=8).
  ==> 3^k - 2^s est toujours "loin" d'un multiple de d.

VOLET 5 — Analyse du quotient q = (3^k - 1)/(2^S - 1) :
  frac(q) le plus proche de 0 : 0.0138 (k=12), 0.0282 (k=24).
  JAMAIS entier pour k >= 4.

VOLET 6 — Fractions continues de log_2(3) :
  [1; 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, ...]
  Convergents "dangereux" : k = 5, 12, 41, 53, 306, ...
  Ce sont les k ou theta(k) est le plus petit.
  MAIS meme pour ces k, la condition diophantienne echoue.

VOLET 7 — Strategie Baker :
  Par le theoreme de Baker (1968), la forme lineaire
    Lambda = k*log(3) - S*log(2)
  satisfait |Lambda| > C * H^{-B} pour constantes effectives C, B.
  Ceci donne une borne K_0 telle que pour k > K_0, le theoreme 8.2 est AUTOMATIQUE.
  Pour k <= K_0 : verification numerique (deja faite pour k <= 49).

STATUT : Verifie pour k = 4..49. Preuve formelle en attente (Baker).
```

### 8.6 Observation : Pas d'invariant universel
```
RESULTAT DEFINITIF (Front 4) :
  Il n'existe AUCUN invariant universel mod m (pour m = 2..50)
  au-dela de : corrSum impair + corrSum non div par 3.

  En particulier :
  - mod 9 pour k >= 6 : residus interdits = {0,3,6} = multiples de 3
    (simple consequence de "non div par 3", pas nouveau)
  - mod 12 : residus interdits = {0,2,3,4,6,8,9,10}
    (consequence de "impair" + "non div par 3")

  ==> Le mecanisme de N_0(d) = 0 est INTRINSEQUE a d = 2^S - 3^k
      et ne se reduit PAS a des congruences universelles.
```

### 8.8 THEOREME (numerique) : Double Peeling — incompatibilite forward/backward
```
ENONCE : Pour tout k in {3,...,14} avec d = 2^S - 3^k > 0 :

  Soient Forward_j = {(s, p_max) : chemins de j pas depuis c_0=1}
         Backward_{k-1-j} = {(s, p_min) : chemins de (k-1-j) pas vers c_{k-1}=0}

  Pour TOUT point de rendez-vous j in {0,...,k-1} :
    il n'existe AUCUN etat s et positions (p_fwd, p_bwd) tels que
      (s, p_fwd) in Forward_j  ET  (s, p_bwd) in Backward_{k-1-j}  ET  p_fwd < p_bwd

CONSEQUENCE : Il n'existe aucun chemin complet de c_0=1 a c_{k-1}=0,
  donc N_0(d) = 0 pour k = 3,...,14.

SIGNIFICANCE :
  - C'est une preuve CONSTRUCTIVE (par exploration exhaustive des couches)
  - Elle ne depend PAS du Theoreme 8.2 (ord_d(2) > S-1) — elle est INDEPENDANTE
  - Elle fonctionne meme pour k=3 (ou le gap algebrique est nul)
  - Elle fonctionne meme pour k=5 (ou C/d = 2.69 >> 1)
  - Elle capture AUTOMATIQUEMENT l'interaction des 3 composantes (A)(B)(C)

OBSERVATION STRUCTURELLE :
  Pour k=14 (d=3605639) au point de RDV j=7 :
    Forward : 252946 chemins, 3522 etats
    Backward : 252946 chemins, 3522 etats
    Etats communs : 3522 (TOUS les etats sont communs !)
    Paires compatibles : 0 (les POSITIONS bloquent tout)

  ==> Le blocage N'EST PAS un probleme d'etats (ils se rencontrent)
      mais un probleme de POSITIONS (l'entonnoir forward et backward
      consomment les memes positions centrales).

STATUT : Verifie numeriquement k=3..14. Formalisation en cours.
```

### 8.7 Observation : Echec CRT et correlations
```
Pour d compose avec k >= 6 :
  Tous les facteurs premiers p | d verifient N_0(p) > 0.
  Pourtant N_0(d) = 0.

  ==> Les valeurs de corrSum mod p et mod q (pour p*q | d) sont CORRELEES.
  ==> Cette correlation est induite par la structure d = 2^S - 3^k
      qui relie les modules entre eux.

PISTE : La correlation pourrait etre quantifiable via le fait que
  2^S = 3^k mod d, ce qui cree une relation globale entre les
  residus mod les differents facteurs premiers.
```

### 8.9 RESULTATS SESSION 6 : Attaque de l'Enonce C
```
SESSION 6 (3 mars 2026) : INVESTIGATION APPROFONDIE DE L'ENONCE C

=== BUG CORRIGE ===
Investigation 6 de session 5b avait un bug dans le prefixe :
  BUGGE  : prefix = 5*3^{k-2} (manque le terme j=2)
  CORRECT: prefix = (9 + 5*2^p)*3^{k-3}  (pour composition 0, p, p+1)
  Pour p=1 (s=5) : prefix = 19*3^{k-3}
Les "faux positifs" (k=5, k=10 cible trouvee) sont des artefacts.
Le target CORRIGE est TOUJOURS ABSENT pour k=5..12.

=== ARGUMENT MOD 3 : INVALIDE ===
Tentative : prefix = 0 mod 3, suffix != 0 mod 3, donc corrSum != 0 mod 3.
ERREUR : gcd(d, 3) = 1 (Lemme 1.2), donc d | corrSum N'EXIGE PAS 3 | corrSum.
L'argument mod 3 est INSUFFISANT.

=== DECOUVERTE CLE : L'OBSTRUCTION EST L'INTERACTION ORDRE × STRUCTURE ===
  L'automate backward SANS contrainte d'ordre (positions quelconques >= p+2)
  atteint TOUJOURS s=5, en utilisant des positions REPETEES (ex: [3,3,5]).
  Pour k=5..13 : couverture 100% de Z/dZ.

  L'automate backward AVEC positions strictement decroissantes
  N'ATTEINT JAMAIS s=5. Verifie pour k=5..13.
  Couverture ordonnee : 3.7% (k=12) a 53.8% (k=5) de Z/dZ.

  CONCLUSION : L'obstruction est la COMBINAISON de trois facteurs :
    1. Contrainte d'ordre strict : reduit C(n, k-2) vs n^{k-2}
    2. Structure multiplicative : poids 3^{k-1-j}*2^{q_j} avec hierarchie
    3. Identite 3^k = 2^S - d : lie le modulus aux poids
  Aucun facteur seul ne suffit. C'est leur INTERACTION qui cree le trou.

=== ZONE D'EXCLUSION CROISSANTE ===
  Distance minimale (ordonnee) entre residus atteignables et target :
    k=5: rayon=1, k=6: rayon=6, k=7: rayon=15, k=9: rayon=64
  Le target est au centre d'un "bassin d'exclusion" croissant.

=== VERIFICATION EXHAUSTIVE ETENDUE ===
  Pour TOUT p (pas seulement p=1) et k=3..12 :
  Aucune composition (0, p, p+1, q_3, ..., q_{k-1}) ordonnee ne donne
  corrSum = 0 mod d. Verifie sur des centaines de milliers de compositions.

=== CONSEQUENCE STRATEGIQUE ===
  L'Enonce C est EQUIVALENT a N_0(d)=0 restreint aux compositions
  commencant par la position p.
  La decomposition A/B/C ne REDUIT PAS la difficulte : elle la redistribue.
  L'Enonce B est facile (pigeonhole), mais C concentre TOUTE la difficulte.
```

### 8.10 RESULTATS SESSION 7 : Deux mecanismes de blocage
```
SESSION 7 (3 mars 2026) : INVESTIGATION SYSTEMATIQUE DES MECANISMES

=== DECOUVERTE : DICHOTOMIE DES MECANISMES ===
Deux mecanismes DISTINCTS empechent N_0(d) = 0 :

MECANISME I : PRIME BLOCKING
  Quand d est premier (ou a un grand facteur premier p) :
  N_0(p) = 0 directement (aucune composition n'annule corrSum mod p)
  Cas verifies : k=3(5), 4(47), 5(13), 7(83), 8(233), 11(7727), 13(502829)

MECANISME II : CRT ANTI-CORRELATION
  Quand d = p_1*p_2*...*p_r (compose) et N_0(p_i) > 0 pour tout i :
  Les compositions annulant mod p_i sont "forcees" vers residus != 0 mod p_j
  Jamais (0, 0, ..., 0) simultane malgre chaque composante possible
  Cas verifies : k=6(5*59), 9(5*2617), 10(13*499), 12(5*59*1753), 14(79*45641)

=== FERMETURE DE PISTES ===
  - Spectrale (matrice de transfert) : FERMEE — difficulte equivalente a N_0(d)=0
  - Counting fails : C/d < 1 ne suffit pas pour k petit
  - L1/Cauchy-Schwarz : borne |T_d(t)| trop faible
  - Modulus universel : pas d'invariant universel
```

### 8.11 RESULTATS SESSION 8 : Investigation multi-lentille (26 investigations)
```
SESSION 8 (4 mars 2026) : PROTOCOLE DISCOVERY v2.0, ARCHITECTURE MULTI-LENTILLE

=== INNOVATIONS PROTOCOLE ===
  - QUASAR adapte : Niveau 0 axiomes, Multi-Lentille L1-L4, Niveaux conviction
  - regression_test.py : 110/110 tests passent (Phase 7.2)
  - 4 scripts d'investigation profonde crees

=== B1 : REFORMULATION ALGEBRIQUE ===
  corrSum = 0 mod d <=> Sum w^j * 2^{A_j} = 0 mod d (w = 3^{-1} mod d)
  Identite w^k = 2^{-S} mod d
  Substitution B_j = A_j - j : Sum (w*2)^j * 2^{B_j} avec B_j >= 0 croissant

=== B2 : BAKER / ENONCE A ===
  *** REDUCTION CRITIQUE ***
  ord_d(2) = S-1 <=> d | (3^k - 2)
  Verifie k=4..35 : d ne divise JAMAIS 3^k - 2
  Cas k=3 : SEUL cas ou d | (3^k-2), car d=5 et 25=5*5
  ord_d(2) >= S verifie pour k=4..30 (calcul exact)
  ==> ENONCE A est VRAI numeriquement (et la reduction est prouvable)

=== B5 : PRIME BLOCKING — DECOUVERTE FONDAMENTALE ===
  *** LA CONTRAINTE D'ORDRE EST CRITIQUE ***
  Pour d premier : sans ordre, image couvre Z/pZ entier (100%)
  Avec ordre strict : image couvre TOUT SAUF 0
  k=3: diff = {0}, k=4: diff contient 0, k=5: diff = {0}
  ==> L'ordre exclut 0 CHIRURGICALEMENT

  *** DISTANCE MINIMALE A LA CIBLE = 1 ***
  Pour k=3 (p=5) : seule valeur absente = {4} = {-1 mod 5}
  Pour k=5 (p=13) : seule valeur absente = {12} = {-1 mod 13}

  *** FOURIER (caracteres) : pas d'annulation aleatoire ***
  Condition Sum|S_t| < C JAMAIS satisfaite
  Le blocking est STRUCTUREL, pas probabiliste

  *** AUTOMATE DE HORNER mod p ***
  c_needed pour atteindre 0 EXISTE dans l'automate
  mais PAS a la bonne couche/position — meme observation que contrainte d'ordre

=== B3 : CRT ANTI-CORRELATION PROFONDE ===
  k=6 (5*59) : (0,0)=0 vs attendu 1.7 si independant
  k=10 (13*499) : (0,0)=0 vs attendu 2.9
  k=12 (5*59*1753) : paires (0,0) EXISTENT mais triplet (0,0,0) JAMAIS

=== L4 : SAT/SMT ENCODING ===
  3 approches implementees :
    1. Double Peeling : UNSAT pour k=3..12 (0 paires compatibles)
    2. Modular Sieve : identifie mecanisme (prime vs CRT)
    3. Branch & Bound : pruning 27-85% de l'espace (ratio BB/C = 0.27 a 2.17)

=== SYNTHESE : DICHOTOMIE FONDAMENTALE ===
  Pour TOUT k >= 3, N_0(d) = 0 par l'un des mecanismes :
    Mec I  : d premier → Prime Blocking (ord exclut 0)
    Mec II : d compose → CRT anti-correlation (2^S = 3^k mod d force dependance)
    Mec III: d compose avec grand facteur premier bloqueur
  CONJECTURE AFFINEE : cette trichotomie est exhaustive
  CONVICTION : ESQUISSE → PROUVE_PARTIEL (verifie k=3..21+)
```

---

## 9. OUTILS CREES

### Scripts d'exploration (dossier scripts/tools/)
```
front1_k5_analysis.py        Analyse exhaustive k=5, d=13 (35 corrSum)
                              ATTENTION : automate bugge (c_0=3 au lieu de 1)
                              PARTIES VALIDES : enumeration, distribution, structure

front1_corrected_deep.py      Automate CORRIGE + analyse multi-k
                              c_0 = 1, contrainte d'ordre respectee
                              Comparaison k=3..15, structure algebrique

front1_blocking_mechanism.py  Trace du mecanisme de blocage pas-a-pas
                              Categorise les raisons : gap / ordre / zero-transit
                              Multi-k avec table synthetique

front4_invariants.py          Recherche systematique d'invariants mod m
                              k=3..17, m=2..50
                              Resultat : pas d'invariant au-dela mod 2 + mod 3

phantom_position_test.py      Test de l'hypothese de la position fantome
                              Verifie si -3^{k-1} mod d est atteignable
                              et si 2^S mod d est dans les positions legales
                              RESULTAT : Theoreme 8.2 (residu fantome inaccessible)

front2_spectral_analysis.py   Analyse spectrale COMPLETE de l'automate de Horner
                              Matrices de permutation M_p, fonctions symetriques f_j(q)
                              Decomposition de Fourier par orbites de <3>
                              DECOUVERTE : 0 accessible depuis tout sauf c_0=1

theorem82_ord_proof.py        Attaque en 7 volets du Theoreme 8.2
                              Diophantine, taille, Pillai, near-miss, quotient,
                              fractions continues, Baker
                              RESULTAT : Verifie pour k=4..49, strategie Baker identifiee

why_c0_equals_1.py            Analyse 5 pistes de la specificite de c_0=1
                              Piste A : bornes corrSum (min/max, distribution n_0)
                              Piste B : trajectoire depuis c_0=1
                              Piste C : corrSum ne peut JAMAIS etre multiple de d
                              Piste D : CORRECTION — nombre d'etats bloques depend de C/d
                              Piste E : Double Peeling (prototype k=6)
                              RESULTAT : Correction decouverte session 4, Double Peeling prometteur

double_peeling_proof.py       Double Peeling systematique k=3..k_max
                              Forward (c_0=1) + Backward (c_{k-1}=0)
                              Transitions inverses via 3^{-1} mod d
                              Test de compatibilite des positions a chaque RDV
                              RESULTAT EXTRAORDINAIRE : N_0(d) = 0 PROUVE pour k=3..14
                              (zero paires compatibles pour TOUS les k testes)

enonce_c_investigation.py     8 investigations initiales pour Enonce C
                              ATTENTION : BUG dans Investigation 6 (prefixe faux)
                              Investigations 1-5, 7-8 restent valides.

enonce_c_deep_analysis.py     Correction bug Investigation 6 + analyse profonde
                              8 parties : verification bug, suffixes, mod 3 (INVALIDE)
                              CRASH a la partie 3 (TypeError). Parties 4-8 non executees.
                              RESULTAT : target corrige TOUJOURS absent k=5..12.

obstruction_search.py         7 approches pour trouver l'obstruction reelle
                              Approche 2 : verification exhaustive TOUS p, k=3..12
                              Approche 4 : DECOUVERTE que automate NON ordonne couvre tout
                              ALERTE : automate approche 4 n'a PAS la contrainte d'ordre

ordered_backward_automaton.py  Automate backward CORRECT avec positions decroissantes
                              SCRIPT CLE de session 6.
                              Tracking (residue, last_position) pour contrainte d'ordre
                              Comparaison ordonne vs non ordonne
                              Zone d'exclusion + interaction analyse
                              RESULTAT : target s=5 ABSENT pour k=5..13 ordonne
                              RESULTAT : target PRESENT pour k=5..13 non ordonne (100%)

session8_multi_branch_investigation.py
                              Investigation multi-branches B1-B6 (6 branches)
                              B1: reformulation w, B2: Baker/ord, B3: CRT,
                              B4: induction, B5: p-adique, B6: coding theory
                              RESULTAT : priorites identifiees (B5 > B2 > B3)

session8_deep_prime_blocking.py
                              9 investigations : image vs cible, alphabet,
                              CONTRAINTE D'ORDRE, sommes partielles, caracteres,
                              identite 2^S=3^k, automate Horner mod p, test etendu,
                              interaction <w>*<2>
                              DECOUVERTE MAJEURE : sans ordre, image = Z/pZ entier
                              AVEC ordre : 0 exclu CHIRURGICALEMENT

session8_deep_B5b_ordering_and_big_primes.py
                              7 investigations : ordres progressifs, blockers pattern,
                              mecanisme couche par couche, ord_p(2) vs S,
                              discrete log, seuil taille, CRT profond
                              DECOUVERTE : pour k=6,9,10,12,14-16 AUCUN bloqueur direct
                              CRT anti-correlation est le SEUL mecanisme

session8_deep_baker.py        9 investigations pour Enonce A
                              Cartographie ord_d(2) k=3..30, arguments taille,
                              factorisation, |3^k-2^s|, Baker bounds,
                              REDUCTION CRITIQUE : ord_d(2)=S-1 <=> d|(3^k-2)
                              Verifie d ne divise JAMAIS 3^k-2 pour k=4..35

session8_deep_sat_smt.py      3 approches SAT/SMT-like
                              Double Peeling (BFS), Modular Sieve (CRT par premier),
                              Branch & Bound (pruning backward)
                              Toutes confirment UNSAT (N_0=0) pour k=3..12+

regression_test.py            Suite de tests de regression (110 tests)
                              8 sections : axiomes, N_0=0, odd, mod3, mod4,
                              ord, double peeling, synthetics
                              EXIGENCE Phase 7.2 du protocole

session9_prime_blocking_formal.py
                              9 investigations : structure de w, couche par couche,
                              PREUVE COMPLETE k=3, analyse k=5, polynome generateur,
                              Fourier, identite w^k=2^{-S}, conjecture image,
                              combinatoire additive
                              RESULTAT : preuve k=3 TERMINEE (3 solutions algebriques
                              toutes position-incompatibles)

session9_algebraic_vs_positional.py
                              7 investigations : positions dernier couche, drift
                              multiplicatif, structure 2^a mod p, backward,
                              conflit position-residu, bornes corrSum, substitution B_j
                              DECOUVERTE : backward depuis 0 n'atteint JAMAIS s_0=1

session9c_deep_backward_exclusion.py
                              9 investigations : backward systematique, pourquoi 1 exclu,
                              u=w*2 (quand u=-1?), 0 seul absent, lien backward/subst,
                              theoreme unifie, anti-concentration, identite profonde,
                              synthese
                              DECOUVERTE : sigma(u) = Sum u^j != 0 (necessaire)
                              u^k = 2^{k-S} (identite universelle)

session9d_target_minus_one.py
                              10 investigations : -1 systematique, seul absent,
                              SANS ORDRE (-1 apparait !), polynomes lacunaires,
                              DFT, induction, ordre de w, weighted subset sum,
                              d composite, synthese
                              DECOUVERTE MAJEURE : sans contrainte d'ordre, -1 est PRESENT
                              L'ordre strict est le SEUL mecanisme qui elimine -1

session9e_crt_anticorrelation.py
                              7 investigations : matrice CRT, distribution conditionnelle,
                              mecanisme exclusion, structure d, mecanisme couple,
                              correlation positions, synthese
                              RESULTAT : anti-correlation PARFAITE pour k=6..11
                              P(r2=0|r1=0) = 0 (exclusion bi-directionnelle)

session10_general_prime_blocking.py
                              9 investigations : pourquoi l'ordre exclut -1,
                              signature de position, sommes partielles,
                              contributions marginales, k=5 detaille, k=4 detaille,
                              barriere monotone, geometrie des poids, synthese
                              OBJECTIF : preuve generale Mecanisme I

session10_protocol_research.md
                              Notes de recherche methodologique
                              7 sources analysees : Aletheia, AlphaProof, FunSearch,
                              AlphaGeometry2, Tao/AlphaEvolve, Safe/Lean4, anti-halluc.
                              RESULTAT : DISCOVERY_PROTOCOL v2.0 → v2.2

session10b_contradiction_approach.py
                              7 investigations : sigma_tilde, multiplication par u,
                              somme complete, Newton sums, scale k=13,
                              condition sigma_zero, synthese
                              RESULTATS CLES :
                              - sigma_tilde(u) = 0 ⟺ ord(u) | (k-1)
                              - f(B+1) = 2*f(B) mod p (relation de decalage)
                              - u^k = 2^{k-S} confirme pour tout k

session10c_exclusion_chain.py
                              8 investigations : chaine d'exclusion, backward chain,
                              structure frontieres, fermeture x2, spread, obstruction
                              algebrique, tous prime k, synthese
                              RESULTATS CLES :
                              ★ THEOREME : Im(f) est x2-presque-close,
                                violations UNIQUEMENT au plafond (B_max=M)
                              ★ -1 toujours dans l'ensemble exclu par le plafond
                              ★ Backward chain : -1/2 accessible mais bloquee au plafond

session10d_mechanism_II_crt.py
                              7 investigations : factorisation, matrice CRT jointe,
                              detail anti-correlation, ordres multiplicatifs,
                              corrSum mod produit, 3+ facteurs, synthese
                              RESULTATS CLES :
                              ★ Classification k=3..13 par mecanisme :
                                Mec. I : k=3,4,5,7,8,11,13 (prime ou un facteur N0=0)
                                Mec. II : k=6,9,10 (pairwise CRT M[0,0]=0)
                                Mec. III : k=12 (triplet M[0,0,0]=0, paires ≠ 0)
                              ★ Anti-correlation bidirectionnelle verifiee
                              ★ Pour k=12 : paires ne bloquent pas, triplet bloque

session10b_scratch.md + session10d_scratch.md
                              Notes d'analyse au fil de l'eau (sessions 10b-d + 10e)

session10e_filtration_proof.py
                              7 investigations : filtration Im_0 ⊂ Im_1 ⊂ ... ⊂ Im_M,
                              shift closure 2·Im_m ⊂ Im_{m+1}, backward chain dans filtration,
                              vrais nouveaux, pattern first_layer(-2^{-m}) = M+1-m
                              RESULTATS CLES :
                              - 2·Im_m ⊂ Im_{m+1} VERIFIE pour k=3,4,5,13
                              - -1 JAMAIS dans aucune couche Im_m
                              - Backward chain TOTALEMENT exclue (k=3,5)
                              ★ Pattern d'apparition decalee confirmé

session10e2_backward_chain_universal.py
                              8 investigations : universalite backward chain, identite
                              corrSum-filtration, orbite de -1, reformulation corrSum
                              RESULTATS CLES :
                              - Backward chain UNIVERSELLEMENT exclue (k=3,4,5,13)
                              - N₀(p)=0 ⟺ -1 ∉ Im_M(f) (equivalence filtration)
                              - k=3,5: Im(f) = Z/pZ \ {-1} (SEUL -1 manque)
                              ★ Equivalence corrSum — filtration prouvee

session10e3_algebraic_proof.py
                              8 investigations : preuves algebriques debordement k=3,4,5,
                              theoreme u=2^{-M}, exposants recentres, partition bandes
                              RESULTATS CLES :
                              - k=3 : 3 solutions, min(max)=3 > M=2 → QED
                              - k=5 : 99 solutions, min(max)=4 > M=3 → QED
                              - k=4 : 40 solutions, min(max)=7 > M=3, overflow=4 → QED
                              ★★★ THEOREME : σ̃=0 ⟹ u = 2^{-M} mod p (PROUVE)
                              ★★ (k-1)M = ord₂(p) pour σ̃=0

session10e4_universal_sigma0.py
                              7 investigations : cas σ̃=0 universels, sommes de Gauss,
                              bandes disjointes, preuve explicite k=3, comptage σ̃≠0
                              RESULTATS CLES :
                              - σ̃=0 avec d premier : seulement k=3,5 (teste k≤49)
                              - Bandes partitionnent exactement une periode de 2 mod p
                              - k=3 : seule combo donnant -1 viole non-decroissance ★★★★★
                              - k=5 : 0 combos contraintes donnent -1 (35 donnent le reste)
                              - σ̃≠0 : C(M+k-1,k-1) < p → image creuse par comptage
                              ★★★★★ ARCHITECTURE 3 CAS identifiee
```

---

## 10. STRATEGIE (mise a jour session 10 — 4 mars 2026)

### PARADIGME : DICHOTOMIE FONDAMENTALE A 3 MECANISMES
```
CHANGEMENT DE PARADIGME (session 8) :
  On ne cherche plus UN argument unique. On a identifie TROIS mecanismes
  distincts et complementaires, dont la preuve peut etre attaquee separement.

  MECANISME I  : PRIME BLOCKING (d premier ou grand facteur premier)
    - N_0(p) = 0 directement
    - La contrainte d'ORDRE exclut 0 CHIRURGICALEMENT
    - Sans ordre : image = Z/pZ entier. Avec ordre : TOUT sauf 0.
    - Cas : k=3,4,5,7,8,11,13 (d premier ou grand premier bloqueur)
    - CONVICTION : PROUVE_PARTIEL (verifie exactement k<=13, k<=18 etendu)

  MECANISME II : CRT ANTI-CORRELATION (d compose sans bloqueur direct)
    - Chaque facteur p_i permet N_0(p_i) > 0
    - MAIS l'identite 2^S = 3^k mod d force une dependance globale
    - Les paires (0,0) n'existent JAMAIS meme si chaque composante possible
    - Pour 3-prime d : paires (0,0) existent mais triplet (0,0,0) JAMAIS
    - Cas : k=6,9,10,12,14,15,16
    - CONVICTION : ESQUISSE (mecanisme identifie, pas de preuve formelle)

  MECANISME III : HYBRIDE (d compose avec bloqueur partiel)
    - Certains grands facteurs premiers bloquent (Mec I)
    - Pour les petits : CRT avec les autres (Mec II)
    - Cas : k=7(23×83, 83 bloque), k=8(7×233, 233 bloque)

  CONJECTURE AFFINEE : Cette trichotomie est EXHAUSTIVE pour tout k >= 3.
```

### AXE STRATEGIQUE 1 : Prouver le Mecanisme I (Prime Blocking)
```
PRIORITE : ★★★★★ (CRITIQUE)
OBJECTIF : Pour tout premier p | d(k), prouver N_0(p) = 0

APPROCHE PRINCIPALE : Formaliser l'exclusion chirurgicale de 0 par l'ordre
  FAIT ETABLI (session 8, 9 investigations) :
    - Image non-ordonnee = Z/pZ entier (100%)
    - Image ordonnee = Z/pZ \ {0} (tout sauf 0)
    - Reformulation : Sum w^j * 2^{A_j} != -1 mod p (A_j strictement croissants)

  PISTE A : Argument via automate de Horner mod p
    - L'etat c_needed pour atteindre 0 EXISTE dans l'automate
    - Mais il n'est JAMAIS a la bonne couche/position
    - Formaliser cette incompatibilite couche-position

  PISTE B : Caracteres et sommes exponentielles
    - Condition Fourier Sum|S_t| < C : JAMAIS satisfaite (blocking non probabiliste)
    - Approche via identite w^k = 2^{-S} mod p et substitution B_j = A_j - j
    - La contrainte 2^S = 3^k mod p contraint la somme de facon rigide

  PISTE C : Argument combinatoire direct
    - Pour d premier (k=3,5) : -1 est la SEULE valeur absente
    - Prouver par recurrence ou structure que l'image ordonnee evite -1

  *** NOUVEAU (session 10c) : PISTE D — Fermeture x2 + plafond ***
    - THEOREME : Im(f) est x2-presque-close (violations UNIQUEMENT a B_max=M)
    - -1 est toujours dans l'ensemble "bloque par le plafond"
    - Backward chain : -1 → -1/2 → -1/4 → ... → σ̃(u) avec plafond a chaque etape
    - Filtration Im_0 ⊂ Im_1 ⊂ ... ⊂ Im_M et exclusion de -1 a chaque couche
    - Condition necessaire : σ̃(u) · 2^M ≠ -1 mod p (VERIFIEE pour tout k teste)
    → PISTE LA PLUS PROMETTEUSE

  *** NOUVEAU (sessions 10e—10e4) : ARCHITECTURE DE PREUVE ***
    SOUS-CAS 1 : σ̃(u) = 0  (seulement k=3,5 avec d premier, teste k≤49)
      - THEOREME : u = 2^{-M} mod p (PROUVE : u = u^k · u^{-(k-1)} = 2^{-M})
      - f(B) = Σ 2^{B_j - jM}, exposants dans bandes disjointes
      - (k-1)M = ord₂(p) : bandes couvrent exactement une periode
      - k=3 : PREUVE COMPLETE — seule combo donnant -1 viole non-decroissance
      - k=5 : PREUVE COMPLETE — 0 combos contraintes donnent -1
      - STATUS : PROUVE pour les 2 cas existants (k=3,5)

    SOUS-CAS 2 : σ̃(u) ≠ 0  (tous k≥4 avec d premier sauf k=5)
      - Image creuse : C(M+k-1,k-1) < p (verifie k=4,13)
      - Backward chain TOTALEMENT exclue de Im(f)
      - Ordre multiplicatif grand → poids u^j diluent l'image
      - k=3,4,5 : preuves par debordement (min(max(B)) > M pour tout k)
      - STATUS : VERIFIE k≤13, A FORMALISER pour k arbitraire
      → CAS PRINCIPAL A PROUVER

    RESULTATS TRANSVERSAUX :
      - N₀(p)=0 ⟺ -1 ∉ Im_M(f) (equivalence filtration PROUVEE)
      - Backward chain {-2^{-m}} universellement exclue (prime d)
      - Debordement : overflow(k=3)=1, overflow(k=4)=4, overflow(k=5)=1

  DEPENDANCE : Enonce A (ord_d(2) >= S) renforce mais n'est PAS requis
    pour le prime blocking — le blocking fonctionne meme pour k=3 (ord=S-1)
```

### AXE STRATEGIQUE 2 : Prouver le Mecanisme II (CRT Anti-correlation)
```
PRIORITE : ★★★★ (HAUTE)
OBJECTIF : Pour d compose sans bloqueur direct, montrer que les residus
  (corrSum mod p_1, corrSum mod p_2, ...) ne sont JAMAIS simultanement 0

APPROCHE PRINCIPALE : Exploiter la dependance induite par 2^S = 3^k mod d
  FAIT ETABLI (session 8, Investigation G) :
    - k=6 (5×59) : (0,0) = 0 vs attendu 1.7 si independant
    - k=10 (13×499) : (0,0) = 0 vs attendu 2.9
    - k=12 (5×59×1753) : paires existent mais triplet JAMAIS

  PISTE A : Identite de couplage CRT
    - 2^S = 3^k mod p_1 ET 2^S = 3^k mod p_2
    - Cela cree une relation entre les compositions annulant mod p_1 et mod p_2
    - Formaliser cette relation comme une anti-correlation exacte

  PISTE B : Structure des compositions zero-mod-p
    - Pour chaque p | d, soit Z_p = {A : corrSum(A) = 0 mod p}
    - Montrer que les Z_p sont "disjoints" au sens CRT
    - i.e. Z_{p_1} ∩ Z_{p_2} = ∅

  PISTE C : Comptage par Inclusion-Exclusion
    - |Z_{p_1} ∩ Z_{p_2}| = 0 a prouver
    - Borne via sommes exponentielles mod p_1*p_2

  *** NOUVEAU (session 10d) : RESULTATS DETAILLES ***
    - Classification COMPLETE k=3..13 :
      Mec. I (prime ou facteur bloqueur) : k=3,4,5,7,8,11,13
      Mec. II (pairwise anti-corr.)      : k=6,9,10
      Mec. III (triplet anti-corr.)       : k=12
    - Anti-correlation BIDIRECTIONNELLE verifiee :
      k=6: 0 absent mod 59 quand ≡0 mod 5, ET reciproque
      k=10: 0 absent mod 499 quand ≡0 mod 13, ET reciproque
    - k=12 : AUCUNE paire ne bloque, besoin du triplet complet
    - Ordres multiplicatifs : N₀(p)=0 correle avec ord_p(2) grand
```

### AXE STRATEGIQUE 3 : Prouver l'Enonce A (ord_d(2) >= S)
```
PRIORITE : ★★★ (IMPORTANT mais pas bloquant pour Mec I)
OBJECTIF : Pour tout k >= 4, prouver ord_d(2) >= S

  *** REDUCTION CRITIQUE (session 8) ***
  ord_d(2) = S-1  <=>  d | (3^k - 2)
  Verifie : d ne divise JAMAIS 3^k - 2 pour k=4..35
  k=3 est le SEUL cas (d=5, 3^3-2=25=5*5)

  APPROCHE 1 : Argument arithmetique direct
    - d | (3^k - 2) => d <= 3^k - 2 < 3^k
    - Mais d = 2^S - 3^k, donc 2^S - 3^k <= 3^k - 2
    - i.e. 2^S <= 2*3^k - 2, mais 2^S >= 3^k (par def de S)
    - La condition est 2^S <= 2*3^k - 2, equivalente a theta <= log_2(2 - 2/3^k)
    - Pour grand k : theta < log_2(2) = 1, ce qui est TOUJOURS vrai
    - ==> L'argument de taille ne suffit PAS a exclure r=S-1

  APPROCHE 2 : Baker (formes lineaires de logarithmes)
    - |k*log(3) - S*log(2)| > exp(-C*log(k)*log(S))
    - Pour grand k : borne effective exclut d | (3^k - 2)
    - Pour petit k : verification directe (deja faite k=4..35)

  APPROCHE 3 : Exclure chaque r ∈ {1,...,S-2} individuellement
    - d | (2^r - 1) pour r < S-1 : argument de taille souvent fonctionne
    - Mais echoue pour ~50% des k (quand 2^{S-1} > d)
    - Combiner avec factorisation de d et ord_{p^e}(2)
```

### AXE STRATEGIQUE 4 : Double Peeling comme cadre unificateur
```
PRIORITE : ★★★ (CADRE CONCEPTUEL)
OBJECTIF : Formaliser pourquoi Forward et Backward ne se connectent JAMAIS

  FAIT ETABLI :
    - N_0(d) = 0 prouve pour k=3..14 par 0 paires compatibles
    - SAT/SMT encoding (3 approches) confirme UNSAT k=3..12+
    - Meme avec 3522 etats communs (k=14), ZERO positions compatibles

  PISTE : Les positions centrales sont "doublement occupees"
    - Forward depuis c_0=1 consomme les petites positions d'abord
    - Backward depuis c_{k-1}=0 consomme les grandes positions d'abord
    - Au point de RDV, les positions forward et backward se CHEVAUCHENT
    - Argument entropique : chaque vague couvre > S/2 positions

  LIEN AVEC LES 3 MECANISMES :
    - Le Double Peeling CAPTURE les 3 mecanismes dans un cadre unique
    - Pour d premier : incompatibilite = prime blocking reformule
    - Pour d compose : incompatibilite = CRT anti-correlation reformulee
    - La preuve du DP formaliserait les 3 mecanismes d'un coup
```

### HIERARCHIE DES PISTES (mise a jour session 10e4)
```
NOUVELLE HIERARCHIE (par impact et faisabilite) :

  (1) ★★★★★ PRIME BLOCKING FORMEL — SOUS-CAS σ̃≠0 (Mec I, cas principal)
      Impact : prouve N_0(p)=0 pour TOUS les k avec d premier et σ̃≠0
      Faisabilite : TRES AVANCEE (session 10e4)
        - Image creuse C(M+k-1,k-1) < p (verifie k=4,13)
        - Backward chain TOTALEMENT exclue de Im(f)
        - Preuves completes k=3,4,5 par debordement (min(max(B)) > M)
        - k=13 : backward chain exclue (computationnel)
        - MANQUE : preuve formelle overflow pour k ARBITRAIRE
      Dependance : aucune
      → CAS PRINCIPAL, PRIORITE ABSOLUE

  (1b) ★★★★ PRIME BLOCKING — SOUS-CAS σ̃=0 (Mec I, k=3,5 seulement ?)
      Impact : complete le cas d premier quand σ̃(u) = 0
      Faisabilite : PROUVE (session 10e4)
        - THEOREME : σ̃=0 ⟹ u = 2^{-M} mod p
        - Bandes d'exposants disjointes, (k-1)M = ord₂(p)
        - k=3 : preuve explicite (violation non-decroissance)
        - k=5 : preuve explicite (0 combos contraintes donnent -1)
        - σ̃=0 avec d premier : SEULEMENT k=3,5 (teste k≤49)
      Dependance : aucune
      STATUS : ESSENTIELLEMENT COMPLET

  (2) ★★★★ CRT ANTI-CORRELATION FORMELLE (Mec II)
      Impact : complete le cas d compose
      Faisabilite : AVANCEE — anti-correlation QUANTIFIEE (session 9-10d)
        P(r2=0|r1=0) = 0 pour k=6..11 (verification exhaustive)
        Exclusion BI-DIRECTIONNELLE : target de chaque facteur exclu
        Mecanisme : poids w1^j != w2^j => directions "orthogonales"
        k=12 : paires insuffisantes, triplet requis (Mec III)
      Dependance : beneficie de (1)

  (3) ★★★ ENONCE A VIA BAKER (ord_d(2) >= S)
      Impact : renforce le gap algebrique (composante A du mecanisme)
      Faisabilite : HAUTE pour grand k (Baker), directe pour petit k
      Dependance : aucune, mais MOINS critique qu'initialement pense

  (4) ★★★ DOUBLE PEELING FORMEL
      Impact : preuve unifiee si formalisable
      Faisabilite : DIFFICILE — pourquoi les positions ne matchent jamais ?
      Dependance : pourrait subsumer (1) et (2)

  (5) ★★ VERIFICATION ETENDUE
      Impact : extension a k=15..25+
      Faisabilite : HAUTE (computationnelle)
      Dependance : aucune

  PISTES FERMEES (session 8) :
    - Invariant universel mod m : FERME (Front 4, aucun au-dela mod 2+3)
    - Argument de taille simple (2^r < d) : FERME (~50% k echouent)
    - Matrice de transfert spectrale : FERME (difficulte equivalente)
    - Enonce C comme lemme isole : FERME (equivalent a N_0(d)=0 restreint)
    - "Gros premier bloque toujours" : REFUTE (k=6,9,10,12,14-16)
```

### Vision long terme
```
STRATEGIE EN 5 PILIERS (mise a jour session 8) :

  Pilier 1 : DEFICIT ENTROPIQUE (k >= 18, deja prouve: C < d)
    ==> N_0(d) = 0 est GENERIQUE pour grand k
    Statut : COMPLET

  Pilier 2 : PRIME BLOCKING FORMEL (Mec I) — EN COURS (session 9)
    ==> Reformule : -1 ∉ Image(Sum w^j*2^{sort(S)_j}) pour d premier
    ==> Preuve k=3 COMPLETE (3 solutions algebriques, toutes incompatibles)
    ==> SANS ORDRE : -1 apparait => ordre strict est le mecanisme
    ==> Anti-concentration parfaite quand C/p > 1.2
    ==> sigma(u) = Sum u^j != 0 (necessaire, verifie)
    ==> u^k = 2^{k-S} (identite universelle de cloture)
    Statut : FORMALISE, preuve generale en cours

  Pilier 3 : CRT ANTI-CORRELATION (Mec II) — EN COURS (session 9)
    ==> Matrice CRT : M[0][0] = 0 pour k=6..11
    ==> P(r2=0|r1=0) = 0 (exclusion bi-directionnelle)
    ==> Mecanisme : poids w1^j != w2^j creent directions orthogonales
    ==> Morphisme phi : compositions -> Z/p1Z x Z/p2Z, (-1,-1) ∉ Image
    Statut : QUANTIFIE, preuve generale en cours

  Pilier 4 : ENONCE A (ord_d(2) >= S pour k >= 4) via Baker
    ==> Renforce le gap algebrique pour les 3 mecanismes
    ==> Reduit a : d ne divise pas (3^k - 2) (verifie k=4..35)
    Statut : REDUIT, VERIFICATION ETENDUE

  Pilier 5 : VERIFICATION COMPUTATIONNELLE
    ==> Double Peeling : N_0(d) = 0 pour k=3..14 (positions incompatibles)
    ==> SAT/SMT : 3 approches confirment UNSAT k=3..12+
    ==> regression_test.py : 110/110 tests passent
    Statut : COMPLET pour k<=14, extensible

  *** OBJECTIF FINAL ***
  Combiner Piliers 1-4 pour couvrir TOUT k >= 3 :
    - Grand k (>= 18) : Pilier 1 (deficit entropique)
    - k moyen (4..17) avec d premier : Pilier 2 (prime blocking)
    - k moyen (4..17) avec d compose : Pilier 3 (CRT anti-correlation)
    - k = 3 : cas special (ord=S-1, mais contrainte d'ordre bloque)
    - Verification : Pilier 5 pour tout k <= 14+
    - Renforcement : Pilier 4 (Enonce A) comme outil transversal
```
