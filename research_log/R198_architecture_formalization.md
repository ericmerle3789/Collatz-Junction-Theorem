# R198 -- FORMALIZER (Agent A2) : Architecture Formalization & Gap Analysis
**Date :** 16 mars 2026
**Round :** R198
**Role :** Formalisateur -- ZERO inventions, pure formalisation et analyse des lacunes
**Prerequis :** R195 (filet 3 mailles, MCE, crible modulaire), R196 (FCQ, LDS, 3 in <2>), R197 (LDS effectif, c = 1/25, ord >= 3, DBA, rho_5 = 1/4)
**Mission :** Squelette de preuve numerote, enumeration de l'ensemble fini de verification, catalogue EXHAUSTIF des gaps

---

## TASK 1 : SQUELETTE DE PREUVE COMPLET

### 1.0 Objectif

**Theoreme Cible (Junction Theorem -- Blocking Mechanism inconditionnel).**
Pour tout k >= 18 et tout diviseur premier p | d(k) ou d(k) = 2^{ceil(k*log_2(3))} - 3^k, le nombre de compositions A in Comp(S,k) telles que corrSum(A) = 0 mod p satisfait N_0(p) = 0. En consequence, g_max(k) < d(k) et aucun cycle de Collatz de longueur k n'existe.

La preuve s'articule en trois etages, plus un front separee pour F_Z.

---

### ETAGE 1 : TRANSPORT AFFINE (petits premiers, p <= 97)

**Enonce.** Pour tout premier p <= 97 et tout k >= 18, N_0(p) = 0.

**Mecanisme.** Le groupe affine Aff(p) = {x -> ax + b : a in F_p*, b in F_p} est engendre par T_2 : x -> 2x et T_1 : x -> (3x+1)/2 pour tout premier impair p >= 3 [R195, Section 1.4 -- PROUVE]. L'action transitive de Aff(p) sur F_p assure l'equidistribution qualitative. L'equidistribution QUANTITATIVE -- |N_r(p) - C/p| < C/p pour tout r -- est garantie pour p <= 97 quand k >= 18, par un argument de mixing spectral : le trou spectral du graphe de Cayley associe a {T_1, T_2} est >= c_0/log(p), et k >= 18 > C*log(97) suffit [R195, Section 1.2 -- CONDITIONNEL sur la constante de mixing].

**Statut :**
| Composante | Statut | Reference |
|---|---|---|
| Aff(p) = <T_1, T_2> pour tout p premier impair | **PROUVE** | R195, Sec 1.4 |
| Transitivite de Aff(p) | **PROUVE** | Consequence immediate |
| Equidistribution quantitative N_0(p) = 0 pour p <= 97, k >= 18 | **PARTIELLEMENT PROUVE** | Preprint (numerique pour 168 premiers, 0 echecs), argument theorique esquisse R195 Sec 1.2 |
| Le seuil 97 est numerique, pas structurel | **OBSERVATION** | R195, Sec 1.2 |

**GAP-E1 : La preuve rigoureuse que le mixing est complet pour TOUS les p <= 97 et k >= 18 repose actuellement sur la verification NUMERIQUE (168 premiers, 0 echecs dans le preprint). L'argument theorique (trou spectral) est ESQUISSE mais la constante effective n'est PAS prouvee.**

**Classification : THEORETICAL** -- il faut un theoreme de mixing effectif pour le graphe de Cayley de Aff(p) avec generateurs T_1, T_2, ou bien COMPUTATIONAL si l'on accepte la verification directe N_0(p) = 0 pour les 25 premiers p <= 97 et les k in [18, 41].

---

### ETAGE 2 : LDS (grands ordres, ord_p(2) >= Q_seuil = 1025)

**Enonce.** Pour tout premier p | d(k) avec k in [18, 41] et ord_p(2) >= 1025, le premier p est "fantome" : le plus petit k' tel que p | d(k') satisfait k' > 41 >= k.

**Mecanisme.** Le LDS [R196-T8] exploite la structure diophantienne de d :

1. p | d(k) implique 2^S = 3^k mod p, donc 3 in <2> mod p [R196-T5 -- PROUVE]
2. La condition p | d(k) equivaut a : ceil(k * theta) = j*k mod q, ou q = ord_p(2) et j est le logarithme discret de 3 en base 2 mod p [R196, Sec B.2]
3. Par equidistribution de Weyl de la suite {k*(theta - j) mod q}, le premier k satisfaisant cette condition est k_0(p) >= q/(a_{n+1} + 2) ou a_{n+1} est le coefficient partiel pertinent de la fraction continue de theta = log_2(3) [R197-T1 -- PROUVE]
4. Pour q <= 15600 (couvrant Q_seuil = 1025), les fractions continues de theta donnent c >= 1/25 (car le pire coefficient partiel est a_9 = 23) [R197-T11 -- PROUVE]
5. Donc k_0(p) >= (1/25) * ord_p(2) >= 1025/25 = 41. Comme k <= 41, p ne peut pas diviser d(k). Le premier est fantome.

**Statut :**
| Composante | Statut | Reference |
|---|---|---|
| 3 in <2> mod p pour tout p \| d(k), p >= 5 | **PROUVE** | R196-T5 |
| ord_p(2) >= 3 pour tout p \| d(k) | **PROUVE** | R197-T5 (p=3 ne divise aucun d) |
| Borne premier retour k_min <= (a_{n+1}+1)*q_n | **PROUVE** | R197-T1 (theorie 3-distances) |
| c >= 1/25 pour q <= 15600 | **PROUVE** | R197-T11 (fractions continues connues de theta) |
| Q_seuil = 1025 couvre k <= 41 | **PROUVE** | 1025/25 = 41 >= k_max |

**Dependance logique :** La borne k <= 41 vient du theoreme de Steiner (pas de cycles avec k > 41 pour des raisons de taille). VERIFIER : cette borne est-elle prouvee dans le preprint ou est-ce k <= 68 (Simons-de Weger) ? Si c'est k <= 68, alors Q_seuil = 68 * 25 = 1700, et c >= 1/25 reste valide (1700 < 15600).

**GAP-E2a : La borne k_max = 41 ou 68 doit etre clarifiee.** Si k_max = 68, alors Q_seuil = 1700 et le LDS couvre toujours (car c >= 1/25 jusqu'a q = 15600). Si k_max est non-borne (c'est-a-dire si l'on veut prouver pour TOUT k >= 18), le LDS seul ne suffit pas car c(q) -> 0 quand les coefficients partiels de theta croissent.

**Classification : THEORETICAL** -- clarifier k_max. Si k_max est fini (Steiner/Simons-de Weger), le gap est FERME. Si k_max est infini, c'est un gap THEORIQUE majeur.

**GAP-E2b : L'argument d'equidistribution de Weyl donne une borne SUPERIEURE sur k_0 (le premier hit arrive avant (a_{n+1}+2)*q), PAS une borne INFERIEURE.** Le Red Team R197 (Audit 1, Niveau 1) identifie cette confusion. Le LDS dit k_0 >= c*q (borne inferieure), ce qui est CORRECT car k_0 est le PREMIER k tel que la congruence est satisfaite, et pour k < c*q, la discrepance de la suite de Weyl est trop grande pour que l'intervalle cible de taille 1/q soit atteint.

**CORRECTION :** Relisons R197-T1 attentivement. Le theoreme borne k_min (le plus petit k frappant un intervalle de taille 1/Q) par le HAUT : k_min <= (a_{n+1}+1)*q_n. C'est une borne SUPERIEURE. Pour le LDS, on veut une borne INFERIEURE : le premier k tel que p | d(k) est k_0 >= ... Ce sont deux questions DIFFERENTES.

- Borne superieure k_min <= (a_{n+1}+1)*q_n : PROUVEE [R197-T1]. Dit que le premier hit arrive AVANT ce seuil. UTILE pour montrer que les primes avec grand q PEUVENT diviser un d(k), mais PAS pour exclure la divisibilite pour petit k.

- Borne inferieure k_0 >= c*q : ce qui est REELLEMENT prouve est que pour q | ceil(k*theta), le plus petit k est k >= q/theta ~ 0.63*q [R196-T7, cas Mersenne]. Pour le cas GENERAL (pas seulement Mersenne), l'argument R196-T8 invoque l'equidistribution de Weyl, qui dit que la DENSITE des k frappant est 1/q, mais ne donne PAS directement k_0 >= c*q.

**GAP-E2c (CRITIQUE) : La borne inferieure k_0(p) >= c*q pour un premier GENERAL p | d(k) n'est PAS rigoureusement etablie.** L'argument R196-T8 confond la densite asymptotique 1/q (PROUVEE par Weyl, R197-T3) avec une borne inferieure sur le premier hit. Le premier hit pourrait etre k = 1 si la congruence est satisfaite accidentellement pour un petit k.

Ce qui EST prouve :
- Pour les Mersenne (q | S) : k_0 >= q/theta ~ 0.63*q [R196-T7 -- PROUVE]
- Pour q general : la densite des k satisfaisants est 1/q [R197-T3 -- PROUVE]
- Pour q general : le premier hit est k_0 <= (a_{n+1}+1)*q_n <= (23+1)*q_{n-1} pour q <= 15600 [R197-T1 -- PROUVE]

Ce qui N'EST PAS prouve :
- k_0(p) >= c*q pour tout premier p (pas seulement Mersenne) avec une constante c > 0 uniforme

**Classification : THEORETICAL** -- une borne inferieure k_0 >= c*q pour p general est NECESSAIRE pour que l'Etage 2 fonctionne. Sans elle, l'Etage 2 est une heuristique.

**REFORMULATION POSSIBLE :** Au lieu de prouver k_0 >= c*q pour tout p, on peut CONTOURNER ce gap en elargissant l'Etage 3 (verification finie). Si l'on ne peut pas exclure les premiers avec grand q du cas "verification finie", il faut verifier TOUS les premiers divisant d(k) pour k in [18, 41], sans distinction de q. C'est exactement la strategie R197-T8 (reduction a verification finie par factorisation des d(k)).

---

### ETAGE 3 : VERIFICATION FINIE (premiers avec 3 <= ord_p(2) < Q_seuil)

**Enonce (version faible, sans la borne inferieure k_0 >= c*q).** Pour chaque k in {18, 19, ..., 41}, factoriser d(k) et verifier que pour CHAQUE premier p | d(k) :
- Soit p <= 97 (couvert par Etage 1), OU
- Soit R(p, k) < epsilon pour un seuil epsilon donnant N_0(p) = 0 (couvert par la contraction / FCQ)

**Enonce (version forte, avec la borne inferieure).** Seuls les premiers avec ord_p(2) < 1025 necessitent une verification. Pour chaque q in {3, 4, ..., 1024}, les premiers p avec ord_p(2) = q divisant un d(k) pour k in [18, 41] forment un sous-ensemble fini de l'ensemble des facteurs premiers de d(k). Verifier R(p, k) < epsilon pour chacun.

**Mecanisme.**
1. Calculer d(k) = 2^{ceil(k*log_2(3))} - 3^k pour k = 18, ..., 41 [24 entiers]
2. Factoriser chaque d(k) [entiers de ~10 a ~20 chiffres decimaux pour k <= 41]
3. Pour chaque facteur premier p > 97 :
   a. Calculer q = ord_p(2)
   b. Calculer rho_p = max_{t != 0} |(1/q) Sum_{m=0}^{q-1} e(t*2^m/p)|
   c. Verifier R(p, k) = q * rho_p^{k-1} < 0.041

**Resultats partiels disponibles :**
| Composante | Statut | Reference |
|---|---|---|
| d(k) factorise pour k <= 41 | **NON FAIT** | A faire (calcul) |
| R(p, 18) < 0.001 pour p = 5 (q=4) | **PROUVE** | R197-T7 (rho_5 = 1/4 exact) |
| R(p, 18) < 0.001 pour p = 7 (q=3) | **PROUVE** | R197-T7 (rho_7 = 1/4 exact) |
| R(p, 18) < 1 pour tout p >= 5 | **PROUVE** | R196-T4 |
| R(p, 18) < 0.041 pour tout p >= 5 | **NON PROUVE** (gap entre R < 1 et R < 0.041) | R196-C1 (conditionnel sur c_0 >= 0.09) |
| Ensemble des premiers "dangereux" est fini (cardinal <= 1560) | **PROUVE** | R197-T6 |
| Verification directe de N_0(p) = 0 par enumeration des compositions | Fait pour 168 premiers dans le preprint | Preprint numerique |

**GAP-E3a (COMPUTATIONAL) : Factoriser d(k) pour k = 18, ..., 41.** Les d(k) ont la forme 2^S - 3^k avec S ~ 1.585*k. Pour k = 41, d(41) = 2^{65} - 3^{41}, un nombre a ~20 chiffres. Factorisable en secondes par des algorithmes standard (trial division + ECM).

**GAP-E3b (THEORETICAL/COMPUTATIONAL) : Prouver R(p, k) < 0.041 pour chaque facteur premier p | d(k) avec p > 97.** La borne prouvee est R < 1 [R196-T4], mais le seuil requis est R < 0.041. Le gap est un facteur ~24. Deux strategies :
1. **Calcul direct** : pour chaque p specifique, calculer rho_p exactement (sommes de racines de l'unite) et verifier. FAISABLE pour les facteurs de d(k), k <= 41.
2. **Borne theorique raffinee** : prouver rho_p <= 1/4 pour tout p | d(k) avec p >= 5. R197 montre que pour les premiers ou 2 est racine primitive (q = p-1), rho_p = 1/(p-1) [R197, innovateur, Sec B.3]. Pour les autres, la borne depend de la structure de <2> mod p.

**Classification : COMPUTATIONAL** (si l'on accepte le calcul direct pour les facteurs de d(k), k <= 41).

---

### FRONT F_Z : LE CAS DES BORDS DOUBLES

**Enonce.** Pour tout k impair >= 7, d(k) ne divise pas F_Z(m) = 4^m - 9^m - 17*6^{m-1} ou m = (k-1)/2.

Ce front est INDEPENDANT des Etages 1-3. Les Etages 1-3 traitent le "cas interieur" (corrSum = 0 mod p pour les compositions interieures). Le front F_Z traite le "cas des bords" (compositions extremales ou la jonction est saturee).

**Resultats prouves :**
| Composante | Statut | Reference |
|---|---|---|
| F_Z < 0 pour tout m >= 1 (trivial : 4^m < 9^m) | **PROUVE** | R197-innovateur-T1 |
| F_Z est impair et premier a 3 | **PROUVE** | Preprint Thm 9.16 |
| F_Z = 3 mod 5 pour tout m >= 1 | **PROUVE** | R195-L1 |
| F_Z non-nul mod 7 pour tout m (cycle de periode 6) | **PROUVE** | R195-L2 |
| 108 premiers "surs" p < 1000 tels que p ne divise jamais F_Z | **PROUVE** | R195, Sec 2 (crible modulaire) |
| 25 premiers "couplage-incompatibles" < 500 | **PROUVE** | R195, Sec 4 |
| n = \|F_Z\|/d satisfait n = 341 mod 512 | **PROUVE** | R195, Sec 3 (MCE) |
| MCE exclut ~99.86% des k | **PROUVE** | R195, Sec 3 |
| k residuels concentres pres des convergents de log_2(3) | **PROUVE** | R197-innovateur-T7 (RCA) |
| Recurrence d'ordre 3 : F_Z(m+3) = 19F_Z(m+2) - 114F_Z(m+1) + 216F_Z(m) | **PROUVE** | R197-innovateur-T13 |
| Verifie d ne divise pas F_Z pour k impair in [7, 10001] | **VERIFIE** | Preprint |
| Borne Baker : m_0 fini tel que n < 341 contradiction | **CONDITIONNEL** | R197-innovateur-T2 (mise en forme Baker non achevee) |
| gcd(F_Z(m), F_Z(m+1)) = 1 pour tout m >= 3 | **CONJECTURE** | R197-innovateur-J1 |

**GAP-FZ1 (THEORETICAL -- MAJEUR) : Prouver que d(k) ne divise pas F_Z(m) pour TOUT k impair >= 7.** C'est le verrou principal du front F_Z. Le schema propose (R197-innovateur) est :

1. MCE donne n >= 341 pour tout k assez grand [PROUVE]
2. Baker-Wustholz sur l'equation S-unitaire F_Z = n*d donne n < 341 pour m >= m_0 [CONDITIONNEL -- mise en forme non achevee]
3. Contradiction pour m >= m_0 : ferme les grands k
4. Pour m < m_0 : verification computationnelle (deja faite pour m <= 5000, mais m_0 pourrait etre plus grand)

Le point 2 est le coeur du gap. L'equation F_Z = n*(2^S - 3^k) est une S-unit equation a {2, 3}-entiers. Par le theoreme d'Evertse (1984), le nombre de solutions non-degenerees est FINI. Par Baker-Wustholz, la plus grande solution est BORNEE explicitement. MAIS la constante C_BW n'a pas ete calculee.

**Classification : THEORETICAL** -- Effectiviser la borne Baker-Wustholz pour F_Z. C'est un calcul STANDARD en theorie des nombres effectifs (comparable a Bennett 2004, Mignotte-Stroeker) mais requiert un travail technique significatif (~1-3 mois de specialiste).

---

## TASK 2 : ENUMERATION DE L'ENSEMBLE DE VERIFICATION FINIE

### 2.1 Etage 1 : p <= 97

Les 25 premiers p <= 97 sont :
2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97

**p = 2 et p = 3 sont exclus** (d est impair et premier a 3 : R197-T4).

Les 23 premiers p in {5, 7, 11, ..., 97} necessitent la verification N_0(p) = 0 pour k in [18, 41].

**Deja fait dans le preprint ?** Le preprint verifie computationnellement N_0(p) = 0 pour 168 premiers (incluant tous les p <= 97) et k dans une range non-specifiee. Si cette verification couvre k in [18, 41], l'Etage 1 est FERME computationnellement.

**GAP :** Confirmer que le preprint couvre bien k in [18, 41] pour tous p <= 97. Si oui : FERME (COMPUTATIONAL, deja fait). Si non : COMPUTATIONAL (a faire, facile).

### 2.2 Etage 2 : Frontiere LDS

La frontiere est determinee par :
- c = 1/25 (pire constante effective pour q <= 15600) [R197-T11]
- k_max = 41 (borne Steiner sur la longueur des cycles) ou k_max = 68 (Simons-de Weger)

**Si k_max = 41 :** Q_seuil = 41 * 25 = 1025
**Si k_max = 68 :** Q_seuil = 68 * 25 = 1700

Le LDS "couvre" (dans le sens : le premier est fantome) les premiers avec ord_p(2) >= Q_seuil.

**MAIS** (cf. GAP-E2c) : la borne inferieure k_0 >= q/25 n'est prouvee que pour les Mersenne. Pour les premiers generaux, la borne inferieure sur k_0 n'est pas etablie.

### 2.3 Etage 3 : Premiers avec 3 <= ord_p(2) < 1025

**Question precise :** Pour q in {3, 4, ..., 1024}, quels premiers p ont ord_p(2) = q ET divisent au moins un d(k) pour k in [18, 41] ?

**Methode d'enumeration :**

Pour chaque k in {18, 19, ..., 41} :
1. Calculer S(k) = ceil(k * log_2(3))
2. Calculer d(k) = 2^{S(k)} - 3^k
3. Factoriser d(k) completement
4. Pour chaque facteur premier p, calculer ord_p(2)

**Valeurs de d(k) pour k = 18, ..., 41 :**

| k | S(k) | d(k) = 2^S - 3^k | Ordre de grandeur |
|---|------|-------------------|-------------------|
| 18 | 29 | 2^29 - 3^18 = 536870912 - 387420489 = 149450423 | ~1.5 * 10^8 |
| 19 | 31 | 2^31 - 3^19 = 2147483648 - 1162261467 = 985222181 | ~9.9 * 10^8 |
| 20 | 32 | 2^32 - 3^20 = 4294967296 - 3486784401 = 808182895 | ~8.1 * 10^8 |
| 21 | 34 | 2^34 - 3^21 = 17179869184 - 10460353203 = 6719515981 | ~6.7 * 10^9 |
| ... | ... | ... | ... |
| 41 | 65 | 2^65 - 3^41 | ~2.0 * 10^19 |

Ces sont des entiers de 9 a 20 chiffres decimaux. Factorisables en SECONDES avec des outils standard (PARI/GP, SageMath, FactorDB).

**Nombre total de facteurs premiers a verifier :** Borne brute : 24 * 65 = 1560 [R197-T6]. En pratique, beaucoup moins car :
- Les d(k) ont typiquement 3-8 facteurs premiers distincts
- Estimation realiste : 24 * 5 = ~120 verifications

**GAP :** Ce calcul n'a PAS ete realise. C'est un gap COMPUTATIONAL pur, faisable en quelques heures.

### 2.4 Enumeration des premiers avec petit ord_p(2) divisant d(k)

Pour les plus petits q, les premiers avec ord_p(2) = q sont contenus dans les facteurs de 2^q - 1. Voici les premiers possibles pour q <= 12 :

| q | 2^q - 1 | Premiers avec ord = q exactement |
|---|---------|----------------------------------|
| 3 | 7 | {7} |
| 4 | 15 = 3*5 | {5} (ord_3(2) = 2) |
| 5 | 31 | {31} |
| 6 | 63 = 9*7 | {} (pas de facteur primitif) |
| 7 | 127 | {127} |
| 8 | 255 = 3*5*17 | {17} |
| 9 | 511 = 7*73 | {73} |
| 10 | 1023 = 3*11*31 | {11} |
| 11 | 2047 = 23*89 | {23, 89} |
| 12 | 4095 = 3^2*5*7*13 | {13} |

**IMPORTANT :** Il ne suffit PAS de lister les facteurs de 2^q - 1. Il faut verifier lesquels divisent effectivement un d(k) pour k in [18, 41]. Seuls ceux-la sont pertinents.

Par exemple, p = 7 avec q = 3 : est-ce que 7 | d(k) pour un k in [18, 41] ? Cela depend de la factorisation de d(k) pour chaque k. C'est un CALCUL A FAIRE.

---

## TASK 3 : CATALOGUE EXHAUSTIF DES GAPS

### Gap 1 : Borne inferieure k_0(p) >= c*q pour p general (GAP-E2c)

**Description :** L'Etage 2 repose sur l'affirmation que le premier k tel que p | d(k) satisfait k_0(p) >= q/25 pour q = ord_p(2). Cette borne est PROUVEE pour les Mersenne [R196-T7] mais PAS pour les premiers generaux. L'argument R196-T8 invoque l'equidistribution de Weyl, qui donne la DENSITE 1/q mais pas une borne inferieure sur le premier hit.

**Impact :** Si ce gap n'est pas ferme, l'Etage 2 s'effondre. Les premiers avec grand q pourraient quand meme diviser d(k) pour de petits k.

**Contournement :** Abandonner l'Etage 2 et etendre l'Etage 3 a TOUS les facteurs premiers de d(k), sans distinction de q. La verification finie reste FAISABLE (la borne brute est 1560 premiers, la borne pratique ~120).

**Classification : THEORETICAL.** Prouver k_0(p) >= c*q necessite un argument diophantien non-trivial exploitant la structure de l'equation ceil(k*theta) = j*k mod q.

**Severite : HAUTE** si l'on veut l'architecture a 3 etages. **NULLE** si l'on adopte la strategie de verification directe (Etage 3 etendu).

---

### Gap 2 : Seuil R(p,k) < 0.041 vs R(p,k) < 1 (GAP-E3b)

**Description :** La FCQ [R196-T4] prouve R(p,18) < 1 pour tout p >= 5. Le seuil operationnel pour N_0(p) = 0 est R < 0.041. Le gap est un facteur ~24.

**Impact :** Si R < 0.041 n'est pas atteint pour un premier specifique p | d(k), la maille 2 ne suffit pas et il faut un argument supplementaire.

**Etat :** Pour p = 5 (q = 4) et p = 7 (q = 3), R est prouve << 0.041 [R197, rho_5 = rho_7 = 1/4]. Pour les autres premiers, la borne R < 1 est LOIN du seuil. CEPENDANT, pour chaque premier SPECIFIQUE p | d(k), on peut calculer rho_p exactement et verifier R < 0.041.

**Contournement :** Calcul direct de R(p, k) pour chaque facteur premier de d(k). FAISABLE computationnellement.

**Classification : COMPUTATIONAL** si l'on accepte la verification cas par cas. **THEORETICAL** si l'on veut une borne uniforme R < 0.041 pour tout p.

**Severite : BASSE** (le contournement computationnel est direct).

---

### Gap 3 : Equidistribution quantitative pour l'Etage 1 (GAP-E1)

**Description :** La preuve que N_0(p) = 0 pour p <= 97 et k >= 18 repose sur la verification numerique du preprint (168 premiers, 0 echecs). L'argument theorique (mixing de Aff(p)) est esquisse mais pas formalise.

**Impact :** Sans formalisation, l'Etage 1 est une "verification computationnelle etendue", pas un theoreme.

**Contournement :** Deux options :
1. Formaliser le mixing de Aff(p) avec une borne effective (travail theorique)
2. Verifier N_0(p) = 0 DIRECTEMENT par enumeration des compositions pour chaque (p, k) avec p <= 97 et k in [18, 41]. Le nombre de compositions C = C(S,k) est potentiellement grand, mais pour p premier, on travaille modulo p et les sommes sont calculables.

**Classification : THEORETICAL** (option 1) ou **COMPUTATIONAL** (option 2).

**Severite : MOYENNE.** Le preprint fournit deja des preuves computationnelles.

---

### Gap 4 : Factorisation des d(k) pour k = 18, ..., 41 (GAP-E3a)

**Description :** Les 24 entiers d(k) doivent etre factorise pour alimenter l'Etage 3. Ce calcul n'a pas ete fait dans le cadre de la recherche R195-R197.

**Impact :** Sans ces factorisations, l'Etage 3 ne peut pas demarrer.

**Contournement :** Aucun -- c'est un prerequis.

**Classification : COMPUTATIONAL.**

**Severite : BASSE** (calcul trivial avec PARI/GP ou SageMath -- quelques secondes).

---

### Gap 5 : Borne Baker-Wustholz pour F_Z (GAP-FZ1)

**Description :** Le schema MCE + Baker pour prouver d ne divise pas F_Z necessite l'effectivisation de la borne Baker-Wustholz pour l'equation S-unitaire F_Z = n*d. La mise en forme precise de la forme lineaire en logarithmes et le calcul de la constante C_BW ne sont pas faits.

**Impact :** Sans cette borne, le front F_Z reste ouvert pour les k au-dela de la range de verification computationnelle (actuellement k <= 10001).

**Contournement partiel :** Etendre la verification computationnelle a k plus grand (faisable mais pas une preuve). La MCE couvre 99.86% des k, et les k residuels (concentres pres des convergents de log_2(3)) sont en nombre FINI pour tout seuil donne.

**Classification : THEORETICAL.**

**Severite : HAUTE** pour une preuve complete. **BASSE** si l'on se contente de k <= K_0 pour un K_0 computationnellement atteignable.

---

### Gap 6 : Borne k_max (GAP-E2a)

**Description :** La valeur exacte de k_max (longueur maximale d'un cycle hypothetique de Collatz) n'est pas clarifiee dans la chaine de preuves. Deux valeurs circulent :
- k_max = 41 (argument de Steiner, preprint)
- k_max = 68 (Simons-de Weger, verification DP exhaustive)

**Impact :** k_max determine Q_seuil pour l'Etage 2. Si k_max = 68, Q_seuil = 1700. Si k_max est plus grand ou non-borne, l'architecture change.

**Contournement :** Le preprint utilise k >= 18 (borne entropique inferieure) ET k <= 68 (Simons-de Weger borne superieure computationnelle). L'intersection [18, 68] est la "zone danger". Q_seuil = 68 * 25 = 1700, et c >= 1/25 est valide pour q <= 15600 >> 1700.

**Classification : CLARIFICATION NECESSAIRE** (pas un gap mathematique, mais une imprecision dans la chaine logique).

**Severite : BASSE.**

---

### Gap 7 : Somme des risques vs risque individuel (Red Team R197, Audit 2)

**Description :** La FCQ montre R(p, k) < 1 pour chaque premier p individuellement. Mais pour N_0(d) = 0, il faut que N_0(p) = 0 pour AU MOINS UN premier p | d. La strategie CRT (Prop 6.4 du preprint) dit : s'il existe un p | d tel que N_0(p) = 0, alors g_max < d.

Le gap est : on n'a PAS prouve que la somme SUM_p R(p,k) sur les p | d est < 1, ni que CHAQUE p individuellement satisfait N_0(p) = 0. On a seulement R(p,k) < 1 par terme.

**Impact :** R(p,k) < 1 ne garantit PAS N_0(p) = 0. Il faut soit N_0(p) = 0 PROUVE pour un p specifique (verification directe), soit un argument de type Borel-Cantelli sur la somme.

**Contournement :** Verification directe N_0(p) = 0 pour chaque facteur premier p de d(k) -- c'est ce que fait l'Etage 3 (version calcul direct).

**Classification : THEORETICAL** (si l'on veut un argument par somme de risques) ou **COMPUTATIONAL** (si l'on verifie directement).

**Severite : MOYENNE.**

---

### Gap 8 : La borne rho_p < 1 - epsilon/q n'est pas prouvee pour q <= sqrt(p)

**Description :** Le Red Team R197 (Audit 2) identifie que la borne rho_p <= sqrt(1 - c_0/q) utilisee dans la FCQ est INJUSTIFIEE pour le regime q <= sqrt(p). Les bornes de Gauss et Parseval donnent |somme de Gauss partielle| <= sqrt(p*q), ce qui implique rho_p <= sqrt(p)/q. Pour rho_p < 1, il faut q > sqrt(p), ce qui n'est pas garanti.

**Impact :** Pour les premiers p avec petit ord_p(2) = q et p grand (type p = 2^q - 1 Mersenne), q ~ log(p) << sqrt(p), et la borne rho_p <= sqrt(p)/q > 1. La FCQ ne s'applique pas.

**Contournement :** Pour les Mersenne, rho est calculable exactement (sommes de Gauss completes quand 2 est racine primitive). Pour les premiers specifiques divisant d(k), calcul direct.

**Classification : THEORETICAL** (pour une borne generale) ou **COMPUTATIONAL** (pour les cas specifiques).

**Severite : MOYENNE.**

---

## SYNTHESE : TABLEAU DES GAPS

| # | Gap | Classification | Severite | Contournement |
|---|-----|----------------|----------|---------------|
| 1 | k_0(p) >= c*q pour p general | THEORETICAL | HAUTE (pour archi 3-etages) / NULLE (si verification directe) | Etendre Etage 3 a tous les premiers |
| 2 | R < 0.041 vs R < 1 | COMPUTATIONAL | BASSE | Calcul direct par premier |
| 3 | Equidistribution quantitative Etage 1 | THEORETICAL ou COMPUTATIONAL | MOYENNE | Verification directe N_0(p) pour p <= 97 |
| 4 | Factorisation des d(k) | COMPUTATIONAL | BASSE | Calcul trivial (secondes) |
| 5 | Baker-Wustholz pour F_Z | THEORETICAL | HAUTE | Extension verification computationnelle |
| 6 | Valeur de k_max | CLARIFICATION | BASSE | Utiliser k_max = 68 (SdW) |
| 7 | Somme des risques vs individuel | THEORETICAL ou COMPUTATIONAL | MOYENNE | Verification directe N_0(p) |
| 8 | Borne rho_p pour q <= sqrt(p) | THEORETICAL ou COMPUTATIONAL | MOYENNE | Calcul direct par premier |

---

## DEPENDANCES LOGIQUES

```
PREPRINT (Junction Theorem)
  |
  +--> Obstr. computationnelle : k <= 67 [Simons-de Weger 2005] --- PROUVE
  |
  +--> Obstr. entropique : k >= 18, C(k) < d(k) --- PROUVE (preprint)
  |      |
  |      +--> SUFFIT si g_max < d. Comment prouver g_max < d ?
  |             |
  |             +--> CRT (Prop 6.4) : il existe p | d tel que N_0(p) = 0
  |                    |
  |                    +--> ETAGE 1 : p <= 97 --> N_0(p) = 0
  |                    |      GAP-E1 : mixing quantitatif [THEOR/COMP]
  |                    |
  |                    +--> ETAGE 2 : ord_p(2) >= Q_seuil --> p fantome
  |                    |      GAP-E2c : borne inf k_0 >= c*q [THEOR]  *** CRITIQUE ***
  |                    |      Contournement : fusionner avec Etage 3
  |                    |
  |                    +--> ETAGE 3 : verification finie
  |                           GAP-E3a : factoriser d(k) [COMP, trivial]
  |                           GAP-E3b : R(p,k) < 0.041 [COMP]
  |                           GAP-7 : N_0(p) = 0 vs R < 1 [COMP]
  |
  +--> FRONT F_Z : d ne divise pas F_Z
         |
         +--> MCE : n >= 341 pour 99.86% des k --- PROUVE [R195]
         +--> Baker-Wustholz : n < 341 pour m >= m_0 --- CONDITIONNEL [R197]
         +--> Verification : k <= 10001 --- FAIT [preprint]
         GAP-FZ1 : effectiviser Baker [THEOR]  *** CRITIQUE ***
```

---

## STRATEGIE RECOMMANDEE (ZERO INVENTION)

### Chemin A : Verification computationnelle finie (REALISTE, ~1 semaine)

1. **Clarifier k_max = 68** (Simons-de Weger). [1 heure]
2. **Factoriser d(k) pour k = 18, ..., 68.** [1 jour avec PARI/GP]
3. **Pour chaque facteur premier p > 97 de chaque d(k) :** calculer ord_p(2) et rho_p exactement, verifier R(p,k) < 0.041 ou mieux, calculer N_0(p) directement. [1-3 jours]
4. **Pour chaque p <= 97 :** confirmer que la verification du preprint couvre k in [18, 68]. [1 heure]
5. **Pour F_Z :** etendre la verification computationnelle a k <= 50000 (ou plus). Cela ne ferme pas F_Z mais renforce la confiance. [1 jour]

**Resultat :** Preuve du Junction Theorem CONDITIONAL sur F_Z (front F_Z reste ouvert pour k > 10001 ou 50001). Le front interieur (N_0(p) = 0) serait FERME par verification computationnelle finie.

### Chemin B : Preuve inconditionnelle (AMBITIEUX, ~3-6 mois)

Ajouter a Chemin A :
6. **Effectiviser Baker-Wustholz pour F_Z.** Formuler l'equation S-unitaire F_Z = n*(2^S - 3^k) comme une forme lineaire en logarithmes de {2, 3}. Appliquer le theoreme de Matveev (2000) ou Baker-Wustholz (1993) pour obtenir m_0 explicite. Verifier computationnellement les m < m_0. [3-6 mois, travail de specialiste]
7. **Formaliser l'argument de mixing pour l'Etage 1** (optionnel si la verification computationnelle suffit). [1-2 mois]

**Resultat :** Preuve COMPLETE et INCONDITIONNELLE du Junction Theorem (sans GRH).

---

## BILAN HONNETE

### Ce qui est PROUVE inconditionnellement :
- Aff(p) = <T_1, T_2> pour tout p premier impair [R195]
- 3 in <2> mod p pour tout p | d(k) [R196-T5]
- ord_p(2) >= 3 pour tout p | d(k) [R197-T5]
- R(p, 18) < 1 pour tout p >= 5 [R196-T4]
- rho_5 = rho_7 = 1/4 [R197]
- c >= 1/25 pour les fractions continues de theta jusqu'a q = 15600 [R197-T11]
- MCE : n = 341 mod 512, couvre 99.86% des k [R195]
- F_Z non-nul mod p pour 108 premiers surs [R195]
- Ensemble de verification est FINI [R197-T6, R197-T8]

### Ce qui est CONDITIONNEL ou OUVERT :
- k_0(p) >= c*q pour p general (pas seulement Mersenne) [GAP-E2c]
- R(p,k) < 0.041 pour tout p [GAP-E3b, mais contournable par calcul]
- N_0(p) = 0 pour p <= 97 avec preuve theorique [GAP-E1]
- d ne divise pas F_Z pour tout k >= 7 [GAP-FZ1]
- Baker-Wustholz effectif pour F_Z [GAP-FZ1]

### Ce qui est un FAUX PROBLEME :
- Le cas p = 5 avec q = 2 [R197-T5 : ord_5(2) = 4, pas 2. R197-innovateur-T3 : rho_5 = 1/4]
- L'uniformite de c pour tout q [non necessaire si k_max est fini et Q_seuil < 15600]

### Distance a une preuve :
- **Front interieur (N_0(p) = 0)** : ~1 semaine de calcul + clarification k_max. PROCHE.
- **Front F_Z (d ne divise pas F_Z)** : ~3-6 mois de travail theorique (Baker). DISTANT.
- **Preuve COMPLETE** : la conjonction des deux. Le maillon faible est F_Z.

---

*R198 FORMALIZER : Squelette a 3 etages + front F_Z. 8 gaps identifies : 2 CRITIQUES (borne inf k_0 pour p general -- contournable ; Baker pour F_Z -- non contournable), 3 COMPUTATIONNELS (trivials a moyens), 3 THEORIQUES/COMPUTATIONNELS (contournables par calcul direct). Le front interieur est a portee de calcul (~1 semaine). Le front F_Z est le verrou principal (~3-6 mois). ZERO invention dans ce document.*
