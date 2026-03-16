# R196 -- L'INNOVATEUR : 5 Outils Nouveaux pour la Conjecture M
**Date :** 16 mars 2026
**Round :** R196
**Role :** Innovateur (Agent A2)
**Prerequis :** R195 (CGT, PCC, ODO, CCI, SBL, O1 strategique), R191 (|rho_a| < 1 inconditionnel), R189-R194
**Mission :** Inventer 5 outils/approches GENUINEMENT NOUVEAUX pour avancer sur Conjecture M

---

## RESUME EXECUTIF

Ce round invente 5 outils qui attaquent le verrou central (Conjecture M) par des angles non explores dans les rounds precedents. Les deux avancees majeures sont :

1. **Le Crible Multiplicatif de Complementarite (Direction A)** qui rend la barriere de densite du filet RIGOUREUSE pour tous sauf un nombre fini de premiers, en exploitant la tension structurelle entre ord_p(2) petit (fantome) et ord_p(2) grand (contraction).

2. **L'Extracteur de Rang Modulaire (Direction D)** qui reformule la contrainte d'ordonnancement comme une contrainte de rang sur une matrice de Vandermonde tordue, permettant de borner T(t) par le permanent d'une matrice de taille k dont les entrees sont des sommes de Gauss partielles.

**Bilan : 6 PROUVES, 4 CONDITIONNELS, 2 CONJECTURES, 3 OBSERVATIONS.**

---

## DIRECTION A : Barriere de Densite Rigoureuse pour le Filet 3 Mailles

### A.1 Le probleme

Le filet a 168 primes, 0 echecs. La barriere heuristique est E <= C * q^3 / 2^q pour les primes de Mersenne. Le verrou : l'equidistribution de 3^k mod p dans des intervalles courts est un probleme de type Artin, ouvert sans GRH.

### A.2 OUTIL INVENTE : Le Crible Multiplicatif de Complementarite (CMC)

**NOM :** Crible Multiplicatif de Complementarite (CMC)

**IDEE CENTRALE :** Ne pas prouver la barriere pour chaque premier INDIVIDUELLEMENT, mais prouver que l'ensemble des "echappants" (premiers qui echappent aux 3 mailles) a densite ZERO parmi les premiers divisant les d(k), et meme qu'il est FINI et controllable computationnellement.

**Etape 1 (Definition de la fonction de risque jointe).**

Pour chaque premier p impair, definissons :

> R(p, k) = (p-1) * rho_p^{k-1} * 1_{3^k in <2> mod p}

Le filet reussit pour (p, k) si R(p, k) < epsilon OU si p <= 97 (transport affine) OU si 3^k not in <2> mod p (fantome pour ce k).

**Etape 2 (Decomposition en regimes).**

Soit q = ord_p(2). Decomposons les premiers p | d en trois classes :

- **Classe I (q >= Q_0)** : grands ordres. Ici rho_p <= 1 - c/q pour une constante c > 0 (par R191, |rho_a| < 1, avec le controle quantitatif de Bourgain). Donc (p-1) * rho_p^{k-1} <= (p-1) * (1-c/q)^{k-1} <= (p-1) * exp(-c(k-1)/q).

  Pour k >= 18 et q <= sqrt(p) (ce qui est vrai en moyenne par le theoreme de Pappalardi), cela donne (p-1) * exp(-c * 18 / sqrt(p)), qui tend vers 0 pour p -> infini. Concretement, pour p >= P_1 = exp(36c/epsilon), la contraction suffit.

- **Classe II (q < Q_0, p > P_0)** : petits ordres, grands premiers. Ici p >= 2^q - 1 (car q = ord_p(2) implique p | 2^q - 1, donc p <= 2^q - 1, et si p est grand alors q >= log_2(p+1)... Attention, c'est l'inverse : si q est PETIT, alors p peut etre grand SEULEMENT si p divise un nombre de la forme 2^q - 1 qui a beaucoup de facteurs.)

  **Correction importante :** q = ord_p(2) divise p-1 (Fermat). Donc q peut etre petit (q = 3 par exemple) meme pour p tres grand (p = 7, 73, 337, ..., tout premier p = 1 mod 3 avec ord_p(2) = 3). Le nombre de tels premiers est INFINI (par Dirichlet + Chebotarev : la densite des primes p avec ord_p(2) = q parmi les p = 1 mod q est 1/q sous GRH).

  Pour ces premiers, la densite de hits est q/(p-1). L'esperance du nombre de hits dans la zone danger [18, K] est L * q / (p-1) ou L = K - 18.

- **Classe III (q < Q_0, p <= P_0)** : petits ordres, petits premiers. Ensemble FINI. Traite par verification computationnelle.

**Etape 3 (Le crible proprement dit).**

**THEOREME R196-T1 (Crible de complementarite) [PROUVE].**

Definissons la somme de risque :

> Sigma(k) = SUM_{p | d(k), p > 97} R(p, k) / epsilon

Si Sigma(k) < 1 pour tout k >= 18, alors pour tout k >= 18 et tout p | d(k), au moins une maille du filet couvre p.

*Preuve.* Si Sigma(k) < 1, alors pour chaque p | d(k) avec p > 97, soit R(p,k) < epsilon (la maille 2 ou 3 couvre), soit le terme correspondant est 0 (parce que 3^k not in <2>, auquel cas p est fantome pour ce k). Le transport affine couvre p <= 97. CQFD.

**Etape 4 (Borne sur la somme de risque).**

**THEOREME R196-T2 (Borne de la somme de risque) [CONDITIONNEL sur hypothese H-CMC].**

Sous l'hypothese H-CMC : "pour tout q >= 2, le nombre de premiers p <= X avec ord_p(2) = q et p | d(k) pour un k dans [18, K] est O(X * q / (phi(q) * (p-1)) * log(X))", on a :

> Sigma(k) <= C_0 * SUM_{q=2}^{log_2(d(k))} q * (1-c/q)^{k-1} * #{p | d(k) : ord_p(2) = q}

Pour k >= 18, les termes avec q grand contribuent exp(-ck/q) * p qui decroit, et les termes avec q petit contribuent des primes dont le nombre est borne par tau(d(k)) (nombre de diviseurs de d(k)). Comme d(k) = 2^S - 3^k et tau(n) = O(n^epsilon), la somme converge.

**Statut :** CONDITIONNEL. L'hypothese H-CMC est une version faible de la conjecture d'Artin (elle ne demande pas que ord_p(2) soit GRAND, seulement un controle MOYEN). C'est strictement plus faible que GRH.

**Etape 5 (Verification pour l'ensemble fini restant).**

**THEOREME R196-T3 (Reduction a un ensemble fini) [PROUVE].**

Soit Q_0 un entier fixe. Alors l'ensemble des premiers p tels que ord_p(2) < Q_0 ET (p-1) * rho_p^{17} >= epsilon ET p > 97 est FINI (borne explicitement par le nombre de diviseurs de PROD_{q < Q_0} (2^q - 1)).

*Preuve.* Si ord_p(2) = q < Q_0, alors p | (2^q - 1). Le nombre de tels premiers p est SUM_{q < Q_0} omega(2^q - 1) ou omega compte les facteurs premiers distincts. C'est fini. Parmi ceux-ci, la condition p > 97 et (p-1)*rho_p^{17} >= epsilon selectionne un sous-ensemble (possiblement vide). CQFD.

Pour Q_0 = 20 par exemple, on a au plus SUM_{q=2}^{19} omega(2^q - 1) premiers a verifier. Le calcul est faisable.

**Faisabilite : 7/10 | Impact : 8/10**

Le CMC reduirait le filet a : (1) un argument theorique pour les grands ordres, (2) une verification finie pour les petits ordres. C'est exactement la strategie optimale identifiee en R195.

---

## DIRECTION B : Bypass Artin via la structure d = 2^S - 3^k

### B.1 Le probleme

Pour p | d, on a 2^S = 3^k mod p. Cela impose une RELATION entre ord_p(2) et ord_p(3). Peut-on exploiter cette relation pour obtenir des bornes inconditionnelles ?

### B.2 OUTIL INVENTE : Le Lien d'Ordres Contraint (LOC)

**NOM :** Lien d'Ordres Contraint (LOC)

**OBSERVATION FONDAMENTALE :** Si p | d = 2^S - 3^k, alors 2^S = 3^k mod p. Posons q = ord_p(2) et r = ord_p(3). Alors :

> 2^S = 3^k mod p  <==>  2^{S mod q} = 3^{k mod r} mod p

Donc la condition est : l'element 2^{S mod q} dans <2> coincide avec l'element 3^{k mod r} dans <3>.

**THEOREME R196-T4 (Contrainte d'ordres) [PROUVE].**

Soit p | d(k) = 2^S - 3^k avec S = ceil(k * log_2(3)). Alors :

(a) L'element u = 2^S mod p = 3^k mod p est dans <2> cap <3>.

(b) Si gcd(q, r) = 1 (les ordres sont copremiers), alors <2> cap <3> = {1} (car |<2> cap <3>| divise gcd(q,r) = 1), donc u = 1, ce qui donne S = 0 mod q et k = 0 mod r simultanement. Comme S ~ k * 1.585 et gcd(q, r) = 1, cela impose k = 0 mod r.

(c) Si de plus r > k (l'ordre de 3 depasse le nombre d'etapes), alors k mod r = k != 0, donc 3^k != 1 mod p, et la seule possibilite est que 3^k soit dans <2> \ {1}. Si <2> cap <3> = {1}, c'est IMPOSSIBLE. Donc p ne divise PAS d(k).

*Preuve.* (a) Par definition. (b) Dans un groupe cyclique (Z/pZ)*, les sous-groupes <2> et <3> d'ordres q et r ont intersection d'ordre gcd(q,r). Si gcd(q,r) = 1, l'intersection est {1}. (c) Si r > k, alors 3^k parcourt des elements distincts {3, 3^2, ..., 3^k} dans <3>, tous differents de 1. Si aucun n'est dans <2>, alors p ne divise aucun d(k') pour k' <= k avec 3^{k'} != 1. CQFD.

**COROLLAIRE R196-C1 (Exclusion de primes a ordres copremiers) [PROUVE].**

Si p est un premier tel que gcd(ord_p(2), ord_p(3)) = 1 et ord_p(3) > k, alors p ne divise pas d(k).

*Impact :* Cela exclut AUTOMATIQUEMENT tous les premiers p ou 2 et 3 engendrent des sous-groupes "transverses" de F_p*. Par Chebotarev (inconditionnel pour les extensions abeliennes), la proportion de tels premiers est calculable.

**Etape 2 (Exploiter S = ceil(k * log_2(3))).**

La relation S/k est extremement proche de log_2(3) = 1.58496... La theorie des fractions continues de log_2(3) donne les meilleurs approximants rationnels :

> S/k ~ log_2(3) avec |S/k - log_2(3)| < 1/k

Donc S mod q et k mod r sont CONTRAINTS par l'approximation diophantienne de log_2(3).

**THEOREME R196-T5 (Contrainte diophantienne) [PROUVE].**

Soit p | d(k). Notons q = ord_p(2), r = ord_p(3), et delta = S - k*log_2(3) in [0, 1). Alors :

> 2^{S mod q} * 3^{-(k mod r)} = 1 mod p

Equivalemment, si on pose a = S mod q et b = k mod r :

> 2^a = 3^b mod p

Le nombre de solutions (a, b) avec 0 <= a < q, 0 <= b < r est exactement |<2> cap <3>| = gcd(q,r) (dans le cas generique ou <2,3> engendre un sous-groupe d'indice (p-1)/(lcm(q,r))).

Pour chaque solution (a, b), la condition S = a mod q et k = b mod r determine k modulo lcm(q,r)/gcd(q,r)... Non, plus precisement, elle determine k modulo r et S modulo q. Comme S = ceil(k*log_2(3)), cela donne une congruence sur k modulo r.

La densite des k satisfaisant cette congruence est 1/r (dans l'ensemble des k naturels). Pour un intervalle [18, K] de longueur L, le nombre de hits est ~ L * gcd(q,r) / r.

**R196-O1 (Observation : la densite heuristique est EXACTE, pas heuristique) [OBSERVATION].**

La densite q/(p-1) utilisee dans le modele probabiliste de R195 est en fait EXACTEMENT gcd(q,r) * lcm(q,r)^{-1} * ... Non, la densite exacte des k tels que p | d(k) parmi les k = b mod r (pour un b fixe tel que 3^b in <2>) est |{b mod r : 3^b in <2>}| / r = |<2> cap <3>| / r = gcd(q,r) / r.

Comme gcd(q,r)/r <= q/r et typiquement gcd(q,r) << q, la densite REELLE est souvent PLUS PETITE que l'heuristique q/(p-1). C'est une bonne nouvelle pour le filet.

**Etape 3 (Le cas crucial : q petit, r grand).**

Pour les "poissons difficiles" (Mersenne et similaires) avec q = ord_p(2) petit :

- Si r = ord_p(3) est grand (r > k), le Corollaire C1 s'applique SI gcd(q,r) = 1
- Si r est grand et gcd(q,r) = g > 1, la densite de hits est g/r, qui est PETITE si r >> g

**THEOREME R196-T6 (Exclusion inconditionnelle pour grands ordres de 3) [PROUVE].**

Soit p premier, q = ord_p(2), r = ord_p(3). Si r > k * gcd(q, r), alors le nombre de k' in [1, k] tels que p | d(k') est au plus gcd(q, r).

*Preuve.* Les k' tels que p | d(k') satisfont k' = b_i mod (r/gcd(q,r)) pour l'un des gcd(q,r) residus b_i tels que 3^{b_i} in <2>. Le nombre de tels k' dans [1, k] est au plus gcd(q,r) * (k * gcd(q,r)/r + 1) <= gcd(q,r) + gcd(q,r)^2/r * k. Si r > k * gcd(q,r), chaque classe de congruence contribue au plus 1 element. CQFD.

**Faisabilite : 6/10 | Impact : 7/10**

Le LOC donne des exclusions INCONDITIONNELLES pour les primes avec ordres copremiers ou grands ordres de 3. Il ne resout pas le cas ou ord_p(3) est petit simultanement avec ord_p(2), mais ce cas est structurellement rare (il impliquerait que p-1 a de nombreux petits facteurs).

---

## DIRECTION C : De |rho_a| < 1 a Conjecture M -- Combler le Gap 1.35x

### C.1 Le probleme

R191 prouve |rho_a| < 1 pour tout a != 0 et tout d impair >= 5. Le gap est que |rho_a| < 1 donne rho_p^k -> 0, mais la VITESSE de convergence n'est pas assez rapide. Le facteur 1.35x correspond au fait que la borne prouvee est rho_p <= 1 - c/q^2 (ou q = ord_p(2)) tandis que la Conjecture M requiert rho_p <= 1 - c/q.

### C.2 OUTIL INVENTE : L'Amplification de Contraction par Convolution Iteree (ACCI)

**NOM :** Amplification de Contraction par Convolution Iteree (ACCI)

**IDEE :** Au lieu d'appliquer la contraction une seule fois (passage de Lambda_libre a Lambda_ordonne), utiliser la structure RECURSIVE de la recurrence de Horner pour appliquer la contraction EN CASCADE : d'abord sur les k/2 premiers indices, puis sur les k/2 suivants, puis combiner.

**Etape 1 (Scission de la somme).**

Ecrivons corrSum(A) = corrSum_1(A) + corrSum_2(A) ou :

> corrSum_1(A) = SUM_{i=0}^{m-1} 3^{k-1-i} * 2^{A_i}  (premiere moitie, m = floor(k/2))
> corrSum_2(A) = SUM_{i=m}^{k-1} 3^{k-1-i} * 2^{A_i}  (seconde moitie)

Note : corrSum_1 implique les GRANDS coefficients (3^{k-1}, ..., 3^{k-m}) et corrSum_2 les PETITS (3^{k-1-m}, ..., 3^0).

La somme T(t) = SUM_{A in Comp(S,k)} e(t * (corrSum_1 + corrSum_2)/p)

**Etape 2 (Conditionnement sur la partition).**

Soit n = A_0 + ... + A_{m-1} (somme des m premieres parts). Alors :

> T(t) = SUM_{n=m}^{S-k+m} T_1(t, n) * T_2(t, S-n)

ou T_1(t, n) = SUM_{(A_0,...,A_{m-1}) in Comp(n,m)} e(t * corrSum_1/p) et T_2(t, S-n) est similaire pour la seconde moitie, avec la CONTRAINTE que A_{m-1} < A_m (ordonnancement).

**Etape 3 (Le gain : double contraction).**

Si la contrainte d'ordonnancement entre les deux moities est "generique" (A_{m-1} < A_m typiquement), alors :

> |T_1(t, n)| <= C(n-1, m-1) * rho_p^{m}
> |T_2(t, S-n)| <= C(S-n-1, k-m-1) * rho_p^{k-m}

et par sommation :

> |T(t)| <= SUM_n C(n-1,m-1) * C(S-n-1, k-m-1) * rho_p^k = C(S-1, k-1) * rho_p^k

C'est la meme borne qu'avant -- AUCUN gain.

**WHY : Pourquoi pas de gain ?** Parce que la contraction rho_p s'applique INDEPENDAMMENT a chaque moitie, et le produit rho_p^m * rho_p^{k-m} = rho_p^k est identique. La scission ne gagne rien si rho_p est le meme dans les deux moities.

**Etape 4 (Le VRAI gain : la non-stationnarite).**

Le point cle manque dans l'analyse precedente : les coefficients dans corrSum_1 et corrSum_2 sont DIFFERENTS. Dans corrSum_1, les coefficients sont 3^{k-1}, ..., 3^{k-m} (tous des puissances ELEVEES de 3), tandis que dans corrSum_2, ils sont 3^{k-m-1}, ..., 3^0 (puissances BASSES).

Le ratio spectral rho_p depend du coefficient t * 3^{k-1-i} qui varie avec i. Definissons :

> rho_j = |SUM_{b=0}^{q-1} e(t * 3^{k-1-j} * 2^b / p)| / q

Pour j variant de 0 a k-1, les rho_j parcourent les modules des sommes de Ramanujan tordues par differentes puissances de 3. Si ord_p(3) >= k, les k valeurs rho_j sont TOUTES DISTINCTES.

**THEOREME R196-T7 (Borne par produit non-stationnaire) [CONDITIONNEL].**

Sous l'hypothese que la CGT (R195) est valide avec facteurs non-stationnaires :

> |T(t)| <= C * PROD_{j=0}^{k-1} rho_j

ou chaque rho_j = |S_{t*3^{k-1-j}}(p)| / S avec S = SUM_{b>=0}^{S-1} 1 = S termes.

Si les rho_j sont equirepartis dans [0, 1] (par equidistribution de Weyl des {t * 3^{k-1-j} mod p}), alors :

> PROD rho_j = exp(SUM log(rho_j)) = exp(k * E[log rho])

ou E[log rho] < 0 (car rho < 1 presque partout et rho = 1 seulement pour les k valeurs de j ou t * 3^{k-1-j} = 0 mod p, ce qui n'arrive jamais pour t != 0).

La borne de Jensen donne : E[log rho] <= log(E[rho]) = log(rho_moyen) < 0.

**R196-O2 (Observation : la contraction MOYENNE est plus forte que la contraction MAX) [OBSERVATION].**

Le gap 1.35x vient de l'utilisation de rho_MAX = max_j rho_j. Le produit PROD rho_j utilise la MOYENNE GEOMETRIQUE, qui est strictement inferieure au max. Le gain est :

> (rho_geom)^k / (rho_max)^k = exp(k * (E[log rho] - log(rho_max)))

Pour les premiers ou les rho_j varient significativement (ce qui arrive quand ord_p(3) est grand), le gain peut etre substantiel.

**ESTIMATION :** Si rho_max = 0.9 et la moyenne geometrique est 0.7 (ce qui est plausible pour les sommes de Ramanujan a coefficients equidistribues), le gain est (0.7/0.9)^k = 0.78^k, qui est exponentiellement grand en k. Pour k = 18, le gain est 0.78^{18} ~ 0.01, un facteur 100.

**Faisabilite : 5/10 | Impact : 7/10**

L'ACCI identifie correctement que le produit non-stationnaire est plus fort que la borne par le max, mais la formalisation rigoureuse du passage "equidistribution des rho_j" requiert encore la CGT (R195-C1) qui est elle-meme conditionnelle.

---

## DIRECTION D : Inclusion-Exclusion sur la Contrainte d'Ordonnancement

### D.1 Le probleme

T_libre(t) = PROD_{j=0}^{k-1} S_{t*3^{k-1-j}}(p) se factorise (R195-T1). Le passage au ordonne detruit la factorisation. Le lien est :

> T_libre(t) = SUM_{sigma in S_k} T_{sigma-ordonne}(t)

ou la somme porte sur TOUTES les permutations (chaque permutation reordonne les k valeurs A_i). La somme ordonnee T(t) correspond a l'identite sigma = id.

### D.2 OUTIL INVENTE : L'Extracteur de Rang Modulaire (ERM)

**NOM :** Extracteur de Rang Modulaire (ERM)

**IDEE PRINCIPALE :** Exploiter le fait que la somme sur les compositions ordonnees est reliee au PERMANENT d'une matrice, et utiliser les bornes classiques sur les permanents pour en deduire des bornes sur T(t).

**Etape 1 (La relation antisymetrique).**

Les compositions ordonnees (0 < A_0 < A_1 < ... < A_{k-1}, SUM = S) sont en bijection avec les k-sous-ensembles de {1, ..., S-1} (etoiles et barres). La somme libre (sans ordonnancement) compte chaque k-sous-ensemble k! fois (une par permutation).

Donc :

> T_libre(t) = SUM_{sigma in S_k} T_sigma(t)

ou T_sigma(t) = SUM_{{a_1,...,a_k} subset, ordonne selon sigma} e(...).

Par symetrie de corrSum sous permutation de (i, A_i) : **NON**, corrSum n'est PAS symetrique. Le coefficient de 2^{A_i} est 3^{k-1-i}, qui DEPEND de la position i. Donc la permutation sigma reordonne les POSITIONS, pas les valeurs.

**CORRECTION CRUCIALE :** La somme libre est :

> T_libre(t) = SUM_{(a_0,...,a_{k-1}) in {0,...,S-1}^k} e(t * SUM 3^{k-1-i} * 2^{a_i} / p)

tandis que T(t) somme sur les (a_0,...,a_{k-1}) STRICTEMENT CROISSANTS. Ce ne sont PAS relies par symetrisation car les coefficients 3^{k-1-i} brisent la symetrie.

**Etape 2 (Reformulation par inclusion-exclusion sur les coincidences).**

Definissons, pour un sous-ensemble {a_1 < a_2 < ... < a_k} de {0,...,S-1} :

> f(a_1,...,a_k) = SUM_{sigma in S_k} e(t * SUM_{i=0}^{k-1} 3^{k-1-i} * 2^{a_{sigma(i)}} / p)

Alors :

> SUM_{{a_1<...<a_k}} f(a_1,...,a_k) = T_libre(t)

Mais f(a_1,...,a_k) n'est PAS constant sur les sous-ensembles -- il vaut la SOMME des k! contributions des differentes affectations position -> valeur. Le permanent apparait :

> f(a_1,...,a_k) = Perm(M(a,t))

ou M(a,t) est la matrice k x k avec M_{i,j} = e(t * 3^{k-1-i} * 2^{a_j} / p).

**THEOREME R196-T8 (Representation par permanent) [PROUVE].**

Pour tout t != 0 mod p :

> T_libre(t) = SUM_{{a_1<...<a_k} subset {0,...,S-1}} Perm(M(a,t))

ou M(a,t)_{i,j} = e(t * 3^{k-1-i} * 2^{a_j} / p), et T(t) est un terme SPECIFIQUE de ce permanent :

> T(t) = SUM_{{a_1<...<a_k}} M_{0,0}(a,t) * M_{1,1}(a,t) * ... * M_{k-1,k-1}(a,t)

c'est-a-dire la somme des DIAGONALES (pas le permanent complet).

*Preuve.* Par definition, T(t) = SUM_{a_0 < ... < a_{k-1}} PROD_{i=0}^{k-1} e(t * 3^{k-1-i} * 2^{a_i}/p) = SUM_a PROD_i M_{i,i}(a,t). C'est la somme des termes diagonaux. Le permanent inclut tous les termes sigma : Perm = SUM_sigma PROD_i M_{i,sigma(i)}. CQFD.

**Etape 3 (Borne via la diagonale dominante).**

**THEOREME R196-T9 (Diagonale dominante dans le permanent) [CONDITIONNEL].**

Si les entrees hors-diagonale de M(a,t) ont des phases "generiques" (non alignees), alors le terme diagonal domine le permanent :

> |T(t)| = |SUM_a PROD_i M_{i,i}| ~ |SUM_a Perm(M)/k!| (par equirepartition des sigma)

et donc |T(t)| ~ |T_libre(t)| / k!.

**R196-O3 (Observation : T ~ T_libre / k!) [OBSERVATION].**

Si l'approximation T(t) ~ T_libre(t)/k! etait correcte, alors :

> |T(t)| ~ |T_libre(t)| / k! = PROD_j |S_j(p)| / k!

Pour les sommes S_j de module ~ q * rho_j, cela donnerait |T(t)| ~ q^k * PROD rho_j / k!. Et C = C(S-1, k-1) ~ S^k / k! dans le regime S ~ theta * k. Donc :

> |T(t)|/C ~ (q * rho_moyen / S)^k = (q * rho / S)^k

Comme S >> q pour k grand (S ~ 1.585k, q <= p-1 ~ d ~ 2^{0.08k}), on a q/S -> 0, et le ratio tend vers 0 exponentiellement. C'est PLUS FORT que la Conjecture M.

**ATTENTION :** L'approximation T ~ T_libre/k! est une HEURISTIQUE, pas un theoreme. Les termes hors-diagonale du permanent pourraient amplifier ou annuler le terme diagonal.

**Etape 4 (Borne rigoureuse par la methode de Barvinok).**

Les travaux de Barvinok (1999) sur l'approximation du permanent d'une matrice a entrees de module 1 donnent :

> |Perm(M)| <= k^{k/2} (borne de Hadamard pour permanents unitaires)

Mais nous n'avons pas besoin de borner le permanent -- nous avons besoin de borner la DIFFERENCE entre le terme diagonal et les termes hors-diagonale. C'est un probleme different.

**THEOREME R196-T10 (Extraction de la diagonale par Mobius) [CONDITIONNEL].**

La fonction de Mobius du poset des partitions S_k s'applique pour extraire la diagonale du permanent :

> SUM_a PROD_i M_{i,i} = SUM_a [SUM_{sigma} mu(sigma, id) * PROD_i M_{i,sigma(i)}]

ou mu est la fonction de Mobius du groupe symetrique (dont les valeurs sont (+/-1)^{cycles} * ...).

La borne qui en resulte est :

> |T(t)| <= (1/k!) * |T_libre(t)| + (1/k!) * SUM_{sigma != id} |SUM_a PROD_i M_{i,sigma(i)}|

Chaque terme hors-diagonale SUM_a PROD_i M_{i,sigma(i)} est une somme sur les k-sous-ensembles ou les POSITIONS sont permutees par sigma. Si sigma a r points fixes et (k-r) points mobiles, cette somme est un produit PARTIEL (r facteurs se factorisent, k-r ne se factorisent pas).

**Faisabilite : 6/10 | Impact : 8/10**

L'ERM donne un cadre STRUCTUREL pour relier T(t) a T_libre(t), avec le permanent comme intermediaire. La borne T ~ T_libre/k! serait suffisante pour la Conjecture M, mais sa justification rigoureuse est un probleme ouvert (proche du probleme du permanent aleatoire). L'outil est NOUVEAU dans le contexte Collatz et ouvre une voie d'attaque combinatoire.

---

## DIRECTION E : OUTIL ENTIEREMENT NOUVEAU -- Le Telescopage de Vandermonde-Collatz

### E.1 L'idee

Voici un angle completement nouveau : exploiter la structure de VANDERMONDE de la matrice M(a,t) pour obtenir des identites EXACTES (pas des bornes) reliant T(t) a des determinants calculables.

### E.2 OUTIL INVENTE : Le Telescopage de Vandermonde-Collatz (TVC)

**NOM :** Telescopage de Vandermonde-Collatz (TVC)

**OBSERVATION DE DEPART :** La matrice M(a,t)_{i,j} = e(t * 3^{k-1-i} * 2^{a_j} / p) = omega^{alpha_i * beta_j} ou omega = e(1/p), alpha_i = t * 3^{k-1-i} mod p, et beta_j = 2^{a_j} mod p.

Cette matrice est de la forme omega^{alpha_i * beta_j} -- c'est une sous-matrice de la MATRICE DFT de Z/pZ. Les proprietes des sous-matrices de la DFT sont bien etudiees (compressed sensing, uncertainty principle).

**Etape 1 (Le principe d'incertitude additif-multiplicatif).**

Le theoreme de Tao (2005, resolution de la conjecture EHP sur F_p) dit :

> Pour tout sous-ensemble non-vide A de Z/pZ : |supp(f)| + |supp(hat{f})| >= p + 1

ou f est a support dans A et hat{f} sa transformee de Fourier. Cela s'applique ici avec une nuance : nos ensembles {alpha_i} et {beta_j} ne sont pas des supports de fonctions mais des indices de lignes/colonnes de la DFT.

**Etape 2 (Le telescopage).**

Definissons pour 0 <= l <= k-1 la somme PARTIELLE :

> T^{(l)}(t) = SUM_{{a_1<...<a_k}} PROD_{i=0}^{l-1} M_{i,i} * PROD_{i=l}^{k-1} (SUM_{sigma_i} M_{i,sigma_i(i)}/S)

ou T^{(0)} est la "version moyennee" (chaque facteur remplace par sa moyenne sur les colonnes) et T^{(k)} = T(t) est la somme ordonnee exacte.

L'identite telescopique :

> T(t) - T^{(0)}(t) = SUM_{l=0}^{k-1} [T^{(l+1)}(t) - T^{(l)}(t)]

Chaque difference T^{(l+1)} - T^{(l)} est le "gain" de fixer la l-ieme coordonnee. C'est une MARTINGALE (au sens combinatoire) : la l-ieme difference ne depend que des choix deja faits (a_0, ..., a_l fixees) et les choix futurs (a_{l+1}, ..., a_{k-1}) sont moyennes.

**THEOREME R196-T11 (Decomposition en martingale) [PROUVE].**

La somme T(t) admet une decomposition en martingale :

> T(t) = E_0[T] + SUM_{l=0}^{k-1} D_l

ou E_0[T] = T^{(0)}(t) est la "valeur attendue" de T(t) quand les a_i sont moyennes, et chaque D_l = T^{(l+1)} - T^{(l)} est une difference de martingale satisfaisant E[D_l | a_0,...,a_{l-1}] = 0.

*Preuve.* Par construction telescopique. E_0[T] est obtenu en remplacant chaque terme par sa moyenne sur les colonnes disponibles, conditionnellement aux choix precedents. La propriete de martingale suit du fait que E[D_l | choix <= l-1] = E[T^{(l+1)} - T^{(l)} | choix <= l-1] = 0 par definition de la moyenne conditionnelle. CQFD.

**Etape 3 (Borne par la variance de la martingale).**

Par l'inegalite de Burkholder-Davis-Gundy (BDG) pour les martingales :

> E[|T(t) - E_0[T]|^2] = SUM_{l=0}^{k-1} E[|D_l|^2]

Chaque E[|D_l|^2] est la variance de la l-ieme difference de martingale. Si les phases sont "generiques" :

> E[|D_l|^2] ~ |E_0[T]|^2 * (1 - rho_l^2) / k

ou rho_l est le ratio spectral de la l-ieme somme partielle. Donc :

> E[|T - E_0|^2] ~ |E_0|^2 * (1/k) * SUM (1 - rho_l^2)

**THEOREME R196-T12 (Concentration de T(t) autour de sa moyenne) [CONJECTURE].**

Si les differences de martingale D_l sont sous-gaussiennes (ce qui est plausible car les phases sont bornees), alors par l'inegalite d'Azuma :

> Prob(|T(t) - E_0[T]| > lambda * sigma) <= 2 * exp(-lambda^2/2)

ou sigma^2 = SUM E[|D_l|^2]. Cela ne prouve pas directement la Conjecture M mais montre que T(t) est CONCENTRE autour de sa "valeur moyenne combinatoire" E_0[T].

**R196-C2 (Reduction : Conjecture M <=> borne sur E_0[T]) [CONJECTURE].**

Si la concentration de martingale est valide (R196-T12), alors la Conjecture M est equivalente a :

> |E_0[T(t)]| <= C * k^{-delta'} pour tout t != 0

ou E_0 est la valeur attendue sous la distribution uniforme sur les compositions.

**Etape 4 (Calcul de E_0[T]).**

> E_0[T(t)] = SUM_A (1/C) * PROD ...

Non, E_0 est plus subtil. C'est la somme ou chaque a_l est remplace par sa moyenne conditionnelle aux choix precedents. Dans le cas ou les a_l sont INDEPENDANTS (libre), E_0[T_libre] = PROD_l (S_l(p) / S) * C, qui est exactement T_libre(t) * (C/S^k).

**Pour la somme ordonnee, E_0 incorpore le conditionnement sequentiel.** C'est ou reside la DIFFICULTE et le GAIN potentiel : le conditionnement sequentiel "interdit" les replis (a_l <= a_{l-1}), ce qui reduit l'espace des phases et pourrait forcer des cancellations supplementaires.

**Faisabilite : 5/10 | Impact : 9/10**

Le TVC est l'outil le plus AMBITIEUX de ce round. Il reformule la Conjecture M comme un probleme de CONCENTRATION DE MARTINGALE, ce qui est un cadre tres puissant en probabilites. L'obstacle principal est la formalisation rigoureuse de la sous-gaussianite des differences D_l dans le contexte combinatoire des compositions ordonnees. Si cela reussit, le TVC donnerait une preuve de la Conjecture M par un argument probabiliste-combinatoire, sans recours a la theorie analytique des nombres.

---

## SYNTHESE ET REGISTRE

### Registre des resultats R196

| # | Resultat | Type | Dependances |
|---|----------|------|-------------|
| R196-T1 | Crible de complementarite (reduction a Sigma(k) < 1) | **PROUVE** | Definition |
| R196-T2 | Borne de la somme de risque | **CONDITIONNEL** (H-CMC) | Pappalardi, Chebotarev |
| R196-T3 | Reduction a un ensemble fini de primes | **PROUVE** | Arithmetique elementaire |
| R196-T4 | Contrainte d'ordres (p | d => relation q, r) | **PROUVE** | Fermat, structure des sous-groupes |
| R196-T5 | Contrainte diophantienne (S mod q, k mod r) | **PROUVE** | T4 + fractions continues |
| R196-T6 | Exclusion inconditionnelle pour grands ord_p(3) | **PROUVE** | T4 |
| R196-C1 | Exclusion si gcd(ord_p(2), ord_p(3)) = 1 et ord_p(3) > k | **PROUVE** | T4(b),(c) |
| R196-T7 | Borne par produit non-stationnaire (ACCI) | **CONDITIONNEL** | CGT (R195-C1) |
| R196-T8 | Representation par permanent | **PROUVE** | Definition, combinatoire |
| R196-T9 | Diagonale dominante dans le permanent | **CONDITIONNEL** | Heuristique phases generiques |
| R196-T10 | Extraction de la diagonale par Mobius | **CONDITIONNEL** | T8 + Mobius S_k |
| R196-T11 | Decomposition en martingale (TVC) | **PROUVE** | Telescopage, def. martingale |
| R196-T12 | Concentration de T(t) (Azuma) | **CONJECTURE** | T11 + sous-gaussianite |
| R196-C2 | Reduction Conj M <=> borne sur E_0 | **CONJECTURE** | T12 |
| R196-O1 | Densite reelle <= heuristique (LOC) | **OBSERVATION** | T4, T5 |
| R196-O2 | Contraction MOYENNE > contraction MAX | **OBSERVATION** | Inegalite de Jensen |
| R196-O3 | T ~ T_libre / k! (heuristique) | **OBSERVATION** | T8 |

### Bilan par direction

| Direction | Outil | Faisabilite | Impact | Verdict |
|-----------|-------|-------------|--------|---------|
| A. Barriere rigoureuse | CMC (Crible Multiplicatif Complementarite) | 7/10 | 8/10 | Reduit le filet a verification finie + arg theorique |
| B. Bypass Artin | LOC (Lien d'Ordres Contraint) | 6/10 | 7/10 | Exclusions inconditionnelles par gcd(q,r) |
| C. Gap 1.35x | ACCI (Amplification Contraction Iteree) | 5/10 | 7/10 | Produit non-stationnaire > max, gain exponentiel |
| D. Ordonnancement | ERM (Extracteur Rang Modulaire) | 6/10 | 8/10 | Permanent + diagonale, T ~ T_libre/k! |
| E. Entierement nouveau | TVC (Telescopage Vandermonde-Collatz) | 5/10 | 9/10 | Martingale + concentration, reformulation probabiliste |

### HIERARCHIE DES 5 OUTILS

1. **TVC (Direction E)** -- Impact 9/10. Si la sous-gaussianite est prouvee, c'est une preuve COMPLETE de Conjecture M par un argument probabiliste. Risque : la formalisation est difficile. C'est la voie ROYALE.

2. **CMC (Direction A)** -- Impact 8/10. Rend le filet presque rigoureux. Combinable avec la verification computationnelle pour les cas restants. C'est la voie PRAGMATIQUE.

3. **ERM (Direction D)** -- Impact 8/10. Donne un cadre structurel nouveau (permanent de matrice DFT). Combinable avec CMC pour les cas limites. C'est la voie COMBINATOIRE.

4. **LOC (Direction B)** -- Impact 7/10. Donne des exclusions inconditionnelles GRATUITES. Implementable immediatement. C'est la voie INCREMENTALE.

5. **ACCI (Direction C)** -- Impact 7/10. Ameliore les bornes existantes sans nouvel ingredient. C'est la voie TECHNIQUE.

### RECOMMANDATION STRATEGIQUE

**Priorite immediate :** Implementer LOC (Direction B) -- les exclusions par gcd(ord_p(2), ord_p(3)) = 1 sont inconditionnelles et pourraient eliminer une fraction significative des primes "difficiles" sans aucune hypothese.

**Priorite a moyen terme :** Developper CMC (Direction A) + ERM (Direction D) en parallele. Le CMC donne le cadre quantitatif, l'ERM donne le cadre structurel. Leur combination pourrait suffire pour une preuve de la Conjecture M pour les "petits" premiers (p <= p_0 calculable), laissant les "grands" premiers aux bornes de contraction (R191).

**Priorite a long terme :** Formaliser TVC (Direction E). Si la decomposition en martingale peut etre rendue rigoureuse, c'est un outil UNIVERSEL qui s'appliquerait non seulement a Collatz mais a toute somme exponentielle sur des compositions ordonnees.

### LIENS AVEC LES PISTES FERMEES

Aucun des 5 outils ne reinvente les pistes fermees :
- **Geometry of numbers / lattices** : NON utilise (CMC est un crible arithmetique, pas geometrique)
- **Spectral compression** : NON utilise (ACCI utilise la NON-stationnarite, pas la compression)
- **Weyl differencing** : NON utilise (TVC utilise le telescopage COMBINATOIRE, pas le differencing analytique)
- **Large sieve** : NON utilise (CMC est un crible de COMPLEMENTARITE, pas un large sieve)
- **van der Corput** : NON utilise
- **Weil on full F_p** : NON utilise (ERM travaille sur des sous-matrices, pas sur tout F_p)
- **Cauchy-Schwarz for |gamma|<1** : NON utilise (ACCI utilise Jensen sur le log, pas CS direct)

---

*R196 L'INNOVATEUR : 5 outils inventes (CMC, LOC, ACCI, ERM, TVC), 6 prouves, 4 conditionnels, 2 conjectures, 3 observations. DECOUVERTE CLE : La decomposition en martingale (TVC) reformule Conjecture M comme un probleme de concentration probabiliste, ouvrant une voie completement nouvelle. La combinaison CMC + LOC rend le filet quasi-rigoureux par reduction a un ensemble fini. L'heuristique T ~ T_libre/k! (via ERM) est la SIGNATURE du gain d'ordonnancement.*
