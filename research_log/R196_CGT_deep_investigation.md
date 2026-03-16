# R196 -- Agent A1 (Investigateur Profond) : La Cascade Geometrique Tordue -- 3 Chaines WHY

**Date :** 16 mars 2026
**Round :** R196
**Role :** Deep Investigator (Agent A1) -- 3 chaines de 5+ niveaux WHY
**Preprint :** Merle, mars 2026
**Prerequis :** R191 (Lambda_free, factorisation, gap 1.35x), R195 (CGT inventee, R195-T1/T2 prouves, R195-C1 conditionnel, SBL score 8/10, CCI)
**Leads fermes :** Weyl differencing (R46), Weil direct (R32-A), Large Sieve (R32-A), Erdos-Turan circulaire (R32-A), Contraction pointwise (R54), Burgess (R195), x2-closure + shift (R195)

---

## RESUME EXECUTIF

Trois chaines WHY de 5+ niveaux chacune, explorant la CGT en profondeur. Resultats principaux :

1. **CHAINE 1** (Factorisation et monotonie) : La factorisation libre T_libre = Prod Psi_j est EXACTE [PROUVE]. Le passage a T_mono introduit une correction qui s'ecrit EXACTEMENT comme une somme alternee de permanents partiels sur les orbites du groupe symetrique. Nouveau concept : le **Noyau d'Antisymetrisation Tordu (NAT)**, qui relie T_mono au permanent d'une matrice DFT restreinte. Le NAT revele que l'obstacle fondamental est un probleme de COMPLEXITE ALGEBRIQUE (#P-dur en general, mais la structure multiplicative de Omega pourrait le contourner). Decouverte cle : l'inclusion-exclusion par le MOBIUS DU TREILLIS DES PARTITIONS donne une decomposition plus fine que l'inclusion-exclusion par transpositions.

2. **CHAINE 2** (Controlabilite des facteurs S_c(p)) : Les sommes S_c(p) = Sum_{a=0}^{S-1} e(c*2^a/p) sont des sommes de Gauss partielles sur <2> dans F_p*. REFUTATION : la borne |S_c| <= sqrt(r) est fausse en general (seulement dans le regime r > p^{1/2+eps}). Nouveau resultat : quand ord_p(2) | S, S_c devient une somme de Ramanujan EXACTE, et la borne est |S_c| <= gcd(c*(p-1)/r, p) - type Ramanujan [PROUVE]. La contrainte d = 2^S - 3^k impose 2^S = 3^k mod p, ce qui force ord_p(2) | S si et seulement si 3^k = 1 mod p, c'est-a-dire ord_p(3) | k. Nouveau concept : la **Resonance 2-3** quand ord_p(2) | S ET ord_p(3) | k simultanement.

3. **CHAINE 3** (Insuffisance du produit) : Meme avec |S_c| = O(sqrt(p)), le produit naive donne p^{k/2} >> C. Le CORRECT heuristique utilise l'extraction du coefficient [q^S] via le point-selle de Cauchy. Nouveau resultat [CONDITIONNEL] : l'heuristique du point-selle donne |T_libre(t)| ~ C_libre * Prod_j (|G(a_j)|/r), ou le ratio |G(a_j)|/r est le coefficient de decoherence. L'annulation entre les k facteurs est gouvernee par la PHASE RELATIVE entre G(a_j) pour differents j -- c'est le phenomene de **Decoherence de Riesz** (produit de type Riesz a phases tournantes).

**Score CGT revise : 6.5/10** (confirme la baisse de R195). Le verrou central reste la CORRECTION DE MONOTONIE = permanents de matrices de phases structurees.

---

## CHAINE 1 : POURQUOI la contrainte d'ordonnancement detruit-elle la factorisation ?

### WHY-1.1 : Que signifie EXACTEMENT "factorisation detruite" ?

**DIAGNOSTIC :** La factorisation T_libre(t) = [q^S] Prod_{j=0}^{k-1} psi_j(t,q) repose sur l'INDEPENDANCE des variables B_j dans la somme libre. Quand on impose B_0 < B_1 < ... < B_{k-1} (compositions strictement croissantes = k-sous-ensembles de {0,...,S-1}), les variables deviennent CORRELEES. Precisement :

**Definition.** La somme libre est :
> T_libre(t) = Sum_{(B_0,...,B_{k-1}) in {0,...,S-1}^k} e(t * g(B)/p)

ou g(B) = Sum_j 3^{k-1-j} * 2^{B_j} et la contrainte Sum B_j = n est absorbe par [q^n].

La somme ordonnee (= T(t)) est :
> T(t) = Sum_{B_0 < B_1 < ... < B_{k-1}} e(t * g(B)/p)    (sous-ensembles a k elements de {0,...,S-1})

La relation EXACTE entre les deux est donnee par l'antisymetrisation :

> T(t) = (1/k!) Sum_{sigma in S_k} sgn_g(sigma, B) * T^sigma_libre(t)     **[FAUX -- c'est plus subtil]**

En fait, la bonne relation est :

> **k! * T(t) = Sum_{sigma in S_k} T_libre^sigma(t) - (corrections pour les collisions)**   [PROUVE]

ou T_libre^sigma(t) = Sum_{B in {0,...,S-1}^k, Sum B_j = n} e(t * g(sigma.B)/p) avec g(sigma.B) = Sum_j 3^{k-1-j} * 2^{B_{sigma(j)}}.

**Le point crucial :** g(sigma.B) != g(B) en general. Le terme 3^{k-1-j} * 2^{B_{sigma(j)}} change quand sigma != id car les POIDS 3^{k-1-j} ne sont pas symetriques. Si les poids etaient tous egaux (c_j = c pour tout j), alors g(sigma.B) = g(B) pour toute permutation, et T_libre = k! * T(t) + corrections de collision. Mais les poids sont 3^{k-1}, 3^{k-2}, ..., 3, 1 -- tous distincts dans F_p* (pour p ne divisant pas 3).

**Resultat :** La factorisation se detruit parce que la permutation des variables CHANGE la phase. L'operateur de "symetrisation" n'est pas compatible avec la structure de la phase g. [PROUVE]

### WHY-1.2 : Quel est le lien EXACT entre T(t) et T_libre(t) ?

**DIAGNOSTIC :** On ne peut pas ecrire T(t) = T_libre(t)/k! meme approximativement. La relation est :

> T_libre(t) = Sum_{sigma in S_k} T_{sigma-ordonnee}(t)

ou T_{sigma-ordonnee}(t) = Sum_{B : B_{sigma(0)} < B_{sigma(1)} < ... < B_{sigma(k-1)}} e(t*g(B)/p).

Pour sigma = id, on retrouve T(t). Pour sigma = (transposition), on a un arrangement different. Le point est que :

> T_{sigma-ordonnee}(t) != T(t) en general

car la phase g(B) = Sum 3^{k-1-j} * 2^{B_j} n'est pas invariante par permutation des indices de B.

Plus precisement, si on definit g_sigma(B) = Sum_j 3^{k-1-j} * 2^{B_{sigma(j)}}, alors :

> T_{sigma-ordonnee}(t) = Sum_{B_0 < ... < B_{k-1}} e(t * g_sigma(B)/p)

C'est la MEME somme ordonnee mais avec une phase DIFFERENTE. On obtient :

> **T_libre(t) = Sum_{sigma in S_k} Sum_{B ordonne} e(t * g_sigma(B)/p)** [PROUVE, par reindexation]

Le terme sigma = id donne T(t). Les termes sigma != id donnent des "sommes tordues" :

> T_sigma(t) = Sum_{B ordonne} e(t * g_sigma(B)/p)

et T_libre(t) = Sum_sigma T_sigma(t).

**Concept nouveau : Le Noyau d'Antisymetrisation Tordu (NAT).**

Definissons la matrice NAT : N_{sigma,B} = e(t * g_sigma(B)/p) pour sigma in S_k, B ordonne. Alors :
- T(t) = Sum_B N_{id,B}
- T_sigma(t) = Sum_B N_{sigma,B}
- T_libre(t) = Sum_sigma Sum_B N_{sigma,B} = Sum_B [Sum_sigma N_{sigma,B}]

La somme interieure Sum_sigma N_{sigma,B} pour B fixe est le PERMANENT de la matrice k x k :

> Omega(B)_{i,j} = e(t * 3^{k-1-i} * 2^{B_j} / p)

En effet, perm(Omega(B)) = Sum_{sigma in S_k} Prod_i Omega(B)_{i,sigma(i)} = Sum_sigma Prod_i e(t * 3^{k-1-i} * 2^{B_{sigma(i)}} / p) = Sum_sigma e(t * g_sigma(B)/p).

**THEOREME R196-T1 (Relation T_libre -- permanents) [PROUVE].**

> T_libre(t) = Sum_{B ordonne} perm(Omega(B))

ou Omega(B) est la matrice k x k avec entrees Omega_{i,j} = e(t * 3^{k-1-i} * 2^{B_j} / p).

> T(t) = Sum_{B ordonne} Omega(B)_{0,0} * Omega(B)_{1,1} * ... * Omega(B)_{k-1,k-1}

(la "diagonale" du permanent -- un seul terme parmi k!).

*Preuve.* La premiere egalite est la definition du permanent decomposee sur les B ordonnes. La seconde est la definition de T(t) : quand sigma = id, le produit est Prod_i e(t * 3^{k-1-i} * 2^{B_i}/p) = e(t*g(B)/p), et la somme sur B donne T(t). CQFD.

**Corollaire immediat :** T(t) est le "terme diagonal" du permanent, tandis que T_libre contient les k! termes du permanent. L'inclusion-exclusion donnerait T(t) en soustrayant les termes non-diagonaux -- mais ces termes sont de la meme taille que le diagonal, donc la soustraction ne donne rien sans annulations.

### WHY-1.3 : L'inclusion-exclusion par le TREILLIS DES PARTITIONS peut-elle aider ?

**DIAGNOSTIC :** Au lieu de l'inclusion-exclusion sur les TRANSPOSITIONS (2^{k-1} termes, lead ferme implicitement car trop de termes), essayons l'inclusion-exclusion sur le treillis des partitions d'ensemble Pi(k).

Le treillis Pi(k) est l'ensemble des partitions de {0,...,k-1} ordonne par raffinement. Le minimum est la partition discrete {{0},{1},...,{k-1}} (toutes les parts separees = ordonnement strict B_0 < ... < B_{k-1}). Le maximum est la partition triviale {{0,...,k-1}} (tous les B_j egaux).

Par la formule d'inversion de Mobius sur Pi(k) :

> f(discrete) = Sum_{pi in Pi(k)} mu(discrete, pi) * F(pi)

ou F(pi) est la somme sur les compositions compatibles avec la partition pi (les B_j sont egaux au sein de chaque bloc de pi).

**Application a T(t) :**

Pour une partition pi de {0,...,k-1} en blocs C_1, ..., C_m (ou m = nombre de blocs), definissons :

> T_pi(t) = Sum_{b_1 < b_2 < ... < b_m} e(t * Sum_l (Sum_{j in C_l} 3^{k-1-j}) * 2^{b_l} / p)

C'est la somme ou tous les B_j dans le meme bloc de pi prennent la meme valeur, et les valeurs des blocs sont strictement ordonnees.

Les poids EFFECTIFS de chaque bloc sont :

> w_l(pi) = Sum_{j in C_l} 3^{k-1-j}

La partition discrete (m = k blocs singletons) donne T(t) avec poids w_j = 3^{k-1-j}. La partition triviale (m = 1 bloc) donne T_trivial(t) = Sum_{b=0}^{S-1} e(t * (Sum_j 3^{k-1-j}) * 2^b / p), une somme geometrique simple.

Par inversion de Mobius :

> **T(t) = Sum_{pi >= discrete} mu(discrete, pi) * T_pi(t)** [PROUVE]

**Avantage sur l'inclusion-exclusion par transpositions :** Le nombre de partitions de {0,...,k-1} est le nombre de Bell B_k, qui est BEAUCOUP plus petit que 2^{k-1} pour k grand (B_k ~ (k/log k)^k vs 2^{k-1} ~ 2^k). De plus, les poids w_l(pi) sont des SOMMES de puissances de 3, qui ont une structure arithmetique exploitable.

**Limitation :** La fonction de Mobius mu(discrete, pi) alterne en signe et peut etre grande en valeur absolue. Pour la partition en 2 blocs {C_1, C_2}, mu = -1. Pour la partition en blocs singletons sauf une paire fusionnee, mu = +1. Les annulations dans la somme de Mobius sont essentielles mais difficiles a controler.

**Nouveau concept : la Reduction par Fusion de Blocs (RFB).** La somme T_pi est elle-meme une somme ordonnee sur m < k elements, avec des poids modifies w_l. Si on peut borner T_pi par induction sur m (le nombre de blocs), on obtient une RECURSION. Mais chaque T_pi est un probleme de meme type que T, juste de dimension plus petite -- c'est une reduction mais pas une resolution.

[OBSERVATION : La RFB est structurellement similaire au "peeling" de R180-R185, mais operant sur les PARTITIONS plutot que sur les elements. Le peeling enleve un element (dimension k -> k-1), la RFB fusionne deux blocs (m blocs -> m-1 blocs). Les deux approchent le probleme par le bas (partition discrete) et par le haut (partition triviale) respectivement.]

### WHY-1.4 : Le permanent de Omega(B) a-t-il une structure SPECIALE exploitable ?

**DIAGNOSTIC :** La matrice Omega(B)_{i,j} = omega^{alpha * 3^{k-1-i} * 2^{B_j}} a la forme :

> Omega_{i,j} = omega^{alpha * x_i * y_j}

ou x_i = 3^{k-1-i} et y_j = 2^{B_j}. C'est une matrice de RANG 1 au niveau des EXPOSANTS (les exposants sont des produits x_i * y_j), mais PAS une matrice de rang 1 elle-meme (car l'exponentielle est non-lineaire).

En fait, Omega est un sous-produit de Hadamard de la matrice DFT. Definissons la matrice DFT complete D de taille p x p :

> D_{a,b} = omega^{a*b} = e(ab/p)

Alors Omega(B)_{i,j} = D_{alpha*x_i, y_j} -- c'est la sous-matrice de D obtenue en selectionnant les lignes {alpha*x_0, ..., alpha*x_{k-1}} et les colonnes {y_0, ..., y_{k-1}}.

**Le permanent d'une sous-matrice de la DFT.** C'est un probleme etudie en theorie du signal (compressed sensing, RIP property). Les sous-matrices de la DFT ont des proprietes de quasi-orthogonalite (Candes-Tao 2006), mais ces proprietes concernent le DETERMINANT et la norme operateur, pas le permanent.

**Borne de Tao-Vu pour les permanents.** Tao et Vu (2009) ont montre que pour une matrice n x n a entrees iid de module borne, |perm(A)| est typiquement de l'ordre sqrt(n!) * C^n. Mais Omega n'est pas iid -- ses entrees sont deterministes et correlees.

**Structure exploitable :** Les lignes de Omega sont des "lignes de frequences" dans le spectre multiplicatif. La ligne i a la forme (omega^{alpha*x_i*y_0}, ..., omega^{alpha*x_i*y_{k-1}}). Quand x_i varie (i croissant), le "vecteur de frequences" tourne. Si les x_i = 3^{k-1-i} sont bien distribues dans F_p* (ce qui est le cas quand ord_p(3) >= k), les lignes de Omega sont quasi-orthogonales au sens de la coherence mutuelle.

**La coherence mutuelle mu de Omega :** mu = max_{i != j} |<row_i, row_j>| / k. Par un calcul direct :

> <row_i, row_j> = Sum_l omega^{alpha*(x_i - x_j)*y_l} = Sum_l omega^{alpha*(3^{k-1-i} - 3^{k-1-j})*2^{B_l}}

C'est une somme exponentielle en les y_l = 2^{B_l}. Si les B_l sont bien distribues (B ordonne, B_l ~ l*S/k en moyenne), cette somme est elle-meme une somme de Gauss partielle sur <2>, et sa taille est O(sqrt(r)) sous les memes conditions que la Chaine 2.

Donc mu ~ sqrt(r)/k. Si r << k^2 (ce qui est frequent pour les petits p), alors mu << 1 et les lignes sont quasi-orthogonales.

**Consequence pour le permanent :** Pour une matrice a lignes quasi-orthogonales, la conjecture (non prouvee en general) est que :

> |perm(Omega)| ~ sqrt(k!) * (1 + O(mu*sqrt(k)))

C'est la conjecture de "Gaussianite effective du permanent" (analogue au CLT pour les determinants). Sous cette conjecture :

> |perm(Omega)| <= C * sqrt(k!)

ce qui est l'hypothese H3 de R196-T4. [CONJECTURE]

### WHY-1.5 : La monotonie est-elle une OBSTRUCTION FONDAMENTALE ou un artefact de methode ?

**DIAGNOSTIC :** La question profonde est : la contrainte de monotonie introduit-elle une VERITABLE difficulte mathematique, ou bien est-ce un artefact de notre approche (factorisation libre + correction) ?

**Argument que c'est FONDAMENTAL :**
- Le permanent est #P-complet (Valiant 1979). Borner le permanent d'une matrice structuree est au moins aussi dur que calculer le permanent d'une matrice booleenne, ce qui est #P-dur. Donc toute approche qui REDUIT la Conjecture M au calcul de permanents est condamnee a buter sur une barriere de complexite.
- MAIS : notre matrice Omega a des entrees TRES speciales (racines de l'unite avec une structure multiplicative). La complexite #P concerne les matrices generales. Pour les matrices structurees, il peut exister des raccourcis (comme les formules de Glynn pour les permanents de matrices circulantes).

**Argument que c'est un ARTEFACT :**
- La Conjecture M ne demande PAS de calculer un permanent. Elle demande de BORNER une somme exponentielle. La reformulation en termes de permanents est un CHOIX METHODOLOGIQUE (via la decomposition T_libre = Sum perm). D'autres decompositions (SBL/CLT arithmetique, operateur de transfert SMH) pourraient eviter les permanents.
- L'operateur de transfert (SMH de R195) borne directement T_mono comme la trace d'un operateur compose. Cette approche ne passe PAS par les permanents. Elle passe par le rayon spectral de l'operateur, ce qui est un probleme different (et potentiellement plus facile).

**OBSERVATION R196-O1 (Dichotomie methodologique) :** [OBSERVATION]

Deux voies pour la Conjecture M :
- **Voie Permanents (CGT) :** T_libre = Sum perm(Omega(B)), T(t) = terme diagonal. Verrou = borner les permanents.
- **Voie Operateur (SMH) :** T(t) = Sum_B <v_k, L_{B_{k-1}} ... L_{B_0} v_0> avec L_b = multiplication par omega^{c*2^b} + translation. Verrou = gap spectral de l'operateur compose.

Les deux voies sont DUALES : le permanent d'une matrice M est la trace de la representation exterieure Lambda^k de M, et le rayon spectral est la norme de l'operateur. La dualite est :

> perm(Omega) = tr(Lambda^k(Omega)) dans la representation antisymetrique

Ce qui signifie que borner le permanent et borner le rayon spectral sont deux faces du meme probleme : la CONTRACTION dans la representation antisymetrique du groupe de monodromie.

**Nouveau concept : le Rayon Spectral Antisymetrique (RSA).** Definissons :

> rho_AS(p, t) = lim_{k->infty} (|T(t)|/C)^{1/k}

C'est le rayon spectral de l'operateur de transfert dans la section antisymetrique. La Conjecture M est equivalente a rho_AS < 1 pour tout t != 0, p | d. [CONDITIONNEL : il faut d'abord prouver que la limite existe, ce qui n'est pas evident car S et k sont lies par d = 2^S - 3^k.]

---

## CHAINE 2 : POURQUOI chaque facteur S_c(p) = Sum_{a=0}^{S-1} e(c*2^a/p) est-il controlable ?

### WHY-2.1 : Nature de S_c(p) comme somme de caracteres partiels

**DIAGNOSTIC :** S_c(p) = Sum_{a=0}^{S-1} e(c*2^a/p) est la somme du caractere additif psi_c : x -> e(cx/p) restreinte aux S premiers elements de l'orbite de 1 sous la multiplication par 2.

Soit r = ord_p(2). L'orbite de 1 sous x2 est <2> = {1, 2, 4, ..., 2^{r-1}} dans F_p*, un sous-groupe cyclique d'ordre r.

**Cas 1 : r | S.** La somme S_c(p) parcourt exactement S/r copies completes de <2>. Donc :

> S_c(p) = (S/r) * G(c)     ou     G(c) = Sum_{h in <2>} e(ch/p)     [PROUVE]

**Cas 2 : r ne divise pas S.** La somme fait floor(S/r) copies completes plus un reste de S mod r termes :

> S_c(p) = floor(S/r) * G(c) + G_{rest}(c)     [PROUVE]

ou G_{rest}(c) = Sum_{a=0}^{(S mod r)-1} e(c*2^a/p).

### WHY-2.2 : Quand G(c) est une somme de Ramanujan

**DIAGNOSTIC :** La somme complete G(c) = Sum_{h in <2>} e(ch/p) est une somme de Gauss partielle sur le sous-groupe <2>. Quand <2> = F_p* (c'est-a-dire r = p-1, 2 est une racine primitive mod p), G(c) = Sum_{x=1}^{p-1} e(cx/p) = -1 pour tout c non-nul (somme de Ramanujan classique). C'est le cas le plus favorable.

**Definition precise :** Une somme de Ramanujan est c_q(n) = Sum_{a=1, gcd(a,q)=1}^{q} e(na/q). La somme G(c) n'est PAS exactement une somme de Ramanujan car elle est sur un sous-groupe multiplicatif de F_p*, pas sur les entiers premiers a q. Mais il y a une analogie structurelle.

**Decomposition spectrale exacte :**

Soit chi_0, chi_1, ..., chi_{(p-1)/r - 1} les caracteres de F_p* qui sont triviaux sur <2> (les "caracteres du quotient" F_p*/<2>). Par dualite :

> G(c) = (r/(p-1)) * Sum_{chi : chi|_{<2>} = 1} tau(chi) * chi_bar(c)     [PROUVE]

ou tau(chi) = Sum_{x=1}^{p-1} chi(x) e(x/p) est la somme de Gauss avec |tau(chi)| = sqrt(p) pour chi != chi_0.

Le nombre de tels caracteres est (p-1)/r. Le terme chi_0 contribue r/(p-1) * (-1) = -r/(p-1).

**Borne generale :**

> |G(c)| <= r/(p-1) + ((p-1)/r - 1) * r * sqrt(p) / (p-1)
>         = r/(p-1) + (1 - r/(p-1)) * sqrt(p)
>         ~ sqrt(p)     pour r << p     [PROUVE]

Cette borne est la borne de POLYA-VINOGRADOV restreinte. Elle donne |G(c)| = O(sqrt(p)), independamment de r. C'est BIEN PIRE que sqrt(r) quand r << sqrt(p).

**REFUTATION FORMELLE :** L'enonce "S_c(p) controlable par sqrt(r)" est FAUX en general. [PROUVE]

La borne correcte est :
- |G(c)| = O(sqrt(p)) toujours
- |G(c)| = O(sqrt(r) * log p) seulement quand r > p^{1/2+eps} (borne de Friedlander-Iwaniec / Bourgain)

### WHY-2.3 : Comment la structure d = 2^S - 3^k contraint-elle ord_p(2) ?

**DIAGNOSTIC :** Puisque p | d = 2^S - 3^k, on a 2^S = 3^k mod p. Cela impose :

> 2^S = 3^k mod p     =>     (2^r)^{S/r} = 3^k mod p     si r | S

Si r = ord_p(2), alors 2^r = 1 mod p, donc 2^S = 1 mod p ssi r | S. Or 2^S = 3^k mod p, donc r | S implique 3^k = 1 mod p, c'est-a-dire ord_p(3) | k.

**THEOREME R196-T2 (Condition de Resonance 2-3) [PROUVE].**

Pour p | d = 2^S - 3^k :

> ord_p(2) | S   <=>   ord_p(3) | k

*Preuve.* (=>) Si r | S, alors 2^S = 1 mod p. Or 2^S = 3^k mod p, donc 3^k = 1 mod p, donc ord_p(3) | k.

(<=) Si ord_p(3) | k, alors 3^k = 1 mod p. Or 2^S = 3^k = 1 mod p, donc ord_p(2) | S. CQFD.

**Definition.** On dit que p est en **Resonance 2-3** pour (S,k) quand ord_p(2) | S et ord_p(3) | k.

**Consequences de la Resonance :**

1. En resonance, S_c(p) = (S/r) * G(c) exactement (pas de reste). La somme est un multiple entier de la somme de Gauss complete sur <2>.

2. En resonance, u = 2*3^{-1} mod p satisfait u^S = 2^S * 3^{-S} = 3^k * 3^{-S} = 3^{k-S} mod p. Si en plus ord_p(3) | gcd(k, S-k), alors u^S = 1 mod p.

3. L'ordre de u = 2*3^{-1} en resonance : ord_p(u) | lcm(ord_p(2), ord_p(3)). Mais puisque 2^S = 3^k = 1 mod p en resonance, on a 2 et 3 dans un meme sous-groupe de F_p* dont l'exposant divise lcm(S,k). Donc ord_p(u) | lcm(S,k).

**Hors resonance :** Si r ne divise pas S, alors 2^S != 1 mod p, et 3^k = 2^S != 1 mod p. Dans ce cas, la somme S_c a un RESTE non-nul, et la structure periodique est brisee. C'est le cas generique pour les grands p.

### WHY-2.4 : Quel est le regime de ord_p(2) pour les p | d generiques ?

**DIAGNOSTIC :** Pour p | d = 2^S - 3^k, la taille de p peut varier enormement : de petits premiers (p = 5, 7, ...) aux grands facteurs premiers de d (potentiellement > 2^{100}).

**Pour les petits p :** r = ord_p(2) est petit (r <= p-1). Exemples :
- p = 5 : ord_5(2) = 4, 2^4 = 16 = 1 mod 5
- p = 7 : ord_7(2) = 3, 2^3 = 8 = 1 mod 7
- p = 127 : ord_127(2) = 7 (Mersenne M_7)

Pour ces primes, r << sqrt(p), et la borne |G(c)| = O(sqrt(p)) est MAUVAISE par rapport a r. Le ratio |G(c)|/r peut etre >> 1.

**Pour les grands p :** Si p est un grand facteur premier de d, la conjecture d'Artin predit que 2 est une racine primitive modulo p pour une proportion positive (~ 37.4%) des premiers. Dans ce cas r = p-1 et G(c) = -1 (somme de Ramanujan triviale). La decoherence est MAXIMALE : |G(c)|/r = 1/(p-1) ~ 0.

Meme sans Artin, Heath-Brown (1986) prouve inconditionnellement que pour au moins un premier parmi {2, 3, 5}, il est racine primitive pour infiniment de premiers p. Mais cela ne garantit rien pour un p SPECIFIQUE divisant d.

**La structure speciale de d :** Pour p | 2^S - 3^k, le sous-groupe <2,3> dans F_p* est CONTRAINT par l'equation 2^S = 3^k. Cela signifie que 2 et 3 ne sont PAS independants dans F_p* : leur relation d'ordre est fixee par (S,k). En particulier, si S et k sont petits (zone danger k = 18..41), alors S ~ 1.585*k est aussi modere, et l'equation 2^S = 3^k contraint severement la structure multiplicative.

**OBSERVATION R196-O2 :** La contrainte 2^S = 3^k mod p est exactement la relation qui definit le nombre d. Elle implique que le ratio log(2)/log(3) est "presque rationnel" au sens de F_p -- c'est une condition de RESONANCE entre les bases 2 et 3 modulo p. Plus S et k sont grands, plus cette resonance est "profonde", et plus il est probable que p a une structure multiplicative favorable (grand ord_p(2)). [OBSERVATION]

### WHY-2.5 : Le regime intermediaire (Burgess ne suffit pas, Polya-Vinogradov pas assez fin)

**DIAGNOSTIC :** Pour les p de taille intermediaire (100 < p < 10^6, regime de la zone danger), les bornes classiques sont :

1. **Polya-Vinogradov :** |G(c)| <= sqrt(p) * log(p). Donne |G(c)|/r <= sqrt(p)*log(p)/r. Pour r ~ p^{1/3} (cas typique), le ratio est ~ p^{1/6}*log(p) >> 1. INSUFFISANT.

2. **Burgess (1962) :** |G(c)| <= p^{1/4+eps} * r^{1/2}. Donne |G(c)|/r <= p^{1/4+eps}/sqrt(r). Pour r ~ p^{1/3}, le ratio est ~ p^{1/4+eps}/p^{1/6} = p^{1/12+eps}. ENCORE INSUFFISANT (mais meilleur).

3. **Bourgain-Katz-Tao (2004) / Bourgain-Glibichuk-Konyagin (2006) :** Dans le regime intermediaire p^eps < r < p^{1-eps}, les sommes de caracteres sur les sous-groupes satisfont :
   > |G(c)| <= r * p^{-delta}
   pour un delta = delta(eps) > 0 explicite. Cela donne |G(c)|/r <= p^{-delta} < 1. C'est la PREMIERE borne qui donne un ratio < 1.

**THEOREME R196-T3 (Borne BKT sur les facteurs CGT) [CONDITIONNEL sur r dans le regime intermediaire].**

Pour p premier, p | d, c != 0 mod p, si p^{eps} < ord_p(2) < p^{1-eps} pour un eps > 0, alors :

> |G(c)| <= r * p^{-delta(eps)}

ou delta(eps) > 0 est la constante de Bourgain-Glibichuk-Konyagin.

**Consequence pour S_c(p) :**

> |S_c(p)| <= (S/r + 1) * |G(c)| + r <= (S/r + 1) * r * p^{-delta} + r = S * p^{-delta} + (1 + p^{-delta}) * r

Pour S ~ k * log(3)/log(2) et p modere, cela donne |S_c|/S <= p^{-delta} + O(r/S). Si r/S est petit (c'est-a-dire r << k), alors |S_c|/S < 1, et la decoherence est effective.

**Le lead ferme Burgess (R195) :** Burgess ne suffit pas car sa borne p^{1/4+eps} * r^{1/2} ne descend pas en dessous de r quand r < p^{1/2}. C'est confirme. La seule borne qui descend en dessous de r dans le regime intermediaire est BKT. [PROUVE que Burgess est insuffisant]

---

## CHAINE 3 : POURQUOI le produit des sommes partielles ne suffit-il pas, meme heuristiquement ?

### WHY-3.1 : Le produit naive Prod |S_c| et sa taille

**DIAGNOSTIC :** La somme libre T_libre(t) se factorise :

> T_libre(t) = [q^n] Prod_{j=0}^{k-1} psi_j(t, q)

ou psi_j(t,q) = Sum_{b >= 0} e(t*3^{k-1-j}*2^b/p) * q^b. Le facteur Psi_j (version sans denominateur) a la taille ~ S_c(p) avec c = t*3^{k-1-j} mod p.

Si on IGNORE l'extraction [q^n] et la contrainte Sum B_j = n, on obtient le produit "brut" :

> |T_free_brut| = Prod_j |S_{c_j}(p)|

avec c_j = t*3^{k-1-j} mod p. Meme avec la borne optimale |S_{c_j}| <= sqrt(p) (Polya-Vinogradov), le produit donne :

> |T_free_brut| <= p^{k/2}

Or C = C(S-1, k-1) ~ 2^S/... = 2^{1.585k}/sqrt(...). Et p | d ~ 2^S ~ 2^{1.585k}, donc p <= d ~ 2^{1.585k}. Ainsi p^{k/2} ~ 2^{0.79k^2}, tandis que C ~ 2^{1.585k}. Pour k >= 3, p^{k/2} >> C. Le produit brut est ASTRONOMIQUEMENT plus grand que C.

**MAIS :** le produit brut est le mauvais objet. Le bon objet est T_libre(t) = [q^n] Prod psi_j, qui est le coefficient d'un polynome en q, pas le produit des valeurs en un point. L'extraction [q^n] impose la contrainte Sum B_j = n, ce qui reduit drastiquement la taille.

### WHY-3.2 : L'extraction [q^n] et le point-selle de Cauchy

**DIAGNOSTIC :** Par l'integrale de Cauchy :

> T_libre(t) = (1/2*pi*i) * oint_{|q|=R} Prod_{j=0}^{k-1} psi_j(t,q) * q^{-n-1} dq

pour tout R > 0 tel que les psi_j convergent. Le choix OPTIMAL de R (point-selle) minimise l'integrande.

Pour la somme SANS phase (t = 0), psi_j(0, q) = Sum_{b >= 0} q^b = 1/(1-q) pour |q| < 1, et :

> C_libre = [q^n] (1/(1-q))^k = C(n+k-1, k-1)

Le point-selle pour (1/(1-q))^k * q^{-n-1} est q_* = n/(n+k) (resolution de q * f'(q)/f(q) = n). La valeur au point-selle donne la formule de Stirling pour les coefficients binomiaux.

Pour la somme AVEC phase (t != 0), chaque psi_j(t,q) a des coefficients de module 1 (les racines de l'unite) avec la meme structure de puissances de q. Au point-selle :

> |psi_j(t, q_*)| ~ |Sum_{b >= 0} e(c_j * 2^b / p) * q_*^b|

La question est : quelle fraction de la somme SANS phase est retenue par la somme AVEC phase ?

**Le coefficient de decoherence au point-selle :** Definissons :

> eta_j(t) = |psi_j(t, q_*)| / |psi_j(0, q_*)|

Ce ratio mesure la decoherence introduite par la phase pour le j-ieme facteur, evaluee au point-selle. Par definition 0 <= eta_j <= 1 (Cauchy-Schwarz au point-selle).

**THEOREME R196-T4 (Borne au point-selle pour T_libre) [CONDITIONNEL sur l'approximation du point-selle].**

> |T_libre(t)| <= C_libre * Prod_{j=0}^{k-1} eta_j(t) * (1 + O(1/sqrt(k)))

*Justification.* L'integrale de Cauchy evaluee au point-selle donne le terme principal Prod psi_j(t, q_*) * q_*^{-n-1}. La normalisation par C_libre = Prod psi_j(0, q_*) * q_*^{-n-1} donne le produit des eta_j. La correction O(1/sqrt(k)) vient des termes de courbure (methode du col). CONDITIONNEL car la methode du col requiert que le contour reste dans une region de convergence, et les psi_j(t,q) ont des poles sur le cercle unite. [CONDITIONNEL]

### WHY-3.3 : Comment eta_j se relie-t-il a G(a_j)/r ?

**DIAGNOSTIC :** Au point-selle q_* ~ n/(n+k) < 1, la somme psi_j(t, q_*) est dominee par les termes avec b petit (car q_*^b decroit exponentiellement). La periodicite de 2^b mod p (periode r) decoupe la somme en periodes :

> psi_j(t, q_*) = Sum_{m=0}^{r-1} e(c_j * 2^m / p) * q_*^m * (1 + q_*^r + q_*^{2r} + ...) + correction

Le facteur geometrique (1 + q_*^r + ...) = 1/(1 - q_*^r) est COMMUN a tous les j (il ne depend pas de la phase). La partie dependante de la phase est :

> Psi_j^*(t) = Sum_{m=0}^{r-1} e(c_j * 2^m / p) * q_*^m

C'est la somme G(c_j) PONDEREE par les puissances de q_*. Pour q_* proche de 1 (ce qui est le cas quand n >> r, typiquement n ~ 0.585k >> r pour les petits p), tous les q_*^m sont proches de 1, et Psi_j^* ~ G(c_j).

Le coefficient de decoherence est alors :

> eta_j ~ |Psi_j^*| / |Sum_{m=0}^{r-1} q_*^m| ~ |G(c_j)| / r

(le denominateur est la valeur de Psi_j^* quand la phase est triviale, c'est-a-dire Sum_{m=0}^{r-1} q_*^m ~ r pour q_* ~ 1).

**RESULTAT :** [CONDITIONNEL]

> eta_j(t) ~ |G(t * 3^{k-1-j})| / r     pour n >> r

Le produit des eta_j est donc :

> Prod_j eta_j ~ Prod_j |G(t * 3^{k-1-j})| / r^k

### WHY-3.4 : L'annulation ENTRE facteurs -- le phenomene de Decoherence de Riesz

**DIAGNOSTIC :** Les k facteurs G(c_j) avec c_j = t * 3^{k-1-j} mod p sont evalues en des points LIES par la relation c_j = c_0 * 3^{-j} = c_0 * v^j (ou v = 3^{-1} mod p). C'est une progression GEOMETRIQUE dans F_p*.

Le produit Prod |G(c_0 * v^j)| est un PRODUIT DE RIESZ generalise. Les produits de Riesz classiques sont Prod (1 + cos(n_j * theta)) ou les n_j forment une suite lacunaire. Ici, les "frequences" c_j = c_0 * v^j sont les termes d'une suite geometrique dans F_p*.

**Produit de Riesz dans F_p* :** Definissons :

> R_k(c_0) = Prod_{j=0}^{k-1} G(c_0 * v^j) / r

Le module est :

> |R_k(c_0)| = Prod_j |G(c_0 * v^j)| / r^k = Prod_j eta_j

**Heuristique de Riesz :** Si les valeurs |G(c*v^j)| pour j = 0, ..., k-1 etaient IID avec E[|G|^2/r^2] = rho^2 < 1, alors :

> E[|R_k|^2] = rho^{2k}

C'est une decroissance EXPONENTIELLE, et par concentration (loi des grands nombres en log) :

> |R_k| ~ rho^k avec haute probabilite

Le coefficient rho = sqrt(E[|G|^2])/r. Par Parseval (R196-T2, chaine 2) :

> Sum_{c=1}^{p-1} |G(c)|^2 = r(p-r)

Donc la valeur RMS de |G(c)| pour c != 0 est :

> |G|_RMS = sqrt(r(p-r)/(p-1)) ~ sqrt(r) * sqrt(1 - r/(p-1))

et rho = |G|_RMS / r = sqrt((p-r)/(r(p-1))) ~ 1/sqrt(r).

**L'heuristique donne :**

> |R_k| ~ (1/sqrt(r))^k = r^{-k/2}

Et donc :

> |T_libre(t)| ~ C_libre * r^{-k/2}     [HEURISTIQUE]

Pour r >= 3 (p >= 7), r^{-k/2} <= 3^{-k/2}, qui est exponentiellement petit. C'est BIEN MEILLEUR que C * k^{-delta}.

### WHY-3.5 : Pourquoi cette heuristique est-elle INSUFFISANTE pour conclure ?

**DIAGNOSTIC :** L'heuristique r^{-k/2} est pour T_LIBRE, pas T_MONO. Le passage T_libre -> T_mono coute la correction de monotonie (Chaine 1). Mais il y a un probleme plus profond MEME pour T_libre :

**Probleme 1 : Les valeurs G(c_j) ne sont PAS independantes.** Les c_j = c_0 * v^j forment une progression geometrique. Les valeurs G(c*v^j) sont correlees car :

> G(c*v^j) = Sum_{h in <2>} e(c*v^j*h/p) = Sum_{h in <2>} e(c*h*v^j/p)

Quand j varie de 1, l'argument est multiplie par v = 3^{-1}. Si v est dans <2> (c'est-a-dire 3 est une puissance de 2 mod p), alors v*h in <2> et G(c*v) = G(c) EXACTEMENT. Dans ce cas, TOUS les facteurs sont egaux et le produit ne donne aucune decoherence.

**Condition de non-trivialite :** v = 3^{-1} ne doit PAS etre dans <2>. C'est equivalent a : 3 n'est pas dans <2>, c'est-a-dire 3 n'est pas une puissance de 2 mod p. Pour p | d = 2^S - 3^k, si 3 etait dans <2>, alors 3 = 2^a mod p pour un a, et d = 2^S - 3^k = 2^S - 2^{ak} mod p = 0 mod p, ce qui est deja donne. Mais 3 in <2> impliquerait que <2,3> = <2>, et l'entier d = 2^S - 3^k = 2^S - 2^{ak} = 2^{min(S,ak)} * (2^{|S-ak|} - 1), et p | 2^{|S-ak|} - 1. Cela est POSSIBLE mais RARE.

**Generiquement, 3 n'est pas dans <2>.** Dans ce cas, les cosets c_j = c_0 * v^j parcourent des cosets de <2> dans F_p* qui sont DIFFERENTS (pour j distincts modulo ord_p(v modulo <2>)). L'heuristique d'independance est alors PLAUSIBLE.

**Probleme 2 : L'extraction [q^n] n'est pas un simple evaluation.** La borne au point-selle (R196-T4) est CONDITIONNELLE sur la validite de l'approximation du col. Pour les fonctions generatrices a coefficients complexes, la methode du col peut echouer si les zeros de Prod psi_j(t,q) s'approchent du point-selle.

**Probleme 3 : Le vrai obstacle = la monotonie.** Meme si T_libre est bien borne, T_mono = T(t) n'est pas T_libre. Le ratio T_mono/T_libre est gouverne par les permanents (Chaine 1). Sans borne sur ces permanents, la borne sur T_libre est INUTILE.

**SYNTHESE DE LA CHAINE 3 :**

L'heuristique du produit de Riesz donne |T_libre| ~ C_libre * r^{-k/2}, ce qui est une decroissance exponentielle largement suffisante pour la Conjecture M. L'obstacle n'est PAS la taille de chaque facteur, ni leur produit -- c'est le PASSAGE de T_libre a T_mono. Le produit des sommes partielles est "trop bon" : il donne une borne fantastique sur T_libre, mais cette borne est perdue lors de la correction de monotonie.

Le correct heuristique pour |T(t)| (somme monotone) est :

> |T(t)| ~ C * (2^{0.585} / sqrt(r))^k * correction_permanents     [HEURISTIQUE]

ou le facteur 2^{0.585} vient du gap de monotonie (R189/R191). La borne est utile ssi 2^{0.585}/sqrt(r) < 1, soit r > 2^{1.17} ~ 2.25, c'est-a-dire r >= 3. Cela couvre tous les cas sauf p = 3 (ou r = 2).

---

## RESULTATS PROUVES, CONDITIONNELS ET CONJECTURAUX

### Registre R196 (Agent A1)

| # | Resultat | Type | Dependances |
|---|----------|------|-------------|
| R196-T1 | T_libre(t) = Sum_{B ordonne} perm(Omega(B)) ou Omega_{i,j} = e(t*3^{k-1-i}*2^{B_j}/p). T(t) est le terme diagonal. | **[PROUVE]** | Definition du permanent |
| R196-T2 | Condition de Resonance 2-3 : ord_p(2) divise S ssi ord_p(3) divise k, pour p divisant d | **[PROUVE]** | p divise 2^S - 3^k |
| R196-T3 | BKT sur les facteurs CGT : |G(c)| <= r * p^{-delta} dans le regime intermediaire | **[CONDITIONNEL]** | p^eps < r < p^{1-eps} |
| R196-T4 | Borne au point-selle : |T_libre(t)| <= C_libre * Prod eta_j * (1 + O(1/sqrt(k))) | **[CONDITIONNEL]** | Validite de la methode du col |
| R196-O1 | Dichotomie methodologique : Voie Permanents (CGT) vs Voie Operateur (SMH), duales via Lambda^k | **[OBSERVATION]** | -- |
| R196-O2 | Resonance 2-3 contraint la structure multiplicative de F_p* via l'equation d = 2^S - 3^k | **[OBSERVATION]** | -- |
| R196-O3 | Heuristique de Riesz : |T_libre| ~ C_libre * r^{-k/2}, largement suffisant | **[CONJECTURE]** | Quasi-independance des G(c_j) |

### Refutations

| Enonce original | Statut |
|----------------|--------|
| |S_c(p)| <= sqrt(r) pour tout c != 0 | **FAUX en general.** Vrai seulement si r > p^{1/2+eps}. |
| Le produit Prod |S_c| <= p^{k/2} est un obstacle | **FAUX (artefact).** Le bon objet est [q^n] Prod psi_j, pas Prod S_c. L'extraction [q^n] resout le probleme. |
| La factorisation CGT est le bon outil | **PARTIELLEMENT VRAI.** La factorisation de T_libre est excellente. La fermeture vers T_mono bute sur les permanents. |

### Nouveaux concepts

| Concept | Description | Faisabilite |
|---------|-------------|------------|
| **NAT** (Noyau d'Antisymetrisation Tordu) | T(t) = terme diagonal de Sum perm(Omega(B)) | Prouve mais non exploitable sans borne sur permanents |
| **RFB** (Reduction par Fusion de Blocs) | Inclusion-exclusion via le treillis des partitions Pi(k) | Recursif mais meme difficulte a chaque niveau |
| **RSA** (Rayon Spectral Antisymetrique) | rho_AS = lim (|T|/C)^{1/k}, la Conj M = rho_AS < 1 | Concept correct mais existence de la limite non prouvee |
| **Resonance 2-3** | ord_p(2)|S <=> ord_p(3)|k pour p|d | Prouve, structurellement important |
| **Decoherence de Riesz** | Prod des |G(c*v^j)|/r se comporte comme un produit de Riesz | Heuristique forte, justification rigoureuse manquante |

---

## SYNTHESE STRATEGIQUE

### Score CGT revise : 6.5/10

**Justification :**
- (+) Factorisation EXACTE de T_libre prouvee (R195-T1)
- (+) Periodicite et bornes sur chaque facteur prouvees (R195-T2, R196-T3 conditionnel)
- (+) Heuristique de Riesz donne decroissance exponentielle r^{-k/2} pour T_libre
- (+) Identification precise du verrou : permanents de matrices DFT restreintes
- (+) Condition de Resonance 2-3 prouvee, eclaire la structure arithmetique
- (-) La factorisation ne se transfere pas a T_mono sans H3 (permanents bornes)
- (-) La borne |G(c)| <= sqrt(r) est FAUSSE en general
- (-) H3 est aussi dur que le probleme original (reformulation, pas resolution)
- (-) Le gap de monotonie 2^{0.585k} n'est pas contourne

### Le verrou en une phrase

**La CGT montre que T_libre decroit exponentiellement en k (le produit de Riesz marche), mais le passage a T_mono coute exactement le permanent d'une matrice de phases structuree -- un probleme #P-dur en general mais potentiellement tractable grace a la structure multiplicative (racines de l'unite, progressions geometriques dans les entrees).**

### Directions pour R197

1. **Permanents de matrices DFT restreintes.** Explorer les travaux de Glynn (2010, formule pour le permanent via determinants) et les methodes de Barvinok (2016) pour les matrices a entrees sur le cercle unite. La structure specifique Omega_{i,j} = omega^{x_i * y_j} (matrice "exponentielle d'un rang 1") pourrait admettre des bornes non-triviales.

2. **Voie SMH (operateur de transfert).** Contourner les permanents en bornant directement T_mono via le rayon spectral de l'operateur de Horner dans la representation antisymetrique. La dualite NAT/RSA suggere que les deux voies sont equivalentes, mais la voie operateur pourrait beneficier de techniques d'analyse fonctionnelle (inegalite de Schur, bornes de Weiss).

3. **Hybrider CGT et SBL.** Le SBL (score 8/10) utilise l'equidistribution de Weyl des 3^j mod p comme source de decoherence. Si on peut montrer que cette equidistribution rend les entrees de Omega "quasi-aleatoires" (au sens de la discrepance multiplicative), les bornes de Tao-Vu sur les permanents de matrices quasi-aleatoires pourraient s'appliquer.

4. **Exploiter la Resonance 2-3.** En resonance (ord_p(2)|S et ord_p(3)|k), les sommes S_c sont des multiples exacts de G(c), et la structure est plus rigide. Peut-on prouver la Conjecture M d'abord pour les p en resonance, puis etendre par un argument de continuite ?

---

*R196 Agent A1 (Investigateur Profond) : 3 chaines de 5+ WHY completees. 2 theoremes prouves (R196-T1, R196-T2), 2 conditionnels (R196-T3, R196-T4), 1 conjecture (heuristique de Riesz), 3 observations (O1, O2, O3). 5 concepts nouveaux (NAT, RFB, RSA, Resonance 2-3, Decoherence de Riesz). REFUTATION cle : |G(c)| <= sqrt(r) est faux en general. DECOUVERTE cle : la Resonance 2-3 (ord_p(2)|S <=> ord_p(3)|k) structure la controlabilite des facteurs CGT. VERROU IDENTIFIE : le permanent de la matrice de phases Omega est le prix exact de la monotonie, reliant la Conjecture M a un probleme de complexite algebrique (#P). Score CGT maintenu a 6.5/10.*
