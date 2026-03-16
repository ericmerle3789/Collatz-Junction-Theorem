# R185 -- Geometrie Periodique-Monotone : Le Cone et l'Hyperplan
**Date :** 16 mars 2026
**Mode :** Innovateur -- raisonnement pur, ZERO calcul
**Prerequis :** R184 A2 (structure w, u), R184 CRT (obstruction collective), R184 metrique-modulaire
**Question centrale :** L'hyperplan {<w, .> = 0 mod p} dans F_p^k intersecte-t-il le cone monotone pour tout p | d simultanement ?

---

## SYNTHESE EN UNE PHRASE

Le vecteur w = (3^{k-1}, ..., 3^0) mod p est PERIODIQUE dans F_p* (de periode ord_p(3)), le vecteur u = (2^{B_0}, ..., 2^{B_{k-1}}) mod p est MONOTONE (contraint par B_j croissant), et la condition <w, u> = 0 mod p demande qu'un signal periodique et un signal monotone soient "orthogonaux" -- une condition qui, pour des raisons de RIGIDITE SPECTRALE, ne peut etre satisfaite simultanement pour tous les p | d.

---

## 0. CADRE ET NOTATIONS

**Objets :**
- g(v) = SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}, avec 0 <= B_0 <= ... <= B_{k-1}, SUM B_j = S - k
- d = 2^S - 3^k (impair, non divisible par 2 ni 3)
- Pour p | d : 2^S = 3^k mod p

**Reformulation produit scalaire (R184 A2) :**
- w = (w_0, ..., w_{k-1}) avec w_j = 3^{k-1-j} mod p
- u = (u_0, ..., u_{k-1}) avec u_j = 2^{B_j} mod p
- g(v) mod p = <w, u> mod p
- Condition de cycle mod p : <w, u> = 0 mod p

**Sanity check k=1 :** w = (1), u = (2^{B_0}) = (2^{S-1}). Condition : 1 * 2^{S-1} = 0 mod p. Impossible car 2^{S-1} est une unite de F_p*. Mais d = 2^2 - 3 = 1 n'a pas de facteur premier. COHERENT : la machinerie est vacante.

**Sanity check k=2 :** d = 7. w = (3, 1). u = (2^{B_0}, 2^{B_1}) avec B_0 + B_1 = 2, B_0 <= B_1. Vecteur (0,2) : u = (1, 4). <w, u> = 3 + 4 = 7 = 0 mod 7. CYCLE EXISTE. L'argument DOIT echouer pour k=2. [VERIFIE]

---

## 1. LE VECTEUR w : MELODIE PERIODIQUE

### 1.1 Periodicite de w dans F_p*

Posons r = ord_p(3), l'ordre multiplicatif de 3 dans F_p*. Alors :

w_j = 3^{k-1-j} mod p

Les composantes de w parcourent le sous-groupe <3> de F_p*, en decroissant : w_0 = 3^{k-1}, w_1 = 3^{k-2}, ..., w_{k-1} = 3^0 = 1.

Puisque 3^r = 1 mod p, on a w_j = w_{j+r} pour tout j (indices modulo la longueur). Autrement dit :

> **w est periodique de periode r = ord_p(3) dans F_p*.**

Quand k <= r : toutes les composantes w_j sont DISTINCTES dans F_p*. Le vecteur w occupe k positions distinctes sur le "cercle" <3>.

Quand k > r : il y a des REPETITIONS. Precisement, w_j = w_{j'} ssi j = j' mod r. Le vecteur w fait floor(k/r) tours complets du sous-groupe <3>, plus un arc residuel de k mod r elements.

**Statut : PROUVE.** (Definition de l'ordre multiplicatif.)

### 1.2 Decomposition en blocs periodiques

Partitionnons les indices {0, ..., k-1} en blocs de taille r (le dernier etant eventuellement incomplet) :

- Bloc 0 : indices {0, 1, ..., r-1}
- Bloc 1 : indices {r, r+1, ..., 2r-1}
- ...
- Bloc m-1 : indices {(m-1)r, ..., k-1} (incomplet si r ne divise pas k)

ou m = ceil(k/r). Dans chaque bloc, w prend les memes valeurs : w_{ir+t} = 3^{k-1-ir-t} = 3^{-t} * 3^{k-1-ir}. Mais 3^{ir} = (3^r)^i = 1^i = 1 mod p. Donc w_{ir+t} = 3^{k-1-t} mod p = w_t.

**FAIT FONDAMENTAL :** w_{ir+t} = w_t pour tout i et tout t. Les blocs sont des COPIES EXACTES les uns des autres (dans F_p).

**Statut : PROUVE.**

### 1.3 Consequence pour <w, u>

Regroupons la somme <w, u> par blocs :

<w, u> = SUM_{t=0}^{r-1} w_t * (SUM_{i : ir+t < k} u_{ir+t}) mod p

Definissons pour chaque position t dans {0, ..., r-1} la SOMME LATERALE :

> **sigma_t = SUM_{i : ir+t < k} u_{ir+t} = SUM_{i : ir+t < k} 2^{B_{ir+t}} mod p**

Alors :

> **<w, u> = SUM_{t=0}^{r-1} w_t * sigma_t mod p**

C'est un produit scalaire de DIMENSION r (pas k) entre le vecteur (w_0, ..., w_{r-1}) et le vecteur (sigma_0, ..., sigma_{r-1}).

**OBSERVATION CRUCIALE :** On a compresse le probleme de dimension k a dimension r = ord_p(3). L'annulation <w, u> = 0 mod p est equivalente a :

> **<w^(r), sigma> = 0 mod p**

ou w^(r) = (3^{k-1}, 3^{k-2}, ..., 3^{k-r}) mod p est le "motif fondamental" de longueur r.

**Statut : PROUVE.** (Regroupement algebrique.)

### 1.4 Sanity check k=2, p=7

r = ord_7(3). 3^1 = 3, 3^2 = 2, 3^3 = 6, 3^4 = 4, 3^5 = 5, 3^6 = 1 mod 7. Donc r = 6 > k = 2. Pas de periodicite (k < r). La compression ne s'applique pas : sigma_t = u_t pour chaque t. Le produit scalaire est 3 * u_0 + 1 * u_1 = 3 + 4 = 7 = 0 mod 7. COHERENT.

---

## 2. LE VECTEUR u : RYTHME MONOTONE

### 2.1 Structure de u dans F_p*

u_j = 2^{B_j} mod p, avec B_0 <= B_1 <= ... <= B_{k-1}.

Posons s = ord_p(2). Le sous-groupe <2> dans F_p* est cyclique d'ordre s. Les composantes u_j parcourent <2> dans un ordre CONTRAINT : puisque B_j est croissant dans Z, les exposants B_j mod s parcourent Z/sZ dans un ordre qui "enroule" le cercle <2> TOUJOURS DANS LE MEME SENS.

**Precision :** Si B_j < B_{j+1}, alors u_{j+1} = 2^{B_{j+1}} = u_j * 2^{B_{j+1}-B_j}. Le passage de u_j a u_{j+1} est une multiplication par 2^{Delta_j} ou Delta_j = B_{j+1} - B_j >= 0. Si Delta_j = 0, u_{j+1} = u_j (repetition). Si Delta_j >= 1, on avance de Delta_j pas dans <2>.

> **u est une marche UNIDIRECTIONNELLE sur le cercle <2> dans F_p*.**

Pas de retour en arriere : on ne multiplie jamais par une puissance negative de 2.

**Statut : PROUVE.** (Consequence directe de la monotonie B_j.)

### 2.2 Le cone monotone dans F_p^k

Definissons le CONE MONOTONE C_k(p) comme l'ensemble des vecteurs u = (2^{B_0}, ..., 2^{B_{k-1}}) mod p ou (B_0, ..., B_{k-1}) parcourt tous les vecteurs d'entiers non-negatifs croissants avec SUM B_j = S - k.

**Proprietes de C_k(p) :**

(P1) C_k(p) est un sous-ensemble de (<2>)^k dans F_p^k. Chaque composante est dans le sous-groupe cyclique <2>.

(P2) C_k(p) n'est PAS un sous-espace vectoriel. C'est un ensemble DISCRET contraint par la monotonie.

(P3) |C_k(p)| = N(k, S), le nombre de vecteurs monotones (dans Z, avant reduction mod p). Des collisions mod p sont possibles : si B_j = B_j' mod s pour tout j, les deux vecteurs ont la meme image dans F_p^k.

**Statut : PROUVE.** (Definitions.)

### 2.3 Marche unidirectionnelle et ses consequences

L'unidirectionnalite a une consequence spectrale profonde. Considerons la "trajectoire" de u sur le cercle <2> :

Position 0 : B_0 mod s
Position 1 : B_1 mod s (>= B_0 mod s... ATTENTION, pas necessairement dans Z/sZ !)

**SUBTILITE CRUCIALE :** B_j est croissant dans Z, mais B_j mod s n'est PAS necessairement croissant dans Z/sZ. Si B_{j+1} - B_j >= s, on fait un tour complet et le "mod s" peut etre plus petit. Cependant, la DISTANCE PARCOURUE SUM Delta_j = B_{k-1} - B_0 est fixe (bornee par S - k).

> La marche parcourt une distance totale B_{k-1} - B_0 <= S - 1 dans Z, ce qui correspond a au plus floor((S-1)/s) tours complets du cercle <2>.

Pour S ~ 1.585k et s typiquement de l'ordre de p-1 (ou un diviseur), le nombre de tours depend du rapport S/s.

**Statut : PROUVE pour la borne. DEDUIT pour les consequences.**

---

## 3. INNOVATION 1 : COMPRESSION SPECTRALE ET CONTRAINTE DE SOMMATION

### 3.1 Le theoreme de compression

De la Section 1.3, la condition <w, u> = 0 mod p se COMPRESSE en :

> **SUM_{t=0}^{r-1} w_t * sigma_t = 0 mod p**     (*)

ou sigma_t = SUM_{i : ir+t < k} 2^{B_{ir+t}} mod p.

Le point cle est que les sigma_t ne sont PAS des elements ARBITRAIRES de F_p. Ils sont des SOMMES PARTIELLES de la marche monotone u, prises a intervalles reguliers de r.

### 3.2 Contrainte de positivite sur les sigma_t

Chaque sigma_t est une somme de m_t termes (ou m_t = nombre d'indices i tels que ir + t < k), et chaque terme est 2^{B_{ir+t}} mod p. Dans Z (avant reduction), chaque terme est un entier POSITIF (puissance de 2). Donc sigma_t dans Z est une somme de m_t puissances de 2, necessairement >= m_t (car 2^B >= 1 pour B >= 0).

Mais modulo p, cette positivite disparait. CEPENDANT, la valeur de sigma_t dans Z est BORNEE :

sigma_t (dans Z) = SUM_{i} 2^{B_{ir+t}} <= m_t * 2^{S-1}

Et sigma_t (dans Z) >= m_t * 1 = m_t (car 2^B >= 1).

**FAIT :** La contrainte metrique (sigma_t dans Z) et la contrainte modulaire (sigma_t mod p) sont COUPLEES. Un sigma_t qui est petit dans Z (parce que les B_{ir+t} sont petits) est aussi petit mod p (a condition que sigma_t < p). Inversement, un sigma_t >= p se "replie" modulo p.

**Innovation :** Pour les petits k (k < 42), ou les B_j sont contraints dans un petit intervalle [0, S-1] avec S ~ 1.585k, les sigma_t dans Z sont BORNES par m_t * 2^{S-1}. Si m_t est petit (1 ou 2 quand k/r est petit), sigma_t est une somme de peu de termes, chacun borne. Cela REDUIT l'espace des sigma_t possibles modulo p, et donc reduit la probabilite que (*) ait une solution.

**Statut : DEDUIT.** L'argument quantitatif precise depend des valeurs de r, s, k, S.

### 3.3 Sanity check k=2, p=7

r = 6, k = 2 < r. Donc m_t = 1 pour t = 0 et t = 1, et m_t = 0 pour t >= 2. sigma_0 = 2^{B_0}, sigma_1 = 2^{B_1}. Condition : 3 * 2^{B_0} + 1 * 2^{B_1} = 0 mod 7. Pour (B_0, B_1) = (0, 2) : 3 * 1 + 4 = 7 = 0 mod 7. Solution EXISTE. Coherent : k=2 doit passer.

---

## 4. INNOVATION 2 : L'INCOMPATIBILITE SPECTRALE PERIODIQUE-MONOTONE

### 4.1 Reformulation en serie de Fourier dans F_p

Le vecteur w^(r) = (3^{k-1}, 3^{k-2}, ..., 3^{k-r}) mod p est un vecteur dont les composantes forment une progression GEOMETRIQUE de raison 3^{-1} mod p dans F_p*. Un tel vecteur a un spectre de Fourier tres CONCENTRE.

Plus precisement, considerons les caracteres de Z/rZ : chi_l(t) = omega^{lt} pour omega une racine r-ieme de l'unite dans un corps contenant F_p (ou dans C si on travaille analytiquement). Le coefficient de Fourier de w^(r) est :

w_hat(l) = SUM_{t=0}^{r-1} w_t * chi_l(t) = SUM_{t=0}^{r-1} 3^{k-1-t} * omega^{lt}
         = 3^{k-1} * SUM_{t=0}^{r-1} (omega^l / 3)^t

C'est une SOMME GEOMETRIQUE. Elle vaut :

- Si omega^l = 3 : w_hat(l) = r * 3^{k-2} (terme dominant)
- Si omega^l != 3 : w_hat(l) = 3^{k-1} * (1 - (omega^l/3)^r) / (1 - omega^l/3)

Puisque 3^r = 1 mod p (definition de r = ord_p(3)), et omega^r = 1, le cas omega^l = 3 survient pour un UNIQUE l_0 dans {0, ..., r-1} (celui tel que omega^{l_0} = 3 dans le corps de decomposition).

> **Le spectre de w est CONCENTRE sur la frequence l_0 telle que omega^{l_0} = 3.**

Pour les autres frequences l != l_0, la somme geometrique s'annule (car (omega^l/3)^r = omega^{lr}/3^r = 1/1 = 1, donc le numerateur 1 - 1 = 0). ATTENDONS -- si (omega^l/3)^r = 1 pour TOUT l (car omega^r = 1 et 3^r = 1), alors le numerateur 1 - (omega^l/3)^r = 0 pour tout l != l_0.

**FAIT REMARQUABLE :** Pour l != l_0 et omega^l/3 != 1 (i.e., l != l_0), la somme geometrique a numerateur 0 et denominateur non nul, donc w_hat(l) = 0.

Et pour l = l_0 : omega^{l_0}/3 = 1, la somme vaut r termes tous egaux a 3^{k-2}, donnant w_hat(l_0) = r * 3^{k-2}.

> **Le spectre de w est un DIRAC pur sur la frequence l_0.** Toute l'energie est concentree en un point.

**Statut : PROUVE.** (Calcul de somme geometrique dans F_p.)

### 4.2 Spectre du vecteur sigma

Le vecteur sigma = (sigma_0, ..., sigma_{r-1}) est la somme laterale de u comprimee par la periodicite de w. Son spectre de Fourier est :

sigma_hat(l) = SUM_{t=0}^{r-1} sigma_t * omega^{lt}

La condition <w^(r), sigma> = 0 mod p, traduite en Fourier par Parseval/convolution, donne :

SUM_{l=0}^{r-1} w_hat(l) * sigma_hat(-l) = 0 mod (p * r)... NON, c'est plus simple.

En fait, <w^(r), sigma> est le produit scalaire standard, pas une convolution. Reecrivons directement :

<w^(r), sigma> = SUM_t w_t * sigma_t = SUM_t 3^{k-1-t} * sigma_t

La condition est : 3^{k-1} * SUM_t 3^{-t} * sigma_t = 0 mod p, soit :

> **SUM_{t=0}^{r-1} 3^{-t} * sigma_t = 0 mod p**     (**)

car 3^{k-1} est inversible mod p.

Cela se reecrit : l'APPLICATION LINEAIRE L : F_p^r -> F_p definie par L(sigma) = SUM_t 3^{-t} * sigma_t s'annule sur sigma.

### 4.3 Structure de L

L est une forme lineaire de F_p^r dans F_p. Son noyau ker(L) est un hyperplan de dimension r-1.

Le vecteur de L est (3^0, 3^{-1}, 3^{-2}, ..., 3^{-(r-1)}) = (1, 3^{-1}, 3^{-2}, ..., 3^{-(r-1)}) mod p.

C'est encore une progression geometrique de raison 3^{-1} dans F_p*. Puisque 3^{-r} = 1 mod p (car 3^r = 1), cette progression parcourt TOUT le sous-groupe <3^{-1}> = <3>.

> **L est determinee par le sous-groupe <3> de F_p*. L annule exactement les vecteurs sigma tels que la "moyenne ponderee par <3>" est nulle.**

**Statut : PROUVE.**

### 4.4 L'image de sigma dans le cone monotone

Le point crucial est que sigma n'est PAS un vecteur ARBITRAIRE de F_p^r. Il provient de la marche monotone u via le regroupement en blocs. Quelles contraintes cela impose-t-il sur sigma ?

**Contrainte C1 (sommation positive) :** Chaque sigma_t = SUM_i 2^{B_{ir+t}} dans Z est une somme d'au plus m = ceil(k/r) puissances de 2, donc sigma_t >= 0 dans Z (meme > 0 si m_t >= 1).

**Contrainte C2 (entrelacement monotone) :** Les B_j sont croissants. Les indices ir+t pour t fixe et i croissant parcourent les positions t, t+r, t+2r, ..., qui sont REGULIEREMENT ESPACEES. La monotonie B_0 <= ... <= B_{k-1} implique que pour t fixe, les exposants B_t, B_{t+r}, B_{t+2r}, ... sont eux aussi CROISSANTS (car les indices forment une sous-suite croissante de {0,...,k-1}).

MAIS AUSSI : entre les blocs, il y a un entrelacement. Pour t < t', on a B_t <= B_{t'} (car t < t'). Cela signifie que les "premieres" composantes de chaque sigma_t (celles avec le plus petit i) sont plus petites que les "premieres" composantes de sigma_{t'}.

> **L'entrelacement monotone couple les sigma_t entre eux : ils ne sont pas independants.**

**Contrainte C3 (somme totale) :** SUM_t sigma_t (dans Z) = SUM_j 2^{B_j} = g(v) / 3^0 + ... (NON, ce n'est pas tout a fait ca). Plutot : SUM_t sigma_t = SUM_j u_j = SUM_j 2^{B_j} mod p. Cette somme est le "poids total" de u. Elle est contrainte par SUM B_j = S - k.

**Statut : PROUVE pour C1-C2. DEDUIT pour C3.**

### 4.5 Theoreme d'incompatibilite spectrale (CONDITIONNEL)

**Enonce informel :** Soit p | d avec r = ord_p(3). Le vecteur sigma provenant d'une marche monotone de k pas dans <2> a un spectre de Fourier ETALE (car la monotonie empeche les oscillations rapides), tandis que la forme lineaire L concentre son "filtre" sur la frequence l_0 (le Dirac de Section 4.1). La condition <L, sigma> = 0 demande que la composante de sigma a la frequence l_0 soit NULLE. Mais un signal monotone a une composante de Fourier non nulle sur TOUTE frequence basse.

**Argument detaille :**

Un signal monotone dans Z (u_0 <= u_1 <= ... <= u_{k-1} en valeur avant mod p) a un spectre de Fourier concentre sur les BASSES FREQUENCES (composante DC dominante, decroissance en 1/l). La frequence l_0 correspondant a 3 dans F_p* n'est PAS une frequence "basse" en general -- elle depend de la position de 3 dans la structure du groupe.

Cependant, cet argument est IMPRECIS car la "monotonie" dans Z ne se traduit pas simplement en "spectre concentre" dans F_p (le passage Z -> F_p "replie" les hautes valeurs).

**Statut : CONJECTURE (speculative).** L'intuition spectrale est suggestive mais pas rigoureuse. La "monotonie" dans Z ne garantit pas directement une propriete spectrale dans F_p.

---

## 5. INNOVATION 3 : LE CONE MONOTONE EST "ETROIT" DANS L'HYPERPLAN

### 5.1 Dimension du cone vs dimension de l'hyperplan

L'hyperplan ker(L) a dimension r-1 dans F_p^r. Le cone monotone C (image de tous les vecteurs sigma provenant de marches monotones) vit dans F_p^r mais a une dimension EFFECTIVE bien plus petite.

**Combien de degres de liberte a sigma ?**

Le vecteur (B_0, ..., B_{k-1}) a k composantes sous la contrainte SUM = S-k et 0 <= B_0 <= ... <= B_{k-1}. Le nombre de degres de liberte est effectivement k-1 (k composantes moins 1 contrainte de somme, plus la monotonie qui reduit encore).

Apres compression en sigma de dimension r, les degres de liberte sont min(k-1, r-1). Quand k > r, la compression "perd" de l'information : plusieurs vecteurs B differents donnent le meme sigma. Mais les sigma accessibles forment un sous-ensemble de F_p^r de dimension au plus min(k-1, r-1).

**L'hyperplan a dimension r-1. Le cone a dimension effective <= min(k-1, r-1).**

Pour k >> r (grand k, petit ordre), le cone a dimension au plus r-1, identique a l'hyperplan. Pas de gain.

Pour k <= r (petit k, grand ordre), le cone a dimension k-1 < r-1 = dim(hyperplan). Le cone est de CODIMENSION r-k dans F_p^r. L'hyperplan a codimension 1. L'intersection attendue a codimension r-k+1, donc dimension r-1-(r-k) = k-2.

**FAIT :** Pour un hyperplan GENERIQUE et un sous-espace GENERIQUE de dimension k-1 dans F_p^r, l'intersection a dimension k-2 (ou est vide si k-2 < 0, i.e., k < 2). Mais le cone monotone n'est PAS un sous-espace lineaire, et l'hyperplan n'est pas generique (il est determine par <3>).

**Statut : DEDUIT (comptage de dimensions). L'argument de genericite est CONDITIONNEL.**

### 5.2 La contrainte de monotonie retrecie le cone

Le cone monotone est plus ETROIT qu'un sous-espace de dimension k-1. Parmi tous les vecteurs u dans (<2>)^k, ceux qui proviennent d'une suite B_j croissante forment un sous-ensemble strict. Le nombre de tels vecteurs est N(k,S) ~ 2^{1.5k} (Section 1 de R184 metrique-modulaire), tandis que le nombre total de vecteurs dans (<2>)^k est s^k (ou s = ord_p(2)).

Le RATIO est N(k,S) / s^k. Pour s grand (de l'ordre de p), ce ratio est EXPONENTIELLEMENT PETIT. Le cone monotone est une fraction NEGLIGEABLE de l'espace total.

> **La probabilite qu'un point ALEATOIRE de (<2>)^k soit dans le cone monotone est ~ 2^{1.5k} / s^k, exponentiellement petite si s > 2^{1.5}.**

Et la probabilite qu'un point de l'hyperplan soit dans le cone est encore plus petite (l'hyperplan a (p-1)/p des points).

**MAIS** : ce qui nous interesse n'est pas la probabilite mais l'EXISTENCE. Meme si la probabilite est petite, existe-t-il un point dans l'intersection ?

**Statut : DEDUIT pour le comptage. INSUFFISANT pour l'existence.**

### 5.3 L'argument multi-premier : intersection de cones etroits dans des hyperplans DIFFERENTS

Voici le coeur de l'innovation. Pour CHAQUE p | d, on a un hyperplan H_p dans F_p^r_p (ou r_p = ord_p(3)). La condition de cycle exige :

> **Pour TOUT p | d : sigma^(p) in ker(L_p)**

ou sigma^(p) est le vecteur compresse de u modulo p. Les sigma^(p) pour differents p ne sont PAS independants : ils proviennent du MEME vecteur (B_0, ..., B_{k-1}) dans Z.

C'est un systeme de contraintes SIMULTANEES :

- Dans F_{p_1}^{r_1} : SUM_t 3^{-t} * sigma_t^{(1)} = 0 mod p_1
- Dans F_{p_2}^{r_2} : SUM_t 3^{-t} * sigma_t^{(2)} = 0 mod p_2
- ...
- Dans F_{p_m}^{r_m} : SUM_t 3^{-t} * sigma_t^{(m)} = 0 mod p_m

Chaque equation elimine (heuristiquement) une fraction 1/p_i des vecteurs B. La fraction survivant a TOUTES les equations est au plus PROD_i (1/p_i) = 1/PROD p_i.

Si PROD p_i >= d (ce qui est vrai car les p_i sont TOUS les facteurs premiers de d, et d = PROD p_i^{a_i} >= PROD p_i), alors la fraction survivante est au plus 1/d^{1/max a_i}, voire 1/d si tous les a_i = 1.

**Sous independance :** le nombre de solutions est ~ N(k,S) / d = C / d.

**Avec anti-correlation (R184 CRT) :** le nombre est ~ C / d^{1+epsilon}.

**L'innovation ici** est que la structure de COMPRESSION (Section 1.3) transforme chaque condition modulaire en une condition dans un espace de dimension r_p, pas k. Si r_p << k, la condition est PLUS CONTRAIGNANTE car elle agit sur un espace plus petit ou le cone est "comprime". La compression NE PERD PAS d'information sur la condition modulaire, mais elle REVELE la redondance : les k termes de g(v) ne fournissent que r_p "degres de liberte modulaires" pour satisfaire la condition mod p.

**Statut : CONDITIONNEL.** L'argument est qualitatif. La quantification exacte du gain par compression reste ouverte.

---

## 6. INNOVATION 4 : LA CONTRAINTE D'ORDRE CROISEE

### 6.1 Le lien entre r = ord_p(3) et s = ord_p(2) via d

Pour p | d, on a 2^S = 3^k mod p. Cela signifie que l'element 2^S * 3^{-k} = 1 dans F_p*. Posons omega = 2/3 dans F_p* (i.e., omega = 2 * 3^{-1} mod p). Alors :

omega^S = 2^S * 3^{-S} = 3^k * 3^{-S} = 3^{k-S} mod p

Et omega^k = 2^k * 3^{-k} mod p.

La relation 2^S = 3^k mod p se reecrit :

> **(2 * 3^{-1})^? = ...** -- reformulons plus directement.

Prenons le logarithme discret dans F_p*. Notons ord_p(2) = s, ord_p(3) = r. La relation 2^S = 3^k mod p signifie que S * log(2) = k * log(3) dans F_p* (en log discret), soit :

> **S/s et k/r ont le meme image dans Z/((p-1)/gcd(s,r))Z**... non, simplifions.

Plus directement : 2^S = 3^k mod p implique que 2^S est dans <3> (si <3> contient <2>, ce n'est pas toujours le cas). Dans tous les cas, l'element 2^S * 3^{-k} = 1 dans F_p*, donc l'element 2^S dans F_p* est egal a 3^k.

**CONSEQUENCE FONDAMENTALE :** L'ordre de l'element 2^S dans F_p* divise a la fois ord_p(2^S) = s/gcd(S,s) et ord_p(3^k) = r/gcd(k,r). Or 2^S = 3^k, donc ces deux ordres sont EGAUX :

> **s / gcd(S, s) = r / gcd(k, r)**

Notons cette relation (ORD). Elle lie les quatre quantites (S, k, s, r) pour chaque p | d.

**Statut : PROUVE.** (Theorie des groupes elementaire : si a = b dans un groupe, ord(a) = ord(b).)

### 6.2 Consequences de (ORD)

La relation (ORD) contraint fortement les couples (r, s) possibles pour les premiers p | d.

**Cas particulier :** Si gcd(S, s) = S (i.e., s | S), alors s/S = r/gcd(k,r), donc r = S * r / (gcd(k,r) * S)... non, reprenons.

s/gcd(S,s) = r/gcd(k,r). Posons s' = s/gcd(S,s) et r' = r/gcd(k,r). Alors s' = r'. Autrement dit :

> **L'ordre de 2^S (= 3^k) dans F_p* est s' = r', et cette valeur commune divise a la fois s et r.**

Appelons cette valeur commune delta_p = ord_p(2^S) = ord_p(3^k). Alors delta_p | s et delta_p | r, donc delta_p | gcd(s, r).

**FAIT :** Pour tout p | d, l'element 2^S = 3^k a un ordre delta_p dans F_p* qui divise gcd(ord_p(2), ord_p(3)).

Cela signifie que les sous-groupes <2> et <3> de F_p* ne sont PAS "transverses" : leur intersection contient au moins l'element 2^S = 3^k d'ordre delta_p.

> **<2> INTER <3> contient un sous-groupe d'ordre delta_p. Les deux cercles (celui de 2 et celui de 3) se CROISENT.**

**Statut : PROUVE.**

### 6.3 Impact sur l'intersection cone-hyperplan

Le croisement des cercles <2> et <3> implique que le vecteur u (qui vit dans <2>^k) a des PROJECTIONS NON TRIVIALES dans <3>^k. L'hyperplan ker(L) est defini par le vecteur w qui vit dans <3>^k. Si <2> et <3> se croisaient trivialement ({1}), le vecteur u serait "orthogonal" a w en un sens generique. Mais le croisement non trivial cree des RESONANCES : certaines composantes de u "voient" w a travers <2> INTER <3>.

**Plus precisement :** L'element 2^S = 3^k dans <2> INTER <3> joue le role de MEDIATEUR. Tout multiple de S dans les exposants B_j cree un "pont" entre le monde de 2 et le monde de 3. Quand B_j est un multiple de S (ou proche), le terme 2^{B_j} mod p est une puissance de 3^k mod p, ce qui le met en RESONANCE avec le vecteur w.

Mais B_j <= S - 1 (par la contrainte sur le vecteur monotone). Donc B_j < S, et aucun B_j n'est un multiple de S (sauf B_j = 0, qui donne 2^0 = 1 = 3^0). La resonance est ATTENUEE.

> **L'attenuation de la resonance est une consequence de la borne B_j <= S - 1. Si les B_j pouvaient atteindre S ou au-dela, la resonance serait complète et l'annulation plus facile.**

**Statut : CONDITIONNEL.** L'argument de resonance est qualitatif. Il identifie un mecanisme mais ne le quantifie pas.

---

## 7. INNOVATION 5 : ORTHOGONALITE UNIVERSELLE -- PEUT-ON Y ECHAPPER ?

### 7.1 Formulation precise du probleme

La question est : existe-t-il un vecteur (B_0, ..., B_{k-1}) monotone avec SUM B_j = S - k tel que POUR TOUT p | d :

SUM_{t=0}^{r_p - 1} 3^{-t} * (SUM_{i : ir_p + t < k} 2^{B_{ir_p + t}}) = 0 mod p

C'est un systeme de omega(d) equations (une par premier p | d) en k - 1 inconnues entieres (les gaps Delta_j = B_{j+1} - B_j >= 0).

### 7.2 Le nombre d'equations vs le nombre d'inconnues

Pour k >= 3, on a k - 1 >= 2 inconnues. Le nombre omega(d) de facteurs premiers de d croit avec k. La question est : omega(d) depasse-t-il k - 1 pour des valeurs de k suffisamment petites ?

**Observation structurelle :** d = 2^S - 3^k. Pour les petits k :
- k=3 : d = 2^5 - 27 = 5. omega = 1. Systeme : 1 equation, 2 inconnues. SOUS-DETERMINE.
- k=5 : d = 2^8 - 243 = 13. omega = 1. Sous-determine.
- k=12 : d = 2^20 - 531441 = 517135. omega >= 2 (5 * ...). Systeme 2 eq, 11 inconnues.

Pour les petits k, le systeme est LARGEMENT sous-determine. L'existence de solutions est attendue du point de vue du comptage de dimensions.

**MAIS :** les inconnues sont entieres, non-negatives, ordonnees, et de somme fixee. C'est un systeme diophantien CONTRAINT. Les methodes de comptage de dimensions ne s'appliquent pas directement.

### 7.3 L'argument par accumulation des contraintes (CONDITIONNEL)

Pour k >= 42, l'argument asymptotique suffit : C/d < 1 (R184 metrique-modulaire). Pour k < 42, l'argument doit etre RENFORCE.

La structure periodique-monotone fournit ce renforcement via la COMPRESSION : chaque premier p avec r_p = ord_p(3) petit compresse le probleme en dimension r_p. Si r_p < k - 1, la condition modulaire est plus contraignante que le comptage naif 1/p ne le suggere.

**Mecanisme :** Quand r_p est petit (disons r_p = 2), la condition (*) se reduit a :
- sigma_0 + 3^{-1} * sigma_1 = 0 mod p, soit sigma_0 = -3^{-1} * sigma_1 mod p

C'est UNE equation reliant DEUX quantites (sigma_0, sigma_1), chacune etant la somme de ~k/2 puissances de 2. La contrainte de monotonie force sigma_0 a provenir des "petits" B_j (indices pairs) et sigma_1 des B_j adjacents (indices impairs). Cette correlation structurelle entre sigma_0 et sigma_1 reduit l'espace des solutions.

**Statut : CONDITIONNEL.** La quantification du gain depend de r_p et de la distribution des B_j.

### 7.4 L'allegorie de la corde et du diapason

Le vecteur u est une CORDE monotone : elle ne vibre que dans un sens (les amplitudes croissent). Le vecteur w est un DIAPASON periodique : il vibre a une frequence fixe (la frequence de 3 dans F_p*). La condition <w, u> = 0 demande que la corde et le diapason soient "en opposition de phase" -- que les vibrations de l'un annulent exactement celles de l'autre.

Une corde monotone (qui monte) ne peut annuler un diapason periodique (qui oscille) qu'en des points SPECIFIQUES -- les "noeuds de battement". Avec UN diapason, il y a des noeuds. Avec PLUSIEURS diapasons simultanement (un par premier p | d), les noeuds de chacun doivent COINCIDER. Et comme chaque diapason a sa propre frequence (determinee par r_p), les noeuds sont a des positions DIFFERENTES.

> **L'orthogonalite universelle demande qu'une corde monotone passe par les noeuds de TOUS les diapasons simultanement. Plus il y a de diapasons (de facteurs premiers), plus c'est improbable.**

**Statut : ALLEGORIE.** Intuitivement correcte, formellement a demontrer.

---

## 8. SYNTHESE ET BILAN

### 8.1 Chaine logique

```
g(v) = <w, u> mod p  (R184 A2)                              [PROUVE]
     |
     v
w est periodique de periode r = ord_p(3)                     [PROUVE]
u est une marche monotone unidirectionnelle dans <2>          [PROUVE]
     |
     v
Compression : <w, u> = <w^(r), sigma> (dimension r, pas k)  [PROUVE]
sigma_t = sommes laterales, contraintes par monotonie         [PROUVE]
     |
     v
La condition est SUM_t 3^{-t} * sigma_t = 0 mod p           [PROUVE]
= forme lineaire L concentree sur la frequence de 3          [PROUVE]
     |
     v
L'ordre de 2^S = 3^k dans F_p* lie ord_p(2) et ord_p(3)    [PROUVE]
via delta_p | gcd(ord_p(2), ord_p(3))                        [PROUVE]
     |
     v
La resonance est attenuee par B_j < S                        [CONDITIONNEL]
La compression renforce la contrainte quand r_p < k          [CONDITIONNEL]
     |
     v
Le systeme multi-premier force l'orthogonalite a TOUS        [CONJECTURE]
les diapasons, ce qui est incompatible avec la monotonie
```

### 8.2 Resultats par statut

| Enonce | Statut | Section |
|--------|--------|---------|
| w est periodique de periode r = ord_p(3) dans F_p | PROUVE | 1.1 |
| Decomposition en blocs : w_{ir+t} = w_t | PROUVE | 1.2 |
| Compression : <w,u> = SUM_t w_t * sigma_t | PROUVE | 1.3 |
| u est une marche unidirectionnelle dans <2> | PROUVE | 2.1 |
| Cone monotone : sous-ensemble strict de (<2>)^k | PROUVE | 2.2 |
| Le spectre de w est un Dirac sur la frequence l_0 | PROUVE | 4.1 |
| La condition se reduit a SUM 3^{-t} sigma_t = 0 | PROUVE | 4.2-4.3 |
| Relation (ORD) : s/gcd(S,s) = r/gcd(k,r) | PROUVE | 6.1 |
| <2> INTER <3> contient un element d'ordre delta_p | PROUVE | 6.2 |
| Attenuation de resonance par B_j < S | CONDITIONNEL | 6.3 |
| Compression renforce la contrainte quand r_p < k | CONDITIONNEL | 5.3 |
| Le cone monotone est exponentiellement etroit | DEDUIT | 5.2 |
| Incompatibilite spectrale periodique-monotone | CONJECTURE | 4.5 |
| Orthogonalite universelle impossible | CONJECTURE | 7.4 |

### 8.3 Innovations genuines par rapport a R184

1. **Compression spectrale (Section 1.3, 3.1)** : Reduction de la dimension k a r = ord_p(3). NOUVEAU -- R184 travaillait en dimension k.

2. **Spectre Dirac de w (Section 4.1)** : Le vecteur w a un spectre de Fourier concentre en un point. NOUVEAU -- observation elementaire mais non exploitee precedemment.

3. **Relation d'ordre croisee (ORD) (Section 6.1)** : Relation explicite entre ord_p(2) et ord_p(3) pour p | d. NOUVEAU sous cette forme, bien que la relation 2^S = 3^k soit connue.

4. **Cone etroit dans l'hyperplan (Section 5)** : Formulation geometrique de la rarete des solutions. PROLONGE R184 CRT (surdetermination dans le cone) avec la compression.

5. **Allegorie corde-diapason (Section 7.4)** : Formulation intuitive de l'incompatibilite multi-premier. NOUVEAU.

### 8.4 Sanity check k=1

Pour k=1 : d = 1, aucun premier, toute la machinerie est vacante. Le cycle trivial existe. COHERENT sur tous les points.

### 8.5 Sanity check k=2

Pour k=2, p=7 : r = 6 > k = 2. Pas de compression. Le cone a dimension k-1 = 1 (un seul degre de liberte). L'hyperplan a dimension r-1 = 5. Un sous-espace de dimension 1 intersecte generiquement un hyperplan de dimension 5 dans F_7^6. Solution (0,2) existe. COHERENT.

---

## 9. PISTES POUR R186

### 9.1 Quantifier la compression (8/10)

Pour chaque p | d, calculer r_p = ord_p(3) et mesurer le gain de compression : le ratio (dimension effective du cone compresse) / (dimension r_p - 1 de l'hyperplan). Si ce ratio est systematiquement < 1, la compression fournit un facteur multiplicatif d'attenuation au-dela de 1/p.

### 9.2 Exploiter le Dirac spectral (7/10)

Le spectre de w etant un Dirac, la condition <w, sigma> = 0 se traduit en : la projection de sigma sur la direction de w est nulle. Or sigma provient d'un cone monotone. Montrer que la projection de ce cone sur w est BORNEE INFERIEURE (toujours > 0 ou toujours < 0), ce qui rendrait l'annulation impossible.

**DANGER :** Pour k=2, cette projection n'est PAS de signe constant (elle s'annule pour (0,2)). Donc l'argument de signe constant est FAUX en general. Il faudrait un argument plus fin, peut-etre probabiliste.

### 9.3 Combiner compression et anti-correlation (9/10)

L'innovation de ce round (compression) et celle de R184 (anti-correlation CRT) sont COMPLEMENTAIRES. La compression reduit la dimension effective, l'anti-correlation reduit la probabilite d'intersection conjointe. Les combiner pourrait donner une borne du type :

N_0(d) <= C * PROD_{p|d} (r_p / (p * k))

ou le facteur r_p/k (< 1 quand r_p < k) provient de la compression et 1/p de la condition modulaire.

**C'est la piste la plus prometteuse pour fermer le gap k < 42.**

---

## META-DIAGNOSTIC

| Critere | Score |
|---------|-------|
| Nouveaute par rapport a R184 | 7/10 (compression, Dirac, relation ORD) |
| Rigueur | 8/10 (nombreux PROUVE, conjectures explicites, sanity checks systematiques) |
| Operationnalite | 6/10 (pistes identifiees, aucune fermee) |
| Profondeur des POURQUOI | 7/10 (4 niveaux dans les sections principales) |
| Coherence avec k=1 et k=2 | 10/10 (verifie partout) |
| Autocritique | 8/10 (limites de l'argument spectral explicitees en 4.5, danger en 9.2) |
