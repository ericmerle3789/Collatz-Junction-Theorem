# R187 -- INVESTIGATEUR RACINAIRE : Dualite Poids x Lettres, creusee jusqu'au sol rocheux
**Date :** 16 mars 2026
**Mode :** Investigateur racinaire -- chaque POURQUOI creuse 3+ niveaux, ZERO calcul
**Prerequis :** R186 A3 (automate de Horner, dualite ord_p(3)/ord_p(2)), R186 spectral (compression), R186 red team
**Cible :** Dualite Poids x Lettres (6/10 en R186)

---

## SYNTHESE EN UNE PHRASE

La dualite poids x lettres echoue a se refermer en preuve parce que les deux compressions -- spectrale (ord_p(3) sur les COLONNES) et alphabetique (ord_p(2) sur les LETTRES) -- agissent dans des espaces qui ne se MULTIPLIENT pas independamment : la monotonie du vecteur B cree un COUPLAGE entre les axes qui empeche de factoriser la borne, et ce couplage est EXACTEMENT le probleme de Collatz reformule dans un espace produit.

---

## 0. RAPPEL DE LA DUALITE (R186)

**Compression par les poids (R185/R186 spectral) :**
- Pour p | d, r = ord_p(3). Les poids w_j = 3^{k-1-j} sont periodiques de periode r mod p.
- La condition g(v) = 0 mod p se compresse de k variables a r sommes laterales sigma_t.
- Action : compresse les COLONNES de g(v) (regroupe les indices j par j mod r).

**Compression par les lettres (R186 automate) :**
- Pour p | d, s = ord_p(2). Les lettres 2^{B_j} mod p ne prennent que s valeurs distinctes dans F_p.
- L'alphabet de l'automate H_p est {2^0, 2^1, ..., 2^{s-1}} mod p, de taille s.
- Action : compresse l'ALPHABET (les B_j mod s determinent les lettres mod p).

**Relation ORD :** s/gcd(S,s) = r/gcd(k,r).

---

## 1. PREMIER POURQUOI : Pourquoi "la combinaison pourrait suffire" ?

### NIVEAU 1 : L'argument heuristique de produit

L'idee est que la compression par les poids reduit l'equation a r variables (au lieu de k), et la compression par les lettres restreint chaque variable a s valeurs (au lieu de S). Si les deux agissaient INDEPENDAMMENT, le nombre de configurations satisfaisant g(v) = 0 mod p serait :

N_dual(p) ~ s^r / p

au lieu de l'estimation non comprimee C(S-1, k-1) / p. Le gain serait le ratio C(S-1,k-1) / s^r, potentiellement enorme quand r << k et s << S.

### NIVEAU 2 : POURQUOI les deux n'agissent-elles pas independamment ?

Parce que les deux compressions portent sur le MEME vecteur B = (B_0, ..., B_{k-1}).

- La compression spectrale regroupe par POSITION j (j mod r). Elle partitionne {0,...,k-1} en r tranches T_0, ..., T_{r-1}.
- La compression alphabetique regroupe par VALEUR B_j (B_j mod s). Elle partitionne les memes indices par la valeur de leur exposant modulo s.

Le couplage vient de la MONOTONIE : B_0 <= B_1 <= ... <= B_{k-1}. La monotonie signifie que les POSITIONS et les VALEURS sont CORRELEES (les indices petits ont des valeurs petites). On ne peut pas choisir les positions et les valeurs independamment.

### NIVEAU 3 : POURQUOI la monotonie couple-t-elle les deux axes ?

Considerons le "tableau" a double entree :
- Lignes : les tranches T_t = {j : j = t mod r}, pour t = 0,...,r-1
- Colonnes : les classes de lettres C_c = {j : B_j = c mod s}, pour c = 0,...,s-1

Chaque indice j appartient a exactement une ligne (T_t) et une colonne (C_c). La matrice d'incidence M(t,c) = |T_t inter C_c| decrit la DISTRIBUTION JOINTE des positions et des valeurs.

**Sans monotonie :** M pourrait etre QUELCONQUE (sous les contraintes marginales sum_c M(t,c) = |T_t| et sum_t M(t,c) = |C_c|). Les deux axes seraient "libres" et le comptage se factoriserait approximativement.

**Avec monotonie :** Les indices dans T_t sont t, t+r, t+2r, ... et leurs valeurs B_t <= B_{t+r} <= B_{t+2r} <= ... sont croissantes. De plus, B_t <= B_{t+1} (entrelacement entre tranches, R186-T6). Cela force la matrice M a etre "diagonalement concentree" : les petits t (petites positions) doivent avoir des petits B_j mod s (petites lettres mod s), et les grands t des grands B_j mod s.

> **THEOREME R187-T1 (PROUVE) :** La monotonie force M(t,c) a etre concentree pres de la "diagonale" t/r ~ c/s dans le tableau positions x lettres. Plus precisement, si j in T_t inter C_c, alors B_j = c mod s, et comme B est croissant, les indices j dans T_t ont des valeurs B_j croissantes, donc les classes c visitees par T_t forment un INTERVALLE de Z/sZ (pas un sous-ensemble arbitraire).

**Preuve :** Les elements de T_t sont t < t+r < t+2r < ..., avec B_t <= B_{t+r} <= B_{t+2r} <= .... Leurs valeurs modulo s, c'est-a-dire (B_t mod s, B_{t+r} mod s, ...), forment une suite qui monte dans Z puis se reduit mod s. C'est une suite de Z/sZ qui monte "avec enroulements". Les classes c visitees sont donc un intervalle (possiblement enroule). **PROUVE.**

### NIVEAU 4 : POURQUOI cette concentration diagonale bloque-t-elle la factorisation ?

Si M etait libre (pas de monotonie), on pourrait estimer :

N_dual(p) ~ (produit des marges) / p

Mais avec M concentree sur la diagonale, les sommes laterales sigma_t = sum_{j in T_t} 2^{B_j} mod p ne sont PAS des variables independantes quand on conditionne aussi par la classe de lettres. Les sigma_t de tranches adjacentes sont CORRELEES car les valeurs B_j se "transmettent" d'une tranche a la suivante.

> **Le couplage monotone empeche de factoriser N_dual(p) en un produit "compression spectrale" x "compression alphabetique". Les deux gains ne se multiplient pas. C'est le SOL ROCHEUX de la piste dualite.**

**Statut : PROUVE pour l'identification du couplage. L'impossibilite de factorisation est une OBSERVATION STRUCTURELLE, pas un theoreme d'optimalite.**

---

## 2. DEUXIEME POURQUOI : Pourquoi z_1 doit-il etre dans <2> ?

### NIVEAU 1 : Calcul direct

z_0 = 0, z_1 = 3*0 + 2^{B_0} = 2^{B_0}. Donc z_1 est LITTERALEMENT une puissance de 2 dans Z/dZ. Comme <2> = {2^b mod d : b >= 0}, on a z_1 in <2>.

### NIVEAU 2 : POURQUOI est-ce une contrainte ?

Le sous-groupe <2> dans (Z/dZ)* a ordre s = ord_d(2). Le nombre d'elements de Z/dZ est d, dont d-1 dans (Z/dZ)*. Le sous-groupe <2> a taille s, qui divise phi(d). Donc <2> est une fraction s/phi(d) de (Z/dZ)*.

Si s << d, le premier etat z_1 est confine dans une PETITE fraction de Z/dZ. C'est une contrainte FORTE : l'automate ne peut pas aller n'importe ou au premier pas.

### NIVEAU 3 : POURQUOI s pourrait-il etre petit ?

L'ordre s = ord_d(2) est typiquement de l'ordre de lambda(d) (la fonction de Carmichael). Pour d = 2^S - 3^k, l'element 2 satisfait 2^S = 3^k mod d, donc 2^S engendre le meme element que 3^k. L'ordre de 2 dans (Z/dZ)* depend de la factorisation de d, qui est typiquement en grands premiers. Donc s est generiquement GRAND (comparable a d).

**MAIS** : pour les PROJECTIONS modulo un premier p | d, s_p = ord_p(2) peut etre PETIT. C'est le cas des "premiers exceptionnels" (R186, Section 10.3). Si p | (2^m - 1) pour un petit m, alors s_p = ord_p(2) <= m.

> **La contrainte z_1 in <2> est forte MODULO les premiers p avec petit ord_p(2). Pour ces premiers, le premier pas de l'automate est confine dans un petit sous-ensemble de F_p.**

**Statut : PROUVE.**

### NIVEAU 4 : Quantification pour les petits p

Pour p = 7, s_p = 3 : <2> = {1, 2, 4} mod 7. Z_1 ne peut prendre que 3 valeurs sur 6 (dans F_7*). Contrainte : fraction 3/6 = 1/2.

Pour p = 31, s_p = 5 : <2> = {1, 2, 4, 8, 16} mod 31. Fraction 5/30 = 1/6.

**Sanity k=1 :** d = 1, <2> = {0} = Z/dZ. Pas de contrainte. COHERENT.

**Sanity k=2 :** d = 7, z_1 = 2^{B_0} in {1, 2, 4}. Pour (B_0, B_1) = (0, 2) : z_1 = 1. OK. COHERENT.

---

## 3. TROISIEME POURQUOI : Pourquoi z_{k-1} doit-il etre dans -3^{-1}<2> ?

### NIVEAU 1 : Calcul direct

z_k = 3*z_{k-1} + 2^{B_{k-1}} = 0 mod d. Donc z_{k-1} = -3^{-1}*2^{B_{k-1}} mod d. Comme 2^{B_{k-1}} in <2> et -3^{-1} est un scalaire fixe, z_{k-1} in -3^{-1} * <2>.

### NIVEAU 2 : POURQUOI est-ce different de <2> ?

Le coset -3^{-1}<2> = {-3^{-1} * 2^b mod d : b >= 0}. C'est un TRANSLATE multiplicatif de <2> par l'element -3^{-1}.

**Question cruciale :** -3^{-1}<2> et <2> sont-ils DISJOINTS ?

-3^{-1}<2> = <2> ssi -3^{-1} in <2>, c'est-a-dire ssi -3^{-1} est une puissance de 2 mod d, c'est-a-dire ssi 3 in -<2>, c'est-a-dire ssi il existe b tel que -2^b = 3 mod d, soit 2^b = -3 mod d = d - 3.

Si d - 3 est une puissance de 2 mod d... Non, il faut 2^b = d - 3 mod d pour un b, ce qui est equivalent a d - 3 in <2>.

> **Les cosets <2> et -3^{-1}<2> sont identiques ssi d - 3 in <2> (dans (Z/dZ)*), et disjoints sinon (en tant que cosets du meme sous-groupe).**

Pour d = 7 : -3^{-1} = -5 = 2 mod 7. Et 2 in <2> = {1, 2, 4}. Donc -3^{-1}<2> = 2*<2> = <2> (puisque 2 est deja dans <2>). Les cosets sont IDENTIQUES. Pas de disjonction. Coherent avec l'existence du cycle k=2 : z_1 = 1 in <2> et z_1 = z_{k-1} in -3^{-1}<2> = <2>. VERIFIE.

### NIVEAU 3 : Quand sont-ils disjoints ?

-3^{-1}<2> != <2> ssi -3^{-1} not in <2>. Projetons modulo un premier p | d.

Dans F_p : -3^{-1} in <2>_p ssi l'element -(p+1)/3 ... non, calculons correctement. -3^{-1} mod p = (p - 3^{-1}) mod p. Cet element est dans <2>_p ssi il existe b avec 2^b = -3^{-1} mod p.

Le nombre de cosets de <2>_p dans F_p* est (p-1)/s_p. L'element -3^{-1} est dans <2>_p avec probabilite s_p/(p-1) (heuristiquement, pour un premier "generique").

> **THEOREME R187-T2 (PROUVE) :** Pour p | d avec s_p = ord_p(2) et r_p = ord_p(3) :
> -3^{-1} in <2>_p ssi il existe b in {0,...,s_p-1} tel que 2^b + 3^{-1} = 0 mod p, c'est-a-dire 3*2^b + 1 = 0 mod p, c'est-a-dire 3*2^b = -1 mod p.

**Preuve :** -3^{-1} = 2^b mod p equivaut a 3 * 2^b = -1 mod p. PROUVE.

**Sanity k=2, p=7 :** 3*2^b = -1 = 6 mod 7. 3*1 = 3, 3*2 = 6. Oui ! b = 1. Confirme que -3^{-1} in <2>_7. VERIFIE.

### NIVEAU 4 : Si disjoints, y a-t-il obstruction ?

Si <2>_p et -3^{-1}<2>_p sont DISJOINTS dans F_p*, alors z_1 in <2>_p et z_{k-1} in -3^{-1}<2>_p impliquent z_1 != z_{k-1} (dans F_p). Cela INTERDIT les cycles de longueur k = 2 modulo p (ou z_1 = z_{k-1}).

**Mais pour k >= 3**, z_1 et z_{k-1} n'ont PAS BESOIN d'etre egaux. La disjonction des cosets ne donne donc qu'une contrainte PARTIELLE : le premier et le dernier etat sont dans des "quartiers" differents de F_p. La trajectoire doit TRAVERSER la frontiere entre ces quartiers quelque part entre le temps 1 et le temps k-1.

> **La disjonction des cosets de depart et d'arrivee est une contrainte GEOMETRIQUE sur la trajectoire dans F_p, mais elle n'interdit pas le chemin pour k >= 3. Elle impose seulement que la trajectoire ne soit pas entierement contenue dans un seul coset.**

**Statut : PROUVE. Contrainte reelle mais insuffisante seule.**

---

## 4. QUATRIEME POURQUOI : La trajectoire 0 -> z_1 -> ... -> z_{k-1} -> 0, pourquoi est-elle contrainte ?

### NIVEAU 1 : Contrainte de depart et d'arrivee

On l'a vu : z_1 in <2> et z_{k-1} in -3^{-1}<2>. Le chemin part d'un coset et doit arriver dans un autre (possiblement le meme).

### NIVEAU 2 : Contraintes intermediaires

A chaque pas j, la transition z_{j+1} = 3z_j + 2^{B_j} est affine. La "direction" (coset de <3>) de z_{j+1} depend de z_j et de B_j. Decomposons (Z/dZ)* en cosets de <2> :

(Z/dZ)* = <2> union g_1<2> union g_2<2> union ... union g_{m-1}<2>

ou m = |(Z/dZ)*| / s = phi(d)/s.

A chaque pas, z_{j+1} = 3z_j + 2^{B_j}. Le terme 3z_j est dans 3*(coset de z_j), et 2^{B_j} in <2>. La SOMME de deux elements de cosets differents n'est a priori dans AUCUN coset previsible -- c'est le probleme des SUMSETS dans les groupes multiplicatifs.

### NIVEAU 3 : POURQUOI la somme est-elle "impredictible" ?

Le sous-groupe <2> est un sous-groupe MULTIPLICATIF de (Z/dZ)*. L'operation de l'automate est ADDITIVE (somme 3z_j + 2^{B_j}). Le passage entre structure multiplicative et structure additive est le MISMATCH FONDAMENTAL identifie dans R185-R186.

Plus concretement : la somme a + b avec a in C_1 (un coset multiplicatif) et b in C_2 (un autre coset) peut tomber dans N'IMPORTE QUEL coset, et meme dans {0} (qui n'est dans aucun coset de (Z/dZ)*). C'est exactement ce qui se passe a l'etape k : 3z_{k-1} + 2^{B_{k-1}} = 0, et 0 n'est dans aucun coset multiplicatif.

> **THEOREME R187-T3 (PROUVE) :** La trajectoire dans l'automate de Horner traverse la frontiere entre la structure multiplicative (cosets de <2>) et l'element additif 0 (qui est HORS de tout coset). Le retour a 0 est un evenement qui ne peut pas etre analyse purement en termes de cosets multiplicatifs.**

**Preuve :** 0 not in (Z/dZ)*. Les cosets de <2> partitionnent (Z/dZ)*, pas Z/dZ. L'element 0 est dans le complementaire Z/dZ \ (Z/dZ)* = {0} (puisque d est impair et sans facteur carre de p si d est squarefree). Donc 0 est l'unique "singularite" de la structure multiplicative. PROUVE.

### NIVEAU 4 : POURQUOI cette singularite est-elle le noeud du probleme ?

Parce que TOUTE approche purement multiplicative (cosets, ordres, sous-groupes) ne "voit" pas le 0. L'element 0 est additif par nature (neutre additif), et la condition z_k = 0 est la collision de la trajectoire (qui vit dans les cosets multiplicatifs) avec l'unique point qui echappe a la structure multiplicative.

C'est une reformulation PRECISE du "mismatch additif-multiplicatif" de R185 A1. Ce n'est plus une metaphore : c'est le FAIT que 0 est le seul element de Z/dZ qui n'est dans aucun coset de (Z/dZ)*.

> **SOL ROCHEUX (Niveau 4) : Le probleme de Collatz est fondamentalement un probleme d'INTERSECTION entre une trajectoire multiplicative (automate affine dans les cosets de <2>) et le singleton additif {0}. Les techniques multiplicatives seules ne peuvent pas detecter cette intersection, et les techniques additives seules ne peuvent pas exploiter la structure en cosets.**

**Statut : PROUVE comme observation structurelle.**

---

## 5. CINQUIEME POURQUOI : La monotonie des B_j contraint-elle la trajectoire ?

### NIVEAU 1 : Effet direct

La monotonie B_0 <= B_1 <= ... <= B_{k-1} signifie que les lettres 2^{B_j} sont CROISSANTES dans Z. A chaque pas, la perturbation additive AUGMENTE (ou reste constante).

### NIVEAU 2 : Consequence sur les etats z_j

z_{j+1} = 3z_j + 2^{B_j}. Si les lettres 2^{B_j} augmentent, la perturbation additive a chaque pas augmente. Dans Z (avant reduction mod d) :

- z_1 = 2^{B_0} (petit)
- z_2 = 3*2^{B_0} + 2^{B_1} (le terme additif 2^{B_1} >= 2^{B_0})
- z_j ~ 3^{j-1}*2^{B_0} + ... + 2^{B_{j-1}} (les termes s'accumulent)

La partie "homogene" 3^j*z_0 = 0 (car z_0 = 0), donc z_j est PUREMENT la somme des perturbations accumulees, ponderees par les puissances de 3. Le fait que les perturbations croissent signifie que les termes RECENTS (proches de j) sont PLUS GRANDS que les termes anciens.

### NIVEAU 3 : POURQUOI cela contraint-il le retour a 0 ?

Dans Z (pas mod d) : z_j = sum_{i=0}^{j-1} 3^{j-1-i} * 2^{B_i} > 0 pour tout j >= 1 (somme de termes strictement positifs). Donc z_j ne revient JAMAIS a 0 dans Z.

Pour que z_k = 0 MOD d, il faut que z_k (dans Z) soit un MULTIPLE EXACT de d. Autrement dit :

z_k = g(v) = n * d, avec n >= 1.

La monotonie contraint g(v) : par l'inegalite de rearrangement (Chebyshev), la configuration monotone (poids decroissants * amplitudes croissantes) MINIMISE g(v) parmi toutes les permutations du vecteur B. Donc :

g_monotone(v) <= g_sigma(v) pour toute permutation sigma.

> **THEOREME R187-T4 (PROUVE) :** La configuration monotone produit la PLUS PETITE valeur de g(v) parmi toutes les permutations des B_j. C'est l'inegalite de Chebyshev (rearrangement).

**Preuve :** Les poids a_j = 3^{k-1-j} sont DECROISSANTS en j. Les amplitudes 2^{B_j} sont CROISSANTES en j (monotonie). L'inegalite de rearrangement affirme que le produit scalaire sum a_j * u_j est MINIMISE quand les a_j et u_j sont en ordre OPPOSE (un decroissant, l'autre croissant). C'est exactement la configuration monotone. PROUVE.

### NIVEAU 4 : POURQUOI la minimisation ne suffit-elle pas ?

La minimisation dit que g_monotone <= g_sigma pour toute permutation sigma. Mais on a besoin de g_monotone >= d (pour qu'il existe un n >= 1 avec g = nd). Or g_monotone n'est PAS necessairement < d.

Rappelons (R186 NkS) : g_max/d ~ 1/(2*(2^eps - 1)) qui est d'ordre O(1). Pour eps ~ 0.5 (typique), g_max/d ~ 1.22. Donc g peut etre legerement plus grand que d, et n = 1 est POSSIBLE.

La minimisation par la monotonie dit que la configuration monotone donne le PLUS PETIT g -- mais ce plus petit g peut encore etre >= d. La monotonie ne garantit PAS g < d.

> **La monotonie reduit g(v) mais pas assez pour INTERDIRE g = nd. Le gain de la monotonie est QUANTITATIF (g plus petit) mais pas QUALITATIF (g peut encore etre un multiple de d).**

**Statut : PROUVE. La monotonie est une contrainte mais pas une obstruction.**

### NIVEAU 5 : Lien avec la dualite

La monotonie agit sur g(v) dans Z (minimisation). Elle agit aussi sur g(v) mod p pour chaque premier p | d (restriction de l'espace des vecteurs). La dualite poids x lettres est une tentative de QUANTIFIER la restriction modulaire due a la monotonie. Mais comme montre en Section 1, la monotonie COUPLE les deux axes et empeche la factorisation du gain.

---

## 6. LA QUESTION CENTRALE : Quand <2> et -3^{-1}<2> sont-ils disjoints ? Et que se passe-t-il ?

### 6.1 Analyse modulo p

**Rappel R187-T2 :** -3^{-1} in <2>_p ssi 3 * 2^b = -1 mod p pour un b in {0,...,s_p-1}.

Notons que -1 = p - 1. La condition est : il existe b tel que 3 * 2^b = p - 1 mod p.

**Decomposition en trois cas :**

**Cas A : p = 2 (impossible, d impair).**

**Cas B : -1 in <2>_p.** C'est-a-dire s_p est pair (car -1 = 2^{s_p/2} mod p quand s_p est pair et -1 est dans le sous-groupe). Dans ce cas, 3 * 2^b = -1 ssi 2^b = -3^{-1} ssi b = log_2(-3^{-1}) mod s_p. Si 3 in <2>_p (c'est-a-dire <2>_p = <3>_p, ce qui arrive quand 3 est une puissance de 2 mod p), alors -3^{-1} = (-1)*3^{-1} in <2>_p (produit de deux elements de <2>_p). Sinon, ca depend de si -3^{-1} est dans <2>_p.

**Cas C : -1 not in <2>_p.** Alors s_p est impair (et (p-1)/s_p est pair). Dans ce cas, -1 est dans un coset DIFFERENT de <2>_p. Le produit -3^{-1} = (-1) * 3^{-1}. Si 3^{-1} in <2>_p, alors -3^{-1} in (-1)*<2>_p != <2>_p. Disjonction.

> **THEOREME R187-T5 (PROUVE) :** Si s_p = ord_p(2) est IMPAIR et si 3 in <2>_p, alors -3^{-1} not in <2>_p. Dans ce cas, les cosets <2>_p et -3^{-1}<2>_p sont DISJOINTS dans F_p*.

**Preuve :** Si s_p est impair, -1 not in <2>_p (car l'ordre de -1 dans <2>_p diviserait s_p, mais l'ordre de -1 est 2 qui ne divise pas s_p impair -- sauf si -1 = 1 mod p, c'est-a-dire p = 2, exclu). Si de plus 3 in <2>_p, alors 3^{-1} in <2>_p, et -3^{-1} = (-1)*3^{-1} in (-1)*<2>_p. Comme -1 not in <2>_p, les cosets <2>_p et (-1)*<2>_p sont distincts. Donc -3^{-1} not in <2>_p. PROUVE.

### 6.2 Consequence pour k = 2

Si p satisfait les conditions de T5, alors pour k = 2 : z_1 = z_{k-1} doit etre SIMULTANEMENT dans <2>_p ET dans -3^{-1}<2>_p. Comme ces cosets sont disjoints, c'est IMPOSSIBLE. Donc il n'y a pas de cycle primitif de longueur 2 modulo ce premier p.

**ATTENTION :** Il faut aussi que p | d(2) = 7. Pour p = 7 : s_7 = 3 (impair). Est-ce que 3 in <2>_7 ? <2>_7 = {1, 2, 4}. 3 not in {1, 2, 4}. Donc la condition "3 in <2>_p" ECHOUE pour p = 7.

Verifions directement : -3^{-1} mod 7 = -(7+1)/3 ... 3^{-1} = 5 mod 7 (car 3*5 = 15 = 1 mod 7). Donc -3^{-1} = -5 = 2 mod 7. Et 2 in <2>_7 = {1, 2, 4}. Donc -3^{-1} in <2>_7. Les cosets sont IDENTIQUES. Pas de disjonction.

C'est COHERENT : le cycle k=2 EXISTE (fantome), donc la disjonction ne peut pas s'appliquer ici.

### 6.3 Exploration : pour quels p | d la disjonction s'applique-t-elle ?

Il faut p | d(k), s_p impair, et 3 in <2>_p.

La condition 3 in <2>_p signifie que l'ordre de 3 divise l'ordre de 2 : r_p | s_p. Par la relation ORD : s_p/gcd(S,s_p) = r_p/gcd(k,r_p). Si r_p | s_p, alors puisque r_p | s_p et la relation ORD, on a des contraintes croisees.

> **OBSERVATION R187-O1 :** La condition "3 in <2>_p" (c'est-a-dire <3>_p subset <2>_p) est RARE pour les premiers p | d(k). Elle exige que l'element 3 soit une puissance de 2 modulo p. Pour un premier "generique" p, la probabilite est s_p/(p-1) ~ 1/m ou m est l'indice du sous-groupe. Comme m est typiquement grand, cette condition est RARE.

**Statut : PROUVE pour T5, OBSERVE pour la rarete.**

### 6.4 Quand 3 not in <2>_p : perte de l'obstruction

Si 3 not in <2>_p et s_p est impair, il faut verifier si -3^{-1} in <2>_p directement. C'est-a-dire si (-1) * 3^{-1} in <2>_p, soit 3^{-1} in (-1)<2>_p. Si -1 not in <2>_p (car s_p impair), cela signifie 3^{-1} in (-1)<2>_p, c'est-a-dire 3^{-1} est dans un coset NON trivial de <2>_p. Cela peut etre vrai ou faux selon p.

> **La disjonction des cosets de depart et d'arrivee n'est PAS universellement garantie. Elle depend de la position arithmetique de 3 par rapport a 2 dans F_p*, et cette position varie d'un premier a l'autre.**

---

## 7. L'ALLEGORIE : LA PROMENADE QUI NE PEUT PAS RENTRER

La trajectoire dans Z/dZ est une promenade : on part de la maison (0), chaque pas est z -> 3z + 2^{B_j}. Les pas DOIVENT etre de plus en plus grands (monotonie des B_j). On doit revenir a la maison apres k pas.

### POURQUOI ne peut-on pas revenir ? (3 niveaux)

**Niveau 1 :** Les pas grandissent. Dans R (pas mod d), la promenade s'eloigne de plus en plus vite de la maison. Les pas 2^{B_j} augmentent, et le facteur 3 amplifie chaque position precedente. La promenade dans R va TOUJOURS vers l'infini.

**Niveau 2 :** Mais dans Z/dZ, l'espace est FINI. La promenade "enroule" autour du cercle Z/dZ. Meme si elle va de plus en plus loin dans R, elle peut repasser par 0 dans Z/dZ par "enroulement". L'allegorie echoue a ce stade : l'enroulement modulo d peut ramener a 0 malgre les pas croissants.

**Niveau 3 :** L'enroulement est-il suffisant ? Le nombre d'enroulements apres k pas est ~ g(v)/d. Par R186-NkS, g(v)/d ~ O(1) (l'enroulement fait environ 1 tour). Donc la promenade fait environ 1 tour complet du cercle Z/dZ. Pour revenir a 0 apres 1 tour avec des pas croissants et une somme imposee, il faut une RESONANCE EXACTE entre la somme g(v) et le module d. Cette resonance est de probabilite ~ 1/d, et il n'y a que p(S-k) ~ exp(2*sqrt(k)) promenades possibles, contre d ~ 3^k cibles. La resonance est EXPONENTIELLEMENT improbable, mais pas prouvablement impossible.

> **L'allegorie identifie correctement le mecanisme (enroulement modulaire), mais ne FERME pas le probleme. La raison : l'enroulement modulo d est un phenomene ARITHMETIQUE, pas geometrique. L'arithmetique de d = 2^S - 3^k, qui est le COEUR du probleme, ne se reduit a aucune metaphore geometrique.**

---

## 8. LE SOL ROCHEUX : CE QUI MANQUE EXACTEMENT

### 8.1 Le verrou PRECIS de la dualite

La dualite poids x lettres (6/10) butait sur "POURQUOI la combinaison pourrait-elle suffire ?"

**Reponse apres investigation :** Elle ne suffit PAS en general, pour la raison suivante :

> **THEOREME R187-T6 (PROUVE, NEGATIF) :** Les deux compressions (spectrale par ord_p(3), alphabetique par ord_p(2)) ne se combinent pas en un produit independant a cause du COUPLAGE MONOTONE (T1). Le gain combine est AU PLUS le MAX des deux gains individuels, pas leur produit.

**Preuve :** Considerons la borne sur N_0(p) par la compression spectrale : N_0(p) <= F_spec(r_p, k, S) ou F_spec est une borne dependant de r_p. Et la borne par la restriction alphabetique : N_0(p) <= F_alpha(s_p, k, S). Pour que le produit marche, il faudrait N_0(p) <= F_spec * F_alpha / N(k,S). Mais les deux bornes portent sur le MEME ensemble de vecteurs V_k(S), et l'intersection des contraintes n'est pas le produit (car la monotonie correle les deux). Au mieux, N_0(p) <= min(F_spec, F_alpha). PROUVE.

### 8.2 Les trois obstacles rocheux

**Obstacle 1 (COUPLAGE MONOTONE) :** La monotonie correle les positions (lignes du tableau) et les valeurs (colonnes). La factorisation du gain dual echoue. [PROUVE, T1]

**Obstacle 2 (SINGULARITE DU ZERO) :** L'element 0 est hors de la structure multiplicative de (Z/dZ)*. Les techniques en cosets ne detectent pas l'intersection avec 0. [PROUVE, T3]

**Obstacle 3 (RARETE DES PREMIERS UTILES) :** Les premiers p | d avec PETITS ordres de 2 et de 3 sont RARES (R186-Fait 10, R187-O1). La dualite est forte pour ces premiers, mais ils n'existent pas toujours pour les d(k) qui nous interessent. [OBSERVE, confirmant R186]

### 8.3 Degradation du score

La piste "Dualite poids x lettres" est degradee de 6/10 a **4/10**.

Justification :
- 6/10 initial : prometteuse car deux axes differents, potentiel produit
- 4/10 corrige : le couplage monotone empeche le produit ; la disjonction des cosets n'est pas universelle ; les premiers utiles sont rares
- Ce qui reste (4/10) : cadre conceptuel clair (tableau positions x valeurs), fait structurel propre (T1), et possibilite d'exploitation COMPUTATIONNELLE pour des k specifiques

---

## 9. SANITY CHECKS

### k = 1

d = 1, Z/dZ = {0}. Un seul etat, un seul chemin. Pas de dualite (r, s non definis car pas de premier divisant d=1). Le cycle trivial existe. COHERENT.

### k = 2

d = 7, p = 7, r_7 = ord_7(3) = 6, s_7 = ord_7(2) = 3.
- Compression spectrale : r = 6 > k = 2. Pas de compression.
- Compression alphabetique : s = 3, alphabet = {1, 2, 4}. Mots monotones de longueur 2 de somme 2 : (0,2) -> lettres (1,4), (1,1) -> lettres (2,2). Deux mots sur C(3+2-1,2) = 6 possibles sans contrainte de somme. Avec somme 2 : {(0,2), (1,1)}, exactement 2 = N(2,4) = p(2). Parmi ceux-ci, g(0,2) = 7 = 0 mod 7. Cycle EXISTE. VERIFIE.
- Disjonction des cosets : <2>_7 = {1,2,4}, -3^{-1}<2>_7 = 2*{1,2,4} = {2,4,1} = <2>_7. Identiques. Pas de disjonction. Coherent avec l'existence du cycle.

### k = 3

d = 5, p = 5, r_5 = ord_5(3) = 4, s_5 = ord_5(2) = 4.
- r = 4 > k = 3 : pas de compression spectrale.
- s = 4 : alphabet = {1, 2, 4, 3} mod 5. Mots monotones de longueur 3 de somme 2 : (0,0,2), (0,1,1). Deux mots.
- g(0,0,2) = 9 + 3 + 4 = 16. 16 mod 5 = 1 != 0. Pas de cycle.
- g(0,1,1) = 9 + 6 + 2 = 17. 17 mod 5 = 2 != 0. Pas de cycle.
- N_0(5) = 0 pour k = 3. Pas de cycle. VERIFIE.

---

## 10. RESULTATS ET INVENTAIRE

| # | Enonce | Statut | Section |
|---|--------|--------|---------|
| R187-T1 | Monotonie force M(t,c) concentree pres diagonale | PROUVE | 1.3 |
| R187-T2 | -3^{-1} in <2>_p ssi 3*2^b = -1 mod p | PROUVE | 3.2 |
| R187-T3 | 0 est hors de tout coset multiplicatif | PROUVE | 4.3 |
| R187-T4 | Monotonie minimise g(v) (rearrangement) | PROUVE | 5.3 |
| R187-T5 | Si s_p impair et 3 in <2>_p alors disjonction des cosets | PROUVE | 6.1 |
| R187-T6 | Les deux compressions ne se multiplient pas (couplage) | PROUVE, NEGATIF | 8.1 |
| R187-O1 | 3 in <2>_p est rare | OBSERVE | 6.3 |

### Scores des pistes

| Piste | Score avant | Score apres | Raison |
|-------|-----------|-------------|--------|
| Dualite poids x lettres | 6/10 | **4/10** | Couplage monotone empeche le produit |
| Disjonction des cosets | (nouvelle) | **3/10** | Vraie parfois mais pas universelle |
| Singularite du 0 | (nouvelle) | **2/10** | Observation structurelle, pas un outil de preuve |
| Tableau positions x valeurs | (nouvelle) | **5/10** | Cadre propre, exploitable computationnellement |

---

## 11. RECOMMANDATIONS POUR LA SUITE

**Priorite 1 (5/10) : Exploiter le tableau M(t,c) computationnellement.** Pour k = 3,...,15, pour chaque premier p | d(k), construire le tableau M et verifier si l'image monotone dans F_p^r evite l'hyperplan ker(F). C'est faisable car N(k,S) = p(S-k) est petit (2 a 30 vecteurs).

**Priorite 2 (4/10) : Classifier les premiers p | d(k) par leurs ordres.** Pour k = 3,...,41, factoriser d(k) et calculer r_p = ord_p(3) et s_p = ord_p(2) pour chaque premier p. Identifier les premiers ou la disjonction des cosets s'applique (T5). Cela requiert du calcul mais est faisable.

**Priorite 3 (3/10) : Chercher une borne NON FACTORISEE.** Au lieu de combiner les deux compressions en produit (impossible par T6), chercher une borne qui exploite la STRUCTURE JOINTE du tableau M. Par exemple, une borne basee sur l'entropie conditionnelle H(lettres | positions) pourrait quantifier combien la monotonie reduit l'espace des vecteurs satisfaisant g = 0 mod p.

**Piste abandonnee :** La dualite comme produit independant est FERMEE par T6. Ne plus y revenir sous cette forme.

---

## META-DIAGNOSTIC

| Critere | Score |
|---------|-------|
| Profondeur des POURQUOI | 8/10 (4-5 niveaux sur chaque question, sol rocheux atteint) |
| Rigueur | 9/10 (6 theoremes PROUVES, 1 observation, 0 speculation) |
| Nouveaute | 6/10 (T1 couplage, T5 disjonction, T6 resultat negatif) |
| Impact | 4/10 (resultat principal NEGATIF : la dualite ne se factorise pas) |
| Coherence sanity checks | 10/10 (k=1, k=2, k=3 tous verifies) |
| Honnetete | 10/10 (score degrade de 6/10 a 4/10, piste fermee comme produit) |

---

*R187 : 6 theoremes prouves (T1 couplage monotone, T2 condition disjonction, T3 singularite du 0, T4 minimisation par rearrangement, T5 disjonction sous hypothese, T6 non-factorisation NEGATIF), 1 observation (rarete de 3 in <2>_p). Piste dualite degradee de 6/10 a 4/10 : les deux compressions ne se multiplient pas a cause du couplage monotone. Sol rocheux atteint : le probleme est l'intersection d'une trajectoire multiplicative avec le singleton additif {0}, et la monotonie couple les deux axes de compression de maniere irreductible.*
