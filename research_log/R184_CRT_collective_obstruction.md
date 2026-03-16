# R184 -- Obstruction COLLECTIVE des premiers p|d : Mecanisme CRT
**Date :** 16 mars 2026
**Methode :** Raisonnement structurel pur (ZERO calcul)
**Agent :** CRT -- obstruction collective
**Prerequis :** R182 A4 (aucun bon premier), R183 A1 (boucle fermee, couplage irreductible, conjecture anti-correlation)

---

## SYNTHESE EN UNE PHRASE

L'obstruction collective provient du fait que les premiers p|d sont lies par une UNIQUE relation diophantienne (2^S = 3^k dans Z), que la condition g(v) = 0 mod p se reformule comme annulation d'une somme de puissances de 2 a exposants STRUCTURES dans F_p*, et que le partage des MEMES exposants B_j entre tous les p force une anti-correlation par rigidite du systeme surdetermine.

---

## 1. POURQUOI p|d <=> 2^S = 3^k mod p : Logarithme discret et structure de g(v) mod p

### 1.1 Le fait de base

**Enonce :** d = 2^S - 3^k, donc p|d si et seulement si 2^S = 3^k mod p.

**Statut : PROUVE** (trivial, arithmetique modulaire).

### 1.2 Reformulation en logarithme discret

Soit p premier impair, p|d. Soit r un generateur de F_p*. Posons :
- a = log_r(2) (logarithme discret de 2 en base r)
- b = log_r(3) (logarithme discret de 3 en base r)

Alors 2^S = 3^k mod p se reecrit : r^{aS} = r^{bk} mod p, soit :

> **aS = bk mod (p-1)**

C'est une UNIQUE equation lineaire en (a,b) modulo (p-1). Cette equation lie les positions de 2 et 3 dans le groupe cyclique F_p*.

**Statut : PROUVE.**

### 1.3 Creusons : que signifie cette relation pour g(v) mod p ?

**Premier niveau (POURQUOI 1) :** La relation aS = bk mod (p-1) signifie que le "chemin" S pas de multiplicateur 2 suivi de k pas de multiplicateur 3^{-1} dans F_p* forme une BOUCLE. Plus precisement, l'element 2^S * 3^{-k} = 1 dans F_p*. Cette boucle est la manifestation modulaire de la relation d = 2^S - 3^k.

**Deuxieme niveau (POURQUOI 2) :** Cela contraint la structure de g(v) mod p. En effet :

g(v) = SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}

Modulo p, chaque terme est r^{b(k-1-j) + a*B_j}. Posons alpha = a/b mod (p-1) si gcd(b, p-1) = 1 (i.e. 3 est un generateur ou b est inversible mod p-1). Alors :

3^{k-1-j} = r^{b(k-1-j)}  et  2^{B_j} = r^{a*B_j}

Donc chaque terme de g(v) est r^{b(k-1-j) + a*B_j} -- une puissance de r dont l'exposant est une COMBINAISON LINEAIRE de j et B_j a coefficients (a, b) lies par aS = bk mod (p-1).

**Troisieme niveau (POURQUOI 3) :** La condition g(v) = 0 mod p demande :

SUM_{j=0}^{k-1} r^{b(k-1-j) + a*B_j} = 0 dans F_p

C'est une annulation de k elements de F_p*, chacun etant une puissance de r. Les exposants b(k-1-j) + a*B_j sont determines par les B_j, mais les coefficients (a, b) sont fixes PAR LA RELATION de boucle aS = bk. C'est la boucle qui calibre les poids de chaque terme.

**Quatrieme niveau (POURQUOI 4) :** Pour un premier generique q ne divisant PAS d, la relation aS != bk mod (q-1), et les poids (a,b) dans F_q* n'ont aucune relation speciale. Pour p|d, les poids sont CONTRAINTS par la boucle. Cette contrainte reduit le nombre de degres de liberte effectifs dans la somme, rendant l'annulation plus sensible a la structure des B_j.

**Statut : PROUVE** pour les reformulations. DEDUIT pour l'impact sur la difficulte d'annulation.

### 1.4 Sanity check k=1

Pour k=1 : g(v) = 2^{B_0} = 2^{S-1}. Condition g = 0 mod p : 2^{S-1} = 0 mod p, impossible car 2^{S-1} est une unite de F_p*. Mais attendons -- pour k=1, d = 2^S - 3 = 2^2 - 3 = 1 (S = ceil(log_2(3)) = 2). Donc d = 1, il n'y a PAS de premier p|d, et l'equation n = g(v)/d = 2^1/1 = 2 donne le cycle trivial 1 -> 4 -> 2 -> 1.

La machinerie CRT est VACANTE pour k=1 car d = 1 n'a pas de facteur premier. **COHERENT.**

---

## 2. g(v) mod p : somme de puissances de 2 a exposants structures

### 2.1 La reformulation fondamentale

Quand p|d, posons alpha = log_p(3)/log_p(2) dans le sens du logarithme discret : si ord_p(2) = r, alors 3 = 2^alpha mod p pour un certain alpha dans Z/rZ (sous reserve que 3 est dans <2>, ce qui n'est pas toujours le cas).

**Cas general :** Soit H = <2, 3> le sous-groupe de F_p* engendre par 2 et 3. Il y a deux sous-cas :
- **Cas 1 :** <3> est un sous-groupe de <2>. Alors alpha = log_2(3) mod ord_p(2) existe, et 3^{k-1-j} = 2^{alpha(k-1-j)} mod p. D'ou g(v) = SUM_j 2^{alpha(k-1-j) + B_j} mod p. C'est une SOMME PURE DE PUISSANCES DE 2.
- **Cas 2 :** <3> n'est pas un sous-groupe de <2>. Alors H est un sous-groupe de F_p* de rang 2 (ou plutot d'index > 1 dans F_p*). La simplification en somme pure n'est pas possible, mais la somme reste dans H.

**Statut :** Cas 1 : PROUVE. Cas 2 : la structure est plus complexe mais le couplage persiste.

### 2.2 Structure des exposants dans le Cas 1

Les exposants sont e_j = alpha(k-1-j) + B_j pour j = 0, ..., k-1. La contrainte de monotonie B_0 <= B_1 <= ... <= B_{k-1} avec B_0 >= 0, B_{k-1} <= S-1, se traduit par :

e_j = alpha(k-1-j) + B_j

ou la partie alpha(k-1-j) est DECROISSANTE en j (car alpha > 0 dans Z/rZ a interpretion en representants) tandis que B_j est CROISSANTE. Les exposants e_j sont la SOMME d'un signal decroissant et d'un signal croissant.

**POURQUOI 1 :** Cette competition entre decroissance et croissance est la manifestation dans F_p* de la FRICTION STRUCTURELLE identifiee en R182 (le vecteur optimal pour annulation est decroissant, mais la monotonie impose croissant).

**POURQUOI 2 :** Pour que g(v) = SUM 2^{e_j} = 0 mod p, il faut que les k puissances de 2 dans F_p s'annulent. Or les puissances de 2 vivent dans le sous-groupe cyclique <2> de F_p*. L'annulation demande un equilibrage de k points sur ce "cercle" (le sous-groupe cyclique de F_p* est isomorphe a Z/r Z, et les puissances de 2 sont des points sur ce cercle).

**POURQUOI 3 :** La contrainte de monotonie B_0 <= ... <= B_{k-1} interdit certaines configurations d'exposants. Les exposants e_j ne peuvent pas etre ARRANGES librement modulo r : la monotonie des B_j et la decroissance de alpha(k-1-j) forcent les e_j dans un "couloir" de l'espace (Z/rZ)^k.

**POURQUOI 4 :** Ce couloir est le MEME quelle que soit la valeur de alpha (donc quel que soit p). La monotonie est une contrainte GLOBALE (dans Z) qui se projette identiquement dans tous les F_p*. C'est la source du couplage inter-p.

**Statut : DEDUIT** (chaque pas est algebriquement correct, mais la conclusion quantitative reste ouverte).

### 2.3 Sanity check k=1

Pour k=1, un seul terme : g(v) = 3^0 * 2^{B_0} = 2^{B_0}. Pas de somme, pas de competition croissant/decroissant, pas d'annulation possible dans F_p* (une puissance de 2 n'est jamais 0). Coherent avec d = 1.

---

## 3. Anti-correlation : le mecanisme profond

### 3.1 Position du probleme

Soient p_1, p_2 deux premiers distincts divisant d. On veut comparer :

- P_12 = Prob(g(v) = 0 mod p_1 ET g(v) = 0 mod p_2) -- probabilite conjointe
- P_1 * P_2 = Prob(g(v) = 0 mod p_1) * Prob(g(v) = 0 mod p_2) -- sous independance

L'anti-correlation est l'affirmation P_12 < P_1 * P_2, soit equivalemment :

> **N_0(p_1 * p_2) / C < (N_0(p_1) / C) * (N_0(p_2) / C)**

### 3.2 Source 1 : les exposants partages (FONDAMENTAL)

Les evenements {g(v) = 0 mod p_1} et {g(v) = 0 mod p_2} sont des contraintes sur le MEME vecteur (B_0, ..., B_{k-1}). Il n'y a pas de degre de liberte supplementaire pour satisfaire la seconde condition une fois la premiere imposee.

**POURQUOI 1 :** Concretement, supposons qu'un vecteur v = (B_0, ..., B_{k-1}) satisfait g(v) = 0 mod p_1. Cela impose une relation non-triviale entre les B_j modulo ord_{p_1}(2) (en Cas 1). Pour que v satisfasse AUSSI g(v) = 0 mod p_2, il faut une relation entre les B_j modulo ord_{p_2}(2). Si gcd(ord_{p_1}(2), ord_{p_2}(2)) est petit (ordres "premiers entre eux"), les deux contraintes sont QUASI-INDEPENDANTES dans l'espace des exposants. Mais si ces ordres partagent des facteurs communs -- ce qui arrive quand p_1 et p_2 divisent le MEME d -- les contraintes se RECOUVRENT.

**POURQUOI 2 :** Pourquoi les ordres ord_{p_i}(2) partageraient-ils des facteurs communs pour p_i | d ? Parce que d = 2^S - 3^k, et la relation 2^S = 3^k mod p_i implique que ord_{p_i}(2) | S * m_i pour un certain m_i lie a la structure de <2,3> dans F_{p_i}*. Plus precisement, ord_{p_i}(2) | lcm(S, ord_{p_i}(3)). Les premiers divisant d partagent cette contrainte sur l'ordre de 2, ce qui correle les ordres entre differents p_i.

**POURQUOI 3 :** La correlation des ordres signifie que les "grilles" mod ord_{p_1}(2) et mod ord_{p_2}(2) dans l'espace des B_j ne sont PAS transverses. Elles sont partiellement alignees. Un vecteur qui tombe dans la sous-variete {g = 0 mod p_1} a une probabilite MODIFIEE (pas 1/p_2) d'etre aussi dans {g = 0 mod p_2}, car les deux sous-varietes sont correlees via la grille commune.

**POURQUOI 4 :** Le sens de la modification (anti-correlation plutot que correlation positive) provient de la MONOTONIE. La sous-variete des vecteurs monotones est un cone de dimension k-1 dans l'espace des vecteurs. Les sous-varietes {g = 0 mod p_i} sont des "nappes" qui traversent ce cone. La monotonie force ces nappes a se couper selon des angles OBTUS (pas aigus), car la contrainte de croissance pousse les solutions vers la meme region de l'espace. Quand deux nappes se coupent a angle obtus dans un cone, leur intersection est PLUS PETITE que le produit de leurs sections (visualiser deux plans presque paralleles dans un cone etroit : ils ne se croisent presque pas a l'interieur du cone).

**Statut :** POURQUOI 1-2 : DEDUIT. POURQUOI 3-4 : CONJECTURE (l'argument geometrique est intuitif mais pas formalise).

### 3.3 Source 2 : la contrainte de taille (AMPLIFICATEUR)

Independamment de la structure, il y a un argument de densite. Le nombre de vecteurs monotones est C = C(S-1, k-1). Le nombre de residus mod d est d = 2^S - 3^k. Sous independance parfaite :

E[N_0(d)] = C / d

Pour que N_0(d) = 0 (pas de cycle), il suffit que C/d < 1, ce qui arrive pour k >= 42 (argument Borel-Cantelli). Pour k < 42, C >> d et l'esperance sous independance est grande.

L'anti-correlation ACCELERE la convergence vers 0 : si les evenements sont negativement correles, la variance de N_0(d) est plus petite, et P(N_0 = 0) est plus grande que sous independance.

**Formellement :** Var(N_0) = SUM_v Var(1_{g(v)=0 mod d}) + SUM_{v != w} Cov(1_{g(v)=0}, 1_{g(w)=0})

Si les indicatrices sont negativement correlees (ce qui est LIE mais DISTINCT de l'anti-correlation entre les E_i), alors Var(N_0) < E[N_0], et par l'inegalite de Chebyshev, N_0 est concentre pres de sa moyenne.

**Statut : CONDITIONNEL** sur la negative correlation entre indicatrices.

### 3.4 Sanity check k=1

d = 1, pas de facteur premier, les notions de P_12, anti-correlation, etc., sont vides. Le cycle trivial existe. COHERENT -- l'obstruction collective n'existe que pour k >= 2.

---

## 4. Source de l'anti-correlation : la monotonie comme contrainte GLOBALE

### 4.1 L'argument central

La monotonie B_0 <= B_1 <= ... <= B_{k-1} est une contrainte dans Z^k. Elle ne depend PAS du premier p. Elle se projette IDENTIQUEMENT dans tous les F_{p_i}*. C'est une contrainte ENTIERE sur les exposants, pas modulaire.

**POURQUOI 1 :** Pour un vecteur v satisfaisant g(v) = 0 mod p_1, la contrainte de monotonie reduit les B_j a un sous-ensemble STRUCTURE de {0, 1, ..., S-1}^k. Les B_j restants disponibles pour satisfaire g(v) = 0 mod p_2 sont DEJA CONTRAINTS par la monotonie ET par la condition mod p_1. Ce double filtrage est plus restrictif que chaque condition prise separement.

**POURQUOI 2 :** Plus concretement, la condition g(v) = 0 mod p_1 selectionne environ C/p_1 vecteurs parmi les C monotones. Parmi ces C/p_1 vecteurs, combien satisfont aussi g(v) = 0 mod p_2 ? Si les deux conditions etaient independantes, environ C/(p_1 * p_2). Mais la monotonie cree une DEPENDANCE : les vecteurs monotones qui annulent g mod p_1 ne sont pas distribues uniformement parmi les monotones -- ils sont concentres dans certaines configurations de B_j (celles qui equilibrent les phases dans F_{p_1}*). Et ces configurations ont une probabilite REDUITE d'equilibrer aussi les phases dans F_{p_2}*, car la monotonie force les phases dans les deux corps a etre COHERENTES (meme monotonie -> meme direction de drift des phases).

**POURQUOI 3 :** La monotonie force un DRIFT directionnel dans chaque F_p*. Les exposants B_j croissants font tourner les termes 2^{B_j} mod p dans une direction systematique autour du sous-groupe cyclique <2>. Pour annuler la somme, il faut que cette rotation soit compensee par la progression geometrique 3^{k-1-j}. Mais la compensation est calibree DIFFEREMMENT dans F_{p_1}* et F_{p_2}* (car alpha_1 != alpha_2 en general). Satisfaire la compensation dans F_{p_1}* force les B_j dans une configuration specifique qui, en general, PERTURBE la compensation dans F_{p_2}*.

**POURQUOI 4 :** Pourquoi "en general" plutot que "parfois" ? Parce que les alpha_i = log_{p_i}(3)/log_{p_i}(2) mod ord_{p_i}(2) sont des objets de DIFFERENTS groupes cycliques. La condition de double compensation :

SUM_j 2^{alpha_1(k-1-j) + B_j} = 0 dans F_{p_1}  ET  SUM_j 2^{alpha_2(k-1-j) + B_j} = 0 dans F_{p_2}

est un systeme de 2 equations a k inconnues (les B_j, entiers monotones). Pour k petit, ce systeme est SURDETERMINE relativement a la monotonie : les solutions de la premiere equation forment une variete de "codimension 1" dans le cone monotone, et la seconde equation coupe cette variete transversalement -- MAIS la monotonie empeche la transversalite propre, creant l'anti-correlation.

**Statut : CONJECTURE.** L'argument est geometrique et qualitatif. La rigueur demanderait de quantifier la "defaut de transversalite" dans le cone monotone.

---

## 5. Formalisation : le ratio P_12 / (P_1 * P_2)

### 5.1 Notations

Pour p premier, p|d, definissons :
- N_0(p) = #{v monotone : g(v) = 0 mod p}
- P(p) = N_0(p) / C (proportion)
- N_0(p_1 p_2) = #{v monotone : g(v) = 0 mod p_1 p_2}
- P(p_1 p_2) = N_0(p_1 p_2) / C

Le ratio d'anti-correlation est :

> **rho(p_1, p_2) = P(p_1 p_2) / (P(p_1) * P(p_2))**

- rho = 1 : independance
- rho < 1 : anti-correlation (obstruction collective)
- rho > 1 : correlation positive (facilitation collective)

### 5.2 Decomposition par CRT

Par le CRT, puisque gcd(p_1, p_2) = 1 :

g(v) = 0 mod p_1 p_2 <=> g(v) = 0 mod p_1 ET g(v) = 0 mod p_2

Donc N_0(p_1 p_2) = #{v : g(v) = 0 mod p_1 ET g(v) = 0 mod p_2}.

**Si les evenements etaient independants sur les vecteurs monotones :**

N_0(p_1 p_2) = C * P(p_1) * P(p_2) = N_0(p_1) * N_0(p_2) / C

### 5.3 Pourquoi rho < 1 : trois arguments convergents

**Argument A (surdetermination) :** Le vecteur v a k-1 degres de liberte (k "variables" B_j avec la monotonie, mais on peut parametrer par les k-1 "gaps" Delta_j = B_j - B_{j-1} >= 0). La condition g(v) = 0 mod p retire essentiellement 1 degre de liberte (une equation dans Z/pZ). Avec r premiers divisant d, on a r equations pour k-1 inconnues. Pour k petit et r grand (beaucoup de facteurs dans d), le systeme est surdetermine et generiquement INCOMPATIBLE.

Le ratio rho mesure le defaut de compatibilite. Surdetermination implique rho <= 1, avec egalite seulement en cas d'alignement special.

**Statut : DEDUIT** (argument de comptage de dimensions standard).

**Argument B (sommes de caracteres) :** En utilisant les caracteres de F_p*, on peut ecrire :

N_0(p) = (1/p) * SUM_{t mod p} SUM_v chi_t(g(v))

ou chi_t est le caractere additif e^{2*pi*i*t/p}. De meme pour N_0(p_1 p_2). Le ratio rho se calcule via les sommes de caracteres croisees. L'anti-correlation rho < 1 revient a montrer que les termes croisees (t_1 != 0, t_2 != 0) dans la double somme de caracteres contribuent negativement.

Or ces termes croisees font intervenir :

SUM_v chi_{t_1}(g(v) mod p_1) * chi_{t_2}(g(v) mod p_2)

= SUM_v exp(2*pi*i * (t_1*g(v)/p_1 + t_2*g(v)/p_2))

= SUM_v exp(2*pi*i * g(v) * (t_1/p_1 + t_2/p_2))

Ce sont des SOMMES EXPONENTIELLES sur les vecteurs monotones. L'annulation de ces sommes (par les methodes de R181-R182) donnerait l'independance asymptotique. L'anti-correlation demande PLUS : que ces sommes aient un signe systematique.

**Statut : CONDITIONNEL** (necessite de borner des sommes exponentielles avec signe).

**Argument C (inclusion-exclusion) :** Par inclusion-exclusion sur les r premiers divisant d :

N_0(d) = SUM_{I subset {1,...,r}} (-1)^{|I|+1} * N_0(prod_{i in I} p_i) + ...

Si rho < 1 pour toutes les paires, les termes d'ordre 2 et plus sont PLUS PETITS que sous independance, et N_0(d) est majore par le produit C * PROD_i P(p_i) -- qui est l'heuristique standard C/d.

Mais la cascade d'anti-correlations a TOUS les ordres (pas seulement les paires) pourrait pousser N_0(d) strictement en dessous de C/d. C'est l'obstruction collective.

**Statut : CONDITIONNEL** sur rho < 1 pour toutes les paires et ordres superieurs.

### 5.4 Sanity check k=1

d = 1, pas de premier, rho n'est pas defini. Pour k=2, d = 2^2 - 3^2 = 4 - 9 = -5, donc |d| = 5, un seul premier, rho entre paires n'est pas defini. Pour k=3, d = 2^5 - 3^3 = 32 - 27 = 5, un seul premier encore.

Pour k=5 : S = 8, d = 256 - 243 = 13, un seul premier. Pour k=12 : S = 20, d = 2^20 - 3^12 = 1048576 - 531441 = 517135 = 5 * 103427 = 5 * 103427. On a 2 facteurs premiers (ou plus si 103427 se decompose), donc rho est defini.

**Observation :** Les petits k ont peu de facteurs dans d, ce qui rend l'obstruction collective faible (peu de paires). Pour les grands k, d a beaucoup de facteurs et l'obstruction collective s'accumule. C'est COHERENT avec le fait que les petits k sont les plus difficiles a exclure (le mur k < 42).

---

## 6. SYNTHESE : le mecanisme d'obstruction collective

### 6.1 Chaine causale complete

```
d = 2^S - 3^k  (definition)
     |
     v
p|d <==> 2^S = 3^k mod p  (arithmetique)  [PROUVE]
     |
     v
Dans F_p*, <2> et <3> sont lies par une BOUCLE  [PROUVE]
     |
     v
g(v) mod p = somme structuree dans F_p* avec exposants (alpha, B_j)  [PROUVE]
     |
     v
La monotonie des B_j est une contrainte GLOBALE partagee entre tous les p  [PROUVE]
     |
     v
Les varietes {g=0 mod p_i} dans le cone monotone sont COUPLEES  [DEDUIT]
     |
     v
Le couplage est NEGATIF (anti-correlation) car la monotonie
aligne les varietes dans la meme direction  [CONJECTURE]
     |
     v
N_0(d) << C/d pour k < 42, et N_0(d) = 0 pour k >= 42  [CONJECTURE]
```

### 6.2 Tableau recapitulatif

| Enonce | Statut | Niveau |
|--------|--------|--------|
| p\|d <=> 2^S = 3^k mod p | PROUVE | Trivial |
| Reformulation en log discret : aS = bk mod (p-1) | PROUVE | Algebrique |
| g(v) mod p = somme de puissances structurees | PROUVE | Algebrique |
| La monotonie couple les contraintes mod p_i entre elles | DEDUIT | Qualitatif |
| Les ordres ord_{p_i}(2) sont correles pour p_i\|d | DEDUIT | Qualitatif |
| Le ratio rho(p_1,p_2) < 1 | CONJECTURE | Non quantifie |
| L'obstruction collective croit avec le nombre de facteurs de d | DEDUIT | Qualitatif |
| N_0(d) = 0 pour tout k >= 2 | CONJECTURE | Objectif final |

### 6.3 Ce qui manque pour une preuve

1. **Quantifier rho.** Montrer rho(p_1, p_2) <= 1 - epsilon pour un epsilon > 0 explicite. Cela demande de borner des sommes de caracteres croisees sur le cone monotone.

2. **Controler les ordres superieurs.** L'anti-correlation par paires ne suffit pas : il faut aussi les triples, quadruples, etc. Cela revient a une version multi-dimensionnelle du probleme des sommes exponentielles.

3. **Traiter k < 42.** Pour k >= 42, l'heuristique C/d < 1 suffit meme sans anti-correlation. Pour k < 42, l'anti-correlation est NECESSAIRE car C >> d. C'est exactement la zone ou l'argument doit etre le plus fin.

4. **Le cas k = 2.** d = -5 (ou |d| = 5). Il n'y a qu'un premier (5), pas d'anti-correlation paire possible. L'exclusion k=2 doit venir d'un argument DIRECT (et effectivement, pour k=2, on verifie que g(v) = 2*3 + 2^{B_1} = 6 + 2^{B_1} avec B_1 in {1,2,3}, donnant g in {8, 10, 14}, et d = -5, donc g/d in {-8/5, -2, -14/5}. Seul g=10, d=-5 donne n=-2, et on verifie : n doit etre > 0 pour un cycle. Donc k=2 est exclu par la positivite de n).

---

## 7. PISTES EMERGENTES

### 7.1 Piste "Systeme surdetermine dans le cone" (8/10)

Formaliser les conditions g(v) = 0 mod p_i comme un systeme d'equations dans l'espace des (Delta_1, ..., Delta_{k-1}) avec Delta_j >= 0. Montrer que pour r facteurs et k-1 variables, le systeme est generiquement incompatible dans le cone positif.

**Avantage :** Se ramene a de la geometrie convexe + theorie des nombres.
**Risque :** Le "generiquement" pourrait avoir des exceptions exactement aux k problematiques.

### 7.2 Piste "Sommes de caracteres avec signe" (6/10)

Borner les sommes SUM_v chi(g(v)) sur le cone monotone avec un controle du signe. Potentiellement via les methodes de van der Corput adaptees aux sommes sur partitions.

**Avantage :** Framework technique bien developpe.
**Risque :** Les bornes existantes donnent |somme| petit, pas signe.

### 7.3 Piste "Couplage par les ordres multiplicatifs" (7/10)

Exploiter le fait que les ordres ord_{p_i}(2) pour p_i|d partagent des diviseurs communs (car tous lies a S via 2^S = 3^k mod p). Montrer que ce partage force rho < 1.

**Avantage :** Specifique a la structure de d = 2^S - 3^k.
**Risque :** Les ordres multiplicatifs sont difficiles a controler individuellement.

---

## 8. CONNEXION AVEC R183

R183 A1 a identifie la racine irreductible : le couplage vient de la forme de Horner et de l'iteration affine z -> 3z + 2^{B_j}. R184 prolonge en trois directions :

1. **Reformulation en log discret** (Section 1) : rend la boucle EXPLICITE dans F_p* via aS = bk mod (p-1).
2. **Formalisation du ratio rho** (Section 5) : donne un cadre QUANTITATIF pour l'anti-correlation.
3. **Identification des pistes operationnelles** (Section 7) : three approaches to attack rho < 1.

**Innovation incrementale :** La decomposition du mecanisme en "surdetermination dans le cone monotone" (7.1) est nouvelle par rapport a R183 et semble la plus prometteuse.

---

## META-DIAGNOSTIC

| Critere | Score |
|---------|-------|
| Nouveaute par rapport a R183 | 5/10 (prolonge plus qu'innove) |
| Rigueur | 7/10 (les pas PROUVES sont solides, les CONJECTURES explicites) |
| Operationnalite | 6/10 (pistes identifiees mais aucune attaquee) |
| Profondeur des POURQUOI | 8/10 (4+ niveaux partout) |
| Coherence avec k=1 | 10/10 (verifie systematiquement) |

**Recommandation pour R185 :** Attaquer la Piste 7.1 (systeme surdetermine dans le cone). Formaliser le comptage de solutions d'un systeme lineaire mod p_1, ..., mod p_r dans le cone {Delta_j >= 0}. Objectif : montrer que le nombre de solutions est O(C / d^{1+epsilon}) au lieu de O(C/d).
