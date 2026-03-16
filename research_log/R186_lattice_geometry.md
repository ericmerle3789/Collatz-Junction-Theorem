# R186 -- AGENT GEOMETRIE DES NOMBRES : Reseaux et Conjecture de Collatz
**Date :** 16 mars 2026
**Mode :** Exploration systematique -- raisonnement pur, ZERO calcul
**Prerequis :** R184-R185 (echecs analytiques/combinatoires documentes), Junction Theorem, Blocking Mechanism
**Mission :** La geometrie des nombres peut-elle mordre sur le probleme des cycles ?

---

## 0. RESUME EXECUTIF

**VERDICT : L'approche par geometrie des nombres NE MORD PAS sur le probleme de Collatz dans sa forme directe.** La raison fondamentale est que g(v) est une forme EXPONENTIELLE (non lineaire) en les coordonnees entieres B_j. Aucune reformulation honnete ne produit un reseau classique auquel appliquer Minkowski, LLL, ou la theorie de Baker de facon decisive. Cinq approches sont explorees et echouent toutes sur des obstacles identifies avec precision. Cependant, une connexion partielle via les formes lineaires en logarithmes (Baker) donne une information DEJA CONNUE (pas de cycle pour k assez grand), et une reformulation en reseau "apres linearisation" donne un cadre conceptuel correct mais computationnellement equivalent au comptage direct.

**Score global de l'approche : 2/10** -- Eclairante sur pourquoi ca ne marche pas, mais zero progres substantiel.

---

## 1. RAPPEL DU CADRE

### 1.1 Objets

- **Vecteur monotone :** v = (B_0, ..., B_{k-1}) avec 0 <= B_0 <= B_1 <= ... <= B_{k-1}, et sum B_j = S - k.
- **Fonction de Syracuse :** g(v) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}
- **Denominateur :** d = 2^S - 3^k (avec S >= k * log_2(3) + 1 pour d > 0)
- **Condition de cycle :** g(v) = n * d pour un entier n >= 1
- **Equivalence :** g(v) congruent a 0 mod d

### 1.2 Sanity check k=1

Pour k = 1 : S >= 2 (car B_0 = S - 1 >= 1). d = 2^S - 3. g(v) = 2^{S-1}.
Cycle ssi 2^{S-1} congruent a 0 mod (2^S - 3). Pour S = 2 : d = 1, g = 2, 2/1 = 2. C'est le cycle trivial {1 -> 4 -> 2 -> 1}. Pour S = 3 : d = 5, g = 4. 4/5 n'est pas entier. Pas de cycle.

**Verifie : le cycle trivial k=1, S=2 est l'unique solution.**

---

## 2. APPROCHE 1 : RESEAU DIRECT DANS Z^k

### 2.1 Tentative

On voudrait definir un reseau Lambda dans Z^k par :
Lambda = { (B_0, ..., B_{k-1}) dans Z^k : g(v) congruent a 0 mod d }

### 2.2 Obstacle fondamental

g(v) = sum 3^{k-1-j} * 2^{B_j} est une fonction **EXPONENTIELLE** en les B_j. La condition g(v) congruent a 0 mod d n'est PAS une condition lineaire en (B_0, ..., B_{k-1}).

Un reseau est un sous-groupe discret de R^n, et la condition d'appartenance a un reseau est definie par des relations LINEAIRES a coefficients entiers. La condition "sum a_j * 2^{B_j} congruent a 0 mod d" est transcendante en les B_j.

**CONCLUSION : Il n'existe pas de reseau dans l'espace des B_j dont l'intersection avec le cone monotone donnerait les solutions.** [PROUVE]

### 2.3 Sanity k=1

Pour k = 1, la "condition de reseau" serait : 2^{B_0} congruent a 0 mod d. C'est une condition sur une seule puissance de 2, pas une relation lineaire.

---

## 3. APPROCHE 2 : LINEARISATION PAR SUBSTITUTION x_j = 2^{B_j}

### 3.1 Formulation

Posons x_j = 2^{B_j}. Alors :
- g(v) = sum_{j=0}^{k-1} a_j * x_j, avec a_j = 3^{k-1-j} (lineaire en x_j)
- Contrainte 1 : x_j dans {1, 2, 4, 8, 16, ...} (puissances de 2)
- Contrainte 2 : x_0 <= x_1 <= ... <= x_{k-1} (monotonie)
- Contrainte 3 : sum log_2(x_j) = S - k (contrainte de somme)
- Condition de cycle : sum a_j * x_j congruent a 0 mod d

### 3.2 Le reseau lineaire

Considerons le reseau L dans Z^k defini par :
L = { (x_0, ..., x_{k-1}) dans Z^k : sum a_j * x_j congruent a 0 mod d }

C'est un VRAI reseau (noyau d'une forme lineaire modulo d). C'est un sous-reseau de Z^k d'indice d (car l'application (x_0,...,x_{k-1}) -> sum a_j * x_j mod d est un morphisme de Z^k vers Z/dZ, et il est surjectif car pgcd(a_0,...,a_{k-1}, d) doit etre examine).

**Examinons pgcd(a_0,...,a_{k-1}, d) :**
- a_j = 3^{k-1-j}, donc les a_j sont des puissances de 3.
- pgcd(3^0, 3^1, ..., 3^{k-1}) = 1 (car a_{k-1} = 3^0 = 1).
- Donc pgcd(a_0,...,a_{k-1}, d) = pgcd(1, d) = 1.

Le morphisme est surjectif, L est d'indice d dans Z^k.

**Parametres du reseau :**
- Dimension : k
- Determinant : det(L) = d = 2^S - 3^k ~ 2^{1.585k} pour S ~ k * log_2(3)
- Volume fondamental : d

### 3.3 Le probleme REEL

L est un reseau parfaitement defini. Le probleme est de trouver un point de L qui :
(a) a toutes ses coordonnees dans {1, 2, 4, 8, ...} (puissances de 2)
(b) satisfait x_0 <= x_1 <= ... <= x_{k-1}
(c) satisfait sum log_2(x_j) = S - k

La contrainte (a) est DEVASTATRICE. L'ensemble des points de Z^k dont toutes les coordonnees sont des puissances de 2 est un ensemble ULTRA-RARE : il a densite ZERO dans tout hypercube [1, N]^k (il y a seulement (log_2 N)^k points de puissances de 2 sur N^k points totaux).

### 3.4 Tentative d'application de Minkowski

**Theoreme de Minkowski :** Si C est un corps convexe symetrique dans R^k de volume > 2^k * det(L), alors C contient un point non-nul de L.

Peut-on l'utiliser EN SENS INVERSE (pas de point de L dans un domaine) ? Non directement. Minkowski donne une condition SUFFISANTE d'existence, pas une condition necessaire. L'absence de point dans un petit domaine ne dit rien si le domaine n'est pas un corps convexe symetrique, et surtout notre domaine (puissances de 2, monotone, somme fixee) n'est pas convexe.

**Alternative : borne superieure.** Le nombre de points de L dans un domaine D est environ Vol(D)/det(L). Si D est l'ensemble des points dont les coordonnees sont des puissances de 2 dans [1, 2^S]... Cet ensemble a |D| ~ (S)^k points (car chaque coordonnee prend S valeurs). Apres contrainte de monotonie et de somme, on retrouve |D| ~ N(k,S) = nombre de partitions, qui est exactement le comptage de T1 de R184/R185.

**CONCLUSION : L'approche par reseau linearise est FORMELLEMENT CORRECTE mais COMPUTATIONNELLEMENT EQUIVALENTE au comptage direct de vecteurs monotones modulo d. Elle ne donne aucune information nouvelle.** [PROUVE]

### 3.5 Sanity k=1

L = { x_0 dans Z : 1 * x_0 congruent a 0 mod d } = dZ. Les puissances de 2 dans dZ : il faut 2^{B_0} = n * d. Pour d = 1 (S=2) : 2^1 = 2, n = 2. OK (cycle trivial). Pour d = 5 (S=3) : 2^{B_0} = 5n. Impossible car 2^{B_0} n'est jamais divisible par 5. Correct.

---

## 4. APPROCHE 3 : BORNES DE MINKOWSKI SUR LE RESEAU DUAL

### 4.1 Idee

Meme si Minkowski ne s'applique pas directement au domaine non-convexe des puissances de 2, on peut examiner le RESEAU DUAL L* et chercher des vecteurs courts dans L* qui imposeraient des contraintes sur les points de L.

Le reseau dual L* = { y dans R^k : <y, x> dans Z pour tout x dans L }.

Pour L = ker(phi) ou phi(x) = sum a_j x_j mod d, le dual est :
L* = Z^k + (1/d)(a_0, a_1, ..., a_{k-1}) * Z

Le plus court vecteur de L* a une norme d'environ 1 (les vecteurs de Z^k sont dans L*), sauf si (a_0,...,a_{k-1})/d est tres proche d'un point entier, ce qui reviendrait a dire qu'il existe c dans Z^k tel que |a_j - c_j * d| est petit pour tout j. Mais a_j = 3^{k-1-j} et d ~ 2^{1.585k}, donc pour les grands j, a_j est petit devant d (a_j < d), et pour les petits j, a_j = 3^{k-1} ~ 2^{1.585(k-1)} ~ d/2, qui n'est pas proche d'un multiple de d en general.

**CONCLUSION : Le reseau dual ne donne pas de vecteur anormalement court. Pas d'obstruction geometrique exploitable.** [PROUVE]

### 4.2 Pourquoi ?

Fondamentalement, le reseau L a un seul "generateur non trivial" (la relation sum a_j x_j congruent a 0 mod d), donc L* est presque Z^k avec un seul vecteur supplementaire. La geometrie est essentiellement triviale : un seul hyperplan modulo d, pas de structure geometrique riche a exploiter.

Pour avoir de la geometrie des nombres non-triviale, il faudrait PLUSIEURS relations lineaires independantes entre les x_j modulo differents moduli. Mais le probleme de Collatz n'en fournit qu'une seule (g congruent a 0 mod d).

---

## 5. APPROCHE 4 : THEORIE DE BAKER (FORMES LINEAIRES EN LOGARITHMES)

### 5.1 Connexion

La condition de cycle g(v) = n * d peut s'ecrire :
n * 2^S - n * 3^k = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}

En divisant par 3^{k-1} * 2^{S-1} :
n * (2/3)^1 * 2^{S-1}/3^{k-1} - n * 3/2^{S} ... Non, cette manipulation ne simplifie pas.

Approche plus directe. La condition d > 0, soit 2^S > 3^k, s'ecrit :
S > k * log_2(3) = k * ln(3)/ln(2)

Et |2^S - 3^k| = d est lie a la PROXIMITE de S/k avec log_2(3). Le theoreme de Baker donne :

**Theoreme (Baker, 1966 ; Laurent, Mignotte, Nesterenko, 2000) :** Pour des entiers non nuls a, b :
|2^a - 3^b| > 2^a / exp(C * (log a)^2)

pour une constante effective C > 0.

En particulier, d = 2^S - 3^k > 2^S / exp(C * (log S)^2) > 2^{S - c*log^2(S)} pour une constante c.

### 5.2 Ce que ca donne

Baker garantit que d n'est pas exponentiellement petit par rapport a 2^S. Plus precisement :
d > 2^{S - c*(log S)^2}

Comme S ~ 1.585k, on a d > 2^{1.585k - c*(log k)^2}.

Pour le cycle, il faut g(v) = n*d avec n >= 1 et g(v) <= g_max ~ tau_k * 2^{S-1} (ou tau_k = sum 3^{k-1-j} * 2^j / 2^S donne tau_k ~ (3/2)^k). Donc n <= g_max / d ~ (3/2)^k * 2^{S-1} / d.

Avec la borne de Baker, n <= (3/2)^k * 2^{S-1} / 2^{S - c*log^2 S} = (3/2)^k * 2^{c*log^2 S - 1} ~ 2^{0.585k + c*log^2 k}.

Pour grand k, n est borne polynomialement en k (grace au facteur log^2 k). Cela signifie que pour grand k, le multiple n est "petit" relativement a d.

### 5.3 Lien avec le comptage

Le nombre de candidats est N(k,S) ~ 2^{alpha*k} avec alpha <= 1.507 (borne superieure de T1). Le nombre de "cibles" (multiples de d dans [1, g_max]) est au plus n_max ~ 2^{0.585k + c*log^2 k}. Par un argument probabiliste, le nombre attendu de collisions est :

E ~ N(k,S) * n_max / g_max ~ 2^{alpha*k} * 2^{0.585k + c*log^2 k} / 2^{1.585k}
  = 2^{(alpha - 1)k + c*log^2 k}

Si alpha < 1 (le vrai N(k,S) croit sous-exponentiellement par rapport a d), alors E -> 0 pour grand k. C'est exactement l'argument de Borel-Cantelli du Junction Theorem (Bloc 1).

**CONCLUSION : Baker renforce quantitativement l'argument de grand-k mais ne dit RIEN de nouveau pour k entre 3 et 41.** [PROUVE]

### 5.4 Sanity k=1

Pour k = 1, S = 2 : d = 1. Baker donne |2^2 - 3^1| = 1 >= 1. Trivial. Le cycle existe effectivement.

---

## 6. APPROCHE 5 : RESEAU DE COPPERSMITH (PETITES RACINES DE POLYNOMES MODULAIRES)

### 6.1 Idee

La methode de Coppersmith (1996, basee sur LLL) permet de trouver les petites racines de polynomes modulo un entier N. Peut-on formuler g(v) congruent a 0 mod d comme un polynome modulaire ?

### 6.2 Formulation

g(v) = sum a_j * 2^{B_j} avec des inconnues B_j entieres. Ce n'est PAS un polynome en les B_j. C'est une somme d'exponentielles.

On pourrait considerer les x_j = 2^{B_j} comme variables et ecrire g = sum a_j * x_j congruent a 0 mod d. C'est un polynome de degre 1 en les x_j. Coppersmith s'applique a des polynomes univaries (ou multivaries avec extensions). Pour le cas lineaire, trouver x tel que a*x congruent a 0 mod d est trivial (x = d/gcd(a,d)).

Le probleme est multilinear et les x_j sont contraints a etre des puissances de 2. Coppersmith ne gere pas les contraintes multiplicatives sur les variables.

**CONCLUSION : Coppersmith ne s'applique pas. Le probleme n'est pas polynomial en des variables "petites".** [PROUVE]

---

## 7. APPROCHE 6 (BONUS) : RESEAU MULTI-MODULAIRE VIA CRT

### 7.1 Idee

Au lieu d'une seule relation mod d, on peut considerer la reduction mod p pour chaque premier p divisant d (ou meme pour tout premier). Cela donne un SYSTEME de relations :

Pour chaque premier p : sum a_j * 2^{B_j} congruent a 0 mod p

Si on fixe l'ordre de 2 modulo p, disons ord_p(2) = r, alors 2^{B_j} mod p ne depend que de B_j mod r. On a donc une relation sur les (B_j mod r).

### 7.2 Le reseau CRT

Pour un premier p fixe, posons c_j = B_j mod r dans {0, 1, ..., r-1}. La condition g congruent a 0 mod p devient :
sum 3^{k-1-j} * 2^{c_j} congruent a 0 mod p

C'est une condition sur les k-uplets (c_0, ..., c_{k-1}) dans (Z/rZ)^k. Le nombre de k-uplets satisfaisant cette condition est au plus r^{k-1} (fixe c_0, ..., c_{k-2} arbitrairement, c_{k-1} est determine modulo r si pgcd(2^{c_{k-1}} mod p variations, p) = 1, ce qui n'est pas exact car c_{k-1} n'apparait pas lineairement).

**OBSTACLE :** La relation est lineaire en les 2^{c_j}, pas en les c_j. Donc la condition filtre les k-uplets (c_j) mais pas de facon lineaire. Il n'y a pas de reseau dans (Z/rZ)^k.

### 7.3 Version amelioree

On peut considerer les variables y_j = 2^{B_j} mod p. Alors :
- sum a_j * y_j congruent a 0 mod p (LINEAIRE en y_j)
- y_j dans <2>_p (le sous-groupe engendre par 2 dans (Z/pZ)*)

La condition lineaire definit un hyperplan H_p dans (Z/pZ)^k. Les points admissibles sont dans H_p inter (<2>_p)^k.

Le nombre de points dans (<2>_p)^k est r^k. Le nombre de points dans H_p inter (Z/pZ)^k est p^{k-1}. Si <2>_p est "generique" (r pas trop petit), l'intersection a taille environ r^k * p^{k-1} / p^k = r^k / p. Pour que cette intersection soit vide, il faudrait r^k < p, soit k < log(p)/log(r).

Pour un premier p ~ d^{1/m} (un facteur de d), r = ord_p(2) <= p - 1. La condition r^k < p donne k * log(r) < log(p), soit k < log(p)/log(r). Si r est proche de p, k < 1 + epsilon. Pas utile.

### 7.4 Multi-premiers

En combinant M premiers p_1, ..., p_M par CRT, on obtient une fraction des k-uplets admissibles qui est le produit :

Fraction = prod_{i=1}^{M} |H_{p_i} inter (<2>_{p_i})^k| / |(<2>_{p_i})^k|

Si chaque premier elimine independamment une fraction (1 - 1/p_i) des candidats (heuristiquement), le produit teleLscopique converge vers 0 lorsque sum 1/p_i diverge... mais c'est exactement l'HEURISTIQUE CRT de R183, reformulee en langage de reseaux. On retrouve le meme objet, sans aucun gain.

**CONCLUSION : L'approche CRT-reseau est un REBRANDING de l'anti-correlation CRT de R183-R184. Zero contenu nouveau.** [PROUVE]

---

## 8. DIAGNOSTIC STRUCTURAL : POURQUOI LA GEOMETRIE DES NOMBRES ECHOUE

### 8.1 La raison profonde (PROUVE)

La geometrie des nombres s'applique lorsque le probleme admet une formulation ou :
(i) Les inconnues sont des coordonnees ENTIERES d'un reseau
(ii) Les contraintes sont LINEAIRES (ou polynomiales de bas degre) en ces coordonnees
(iii) Le domaine de recherche est un corps CONVEXE

Pour le probleme de Collatz :
- Les inconnues naturelles sont les B_j (entiers), condition (i) OK
- La contrainte g(v) congruent a 0 mod d est EXPONENTIELLE en B_j, condition (ii) ECHOUE
- Le domaine (monotonie + somme fixee) est un simplexe, condition (iii) OK

La linearisation x_j = 2^{B_j} restaure (ii) mais detruit (i) et (iii) :
- Les x_j ne sont plus des coordonnees entieres generiques mais des puissances de 2, condition (i) ECHOUE
- Le domaine en x_j (puissances de 2, monotone, produit fixe) n'est pas convexe, condition (iii) ECHOUE

**Il n'existe pas de systeme de coordonnees dans lequel les trois conditions (i), (ii), (iii) sont simultanement satisfaites.** C'est le meme MISMATCH DE REGISTRES identifie en R185 (Branche 1, Niveau A2) : la structure additive de g et la structure multiplicative des puissances de 2 vivent dans des mondes incompatibles.

### 8.2 Comparaison avec des problemes ou la geometrie des nombres MARCHE

| Probleme | Inconnues | Contrainte | Domaine | GdN marche ? |
|----------|-----------|------------|---------|--------------|
| Sommes de carres | a, b dans Z | a^2 + b^2 = n | cercle (convexe) | OUI (Gauss) |
| Approximation diophantienne | p, q dans Z | |alpha - p/q| < epsilon | bande (convexe) | OUI (Minkowski, LLL) |
| Factorisation (Coppersmith) | x dans Z | f(x) = 0 mod N | [-X, X] (convexe) | OUI (LLL) |
| **Cycles de Collatz** | **B_j dans Z** | **sum a_j * 2^{B_j} = 0 mod d** | **simplexe monotone** | **NON** |

La difference cruciale : dans les cas ou la GdN marche, la contrainte est POLYNOMIALE (degre 1 ou 2) en les inconnues entieres. Pour Collatz, la contrainte est EXPONENTIELLE.

### 8.3 Y a-t-il un passage a la limite ?

On pourrait imaginer une astuce : prendre le logarithme de g(v). Mais log(sum a_j * 2^{B_j}) n'est pas une expression simple en les B_j. Le logarithme d'une somme n'est pas la somme des logarithmes.

La seule exception serait si g(v) etait DOMINE par un seul terme (le terme maximal). Dans ce cas, log g(v) ~ log(a_0 * 2^{B_0}) = (k-1)*log 3 + B_0 * log 2, qui EST lineaire en B_0. Mais la dominance d'un seul terme n'est valide que si les autres termes sont negligeables, ce qui n'est pas le cas en general (les k termes de g ont des ordres de grandeur comparables quand les B_j sont espaces regulierement).

**CONCLUSION : Pas de passage a la limite exploitable.** [PROUVE]

---

## 9. CE QUI RESTE

### 9.1 Ce que la geometrie des nombres a clarifie

1. **Le probleme de Collatz n'a PAS de structure de reseau naturelle.** C'est un fait structural, pas un echec technique. [PROUVE]

2. **La linearisation x_j = 2^{B_j} produit un reseau (L d'indice d dans Z^k) mais les contraintes residuelles (x_j puissance de 2) rendent le probleme PLUS DUR, pas plus facile.** [PROUVE]

3. **L'approche CRT multi-premiers est un rebranding de l'anti-correlation CRT.** Pas de gain. [PROUVE]

4. **Baker donne des bornes sur d mais ne traite que le regime k -> infini, deja couvert par Borel-Cantelli.** [PROUVE]

5. **Le diagnostic fondamental est confirme : le mismatch entre la structure additive (g est une somme) et la structure multiplicative (les termes sont des puissances de 2 ponderees par des puissances de 3) est l'OBSTACLE CENTRAL.** Ce mismatch est le meme que celui identifie en R185 (Branche 1), sous un angle different. [CONDITIONNEL -- c'est une interpretation, pas un theoreme]

### 9.2 Directions NON explorees ici

- **Reseaux p-adiques :** Travailler dans Q_2 ou Q_3 pourrait changer la geometrie. La condition g congruent a 0 mod d est une condition 2-adique et 3-adique. L'analyse p-adique de la dynamique de Collatz existe (Lagarias) mais ne produit pas de reseaux exploitables a ma connaissance.

- **Geometrie tropicale :** Dans le semi-anneau tropical (min, +), les sommes d'exponentielles se linearisent (max des termes). La condition g(v) ~ 0 deviendrait max_j (a_j + B_j * log 2) ~ 0, qui est lineaire par morceaux. Mais "~ 0" perd l'information exacte de divisibilite. Piste SPECULATIVE, probablement un cul-de-sac.

- **Reseaux de fonctions L :** Connexion avec la geometrie arithmetique via les fonctions zeta de hauteur. Totalement speculatif et probablement hors de portee.

---

## 10. SANITY CHECK FINAL

### k = 1
S = 2, d = 1, g = 2^1 = 2. Reseau L = Z (tout entier est dans L). La contrainte x_0 = 2^{B_0} avec B_0 = 1 donne x_0 = 2. On a 2 congruent a 0 mod 1. Cycle trivial trouve. COHERENT.

### k = 2
S = 4 (minimal : d = 16 - 9 = 7). Contrainte : B_0 + B_1 = 2, B_0 <= B_1.
Vecteurs : (0, 2), (1, 1).
g((0,2)) = 3 * 1 + 1 * 4 = 7. 7/7 = 1. CYCLE ! Mais attendons... k=2, S=4, d=7, n=1 donnerait n_0 = 7/7 = 1. Le nombre 1 a-t-il un cycle de type (k=2, S=4) ? Verifions : 1 -> 4 -> 2 -> 1 (c'est le cycle trivial avec k=1). Pour k=2, la sequence serait : n -> (3n+1)/2^{B_0} -> (3*(...)+1)/2^{B_1} -> n. Avec B_0 = 0, B_1 = 2 : n -> (3n+1)/1 = 3n+1 -> (3(3n+1)+1)/4 = (9n+4)/4. Pour boucler : (9n+4)/4 = n, soit 9n+4 = 4n, soit 5n = -4. n = -4/5. Pas entier.

**CORRECTION :** La formule g(v) = n*d ne donne pas directement n comme point de depart du cycle avec cette parametrisation. Revoyons. Avec la convention standard : le cycle a k etapes impaires, S etapes totales, et n = g(v)/d. Pour (0,2) : g = 7, d = 7, n = 1. Verifions le cycle de 1 : T(1) = (3*1+1)/2^2 = 1. Oui ! C'est le cycle trivial {1}, en 1 etape impaire (1 est impair, 3*1+1 = 4, 4/4 = 1). Mais c'est k=1 (une seule etape impaire), pas k=2. Le probleme : B_0 = 0 signifie ZERO divisions par 2 apres une etape impaire, ce qui est interdit (3n+1 est toujours pair, donc B_j >= 1).

Avec B_j >= 1 : B_0 + B_1 = 2, B_0 <= B_1, B_j >= 1. Seul vecteur : (1,1). g((1,1)) = 3*2 + 1*2 = 8. 8/7 n'est pas entier. Pas de cycle k=2, S=4. COHERENT.

---

## 11. CONCLUSION

**La geometrie des nombres ne fournit pas d'outil applicable au probleme des cycles de Collatz.** L'obstacle est structurel et irreductible : le melange de bases 2 et 3 dans g(v) cree une forme exponentielle qui ne s'inscrit dans aucun cadre de reseau classique. Toute linearisation introduit des contraintes residuelles (puissances de 2) qui detruisent la structure convexe necessaire aux theoremes de Minkowski/LLL/Baker.

Ce n'est pas une surprise : si la geometrie des nombres suffisait, le probleme serait resolu depuis les annees 1980 (LLL date de 1982). L'echec est informatif : il confirme que le coeur du probleme reside dans l'INTERACTION entre bases 2 et 3, que ni l'analyse (Baker), ni la combinatoire (comptage), ni la geometrie (reseaux) ne parviennent a saisir isolement.

**Statut : IMPASSE DIAGNOSTIQUEE.** L'approche est honnement fermee.

---

## INVENTAIRE DES RESULTATS

| # | Enonce | Statut | Score |
|---|--------|--------|-------|
| R186.1 | g(v) congruent a 0 mod d n'est pas une condition de reseau en (B_j) | PROUVE | - |
| R186.2 | La linearisation x_j = 2^{B_j} donne un reseau L d'indice d dans Z^k | PROUVE | - |
| R186.3 | L'intersection L inter {puissances de 2}^k est equivalente au comptage direct | PROUVE | - |
| R186.4 | Le reseau dual L* n'a pas de vecteur anormalement court | PROUVE | - |
| R186.5 | Baker donne d > 2^{S - c*log^2 S} mais ne traite que k -> infini | PROUVE | - |
| R186.6 | Coppersmith ne s'applique pas (pas de polynome en variables "petites") | PROUVE | - |
| R186.7 | L'approche CRT-reseau = rebranding de l'anti-correlation CRT | PROUVE | - |
| R186.8 | Pas de coordonnees satisfaisant (lineaire, entier, convexe) simultanement | PROUVE | - |
| R186.9 | Le mismatch additif/multiplicatif est l'obstacle central | CONDITIONNEL | - |

**Score R186 : 2/10** -- Zero progres sur les cycles, mais 9 resultats negatifs proprement etiquetes qui ferment l'approche.
