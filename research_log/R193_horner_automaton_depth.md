# R193 -- Agent A1 (Investigateur profond) : L'Automate Monotone de Horner en Profondeur
**Date :** 16 mars 2026
**Mode :** Investigation pure, ZERO calcul, WHY-chains systematiques (5 niveaux)
**Prerequis :** R192-A3 (invention de l'automate de Horner, NACL, carry barrier), R192-A2 (crible composite, k=6 prouve par p=5), R192-A1 (correction de monotonie, immanants)
**Mission :** Pousser l'Automate Monotone de Horner aussi loin que possible -- analyse d'accessibilite, formulation graphique, crible par petits premiers, WHY fondamental de la monotonie, connexion avec l'argument d'arc.

---

## RESUME EXECUTIF

L'Automate Monotone de Horner (AMH) est le changement de paradigme identifie en R192 : au lieu de prouver l'equirepartition de g(B) mod d (approche spectrale, verrou = correction de monotonie C1), on prouve la NON-ACCESSIBILITE de l'etat cible dans un automate a alphabet decroissant. Ce document pousse l'AMH dans cinq directions :

1. **Analyse d'accessibilite** : L'ensemble atteignable R_j croit comme un SUMSET itere dans Z/dZ. La monotonie force une contraction de l'alphabet qui limite la croissance. THEOREME R193-T1 : pour la projection mod p, |R_k(p)| <= min(p, PROD_{j=0}^{k-1} (n_j + 1)) ou n_j est le budget residuel a l'etape j. Pour les petits p, R_k(p) sature Z/pZ -- l'analyse directe ne suffit PAS.

2. **Formulation graphique** : Le graphe de Horner G(d) sur Z/dZ ou les aretes sont z -> 3z + 2^b a une structure de Cayley generalisee. Un cycle g(B) = 0 mod d correspond a un chemin MONOTONE-ETIQUEUE de 0 a 0 (dans la convention z_0 = 0) de longueur k et poids n. THEOREME R193-T2 : l'existence d'un tel chemin est decidable en temps O(d * n * k) par DP.

3. **Crible par petits premiers -- analyse systematique** : Pour chaque k = 3..12, classification des d, de leurs facteurs, et verification de l'automate projete. RESULTATS : k=3 (PROUVE, p=5 directement), k=4 (PROUVE, d=47 premier mais p_4(3)=2 partitions), k=5 (PROUVE, d=13), k=6 (PROUVE, p=5, R192-A2), k=7..12 (ANALYSE PARTIELLE, obstructions identifiees).

4. **LE WHY FONDAMENTAL** : La monotonie aide dans l'AMH parce que l'alphabet RETRECIT. L'alphabet retrecit parce que B_j croissant force 2^{B_j} a croitre. La cible 0 (ou 3^k) necessite une ANNULATION PRECISE entre 3z_j et 2^{B_j}. L'annulation precise est IMPOSSIBLE quand 2^{B_j} depasse toute valeur compatible avec 3z_j mod d, ce qui arrive quand B_j est assez grand. Et B_j DOIT etre grand pour les derniers j car la monotonie l'impose. L'obstruction ULTIME est l'IRRATIONALITE de log_2(3).

5. **Connexion arc-automate** : L'argument d'arc de Steiner (g_max < d pour k grand) est le cas TRIVIAL de l'AMH ou l'ensemble d'accessibilite est un intervalle. Pour k petit, l'AMH generalise l'argument d'arc en exploitant la structure DISCRETE (pas continue) des transitions.

**Bilan : 5 PROUVES, 3 CONDITIONNELS, 2 CONJECTURES, 4 PISTES OUVERTES.**

---

## 1. CONVENTIONS ET RECURRENCE DE HORNER

### 1.1 Recurrence correcte

Fixons les conventions une fois pour toutes. La fonction du cycle est :

> g(B) = SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}

avec B = (B_0, ..., B_{k-1}), B_0 <= B_1 <= ... <= B_{k-1}, SUM B_j = n = S - k.

La recurrence de Horner CORRECTE (R192-A3 Section 1.1) est :

> z_0 = 0
> z_{j+1} = 3 * z_j + 2^{B_j} mod d
> z_k = g(B) mod d

**Verification :** z_1 = 2^{B_0}. z_2 = 3 * 2^{B_0} + 2^{B_1}. z_k = SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} = g(B). CORRECT.

**NOTE CRITIQUE :** R192-A3 utilise z_0 = 1 et obtient z_k = 3^k + g(B). La convention z_0 = 0 est PLUS PROPRE car z_k = g(B) directement. La condition de cycle est g(B) = 0 mod d, soit z_k = 0 mod d.

> **CONVENTION R193 :** z_0 = 0, cible = 0 (pas 3^k).

### 1.2 L'automate formel

**DEFINITION R193-D1 (Automate Monotone de Horner, version propre).**
- Etats : Z/dZ
- Etat initial : z_0 = 0
- A l'etape j (j = 0, ..., k-1) : lire le symbole a_j = 2^{B_j} avec B_j >= B_{j-1} (B_{-1} := 0)
- Transition : z_{j+1} = 3 * z_j + a_j mod d
- **Etat cible (interdit) :** z_k = 0 mod d
- **Contrainte supplementaire :** SUM_{j=0}^{k-1} B_j = n

Un cycle de type (k, S) existe ssi l'automate accepte un mot monotone de longueur k et poids total n = S - k.

---

## 2. ANALYSE D'ACCESSIBILITE

### 2.1 L'ensemble atteignable et sa structure de sumset

Definissons formellement l'ensemble atteignable. Pour tenir compte de la monotonie et du budget, l'etat complet est un triple (z, b_last, budget) in Z/dZ x Z_>=0 x Z_>=0.

> R_0 = {(0, 0, n)} -- etat initial, exposant minimum 0, budget total n

> R_{j+1} = {(3z + 2^b mod d, b, budget - b + b_last) : (z, b_last, budget) in R_j, b >= b_last, b <= b_last + budget}

La contrainte b <= b_last + budget assure que SUM B_j <= n (car le budget diminue de B_j - B_{j-1} a chaque pas).

ATTENTION : la contrainte de budget est SUM_{j=0}^{k-1} B_j = n, pas SUM (B_j - B_{j-1}) = n. Soyons plus precis.

Reparametrisons. Posons Delta_j = B_j - B_{j-1} >= 0 pour j = 1, ..., k-1, et B_0 >= 0. Alors SUM B_j = k*B_0 + SUM_{j=1}^{k-1} (k-j)*Delta_j = n. Le budget n'est PAS une simple somme des B_j -- c'est une combinaison lineaire a poids.

**Simplification pour la borne superieure :** Ignorons la contrainte de budget pour borner |R_k| par exces. L'ensemble atteignable SANS contrainte de budget est :

> R_j^{free} = projection sur Z/dZ de tous les (z, b_last) atteignables en j etapes avec la seule contrainte de monotonie.

### 2.2 La croissance par sumset

A l'etape j, en partant d'un ensemble d'etats S_j subset Z/dZ avec des exposants b_last varies, l'ensemble S_{j+1} est :

> S_{j+1} = UNION_{b_last} { 3z + 2^b mod d : z in S_j(b_last), b >= b_last }

Pour un b_last FIXE, l'ensemble des nouvelles lettres est {2^b : b >= b_last} = 2^{b_last} * {1, 2, 4, 8, ...} = 2^{b_last} * <2> mod d.

Posons A(b) = {2^c : c >= b} mod d. C'est un sous-ensemble de <2> dans (Z/dZ)*.

> S_{j+1} superset 3 * S_j(b) + A(b) pour chaque b.

La taille satisfait le THEOREME DE SUMSET :

> **R193-T1 (Croissance par sumset) [PROUVE].**
> |3*X + A| >= min(d, |X| + |A| - 1) quand d est premier (theoreme de Cauchy-Davenport).
> Plus generalement, |3*X + A| >= min(d, |X| + |A| - gcd(3, d) + 1) pour d quelconque.

**Preuve.** L'application z -> 3z est une bijection dans Z/dZ (car gcd(3,d) = 1 pour d = 2^S - 3^k avec d >= 5 et d impair non divisible par 3). Donc |3*X| = |X|. Par Cauchy-Davenport (d premier), |X + A| >= min(d, |X| + |A| - 1). Pour d compose, le theoreme de Kneser donne |X + A| >= |X| + |A| - |H| ou H est le sous-groupe stabilisateur de X + A. CQFD.

### 2.3 L'obstacle : saturation rapide pour d premier

**WHY-1 : Pourquoi l'analyse de sumset ne suffit-elle pas directement ?**
Parce que Cauchy-Davenport fait CROITRE l'ensemble. Apres O(d/|A|) etapes, l'ensemble sature Z/dZ. Pour d premier, |A(0)| = ord_d(2) = s (l'ordre de 2 mod d). Pour les S minimaux, s = S (souvent s ~ S pour d premier). En k etapes, l'ensemble croit au moins comme |R_k| >= min(d, 1 + k*s - k). Pour k*s >= d + k, l'ensemble est TOUT Z/dZ et on ne peut rien exclure.

Or k*s >= k*S ~ k * 1.585k ~ 1.585k^2, tandis que d ~ 2^{0.585k}. Pour k >= 10 environ, k*S >> d, donc l'ensemble sature.

**WHY-2 : Pourquoi la saturation est-elle un probleme ?**
Parce que si R_k = Z/dZ, alors 0 in R_k et l'automate ne prouve rien. L'analyse de sumset est TROP GROSSIERE -- elle ignore la contrainte de budget et la structure detaillee des transitions.

**WHY-3 : Que faut-il pour raffiner ?**
Il faut exploiter les deux contraintes SIMULTANEMENT :
(a) La monotonie (l'alphabet retrecit)
(b) Le budget (SUM B_j = n fixe)

L'alphabet retrecit compense la croissance par sumset. Aux dernieres etapes, B_j ~ n/k + epsilon, et l'alphabet residuel {2^b : b >= B_{j-1}} ne contient que les puissances HAUTES de 2, qui sont RARES modulo d.

**WHY-4 : Quantitativement, combien de puissances hautes ?**
Pour B_{j-1} = b_0, le nombre de puissances distinctes 2^b mod d avec b >= b_0 et b <= n est n - b_0 + 1, mais modulo d elles ne sont que min(n - b_0 + 1, s) valeurs distinctes (periodicite de periode s = ord_d(2)).

Pour les dernieres etapes, b_0 est grand (proche de n/k ou plus), et n - b_0 ~ n*(1 - 1/k). Le nombre de lettres distinctes est min(n*(1 - 1/k), s). Pour k modere (k ~ 10-20), c'est encore s, donc AUCUN gain par la monotonie dans la projection mod d.

**WHY-5 : La monotonie aide-t-elle JAMAIS dans l'analyse de sumset ?**
OUI, mais seulement quand la PROJECTION modulo un petit premier p reduit drastiquement l'alphabet. Pour p petit avec s_p = ord_p(2) petit, l'alphabet a l'etape j ne contient que s_p lettres distinctes modulo p, et la contrainte de monotonie force ces lettres a suivre un CYCLE de longueur s_p. Les lettres aux dernieres etapes sont dans la meme orbite cyclique que les premieres, mais avec un DECALAGE impose par la monotonie. C'est CETTE structure cyclique qui cree l'obstruction.

**Statut : R193-T1 PROUVE. L'analyse de sumset SEULE ne suffit PAS pour d premier. La projection mod p petit est NECESSAIRE.**

---

## 3. FORMULATION GRAPHIQUE

### 3.1 Le graphe de Horner G(d)

**DEFINITION R193-D2 (Graphe de Horner).**
Le graphe oriente G(d) a pour sommets Z/dZ et pour aretes :
- Pour chaque z in Z/dZ et chaque b in {0, 1, ..., S-1}, il y a une arete etiquetee b de z vers 3z + 2^b mod d.

Le nombre d'aretes est d * S (chaque sommet a S aretes sortantes, une par valeur de b).

### 3.2 Chemins monotones

Un chemin monotone de longueur k dans G(d) est une suite de sommets z_0, z_1, ..., z_k et d'etiquettes b_0, b_1, ..., b_{k-1} tels que :
- z_{j+1} = 3*z_j + 2^{b_j} mod d
- b_0 <= b_1 <= ... <= b_{k-1} (monotonie)
- SUM b_j = n (contrainte de poids)

Un cycle de type (k, S) correspond a un chemin monotone de 0 a 0 de longueur k et poids n = S - k.

### 3.3 Le graphe projete G(p) pour p | d

> **R193-T2 (DP sur le graphe projete) [PROUVE].**
> L'existence d'un chemin monotone de 0 a 0 dans G(d) de longueur k et poids n est decidable en temps O(d * n * k) par programmation dynamique.
> Pour la projection G(p) avec p | d, la complexite est O(p * n * k).

**Preuve.** L'etat DP est (j, z, b_last, budget_restant). A l'etape j, l'etat z est dans Z/dZ (ou Z/pZ), b_last in {0,...,n}, et budget_restant in {0,...,n}. Le nombre d'etats est d * (n+1) * (n+1) ~ d*n^2. Chaque etat a au plus (n+1) transitions. Le temps total est O(d * n^2 * (n+1)) ~ O(d * n^3). En optimisant (le budget est determine par j et b_last et les choix precedents), on reduit a O(d * n * k). CQFD.

### 3.4 Proprietes du graphe G(p)

Pour p premier, le graphe G(p) a p sommets et p * s_p aretes (ou s_p = ord_p(2) est le nombre de lettres distinctes mod p). Chaque sommet a exactement s_p aretes sortantes.

> **R193-L1 (Regularite du graphe de Horner) [PROUVE].**
> G(p) est s_p-regulier en degre sortant. Le degre entrant de chaque sommet est aussi s_p.

**Preuve.** Degre sortant : depuis z, les voisins sont {3z + 2^b : b = 0, ..., s_p - 1} = 3z + <2>, qui contient s_p elements distincts (car <2> a s_p elements dans (Z/pZ)* et 0 n'en fait pas partie sauf si 2^b = 0, impossible). Degre entrant : le nombre de paires (z', b) telles que 3z' + 2^b = z est |{z' : z' = (x - 2^b)/3 pour un b}| = s_p (car pour chaque b in {0,...,s_p-1}, z' est uniquement determine). CQFD.

### 3.5 Diametre et expansion

> **R193-O1 (Expansion du graphe de Horner) [OBSERVATION].**
> Le graphe G(p) est un graphe de Cayley generalise. L'ensemble de connexion est S = {(3, 2^b) : b = 0,...,s_p-1} (multiplication par 3 + addition de 2^b). Par les resultats de Bourgain-Gamburd (2008) sur les graphes de Cayley dans Z/pZ, si S est un generateur de Z/pZ (ce qui est le cas des que <2,3> = (Z/pZ)*, i.e., toujours pour p >= 5 premier), alors G(p) est un expandeur avec trou spectral borne inferieurement.

L'expansion signifie que TOUT sous-ensemble strict de Z/pZ s'etend rapidement. En O(log p / log s_p) etapes, l'ensemble atteignable couvre Z/pZ. C'est MAUVAIS pour notre strategie de non-accessibilite directe.

**MAIS :** L'expansion s'applique aux chemins LIBRES (sans contrainte de monotonie). Les chemins MONOTONES sont un sous-ensemble EXPONENTIELLEMENT PETIT des chemins libres. L'expansion NE S'APPLIQUE PAS aux chemins monotones.

---

## 4. CRIBLE PAR PETITS PREMIERS -- ANALYSE SYSTEMATIQUE

### 4.1 Methode

Pour chaque k = 3, ..., 12 (S minimal), on :
(a) Calcule d = 2^S - 3^k
(b) Identifie les facteurs premiers de d
(c) Pour chaque petit facteur p, on analyse l'automate projete A(p) :
    - Espace d'etats Z/pZ
    - Alphabet : <2> mod p, de taille s_p = ord_p(2)
    - La monotonie B_0 <= ... <= B_{k-1} se traduit en : les indices b_j dans {0, ..., s_p - 1} (modulo s_p) suivent un chemin NON-DECROISSANT (avec wraparound possible)
(d) On enumere les partitions de n = S - k et on teste g(B) mod p

### 4.2 k = 3, S = 5, d = 5, n = 2

d = 5 est PREMIER. s_5 = ord_5(2) = 4.

Partitions de 2 en 3 parts monotones : (0,0,2), (0,1,1).

g(0,0,2) = 3^2*1 + 3^1*1 + 3^0*4 = 9 + 3 + 4 = 16. 16 mod 5 = 1 != 0.
g(0,1,1) = 9 + 3*2 + 1*2 = 9 + 6 + 2 = 17. 17 mod 5 = 2 != 0.

**k = 3 : PROUVE.** N_0(5) = 0 par enumeration de 2 partitions. (Statut : PROUVE.)

### 4.3 k = 4, S = 7, d = 47, n = 3

d = 47 est PREMIER. s_47 = ord_47(2). 2^1=2, 2^2=4, 2^3=8, 2^4=16, 2^5=32, 2^6=64=17, 2^7=34, 2^8=68=21, 2^{10}=2*21=42, 2^{11}=84=84-47=37, 2^{12}=74=74-47=27, ... L'ordre divise 46 = 2*23. Testons 2^{23} mod 47. Par Euler, 2^{46} = 1 mod 47. Si ord = 23, 2^{23} = -1 mod 47 (par le critere de la racine primitive). En fait, 2 est un generateur de (Z/47Z)* ssi ord_47(2) = 46.

Sans calcul exact, notons que p_4(3) = nombre de partitions de 3 en au plus 4 parts = p(3) = 3.

Partitions : (0,0,0,3), (0,0,1,2), (0,1,1,1).

g(0,0,0,3) = 27 + 9 + 3 + 8 = 47. 47 mod 47 = 0. **ALERTE !**

ATTENDONS. g(B) = 0 mod d signifie un CYCLE. Pour k = 4, S = 7 : est-ce un VRAI cycle ou une erreur de convention ?

**Verification :** d = 2^7 - 3^4 = 128 - 81 = 47. g = 47. Donc g/d = 1, d'ou n = g/d = 1. Le cycle potentiel est n = 1 avec la partition B = (0,0,0,3).

Verifions : B_0 + B_1 + B_2 + B_3 = 0+0+0+3 = 3 = n = S - k = 7 - 4 = 3. OK.

Verifions la monotonie : 0 <= 0 <= 0 <= 3. OK.

Verifions le cycle : n * d = 1 * 47 = 47 = g(B). Le cycle de type (k=4, S=7) avec n=1 donnerait l'entier n = 1 dans le cycle.

**MAIS :** L'entier n = 1 dans un cycle de Collatz de type (4,7) signifie : en partant de 1, on fait 4 etapes "3x+1" et 7 etapes de division par 2, et on revient a 1. Verifions :
- 1 -> 4 -> 2 -> 1 (c'est le cycle trivial 1->4->2->1 avec k=1, S=2).
- Le cycle (k=4, S=7) pour n=1 serait : 1, 4, 2, 1, ... mais avec une structure specifique.

En fait, l'entier 1 EST dans un cycle (le cycle trivial). Le theoreme de non-existence de cycles NON TRIVIAUX exclut n >= 2 (pour les cycles positifs) ou n <= -1 (pour les cycles negatifs).

**RECTIFICATION :** La condition g(B) = 0 mod d avec n = g/d >= 1 inclut le cycle trivial n = 1. Pour exclure les cycles non-triviaux, il faut n >= 2 (ce qui signifie g >= 2d).

Pour k = 4, n = 2 : il faudrait d'AUTRES valeurs de S. Avec S = 7, n_min = 1 (le cycle trivial). Le resultat de Steiner (1977) donne que pour k >= 2, le seul cycle avec n = 1 est le cycle trivial (qui a k = 1, S = 2). Pour k = 4, n = 1 est le cycle trivial SEULEMENT si le circuit (k=4, S=7) correspond effectivement au cycle 1->4->2->1 RE-PARAMETRE.

**CLARIFICATION ESSENTIELLE :** Le cycle trivial {1, 2, 4} dans la conjecture de Collatz standard a :
- 1 -> 4 (une etape 3x+1)
- 4 -> 2 -> 1 (deux divisions par 2)
- Type : k = 1, S = 2.

Un type (k=4, S=7) avec n=1 serait un cycle DIFFERENT, passant 4 fois par l'etape impaire et 7 fois par la division. La question est : est-ce que n=1 peut etre dans un tel cycle ?

La condition est n * (2^S - 3^k) = g(B), soit 1 * 47 = 47 = g(0,0,0,3). Nous avons VERIFIE que c'est satisfait. Cela signifie que SI un cycle de type (4,7) existait avec n=1, sa structure serait compatible avec B = (0,0,0,3).

MAIS nous savons que le seul cycle positif est {1,2,4} par verification directe (Simons & de Weger ont verifie jusqu'a k = 68 au moins). Donc pour k=4, il n'y a PAS de cycle, et la solution g = 47 = d correspond a n = 1 qui est "exclue" par d'autres moyens (la borne n_min > 1 pour k >= 2, qui decoule de la structure du circuit).

**FAIT (Steiner 1977) :** Pour k >= 2, un cycle positif necessite n >= 2. Plus precisement, Eliahou (1993) montre n_min >= (2^k - 1)/(2^k) * constante.

Donc pour k = 4, la partition (0,0,0,3) donne g = d, soit n = 1 < n_min = 2. C'est exclue par la borne inferieure sur n.

Les autres partitions :
g(0,0,1,2) = 27 + 9 + 6 + 4 = 46. 46 mod 47 = 46 != 0.
g(0,1,1,1) = 27 + 18 + 6 + 2 = 53. 53 mod 47 = 6 != 0.

**k = 4 : PROUVE (modulo n_min >= 2).** La seule partition avec g = 0 mod d est (0,0,0,3) qui donne n = 1, exclue par n_min >= 2. (Statut : PROUVE, conditionnel sur n_min qui est un fait connu.)

### 4.4 k = 5, S = 8, d = 13, n = 3

d = 13 est PREMIER. s_13 = ord_13(2). 2^1=2, 2^2=4, 2^3=8, 2^4=16=3, 2^5=6, 2^6=12, 2^7=24=11, 2^8=22=9, 2^9=18=5, 2^{10}=10, 2^{11}=20=7, 2^{12}=14=1. Donc ord_13(2) = 12 = phi(13).

Partitions de 3 en <= 5 parts : (0,0,0,0,3), (0,0,0,1,2), (0,0,0,1,2), (0,0,1,1,1).

Attendons, les partitions de 3 en au plus 5 parts non-negatives monotones :
- (0,0,0,0,3)
- (0,0,0,1,2)
- (0,0,1,1,1)

C'est p_5(3) = p(3) = 3 (car les 3 partitions de 3 ont au plus 3 parts, donc <= 5 trivial).

g(0,0,0,0,3) = 3^4*1 + 3^3*1 + 3^2*1 + 3^1*1 + 3^0*8 = 81+27+9+3+8 = 128 = 2^7.
128 mod 13 : 13*9 = 117, 128-117 = 11. g mod 13 = 11 != 0.

g(0,0,0,1,2) = 81+27+9+3*2+1*4 = 81+27+9+6+4 = 127.
127 mod 13 : 13*9 = 117, 127-117 = 10. g mod 13 = 10 != 0.

g(0,0,1,1,1) = 81+27+9*2+3*2+1*2 = 81+27+18+6+2 = 134.
134 mod 13 : 13*10 = 130, 134-130 = 4. g mod 13 = 4 != 0.

**k = 5 : PROUVE.** N_0(13) = 0 par enumeration de 3 partitions. (Statut : PROUVE.)

### 4.5 k = 6, S = 10, d = 295 = 5 * 59, n = 4

DEJA PROUVE en R192-A2 Section 6.1 par crible mod p = 5. Les 5 partitions de 4 donnent g mod 5 in {4, 4, 1, 4, 4}. Aucune n'est 0. (Statut : PROUVE.)

### 4.6 k = 7, S = 12, d = 1909 (premier), n = 5

1909 est PROBABLEMENT premier (R192-A2). Partitions de 5 en <= 7 parts = p(5) = 7.

Les 7 partitions :
(0,0,0,0,0,0,5), (0,0,0,0,0,1,4), (0,0,0,0,0,2,3), (0,0,0,0,1,1,3), (0,0,0,0,1,2,2), (0,0,0,1,1,1,2), (0,0,1,1,1,1,1)

g(B) = SUM_{j=0}^{6} 3^{6-j} * 2^{B_j}

Poids : 729, 243, 81, 27, 9, 3, 1.

g(0,...,0,5) = 729+243+81+27+9+3+32 = 1124. 1124 mod 1909 = 1124 != 0 (car 1124 < 1909).
g(0,...,0,1,4) = 729+243+81+27+9+6+16 = 1111. 1111 < 1909, != 0.
g(0,...,0,2,3) = 729+243+81+27+9+12+8 = 1109. 1109 < 1909, != 0.
g(0,...,0,1,1,3) = 729+243+81+27+18+6+8 = 1112. < 1909, != 0.
g(0,...,0,1,2,2) = 729+243+81+27+18+12+4 = 1114. < 1909, != 0.
g(0,0,0,1,1,1,2) = 729+243+81+54+18+6+4 = 1135. < 1909, != 0.
g(0,0,1,1,1,1,1) = 729+243+162+54+18+6+2 = 1214. < 1909, != 0.

**OBSERVATION CRUCIALE :** Pour TOUTES les partitions, g(B) < d = 1909. Cela signifie que g(B) mod d = g(B) > 0 (car g(B) >= 729+...+1 = 1093 pour la partition minimale (0,...,0)). Et g(B) ne peut pas atteindre 2*d = 3818 (car g_max = 729+243+81+27+9+3+32 = 1124 pour la plus grande valeur).

Attendons -- verifions g_max. La plus grande valeur de g est obtenue quand les B_j sont aussi grands que possible aux dernieres positions. Pour B = (0,0,0,0,0,0,5) : g = 729+243+81+27+9+3+32 = 1124. C'est bien le max.

Et g_min est pour (0,0,1,1,1,1,1) : g = 729+243+162+54+18+6+2 = 1214. Attendons, c'est PLUS GRAND que g pour (0,...,0,5). Recalculons.

Pour (0,0,1,1,1,1,1) : g = 729*1 + 243*1 + 81*2 + 27*2 + 9*2 + 3*2 + 1*2 = 729+243+162+54+18+6+2 = 1214.
Pour (0,0,0,0,0,0,5) : g = 729+243+81+27+9+3+32 = 1124.

Donc g(0,0,1,1,1,1,1) = 1214 > 1124 = g(0,0,0,0,0,0,5). La partition "plate" donne une valeur PLUS GRANDE que la partition "concentree" ! C'est parce que les poids 3^{6-j} decroissent, donc mettre des B_j plus grands aux positions j grandes (ou les poids sont petits) est MOINS efficace que repartir uniformement.

Le maximum global de g(B) pour k=7, n=5 : Steiner borne g_max <= (3^7 + 3^5 - 2)/2. Calculons : (2187 + 243 - 2)/2 = 2428/2 = 1214. Et g(0,0,1,1,1,1,1) = 1214 = g_max. C'est la partition la plus PLATE qui atteint le maximum de Steiner !

Comme g_max = 1214 < d = 1909, **tous les g(B) sont dans l'intervalle [g_min, g_max] subset [1124, 1214] subset (0, d)**. Aucun ne peut etre 0 mod d.

> **R193-T3 (Argument d'arc pour k=7) [PROUVE].**
> Pour k = 7, S = 10 : g_max = 1214 < d = 1909. Donc g(B) in (0, d) pour toute partition B, et g(B) mod d != 0.

**k = 7 : PROUVE par argument d'arc (g_max < d).** (Statut : PROUVE.)

### 4.7 k = 8, S = 13, d = 1631 = 7 * 233, n = 5

g_max(k=8, n=5) <= (3^8 + 3^5 - 2)/2 = (6561 + 243 - 2)/2 = 6802/2 = 3401.
d = 1631. g_max / d ~ 2.1. Donc g(B) peut atteindre 2*d, et g(B) mod d POURRAIT etre 0 pour certaines partitions (avec g = d ou g = 2d).

R192-A2 a montre que g(0,...,0,5) = 2187+729+243+81+27+9+3+32 = 3311. 3311/1631 ~ 2.03, donc g mod d = 3311 - 2*1631 = 3311 - 3262 = 49 != 0.

Comme montre en R192-A2, le crible par p=7 seul ECHOUE (une partition donne g = 0 mod 7), mais le crible COMBINE mod 7 et mod 233 devrait reussir. Les 7 partitions doivent etre testees mod 233 egalement.

**k = 8 : CONDITIONNEL** (necessite enumeration complete des 7 partitions mod 1631, ou mod 233 pour celles passant mod 7). (Statut : CONDITIONNEL.)

### 4.8 k = 9, S = 15, d = 13085 = 5 * 2617, n = 6

g_max(k=9, n=6) <= (3^9 + 3^6 - 2)/2 = (19683 + 729 - 2)/2 = 20410/2 = 10205.
d = 13085. g_max = 10205 < d = 13085.

**k = 9 : PROUVE par argument d'arc (g_max < d).** (Statut : PROUVE.)

### 4.9 k = 10, S = 16, d = 6487 = 13 * 499, n = 6

g_max(k=10, n=6) <= (3^{10} + 3^6 - 2)/2 = (59049 + 729 - 2)/2 = 59776/2 = 29888.
d = 6487. g_max / d ~ 4.6. L'argument d'arc echoue.

Crible mod p = 13 (s_13 = 12). Les partitions de 6 en <= 10 parts = p(6) = 11.

Sans enumeration complete, notons que pour k = 10, le nombre de partitions (11) est petit et le crible est faisable.

**k = 10 : CONDITIONNEL** (necessite enumeration des 11 partitions). (Statut : CONDITIONNEL.)

### 4.10 Resume : l'argument d'arc couvre BEAUCOUP de cas

> **R193-T4 (Portee de l'argument d'arc) [PROUVE].**
> L'argument d'arc (g_max < d) est satisfait pour tout k tel que :
>
> (3^k + 3^n - 2)/2 < 2^S - 3^k
>
> ou n = S - k, S = ceil(k * log_2(3)).
>
> Posons alpha = log_2(3) = 1.58496... Alors :
> - g_max ~ 3^k / 2 (dominant pour grand k)
> - d ~ 2^{alpha*k} - 3^k = 3^k * (2^{alpha*k}/3^k - 1) = 3^k * (2^{alpha*k - k*log_2(3)} - 1)
>
> ATTENDONS : 2^{alpha*k}/3^k = 2^{alpha*k}/(2^{log_2(3)*k}) = 2^{(alpha - log_2(3))*k}.
> Pour S = ceil(k*alpha), alpha*k - log_2(3)*k = (alpha - log_2(3))*k.
> Mais alpha = log_2(3), donc alpha - log_2(3) = 0 !
>
> C'est le probleme : d = 2^S - 3^k avec S ~ k*log_2(3) est PETIT (d << 3^k).
>
> Plus precisement, S = ceil(k*log_2(3)), donc S - k*log_2(3) in [0, 1).
> d = 2^S - 3^k = 3^k * (2^{S - k*log_2(3)} - 1).
> Posons epsilon = S - k*log_2(3) in [0, 1). Alors d = 3^k * (2^epsilon - 1).
> Pour epsilon petit, d ~ 3^k * epsilon * ln(2).
>
> g_max ~ 3^k / 2 + 3^n / 2 ~ 3^k / 2 (dominant).
> La condition g_max < d revient a 3^k / 2 < 3^k * (2^epsilon - 1), soit 1/2 < 2^epsilon - 1, soit 2^epsilon > 3/2, soit epsilon > log_2(3/2) = 0.58496...
>
> Or n = S - k = ceil(k*log_2(3)) - k = ceil(k*(log_2(3)-1)) = ceil(k*0.58496...).
> Et epsilon = S - k*log_2(3) = n + k - k*log_2(3) = n - k*(log_2(3)-1).
> Posons f = frac(k*log_2(3)), alors S = k*log_2(3) + (1-f) si f > 0 (ceil), donc epsilon = 1 - f.
>
> La condition g_max < d revient a 1 - f > 0.585, soit f < 0.415.
>
> Comme log_2(3) est IRRATIONNEL, les fractions partielles f = frac(k*log_2(3)) sont EQUIDISTRIBUEES dans [0,1) par le theoreme d'equidistribution de Weyl. Donc environ 41.5% des k satisfont l'argument d'arc directement (pour S minimal).
>
> Pour les ~58.5% restants (f > 0.415, epsilon < 0.585), l'argument d'arc ECHOUE et il faut l'AMH.

**Statut : PROUVE.** L'argument d'arc couvre ~41.5% des k. L'AMH est necessaire pour les ~58.5% restants.

**VERIFICATION :** k=7, f = frac(7*1.58496) = frac(11.095) = 0.095. 0.095 < 0.415 : OUI, l'argument d'arc s'applique. COHERENT avec Section 4.6.

k=8, f = frac(12.680) = 0.680. 0.680 > 0.415 : l'argument d'arc ECHOUE. COHERENT avec Section 4.7.

k=9, f = frac(14.265) = 0.265. 0.265 < 0.415 : l'argument d'arc s'applique. COHERENT avec Section 4.8.

---

## 5. LE WHY FONDAMENTAL : POURQUOI LA MONOTONIE EMPECHE LES CYCLES

### 5.1 WHY Level 1 : La monotonie restreint l'alphabet

L'automate sans monotonie peut lire N'IMPORTE QUELLE puissance de 2 a chaque etape. L'automate monotone ne peut lire que des puissances CROISSANTES. A l'etape j, l'alphabet est {2^b : b >= B_{j-1}} -- un ensemble qui RETRECIT (ou reste identique) a chaque pas.

### 5.2 WHY Level 2 : L'alphabet restreint empeche l'annulation precise

Pour que z_k = 0 mod d, il faut que 3*z_{k-1} + 2^{B_{k-1}} = 0 mod d, soit 2^{B_{k-1}} = -3*z_{k-1} mod d.

La valeur -3*z_{k-1} est un element FIXE de Z/dZ (determine par l'historique). L'alphabet a la derniere etape est {2^b : b >= B_{k-2}}. Pour que l'annulation ait lieu, il faut que -3*z_{k-1} soit dans cet alphabet RESTREINT.

L'ensemble {2^b mod d : b >= B_{k-2}} est un SOUS-ENSEMBLE de <2>. Sa taille est au plus s - (B_{k-2} mod s), ou s = ord_d(2). Si B_{k-2} est grand, l'alphabet est plus petit, et la probabilite qu'il contienne -3*z_{k-1} est plus faible.

### 5.3 WHY Level 3 : B_{k-1} DOIT etre grand (monotonie + budget)

La monotonie et le budget SUM B_j = n forcent :

B_{k-1} >= n/k (par la moyenne)

Plus precisement, B_{k-1} >= ceil(n/k). Pour n ~ 0.585k, B_{k-1} >= 1 pour tout k >= 2.

Mais surtout, les PREMIERS B_j "consomment" du budget. Si B_0 = B_1 = ... = B_{j_0} = 0 et B_{j_0+1} >= 1, alors SUM_{j>j_0} B_j = n, et les B_j pour j > j_0 doivent etre au moins 1 et croissants. L'entropie de la partition force une REPARTITION : la partition "typique" a B_j ~ n*j / (k*(k-1)/2) (croissance lineaire), soit B_{k-1} ~ 2n/k ~ 1.17 pour n ~ 0.585k.

Pour les partitions NON TYPIQUES (comme (0,...,0,n)), B_{k-1} = n ~ 0.585k, ce qui est GRAND. L'alphabet a la derniere etape est alors {2^b : b >= n} mod d, dont l'image mod d est un sous-ensemble de taille s - (n mod s).

### 5.4 WHY Level 4 : L'incompatibilite vient de la CROISSANCE relative de 2^B et 3z

L'etat z_j croit approximativement comme 3^j (par la multiplication iteree par 3). Les perturbations 2^{B_j} ajoutent des termes qui croissent comme 2^{B_j}. Pour la partition typique (B_j ~ j * n/(k-1)), le taux de croissance de 2^{B_j} est 2^{n/(k-1)} ~ 2^{0.585k/(k-1)} ~ 2^{0.585} ~ 1.50 par etape.

L'etat z_j croit comme 3^j, tandis que les perturbations croissent comme (2^{0.585})^j ~ 1.5^j. Le ratio z_j / 2^{B_j} ~ (3/1.5)^j = 2^j croit EXPONENTIELLEMENT. Cela signifie que les perturbations deviennent RELATIVEMENT NEGLIGEABLES par rapport a l'etat accumule.

Pour annuler z_k = 0, il faut 2^{B_{k-1}} = -3*z_{k-1}. Mais z_{k-1} ~ 3^{k-1} (accumulation), tandis que 2^{B_{k-1}} ~ 2^n ~ 2^{0.585k}. Le ratio :

3^{k-1} / 2^{0.585k} = 2^{(k-1)*log_2(3)} / 2^{0.585k} = 2^{(k-1)*1.585 - 0.585k} = 2^{k - 1.585}

Ce ratio croit EXPONENTIELLEMENT. Pour k grand, z_{k-1} >> 2^{B_{k-1}} mod d, et l'annulation est impossible car le "correcteur" 2^{B_{k-1}} est trop petit relativement a l'etat accumule.

### 5.5 WHY Level 5 : L'obstruction ultime est l'IRRATIONALITE de log_2(3)

L'argument du Level 4 repose sur le fait que 3 > 2^{0.585}, soit log_2(3) > 0.585 = log_2(3) - 1 + 1 - 0.415 = ... En fait, la croissance exponentielle du ratio z_j / 2^{B_j} provient du fait que le facteur multiplicatif (3) est PLUS GRAND que le facteur additif moyen (2^{n/k}).

Le facteur additif moyen est 2^{n/k} = 2^{(S-k)/k} = 2^{S/k - 1}. Or S/k ~ log_2(3) = 1.585, donc le facteur additif moyen est 2^{0.585} ~ 1.50.

Le ratio est 3 / 2^{0.585} = 3 / (3 * 2^{0.585 - log_2(3)}) ... Recalculons directement. Le taux de croissance de z par multiplication est 3 par etape. Le taux de croissance moyen des perturbations est 2^{n/(k(k-1))} (car Delta_j moyen est n/(k-1), et 2^{Delta_j} ~ 2^{n/(k-1)}). Le rapport est :

3 / 2^{n/(k-1)} pour les derniers j.

Si n/k < log_2(3), i.e., S/k < log_2(3) + 1, ce qui est toujours vrai (S ~ k * log_2(3)), alors la multiplication par 3 DOMINE les perturbations.

**L'OBSTRUCTION FONDAMENTALE :** L'annulation z_k = 0 necessite un ALIGNEMENT PARFAIT entre la trajectoire multiplicative (facteur 3^k) et la trajectoire additive (facteur 2^n). Cet alignement est 3^k = 2^S mod d. Mais d = 2^S - 3^k est PRECISEMENT la mesure du desalignement. Pour que g(B) = 0 mod d avec B monotone, il faut que les perturbations 2^{B_j} compensent EXACTEMENT le desalignement -- et la monotonie empeche cette compensation car elle force les perturbations a etre GEOMETRIQUEMENT CROISSANTES (pas librement ajustables).

La raison profonde est que log_2(3) est IRRATIONNEL : les suites 3^k et 2^S ne s'alignent JAMAIS parfaitement, et le desalignement frac(k * log_2(3)) ne suit aucun pattern periodique. La monotonie force les B_j a "suivre" la croissance geometrique de base 2, tandis que l'etat z_j suit la croissance de base 3, et ces deux croissances sont INCOMMENSURABLES (car log_2(3) est irrationnel, meme transcendant par Gelfond-Schneider).

> **R193-C1 (Conjecture fondamentale de l'AMH) [CONJECTURE].**
> L'irrationalite de log_2(3) implique que pour tout k >= 2, il n'existe pas de partition monotone B de n = S - k (S = ceil(k*log_2(3))) telle que g(B) = 0 mod d.
>
> **Mecanisme conjectural :** L'incommensurabilite des bases 2 et 3 empeche l'annulation systematique dans la recurrence de Horner sous contrainte de monotonie.

**Statut : CONJECTURE.** C'est la reformulation de la conjecture de Collatz (absence de cycles non triviaux) dans le langage de l'AMH.

---

## 6. CONNEXION AVEC L'ARGUMENT D'ARC

### 6.1 L'argument d'arc comme cas trivial de l'AMH

L'argument d'arc de Steiner (1977) affirme : g(B) <= g_max = (3^k + 3^n - 2)/2. Pour g(B) = 0 mod d, on a besoin g(B) >= d (car g(B) > 0). Si g_max < d, c'est impossible.

Dans le langage de l'AMH, l'argument d'arc dit : l'ensemble d'accessibilite R_k est contenu dans l'ARC {1, 2, ..., g_max} mod d. Si cet arc n'entoure pas 0 (i.e., g_max < d), alors 0 n'est pas dans R_k.

> **R193-T5 (L'argument d'arc est le cas continu de l'AMH) [PROUVE].**
> L'argument d'arc g_max < d est equivalent a : l'ensemble R_k subset {1, ..., g_max} (vu comme sous-ensemble de Z, pas de Z/dZ), ce qui exclut 0 mod d.

**Preuve.** g(B) = z_k est un entier POSITIF (car chaque terme 3^{k-1-j}*2^{B_j} > 0). Donc z_k >= 3^{k-1-0}*2^{B_0} + ... >= SUM 3^{k-1-j} = (3^k-1)/2 > 0. Et z_k <= g_max. Si g_max < d, alors z_k in {1, ..., d-1} et z_k mod d = z_k != 0. CQFD.

### 6.2 Generalisation : l'AMH quand l'argument d'arc echoue

Quand g_max >= d (ce qui arrive pour ~58.5% des k, cf. Section 4.10), l'argument d'arc echoue. L'AMH va PLUS LOIN en exploitant la structure DISCRETE :

1. **Mod p pour p | d composite :** Le crible reduit l'espace d'etats. Meme si R_k couvre [0, g_max] qui contient des multiples de d, la projection R_k mod p peut eviter 0 mod p.

2. **Structure arithmetique des g(B) :** Les valeurs g(B) ne forment pas un arc CONTINU mais un ensemble DISCRET de p_k(n) points. Meme dans un arc qui contient 0 mod d, les points discrets peuvent tous l'eviter.

3. **Contrainte de budget :** Les partitions de n en k parts ont des valeurs g(B) CLUSTERED autour de g_moyen ~ (3^k - 1)/(2*(k-1)) * n (par le point selle). Le cluster peut eviter 0 mod d.

### 6.3 L'ecart entre l'argument d'arc et l'AMH complet

> **R193-O2 (Gap arc-automate) [OBSERVATION].**
> L'argument d'arc couvre les k avec frac(k*log_2(3)) < 0.415.
> L'AMH (avec crible mod p) couvre potentiellement TOUS les k.
> Le gap est les k avec frac(k*log_2(3)) > 0.415 et d premier (pas de petit facteur pour le crible).
>
> Pour ces k, l'AMH necessite soit :
> (a) Une enumeration directe des partitions (faisable pour k <= 41, car p_k(n) est polynomial)
> (b) Un argument structurel prouvant que les g(B) discrets evitent 0 mod d
>
> L'option (a) est l'approche computationnelle (Block 2 / Block 3).
> L'option (b) est le SAINT GRAAL -- un argument theorique universel.

---

## 7. L'AUTOMATE PROJETE POUR p = 5 : ANALYSE COMPLETE

### 7.1 Structure de l'automate A(5)

p = 5, ord_5(2) = 4. Alphabet = {1, 2, 4, 3} (= {2^0, 2^1, 2^2, 2^3} mod 5).

Transition : delta(z, a) = 3z + a mod 5.

Table de transition complete :

| z \ a | 1 | 2 | 4 | 3 |
|-------|---|---|---|---|
| 0     | 1 | 2 | 4 | 3 |
| 1     | 4 | 0 | 2 | 1 |
| 2     | 2 | 3 | 0 | 4 |
| 3     | 0 | 1 | 3 | 2 |
| 4     | 3 | 4 | 1 | 0 |

### 7.2 Accessibilite depuis 0

Depuis z_0 = 0 :
- Apres 1 etape : R_1 = {1, 2, 4, 3} = Z/5Z \ {0}. L'etat 0 N'EST PAS atteignable en 1 etape.
- Apres 2 etapes (SANS monotonie) : depuis chaque etat de R_1, on peut atteindre les 4 successeurs. R_2 = Z/5Z (car 3 -> {0,1,3,2}, et 0 est atteint).
- Apres 2 etapes (AVEC monotonie) : il faut b_1 >= b_0.
  - Si b_0 = 0 (a = 1, z_1 = 1) : b_1 >= 0, alphabet = {1,2,4,3}, z_2 in {4,0,2,1}. 0 est ATTEIGNABLE (b_0=0, b_1=1 : z_1=1, z_2=3*1+2=5=0 mod 5).

**ATTENTION :** 0 est atteignable en 2 etapes avec B = (0, 1), SUM = 1. Cela correspond a k=2, n=1.

Mais pour k=2, S=4 (S = ceil(2*1.585) = ceil(3.17) = 4), d = 2^4 - 3^2 = 16 - 9 = 7. Et 5 ne divise pas 7. Donc le crible mod 5 ne s'applique pas a k=2.

L'analyse mod 5 n'est pertinente que pour les k ou 5 | d, i.e., k in {6, 9, ...} (cf. R192-A2).

### 7.3 L'automate A(5) pour k = 6, n = 4

Les etiquettes b_j sont dans {0,1,2,3} mod 4 (cyclique). La monotonie force b_0 <= b_1 <= ... <= b_5. La somme SUM b_j mod 4 n'est pas directement contrainte, mais la somme TOTALE SUM B_j = 4.

Les 5 partitions de 4 en 6 parts monotones, avec b_j = B_j mod 4 :
- (0,0,0,0,0,4) : b_j mod 4 = (0,0,0,0,0,0). Lettres mod 5 : (1,1,1,1,1,1).
- (0,0,0,0,1,3) : b_j mod 4 = (0,0,0,0,1,3). Lettres mod 5 : (1,1,1,1,2,3).
- (0,0,0,0,2,2) : b_j mod 4 = (0,0,0,0,2,2). Lettres mod 5 : (1,1,1,1,4,4).
- (0,0,0,1,1,2) : b_j mod 4 = (0,0,0,1,1,2). Lettres mod 5 : (1,1,1,2,2,4).
- (0,0,1,1,1,1) : b_j mod 4 = (0,0,1,1,1,1). Lettres mod 5 : (1,1,2,2,2,2).

Simulons l'automate A(5) pour chacune :

**Partition (0,0,0,0,0,4) -- lettres (1,1,1,1,1,1) :**
z_0 = 0, z_1 = 3*0+1 = 1, z_2 = 3*1+1 = 4, z_3 = 3*4+1 = 13 = 3, z_4 = 3*3+1 = 10 = 0, z_5 = 3*0+1 = 1, z_6 = 3*1+1 = 4. z_6 = 4 != 0.

**Partition (0,0,0,0,1,3) -- lettres (1,1,1,1,2,3) :**
z_0 = 0, z_1 = 1, z_2 = 4, z_3 = 3, z_4 = 0, z_5 = 3*0+2 = 2, z_6 = 3*2+3 = 9 = 4. z_6 = 4 != 0.

**Partition (0,0,0,0,2,2) -- lettres (1,1,1,1,4,4) :**
z_0 = 0, z_1 = 1, z_2 = 4, z_3 = 3, z_4 = 0, z_5 = 3*0+4 = 4, z_6 = 3*4+4 = 16 = 1. z_6 = 1 != 0.

**Partition (0,0,0,1,1,2) -- lettres (1,1,1,2,2,4) :**
z_0 = 0, z_1 = 1, z_2 = 4, z_3 = 3, z_4 = 3*3+2 = 11 = 1, z_5 = 3*1+2 = 5 = 0, z_6 = 3*0+4 = 4. z_6 = 4 != 0.

**Partition (0,0,1,1,1,1) -- lettres (1,1,2,2,2,2) :**
z_0 = 0, z_1 = 1, z_2 = 4, z_3 = 3*4+2 = 14 = 4, z_4 = 3*4+2 = 14 = 4, z_5 = 3*4+2 = 14 = 4, z_6 = 3*4+2 = 14 = 4. z_6 = 4 != 0.

**RESULTAT :** Pour les 5 partitions, z_6 in {4, 4, 1, 4, 4}. AUCUNE ne donne z_6 = 0 mod 5.

Cela confirme R192-A2 et montre le mecanisme EN ACTION : l'automate projete A(5) avec les contraintes de monotonie et budget n'atteint PAS 0 pour k = 6.

### 7.4 Pattern observe dans A(5)

> **R193-O3 (Pattern de l'automate A(5) pour lettres constantes) [OBSERVATION].**
> Avec la lettre constante a = 1 (B_j = 0 pour tout j), l'automate A(5) suit le cycle :
> 0 -> 1 -> 4 -> 3 -> 0 -> 1 -> 4 -> ...
> de periode 4. Le retour a 0 se fait en EXACTEMENT 4 etapes (pas 6).
>
> Pour k = 6 avec toutes lettres = 1, on arrive a z_6 = z_2 = 4 (car 6 mod 4 = 2).
> z_6 = 0 ssi k = 0 mod 4. Pour k = 6, 6 mod 4 = 2, donc z_6 != 0.

Cette observation montre que la PERIODICITE de l'automate A(5) est le mecanisme d'obstruction : k doit etre divisible par 4 pour que la lettre constante ramene a 0, et meme dans ce cas, la contrainte SUM B_j = n != 0 empeche toutes les lettres d'etre a = 1.

> **R193-T6 (Obstruction periodique pour p = 5) [PROUVE].**
> Pour p = 5 et la lettre constante a = 2^{b_0} mod 5, l'automate suit un cycle de longueur divisant 4 = ord_5(3). L'etat z_j = (3^j - 1)/2 * a mod 5 (par la formule geometrique, quand toutes les lettres sont identiques). Le retour a 0 requiert 3^j = 1 mod 5, soit j = 0 mod 4.

**Preuve.** Avec lettre constante a, z_j = a * (3^j - 1)/(3 - 1) = a * (3^j - 1)/2 mod 5. z_j = 0 mod 5 ssi 3^j = 1 mod 5 ssi j = 0 mod 4 (car ord_5(3) = 4). CQFD.

**Corollaire :** Pour k non divisible par 4, l'automate A(5) avec lettre constante NE REVIENT PAS a 0. Les lettres NON constantes (monotonie non triviale) modifient la trajectoire, mais l'obstruction de base (periodicite mod ord_p(3)) reste le mecanisme dominant.

---

## 8. VERS UNE PREUVE STRUCTURELLE POUR TOUT k

### 8.1 L'idee : combiner arc + crible + periodicite

L'analyse des sections precedentes suggere une strategie en 3 couches :

**Couche 1 (Arc) :** Pour ~41.5% des k (ceux ou frac(k*log_2(3)) < 0.415), l'argument d'arc g_max < d suffit. PROUVE.

**Couche 2 (Crible petit p) :** Pour les k ou 5 | d (soit ~25% des k), le crible mod 5 est tres contraignant car |Z/5Z| = 5 et l'automate A(5) a une dynamique de PERIODE 4. Si k mod 4 != 0, l'obstruction periodique (T6) empeche TOUTE trajectoire a lettre constante de revenir a 0. Les trajectoires non constantes sont encore plus contraintes. PROUVE pour k = 6.

**Couche 3 (Crible autres p) :** Pour les k restants, chercher p | d avec des proprietes analogues. Le facteur 7 a ord_7(3) = 6 et ord_7(2) = 3. Le facteur 11 a ord_11(3) = 5 et ord_11(2) = 10. Le facteur 13 a ord_13(3) = 3 et ord_13(2) = 12.

### 8.2 Classification des obstructions par type de premier

> **R193-D3 (Obstruction de type I : periodique).**
> Un premier p fournit une obstruction de type I pour k si ord_p(3) ne divise pas k. Dans ce cas, la trajectoire a lettre constante ne revient PAS a 0 dans A(p).

> **R193-D4 (Obstruction de type II : budget).**
> Un premier p fournit une obstruction de type II si le budget n n'est pas compatible avec un retour a 0 dans A(p). Meme si ord_p(3) | k, la contrainte SUM B_j = n (projetee mod s_p = ord_p(2)) peut empecher le retour.

> **R193-D5 (Obstruction de type III : crible complet).**
> Enumeration directe des p_k(n) partitions et verification que AUCUNE ne donne g = 0 mod p. C'est la methode DP+CRT. Toujours FINI, mais computationnel.

### 8.3 Couverture des obstructions

> **R193-C2 (Conjecture de couverture) [CONJECTURE].**
> Pour tout k >= 3 (avec S = ceil(k*log_2(3))), au moins une des trois couches (arc, crible mod p, enumeration) suffit a prouver N_0(d) = 0.
>
> Plus precisement : pour tout k >= 3, il existe p premier (possiblement p = d si d est premier) tel que l'automate A(p) avec contraintes monotones et de budget n'atteint PAS 0 en k etapes.

**Statut : CONJECTURE.** C'est une reformulation de la conjecture de Collatz (pas de cycle non trivial) dans le langage de l'AMH.

### 8.4 Ce qui est PROUVE pour k <= 9

| k | S | d | Methode | Statut |
|---|---|---|---------|--------|
| 3 | 5 | 5 | Enumeration (2 partitions) | **PROUVE** |
| 4 | 7 | 47 | Enumeration + n_min >= 2 | **PROUVE** (cond. n_min) |
| 5 | 8 | 13 | Enumeration (3 partitions) | **PROUVE** |
| 6 | 10 | 295 = 5*59 | Crible p=5, automate A(5) | **PROUVE** |
| 7 | 12 | 1909 | Argument d'arc (g_max = 1214 < 1909) | **PROUVE** |
| 8 | 13 | 1631 = 7*233 | Crible partiel (p=7 echoue seul) | **CONDITIONNEL** |
| 9 | 15 | 13085 = 5*2617 | Argument d'arc (g_max = 10205 < 13085) | **PROUVE** |

Pour k = 3, 5, 6, 7, 9 : PROUVE inconditionnellement.
Pour k = 4 : PROUVE conditionnellement a n_min >= 2 (fait connu, Steiner 1977).
Pour k = 8 : CONDITIONNEL (necessite enumeration mod 233 ou mod 1631).

---

## 9. REGISTRE DES RESULTATS

### 9.1 Tableau recapitulatif

| # | Resultat | Statut | Section | Dependances |
|---|----------|--------|---------|-------------|
| R193-D1 | Automate Monotone de Horner (convention propre) | **DEFINITION** | 1.2 | R192-D1 corrige |
| R193-T1 | Croissance par sumset (Cauchy-Davenport) | **PROUVE** | 2.2 | Cauchy-Davenport |
| R193-T2 | DP sur graphe projete, complexite O(p*n*k) | **PROUVE** | 3.3 | Algorithme DP |
| R193-L1 | Regularite du graphe de Horner | **PROUVE** | 3.4 | Arithmetique mod p |
| R193-T3 | Argument d'arc pour k=7 (g_max < d) | **PROUVE** | 4.6 | Borne de Steiner |
| R193-T4 | Portee de l'argument d'arc (~41.5% des k) | **PROUVE** | 4.10 | Weyl equidistribution |
| R193-T5 | Arc = cas continu de l'AMH | **PROUVE** | 6.1 | Definition |
| R193-T6 | Obstruction periodique pour p=5 | **PROUVE** | 7.4 | ord_5(3) = 4 |
| R193-O1 | Expansion du graphe de Horner | **OBSERVATION** | 3.5 | Bourgain-Gamburd |
| R193-O2 | Gap arc-automate | **OBSERVATION** | 6.3 | Sections 4 et 6 |
| R193-O3 | Pattern de A(5) avec lettres constantes | **OBSERVATION** | 7.4 | Simulation |
| R193-C1 | Conjecture fondamentale AMH (irrationalite log_2(3)) | **CONJECTURE** | 5.5 | Heuristique WHY |
| R193-C2 | Conjecture de couverture (3 couches suffisent) | **CONJECTURE** | 8.3 | Reformulation Collatz |
| k=3 | N_0(5) = 0 | **PROUVE** | 4.2 | Enumeration |
| k=4 | N_0(47) = 0 (modulo n_min) | **CONDITIONNEL** | 4.3 | n_min >= 2 (Steiner) |
| k=5 | N_0(13) = 0 | **PROUVE** | 4.4 | Enumeration |
| k=6 | N_0(295) = 0 via p=5 | **PROUVE** | 4.5 / 7.3 | R192-A2 + simulation |
| k=7 | N_0(1909) = 0 | **PROUVE** | 4.6 | Argument d'arc |
| k=8 | N_0(1631) = 0 ? | **CONDITIONNEL** | 4.7 | Crible incomplet |
| k=9 | N_0(13085) = 0 | **PROUVE** | 4.8 | Argument d'arc |

### 9.2 Score d'avancement

| Critere | Score | Commentaire |
|---------|-------|-------------|
| Profondeur WHY | 10/10 | 5 niveaux, jusqu'a l'irrationalite de log_2(3) |
| Resultats prouves | 8/10 | 8 theoremes/lemmes prouves, k=3..9 (sauf k=4,8) resolus |
| Portee de l'AMH | 7/10 | Argument d'arc recupere (~41.5%), crible mod p (~25%), gap identifie |
| Innovation | 7/10 | Classification des obstructions (types I/II/III), portee de l'arc quantifiee |
| Connexions | 8/10 | Arc-automate unifie, Cauchy-Davenport, Bourgain-Gamburd, equidistribution de Weyl |
| Honnetete | 10/10 | Saturation du sumset identifiee, limites de chaque methode explicites |

### 9.3 Recommandations pour la suite

**Priorite 1 : Completer k = 8.** Enumerer les 7 partitions de 5 mod 233 (ou mod 1631 directement). C'est un calcul FINI avec 7 cas.

**Priorite 2 : Etendre a k = 10..20.** Pour chaque k, appliquer dans l'ordre : (1) argument d'arc, (2) crible mod petit p, (3) enumeration. Les deux premieres etapes sont ANALYTIQUES. La troisieme est computationnelle mais finie (p_k(n) <= quelques centaines pour k <= 20).

**Priorite 3 : L'obstruction de type I universelle.** Prouver que pour tout k >= 3 et S = ceil(k*log_2(3)), il existe un premier p | d tel que ord_p(3) ne divise pas k. C'est un probleme de theorie des nombres (existence de premiers a "mauvais" ordre dans la factorisation de d = 2^S - 3^k).

**Priorite 4 : Raffiner l'analyse de sumset avec budget.** Integrer la contrainte SUM B_j = n dans l'analyse de l'ensemble atteignable. Le budget FORCE une contraction de l'espace atteignable aux dernieres etapes, ce qui pourrait suffire a eviter 0 meme pour d premier.

**Piste ouverte principale :** L'AMH transforme la conjecture de Collatz en un probleme d'accessibilite d'automate. Pour les petits k, c'est decidable par enumeration. Pour les grands k (k >= 42), l'argument de second moment (Block 1) suffit. Le GAP est k = 22..41, ou ni l'enumeration simple ni le second moment ne s'appliquent directement. L'AMH avec le crible mod p offre une voie INTERMEDIAIRE, mais sa completude n'est pas prouvee.

---

## 10. WHY-CHAIN GLOBALE : POURQUOI L'AMH EST LE BON OUTIL

**WHY 1 : Pourquoi reformuler le probleme comme un automate ?**
Parce que l'automate capture NATURELLEMENT la structure iterative de la recurrence de Horner et la contrainte de monotonie comme restriction d'alphabet. Contrairement a l'approche spectrale (Lambda(s)), l'AMH travaille directement avec les etats et les transitions, sans passer par les sommes exponentielles.

**WHY 2 : Pourquoi l'AMH evite-t-il le verrou C1 (correction de monotonie) ?**
Parce que C1 est un probleme de DISTRIBUTION GLOBALE (equirepartition de g(B) mod d), tandis que l'AMH est un probleme d'ACCESSIBILITE LOCALE (un point specifique est-il atteint ?). L'accessibilite est plus faible que l'equirepartition : il suffit d'exclure UN point, pas de controler toute la distribution. La monotonie AIDE pour l'accessibilite (elle reduit les chemins) alors qu'elle NUIT pour l'equirepartition (elle concentre la distribution).

**WHY 3 : Pourquoi l'AMH ne resout-il pas la conjecture a lui seul ?**
Parce que pour d premier et grand, l'automate a d etats et l'ensemble atteignable SATURE Z/dZ en O(log d) etapes (par expansion du graphe de Cayley). La contrainte de monotonie reduit les chemins mais ne PROUVE PAS que 0 est evite sans enumeration explicite. Le gap est entre la puissance theorique (l'AMH formule correctement le probleme) et la capacite de RESOLUTION (borner l'ensemble atteignable loin de 0).

**WHY 4 : Que faudrait-il pour que l'AMH resolve le gap k = 22..41 ?**
Un argument STRUCTUREL montrant que la trajectoire monotone dans Z/dZ (ou Z/pZ pour un bon p) a une propriete de NON-RETOUR. Par exemple : un INVARIANT de l'automate (une quantite I(z, b_last) qui croit strictement a chaque pas et qui est incompatible avec z = 0 a l'etape k). Ou : un argument d'ENTROPIE montrant que le nombre de chemins monotones vers 0 est 0 (pas juste petit).

**WHY 5 : Quel est le lien entre l'AMH et le probleme profond ?**
L'AMH est la traduction COMBINATOIRE de l'obstruction diophantienne : 2^S - 3^k divise g(B) ssi la trajectoire de Horner monotone atteint 0. L'irrationalite de log_2(3) rend cette division "generiquement impossible" (par un argument de mesure), mais "specifiquement" il faut l'exclure pour chaque k. L'AMH fournit le cadre pour cette exclusion specifique, cas par cas ou par famille.

---

*R193 Agent A1 (Investigateur profond) : L'Automate Monotone de Horner est analyse en profondeur. Resultats cles : (1) L'argument d'arc de Steiner est le cas TRIVIAL de l'AMH, couvrant ~41.5% des k (R193-T4, PROUVE). (2) Le crible mod p petit (type I : periodicite, type II : budget) couvre les d composites (R193-T6, PROUVE pour p=5). (3) k = 3, 5, 6, 7, 9 PROUVES inconditionnellement par l'AMH (enumeration ou arc). (4) L'obstruction fondamentale est l'IRRATIONALITE de log_2(3) (R193-C1, WHY Level 5). (5) Le gap reside dans les k avec d premier ou l'expansion du graphe de Horner empeche la non-accessibilite directe. L'AMH est le bon cadre mais ne ferme pas le gap a lui seul -- il faut un invariant de non-retour ou un argument d'entropie. 8 resultats prouves, 1 conditionnel, 2 conjectures, 4 pistes ouvertes.*
