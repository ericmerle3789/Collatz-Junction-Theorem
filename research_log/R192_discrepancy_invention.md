# R192 -- Agent A3 (Innovateur) : Invention d'outils pour borner la discrepance de g(B) mod d
**Date :** 16 mars 2026
**Mode :** INVENTION PURE -- raisonnement mathematique, zero calcul
**Prerequis :** R189 (operateurs, Lambda(s), gap 1.35x), R190 (saddle point, close gap, red team), R191 (Lambda_free factorise PROUVE, correction monotonie = gap, sum-product BKT, compensations orbitales)
**Mission :** INVENTER un outil pour borner la discrepance de g(B) mod d pour B monotone.

---

## RESUME EXECUTIF

R191 a identifie le verrou central : la monotonie concentre les phases et cree un gap de ~2^{0.585k} qui empeche les bornes individuelles sur |Lambda(s)| de conclure. Les trois approches de R191 (Lambda_free + correction, BKT, compensations orbitales) convergent vers le MEME obstacle : la correction de monotonie (Conjecture C1).

Ce document INVENTE cinq outils nouveaux, dont deux sont veritablement originaux. L'outil le plus prometteur est le **Horner Automaton Reachability** (Approche 1), qui reformule le probleme comme un probleme d'accessibilite dans un automate sur Z/dZ et exploite la monotonie comme une RESTRICTION d'alphabet qui AIDE (au lieu de nuire). Le second outil cle est le **Carry Propagation Barrier** (Approche 3), qui exploite la structure binaire des carries dans la somme g(B) pour creer une obstruction arithmetique a g(B) = 0 mod d.

**Bilan :** 2 PROUVES, 3 CONDITIONNELS, 2 CONJECTURES, 3 PISTES OUVERTES.

---

## 1. APPROCHE 1 : L'AUTOMATE MONOTONE DE HORNER

### 1.1 La reformulation iterative

La structure de Horner de g(B) est la suivante. Definissons la recurrence :

> z_0 = 1
> z_{j+1} = 3 * z_j + 2^{B_j} mod d
> g(B) = z_k mod d (a verifier)

**Verification :** z_1 = 3 + 2^{B_0}. z_2 = 3(3 + 2^{B_0}) + 2^{B_1} = 9 + 3*2^{B_0} + 2^{B_1}. z_3 = 27 + 9*2^{B_0} + 3*2^{B_1} + 2^{B_2} = 3^3 + 3^2*2^{B_0} + 3^1*2^{B_1} + 3^0*2^{B_2}.

En general : z_k = 3^k + SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} = 3^k + g(B).

Donc **g(B) = z_k - 3^k mod d**. Et g(B) = 0 mod d ssi z_k = 3^k mod d.

Or 3^k = 2^S mod d (identite fondamentale). Donc :

> **g(B) = 0 mod d ssi z_k = 2^S mod d**

### 1.2 L'automate A(k, d)

**DEFINITION R192-D1 (Automate de Horner).**
L'automate A(k, d) est defini par :
- **Etats :** Z/dZ
- **Etat initial :** z_0 = 1
- **Alphabet :** A = {2^0, 2^1, 2^2, ...} = <2> dans Z/dZ (toutes les puissances de 2 mod d)
- **Transition :** delta(z, 2^b) = 3z + 2^b mod d
- **Etat cible (interdit) :** z_target = 2^S mod d = 3^k mod d

Un mot w = (2^{B_0}, 2^{B_1}, ..., 2^{B_{k-1}}) de longueur k sur l'alphabet A mene de z_0 = 1 a z_k = z_target ssi g(B) = 0 mod d.

### 1.3 La contrainte de monotonie comme restriction d'alphabet

La monotonie B_0 <= B_1 <= ... <= B_{k-1} signifie que le symbole lu a l'etape j+1 est au moins aussi grand (en exposant) que celui lu a l'etape j.

**DEFINITION R192-D2 (Automate monotone).**
L'automate MONOTONE A_mono(k, d) est l'automate A(k, d) ou l'alphabet disponible a l'etape j est :

> A_j = {2^b : b >= B_{j-1}} (les puissances de 2 au moins aussi grandes que la precedente)

Autrement dit, l'alphabet est RESTREINT et CROISSANT au fil du temps.

### 1.4 L'ensemble d'accessibilite R_j

**DEFINITION R192-D3.** L'ensemble d'accessibilite monotone a l'etape j est :

> R_0 = {1}
> R_j = {3z + 2^b mod d : z in R_{j-1}(b_prev), b >= b_prev} (ou b_prev est l'exposant utilise a l'etape j-1)

Plus precisement, on doit tracker l'etat ET le dernier exposant utilise. Definissons :

> R_j subset Z/dZ x Z_{>=0} (paires (etat, dernier exposant))
> R_0 = {(1, 0)} (etat initial, exposant minimum 0)
> R_{j+1} = {(3z + 2^b mod d, b) : (z, b_prev) in R_j, b >= b_prev, SUM contraintes}

L'ensemble d'accessibilite FINAL est R_k = {z : (z, b) in R_k pour un b}. La question est :

> **2^S mod d est-il dans R_k ?**

### 1.5 WHY chain : pourquoi la monotonie AIDE dans cette formulation

**WHY 1 : Pourquoi la restriction d'alphabet aide-t-elle ?**
Parce que chaque restriction b >= b_prev ELIMINE des transitions. L'ensemble R_j monotone est un SOUS-ENSEMBLE de l'ensemble R_j libre (sans monotonie). Moins de transitions = moins d'etats accessibles = plus de chance d'eviter la cible.

**WHY 2 : Pourquoi est-ce different de la formulation Lambda(s) ou la monotonie NUIT ?**
Parce que dans Lambda(s), on essaie de montrer ANNULATION (les phases se compensent). La monotonie concentre les phases et REDUIT l'annulation. Mais ici, on essaie de montrer NON-ACCESSIBILITE (l'etat cible n'est jamais atteint). La monotonie RESTREINT les chemins et AUGMENTE la non-accessibilite.

**C'est un CHANGEMENT DE PARADIGME.** Au lieu de prouver que les valeurs g(B) sont bien reparties (approche spectrale), on prouve qu'elles EVITENT un point specifique (approche d'accessibilite).

**WHY 3 : Pourquoi ce paradigme est-il potentiellement plus puissant ?**
Parce que l'evitement d'un point est une propriete LOCALE (il suffit qu'un voisinage de 2^S soit evite), tandis que l'equirepartition est GLOBALE (il faut controler la distribution sur tout Z/dZ). La monotonie cree une structure LOCALE dans les transitions qui peut exclure certains voisinages.

**WHY 4 : Comment quantifier l'avantage de la monotonie ?**
A l'etape j, si le dernier exposant utilise est b_prev, l'alphabet est {2^b : b >= b_prev}. Le nombre de symboles disponibles est n - (somme des precedents) + 1 (par la contrainte de somme). Pour les premieres etapes (b_prev petit), l'alphabet est large. Pour les dernieres etapes (b_prev grand), l'alphabet est ETROIT. Cette contraction progressive de l'alphabet force R_j a RETRECIR.

**WHY 5 : Peut-on borner |R_j| ?**
OUI, c'est l'objet du theoreme suivant.

### 1.6 Borne sur l'ensemble d'accessibilite

**ENONCE (R192-T1 : Contraction de l'ensemble d'accessibilite) [CONDITIONNEL].**

Supposons d premier et ord_d(3) >= k. Definissons :

> r_j = |{z : (z, b) in R_j pour un b}| (taille de la projection sur Z/dZ)

Alors :

> r_0 = 1
> r_1 <= n + 1 (au plus n+1 choix pour B_0 in {0, ..., n})
> r_j <= min(r_{j-1} * (n - j + 2), d) (borne multiplicative grossiere)

Mais la borne UTILE vient de la MULTIPLICATION par 3. La transition z -> 3z + 2^b est une application AFFINE de Z/dZ dans Z/dZ. Pour b fixe, c'est une bijection (car 3 est inversible mod d). Donc l'image de R_{j-1} sous z -> 3z + 2^b est une TRANSLATION de 3 * R_{j-1}, de taille exactement |R_{j-1}|.

L'union sur b >= b_prev donne :

> R_j subset UNION_{b >= b_prev} (3 * R_{j-1} + 2^b)

Si les translations 3*R_{j-1} + 2^b sont DISJOINTES (pour des b differents), alors |R_j| = |R_{j-1}| * (nombre de b valides). Si elles se CHEVAUCHENT, |R_j| < produit.

**Condition de chevauchement :** 3*R_{j-1} + 2^b et 3*R_{j-1} + 2^{b'} se chevauchent ssi 2^b - 2^{b'} in (3*R_{j-1} - 3*R_{j-1}) = 3*(R_{j-1} - R_{j-1}), ou R - R est l'ensemble des differences.

Si |R_{j-1}| est grand (> sqrt(d)), alors R_{j-1} - R_{j-1} couvre une proportion significative de Z/dZ, et les translations chevauchent beaucoup. L'ensemble R_j SATURE a ~d.

Si |R_{j-1}| est petit (< sqrt(d)), les translations sont presque disjointes, et R_j croit multiplicativement.

**Le point critique :** La croissance s'arrete quand |R_j| ~ d (saturation). Mais pour eviter 2^S, on a besoin que |R_k| < d, ce qui signifie que la saturation ne doit PAS se produire en k etapes.

Pour k < 42, n ~ 0.585k ~ 24, et le nombre total de pas est k ~ 41. La croissance est au plus multiplicative avec facteur ~ n/k ~ 0.585 par etape en moyenne (car le budget se repartit). Donc |R_k| <= (0.585)^k * constante^k, ce qui ne sature PAS d pour k < 42 (car 0.585^k * C^k << d ~ 3^k pour C modere).

**ATTENTION :** Cette borne est TRES grossiere. Le comportement reel depend de la structure arithmetique des transitions.

**Statut : CONDITIONNEL** (la borne multiplicative est heuristique ; la non-saturation necessite un argument rigoureux sur la structure des ensembles R_j).

### 1.7 La structure de l'automate et le sous-groupe <3>

**ENONCE (R192-T2 : Action de <3> sur l'automate) [PROUVE].**

La transition z -> 3z + 2^b est equivalente a : 3(z + 2^b * 3^{-1}). Donc la transition est une MULTIPLICATION par 3 suivie d'une TRANSLATION.

Apres k etapes sans les 2^{B_j} (i.e., tous les B_j = 0, donc 2^{B_j} = 1), on aurait z_k = 3^k + (3^{k-1} + ... + 1) = 3^k + (3^k - 1)/2 = (3^{k+1} - 1)/2.

L'etat cible est z_target = 2^S = 3^k + d = 3^k + 2^S - 3^k = 2^S mod d. Par l'identite fondamentale, z_target = 3^k mod d.

Donc **la cible est EXACTEMENT 3^k mod d**, qui est un element du sous-groupe <3>.

La trajectoire dans l'automate part de 1 (element neutre de <3>) et evolue par multiplications par 3 et additions de puissances de 2. La question est : cette trajectoire atteint-elle l'element 3^k de <3> ?

**Observation structurelle :** La trajectoire "ideale" (sans les 2^{B_j}) serait z_j = (3^{j+1} - 1)/2. Elle atteint z_k = (3^{k+1} - 1)/2 != 3^k (sauf pour k = 1). Les termes 2^{B_j} ajoutent des PERTURBATIONS qui devient la trajectoire de ce chemin "naturel" dans <3>.

La question devient : **les perturbations 2^{B_j} peuvent-elles devier la trajectoire exactement vers 3^k ?**

**Preuve :** Calcul direct de la recurrence. CQFD.

### 1.8 L'invention : le Critere de Non-Accessibilite par Congruence Locale (NACL)

**DEFINITION R192-D4 (Critere NACL).**
Pour un facteur premier p | d, definissons l'automate projete A_p par reduction mod p :
- Etats : Z/pZ
- Transition : delta_p(z, 2^b) = 3z + 2^b mod p
- Cible : 3^k mod p

Si l'ensemble d'accessibilite R_k mod p N'ATTEINT PAS 3^k mod p, alors g(B) != 0 mod d pour toute partition monotone B.

**THEOREME R192-T3 (NACL) [PROUVE].**
Si d a un facteur premier p tel que, pour l'automate projete A_p, l'ensemble R_k(p) ne contient pas 3^k mod p, alors N_cycle = 0 pour le type (k, S).

**Preuve :** Si g(B) = 0 mod d, alors g(B) = 0 mod p. Or g(B) = z_k - 3^k, donc z_k = 3^k mod p. Mais z_k mod p est dans R_k(p), et 3^k mod p n'est pas dans R_k(p). Contradiction. CQFD.

**WHY chain :**

**WHY 1 : Pourquoi projeter sur un petit premier aide-t-il ?**
Parce que dans Z/pZ, l'ensemble d'accessibilite R_k(p) a au plus p elements. Si R_k(p) est STRICTEMENT inclus dans Z/pZ, il y a des "trous". Si 3^k mod p est un tel trou, on conclut.

**WHY 2 : Quand R_k(p) est-il strictement inclus dans Z/pZ ?**
Quand k * log(alphabet_size) < log(p), approximativement. Pour p ~ sqrt(d) et l'alphabet de taille ~ n ~ 0.585k, on a k * log(n) ~ k * log(k) << log(sqrt(d)) ~ 0.8k * log 2. Pour k modere, la croissance de l'automate ne sature pas Z/pZ.

**WHY 3 : Pourquoi la cible 3^k mod p serait-elle un trou ?**
Parce que l'automate est biaise : il part de 1 et fait des multiplications par 3 + translations par puissances de 2. La trajectoire reste "pres" du sous-groupe <3> (perturbee par <2>). La cible 3^k est dans <3>, mais le chemin pour l'atteindre est contraint par la monotonie des B_j. Les perturbations monotones CROISSANTES creent un biais ASYMETRIQUE : les premieres perturbations sont petites (2^0 = 1), les dernieres sont grandes (2^n). Ce biais peut rendre 3^k inaccessible.

**WHY 4 : Le critere NACL est-il effectif ?**
OUI pour d compose avec un petit facteur premier p. Pour d premier, NACL ne s'applique qu'avec p = d, auquel cas R_k(d) est exactement R_k et le critere est equivalent au probleme original.

**WHY 5 : Comment NACL se combine-t-il avec les approches existantes ?**
NACL est un CRIBLE : pour chaque petit premier p | d, on filtre. Si au moins un p bloque, c'est fini. Pour les d premiers, NACL est inutilisable directement, mais il SUGGERE une approche modulaire : travailler modulo des entiers auxiliaires m tels que la congruence de l'automate sur Z/mZ donne des informations.

**Statut : PROUVE** (T3). **OUVERT** (effectivite pour d premier).

---

## 2. APPROCHE 2 : DISCREPANCE PAR ERDOS-TURAN ET DECOUPLAGE

### 2.1 La circularite et comment la briser

R191 a identifie la circularite : l'inegalite d'Erdos-Turan pour la discrepance fait intervenir |Lambda(s)|, qu'on ne sait pas borner a cause de la monotonie.

**L'invention :** Au lieu d'appliquer Erdos-Turan a la distribution de g(B) mod d directement, appliquer Erdos-Turan a la distribution de **h(Delta) mod d**, ou Delta = (Delta_1, ..., Delta_{k-1}) est le vecteur des INCREMENTS (Rappel de R191-T3 : g(B) = 2^{B_0} * h(Delta), h ne depend que des increments).

Les increments Delta_j = B_j - B_{j-1} >= 0 sont des entiers NON-NEGATIFS avec SUM Delta_j = B_{k-1} - B_0 <= n. La contrainte de monotonie est AUTOMATIQUEMENT satisfaite dans le monde des increments (toute suite de Delta >= 0 est valide).

### 2.2 Le decouplage partiel dans l'espace des increments

**ENONCE (R192-T4 : Factorisation partielle dans l'espace des increments) [CONDITIONNEL].**

Definissons :
- B_0 = b (le point de depart)
- Delta_j = B_j - B_{j-1} >= 0 pour j = 1, ..., k-1
- Contrainte : b + SUM_{j=1}^{k-1} j * Delta_j ... Non, la contrainte est SUM B_j = n, soit kb + SUM_{j=1}^{k-1} (k-j) * Delta_j = n.

Hmm, la contrainte est plus complexe que prevu. Ecrivons B_j = b + SUM_{l=1}^{j} Delta_l. Alors SUM_{j=0}^{k-1} B_j = kb + SUM_{j=1}^{k-1} (k-j) * Delta_j = n.

Les Delta_j sont COUPLES par cette contrainte de somme ponderee. Ce n'est pas une simple contrainte de somme -- les poids (k-j) decroissent.

**Neanmoins,** g(B) dans les variables (b, Delta_1, ..., Delta_{k-1}) s'ecrit :

g(B) = SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{b + SUM_{l=1}^{j} Delta_l}
     = 2^b * SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{SUM_{l=1}^{j} Delta_l}
     = 2^b * h(Delta)

ou h(Delta) = SUM_{j=0}^{k-1} 3^{k-1-j} * PROD_{l=1}^{j} 2^{Delta_l}.

La condition g(B) = 0 mod d equivaut a h(Delta) = 0 mod d (car gcd(2^b, d) = 1).

**Le gain partiel :** La variable b est ELIMINEE. On travaille avec k-1 increments Delta_j >= 0 sous la contrainte SUM (k-j) * Delta_j = n - kb.

Le parametre b est libre (0 <= b <= n/k), et pour chaque b fixe, les Delta_j vivent dans un simplexe PONDERE.

**Statut : CONDITIONNEL** (la factorisation est exacte, mais l'utilisation de la structure du simplexe pondere pour Erdos-Turan reste a developper).

### 2.3 WHY chain : avantage de l'espace des increments

**WHY 1 : Pourquoi passer aux increments ?**
Parce que la monotonie devient TRIVIALE (Delta >= 0 est automatique), et la variable B_0 s'elimine. On reduit la dimension de k a k-1 et on supprime la contrainte d'ordre.

**WHY 2 : Pourquoi la contrainte ponderee est-elle un probleme ?**
Parce que les poids (k-j) couplent les Delta_j de facon NON-UNIFORME. Les "grands" increments (j petit, poids k-j grand) sont plus contraints que les "petits" (j grand, poids 1). Cette non-uniformite empeche la factorisation directe.

**WHY 3 : Peut-on neanmoins appliquer Erdos-Turan dans cet espace ?**
OUI, via la methode de Cauchy. Lambda_h(s) = SUM_{Delta : contrainte} omega^{s * c * h(Delta)} est le coefficient de q^{n-kb} dans une fonction generatrice PONDEREE. Les poids differents pour chaque Delta_j empechent la factorisation directe, MAIS on peut utiliser un changement de variable : poser sigma_j = SUM_{l=1}^j Delta_l (les sommes partielles). Alors sigma_0 = 0, sigma_j >= sigma_{j-1}, et :

h = SUM 3^{k-1-j} * 2^{sigma_j}

Les sigma_j forment une suite CROISSANTE. La contrainte SUM (k-j) Delta_j = SUM_{j=1}^{k-1} (sigma_j - sigma_{j-1}) * (k-j) = SUM sigma_j * [(k-j) - (k-j-1)] + ... C'est un changement de variables lineaire (sommation par parties).

**WHY 4 : Que donne la sommation par parties ?**
SUM_{j=1}^{k-1} (k-j)(sigma_j - sigma_{j-1}) = SUM_{j=1}^{k-1} sigma_j * 1 = SUM_{j=1}^{k-1} sigma_j (par Abel / sommation par parties, car le coefficient de sigma_j dans le telescopage est 1).

Donc la contrainte est : **SUM_{j=1}^{k-1} sigma_j = n - kb**, avec 0 = sigma_0 <= sigma_1 <= ... <= sigma_{k-1}.

C'est une PARTITION monotone de (n - kb) en (k-1) parts ! On est revenu a un probleme de partitions, mais en dimension k-1 au lieu de k, et avec h(sigma) = SUM 3^{k-1-j} * 2^{sigma_j}.

**WHY 5 : Avons-nous gagne quelque chose ?**
Oui et non. On a reduit la dimension de 1 (k -> k-1) et elimine B_0. Mais la STRUCTURE du probleme est la meme. Le gain est MARGINAL pour cette approche. Le vrai gain serait de CASSER la structure de partition, ce que l'espace des increments ne fait pas.

**Statut : OBSERVATION** (gain marginal, pas de percee).

---

## 3. APPROCHE 3 : BARRIERE DE PROPAGATION DE RETENUES (CARRY PROPAGATION BARRIER)

### 3.1 L'idee maitresse

g(B) = SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}. Quand on ecrit cette somme en base 2, chaque terme 3^{k-1-j} * 2^{B_j} est le nombre 3^{k-1-j} DECALE de B_j positions vers la gauche (en binaire).

La representation binaire de 3^m est un nombre de ~m * log_2(3) ~ 1.585m bits. Les termes se CHEVAUCHENT en position binaire grace aux decalages B_j.

La condition g(B) = 0 mod d = 2^S - 3^k signifie que g(B) est un MULTIPLE de 2^S - 3^k. Or 2^S - 3^k en binaire est un nombre de S bits avec une structure specifique (1 suivi de S-1 bits determines par 3^k).

### 3.2 La structure binaire des retenues

**DEFINITION R192-D5 (Profil de retenue).**
Pour une partition B, le profil de retenue C(l) a la position binaire l (l = 0, 1, 2, ...) est defini recursivement :
- Soit s(l) = SUM_{j : B_j <= l} bit_{l - B_j}(3^{k-1-j}) (la somme des bits entrants a la position l)
- C(l+1) = floor((s(l) + C(l)) / 2) (retenue sortante)
- Le bit de g(B) a la position l est (s(l) + C(l)) mod 2

avec C(0) = 0.

**ENONCE (R192-T5 : Contrainte de retenue pour g = 0 mod d) [PROUVE].**

g(B) = m * d pour un entier m >= 1 ssi :
- g(B) en binaire s'ecrit comme m * (2^S - 3^k) en binaire
- Les retenues a CHAQUE position binaire doivent etre COHERENTES

Cela impose un SYSTEME de contraintes sur les bits entrants a chaque position, qui depend de l'arrangement des B_j.

**Preuve :** Definition de la multiplication binaire. Tautologique.

### 3.3 L'exploitation de la monotonie dans les retenues

**OBSERVATION R192-O1 (Monotonie et retenues) [OBSERVATION CLE].**

La monotonie B_0 <= B_1 <= ... <= B_{k-1} signifie que les termes 3^{k-1-j} * 2^{B_j} sont decales PROGRESSIVEMENT vers la gauche. Le terme j = 0 (coefficient 3^{k-1}, le plus grand) est decale le MOINS (B_0 est le plus petit). Le terme j = k-1 (coefficient 1, le plus petit) est decale le PLUS (B_{k-1} est le plus grand).

**Consequence cruciale :** Les retenues se propagent de DROITE a GAUCHE (des bits de poids faible vers les bits de poids fort). Le terme le plus a droite (le moins decale, j = 0) a le coefficient le plus grand (3^{k-1}). Cela signifie que les retenues DEBUTENT dans une zone de forte activite (beaucoup de bits du grand coefficient 3^{k-1}) et se propagent vers une zone de faible activite (le petit coefficient 3^0 = 1, tres decale vers la gauche).

**L'hypothese de barriere :** Si les retenues initiees par 3^{k-1} aux positions basses (pres de B_0) sont TROP GRANDES pour etre absorbees par les termes suivants (qui sont plus petits en coefficient mais plus decales), alors il y a une INCOMPATIBILITE entre les retenues et la condition g = m * d.

### 3.4 Formalisation : la barriere de retenue basse

**ENONCE (R192-T6 : Barriere de retenue) [CONJECTURE].**

Pour que g(B) = m * (2^S - 3^k) avec m >= 1, les retenues C(l) aux positions l = B_0, B_0+1, ..., B_0 + ceil(k * log_2 3) doivent satisfaire un systeme de congruences qui est INCOMPATIBLE avec la monotonie pour k < k_0.

**Argument heuristique :** Le terme 3^{k-1} * 2^{B_0} contribue ~1.585(k-1) bits a partir de la position B_0. Le nombre d = 2^S - 3^k a une representation binaire ou les S premiers bits sont determines. Pour que g(B) soit un multiple de d, les ~1.585k bits bas de g(B) doivent correspondre a m * (-3^k) mod 2^S, ce qui impose une structure RIGIDE sur les retenues.

La monotonie force les termes suivants (j = 1, 2, ...) a etre decales d'au moins B_0 aussi. Donc les ~B_0 bits les plus bas de g(B) sont determines UNIQUEMENT par le bit de poids faible de 3^{k-1}, ce qui est 1 (car 3^m est toujours impair). Donc le bit B_0 de g(B) est 1.

Pour que g(B) = m * d, le bit B_0 de m * d doit etre 1. Or d = 2^S - 3^k est impair (2^S est pair pour S >= 1, 3^k est impair, leur difference est impair). Donc m * d a le meme bit 0 que m. Donc le bit B_0 de m * d est le bit B_0 de m * un_nombre_impair, ce qui depend de m.

**C'est moins contraint que je l'esperais.** La barriere de retenue fonctionne potentiellement pour les bits INTERMEDIAIRES (pas les bits extremes).

### 3.5 WHY chain : la propagation de retenue comme outil

**WHY 1 : Pourquoi les retenues sont-elles un outil prometteur ?**
Parce qu'elles encodent des CONTRAINTES LOCALES sur la structure binaire de g(B), et la monotonie impose des RELATIONS entre ces contraintes locales (les termes arrivent dans un ordre specifique).

**WHY 2 : Pourquoi l'approche directe (tous les bits) est-elle difficile ?**
Parce que le systeme de retenues a ~S variables (une par position binaire) et est globalement COUPLE (chaque retenue depend de la precedente). C'est un systeme dynamique a une dimension (la retenue entrante), pas un systeme combinatoire simple.

**WHY 3 : Peut-on exploiter la dynamique unidimensionnelle ?**
OUI. La retenue C(l) est un entier entre 0 et k-1 (au plus k termes contribuent a chaque position). La dynamique C(l) -> C(l+1) est determinee par les bits entrants a la position l et par C(l). C'est un AUTOMATE A ETATS FINIS (etats = {0, 1, ..., k-1}).

**WHY 4 : Quel est le lien avec l'automate de Horner (Approche 1) ?**
L'automate de Horner travaille dans Z/dZ (d etats). L'automate de retenue travaille dans {0, ..., k-1} (k etats). L'automate de retenue est PLUS PETIT et potentiellement plus maniable. Mais il capture une information DIFFERENTE (structure binaire locale vs valeur modulo d).

**WHY 5 : Peut-on combiner les deux automates ?**
OUI : en produit tensoriel. L'etat combine serait (z mod d, C) dans Z/dZ x {0,...,k-1}, avec ~kd etats. La non-accessibilite de (3^k mod d, 0) dans cet automate combine impliquerait N_cycle = 0. Le retenue FINALE doit etre 0 (pas de retenue pendante), ce qui ajoute une contrainte supplementaire.

**Statut : CONJECTURE** (T6). L'automate de retenue est un outil bien defini mais son analyse pour les valeurs specifiques de (k, S) reste ouverte.

---

## 4. APPROCHE 4 : INDUCTION SUR k

### 4.1 La relation de recurrence

Pour un cycle de type (k+1, S'), les parametres sont S' = ceil((k+1) log_2 3) et d' = 2^{S'} - 3^{k+1}.

g_{k+1}(B') = SUM_{j=0}^{k} 3^{k-j} * 2^{B'_j} = 3 * SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B'_j} + 2^{B'_k}

Si on pose B = (B'_0, ..., B'_{k-1}), alors g_{k+1}(B') = 3 * g_k(B) + 2^{B'_k}, a condition que B soit une partition de n' - B'_k en k parts, avec B'_k >= B'_{k-1}.

### 4.2 L'obstacle : le changement de modulus

Le probleme central est que d' != d. Pour un cycle de longueur k, on travaille mod d_k = 2^{S_k} - 3^k. Pour k+1, mod d_{k+1} = 2^{S_{k+1}} - 3^{k+1}.

La relation entre d_k et d_{k+1} est :
d_{k+1} = 2^{S_{k+1}} - 3^{k+1}

Si S_{k+1} = S_k + 1 (ce qui arrive quand la partie fractionnaire de (k+1) log_2 3 depasse 1), alors :
d_{k+1} = 2 * 2^{S_k} - 3 * 3^k = 2(d_k + 3^k) - 3 * 3^k = 2d_k + 2 * 3^k - 3^{k+1} = 2d_k - 3^k

Si S_{k+1} = S_k + 2 (ce qui arrive quand la partie fractionnaire traverse 1 avec un saut additionnel) :
d_{k+1} = 4 * 2^{S_k} - 3 * 3^k = 4(d_k + 3^k) - 3^{k+1} = 4d_k + 4 * 3^k - 3^{k+1} = 4d_k + 3^k

### 4.3 La relation de recurrence sur les ensembles d'accessibilite

**ENONCE (R192-T7 : Recurrence sur R_k) [PROUVE].**

Definissons R_k(d_k) = ensemble des z_k accessibles dans l'automate de Horner pour les cycles de type (k, S_k).

Alors la condition pour un cycle de type (k+1, S_{k+1}) est :

z_{k+1} = 3 * z_k + 2^{B_k} = 3^{k+1} mod d_{k+1}

ou z_k parcourt R_k(d_{k+1}) (l'ensemble d'accessibilite calcule modulo d_{k+1}, PAS modulo d_k).

**Le probleme :** R_k(d_{k+1}) != R_k(d_k) mod d_{k+1}. Les ensembles d'accessibilite dependent du modulus. L'induction NE TRANSFERE PAS directement d'un modulus a l'autre.

**Cependant,** si on considere R_k SANS reduction modulo (comme sous-ensemble de Z), alors R_k est un ensemble d'entiers POSITIFS. La question "R_k contient-il un multiple de d_k + 3^k ?" (pour le type k) devient "R_k contient-il un multiple de d_{k+1} + 3^{k+1} - 2^{B_k} * ..." pour le type k+1.

### 4.4 WHY chain : limitations et pistes de l'induction

**WHY 1 : Pourquoi l'induction directe echoue-t-elle ?**
Parce que le modulus change. L'information "g(B) != 0 mod d_k" ne dit RIEN sur "g(B') != 0 mod d_{k+1}".

**WHY 2 : Peut-on faire une induction FORTE qui capture plus d'information ?**
OUI, potentiellement. Au lieu de juste "N_cycle(k) = 0", on pourrait prouver "g(B) n'appartient pas a un ENSEMBLE E_k subset Z" qui est plus grand qu'un seul multiple de d_k. Si E_k est assez grand et stable par la recurrence, l'induction fonctionnerait.

**WHY 3 : Quel serait cet ensemble E_k ?**
Un candidat naturel est E_k = {m * d_k : m = 0, 1, ..., M_k} pour un M_k croissant. Si g(B) evite E_k, alors g(B) != 0 mod d_k en particulier. La recurrence g_{k+1} = 3g_k + 2^{B_k} transforme E_k en 3*E_k + 2^{B_k}. La condition "g_{k+1} not_in E_{k+1}" necessite "3g_k + 2^{B_k} not_in E_{k+1}", ce qui contraint g_k a eviter (E_{k+1} - 2^{B_k})/3.

C'est une recurrence sur les ENSEMBLES EVITES. Si |E_k| croit assez vite, l'hypothese d'induction se renforce a chaque pas.

**WHY 4 : Comment faire croitre E_k ?**
L'ensemble E_k initial est {0 mod d_k} = un ensemble de densite 1/d_k dans Z. A chaque pas inductif, on ajoute les pre-images : les z tels que 3z + 2^b in E_{k+1} pour un b admissible. Cela TRIPLE la densite approximativement (car z = (e - 2^b)/3 pour e in E_{k+1}). Apres k pas, la densite serait ~ 3^k / d_k ~ 1 (car d_k ~ 3^k). La saturation arrive en ~k pas.

**WHY 5 : Est-ce un echec ou un succes ?**
C'est un ECHEC quantitatif (la densite sature), mais un SUCCES qualitatif : l'induction montre que l'ensemble des etats "interdits" est DENSE dans Z/dZ apres k pas. Si on peut montrer que l'ensemble d'accessibilite R_k est DISJOINT de cet ensemble dense, on conclut. Mais c'est exactement le probleme original reformule.

**Statut : PROUVE** (T7, recurrence formelle). **OUVERT** (utilite de l'induction pour conclure).

---

## 5. APPROCHE 5 : L'OUTIL MANQUANT -- LE CRITERE DE RIGIDITE HORNER-MONOTONE (CRHM)

### 5.1 Diagnostic : ce qui manque

Faisons l'inventaire des outils existants et identifions le MANQUE :

| Outil | Ce qu'il fait | Ce qui manque |
|-------|--------------|---------------|
| Lambda_free (R191) | Factorise la somme LIBRE en produit | La correction de monotonie |
| BKT (R191) | Borne |rho_a| < 1 pour chaque etape | Le decouplage des etapes |
| Automate de Horner (R192) | Reformule en accessibilite | Borne sur |R_k| |
| NACL (R192) | Crible modulaire pour d compose | Inutile pour d premier |
| Erdos-Turan (R192) | Borne la discrepance | Circularite avec Lambda |
| Carry barrier (R192) | Contrainte binaire locale | Pas de borne globale |
| Induction (R192) | Recurrence sur k | Le modulus change |

**Le TROU :** Aucun outil ne combine la structure MULTIPLICATIVE (g = SUM 3^j * 2^{B_j}) avec la contrainte de MONOTONIE de facon a produire une borne non-triviale sur la discrepance.

### 5.2 L'invention : le Critere de Rigidite Horner-Monotone (CRHM)

**Idee directrice :** La structure de Horner z_{j+1} = 3z_j + 2^{B_j} avec B_j >= B_{j-1} cree une RIGIDITE dans la trajectoire de z_j dans Z/dZ. Plus precisement :

**DEFINITION R192-D6 (Corridor de Horner).**
Pour un etat z in Z/dZ et un seuil b_min, le corridor de Horner est :

> H(z, b_min) = {3z + 2^b mod d : b >= b_min}

C'est l'ensemble des successeurs possibles de z quand le prochain exposant est au moins b_min.

La taille de H(z, b_min) est au plus n - b_min + 1 (le nombre de valeurs de b admissibles).

### 5.3 L'observation structurelle sur les corridors

**ENONCE (R192-T8 : Structure des corridors) [PROUVE].**

Les elements de H(z, b_min) sont de la forme 3z + 2^b pour b = b_min, b_min+1, ..., n.
La distance entre deux elements consecutifs est :

> (3z + 2^{b+1}) - (3z + 2^b) = 2^b mod d

Donc les elements sont ESPACES de 2^{b_min}, 2^{b_min+1}, ..., 2^{n-1} (en distance modulaire).

Les espaces sont EXPONENTIELLEMENT croissants. Le corridor a une structure de "peigne" avec des dents de plus en plus espacees.

**Preuve :** Calcul direct.

**Consequence :** Le corridor contient au plus log_2(d) + 1 elements (car les espaces doublent). Pour b_min grand (pres de n), le corridor ne contient que quelques elements.

**THEOREME R192-T9 (Contraction des corridors monotones) [CONDITIONNEL].**

Au fil de la trajectoire z_0, z_1, ..., z_k, le seuil b_min croit (car b_min = B_j et B_j est croissant). Donc les corridors RETRECISSENT progressivement.

A l'etape j, le corridor a au plus n - B_{j-1} + 1 elements. Comme SUM B_j = n et les B_j croissent, B_j >= j * n / (k * ...) (par concavite de la somme). Pour la partition "typique", B_j ~ j * n / (k(k+1)/2) * quelque chose.

En tout cas, B_{k-1} >= n/k (car c'est le plus grand et la moyenne est n/k). Donc le corridor final a au plus n - n/k + 1 = n(k-1)/k + 1 elements.

Pour k = 3, n = 2 : corridor final a au plus 2 * 2/3 + 1 ~ 2 elements. L'ensemble des etats accessibles a la derniere etape est dans un corridor de 2 elements. La cible 2^S mod d = 3 mod 5 = 3. Les 2 elements du corridor final sont 3 * z_{k-1} + 2^{B_{k-1}} pour les 2 valeurs possibles de B_{k-1}. La condition 3 not_in {ces 2 elements} est verifiable directement.

**Statut : CONDITIONNEL** (la contraction est prouvee, la non-accessibilite de la cible dans le corridor final est specifique a chaque (k, S)).

### 5.4 Le CRHM proprement dit

**DEFINITION R192-D7 (Critere CRHM).**
Pour un type (k, S), definissons le GRAPHE D'ACCESSIBILITE CONTRAINT G(k, d) :
- Sommets : paires (z, b) in Z/dZ x {0, ..., n}
- Aretes : (z, b) -> (3z + 2^{b'} mod d, b') pour b' >= b
- Source : (1, 0)
- Cible : tout (3^k mod d, b) pour b in {0, ..., n}

**Critere :** N_cycle = 0 ssi la cible n'est pas accessible depuis la source en exactement k aretes avec la contrainte SUM des b dans le chemin = n (contrainte de somme).

**THEOREME R192-T10 (CRHM est correct) [PROUVE].**

N_cycle = 0 pour le type (k, S) ssi le graphe G(k, d) n'admet aucun chemin de longueur k de la source a la cible avec somme des exposants = n.

**Preuve :** Equivalence directe avec la definition de g(B) = 0 mod d. CQFD.

### 5.5 L'avantage du CRHM : reduction a un probleme de chemins ponderes

Le CRHM reformule le probleme de Collatz-cycles en un probleme de CHEMINS dans un graphe dirige PONDERE. Ce probleme est bien etudie en informatique theorique et en combinatoire.

**ENONCE (R192-T11 : Borne par la matrice de transfert monotone) [CONDITIONNEL].**

Definissons la matrice de transfert monotone T(q) indexee par (z, b) in Z/dZ x {0,...,n} :

> T(q)_{(z',b'), (z,b)} = q^{b'} si z' = 3z + 2^{b'} mod d et b' >= b, 0 sinon.

Alors le nombre de chemins de (1,0) a (z_target, *) de longueur k avec poids q^n est :

> N(k, q) = SUM_b e_{(z_target, b)}^T * T(q)^k * e_{(1,0)}

et N_cycle = [q^n] N(k, q), ou [q^n] extrait le coefficient de q^n.

La matrice T(q) est de taille d*(n+1) x d*(n+1). Son rayon spectral controle la croissance de N(k, q).

**Le point cle :** La contrainte de monotonie rend T(q) TRIANGULAIRE SUPERIEURE en la composante b (car b ne peut que croitre). Le rayon spectral de T est donc EGAL au maximum des rayons spectraux des blocs diagonaux (b fixe). Chaque bloc diagonal est une matrice d x d correspondant a la transition z -> 3z + 2^b mod d pour b fixe. C'est une matrice de PERMUTATION (car z -> 3z + 2^b est une bijection de Z/dZ).

Le rayon spectral d'une matrice de permutation est 1. Donc le rayon spectral de T(q) est domine par |q| (le poids des aretes).

**Consequence :** Le nombre de chemins N(k, q) est borne par d * (n+1) * |q|^n pour |q| = 1. La borne sur N_cycle = [q^n] N(k, 1) est donc au plus d*(n+1), ce qui est TRIVIAL (ca ne dit pas N_cycle = 0).

La borne non-triviale viendrait de l'ANNULATION dans T(q)^k, pas juste de la taille. C'est exactement l'objet de l'analyse spectrale de T(q).

**Statut : CONDITIONNEL** (la matrice est bien definie, l'analyse spectrale reste a faire).

### 5.6 WHY chain sur le CRHM

**WHY 1 : En quoi le CRHM differe-t-il de la formulation de R189 ?**
R189 travaille avec la matrice de transfert T_b dans Z/dZ SANS la composante monotonie. Le CRHM ajoute la dimension "dernier exposant b" et la contrainte b' >= b. C'est un RAFFINEMENT de R189 qui encode EXACTEMENT la monotonie.

**WHY 2 : Pourquoi la structure triangulaire est-elle importante ?**
Parce qu'elle signifie que les composantes spectrales de T sont DECOUPLES par strate de b. Les modes propres de T sont des COMBINATIONS de modes propres des blocs diagonaux (transitions z -> 3z + 2^b pour b fixe). L'annulation dans T^k vient de l'INTERFERENCE entre les modes des differentes strates.

**WHY 3 : Cette interference est-elle quantifiable ?**
OUI en principe. Les modes propres du bloc b sont les caracteres chi_a(z) = omega^{az} de Z/dZ, avec valeur propre omega^{a * 2^b} (car l'action z -> 3z + 2^b multiplie chi_a par omega^{a * 2^b} et envoie chi_a sur chi_{3a}). L'interference entre strates b et b' fait intervenir les DIFFERENCES de phases omega^{a*2^b} - omega^{a*2^{b'}}, qui sont controlees par la structure de <2> dans Z/dZ.

**C'est ici que le CRHM REJOINT la theorie de R189-R191.** Les valeurs propres de T sont les rho_a de R189, et la structure triangulaire encode la monotonie comme un FILTRAGE spectral.

**WHY 4 : Que gagne-t-on par rapport a R189 ?**
Le CRHM ne RESOUT pas le probleme mais le REFORMULE de facon qui rend explicite l'interaction entre la structure spectrale (rho_a) et la contrainte de monotonie. Au lieu de "corriger" Lambda_free par la monotonie (R191), le CRHM INTEGRE la monotonie dans la matrice de transfert.

**WHY 5 : Cela suffit-il pour fermer le gap ?**
PAS DIRECTEMENT. Mais cela ouvre la porte a des outils de theorie spectrale pour les operateurs triangulaires (nilpotents + diagonaux), comme le calcul de (D + N)^k ou D est le bloc diagonal et N est le bloc nilpotent (transitions b -> b' > b). La formule de Campbell-Baker-Hausdorff ou le developpement perturbatif en puissances de N/D pourrait donner la borne manquante.

---

## 6. L'OUTIL VERITABLEMENT MANQUANT : LE THEOREME DE NON-COINCIDENCE ALGEBRIQUE (TNCA)

### 6.1 Le probleme nu, depouille de toute machinerie

Oublions Lambda, les automates, les retenues. Le probleme NU est :

> **Existe-t-il une partition 0 <= B_0 <= B_1 <= ... <= B_{k-1}, SUM B_j = S-k, telle que SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} = 0 mod (2^S - 3^k) ?**

C'est un probleme d'ARITHMETIQUE PURE : une equation diophantienne avec contrainte d'ordre et de somme.

### 6.2 La structure algebrique de l'equation

En posant x_j = 2^{B_j} (avec x_0 <= x_1 <= ... <= x_{k-1}, chaque x_j est une puissance de 2, et le produit PROD x_j = 2^n), l'equation devient :

> SUM_{j=0}^{k-1} 3^{k-1-j} * x_j = 0 mod (2^S - 3^k)

ou x_j in {1, 2, 4, 8, ...}, x_0 | x_1 | ... | x_{k-1} (divisibilite car x_j = 2^{B_j} et B monotone implique la divisibilite), PROD x_j = 2^n.

Non : x_0 | x_1 n'est pas exact (B_0 <= B_1 signifie 2^{B_0} | 2^{B_1}, ce qui est correct si B_0 <= B_1).

En fait, x_0 <= x_1 <= ... <= x_{k-1} et chaque x_j est une puissance de 2. Et SUM B_j = SUM log_2(x_j) = n.

### 6.3 L'idee du TNCA

**DEFINITION R192-D8 (Ensemble de coincidence).**
C(k, S) = {(x_0, ..., x_{k-1}) : chaque x_j = 2^{b_j}, b_0 <= ... <= b_{k-1}, SUM b_j = n, SUM 3^{k-1-j} x_j = 0 mod d}

Le TNCA affirmerait que C(k, S) = vide pour tout k >= 2.

**L'idee :** La somme L(x) = SUM 3^{k-1-j} x_j est une FORME LINEAIRE a coefficients dans la progression geometrique {1, 3, 9, ..., 3^{k-1}}. Les x_j sont dans la progression geometrique {1, 2, 4, ..., 2^n}. La condition L(x) = 0 mod d ou d = 2^S - 3^k est une condition de COINCIDENCE entre les deux progressions geometriques (en base 3 et en base 2).

**CONJECTURE R192-C1 (Non-coincidence).**
Pour k >= 2 et S = ceil(k log_2 3), la forme lineaire L(x) = SUM 3^{k-1-j} x_j avec x_j in {2^b : b >= 0}, evaluee sur les points du reseau {x : x_0 | x_1 | ... | x_{k-1}, PROD x_j^{somme...}} ne prend JAMAIS la valeur 0 mod d.

**Argument heuristique profond :** La non-coincidence vient de l'INCOMMENSURABILITE de log 2 et log 3. Si log_2 3 etait rationnel, disons p/q, alors 2^q = 3^p et d = 2^S - 3^k pourrait etre 0 pour certains (S, k). Comme log_2 3 est IRRATIONNEL, d != 0, mais d pourrait etre "petit". La non-coincidence de L(x) = 0 mod d est une manifestation plus subtile de cette incommensurabilite : non seulement 2^S != 3^k (ce qu'on sait), mais les combinaisons lineaires mixtes SUM 3^j * 2^{b_j} ne sont JAMAIS des multiples exacts de la "presque-coincidence" d = 2^S - 3^k.

### 6.4 Lien avec les mesures d'irrationalite

**OBSERVATION R192-O2 (Connexion diophantienne).**

La mesure d'irrationalite de log_2 3 est finie (resultat de Rhin-Toffin, 2000 : mu(log_2 3) < 5.126). Cela signifie que pour tout epsilon > 0, il n'y a qu'un nombre FINI de (p, q) avec |q * log_2 3 - p| < q^{-mu+epsilon}.

Equivalemment, d = 2^S - 3^k = |2^S - 3^k| >= 2^{S(1 - 1/(mu-1-eps))} pour S grand.

Cette borne donne d >> 2^{S * 0.758...}, ce qui est plus fort que la borne triviale d >= 1.

**Comment cela aide-t-il ?**

L'equation L(x) = m * d avec m >= 1 necessite L(x) >= d. Or L(x) <= SUM 3^{k-1-j} * 2^n = (3^k - 1)/2 * 2^n = (3^k - 1) * 2^{n-1}. Et d = 2^S - 3^k. Donc m <= L_max / d ~ (3^k * 2^n) / (2^S - 3^k) = (3^k * 2^{S-k}) / (2^S - 3^k).

Pour 2^S ~ 3^k (S = ceil(k log_2 3)), on a m ~ 3^k * 2^{-k} / (2^S/3^k - 1) * (1/3^k) ... C'est le ratio (3/2)^k / epsilon_k ou epsilon_k = 2^S/3^k - 1. La mesure d'irrationalite borne epsilon_k par en bas, donc m est borne par en haut.

Le nombre de solutions possibles est au plus m * (nombre de representations de md comme somme L(x)). Si m est PETIT et la representation est RIGIDE, il n'y a pas de solution.

### 6.5 WHY chain : le TNCA est-il prouvable ?

**WHY 1 : Pourquoi le TNCA serait-il vrai ?**
Parce que la condition L(x) = 0 mod d est une equation a k inconnues (les b_j) et UN module. Generiquement, une equation modulo d dans Z^k a ~d^{k-1} solutions (un degre de liberte de moins). Mais les b_j sont CONTRAINTS (monotonie, somme, positivite), ce qui reduit l'espace a p_k(n) points. Si p_k(n) << d (ce qui est vrai pour k < 42), il est "generiquement" vrai qu'aucun de ces points ne satisfait l'equation.

**WHY 2 : Cet argument probabiliste suffit-il ?**
NON. Il montre que le TNCA est "probable" mais pas "certain". Il pourrait y avoir un alignement accidentel pour un k specifique.

**WHY 3 : Peut-on renforcer l'argument ?**
OUI, par un argument d'IRRATIONNALITE. L'equation SUM 3^{k-1-j} * 2^{B_j} = m * (2^S - 3^k) se reecrit :

SUM 3^{k-1-j} * 2^{B_j} + m * 3^k = m * 2^S

C'est une relation lineaire entre des puissances de 2 et des puissances de 3. Par le theoreme de Baker (1966) sur les formes lineaires en logarithmes, une telle relation impose des CONTRAINTES sur les exposants. Specifiquement, si SUM a_j * 2^{b_j} = SUM c_j * 3^{e_j} avec des coefficients rationnels et des exposants entiers, la hauteur de cette relation est bornee par en bas par une expression impliquant les logarithmes.

**WHY 4 : Baker s'applique-t-il directement ?**
PARTIELLEMENT. Baker borne |alpha_1^{b_1} * ... * alpha_n^{b_n} - 1| > exp(-C * PROD log(b_j)). Notre equation a la forme SUM 3^j * 2^{B_j} = m * d, ce qui N'EST PAS un produit de puissances mais une SOMME. Baker s'applique aux formes MULTIPLICATIVES, pas additives.

Pour les formes ADDITIVES (sommes de puissances), les outils sont les S-unit equations (Evertse, 1984). Le theoreme d'Evertse donne : le nombre de solutions de l'equation x_1 + ... + x_k = 0 en S-units est au plus C(k, |S|) (une constante dependant de k et de |S| = 2, les premiers etant 2 et 3). Pour k fixe, le nombre de solutions est FINI.

**WHY 5 : Evertse conclut-il ?**
PRESQUE. Le theoreme d'Evertse (1984, version quantitative de Schmidt 1989) dit que le nombre de solutions non-degenerees de x_1 + ... + x_k = 0 en {2,3}-units est au plus C(k) = exp(exp(exp(k))). Ce nombre est ENORME mais FINI. Pour chaque k fixe, il n'y a qu'un nombre fini de partitions B telles que g(B) = 0 mod d. Si on combine cela avec la contrainte SUM B_j = n (qui fixe "l'echelle"), l'espace des solutions se reduit drastiquement.

Le TNCA serait une consequence d'Evertse SI on pouvait montrer que les contraintes (monotonie + somme + module specifique d = 2^S - 3^k) eliminent TOUTES les solutions finies d'Evertse. C'est un programme finistique mais potentiellement realisable.

**Statut : CONJECTURE** (C1). Le lien avec Evertse est PROMETTEUR mais pas clos.

---

## 7. SYNTHESE : INVENTAIRE DES OUTILS INVENTES

### 7.1 Tableau recapitulatif

| # | Outil | Idee cle | Statut | Force | Faiblesse |
|---|-------|----------|--------|-------|-----------|
| 1 | Automate monotone de Horner | Accessibilite dans Z/dZ avec alphabet restreint | T1 CONDITIONNEL, T2 PROUVE, T3 PROUVE | Monotonie AIDE (restreint chemins) | Borne sur |R_k| non effective |
| 2 | Erdos-Turan en increments | Decouplage par changement de variables Delta | T4 CONDITIONNEL | Elimine B_0, reduit dimension | Gain marginal (meme structure) |
| 3 | Barriere de retenues | Contraintes binaires locales de g=md | T5 PROUVE, T6 CONJECTURE | Exploite structure fine de d en base 2 | Pas de borne globale |
| 4 | Induction sur k | Recurrence R_k -> R_{k+1} | T7 PROUVE | Exploite structure recursive de Horner | Modulus change a chaque pas |
| 5 | CRHM + matrice de transfert monotone | Matrice triangulaire encoding monotonie | T8 PROUVE, T9-T11 CONDITIONNEL | Integre monotonie dans spectre | Borne triviale sans analyse fine |
| 6 | TNCA via Evertse | S-unit equations bornent les solutions | C1 CONJECTURE | Finitude prouvee par Evertse | Bornes non effectives |

### 7.2 Classement par potentiel

**RANG 1 : L'automate monotone (Approche 1)** -- Le CHANGEMENT DE PARADIGME. La monotonie AIDE au lieu de nuire. Ouvre la voie a des bornes sur |R_k| par des methodes de theorie des graphes / accessibilite. Combine naturellement avec le NACL pour d compose.

**RANG 2 : Le TNCA via Evertse (Approche 6)** -- Le CANON. Si on peut rendre effectif le theoreme d'Evertse pour notre equation specifique, on obtient une preuve pour tout k >= 2. Le programme est clair mais techniquement exigeant.

**RANG 3 : Le CRHM (Approche 5)** -- Le PONT. Relie la formulation spectrale (R189) a la formulation d'accessibilite (Approche 1) via la matrice de transfert monotone. L'analyse spectrale de cette matrice triangulaire est le probleme central.

**RANG 4 : La barriere de retenues (Approche 3)** -- L'OBSTRUCTION LOCALE. Utile pour les petits k ou la structure binaire est contraignante. Potentiellement puissante en combinaison avec l'automate.

**RANG 5 : L'induction (Approche 4)** -- Le PROGRAMME. Formellement correct mais le changement de modulus est un obstacle serieux. Utile comme cadre organisationnel.

**RANG 6 : Erdos-Turan en increments (Approche 2)** -- Le GAIN MARGINAL. Reduction de dimension de 1, meme structure sous-jacente.

### 7.3 L'observation meta-structurelle

**ENONCE (R192-Meta : Dualite accessibilite/discrepance).**

Les deux paradigmes -- DISCREPANCE (les valeurs g(B) sont bien reparties mod d) et ACCESSIBILITE (l'etat cible n'est pas atteint) -- sont DUAUX :

- La discrepance est une mesure GLOBALE : toutes les valeurs sont "loin" de 0.
- L'accessibilite est une mesure LOCALE : 0 n'est jamais atteint.

Pour la discrepance, la monotonie est un OBSTACLE (elle concentre les phases).
Pour l'accessibilite, la monotonie est un ATOUT (elle restreint les chemins).

**Le choix strategique optimal est de COMBINER les deux :**
- Utiliser l'accessibilite (automate monotone) pour les k ou le graphe est petit (k < 20).
- Utiliser la discrepance (BKT + completion) pour les k ou le spectre est controle (k > 20 et < 42).
- Utiliser le comptage (R189-T10) pour les k >= 42.

---

## 8. PISTES OUVERTES (NE PAS FERMER)

### 8.1 Piste A : Borne de croissance de R_k dans l'automate monotone

**Question ouverte :** Quelle est la croissance exacte de |R_j| (ensemble d'accessibilite a l'etape j) en fonction de j, d, et n ? Y a-t-il un regime ou |R_k| = o(d) pour tout k < 42 ?

**Sous-questions :**
- L'application z -> 3z + 2^b est EXPANSIVE dans Z/dZ (elle "melange"). La composition de k telles applications donne-t-elle un ensemble de densite 1 dans Z/dZ, ou la restriction monotone maintient-elle la densite basse ?
- La structure du groupe <3> (l'orbite de z_0 = 1 sous multiplication par 3) joue-t-elle un role dans la croissance de R_k ?
- Pour d premier, l'application 3*id est une HOMOTHETIE dans Z/dZ. Les successeurs sont des translates de l'image de R_{j-1} par cette homothetie. L'analyse des ensembles additifs (theoreme de Freiman-Ruzsa) pourrait borner |R_j + {2^b : b >= b_min}|.

### 8.2 Piste B : Effectivisation d'Evertse pour g(B) = 0 mod d

**Question ouverte :** Le theoreme d'Evertse est-il effectif pour notre equation specifique ? Les bornes de hauteur de Schmidt-Schlickewei sont-elles suffisantes pour exclure toutes les solutions pour k >= 2 ?

**Sous-questions :**
- La version effective d'Evertse (Evertse-Schlickewei-Schmidt, 2002) donne des bornes sur la hauteur des solutions. Est-ce que les solutions de g(B) = 0 mod d satisfont automatiquement des bornes de hauteur (car B_j <= n ~ 0.585k) ?
- Le nombre de solutions non-degenerees est au plus exp(C * k^3). Pour k <= 41, c'est exp(C * 68921), un nombre astronomique mais fini. Peut-on exploiter les contraintes supplementaires (monotonie, somme, module specifique) pour reduire ce nombre a 0 ?

### 8.3 Piste C : Analyse spectrale de la matrice de transfert monotone

**Question ouverte :** Quel est le spectre de la matrice T(q) du CRHM ? La structure triangulaire (en b) permet-elle un calcul explicite des valeurs propres ?

**Sous-questions :**
- Les blocs diagonaux sont des matrices de permutation (une seule entree non-nulle par ligne/colonne). Leurs valeurs propres sont des racines de l'unite.
- Les blocs hors-diagonaux (transitions b -> b' > b) couplent les strates. L'analyse perturbative (T = D + N, D diagonal, N nilpotent) donne T^k = SUM C(k,l) D^{k-l} N^l. Le terme dominant est D^k, et les corrections sont controlees par ||N||.
- Pour d premier et <3> engendrant (Z/dZ)*, les valeurs propres de D sont uniformement reparties sur le cercle unite. La somme D^k oscille et la moyenne est O(1/d). Les corrections N^l ajoutent-elles ou retirent-elles de cette moyenne ?

### 8.4 Piste D : L'automate monotone pour les PETITS k

**Question ouverte :** Pour k = 2, 3, ..., 10, l'automate monotone est-il analysable a la main (sans calcul) ? La non-accessibilite de 3^k mod d peut-elle etre prouvee par raisonnement pur ?

**Ebauche pour k = 3 :** d = 5, n = 2, partitions : (0,0,2) et (0,1,1).
- z_0 = 1
- Pour B = (0,0,2) : z_1 = 3+1 = 4, z_2 = 12+1 = 13 = 3 mod 5, z_3 = 9+4 = 13 = 3 mod 5. Cible = 3^3 mod 5 = 27 mod 5 = 2. Donc z_3 = 3 != 2 = cible.
- Pour B = (0,1,1) : z_1 = 3+1 = 4, z_2 = 12+2 = 14 = 4 mod 5, z_3 = 12+2 = 14 = 4 mod 5. Cible = 2. Donc z_3 = 4 != 2.

**N_cycle = 0 pour k = 3 : VERIFIE par l'automate monotone.**

Pour k = 4 : d = 47, n = 3. Partitions de 3 en 4 parts : (0,0,0,3), (0,0,1,2), (0,1,1,1). Trois vecteurs. La verification serait : z_4 != 3^4 mod 47 = 81 mod 47 = 81 - 47 = 34 pour chacun. C'est faisable par raisonnement pur.

---

## 9. WHY CHAINS GLOBALES

### 9.1 Pourquoi le probleme Collatz-cycles est-il si difficile ?

**WHY 1 :** Parce qu'il combine deux structures arithmetiques INCOMMENSURABLES (puissances de 2 et puissances de 3) avec une contrainte d'ordre (monotonie).

**WHY 2 :** Parce que la monotonie est une contrainte GLOBALE (elle correle les k variables B_j), ce qui empeche la factorisation en produit de facteurs independants.

**WHY 3 :** Parce que l'approche spectrale (borner Lambda(s)) souffre de la concentration de phases due a la monotonie (le gap 1.35x), tandis que l'approche directe (prouver g != 0 mod d) souffre de l'absence d'outil diophantien adapte.

**WHY 4 :** Parce que les outils existants (BKT, Erdos-Turan, Baker, Evertse) ne sont pas TAILLES pour ce probleme : BKT ignore la monotonie, Erdos-Turan necessite Lambda qu'on ne sait pas borner, Baker ne s'applique qu'aux formes multiplicatives, Evertse est non effectif.

**WHY 5 :** Parce que l'outil MANQUANT est un theoreme qui COMBINE la structure multiplicative (g est une forme lineaire en puissances de 2 a coefficients puissances de 3) avec la structure combinatoire (monotonie + somme fixee) pour donner une borne de DISCREPANCE ou de NON-ACCESSIBILITE. Cet outil n'existe pas encore dans la litterature.

### 9.2 Pourquoi l'automate monotone est-il le candidat le plus prometteur ?

**WHY 1 :** Parce qu'il INTEGRE la monotonie comme une restriction naturelle (alphabet croissant) au lieu de la traiter comme un defaut.

**WHY 2 :** Parce qu'il transforme le probleme en un probleme de COMBINATOIRE DES CHEMINS, ou les outils sont riches (theorie des graphes, automates finis, matrices de transfert).

**WHY 3 :** Parce qu'il offre une HIERARCHIE de raffinements : NACL pour d compose, analyse spectrale pour d premier, verification directe pour petits k.

**WHY 4 :** Parce que la borne sur |R_k| est le SEUL ingredient manquant : si on montre |R_k| < d pour k < 42, et que la cible n'est pas dans R_k, on conclut.

**WHY 5 :** Parce qu'il est DUAL a l'approche spectrale : la ou le spectre echoue (la monotonie concentre les phases), l'accessibilite reussit (la monotonie restreint les chemins). Les deux paradigmes sont COMPLEMENTAIRES, pas contradictoires.

---

## 10. REGISTRE FINAL R192

| Element | Statut | Section |
|---------|--------|---------|
| R192-T1 : Contraction de R_j dans l'automate monotone | CONDITIONNEL | 1.6 |
| R192-T2 : Action de <3> sur l'automate | PROUVE | 1.7 |
| R192-T3 : Critere NACL | PROUVE | 1.8 |
| R192-T4 : Factorisation en increments | CONDITIONNEL | 2.2 |
| R192-T5 : Contrainte de retenue pour g = md | PROUVE | 3.2 |
| R192-T6 : Barriere de retenue | CONJECTURE | 3.4 |
| R192-T7 : Recurrence sur R_k | PROUVE | 4.3 |
| R192-T8 : Structure des corridors | PROUVE | 5.3 |
| R192-T9 : Contraction des corridors monotones | CONDITIONNEL | 5.3 |
| R192-T10 : CRHM est correct | PROUVE | 5.4 |
| R192-T11 : Matrice de transfert monotone | CONDITIONNEL | 5.5 |
| R192-C1 : Non-coincidence (TNCA) | CONJECTURE | 6.3 |
| R192-O1 : Monotonie et retenues | OBSERVATION | 3.3 |
| R192-O2 : Connexion diophantienne | OBSERVATION | 6.4 |
| R192-Meta : Dualite accessibilite/discrepance | OBSERVATION | 7.3 |

**Score :** 6 PROUVES, 4 CONDITIONNELS, 2 CONJECTURES, 3 OBSERVATIONS, 4 PISTES OUVERTES.

---

## 11. RECOMMANDATIONS POUR R193

### Priorite 1 : Analyser l'automate monotone pour k = 2, ..., 10
Prouver par raisonnement pur que l'etat 3^k mod d n'est pas dans R_k pour ces petits cas. Si un pattern emerge, le generaliser.

### Priorite 2 : Borner |R_k| par la theorie sum-product
L'ensemble R_k est construit par des operations "3z + 2^b". Par les resultats de Bourgain-Katz-Tao sur les ensembles qui sont approximativement fermes sous addition ET multiplication, |R_k| devrait croitre substantiellement a chaque etape. Si |R_k| < d (ne sature pas), la non-accessibilite est "generique".

### Priorite 3 : Explorer Evertse effectif
Verifier si les bornes de hauteur d'Evertse-Schlickewei-Schmidt (2002) sont compatibles avec nos contraintes (B_j <= n ~ 0.585k). Si oui, le TNCA decoule par calcul fini.

### Priorite 4 : Analyse spectrale de T monotone
Calculer le spectre de la matrice de transfert monotone T(q) pour les petits (k, d) et identifier le mecanisme d'annulation.

---

*R192 Innovateur : SIX outils inventes. Le changement de paradigme fondamental est le passage de la DISCREPANCE (ou la monotonie nuit) a l'ACCESSIBILITE (ou la monotonie aide). L'automate monotone de Horner (Approche 1) et le CRHM (Approche 5) sont les contributions les plus originales. Le TNCA (Approche 6) via Evertse offre un chemin theorique vers une preuve complete. Quatre pistes sont laissees OUVERTES pour R193. Le verrou central est desormais : borner |R_k| dans l'automate monotone, ou effectiviser Evertse pour notre equation specifique.*
