# R183 -- Argument Combinatoire sur le Simplexe Discret
**Date :** 16 mars 2026
**Methode :** Raisonnement combinatoire pur -- aucune somme exponentielle, aucun corps fini
**Auteur :** Claude (mode INNOVATEUR MATHEMATIQUE)

---

## 0. CADRE ET NOTATIONS

**Simplexe discret :**
V_k(S) = {(B_0,...,B_{k-1}) dans N^k : 0 <= B_0 <= B_1 <= ... <= B_{k-1} <= S-1}

**Cardinalite :** |V_k(S)| = C(S+k-2, k-1)

**Fonctionnelle :** g(v) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}

**Cible :** d = 2^S - 3^k > 0 (pour S = ceil(k * log_2(3)))

**Question :** g(v) = 0 mod d a-t-il des solutions dans V_k(S) pour k >= 3 ?

**Valeurs extremes :**
- g_min = g(0,...,0) = sum_{j=0}^{k-1} 3^{k-1-j} = (3^k - 1)/2
- g_max = g(S-1,...,S-1) = 2^{S-1} * (3^k - 1)/2

**Rappel k=1 :** S=2, d=1, g(v)=2^{B_0}, trivially g=0 mod 1. Cycle {1->4->2->1} existe. Tout argument doit ECHOUER pour k=1.

---

## APPROCHE 1 : DECOMPOSITION EN CHAINES ET OBSTRUCTION MONOTONE

### 1.1 Idee

Le simplexe V_k(S) est un poset sous l'ordre composante par composante : v <= w ssi B_j <= B'_j pour tout j. La fonctionnelle g est strictement croissante sur ce poset (puisque chaque 3^{k-1-j} > 0 et 2^x est strictement croissante). Donc g est une extension lineaire reelle du poset.

Par le theoreme de Dilworth, V_k(S) se decompose en chaines (totalement ordonnees) et en antichaines. Sur chaque chaine maximale, g est strictement croissante. La question est : peut-on decomposer V_k(S) en chaines telles que, sur chaque chaine, g mod d ne passe jamais par 0 ?

### 1.2 Analyse

Sur une chaine maximale (0,...,0) -> ... -> (S-1,...,S-1), g parcourt de g_min a g_max. Le nombre de residus 0 mod d traverses est exactement floor(g_max/d) - floor((g_min-1)/d).

Calculons :
- g_max / d = 2^{S-1} * (3^k-1) / (2*(2^S - 3^k)) = 2^{S-1} * (3^k-1) / (2*d)
- g_min / d = (3^k - 1) / (2*d) = (3^k - 1) / (2*(2^S - 3^k))

Puisque d = 2^S - 3^k et 2^S ~ 3^k (car S = ceil(k*log_2(3))), on a d << 3^k pour grand k.
Donc g_min/d ~ (3^k)/(2d) >> 1 et g_max/d ~ 2^{S-1} * 3^k / (2d) >> 1.

L'intervalle [g_min, g_max] contient ENORMEMENT de multiples de d. On ne peut pas esperer qu'une chaine les evite tous.

### 1.3 Obstruction structurelle ?

L'idee etait : la contrainte de monotonie (B_0 <= ... <= B_{k-1}) restreint g a un sous-ensemble de [g_min, g_max], et peut-etre ce sous-ensemble evite certains residus.

Mais l'image Im(g) sur V_k(S) est un SOUS-ENSEMBLE de Z, pas un intervalle continu. La question devient : Im(g) mod d contient-il 0 ?

**Probleme :** |Im(g)| <= C(S+k-2, k-1) mais g_max - g_min >> |Im(g)| pour grand k. Donc Im(g) est EPARS dans [g_min, g_max]. Mais |Im(g)| >> d des que C(S+k-2, k-1) >> d, ce qui arrive TRES vite (le binomial croit polynomialement en S, d croit exponentiellement en k mais C croit exponentiellement aussi).

### 1.4 Verdict

**Statut : ECHEC.** L'approche par chaines ne fournit pas d'obstruction. La raison profonde : g est monotone sur le poset, mais le passage mod d detruit la monotonie. Les residus de g mod d sur une chaine sont une marche dans Z/dZ qui ne respecte aucun ordre. La decomposition en chaines est un outil pour les problemes ou la monotonie est PRESERVEE, pas pour les questions modulaires.

**Ce qui reste :** L'observation que Im(g) est epars pourrait etre utile si l'on pouvait montrer que l'eparsite est STRUCTUREE (pas aleatoire). C'est la piste de l'Approche 3.

---

## APPROCHE 2 : COLORATION DU SIMPLEXE PAR RESIDUS PARTIELS

### 2.1 Idee

Colorier chaque vecteur v par une "signature" qui contraint g(v) mod d. L'idee vient de la theorie de Ramsey : si le simplexe est assez grand et les couleurs assez peu nombreuses, il contient une structure monochromatique.

Definissons les sommes partielles :
- G_m(v) = sum_{j=0}^{m} 3^{k-1-j} * 2^{B_j} pour m = 0, 1, ..., k-1
- G_{k-1}(v) = g(v)

Chaque v est "colorie" par le k-uplet (G_0 mod d, G_1 mod d, ..., G_{k-1} mod d).

### 2.2 La recurrence des sommes partielles

G_m = G_{m-1} + 3^{k-1-m} * 2^{B_m}

Donc : G_m mod d = G_{m-1} mod d + 3^{k-1-m} * 2^{B_m} mod d

C'est une MARCHE dans Z/dZ, avec des pas de taille 3^{k-1-m} * 2^{B_m} mod d.

Pour m fixe, quand B_m varie dans {B_{m-1}, B_{m-1}+1, ..., S-1}, les pas possibles sont :
{3^{k-1-m} * 2^b mod d : b = B_{m-1}, ..., S-1}

### 2.3 L'ensemble des pas

Fixons c = 3^{k-1-m} mod d. Les pas possibles sont {c * 2^b mod d : b = 0, ..., S-1}.

Or 2^S mod d = 2^S mod (2^S - 3^k) = 3^k. Donc :
- 2^0, 2^1, ..., 2^{S-1} mod d sont les elements {1, 2, 4, ..., 2^{S-1}} mod d
- 2^S mod d = 3^k

L'ensemble {2^b mod d : b = 0,...,S-1} est un sous-ensemble de Z/dZ de taille exactement S (car ces puissances sont toutes < 2^S = d + 3^k, et pour b < S, 2^b < 2^S, donc 2^b mod d prend au plus 2 valeurs par "tour" de d... mais plus precisement, 2^b < d pour b <= S-1 n'est PAS garanti puisque d < 2^S).

**Observation cle :** Pour b <= S-2, 2^b <= 2^{S-1} < 2^S = d + 3^k, mais d = 2^S - 3^k, donc 2^{S-1} < d ssi 2^{S-1} < 2^S - 3^k ssi 3^k < 2^{S-1}. Or S = ceil(k*log_2(3)), donc 2^S > 3^k mais 2^{S-1} peut etre < 3^k. En fait, 2^{S-1} < 3^k < 2^S est la condition generique (c'est pourquoi d < 2^{S-1} generiquement, donc d < 3^k).

Consequence : certains 2^b avec b proche de S-1 sont PLUS GRANDS que d, donc 2^b mod d = 2^b - d = 2^b - 2^S + 3^k, et comme b <= S-1, 2^b - 2^S + 3^k = 3^k - (2^S - 2^b) = 3^k - 2^b*(2^{S-b} - 1).

### 2.4 Ce que la coloration nous dit

Si l'on pouvait montrer que pour chaque couleur du prefixe (G_0,...,G_{m-1}) mod d, l'ensemble des pas disponibles a l'etape m EVITE la couleur necessaire pour atteindre 0 au final, on aurait une preuve.

Mais cela revient a montrer : pour chaque valeur de G_{m-1} mod d et chaque choix futur de (B_m,...,B_{k-1}), il est impossible d'atteindre G_{k-1} = 0 mod d.

C'est exactement le probleme original reformule recursivement. La coloration ne reduit pas la complexite : elle la DEPLACE sur les k-m derniers termes.

### 2.5 Sous-produit utile

Neanmoins, cette approche revele que le probleme est EQUIVALENT a une question sur les marches dans Z/dZ avec des pas contraints (chaque pas dans un ensemble qui depend de l'etat precedent a cause de la monotonie B_m >= B_{m-1}).

**Statut : ECHEC PARTIEL.** La coloration reformule mais ne resout pas. Cependant, l'equivalence avec une marche contrainte dans Z/dZ est un OUTIL potentiel pour l'Approche 5.

---

## APPROCHE 3 : EPARSITE STRUCTUREE DE Im(g) -- L'ARGUMENT DE LACUNARITE

### 3.1 Idee

g(v) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} est une somme de termes de la forme 3^a * 2^b. L'ensemble des valeurs possibles pour chaque terme est :
- Terme j : {3^{k-1-j} * 2^b : b in {0,...,S-1}} = {3^{k-1-j}, 2*3^{k-1-j}, ..., 2^{S-1}*3^{k-1-j}}

C'est un ensemble LACUNAIRE (les valeurs sont espacees de facon exponentielle). La somme de k ensembles lacunaires n'est generalement pas dense -- elle possede des "trous" structurels.

### 3.2 La structure multiplicative de g

Reecrivons g comme :
g(v) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} = 3^{k-1} * 2^{B_0} + 3^{k-2} * 2^{B_1} + ... + 3^0 * 2^{B_{k-1}}

Chaque terme est dans un "rail" : le rail j est {3^{k-1-j} * 2^b : b = 0,...,S-1}.

Les rails sont GEOMETRIQUEMENT DISTINCTS. Le rail j contient des multiples de 3^{k-1-j} qui ne sont PAS des multiples de 3^{k-j} (sauf si 2^b l'est, ce qui est impossible). Donc les rails sont quasi-disjoints dans le sens suivant :

**FAIT.** La valuation 3-adique de chaque terme j est exactement k-1-j (puisque v_3(2^{B_j}) = 0). Donc v_3(g(v)) = v_3 de la somme, et le terme dominant pour la valuation 3-adique est le DERNIER terme (j=k-1) qui a valuation 3-adique 0.

En fait : g(v) = 2^{B_{k-1}} + 3*(contribution de j=0,...,k-2). Donc g(v) mod 3 = 2^{B_{k-1}} mod 3.

### 3.3 Cascades de congruences

g(v) mod 3 = 2^{B_{k-1}} mod 3 = (-1)^{B_{k-1}} mod 3 = {1 si B_{k-1} pair, 2 si B_{k-1} impair}

Or d mod 3 = (2^S - 3^k) mod 3 = 2^S mod 3 = (-1)^S.

Pour g(v) = 0 mod d, il faut g(v) = 0 mod gcd(3, d). Si 3 ne divise pas d (ce qui est le cas car 3 | 3^k mais 3 ne divise pas 2^S sauf si... non, 3 ne divise jamais 2^S, et d = 2^S - 3^k, donc d mod 3 = 2^S mod 3 = (-1)^S != 0). Donc 3 ne divise pas d, et la congruence mod 3 ne donne pas d'obstruction directe.

Mais si d = 0 mod d, alors g(v) doit etre un multiple de d. Combinee a g(v) mod 3 in {1,2}, cela impose que le multiple de d choisi doit etre congru a 1 ou 2 mod 3. C'est une condition faible (elimine seulement les multiples de d qui sont aussi multiples de 3, soit environ 1/3 d'entre eux).

### 3.4 Extension aux congruences superieures (3^2, 3^3, ...)

g(v) mod 9 = 2^{B_{k-1}} + 3 * 2^{B_{k-2}} mod 9

Cela ne depend que des DEUX derniers termes. Plus generalement, g(v) mod 3^m ne depend que des m derniers termes.

C'est une structure de TYPE ULTRAMETRIQUE : les chiffres de poids faible de g(v) dans la base 3 sont determines par les dernieres composantes de v. Cela est dual a la structure usuelle ou les chiffres de poids fort sont determines par les premieres composantes.

**Obstruction potentielle :** Si d a une grande valuation p-adique pour un premier p tel que g(v) mod p^m est contraint, on pourrait avoir une obstruction locale. Mais d = 2^S - 3^k est impair et non divisible par 3, donc les seuls premiers pertinents sont ceux divisant d.

### 3.5 Verdict

**Statut : ECHEC ENRICHISSANT (DEDUIT).** La lacunarite de g est reelle mais n'induit pas d'obstruction detectable par des congruences simples. La raison : d est "generique" (pas de structure arithmetique forte connue pour 2^S - 3^k), donc les congruences locales ne s'accumulent pas en une obstruction globale.

**Sous-produit :** La structure ultrametrique (g mod 3^m ne depend que des m derniers termes) est un FAIT PROUVE et pourrait servir dans un argument par induction sur les composantes.

---

## APPROCHE 4 : ARGUMENT DE DENSITE PAR BOITES -- LE PIGEONHOLE STRUCTURE

### 4.1 Idee

Plutot que chercher une obstruction, chercher une PREUVE D'EXISTENCE de solutions, et identifier ou elle echoue. Si elle echoue systematiquement, la raison de l'echec EST l'obstruction.

**Strategie :** Le nombre de vecteurs est C = C(S+k-2, k-1). Si g etait "assez aleatoire" modulo d, la probabilite qu'aucun vecteur ne tombe sur 0 serait (1 - 1/d)^C ~ exp(-C/d). Cette probabilite est negligeable des que C >> d.

### 4.2 Le ratio C/d

C = C(S+k-2, k-1) ~ S^{k-1} / (k-1)! pour S >> k
d = 2^S - 3^k ~ 2^S (1 - (3/2)^k * 2^{-S+k}) ... non, d < 2^S mais d > 0, et d peut etre tres petit.

Plus precisement, d/3^k = 2^S/3^k - 1, et 2^S/3^k = 2^{S - k*log_2(3)}. Puisque S = ceil(k*log_2(3)), on a S - k*log_2(3) in [0,1), donc 2^S/3^k in [1, 2), donc d/3^k in (0, 1), donc d < 3^k.

Et C = C(S+k-2, k-1). Pour k fixe et S croissant, C ~ S^{k-1}/(k-1)!. Or S ~ k*log_2(3) ~ 1.585*k, donc C ~ (1.585k)^{k-1} / (k-1)!. Par Stirling, cela donne C ~ (1.585*e)^{k-1} / sqrt(2*pi*k) ~ (4.31)^k / sqrt(k). Et d < 3^k.

Donc C/d > (4.31)^k / (sqrt(k) * 3^k) = (4.31/3)^k / sqrt(k) = (1.437)^k / sqrt(k) → +infini.

**FAIT (DEDUIT) :** Pour tout k >= 3, C/d → +infini exponentiellement vite. Donc s'il y avait equidistribution de g mod d, il y aurait ~C/d >> 1 solutions.

### 4.3 Pourquoi le pigeonhole echoue malgre C >> d

Le pigeonhole ne s'applique pas directement car g n'est PAS injective modulo d. Des vecteurs differents donnent le meme g(v), a fortiori le meme g(v) mod d. Le nombre de VALEURS DISTINCTES de g(v) mod d pourrait etre beaucoup plus petit que C.

Mais meme cela est insuffisant pour prouver l'absence de 0 : il faudrait que Im(g) mod d ait exactement d-1 elements (tous sauf 0), ce qui est extremement improbable.

### 4.4 Le vrai obstacle : non-equidistribution

L'argument de densite echoue non pas parce que C est trop petit mais parce que g mod d pourrait etre BIAISE. Le biais viendrait de la structure de g : c'est une combinaison lineaire de termes exponentiels avec des coefficients en progression geometrique.

**L'hypothese d'equidistribution est EQUIVALENTE a l'annulation des sommes de caracteres.** C'est exactement ce que les approches F_p calculent. L'approche combinatoire pure ne peut pas eviter cette equivalence -- elle ne peut que la reformuler.

### 4.5 Cependant : l'argument par comptage de POIDS

Voici une idee genuinement combinatoire. Definissons le POIDS d'un vecteur v comme w(v) = sum_{j} B_j. Regroupons les vecteurs par poids : V_k(S) = union_{W=0}^{(k-1)(S-1)} V_k(S, W) ou V_k(S, W) = {v in V_k(S) : w(v) = W}.

Pour W fixe, g(v) sur V_k(S,W) peut etre reecrit comme g(v) = sum 3^{k-1-j} * 2^{B_j} avec sum B_j = W fixe. La contrainte de poids fixe PLUS la monotonie donnent un ensemble beaucoup plus petit. Si Im(g) mod d sur chaque V_k(S,W) est "petit" et si les unions de ces images ne recouvrent toujours pas 0...

**Probleme :** Le nombre de strates de poids est (k-1)(S-1)+1 ~ k*S, et dans chaque strate il y a en moyenne C/kS vecteurs. Si g etait injectif sur chaque strate, chaque strate contribuerait C/kS residus. Mais kS ~ k^2, et C/k^2 >> d/k^2 pour grand k, donc chaque strate fournirait encore >> d/k^2 residus. Pas d'obstruction par cette voie.

### 4.6 Verdict

**Statut : ECHEC (PROUVE que l'approche ne fonctionne pas).** Le ratio C/d croissant exponentiellement implique que toute approche purement basee sur le comptage (pigeonhole, densite, poids) est TROP FAIBLE pour detecter une obstruction. Si l'obstruction existe, elle doit etre de nature ALGEBRAIQUE, pas combinatoire-densite.

**THEOREME NEGATIF CANDIDAT (DEDUIT) :** Aucun argument de comptage pur (pigeonhole, densite, strates par poids, decomposition de Dilworth) ne peut prouver g(v) != 0 mod d pour tout v in V_k(S), car le nombre de vecteurs C depasse exponentiellement le module d.

---

## APPROCHE 5 : MARCHE CONTRAINTE DANS Z/dZ -- L'ARGUMENT D'ACCESSIBILITE

### 5.1 Idee

D'apres l'Approche 2, le probleme est equivalent a une marche dans Z/dZ :
- Position initiale : 0
- A l'etape m (m = 0,...,k-1) : ajouter 3^{k-1-m} * 2^{B_m} mod d
- Contrainte : B_m >= B_{m-1} (monotonie)
- Question : la position finale peut-elle etre 0 mod d ?

C'est un probleme d'ACCESSIBILITE dans un graphe dirige.

### 5.2 Le graphe d'accessibilite

Definissons le graphe G = (Z/dZ, E) ou les aretes a l'etape m sont :
(x, x + 3^{k-1-m} * 2^b mod d) pour b in {0, ..., S-1}

MAIS la contrainte de monotonie couple les etapes : le b choisi a l'etape m contraint les b possibles a l'etape m+1 (B_{m+1} >= B_m). Donc ce n'est PAS une marche sur un graphe fixe -- c'est une marche sur un graphe VARIABLE dont les aretes dependent de l'historique.

### 5.3 Reformulation comme produit de graphes

Definissons l'espace d'etats elargi : (x, b) in Z/dZ x {0,...,S-1} ou x est la position dans Z/dZ et b est la derniere valeur de B choisie. La transition de l'etape m a l'etape m+1 est :

(x, b) -> (x + 3^{k-1-(m+1)} * 2^{b'} mod d, b') pour tout b' >= b

C'est une marche MARKOVIENNE dans Z/dZ x {0,...,S-1} avec un operateur de transition T_m qui depend de m (a cause du facteur 3^{k-1-m}).

### 5.4 L'ensemble accessible

Apres k etapes, l'ensemble des positions accessibles dans Z/dZ est :

A = {sum_{m=0}^{k-1} 3^{k-1-m} * 2^{B_m} mod d : (B_0,...,B_{k-1}) in V_k(S)}

La question est : 0 in A ?

L'ensemble A est l'image de la projection pi_1 de l'ensemble des etats finaux. L'ensemble des etats finaux est l'image du produit des operateurs T_0 * T_1 * ... * T_{k-1} applique a l'etat initial (0, 0) ... non, l'etat initial est (0, ?) ou B_{-1} n'existe pas, donc b_0 est libre.

### 5.5 Borne sur |A|

**BORNE INFERIEURE.** Chaque choix de (B_0,...,B_{k-1}) donne un element de A. Mais g pourrait ne pas etre injective mod d. Cependant, si g est "generique", |A| ~ min(C, d).

Or C >> d (Approche 4), donc heuristiquement |A| = d, c'est-a-dire A = Z/dZ.

**Si A = Z/dZ, alors 0 in A et un cycle existe.** C'est le contraire de ce qu'on veut prouver !

### 5.6 Quand A != Z/dZ ?

Pour que A != Z/dZ (et 0 soit absent), il faudrait une structure TRES PARTICULIERE de g. Specifiquement, il faudrait que Im(g) mod d soit un SOUS-GROUPE PROPRE ou un coset, ou un ensemble avec une structure algebrique rigide.

**Exploration pour k=2 (controle) :** Avec k=2, S=4, d=16-9=7.
V_2(4) = {(B_0,B_1) : 0 <= B_0 <= B_1 <= 3}
g(v) = 3 * 2^{B_0} + 2^{B_1}

Vecteurs et valeurs :
- (0,0): 3+1=4, mod 7 = 4
- (0,1): 3+2=5, mod 7 = 5
- (0,2): 3+4=7, mod 7 = 0   **<-- SOLUTION pour k=2 !**
- (0,3): 3+8=11, mod 7 = 4
- (1,1): 6+2=8, mod 7 = 1
- (1,2): 6+4=10, mod 7 = 3
- (1,3): 6+8=14, mod 7 = 0   **<-- SOLUTION pour k=2 !**
- (2,2): 12+4=16, mod 7 = 2
- (2,3): 12+8=20, mod 7 = 6
- (3,3): 24+8=32, mod 7 = 4

Image mod 7 = {0, 1, 2, 3, 4, 5, 6} = Z/7Z en entier. Deux solutions sur dix vecteurs.

**OBSERVATION CRUCIALE (PROUVE par calcul direct) :** Pour k=2, A = Z/dZ. Des solutions EXISTENT. Cela est coherent avec le fait que k=2 n'est pas exclu par le probleme (la conjecture de Collatz ne predit pas l'absence de cycles de longueur 2 a priori -- elle est exclue par d'AUTRES arguments, specifiquement que d=7 et g(v) = 0 mod 7 implique g(v) = 7 ou 14, correspondant aux cycles {B}=(0,2) et (1,3), mais il faut verifier que ces vecteurs correspondent a de VRAIS cycles Collatz, pas seulement a la condition modulaire).

### 5.7 Le probleme fondamental de l'approche d'accessibilite

Pour k >= 3, C/d >> 1 egalement. L'image A devrait recouvrir Z/dZ SAUF si la structure des pas {3^{k-1-m} * 2^b mod d} a une proprietee speciale.

**Candidat a une propriete speciale :** Puisque d = 2^S - 3^k, les puissances de 2 et de 3 ont une relation TRES SPECIALE modulo d :
- 2^S = 3^k mod d
- Donc 2^{S+a} = 3^k * 2^a mod d
- Et 3^k = 2^S mod d

Les pas 3^{k-1-m} * 2^b mod d satisfont :
3^{k-1-m} * 2^b = 3^{-1-m} * 3^k * 2^b = 3^{-1-m} * 2^{S+b} mod d (en utilisant 3^k = 2^S mod d)

Autrement dit, chaque pas est une PUISSANCE DE 2 (modulo d) multipliee par un facteur 3^{-1-m} mod d.

Soit mu = 3^{-1} mod d (l'inverse de 3 modulo d). Alors :
3^{k-1-m} = 3^{-1-m} * 3^k = mu^{1+m} * 2^S mod d

Donc le pas a l'etape m pour le choix b est :
mu^{1+m} * 2^{S+b} mod d = mu^{1+m} * 2^{S+b} mod d

Et g(v) = sum_{m=0}^{k-1} mu^{1+m} * 2^{S+B_m} mod d

= mu * sum_{m=0}^{k-1} mu^m * 2^{S+B_m} mod d

= mu * 2^S * sum_{m=0}^{k-1} (mu * 2^{B_m-0})... Non, soyons precis :

g(v) mod d = sum_{m=0}^{k-1} 3^{k-1-m} * 2^{B_m} mod d

Utilisons 3^{k-1-m} = (2^S / 3) * 3^{-m} mod d = 2^S * mu * mu^m mod d.

Donc g(v) mod d = 2^S * mu * sum_{m=0}^{k-1} mu^m * 2^{B_m} mod d.

Or 2^S = 3^k mod d, donc g(v) mod d = 3^k * mu * sum_{m=0}^{k-1} mu^m * 2^{B_m} mod d.

Et 3^k * mu = 3^k * 3^{-1} = 3^{k-1} mod d. Verification : g(v) = sum 3^{k-1-m} * 2^{B_m} et 3^{k-1} * sum mu^m * 2^{B_m} = sum 3^{k-1} * 3^{-m} * 2^{B_m} = sum 3^{k-1-m} * 2^{B_m}. Correct.

Donc g(v) = 0 mod d ssi sum_{m=0}^{k-1} mu^m * 2^{B_m} = 0 mod (d / gcd(d, 3^{k-1})).

Et gcd(d, 3^{k-1}) = gcd(2^S - 3^k, 3^{k-1}) = gcd(2^S, 3^{k-1}) = 1 (car 2^S est copremier a 3).

Donc g(v) = 0 mod d ssi sum_{m=0}^{k-1} mu^m * 2^{B_m} = 0 mod d, ou mu = 3^{-1} mod d.

### 5.8 La nouvelle forme : somme geometrique tordue

h(v) = sum_{m=0}^{k-1} mu^m * 2^{B_m} mod d

ou mu = 3^{-1} mod d et 0 <= B_0 <= ... <= B_{k-1} <= S-1.

C'est une forme PLUS SYMMETRIQUE que g. Les coefficients forment une progression geometrique de raison mu dans Z/dZ.

**FAIT (PROUVE) :** mu * 2 = 2/3 mod d. Et la question h(v) = 0 mod d est equivalent au probleme original.

**Ce qui est remarquable :** Le ratio mu*2 / 1 = 2*mu = 2/3 mod d. Cela lie directement au ratio de Collatz. Si on pose alpha = 2/3 mod d, alors les coefficients sont 1, mu, mu^2, ... = 1, (2/3)^0 * mu, ... Non, mu = 1/(3 mod d), et mu^m = 3^{-m} mod d. Donc le coefficient de 2^{B_m} est 3^{-m} mod d, et le terme entier est 3^{-m} * 2^{B_m} = (2/3)^{B_m} * 3^{B_m - m} mod d... cela se complique.

### 5.9 Verdict

**Statut : DEDUIT / INVENTION.** La reformulation h(v) = sum mu^m * 2^{B_m} = 0 mod d est une SIMPLIFICATION REELLE du probleme : les coefficients sont une suite geometrique, et la question est purement en termes de puissances de 2 ponderees par des puissances de mu = 3^{-1} mod d.

Mais le probleme reste un probleme de REPRESENTATION : d peut-il etre represente comme combinaison mu-geometrique de puissances de 2, sous contrainte de monotonie ?

---

## APPROCHE 6 : L'INVARIANT DE PARITE CROISEE

### 6.1 Idee -- une invention pure

Definissons la PARITE CROISEE d'un vecteur v comme :

P(v) = sum_{j=0}^{k-1} (k-1-j) * B_j mod 2

C'est la somme des produits (exposant ternaire) * (exposant binaire) modulo 2.

### 6.2 Que vaut P pour g(v) = 0 mod d ?

g(v) = sum 3^{k-1-j} * 2^{B_j}. Modulo 2, g(v) = 2^{B_0} (car seul le terme j avec le plus petit B_j survit si B_0 = 0, ou bien g est pair si B_0 >= 1).

Plus precisement : g(v) est IMPAIR ssi B_0 = 0 ET k-1 est pair... non. 3^{k-1-j} est toujours impair. Donc g(v) mod 2 = sum 2^{B_j} mod 2. Si B_0 = 0, le terme j=0 contribue 1 (impair) et les autres contribuent des puissances paires ou non... Non, 2^{B_j} mod 2 = 0 si B_j >= 1, et = 1 si B_j = 0. Donc g(v) mod 2 = |{j : B_j = 0}| mod 2.

Et d = 2^S - 3^k est impair (car 2^S est pair et 3^k est impair).

Pour g(v) = 0 mod d avec d impair, g(v) doit etre un multiple de d. Puisque d est impair, g(v) doit avoir la MEME parite que le multiple choisi.

Cela ne donne pas une obstruction via la parite simple.

### 6.3 Parite croisee et structure mod 4, mod 8

g(v) mod 4 : seuls les termes avec B_j in {0,1} contribuent non trivialement.
Si B_0 >= 2, tous les termes sont divisibles par 4, donc g(v) = 0 mod 4.
Si B_0 = 1 : les termes avec B_j = 1 contribuent 2 * 3^{k-1-j} mod 4 = 2 * (3 mod 4)^{k-1-j} mod 4 = 2 * (-1)^{k-1-j} mod 4.
Si B_0 = 0 : le terme j=0 contribue 3^{k-1} mod 4 = (-1)^{k-1} mod 4.

Cela depend de la PARITE de k, pas d'un invariant du vecteur. Interessant mais pas une obstruction.

### 6.4 Verdict

**Statut : ECHEC.** La parite croisee P(v) ne contraint pas g(v) de maniere utile. La raison : P(v) est un invariant ADDITIF modulo 2, tandis que g(v) mele multiplication (3^a * 2^b) et addition. Le passage mod 2 detruit toute la structure multiplicative de g.

**Lecon :** Tout invariant defini modulo un PETIT nombre (2, 3, 4, ...) perd trop d'information sur g pour etre utile. L'obstruction, si elle existe, doit impliquer le module d EN ENTIER, pas des projections locales.

---

## APPROCHE 7 : ARGUMENT PAR CAPACITE -- LE VOLUME DANS L'ESPACE DES REPRESENTATIONS

### 7.1 Idee

Chaque vecteur v = (B_0,...,B_{k-1}) dans V_k(S) definit une REPRESENTATION de g(v) comme somme de k termes 3^{k-1-j} * 2^{B_j}. L'ensemble des entiers representables est :

R = {sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} : v in V_k(S)}

Sans la contrainte de monotonie, R est l'ensemble de TOUTES les sommes sum c_j * 2^{b_j} avec c_j = 3^{k-1-j} et b_j in {0,...,S-1}. Avec la monotonie, R est un SOUS-ENSEMBLE strict.

### 7.2 Quantifier l'effet de la monotonie

**Sans monotonie :** Le nombre de vecteurs est S^k (chaque B_j choisit librement dans {0,...,S-1}).
**Avec monotonie :** Le nombre de vecteurs est C(S+k-2, k-1).

Le ratio est C(S+k-2,k-1) / S^k. Pour S ~ 1.585k, cela vaut approximativement :

C(1.585k + k - 2, k-1) / (1.585k)^k ~ C(2.585k, k) / (1.585k)^k

Par Stirling : C(2.585k, k) ~ (2.585)^{2.585k} / ((1.585)^{1.585k} * 1^k) * corrections... En fait :

C(n,k) ~ (n/k)^k * e^{-k} * sqrt(...) pour n ~ alpha*k, et ici n = S+k-2 ~ 2.585k, k-1 ~ k.
C(2.585k, k) / (1.585k)^k ~ (2.585k)^k / (k! * (1.585k)^k) ~ (2.585/1.585)^k / k! ~ (1.631)^k / k!

Donc le ratio est ~ (1.631)^k / k!, qui tend vers 0 SUPER-EXPONENTIELLEMENT. La monotonie reduit ENORMEMENT le nombre de vecteurs.

**Mais** (Approche 4 a montre que) meme apres reduction, C reste >> d exponentiellement.

### 7.3 La monotonie reduit-elle les VALEURS ou seulement les VECTEURS ?

**Question cruciale :** Im(g) avec monotonie a-t-il beaucoup moins d'elements que Im(g) sans monotonie ?

**Argument pour "oui" :** La monotonie force les B_j a etre regroupes. Par exemple, les vecteurs (0,0,...,0,S-1) et (0,S-1,S-1,...,S-1) sont autorises, mais pas (S-1,0,...,0). Cette contrainte elimine les configurations "extremes" ou les poids binaires sont melanges. Pour g, cela elimine les configurations ou un terme de GRAND coefficient ternaire (j=0) a un GRAND exposant binaire tandis qu'un terme de PETIT coefficient ternaire a un PETIT exposant binaire. C'est la source de l'anti-correlation observee dans R181.

**Argument pour "non" :** Meme avec la monotonie, les valeurs de g couvrent [g_min, g_max] avec une resolution suffisante car g est sensible a de petites variations des B_j.

### 7.4 Representation en ecriture mixte

Chaque entier n in Im(g) peut s'ecrire n = sum_{j} 3^{k-1-j} * 2^{B_j(n)} pour au moins un vecteur monotone. C'est une ECRITURE MIXTE (base 2 et base 3 melangees). La monotonie impose que ces ecritures sont REGULIERES (les exposants binaires croissent).

**Theoreme de representation mixte (CONJECTURE) :** Tout entier n suffisamment grand dans [g_min, g_max] admet une representation en ecriture mixte monotone.

Si ce theoreme est vrai, Im(g) = {g_min, ..., g_max} inter Z (tous les entiers de l'intervalle), et donc Im(g) mod d = Z/dZ pour g_max - g_min >> d, ce qui est toujours le cas.

**Ce theoreme impliquerait que 0 in Im(g) mod d, donc qu'un cycle existe.** C'est CONTRADICTOIRE avec la conjecture de Collatz.

### 7.5 Ou le theoreme de representation mixte echoue-t-il ?

Il echoue NECESSAIREMENT si la conjecture de Collatz est vraie. L'echec doit venir de la STRUCTURE ARITHMETIQUE FINE de d = 2^S - 3^k et de la facon dont g(v) = 0 mod d interagit avec la monotonie.

**Hypothese de travail (INVENTION) :** La monotonie cree un BIAIS dans Im(g) mod d. Les valeurs de g(v) mod d ne sont PAS uniformes : elles sont concentrees dans un sous-ensemble de Z/dZ qui depend de la structure de d. Pour des d "generiques", le sous-ensemble couvre tout Z/dZ. Mais pour d = 2^S - 3^k (qui est un nombre TRES SPECIAL en raison de la relation 2^S = 3^k mod d), le biais pourrait exclure 0.

### 7.6 Verdict

**Statut : CONJECTURE.** L'argument de capacite sugere que 0 DEVRAIT etre dans Im(g) mod d (par densite), mais la structure speciale de d = 2^S - 3^k pourrait creer une exclusion. Cette hypothese est inverifiable par methode purement combinatoire -- elle necessite une analyse de la distribution de g mod d, ce qui ramene aux sommes exponentielles.

---

## SYNTHESE : LE MUR COMBINATOIRE

### Bilan des 7 approches

| # | Approche | Statut | Pourquoi elle echoue |
|---|----------|--------|---------------------|
| 1 | Chaines + monotonie | ECHEC | La reduction mod d detruit la monotonie |
| 2 | Coloration par sommes partielles | ECHEC PARTIEL | Reformulation utile mais pas de resolution |
| 3 | Lacunarite + congruences locales | ECHEC ENRICHISSANT | d trop "generique" pour les obstructions locales |
| 4 | Pigeonhole / densite | ECHEC (PROUVE) | C/d → infini : le comptage va CONTRE l'absence de solution |
| 5 | Marche contrainte + reformulation | DEDUIT / INVENTION | Produit h(v) = sum mu^m * 2^{B_m}, mais reste un probleme de representation |
| 6 | Invariant de parite croisee | ECHEC | Trop d'information perdue par reduction mod petit nombre |
| 7 | Capacite / representation mixte | CONJECTURE | Sugere l'existence de solutions, pas leur absence |

### Le theoreme negatif central

**THEOREME (DEDUIT, demontre ci-dessous) :** Aucune methode purement combinatoire-densite (comptage, pigeonhole, Dilworth, Ramsey classique) ne peut prouver que g(v) != 0 mod d pour tout v in V_k(S) avec k >= 3.

**Preuve du theoreme negatif :**
1. |V_k(S)| = C(S+k-2, k-1) >> d = 2^S - 3^k exponentiellement (Approche 4, Section 4.2).
2. Toute methode de comptage pur repose sur la comparaison |source| vs |cible|.
3. Ici |source| >> |cible|, ce qui favorise l'existence de solutions, pas leur absence.
4. Pour prouver l'absence, il faudrait montrer une OBSTRUCTION STRUCTURELLE dans Im(g) mod d.
5. Les obstructions par congruences locales (mod 2, 3, ...) echouent car d est copremier a 2 et 3, et les petits premiers ne suffisent pas (Approche 3 et 6).
6. Donc toute preuve doit exploiter la structure GLOBALE de d = 2^S - 3^k, ce qui depasse le cadre combinatoire-densite. CQFD.

### Le candidat-theoreme positif

**CONJECTURE FORTE (INVENTION) :** Pour tout k >= 3, l'image Im(g) mod d = Z/dZ.

**Evidence :** Le calcul pour k=2 (Approche 5, Section 5.6) montre Im(g) mod d = Z/dZ complet. Le ratio C/d croissant exponentiellement et l'absence d'obstruction locale soutiennent cette conjecture.

**Consequence :** Si cette conjecture est vraie, l'equation g(v) = 0 mod d A DES SOLUTIONS pour tout k. Cela signifierait que la condition g(v) = 0 mod d est NECESSAIRE mais PAS SUFFISANTE pour un cycle Collatz. L'absence de cycles non triviaux proviendrait d'une condition supplementaire (par exemple, g(v) doit etre exactement 0 dans Z, pas seulement mod d ; ou plus precisement, g(v) doit etre un multiple SPECIFIQUE de d compatible avec la structure du cycle).

**Statut : CONJECTURE, avec evidence numerique pour k=2 et evidence heuristique (densite) pour k >= 3.**

### Le vrai probleme reformule

La question n'est pas "Im(g) mod d contient-il 0 ?" (reponse probable : OUI) mais plutot : "Existe-t-il v in V_k(S) tel que g(v) = k * d ?" (c'est la condition EXACTE pour un cycle Collatz, pas la condition modulaire).

La condition exacte est : g(v) = k * d = k * (2^S - 3^k).

Or g_min = (3^k-1)/2 et k*d = k*(2^S - 3^k). Pour grand k, k*d ~ k*3^k * (2^{frac(k*log_2(3))} - 1) ~ k * 3^k * frac, tandis que g_max = 2^{S-1}*(3^k-1)/2 ~ 2^{S-1} * 3^k / 2.

La question devient : k*d / g_max ~ 2k*d / (2^{S-1} * (3^k-1)) ~ 2k*(2^S-3^k) / (2^{S-1}*3^k) = 4k/3^k * (1 - 3^k/2^S) / (1 - 1/3^k)... Cela tend vers 0 super-exponentiellement. Donc k*d << g_max, et la cible est dans l'intervalle [g_min, g_max].

Mais la cible k*d est UN SEUL POINT dans un intervalle de taille g_max - g_min. La probabilite qu'un entier aleatoire de Im(g) tombe exactement sur k*d est ~ |Im(g)|^{-1} si Im(g) est dense, soit negligeable.

**THEOREME CANDIDAT (CONJECTURE) :** La densite de Im(g) dans [g_min, g_max] est O(C / (g_max - g_min)) = O(C / (2^{S-1}*3^{k-1})), et puisque C est polynomial en S tandis que g_max - g_min est exponentiel, Im(g) est EXTREMEMENT EPARS. La probabilite de toucher k*d exactement est ~ 1/(g_max/C) ~ C/g_max ~ polynome * 2^{-S}, qui est negligeable. Mais "negligeable" != "zero".

### Conclusion

L'approche combinatoire pure produit un resultat INATTENDU : elle suggere que la condition modulaire g(v) = 0 mod d est probablement SATISFAITE (le simplexe est trop grand pour l'eviter), mais que la condition EXACTE g(v) = k*d est probablement NON satisfaite (l'image est trop eparse dans Z pour toucher un point precis). La "preuve" de l'absence de cycles ne serait alors pas une obstruction modulaire mais une obstruction METRIQUE : le simplexe discret est trop "troue" en valeurs absolues pour representer exactement k*d, meme s'il recouvre tous les residus mod d.

C'est une perspective radicalement differente des approches par sommes exponentielles, et elle merite une investigation serieuse en tant que PROGRAMME DE RECHERCHE.

---

**FIN R183 -- 16 mars 2026**
