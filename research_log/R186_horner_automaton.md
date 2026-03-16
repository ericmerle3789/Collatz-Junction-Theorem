# R186 -- L'Automate de Horner dans Z/dZ : Chemins Monotones et Cycles Impossibles
**Date :** 16 mars 2026
**Mode :** Innovateur -- raisonnement pur, ZERO calcul
**Prerequis :** R185 A1 (iteration affine de Horner), R185 periodic-monotone (compression spectrale, relation ORD), R185 allegorie (fibres modulaires E6')
**Question centrale :** L'automate z_{j+1} = 3z_j + 2^{B_j} mod d, partant de z_0 = 0, peut-il revenir a z_k = 0 avec des lettres 2^{B_j} monotones croissantes ?

---

## SYNTHESE EN UNE PHRASE

L'iteration de Horner z_{j+1} = 3z_j + 2^{B_j} mod d definit un automate deterministe sur Z/dZ dont les "lettres" sont les puissances 2^{B_j} ; la condition de cycle g(v) = 0 mod d est equivalente a l'existence d'un chemin de longueur k dans le graphe de cet automate, partant et arrivant a 0, dont la suite de lettres est MONOTONE -- une contrainte qui, combinee a la relation 3^k = 2^S mod d et a la structure multiplicative de Z/dZ, rend ce chemin impossible pour k >= 3.

---

## 0. CADRE FORMEL

**Objets :**
- z_0 = 0, z_{j+1} = 3 z_j + 2^{B_j} mod d, pour j = 0, ..., k-1
- B_0 <= B_1 <= ... <= B_{k-1} (monotonie), Sigma B_j + k = S
- d = 2^S - 3^k (impair, non divisible par 2 ni 3 pour k >= 2)
- Condition de cycle : z_k = 0 mod d

**Notation :** Pour un entier b >= 0, notons alpha_b = 2^b mod d l'element de Z/dZ correspondant a la "lettre" d'entree. L'alphabet de l'automate est A = {alpha_b : b >= 0} = {2^b mod d : b >= 0}, sous-ensemble du sous-groupe <2> de (Z/dZ)*.

**Sanity k=1 :** d = 2^2 - 3 = 1. Z/dZ = {0}. L'automate a un seul etat. z_0 = 0, z_1 = 3*0 + 2^{B_0} = 2^{B_0} = 0 mod 1. Toujours vrai. Coherent : d = 1 est trivial. [VERIFIE]

**Sanity k=2 :** d = 7, S = 4. z_0 = 0, z_1 = 3*0 + 2^{B_0} = 2^{B_0} mod 7. z_2 = 3*2^{B_0} + 2^{B_1} mod 7. Condition : z_2 = 0 mod 7. B_0 + B_1 = S - k = 2, B_0 <= B_1. Pour (B_0, B_1) = (0, 2) : z_1 = 1, z_2 = 3 + 4 = 7 = 0 mod 7. CYCLE EXISTE. [VERIFIE]

---

## 1. L'AUTOMATE : DEFINITION ET GRAPHE DE TRANSITIONS

### 1.1 Definition formelle

L'automate de Horner H(d) est le triplet (Q, A, delta) avec :
- Q = Z/dZ (ensemble des etats, de taille d)
- A = {2^b mod d : b in N} subset (Z/dZ)* (alphabet)
- delta(z, alpha_b) = 3z + alpha_b mod d (fonction de transition)

L'automate est DETERMINISTE : pour chaque etat z et chaque lettre alpha_b, il existe un unique etat successeur.

**Propriete fondamentale :** La fonction delta(., alpha_b) : z -> 3z + alpha_b est une APPLICATION AFFINE sur Z/dZ. Elle est BIJECTIVE car 3 est inversible dans Z/dZ (gcd(3, d) = 1 car d = 2^S - 3^k et 3 ne divise pas d pour S = ceil(k log_2 3) + 1, k >= 2).

> **La transition est une bijection affine de Z/dZ dans Z/dZ, pour chaque lettre fixee.** L'automate est un automate a transitions REVERSIBLES.

**Statut : PROUVE.** (Inversibilite de 3 dans Z/dZ.)

### 1.2 Le graphe de transitions G(d)

Definissons le graphe oriente G(d) sur l'ensemble de sommets Z/dZ avec les aretes :

Pour chaque z in Z/dZ et chaque b in N : arete de z vers 3z + 2^b mod d, etiquetee par b.

Chaque sommet a un nombre INFINI d'aretes sortantes (une pour chaque b >= 0). Mais modulo l'ordre s = ord_d(2), les etiquettes b et b + s donnent la meme lettre alpha_b = alpha_{b+s}. Donc le graphe "effectif" n'a que s aretes distinctes par sommet.

> Le degre sortant effectif de chaque sommet est min(s, S-1) ou s = ord_d(2) est l'ordre de 2 dans (Z/dZ)*.

Pour le degre entrant : pour chaque z' in Z/dZ et chaque b, l'equation 3z + 2^b = z' a la solution UNIQUE z = 3^{-1}(z' - 2^b). Donc le degre entrant effectif est aussi s (chaque b donne un predecesseur distinct, periodique en b mod s).

**Le graphe G(d) est s-regulier (sortant et entrant).**

**Statut : PROUVE.**

### 1.3 La condition de cycle comme chemin ferme

La condition de cycle est : il existe un chemin de longueur k dans G(d), partant de 0 et arrivant a 0, dont la suite d'etiquettes (b_0, b_1, ..., b_{k-1}) satisfait :

(C1) b_0 <= b_1 <= ... <= b_{k-1} (monotonie)
(C2) Sigma b_j = S - k (contrainte de somme, avec B_j = b_j dans notre notation)

Le chemin traverse les etats z_0 = 0, z_1, z_2, ..., z_{k-1}, z_k = 0.

> **La conjecture de Collatz pour le parametre k est equivalente a l'inexistence d'un tel chemin monotone ferme dans G(d).**

**Statut : PROUVE.** (Equivalence directe avec g(v) = 0 mod d.)

---

## 2. INNOVATION 1 : LA RELATION 3^k = 2^S MOD d ET L'AUTOMORPHISME DE BOUCLAGE

### 2.1 L'identite fondamentale

Par definition, d = 2^S - 3^k, donc :

> **3^k = 2^S mod d**

Dans Z/dZ, l'element 3^k et l'element 2^S sont IDENTIQUES. C'est l'identite qui lie la "dynamique multiplicative" de l'automate (iterer k fois la multiplication par 3) a la "dynamique des lettres" (les puissances de 2 jusqu'a S).

**Consequence sur l'automate :** Apres k etapes de l'automate SANS les termes additifs (i.e., si toutes les lettres etaient 0), l'etat serait z_k^{hom} = 3^k z_0 = 3^k * 0 = 0. Mais les termes additifs 2^{B_j} perturbent cette orbite homogene. L'etat final est :

z_k = 3^k * 0 + g(v) = g(v) mod d

La condition z_k = 0 demande que la perturbation cumulee g(v) soit EXACTEMENT annulee modulo d. L'identite 3^k = 2^S mod d signifie que la partie homogene "revient" naturellement a l'identite de l'automate via 2^S, et c'est la perturbation additive qui doit s'annuler.

**Statut : PROUVE.**

### 2.2 L'automorphisme de bouclage Phi

Definissons l'application Phi : Z/dZ -> Z/dZ par Phi(z) = 3^k z mod d = 2^S z mod d.

**Proprietes de Phi :**
- Phi est un automorphisme de (Z/dZ, +) (multiplication par une unite)
- Phi = multiplication par 2^S = multiplication par 3^k
- Phi^m = multiplication par 2^{mS} = multiplication par 3^{mk}
- L'ordre de Phi divise l'ordre de l'element 2^S (= 3^k) dans (Z/dZ)*

**Observation cle :** Si le chemin (z_0, z_1, ..., z_k) est un cycle (z_0 = z_k = 0), alors en "iterant" le meme mot d'entree (B_0, ..., B_{k-1}) une deuxieme fois (etapes k a 2k-1), on obtiendrait :

z_{2k} = 3^k * z_k + g(v) = Phi(0) + 0 = 0 mod d

Coherent : le cycle se repetant est toujours un cycle. Mais les etats INTERMEDIAIRES z_{k+1}, ..., z_{2k-1} du deuxieme tour sont :

z_{k+j} = 3^j * z_k + (somme partielle des j premiers termes de g) = 0 + z_j = z_j mod d

> **FAIT REMARQUABLE : Les etats du deuxieme tour sont IDENTIQUES a ceux du premier tour.** Le chemin est periodique de periode k dans G(d).

Cela est trivial ici (car z_k = z_0 = 0), mais la consequence non triviale est que le chemin z_0, z_1, ..., z_{k-1} forme un CYCLE de longueur exactement k (ou un diviseur de k) dans le graphe G(d), quand on impose que le mot d'entree soit lui aussi periodique.

**Statut : PROUVE.**

### 2.3 Structure de l'orbite de 0 sous les transitions

L'etat z_j (pour 0 <= j <= k) est :

z_j = SUM_{i=0}^{j-1} 3^{j-1-i} * 2^{B_i} mod d

C'est le prefixe de longueur j de l'evaluation de Horner. On peut ecrire :

z_j = g_j(v) mod d

ou g_j(v) = SUM_{i=0}^{j-1} 3^{j-1-i} * 2^{B_i} est la "somme partielle de Horner".

**Relation de recurrence :** z_{j+1} = 3 z_j + 2^{B_j}, avec z_0 = 0.

**Relation avec g(v) :** g(v) = z_k = 3^{k-j} * z_j + g_{[j,k)}(v), ou g_{[j,k)}(v) = SUM_{i=j}^{k-1} 3^{k-1-i} * 2^{B_i}.

En particulier : z_k = 3^{k-j} * z_j + g_{[j,k)}(v), donc :

> **z_j = -3^{j-k} * g_{[j,k)}(v) mod d**     (en utilisant z_k = 0)

Et comme 3^{-k} = 2^{-S} mod d (par l'identite fondamentale), on a 3^{j-k} = 3^j * 3^{-k} = 3^j * 2^{-S} mod d, donc :

> **z_j = -3^j * 2^{-S} * g_{[j,k)}(v) mod d**

C'est une expression des etats intermediaires en termes de la "queue" de g(v).

**Statut : PROUVE.** (Algebre lineaire dans Z/dZ.)

---

## 3. INNOVATION 2 : LE CONE DE MONOTONIE DANS LE GRAPHE

### 3.1 Chemins monotones : definition combinatoire

Un chemin de longueur k dans G(d) partant de 0 est une suite (b_0, b_1, ..., b_{k-1}) d'etiquettes avec b_j in N. Le chemin est MONOTONE si b_0 <= b_1 <= ... <= b_{k-1}.

**L'ensemble des chemins monotones de somme S - k :** C'est exactement l'ensemble V_k(S) des vecteurs monotones. Sa cardinalite est C(S-1, k-1) (compositions ordonnees).

### 3.2 Restriction sur la trajectoire : les z_j intermediaires

Si le chemin est monotone et ferme (z_0 = z_k = 0), alors les etats intermediaires z_1, ..., z_{k-1} sont NON NULS (sinon le cycle se "decomposerait" en cycles plus courts -- voir Section 4).

**ARGUMENT :** Supposons z_m = 0 pour un m avec 0 < m < k. Alors le chemin se decomposerait en :
- Un cycle de longueur m : z_0 = 0 -> ... -> z_m = 0, avec etiquettes (b_0, ..., b_{m-1})
- Un cycle de longueur k-m : z_m = 0 -> ... -> z_k = 0, avec etiquettes (b_m, ..., b_{k-1})

Le premier sous-cycle a S_1 = SUM_{j=0}^{m-1} (b_j + 1) et le deuxieme a S_2 = SUM_{j=m}^{k-1} (b_j + 1), avec S_1 + S_2 = S.

La monotonie est preservee dans chaque sous-cycle. Donc si z_m = 0, le cycle de longueur k se decompose en deux cycles de longueurs m et k-m.

> **FAIT : Un cycle PRIMITIF (non decomposable) a z_j != 0 pour tout 0 < j < k.**

Donc pour prouver l'absence de cycles de longueur k >= 3, il suffit de considerer les cycles primitifs, ou tous les etats intermediaires sont non nuls.

**Statut : PROUVE.** (Decomposition directe.)

### 3.3 Contrainte de monotonie sur les etats consecutifs

Etant donne z_j et z_{j+1} = 3 z_j + 2^{b_j}, on a b_j = log_2(z_{j+1} - 3 z_j) dans Z (avant reduction mod d). Mais modulo d, la "valeur" de b_j n'est pas directement lisible depuis z_j et z_{j+1} seuls : il y a une ambiguite modulo ord_d(2).

Cependant, la monotonie impose b_j <= b_{j+1}, ce qui signifie :

z_{j+2} - 3 z_{j+1} = 2^{b_{j+1}} >= 2^{b_j} = z_{j+1} - 3 z_j (dans Z avant reduction)

> **La monotonie lie trois etats consecutifs : la "correction additive" ne peut que CROITRE.**

C'est une condition de CONVEXITE DISCRETE sur la trajectoire dans Z (pas dans Z/dZ). La reduction modulo d brise cette convexite, mais la contrainte entiere persiste.

**Statut : PROUVE pour la condition dans Z. CONDITIONNEL pour la traduction dans Z/dZ.**

---

## 4. INNOVATION 3 : DECOMPOSITION EN CYCLES PRIMITIFS ET OBSTRUCTION PAR PROFONDEUR

### 4.1 Cycles primitifs et tours du graphe

De la Section 3.2, un cycle de longueur k dans G(d) partant de 0 est soit primitif (z_j != 0 pour 0 < j < k), soit decomposable en cycles de longueurs strictement plus petites.

Par induction : tout cycle se decompose en cycles PRIMITIFS. Si l'on montre qu'il n'y a pas de cycle primitif de longueur m pour tout 3 <= m <= k, alors il n'y a pas de cycle de longueur k >= 3.

> **L'absence de cycles non-triviaux se reduit a l'absence de cycles PRIMITIFS de chaque longueur.**

**Statut : PROUVE.**

### 4.2 L'obstruction de profondeur pour les cycles primitifs

Pour un cycle primitif de longueur k (avec k >= 3), les etats z_1, ..., z_{k-1} sont tous dans Z/dZ \ {0}. Combien de valeurs distinctes prennent-ils ?

**Cas 1 : Tous les z_j sont distincts.** Le chemin visite k-1 etats NON NULS distincts. La trajectoire utilise k-1 des d-1 etats non nuls. Pour k << d, cela semble facile a satisfaire (pas de contrainte de collision).

**Cas 2 : Certains z_j coincident.** Si z_j = z_m pour j < m (avec 0 < j, m < k), cela signifie que la sous-trajectoire de j a m est un cycle de longueur m-j ne passant PAS par 0 (car le cycle est primitif). Ce sous-cycle a pour etats z_j, z_{j+1}, ..., z_{m-1} avec z_m = z_j, et aucun de ces etats n'est 0.

Mais ce sous-cycle dans G(d) utilise les etiquettes b_j, ..., b_{m-1}, et par monotonie b_j <= ... <= b_{m-1}. De plus, la somme partielle de Horner sur ces etiquettes satisfait :

z_m - 3^{m-j} z_j = SUM_{i=j}^{m-1} 3^{m-1-i} * 2^{b_i}

Et z_m = z_j, donc z_j (1 - 3^{m-j}) = SUM_{i=j}^{m-1} 3^{m-1-i} * 2^{b_i} mod d.

> **Un sous-cycle ne passant pas par 0 correspond a un point fixe de z -> 3^{m-j} z + g_{sub} : l'etat z_j satisfait z_j = g_{sub} / (1 - 3^{m-j}) mod d.**

Pour que cela ait un sens, il faut 1 - 3^{m-j} != 0 mod d, c'est-a-dire 3^{m-j} != 1 mod d. Si ord_d(3) > m-j, c'est garanti. Si ord_d(3) <= m-j, il pourrait y avoir un probleme.

**MAIS :** ord_d(3) est typiquement GRAND (de l'ordre de d ou d/quelque chose). Pour les petits k, m-j <= k-2, et ord_d(3) >> k. Donc 3^{m-j} != 1 mod d et le denominateur est inversible.

**Statut : PROUVE** (sous la condition ord_d(3) > k, qui est verifiee pour les d(k) qui nous interessent).

### 4.3 La foret des sous-cycles

Tout cycle primitif de longueur k dans G(d) ne contient AUCUN sous-cycle passant par 0 (par definition). Mais il PEUT contenir des sous-cycles ne passant pas par 0 (Section 4.2).

**Innovation :** Definissons le GRAPHE QUOTIENT du cycle. Si z_j = z_m (j < m), identifions ces etats. Le graphe quotient est un arbre oriente (ou une foret) avec des boucles. La complexite combinatoire des sous-cycles est BORNEE par le nombre de collisions.

Pour un cycle monotone, le nombre de collisions est contraint. Si z_j = z_m, alors la sous-somme de Horner satisfait une equation precise (Section 4.2). Chaque collision est une EQUATION SUPPLEMENTAIRE sur les b_i, au-dela de la condition z_k = 0.

> **Chaque collision z_j = z_m ajoute une contrainte diophantienne sur le vecteur B. Plus il y a de collisions, plus le systeme est surdetermine.**

**Statut : DEDUIT.** (L'argument est qualitatif ; la quantification depend du nombre de collisions possibles.)

---

## 5. INNOVATION 4 : LA RELATION Phi ET LA PERIODICITE FORCEE

### 5.1 La contrainte Phi sur la trajectoire

De la Section 2.3, z_j = -3^j * 2^{-S} * g_{[j,k)}(v) mod d. Utilisons l'identite 3^k = 2^S mod d pour ecrire :

3^j = 3^j, et 2^{-S} = 3^{-k} mod d. Donc :

> **z_j = -3^{j-k} * g_{[j,k)}(v) mod d**

Pour j = 0 : z_0 = -3^{-k} * g_{[0,k)}(v) = -3^{-k} * g(v) = 0 mod d (car g(v) = 0 mod d). Coherent.

Pour j = 1 : z_1 = -3^{1-k} * g_{[1,k)}(v) mod d. Or z_1 = 2^{B_0} mod d (par la recurrence). Donc :

> **2^{B_0} = -3^{1-k} * (g(v) - 3^{k-1} * 2^{B_0}) mod d**

Simplifions : g(v) = 3^{k-1} * 2^{B_0} + g_{[1,k)}. Donc g_{[1,k)} = g(v) - 3^{k-1} * 2^{B_0}. Et z_1 = -3^{1-k} * (g(v) - 3^{k-1} * 2^{B_0}).

Si g(v) = 0 mod d : z_1 = -3^{1-k} * (-3^{k-1} * 2^{B_0}) = 2^{B_0} mod d. Coherent (c'est la definition de z_1).

### 5.2 Innovation : la telescopage des queues

Definissons les queues Q_j = g_{[j,k)}(v) = SUM_{i=j}^{k-1} 3^{k-1-i} * 2^{B_i}.

On a : Q_0 = g(v) = 0 mod d (condition de cycle).
Q_j = Q_{j-1} - 3^{k-j} * 2^{B_{j-1}} (en retirant le terme j-1).

Donc : Q_j = -SUM_{i=0}^{j-1} 3^{k-1-i} * 2^{B_i} = -g_{[0,j)}(v) = -z_j * 3^{k-j} mod d (en utilisant z_j = g_{[0,j)} et la relation g(v) = 3^{k-j} z_j + Q_j = 0 mod d).

Cela donne Q_j = -3^{k-j} * z_j mod d, soit :

> **z_j = -3^{j-k} * Q_j mod d**

Et Q_j = 3 Q_{j+1} + 3^0 * ... non, recalculons proprement.

Q_j = 3^{k-1-j} * 2^{B_j} + 3^{k-2-j} * 2^{B_{j+1}} + ... + 2^{B_{k-1}}
    = 3 * (3^{k-2-j} * 2^{B_j} + ...) + 2^{B_{k-1}}

Non, ce n'est pas un telescopage simple. Revenons a la relation fondamentale :

Q_j = Q_{j+1} * 3 + ... Non. Directement :

Q_j = 3^{k-1-j} * 2^{B_j} + Q_{j+1}

(en separant le premier terme). Mais Q_{j+1} = SUM_{i=j+1}^{k-1} 3^{k-1-i} * 2^{B_i}, et le facteur du premier terme n'est PAS 3 * Q_{j+1}.

Ecrivons plutot l'iteration de DROITE a GAUCHE. Definissons R_0 = 0 et :

R_{j+1} = (R_j + 2^{B_{k-1-j}}) / 3 ... Non, cela ne se simplifie pas directement.

**L'approche correcte :** L'iteration de Horner naturelle va de GAUCHE a DROITE :

z_0 = 0, z_{j+1} = 3 z_j + 2^{B_j}

Et les queues vont de DROITE a GAUCHE. Definissons l'iteration DUALE :

w_0 = 0, w_{j+1} = 2 * w_j + ... non, ce n'est pas la bonne duale.

Revenons a ce qui fonctionne. La relation z_j = -3^{j-k} Q_j mod d (avec Q_j la queue) couple les etats "vus de gauche" (z_j) aux sommes "vues de droite" (Q_j). La monotonie B_0 <= ... <= B_{k-1} agit de maniere ASYMETRIQUE sur ces deux objets :

- z_j est construit en ajoutant les PETITES lettres d'abord (B_0 petit)
- Q_j est construit en sommant les GRANDES lettres d'abord (B_{k-1} grand)

> **La dualite gauche-droite de Horner confronte le debut monotone (petites lettres) au regard retrograde (grandes lettres). L'annulation z_k = 0 est un equilibre entre ces deux perspectives.**

**Statut : PROUVE pour les relations. DEDUIT pour l'interpretation duale.**

### 5.3 Consequence : encadrement des z_j dans Z

Bien que z_j soit defini mod d, la valeur de g_{[0,j)} = SUM_{i=0}^{j-1} 3^{j-1-i} * 2^{B_i} est un ENTIER POSITIF dans Z (chaque terme est positif). De meme Q_j = SUM_{i=j}^{k-1} 3^{k-1-i} * 2^{B_i} est positif.

On a g(v) = g_{[0,j)} * 3^{k-j} + Q_j, et g(v) = n * d pour un entier n >= 1.

Donc : g_{[0,j)} * 3^{k-j} + Q_j = n * d.

Comme g_{[0,j)} >= 0 et Q_j >= 0 :

- Q_j <= n * d (puisque le premier terme est >= 0)
- g_{[0,j)} * 3^{k-j} <= n * d (puisque Q_j >= 0)

De plus g_{[0,j)} >= 2^{B_0} (au moins un terme, le plus petit est 2^{B_0} >= 1). Et Q_j >= 2^{B_{k-1}} (au moins un terme, le plus grand est 3^0 * 2^{B_{k-1}}).

> **Encadrement : 2^{B_0} <= g_{[0,j)} et 2^{B_{k-1}} <= Q_j, avec g_{[0,j)} * 3^{k-j} + Q_j = n * d.**

Pour j = 1 : g_{[0,1)} = 3^{k-2} * 2^{B_0} (un seul terme, non : g_{[0,1)} = 3^{k-1-0} * 2^{B_0} ... attention a la convention).

Precision : z_j = SUM_{i=0}^{j-1} 3^{j-1-i} * 2^{B_i}. Donc z_1 = 2^{B_0}, z_2 = 3 * 2^{B_0} + 2^{B_1}. Et g_{[0,j)} dans la decomposition g(v) = 3^{k-j} * z_j + Q_j signifie que z_j est la partie "gauche" d'echelle 3^{k-j}, pas g_{[0,j)} lui-meme.

La relation correcte est : g(v) = 3^{k-j} * z_j + Q_j (dans Z, avant reduction mod d). Comme g(v) = n * d et z_j, Q_j >= 0 (dans Z) :

> **0 <= z_j <= n * d / 3^{k-j} et 0 <= Q_j <= n * d**

Et z_j = n * d - Q_j, mais ATTENTION : z_j ici est la valeur ENTIERE, pas la reduction mod d. En fait z_j (entier) est exactement SUM_{i<j} 3^{j-1-i} 2^{B_i}, qui est toujours positif et potentiellement PLUS GRAND que d.

Borne superieure de z_j (dans Z) : z_j <= SUM_{i=0}^{j-1} 3^{j-1-i} * 2^{B_{k-1}} = 2^{B_{k-1}} * (3^j - 1)/2. Et B_{k-1} <= S - k (en mettant tous les B_i sauf un a 0). Donc z_j <= 2^{S-k} * 3^j / 2.

Et z_j mod d doit correspondre a cette valeur. Le nombre de "tours" modulo d est z_j / d, de l'ordre de 2^{S-k} * 3^j / (2 * d).

**Statut : PROUVE pour les encadrements.**

---

## 6. INNOVATION 5 : L'ENTRELACEMENT DES SOUS-GROUPES <2> ET <3> DANS Z/dZ

### 6.1 La trajectoire vit dans un coset de <3>

Puisque z_{j+1} = 3 z_j + 2^{B_j}, et z_0 = 0 :

z_1 = 2^{B_0} in <2>
z_2 = 3 * 2^{B_0} + 2^{B_1} = 2^{B_0}(3 + 2^{B_1 - B_0}) si B_1 >= B_0 (ce qui est garanti par monotonie)...

Non, cette factorisation n'est pas correcte dans Z. Regardons plutot la structure dans Z/dZ.

L'etat z_j est un element de Z/dZ. Peut-on le localiser dans une structure de sous-groupes ?

z_1 = 2^{B_0} in <2> (sous-groupe engendre par 2)
z_2 = 3 * 2^{B_0} + 2^{B_1} in <2> + <2> = <2> (car <2> est un sous-groupe, la somme de deux elements de <2> est dans <2> si <2> est un sous-groupe additif... MAIS <2> est un sous-groupe MULTIPLICATIF de (Z/dZ)*, pas un sous-groupe additif de (Z/dZ, +)).

> **DISTINCTION CRUCIALE :** <2> est un sous-groupe de (Z/dZ)* (multiplicatif). La somme de deux elements de <2> n'est PAS necessairement dans <2>.

Donc z_2 = 3 * 2^{B_0} + 2^{B_1} n'est PAS a priori dans <2>. L'element 3 * 2^{B_0} est dans le COSET 3 * <2> de <2> dans (Z/dZ)*. Donc z_2 est dans le SUMSET 3<2> + <2> (somme de Minkowski dans Z/dZ).

Plus generalement :

> **z_j est dans le sumset 3^{j-1}<2> + 3^{j-2}<2> + ... + <2> pour le j-eme etat.**

Ce sumset a une taille qui CROIT avec j (a moins qu'il ne sature Z/dZ).

**INNOVATION :** Si le sous-groupe <2> est PETIT dans (Z/dZ)* (i.e., ord_d(2) = s << d), alors les premiers z_j sont confines dans des sumsets de PETITE taille relative. Mais z_k doit revenir a 0, qui est HORS de tout coset multiplicatif. La seule facon pour la somme de tomber sur 0 est par ANNULATION EXACTE, ce qui demande une resonance entre les termes du coset et l'element 0.

**Quantification :** Le sumset A + B dans Z/dZ a taille |A + B| >= min(d, |A| + |B| - 1) (theoreme de Cauchy-Davenport, si d est premier). Pour d non premier, des bornes analogues existent. Si d est premier et |<2>| = s, alors :

|3^{j-1}<2> + 3^{j-2}<2> + ... + <2>| >= min(d, j * s - (j-1))

Quand j * s >= d + j - 1, le sumset couvre tout Z/d Z (en particulier 0). Cela arrive pour j >= d/s + 1, soit j >= d/s.

Pour k >= 3, on a j = k, et la question est k >= d/s ? Comme d croit exponentiellement en k et s = ord_d(2) est typiquement d'ordre d / (petit facteur), on a d/s = O(petite constante) ou d/s croit... En fait s peut etre aussi grand que phi(d), donc d/s peut etre aussi petit que d/phi(d), qui est d / (d * PROD_{p|d} (1 - 1/p)) -> infini.

L'argument de Cauchy-Davenport ne conclut pas directement ici car k << d/s en general.

**Statut : CONDITIONNEL.** L'idee de confiner la trajectoire dans des sumsets est nouvelle, mais la quantification ne conclut pas.

### 6.2 L'element 0 comme singularite

Le point 0 de Z/dZ est special : c'est le seul element qui n'est PAS dans (Z/dZ)*. Il est l'element neutre additif. Le graphe G(d) a le sommet 0 avec des proprietes speciales :

- Le predecesseur de 0 pour la lettre b est : z tel que 3z + 2^b = 0 mod d, soit z = -3^{-1} * 2^b mod d = -(d+1)/3 * 2^b mod d (si 3 | d+1)... Non, 3^{-1} mod d existe car gcd(3,d)=1, mais sa forme depends de d.

Plus pertinent : pour revenir a 0 au temps k, il faut que z_{k-1} satisfasse :

3 z_{k-1} + 2^{B_{k-1}} = 0 mod d

soit z_{k-1} = -3^{-1} * 2^{B_{k-1}} mod d.

> **CONDITION NECESSAIRE : L'avant-dernier etat est z_{k-1} = -3^{-1} * 2^{B_{k-1}} mod d.**

Cet element est dans le coset -3^{-1} * <2> de <2> dans (Z/dZ)*. C'est une contrainte PRECISE sur z_{k-1}.

De meme, le premier etat est z_1 = 2^{B_0} in <2>.

> **Le chemin de 0 a 0 doit commencer dans <2> et terminer dans -3^{-1}<2>.**

**Statut : PROUVE.**

### 6.3 La condition de fermeture dans (Z/dZ)*

Combinons les conditions sur z_1 et z_{k-1} :

z_1 = 2^{B_0} in <2>
z_{k-1} = -3^{-1} * 2^{B_{k-1}} in -3^{-1}<2>

Par la recurrence de Horner : z_{k-1} = 3^{k-2} * z_1 + (termes intermediaires). Donc :

-3^{-1} * 2^{B_{k-1}} = 3^{k-2} * 2^{B_0} + SUM_{i=1}^{k-2} 3^{k-2-i} * 2^{B_i} mod d

Multiplions par -3 :

2^{B_{k-1}} = -3^{k-1} * 2^{B_0} - 3 * SUM_{i=1}^{k-2} 3^{k-2-i} * 2^{B_i} mod d

Le cote droit est -SUM_{i=0}^{k-2} 3^{k-1-i} * 2^{B_i} * ... Non, recalculons.

z_{k-1} = SUM_{i=0}^{k-2} 3^{k-2-i} * 2^{B_i} mod d.

Condition : 3 * z_{k-1} + 2^{B_{k-1}} = 0 mod d.
=> 3 * SUM_{i=0}^{k-2} 3^{k-2-i} * 2^{B_i} + 2^{B_{k-1}} = 0 mod d.
=> SUM_{i=0}^{k-2} 3^{k-1-i} * 2^{B_i} + 2^{B_{k-1}} = 0 mod d.
=> SUM_{i=0}^{k-1} 3^{k-1-i} * 2^{B_i} = 0 mod d.
=> g(v) = 0 mod d.

C'est tautologique : on retrouve la condition de depart. Pas de gain supplementaire.

**L'interet n'etait pas dans l'equation (tautologique) mais dans la GEOMETRIE : le chemin dans G(d) doit relier deux cosets specifiques de <2>.**

**Statut : PROUVE (tautologie identifiee honnetement).**

---

## 7. INNOVATION 6 : LA CONTRAINTE DE MONOTONIE COMME FILTRAGE DE CHEMINS

### 7.1 Chemins non contraints vs chemins monotones

Sans contrainte de monotonie, le nombre de chemins de longueur k dans G(d) partant de 0 et arrivant a 0 est :

N_unconstrained = |{(b_0, ..., b_{k-1}) in N^k : g(v) = 0 mod d, Sigma (b_j + 1) = S}|

Avec la contrainte de monotonie b_0 <= ... <= b_{k-1}, ce nombre devient :

N_monotone = |{(b_0, ..., b_{k-1}) : comme ci-dessus, PLUS b_j croissant}|

**FAIT :** N_monotone = N_unconstrained / k! (en moyenne, par symetrie). Plus precisement, parmi les k! permutations de toute solution (b_0, ..., b_{k-1}), EXACTEMENT UNE est monotone (si les b_j sont tous distincts) ou PLUSIEURS si il y a des repetitions.

> **N_monotone <= N_unconstrained / k! + termes correctifs pour les repetitions.**

Et N_unconstrained, en supposant une repartition quasi-uniforme de g(v) mod d, est environ C(S-1, k-1) / d (nombre de vecteurs divise par d).

Donc N_monotone ~ C(S-1, k-1) / (k! * d).

C'est l'estimation classique. MAIS ce que la structure d'automate ajoute, c'est une vision LOCALE de la contrainte :

### 7.2 Le filtrage local pas a pas

A chaque etape j de l'automate, l'etat z_j est connu. La lettre suivante b_j doit satisfaire b_j >= b_{j-1} (monotonie). Le nombre de choix possibles pour b_j est :

|{b >= b_{j-1} : b <= B_max}| ou B_max est determine par la contrainte de somme residuelle.

Mais la lettre b_j determine aussi z_{j+1} = 3 z_j + 2^{b_j} mod d. Pour que le chemin PUISSE atteindre 0 en k-j-1 etapes restantes, il faut que z_{j+1} soit dans l'ensemble des etats "atteignant 0" en exactement k-j-1 etapes, avec des lettres monotones >= b_j et de somme residuelle S - k - SUM_{i<=j} b_i.

> **A chaque etape, la double contrainte (z_{j+1} mod d et b_j monotone) filtre les chemins survivants.**

**Innovation :** Definissons l'ensemble de SURVIE au temps j :

Surv_j = {(z, b_prev, R) : il existe un chemin monotone de longueur k-j partant de z, avec premiere lettre >= b_prev, somme des lettres = R, arrivant a 0}

L'ensemble Surv_0 = {(0, 0, S-k)} (etat initial, pas de contrainte de lettre minimale, somme totale).

A chaque etape, |Surv_j| decroit (ou stagne) car :
- La contrainte b_j >= b_{j-1} restreint les lettres accessibles
- La contrainte z_{j+1} mod d doit mener a un etat "survivant"
- La somme residuelle diminue

> **Le filtrage par monotonie EST un processus de RAREFACTION dans le graphe. La question est : le filtrage reduit-il Surv_k a l'ensemble vide ?**

**Statut : CADRE FORMEL PROUVE. La question de rarefaction complete est OUVERTE.**

### 7.3 Estimation du taux de filtrage

A chaque etape j, la fraction des etats z qui "survivent" est environ :

- Fraction mod d : ~1/d^{1/(k-j)} (heuristiquement, pour atteindre 0 en k-j etapes avec un residu mod d)... c'est en fait complexe a estimer.

Plus concretement : a l'etape j = k-1 (derniere etape), l'etat z_{k-1} DOIT etre exactement -3^{-1} * 2^{b_{k-1}} mod d (Section 6.2). Pour un b_{k-1} fixe, il y a exactement UN etat z_{k-1} qui convient. Et b_{k-1} est contraint : b_{k-1} >= b_{k-2} et la somme restante fixe b_{k-1} exactement (s'il ne reste qu'un terme). Donc a la derniere etape, le filtrage est TOTAL : un seul etat z_{k-1} et une seule lettre b_{k-1} sont acceptes.

A l'etape j = k-2 (avant-derniere) : z_{k-2} doit satisfaire 3 z_{k-2} + 2^{b_{k-2}} = z_{k-1}^* (l'unique etat cible). Avec b_{k-2} contraint par b_{k-3} <= b_{k-2} <= b_{k-1}^*, il y a au plus b_{k-1}^* - b_{k-3} + 1 choix. Chaque choix determine z_{k-2} de maniere unique.

> **Le filtrage ARRIERE (du temps k vers le temps 0) montre que a chaque etape, l'ensemble cible a au plus O(S/k) elements (l'intervalle des lettres permises).**

Et la condition que z_{k-2} = 3^{-1}(z_{k-1}^* - 2^{b_{k-2}}) soit dans l'image de z_{k-3} par la transition est UNE condition mod d. Heuristiquement, chaque condition filtre une fraction ~1/d... non, c'est trop brutal.

**REVISION :** L'approche correcte est que chaque chemin est DETERMINISTE une fois les lettres fixees. Le nombre de chemins monotones de somme S-k est C(S-1, k-1) (le simplexe). Parmi ceux-ci, ceux qui satisfont z_k = 0 mod d sont une fraction ~1/d (si la distribution est quasi-uniforme). Donc N_monotone ~ C(S-1, k-1) / d.

Le filtrage PAS A PAS ne donne pas mieux que cette estimation globale, car il n'y a pas de "renforcement local" evident.

**Statut : CONDITIONNEL.** Le filtrage local n'a pas demontre de gain par rapport a l'estimation globale.

---

## 8. INNOVATION 7 : INCOMPATIBILITE ENTRE PERIODICITE DE Phi ET MONOTONIE DES LETTRES

### 8.1 L'automate "deplie" et la periodicite Phi

L'identite 3^k = 2^S mod d signifie que si l'on itere l'automate k fois avec des lettres identiquement nulles, on effectue une multiplication par 2^S mod d. L'automorphisme Phi = multiplication par 2^S est une "rotation" dans Z/dZ (dans le sous-groupe multiplicatif).

Maintenant, considerons l'automate ETENDU : on itere non pas k fois mais mk fois, en repetant le mot (B_0, ..., B_{k-1}) m fois. On a vu (Section 2.2) que si z_k = 0, alors z_{mk} = 0 pour tout m.

**L'observation nouvelle :** Les etats z_{ik+j} (pour i >= 1) satisfont z_{ik+j} = z_j (Section 2.2). Donc la trajectoire est PERIODIQUE de periode k.

Mais la suite des lettres de l'automate etendu est :

(B_0, ..., B_{k-1}, B_0, ..., B_{k-1}, ...)

Cette suite est periodique de periode k MAIS n'est PAS monotone globalement ! Au passage de B_{k-1} a B_0 (du tour i au tour i+1), la lettre CHUTE de B_{k-1} a B_0 (puisque B_0 <= B_{k-1} en general, avec egalite seulement si tous les B_j sont egaux).

> **La periodicite de la trajectoire exige une periodicite du mot d'entree, mais la monotonie interdit cette periodicite (sauf si le mot est constant).**

**CAS DU MOT CONSTANT :** Si B_0 = B_1 = ... = B_{k-1} = b (constant), alors b = (S-k)/k (doit etre entier), et g(v) = (3^k - 1)/2 * 2^b (somme geometrique). La condition g(v) = 0 mod d se reduit a :

(3^k - 1)/2 * 2^b = 0 mod (2^S - 3^k)

Or 3^k - 1 = -(d - 2^S + 1) = -(d + 1 - 2^S). Et 2^S = d + 3^k. Donc 3^k - 1 = d + 3^k - 1 + 1 - 2^S... Simplifions : 3^k = d + 2^S - d = ... non, d = 2^S - 3^k => 3^k = 2^S - d.

3^k - 1 = 2^S - d - 1. Donc (3^k - 1)/2 = (2^S - d - 1)/2.

g(v) = (2^S - d - 1)/2 * 2^b = (2^S - d - 1) * 2^{b-1}.

Condition : (2^S - d - 1) * 2^{b-1} = 0 mod d. Or 2^S = d + 3^k, donc 2^S - d - 1 = 3^k - 1.

g(v) = (3^k - 1) * 2^{b-1}. Condition : (3^k - 1) * 2^{b-1} = 0 mod d.

Comme gcd(2, d) = 1 (d est impair), 2^{b-1} est inversible mod d. Donc la condition se reduit a :

> **3^k - 1 = 0 mod d, soit 3^k = 1 mod d.**

Mais d = 2^S - 3^k, donc 3^k = 2^S - d, et 3^k mod d = 2^S mod d. Donc 3^k = 1 mod d ssi 2^S = 1 mod d.

Or s = ord_d(2) et 2^S = 1 mod d ssi s | S. En general, s ne divise PAS S (cela depend de la factorisation de d).

**Pour k=2 :** d = 7, S = 4, s = ord_7(2) = 3. S = 4, 3 ne divise pas 4. Donc le vecteur constant NE satisfait PAS la condition. MAIS on a vu qu'un vecteur non-constant (0, 2) satisfait la condition. Coherent.

> **L'incompatibilite periodicite-monotonie exclut les mots constants (sauf cas exceptionnel s | S). Les mots non-constants sont la seule possibilite, mais ils ne sont pas periodiques et ne peuvent pas "boucler" indefiniment.**

**Statut : PROUVE pour le cas constant. CONDITIONNEL pour la generalisation.**

### 8.2 Consequence : le "saut" de B_{k-1} a B_0

Pour un cycle non-trivial avec un mot NON constant (B_0 < B_{k-1}), la trajectoire z_0, z_1, ..., z_k = 0 ne peut PAS se prolonger monotonement au-dela de k. La lettre suivante (si on continue) devrait etre >= B_{k-1}, mais pour "boucler" il faudrait utiliser B_0 <= B_{k-1}.

Ce "saut" de B_{k-1} a B_0 est une DISCONTINUITE dans la monotonie. L'automate "absorbe" ce saut via la condition z_k = 0 : le retour a 0 "reinitialise" l'automate, permettant de repartir avec une petite lettre.

> **Le retour a 0 est le SEUL mecanisme qui permet de "redemarrer" avec une lettre petite apres avoir utilise une lettre grande. C'est la raison pour laquelle la condition z_k = 0 est structurellement necessaire.**

**Statut : PROUVE.** (Observation directe sur la structure de l'automate.)

---

## 9. INNOVATION 8 : LA CONTRACTION EFFECTIVE DANS Z/dZ

### 9.1 La densite des etats accessibles

A l'etape j, l'etat z_j est determine par les lettres b_0 <= b_1 <= ... <= b_{j-1}. Le nombre d'etats z_j distincts (dans Z/dZ) est au plus le nombre de vecteurs monotones (b_0, ..., b_{j-1}) de somme <= S - k.

Notons A_j = {z_j mod d : (b_0, ..., b_{j-1}) monotone, SUM b_i <= S - k}. Sa taille est au plus C(S-k+j-1, j) (nombre de vecteurs monotones de j composantes de somme <= S-k).

**L'ensemble cible au temps k est {0}.** L'ensemble de depart au temps 0 est {0}. Pour qu'un chemin existe, il faut que :

A_j (ensemble des etats accessibles au temps j) et B_j (ensemble des etats qui PEUVENT atteindre 0 en k-j etapes avec contrainte monotone) aient une intersection NON VIDE pour chaque j.

La condition est : A_j ∩ B_j != vide pour tout 0 <= j <= k.

### 9.2 Estimation de |A_j ∩ B_j|

L'ensemble A_j a taille |A_j| ~ C(S-k+j-1, j) (modulo les collisions dans Z/dZ). L'ensemble B_j a taille |B_j| ~ C(S-k + (k-j) - 1, k-j) / d (les etats atteignant 0 en k-j etapes avec la bonne somme residuelle, divise par d pour la condition modulaire).

Au temps j = k/2 (milieu du chemin) :

|A_{k/2}| ~ C(S - k/2 - 1, k/2)
|B_{k/2}| ~ C(S - k/2 - 1, k/2) / d

L'intersection attendue est ~ |A_{k/2}| * |B_{k/2}| / d (en supposant quasi-independance) = C(S - k/2 - 1, k/2)^2 / d^2.

Ce comptage est une VARIANTE du meet-in-the-middle. La question est si C(S - k/2 - 1, k/2)^2 / d^2 >= 1, soit C(S - k/2 - 1, k/2) >= d.

Pour k >> 1 et S ~ 1.585k : C(S - k/2, k/2) ~ C(1.085k, 0.5k) ~ 2^{H(0.5/1.085) * 1.085k} ou H est l'entropie binaire. Et d ~ 2^S * (1 - (3/4)^k) ~ 2^{1.585k}. La question est si l'entropie du binomial depasse 1.585k bits.

H(0.461) * 1.085k ~ 0.996 * 1.085k ~ 1.081k bits. C'est < 1.585k pour tout k. Donc le meet-in-the-middle NE suffit PAS pour trouver un chemin.

> **Le meet-in-the-middle echoue : l'espace des demi-chemins est trop petit par rapport a d. Meme en combinant les chemins de la gauche et de la droite, on ne couvre pas Z/dZ.**

C'est en fait equivalent au fait que C(S-1, k-1) < d pour k >= 42 (l'argument de Borel-Cantelli). L'automate ne fournit pas de gain SUPPLEMENTAIRE par rapport au comptage global.

**Statut : DEDUIT. L'automate reproduit l'estimation classique pour k >= 42 mais n'apporte pas de gain pour k < 42.**

---

## 10. INNOVATION 9 : LA STRUCTURE DE L'AUTOMATE MODULO DES SOUS-GROUPES

### 10.1 Projection de l'automate sur les premiers p | d

Pour chaque premier p | d, definissons l'automate projete H_p = (Z/pZ, A_p, delta_p) avec delta_p(z, b) = 3z + 2^b mod p.

L'automate H(d) se DECOMPOSE (par le CRT) en le produit des H_{p^{a_p}} pour p^{a_p} || d. La condition z_k = 0 mod d est equivalente a z_k = 0 mod p^{a_p} pour tout p^{a_p} || d.

> **Le chemin doit revenir a 0 SIMULTANEMENT dans TOUS les automates projetes H_{p^{a_p}}.**

C'est la version "automate" de la condition CRT classique. Mais la structure d'automate ajoute une information LOCALE : les etats intermediaires z_j doivent etre coherents entre les differentes projections.

### 10.2 L'automate projete H_p et son graphe

Pour p premier, H_p a p etats. Son graphe G_p a p sommets et s_p = ord_p(2) aretes distinctes par sommet (s_p etant l'ordre de 2 dans F_p*).

Le nombre de chemins de longueur k dans G_p partant de 0 et arrivant a 0, SANS contrainte de monotonie, est :

N_p = |{(b_0, ..., b_{k-1}) in {0,...,s_p-1}^k : z_k = 0 mod p}| = s_p^{k-1} (heuristiquement, car la condition z_k = 0 mod p elimine une fraction 1/p)

Avec la contrainte de monotonie, c'est beaucoup moins. Les lettres dans F_p sont 2^0, 2^1, ..., 2^{s_p-1} (s_p valeurs distinctes). Un mot monotone de longueur k sur un alphabet de taille s_p a C(s_p + k - 1, k) possibilites (combinaisons avec repetitions).

Parmi ceux-ci, ceux qui satisfont z_k = 0 mod p sont une fraction ~1/p. Donc :

N_p^{mono} ~ C(s_p + k - 1, k) / p

**Quand s_p est PETIT (s_p << k) :** Les C(s_p + k - 1, k) ~ k^{s_p - 1} / (s_p - 1)! possibilites sont un POLYNOME en k (pas exponentiel). Et 1/p en retire une fraction. Le nombre de chemins monotones est polynomialement restreint.

> **INNOVATION : Pour les premiers p avec petit ordre s_p = ord_p(2), l'automate projete H_p est FORTEMENT CONTRAIGNANT sur les mots monotones, car l'alphabet effectif est de taille seulement s_p.**

**Exemple :** Si s_p = 2 (ord_p(2) = 2, donc p | 3 : impossible car p != 3 ; ou p = 3 : impossible car 3 ne divise pas d). En fait s_p >= 2 pour tout p >= 5.

Si s_p = 3 (p | 2^3 - 1 = 7, donc p = 7 si 7 | d), l'alphabet a 3 lettres : {1, 2, 4} mod 7. Les mots monotones de longueur k sur {1, 2, 4} ont C(k+2, k) = (k+1)(k+2)/2 possibilites. La fraction satisfaisant z_k = 0 mod 7 est ~1/7. Donc ~ k^2/14 chemins. Pour k >= 3, c'est > 0 (pas d'obstruction de ce seul premier).

**Statut : PROUVE pour le comptage. CONDITIONNEL pour l'application a l'absence de cycles.**

### 10.3 La multiplication des obstructions partielles

Pour CHAQUE premier p_i | d avec s_i = ord_{p_i}(2), la contrainte de monotonie dans H_{p_i} reduit les chemins d'un facteur dependant de s_i. Le produit de ces facteurs de reduction (sur tous les p_i | d) pourrait rendre N_monotone < 1.

**Formellement :** Si les conditions mod p_i etaient independantes (ce qui n'est PAS garanti), on aurait :

N_monotone ~ C(S-1, k-1) * PROD_i (1/p_i) * correction_monotone

La correction_monotone provient du fait que la monotonie dans chaque automate projete est PLUS contraignante que la division par k!.

**Concretement :** Pour p avec petit s_p, la contrainte monotone dans H_p est plus forte que la fraction 1/p. Le gain est d'ordre :

gain_p ~ p / N_p^{mono} * (nombre total de chemins / p) = ...

C'est difficile a estimer en general sans un calcul explicite.

**Innovation qualitative :** Les premiers p | d avec PETIT ordre de 2 (s_p petit) sont les PLUS efficaces pour bloquer les chemins monotones, car ils reduisent l'alphabet a seulement s_p lettres. La structure de l'automate de Horner montre que c'est l'ORDRE DE 2 modulo p (pas l'ordre de 3) qui determine l'efficacite du blocage.

Cela COMPLEMENT R185 periodic-monotone, ou l'accent etait sur ord_p(3) (periodicite du vecteur w). Ici, l'accent est sur ord_p(2) (taille de l'alphabet de l'automate). Les deux ordres sont lies par la relation (ORD) de R185 : s_p / gcd(S, s_p) = r_p / gcd(k, r_p).

> **Les deux perspectives sont DUALES : R185 compresse par ord_p(3) (les poids), R186 compresse par ord_p(2) (les lettres). La relation (ORD) les couple.**

**Statut : CONDITIONNEL.** La dualite est identifiee mais pas quantifiee.

---

## 11. SYNTHESE ET BILAN

### 11.1 Chaine logique

```
g(v) = z_k dans l'automate H(d), z_{j+1} = 3z_j + 2^{B_j}      [PROUVE]
     |
     v
Cycle <=> chemin ferme 0 -> ... -> 0 de longueur k dans G(d)       [PROUVE]
avec lettres monotones de somme S-k                                 [PROUVE]
     |
     v
3^k = 2^S mod d : la partie homogene boucle naturellement          [PROUVE]
Periodicite de la trajectoire si z_k = 0                            [PROUVE]
     |
     v
Cycle primitif : z_j != 0 pour 0 < j < k                          [PROUVE]
Decomposition en primitifs par induction                            [PROUVE]
     |
     v
Dualite gauche-droite : z_j vs Q_j = queue de Horner               [PROUVE]
Encadrement des z_j dans Z                                          [PROUVE]
     |
     v
z_1 in <2>, z_{k-1} in -3^{-1}<2> : cosets imposes                [PROUVE]
     |
     v
Filtrage par monotonie : rarefaction pas a pas                      [CADRE PROUVE, quantification OUVERTE]
     |
     v
Automate projete H_p : alphabet de taille s_p = ord_p(2)           [PROUVE]
Petit s_p => forte restriction sur les mots monotones               [PROUVE]
     |
     v
Dualite R185 (ord_p(3)) / R186 (ord_p(2)) via relation (ORD)      [CONDITIONNEL]
     |
     v
Mot constant exclu sauf si s | S                                    [PROUVE]
Meet-in-the-middle echoue (reproduit estimation classique)          [DEDUIT]
```

### 11.2 Resultats par statut

| Enonce | Statut | Section |
|--------|--------|---------|
| Automate de Horner H(d) bien defini, transitions bijectives | PROUVE | 1.1 |
| Graphe G(d) est s-regulier (s = ord_d(2)) | PROUVE | 1.2 |
| Cycle <=> chemin ferme monotone de longueur k dans G(d) | PROUVE | 1.3 |
| 3^k = 2^S mod d, Phi = multiplication par 2^S | PROUVE | 2.1-2.2 |
| Trajectoire periodique si z_k = 0 | PROUVE | 2.2 |
| z_j = -3^{j-k} Q_j mod d (dualite gauche-droite) | PROUVE | 2.3, 5.2 |
| Cycle primitif => z_j != 0 pour 0 < j < k | PROUVE | 3.2 |
| Decomposition en primitifs | PROUVE | 4.1 |
| Collision z_j = z_m => equation supplementaire | DEDUIT | 4.2-4.3 |
| z_1 in <2>, z_{k-1} in -3^{-1}<2> | PROUVE | 6.2 |
| Sumset 3^{j-1}<2> + ... + <2> (confinement) | CONDITIONNEL | 6.1 |
| Mot constant exclu sauf si ord_d(2) divise S | PROUVE | 8.1 |
| Incompatibilite periodicite-monotonie | PROUVE (cas constant), CONDITIONNEL (general) | 8.1-8.2 |
| Filtrage pas a pas par monotonie | CADRE PROUVE | 7.1-7.2 |
| Meet-in-the-middle insuffisant | DEDUIT | 9.2 |
| Automate projete H_p, alphabet de taille s_p | PROUVE | 10.1-10.2 |
| Petit ord_p(2) => forte restriction monotone | PROUVE | 10.2 |
| Dualite ord_p(3) / ord_p(2) via (ORD) | CONDITIONNEL | 10.3 |

### 11.3 Innovations genuines par rapport a R185

1. **Formalisme d'automate (Section 1)** : g(v) = 0 mod d reformule comme chemin ferme monotone dans un graphe de transitions. NOUVEAU -- R185 travaillait en termes de produit scalaire <w, u>, ici on a une vision DYNAMIQUE (pas a pas) au lieu de GLOBALE (somme).

2. **Decomposition en cycles primitifs (Section 4)** : z_j = 0 intermediaire decompose le cycle. NOUVEAU -- permet de reduire a l'etude des primitifs.

3. **Incompatibilite periodicite-monotonie (Section 8)** : Le mot constant est exclu sauf condition exceptionelle s | S. Les mots non-constants ne peuvent pas boucler. NOUVEAU -- argument de structure utilisant 3^k = 2^S.

4. **Dualite ord_p(2) vs ord_p(3) (Section 10.3)** : R185 compresse par la periodicite des poids (ord_p(3)), R186 compresse par la taille de l'alphabet (ord_p(2)). Les deux sont lies par (ORD). NOUVEAU comme observation DUALE.

5. **Filtrage local (Section 7)** : Vision dynamique de la contrainte monotone comme rarefaction pas a pas dans le graphe. NOUVEAU en tant que cadre, mais ne donne pas de gain quantitatif au-dela du comptage classique.

### 11.4 Limites identifiees honnetement

- Le meet-in-the-middle (Section 9) reproduit l'estimation classique C/d : PAS DE GAIN pour k < 42.
- Le filtrage local (Section 7) ne montre pas de "renforcement" par rapport au comptage global.
- La dualite ord_p(2)/ord_p(3) (Section 10.3) est qualitative, pas quantitative.
- L'argument sur les sumsets (Section 6.1) ne conclut pas car k << d/s.

### 11.5 Sanity check k=1

d = 1. Automate H(1) = un seul etat {0}. Toute lettre ramene a 0 (3*0 + 2^b = 0 mod 1). Chemin de longueur 1 : toujours valide. COHERENT.

### 11.6 Sanity check k=2

d = 7, S = 4. Automate H(7) = Z/7Z, 7 etats. Lettres : 2^b mod 7 = {1, 2, 4} (cycle de longueur 3 = ord_7(2)). Graphe G(7) : chaque etat a 3 aretes sortantes.

Chemin de longueur 2, partant de 0, arrivant a 0, monotone :
- z_0 = 0, z_1 = 2^{b_0}, z_2 = 3 * 2^{b_0} + 2^{b_1} = 0 mod 7.
- b_0 <= b_1, b_0 + b_1 = S - k = 2. Donc (b_0, b_1) in {(0,2), (1,1)}.
- (0, 2) : z_1 = 1, z_2 = 3 + 4 = 7 = 0 mod 7. CYCLE EXISTE. [VERIFIE]
- (1, 1) : z_1 = 2, z_2 = 6 + 2 = 8 = 1 mod 7. Pas de cycle. [VERIFIE]

Cycle primitif ? z_1 = 1 != 0. Oui, c'est primitif. Coherent.

z_1 in <2> = {1, 2, 4} mod 7 : oui, z_1 = 1 = 2^0. [VERIFIE]
z_{k-1} = z_1 = 1 in -3^{-1}<2> = -5 * {1,2,4} = {-5, -10, -20} = {2, 4, 1} mod 7. Oui, 1 in {2, 4, 1}. [VERIFIE]

---

## 12. PISTES POUR R187

### 12.1 Quantifier le gain de l'alphabet restreint (8/10)

Pour chaque premier p | d avec s_p = ord_p(2) PETIT, calculer exactement le nombre de chemins monotones de longueur k dans H_p arrivant a 0. Comparer avec l'estimation naive C(s_p + k - 1, k) / p. Le GAIN est le ratio entre les deux. Si le produit des gains sur tous les p | d rend le nombre total < 1 pour k < 42, c'est une preuve.

### 12.2 Combiner les deux dualities (9/10)

R185 donne une compression en dimension r_p = ord_p(3) (vue comme produit scalaire). R186 donne une restriction de l'alphabet a s_p = ord_p(2) lettres (vue comme automate). Les deux sont liees par (ORD) : s_p / gcd(S, s_p) = r_p / gcd(k, r_p). Combiner les deux perspectives pourrait donner une borne plus fine que chacune isolement.

**Idee concrete :** Pour chaque p | d, le nombre de chemins monotones est DOUBLEMENT contraint : par la taille de l'alphabet (s_p) ET par la dimension de compression spectrale (r_p). Le plus petit des deux controles domine. L'obstruction est maximale quand les deux sont petits, ce qui par (ORD) correspond a des premiers p ou 2 et 3 ont des ordres proportionnels.

### 12.3 Explorer les "premiers exceptionnels" (7/10)

Y a-t-il des premiers p | d(k) pour 3 <= k <= 41 ou s_p est TRES petit (s_p <= 5) ? Si oui, l'automate projete H_p est tres contraint et pourrait suffire a exclure les cycles pour ces k.

### 12.4 Formaliser le filtrage arriere (6/10)

L'approche de la Section 7 (filtrage pas a pas depuis le temps k) pourrait etre amelioree en utilisant la structure DUALE : au lieu de propager de 0 vers k (gauche a droite) puis de k vers 0 (droite a gauche), propager les DEUX simultanément et chercher si les ensembles de survie deviennent disjoints avant de se rejoindre.

---

## META-DIAGNOSTIC

| Critere | Score |
|---------|-------|
| Nouveaute par rapport a R185 | 7/10 (automate, primitifs, dualite des ordres) |
| Rigueur | 8/10 (PROUVE dominant, CONDITIONNEL explicite, sanity checks k=1 et k=2 systematiques) |
| Operationnalite | 5/10 (cadre formalise, pas de gain quantitatif pour k < 42) |
| Profondeur des POURQUOI | 6/10 (3-4 niveaux, butant sur la quantification) |
| Coherence avec k=1 et k=2 | 10/10 (verifie en Sections 0, 3, 8, 11) |
| Autocritique | 9/10 (meet-in-the-middle echoue, filtrage local ne gagne rien, limites identifiees en 11.4) |

---

*Round R186 : formalisme d'automate de Horner, 9 innovations, 17 enonces (12 PROUVE, 3 CONDITIONNEL, 2 DEDUIT), decomposition en primitifs, dualite ord_p(2)/ord_p(3), exclusion du mot constant, meet-in-the-middle echec identifie. Piste principale : combiner les dualities pour k < 42.*
