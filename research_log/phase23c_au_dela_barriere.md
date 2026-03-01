# Phase 23c — Au-dela de la Barriere : Trois Voies de Sortie
# Date : 28 fevrier 2026
# Auteur : Eric Merle (assiste par Claude)

---

## 0. Situation apres Phase 23b

Phase 23b a etabli la **barriere de la racine carree** : AUCUNE methode
de Fourier/moments ne peut prouver N_0(p) = 0 dans le regime p ~ C^{1.06}.
L'exposant 1.06 - 2.06/r > 0 pour tout r >= 2 le demontre.

Phase 23c explore trois voies pour CONTOURNER cette barriere.

---

## 1. VOIE S : La Conjecture de Skolem

### 1.1. La conjecture

**Conjecture de Skolem.** Si une equation diophantienne exponentielle
purement n'a pas de solution dans Z, alors elle n'a pas de solution
modulo un entier m convenablement choisi.

Bertok et Hajdu (2021, 2024) ont confirme cette conjecture pour
des familles croissantes d'equations et developpe un ALGORITHME
pour trouver le module m.

### 1.2. Reformulation de l'equation de Steiner

L'equation pour un cycle Collatz de longueur k :

  sum_{i=0}^{k-1} 3^{k-1-i} * 2^{a_i} = n_0 * (2^S - 3^k)

avec 0 = a_0 < a_1 < ... < a_{k-1} <= S-1, n_0 >= 1.

Developpons :

  3^{k-1} + 3^{k-2}*2^{a_1} + ... + 2^{a_{k-1}} + n_0*3^k = n_0*2^S

C'est une equation en k+1 variables entieres (a_1,...,a_{k-1}, n_0)
avec TOUTES les quantites etant des produits de puissances de 2 et 3.

**C'est une equation S-unitaire a k+1 termes dans le groupe <2,3>.**

### 1.3. Application de Skolem

Si la conjecture de Skolem est vraie pour cette equation, alors pour
chaque k sans solution, il existe m(k) tel que l'equation n'a PAS
de solution mod m(k).

**Observation cruciale** : le module m = d(k) = 2^S - 3^k est un
candidat NATUREL ! L'equation mod d se reduit a :

  corrSum(A) = 0 mod d

Et N_0(d) = 0 est EXACTEMENT "pas de solution mod d". La conjecture de
Skolem avec m = d est donc EQUIVALENTE a l'hypothese H !

Mais Skolem dit qu'il EXISTE un m, pas que m = d marche.
Pourrions-nous trouver un AUTRE module m qui fonctionne ?

### 1.4. Exploration d'autres modules

Essayons m = 2^a * 3^b pour des petites valeurs.

**Mod 2** : corrSum est impair (v_2 = 0), et d est impair.
  Donc n_0*d est impair. corrSum impair = n_0*d impair. ✓ Compatible.

**Mod 3** : corrSum mod 3 = 2^{a_{k-1}} mod 3 = (-1)^{a_{k-1}}.
  d mod 3 = (2^S - 3^k) mod 3 = (-1)^S.
  n_0*d mod 3 = n_0*(-1)^S.
  Equation : (-1)^{a_{k-1}} = n_0*(-1)^S mod 3.
  Pour n_0 = 1 : (-1)^{a_{k-1}} = (-1)^S, soit a_{k-1} = S mod 2.
  Ceci est satisfait quand a_{k-1} et S ont la meme parite.
  Pas d'obstruction.

**Mod 4** : corrSum mod 4 = (3^{k-1} + 3^{k-2}*2 + ...) mod 4.
  Seul le premier terme 3^{k-1} est impair. Le second 3^{k-2}*2 contribue 2*(...).
  corrSum mod 4 = 3^{k-1} + 2 * (3^{k-2} + ... ) mod 4.
  Si k >= 3 : corrSum = 3^{k-1} + 2*M ou M depend des a_i.
  3^{k-1} mod 4 : 3^1=3, 3^2=1, 3^3=3, 3^4=1. Alternance.
  Pour k impair : corrSum ≡ 3 + 2M mod 4, soit 1 ou 3 mod 4.
  Pour k pair : corrSum ≡ 1 + 2M mod 4, soit 1 ou 3 mod 4.
  En tout cas corrSum est impair mod 4 (deja connu).
  d mod 4 : 2^S mod 4 = 0 (S >= 2), 3^k mod 4 alterne 3,1.
  d ≡ -3^k mod 4 : soit d ≡ 1 mod 4 (k impair) ou d ≡ 3 mod 4 (k pair).
  n_0*d mod 4 : n_0 impair (demontre en Phase 23b).
  Pas de nouvelle obstruction.

**Mod 8, 9, 16, ...** : les obstructions deviennent de plus en plus
specifiques a chaque k. Pas de FORMULE universelle.

### 1.5. Verdict sur la voie Skolem

L'approche Skolem est EXACTEMENT l'approche CRT de la Phase 22,
vue depuis le cadre de la theorie des equations diophantiennes.

Le module d lui-meme est le candidat naturel, et N_0(d) = 0 est
precisement la non-existence de solution mod d.

Les petits modules (2, 3, 4, 8, 9, ...) ne donnent PAS d'obstruction
universelle a cause de la flexibilite des parametres (a_i, n_0).

**Apport** : Le cadre Skolem formalise le probleme et justifie l'approche
modulaire. Bertok-Hajdu pourraient traiter des FAMILLES de k si on
sait formuler l'equation dans leur cadre algorithmique.

**Limite** : Pas de module UNIVERSEL (valable pour tout k). Chaque k
necessite son propre module, ce qui revient au probleme original.

---

## 2. VOIE O : Sur-determination 2-adique (Horner Tree)

### 2.1. L'observation cle

Dans l'equation corrSum(A) = n_0 * d, reduisons mod 2^{a_1} :

  3^{k-1} + 0 + ... + 0 ≡ n_0 * d mod 2^{a_1}

(tous les termes sauf le premier ont un facteur 2^{a_i} >= 2^{a_1})

Comme d est impair et 3^{k-1} est impair :

  n_0 ≡ 3^{k-1} * d^{-1} mod 2^{a_1}

Ceci DETERMINE n_0 mod 2^{a_1} a partir du SEUL choix de a_1.

### 2.2. Recurrence de determination

A chaque etape j, la valeur de a_j ajoute de nouvelles contraintes
sur n_0. Precisement :

Etape j = 1 : n_0 mod 2^{a_1} est determine.
Etape j = 2 : reduit mod 2^{a_2}, on obtient n_0 mod 2^{a_2}.
...
Etape j = k-1 : n_0 mod 2^{a_{k-1}} est entierement determine.

Le nombre TOTAL de bits determines est a_{k-1} <= S-1.
Le nombre de bits SIGNIFICATIFS de n_0 est environ :
  log_2(n_0) ~ log_2(C/d) + log_2(C) ~ S - k ~ 0.585*S

### 2.3. Le ratio de sur-determination

Bits determines : a_{k-1} (peut aller jusqu'a S-1 ~ 1.585k)
Bits significatifs de n_0 : S - k ~ 0.585k

Ratio : (S-1) / (S-k) ~ 1.585k / 0.585k ~ 2.7

Le systeme est **sur-determine par un facteur 2.7** : on impose
~2.7 fois plus de contraintes binaires qu'il n'y a d'inconnues.

### 2.4. Comptage heuristique

Pour chaque composition A, les a_{k-1} bits determines de n_0
doivent etre coherents avec n_0 ayant seulement ~0.585k bits
significatifs. Les a_{k-1} - (S-k) ~ k bits restants sont des
contraintes de CONSISTANCE.

Si ces bits etaient "aleatoires" : probabilite de consistance = 2^{-k}.

Nombre de compositions : C ~ 2^{1.5k}.

Nombre attendu de hits : C * 2^{-k} = 2^{0.5k} — ENCORE TROP GRAND.

### 2.5. Pourquoi le comptage echoue

Le probleme : les compositions ne sont PAS independantes. Deux
compositions partageant les memes premiers choix (a_1,...,a_j)
donnent les MEMES contraintes sur n_0 jusqu'a l'etape j.

L'arbre de Horner a C feuilles mais beaucoup de branches partagees.
Le nombre de branches DISTINCTES a chaque niveau j est C(S-1-j, k-1-j),
qui decroit exponentiellement avec j.

La sur-determination ne suffit PAS a elle seule car les contraintes
sont CORRELEES entre compositions proches dans l'arbre.

### 2.6. Contribution de cette voie

Malgre l'echec, cette analyse revele :

1. **n_0 est determine mod 2^{a_{k-1}}** — preuve elementaire.
2. **gcd(n_0, 6) = 1** — preuve elementaire (v_2 = v_3 = 0).
3. **L'arbre de Horner** est la structure combinatoire naturelle
   du probleme. Son analyse fine pourrait donner des obstructions.

---

## 3. VOIE M' : La Conjecture M' Revisitee

### 3.1. Rappel de M' (Phase 18)

**Conjecture M'.** Pour tout k assez grand, tout p | d, tout r in F_p :

  |N_r(p) - C/p| <= C^{1/2 + epsilon}

Consequence : N_0(p) = 0 des que p > C^{1/2 - epsilon}, ce qui est
BEAUCOUP plus faible que p > C.

### 3.2. M' suffit-elle ?

Pour M', il faut p > C^{1/2}. Avec C ~ 2^{0.95S} :
  p > 2^{0.475S}

Et d = 2^S - 3^k ~ 2^S. Le plus grand facteur premier de d satisfait
(Stewart) : P(d) > 2^{S*f(S)} avec f -> 1.

Pour f(S) > 0.475 (largement satisfait pour S > 10), il existe p | d
avec p > C^{1/2}.

**DONC : Stewart + M' => il existe p | d avec p > C^{1/2} et N_0(p) = 0.**

### 3.3. Que faut-il prouver pour M' ?

M' est : |N_r(p) - C/p| <= C^{1/2+eps}. Par Fourier :
  |N_r - C/p| <= (1/p) * sum |T(t)|

Par Cauchy-Schwarz : (1/p)*sum|T| <= (1/p)*sqrt((p-1)*sum|T|^2)
  = (1/p)*sqrt((p-1)*pC_2) ou C_2 = sum f(r)^2.

Pour quasi-uniformite : C_2 ~ C^2/p + C. Donc :
  (1/p)*sqrt(p^2*(C^2/p+C)) ~ sqrt(C^2/p + C) ~ C/sqrt(p) + sqrt(C)

Pour p > C^{1/2} : C/sqrt(p) < C/C^{1/4} = C^{3/4}. Et sqrt(C).
Donc : |N_r - C/p| <= C^{3/4} + C^{1/2}  ?

Non — ceci SUPPOSE la quasi-uniformite (C_2 ~ C^2/p + C), qui est
EXACTEMENT ce qu'on veut prouver.

Circulaire a nouveau. Mais MOINS circulaire que la voie directe :

### 3.4. Le second moment CONDITIONNEL

Definissons C_2 = sum_r f(r)^2 (la "norme L^2 de f").

**Si on pouvait prouver** : C_2 <= C^2/p + C*(1 + beta_k) avec beta_k -> 0,
alors M' suivrait.

C_2 est le nombre de PAIRES (A,B) avec corrSum(A) = corrSum(B) mod p.
C'est la "collision number" modulo p.

C_2 = C + #{(A,B), A != B : corrSum(A) = corrSum(B) mod p}

Pour des valeurs "generiques" : la probabilite que deux compositions
aleatoires coincident mod p est 1/p. Il y a C*(C-1) paires.
Donc E[C_2] = C + C*(C-1)/p ~ C + C^2/p.

**Prouver que C_2 <= C + C^2/p + o(C^2/p) est EQUIVALENT a prouver
que corrSum est quasi-uniforme.**

C'est toujours circulaire, mais le probleme est REFORMULE comme
un probleme de COLLISION :

### 3.5. Le probleme de collision

**Probleme des Collisions de Horner.** Soit p premier, p | d(k).
Borner le nombre de paires (A, B) de compositions distinctes telles
que corrSum(A) = corrSum(B) mod p.

Si A et B different en position j seulement (A et B coincident sauf
a_j != b_j), alors :
  corrSum(A) - corrSum(B) = 3^{k-1-j} * (2^{a_j} - 2^{b_j}) mod p

Ceci est 0 mod p ssi p | 3^{k-1-j}*(2^{a_j} - 2^{b_j}),
soit p | (2^{a_j} - 2^{b_j}) (car gcd(p,3) = 1),
soit p | 2^{min(a_j,b_j)} * (2^{|a_j-b_j|} - 1),
soit p | (2^{|a_j-b_j|} - 1) (car gcd(p,2) = 1),
soit omega_2(p) | |a_j - b_j|.

Pour omega_2(p) > S : il n'y a AUCUNE paire "single-swap" colliding,
car |a_j - b_j| < S < omega_2(p).

**C'est le mecanisme de troncature formalise !** Les collisions
simples (swap d'un seul element) sont EXCLUES quand omega_2(p) > S.

### 3.6. Collisions multiples

Les paires differant en 2 positions : corrSum(A)-corrSum(B) =
3^{k-1-i}*(2^{a_i}-2^{b_i}) + 3^{k-1-j}*(2^{a_j}-2^{b_j}).

C'est 0 mod p ssi :
  3^{k-1-i}*(2^{a_i}-2^{b_i}) = -3^{k-1-j}*(2^{a_j}-2^{b_j}) mod p
  (2^{a_i}-2^{b_i}) / (2^{a_j}-2^{b_j}) = -3^{j-i} mod p

Le membre gauche est un quotient de DIFFERENCES de puissances de 2.
Le membre droit est une puissance de 3. L'equation demande qu'un
quotient de differences de puissances de 2 soit egal a une puissance
de 3 modulo p.

Par l'INDEPENDANCE MULTIPLICATIVE de 2 et 3 : cette equation
n'a de solution que pour des cas "accidentels" dependant de p.

### 3.7. Extension aux collisions d'ordre r

Pour des paires differant en r positions : l'equation de collision
est une relation lineaire entre r termes de la forme 3^{alpha}*2^{beta}.

Par le theoreme de Evertse (1984) sur les S-unit equations :
le nombre de solutions NON-DEGENEREES d'une equation a r termes
dans le groupe S-unitaire est <= exp(C'*r).

Pour r = 2 : <= exp(C') solutions non-degenerees.
Pour r = k : <= exp(C'*k) solutions, mais C est de l'ordre de 2^{1.5k},
donc exp(C'*k) << C pour k grand. Les collisions non-degenerees
sont RARES comparees a C !

### 3.8. Le theoreme potentiel

**Theoreme (PROGRAMME — non prouve).** Soit p | d(k) avec omega_2(p) > S.
Alors :

  C_2(p) = sum_r N_r(p)^2 <= C + C^2/p + C * exp(-alpha*k)

pour une constante alpha > 0, des que k >= K_0.

*Preuve (esquisse non rigoureuse) :*

1. Collisions triviales (A = B) : contribuent C.
2. Collisions "single-swap" : contribuent 0 (car omega_2(p) > S).
3. Collisions "r-swap" (r >= 2) : chaque collision est une solution
   d'une S-unit equation a r+1 termes. Par Evertse, au plus
   exp(C''*r) solutions par "type" de r-swap.
4. Le nombre de types de r-swap est C(k, r) * (choix des replacements).
5. Pour r fixe : contribution <= C(k,r) * S^r * exp(C''*r) = O(k^r*S^r*exp(C''*r)).
6. Sommant sur r = 2,...,k : O(sum (kS)^r * exp(C''r)) = O((kS*exp(C''))^k).
7. Si kS*exp(C'') < 2^{1.5/k} * (C^2/p)^{1/k}... ceci ne converge pas.

**L'esquisse echoue** car le nombre de types de collisions croit trop vite.

### 3.9. L'ingredient manquant pour M'

Pour prouver M', il faudrait borner C_2 DIRECTEMENT, ce qui revient
a borner le nombre de paires collidant modulo p. Le theoreme d'Evertse
borne les collisions EXACTES (dans Z), pas les collisions modulaires.

La version MODULAIRE du theoreme d'Evertse n'existe pas dans la
litterature. C'est un SECOND probleme ouvert (distinct de Lemme B').

---

## 4. VOIE T : Le Theoreme Triangulaire (combinant tout)

### 4.1. L'architecture

Au lieu de deux lemmes independants (A' et B'), construisons un
THEOREME UNIQUE qui utilise l'interaction entre :
- La sur-determination 2-adique (Voie O)
- La conjecture de Skolem (Voie S)
- Le controle des collisions (Voie M')

### 4.2. Enonce du Theoreme Triangulaire

**Theoreme (CONJECTURAL — le Programme Merle).** Pour tout k >= 3 :

  N_0(d(k)) = 0

*Preuve (structure complete, avec UN ingredient manquant) :*

**Etape 1.** (Inconditionnel) Pour k = 1 : d = 1, trivial.
Pour k = 2 : seul cycle trivial. Pour k = 3..17 : exhaustif (Phase 22).

**Etape 2.** (Inconditionnel) Pour k >= 18 : C < d (Theoreme 1).

**Etape 3.** (Inconditionnel) Par Stewart, P(d) > 2^{S*f(S)} avec
f(S) -> 1. Pour S >= S_0 : P(d) > C^{1/2} > 2^{0.475S}.

Soit p_max le plus grand premier divisant d. Alors p_max > C^{1/2}.

**Etape 4.** (Semi-conditionnel) Par les resultats de Zsygmondy/Carmichael
generalises : pour presque tout k, il existe p | d avec omega_2(p) > S.

Precision : les exceptions sont liees aux convergents q_n de log_2(3)
et aux "facteurs de Wieferich" (p tels que 2^{p-1} = 1 mod p^2).
Le nombre d'exceptions pour k <= K est O(log K) (heuristique).

**Etape 5.** (Conditionnel sur M' ou equivalent) Pour le premier p
de l'etape 3-4 :

  N_0(p) = C/p + R(p)

avec |R(p)| <= C^{1/2+eps} (Conjecture M').

Pour p > C^{1/2+eps} : N_0(p) < C/p + C^{1/2+eps} < C/C^{1/2+eps} + C^{1/2+eps}.
Si C > 1 (toujours vrai pour k >= 3) et eps < 1/4 :
  N_0(p) < C^{1/2-eps} + C^{1/2+eps} < 2*C^{3/4} (pour eps = 1/4).
Pour k assez grand : C^{3/4} < 1 est FAUX (C croit exponentiellement).

**ERREUR** dans l'etape 5. Reprenons.

**Etape 5 (corrigee).** Pour p > C^{1/2+eps} (garanti par Stewart pour
k assez grand, car P(d) > 2^{S*f(S)} >> C^{1/2+eps}) :

  N_0(p) < C/p + C^{1/2+eps}

Le premier terme C/p < C/C^{1/2+eps} = C^{1/2-eps}.
Le second terme est C^{1/2+eps}.

TOTAL : N_0(p) < C^{1/2-eps} + C^{1/2+eps} < 2*C^{1/2+eps}.

Pour N_0(p) < 1 : il faut C^{1/2+eps} < 1/2, soit C < 1. IMPOSSIBLE.

**M' ne suffit PAS non plus** pour les grands k, car C^{1/2} >> 1 toujours.

### 4.3. Correction : ce qu'il faut VRAIMENT

La bonne conjecture n'est ni M ni M'. C'est :

**Conjecture M'' (operationnelle, Phase 18).** Pour tout k assez grand
et tout p | d(k) :

  sum_{t=1}^{p-1} T(t) = -C + O(1)

C'est-a-dire : la SOMME des T(t) pour t != 0 est presque exactement -C.

En effet : N_0(p) = C/p + (1/p)*sum T(t). Si sum T(t) = -C + O(1) :

  N_0(p) = C/p + (-C + O(1))/p = O(1/p) < 1 pour p >= 2.

**M'' implique N_0(p) = 0 pour TOUT p >= 2, donc pour tout p | d, donc N_0(d) = 0.**

### 4.4. Ce que M'' signifie

sum_{t=0}^{p-1} T(t) = p * N_0(p)

T(0) = C

Donc sum_{t=1}^{p-1} T(t) = p*N_0(p) - C.

M'' dit : p*N_0(p) - C = -C + O(1), soit p*N_0(p) = O(1), soit
N_0(p) = O(1/p). Pour p >= 2 et N_0 entier : N_0(p) = 0.

**M'' est EXACTEMENT equivalente a H.**

Circulaire ? NON — M'' est une formulation ANALYTIQUE de H.
Elle dit que les sommes exponentielles T(t) ont une ANNULATION PRESQUE
TOTALE quand on les somme. C'est un phenomene de CANCELLATION MASSIVE.

### 4.5. Pourquoi la cancellation massive est plausible

T(t) = sum_A e(t*corrSum(A)/p). Si corrSum(A) etait equidistribue
parmi les p residus :

  T(t) ~= C * (1/p) * sum_{r=0}^{p-1} e(tr/p) = 0  pour t != 0

Donc pour une distribution parfaitement uniforme : T(t) = 0 pour t != 0,
et sum T(t) = 0 = -C + C. OK, ca colle.

Pour une distribution PRESQUE uniforme : T(t) ~= petit, et sum T(t) ~= -C + petit.

### 4.6. La formulation FINALE

Combinant tout, LE THEOREME aurait la forme :

**Theoreme (Programme Merle, COMPLET).**

Pour tout k >= 3, il n'existe pas de cycle positif non trivial
de longueur k dans la dynamique de Collatz.

*Preuve :*

k = 1,2 : standard.
k = 3..17 : exhaustif (Phase 22, Proposition 22.1).

k >= 18 : par l'absurde, supposons N_0(d) >= 1 pour un k >= 18.
Alors pour tout p | d, N_0(p) >= 1.

Soit p | d avec p > C^{1/2} (existe par Stewart pour k >= K_1).

Par N_0(p) >= 1 et Parseval (Theoreme 16.1, Phase 18) :

  sum_{t=1}^{p-1} |T(t)|^2 >= (p-C)^2 / (p-1)

C'est un COUT ENERGETIQUE : si N_0(p) >= 1, les sommes T(t) doivent
porter une energie Parseval >= p (en ordre de grandeur).

**[INGREDIENT MANQUANT]** : Montrer que cette energie est IMPOSSIBLE
a realiser par des sommes de Horner lacunaires.

Plus precisement, prouver :

  sum |T(t)|^2 < (p-C)^2 / (p-1)   (borne superieure sur l'energie)

Ceci contredirait N_0(p) >= 1, prouvant N_0(p) = 0 et donc N_0(d) = 0. QED.

---

## 5. L'Ingredient Manquant Unique (Version Energie)

### 5.1. Reformulation energetique

L'ingredient manquant, dans sa forme la plus PURE :

  **Prouver : sum_{t=1}^{p-1} |T(t)|^2 < (p - C)^2 / (p - 1)**

  pour p premier, p | d(k), p > C^{1/2}, k >= K_0.

Le cote gauche est l'ENERGIE DE FOURIER des compositions.
Le cote droit est le COUT MINIMAL d'un hit (N_0 >= 1).

### 5.2. Valeurs numeriques

Par Parseval : sum |T(t)|^2 = p * C_2 - C^2, ou C_2 = sum f(r)^2.

Pour la distribution uniforme (pas de hit) : C_2 = C + C(C-1)/p.
Energie = p*(C + C^2/p - C/p) - C^2 = pC + C^2 - C - C^2 = pC - C = C(p-1).

Pour un hit (N_0 >= 1) : C_2 >= C + C^2/p + ... >= C + C^2/p + (C/p - 1).
Cout minimal : (p-C)^2/(p-1).

Pour k = 20 (S=32, C~10^7, p~10^9) :
  Energie uniforme : C(p-1) ~ 10^{16}
  Cout du hit : (p-C)^2/(p-1) ~ p ~ 10^9

Puisque C(p-1) >> p, l'energie uniforme est BIEN PLUS GRANDE que le cout du hit.
Le hit ne coute "presque rien" en energie — d'ou la difficulte.

### 5.3. La contradiction impossiblement fine

Pour les grands k, avec p ~ C^{1.06} :
  Energie uniforme : C*p ~ C^{2.06}
  Cout du hit : p ~ C^{1.06}
  Ratio : C^{2.06}/C^{1.06} = C ~ 2^{1.5k}

Le cout du hit est C FOIS plus petit que l'energie totale.
Detecter un hit dans cette mer d'energie revient a detecter
un signal de taille 1/C dans le bruit — c'est la BARRIERE,
vue depuis le domaine de l'energie.

---

## 6. Synthese Finale des Trois Voies

| Voie | Principe | Resultat | Obstacle restant |
|------|----------|----------|-----------------|
| S (Skolem) | Non-existence mod m | Equivalente a H si m=d | Pas de module universel |
| O (Over-det.) | 2-adic Horner tree | n_0 mod 2^{a_{k-1}} determine | Correlations dans l'arbre |
| M' (Collisions) | Borner C_2 | Reduit a S-unit modulaire | Evertse modulaire inexistant |
| Energie | Cout Parseval du hit | Cout 1/C fois l'energie | Barriere sqrt universelle |

### La Figure Unificatrice

```
  EQUATION DE STEINER
  corrSum(A) = n_0 * (2^S - 3^k)
        |
        | reformulation
        v
  EQUATION S-UNITAIRE a k+1 termes dans <2,3>
        |
        +-- Mod d --> Hypothese H (N_0(d) = 0)
        |               |
        |               +-- Fourier --> Barriere sqrt (Phase 23b)
        |               |
        |               +-- CRT --> Besoin N_0(p) = 0 pour UN p
        |                            |
        |                            +-- Parseval --> Cout du hit (Section 5)
        |                            |
        |                            +-- Spectral --> Mixing insuffisant
        |
        +-- Mod 2^M --> Sur-determination (Section 2)
        |               |
        |               +-- Arbre de Horner --> Correlees
        |
        +-- S-unit --> Evertse (Solutions bornees dans Z)
                        |
                        +-- Version mod p : OUVERTE
```

### Le Verdict en une phrase

> **Chaque voie d'attaque converge vers le meme obstacle fondamental :
> l'independance multiplicative de 2 et 3 cree une rigidite qui empeche
> les methodes generiques de fonctionner, mais cette meme rigidite est
> ce qui devrait rendre les cycles impossibles — si seulement on savait
> la formaliser.**

---

## 7. Programme de Recherche (Post-Phase 23)

### 7.1. Priorite 1 : Evertse Modulaire (nouveau theoreme)

**Probleme.** Borner le nombre de solutions de :

  sum_{i=1}^n a_i * x_i ≡ 0 mod p

ou les x_i sont dans un sous-groupe S-unitaire de F_p* et les a_i
sont des puissances d'un element fixe.

Un tel theoreme generaliserait BGK (qui traite le cas n=1) et
Evertse (qui traite le cas dans Z, pas mod p).

### 7.2. Priorite 2 : Extension computationnelle

Verifier N_0(d) = 0 pour k = 18..25 par enumeration directe.
Pour k = 18 : C ~ 2.2M, faisable en quelques minutes.
Pour k = 25 : C ~ 10^10, faisable en quelques heures avec optimisation.

### 7.3. Priorite 3 : Algorithme de Bertok-Hajdu

Formuler l'equation de Steiner dans le cadre de Bertok-Hajdu et
tester leur algorithme de recherche de module obstruant.

### 7.4. Priorite 4 : Theorie des carries dans le Horner

Formaliser la propagation de retenues dans c_j = 3c_{j-1} + 2^{a_j}
(la multiplication par 3 = 2+1 cree des retenues specifiques).
Chercher une obstruction combinatoire a corrSum = n_0*d.

---

## References supplementaires

- Bertok, Hajdu (2021) "Skolem's conjecture confirmed for a family..."
  Acta Arithmetica 192(1).
- Bertok, Hajdu (2024) "The resolution of three exponential Diophantine
  equations..." J. Number Theory 260.
- Evertse (1984) "On sums of S-units and linear recurrences."
  Compositio Math. 53(2), 225-244.
- Cobham (1969) "On the base-dependence of sets of numbers recognizable
  by finite automata." Math. Systems Theory 3, 186-192.
- Stewart (2013) "On the representation of an integer in two different
  bases." J. reine angew. Math. 319, 63-72.
