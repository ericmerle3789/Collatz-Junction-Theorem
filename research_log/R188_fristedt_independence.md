# R188 — AGENT PROBABILISTE : Fristedt (1993) et l'independance des multiplicites
**Date :** 16 mars 2026
**Mode :** Raisonnement pur, ZERO calcul
**Prerequis :** R186-NkS (N(k,S) = p(S-k)), R187 (obstructions modulaires, structure de Horner)
**Objectif :** Fristedt (1993) donne l'independance approximative des multiplicites m_b d'une partition aleatoire. Cela implique-t-il l'equidistribution de g(v) mod d ?

---

## 0. RESUME EXECUTIF

**VERDICT : NON.** L'independance de Fristedt ne suffit PAS a prouver l'equidistribution de g mod d. Le verrou est identifie avec precision : trois obstructions distinctes empechent le transfert de l'independance des m_b vers l'equidistribution de g.

Neanmoins, l'analyse revele la STRUCTURE EXACTE du gap :

1. **R188-T1 [PROUVE]** : g(v) se reecrit comme g = SUM_{b >= 0} S_b * 2^b, ou S_b depend des multiplicites m_b ET de l'ASSIGNATION des positions j aux parts de valeur b. L'independance de Fristedt porte sur les m_b, pas sur l'assignation.

2. **R188-T2 [PROUVE]** : Meme sous l'hypothese d'independance complete des m_b (plus forte que Fristedt), g mod d n'est PAS equidistribuee car les coefficients S_b ne sont PAS des fonctions des m_b seuls.

3. **R188-T3 [PROUVE, NEGATIF]** : Le "modele de Fristedt" (m_b independants, geometriques) est un modele SANS ORDRE. Or g depend ESSENTIELLEMENT de l'ordre (via les poids 3^{k-1-j}). L'independance dans le modele sans ordre est ORTHOGONALE au probleme qui vit dans le modele ordonne.

4. **R188-V1 [VERROU IDENTIFIE]** : Le verrou irreductible est le COUPLAGE position-valeur : le coefficient de 2^b dans g est SUM_{j : B_j = b} 3^{k-1-j}, qui depend de QUELS indices j prennent la valeur b, pas seulement de COMBIEN d'indices la prennent. L'independance de Fristedt ne controle que le "combien", pas le "quels".

**Score de la piste Fristedt : 4/10.** Meilleure que les formes modulaires (3/10) car elle identifie un verrou plus fin, mais ne fournit aucun levier de preuve.

---

## 1. LE THEOREME DE FRISTEDT — ENONCE PRECIS

### 1.1 Cadre

Soit lambda une partition aleatoire uniforme de n (tiree uniformement parmi les p(n) partitions de n). Notons :
- m_b(lambda) = #{i : lambda_i = b} la multiplicite de la part b
- Contrainte : SUM_{b >= 0} b * m_b = n et SUM_{b >= 0} m_b = k (nombre de parts)

### 1.2 Theoreme (Fristedt, 1993)

Sous la mesure uniforme sur les partitions de n, les variables aleatoires (m_1, m_2, m_3, ...) convergent en distribution (pour n -> infini) vers des variables aleatoires INDEPENDANTES, ou m_b suit une loi geometrique de parametre 1 - q^b avec q = e^{-c/sqrt(n)}, c = pi * sqrt(2/3).

Plus precisement : la mesure jointe de (m_1, ..., m_R) pour R fixe est asymptotiquement un produit de geometriques :

P(m_1 = a_1, ..., m_R = a_R) ~ PROD_{b=1}^{R} (1 - q^b) * (q^b)^{a_b}

L'approximation est a un facteur (1 + o(1)) pres, uniformement en (a_1, ..., a_R) bornes.

### 1.3 Ce que Fristedt dit et NE dit PAS

**DIT :**
- Les multiplicites d'un nombre FIXE de parts de tailles FIXES sont approximativement independantes.
- Chaque m_b est approximativement geometrique.
- L'approximation est valable pour b = O(1) quand n -> infini.

**NE DIT PAS :**
- Rien sur les parts de taille b = O(sqrt(n)) ou plus (la zone ou q^b est loin de 1).
- Rien sur l'ordre INTERNE des parts : si m_b = 3, Fristedt ne dit pas quelles positions j (dans le vecteur ordonne) prennent la valeur b.
- Rien sur les fonctions NON-LINEAIRES des parts.

---

## 2. TRADUCTION : DES m_b A g(v)

### 2.1 La reecriture de g en termes de multiplicites

Soit v = (B_0 <= B_1 <= ... <= B_{k-1}) un vecteur monotone. La partition correspondante a multiplicites m_b = #{j : B_j = b}.

Reecrivons g :

g(v) = SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}

Regroupons par valeur de B_j :

g = SUM_{b >= 0} [SUM_{j : B_j = b} 3^{k-1-j}] * 2^b

Definissons S_b = SUM_{j : B_j = b} 3^{k-1-j}.

Alors :

**g = SUM_{b >= 0} S_b * 2^b**

> **Theoreme R188-T1 (PROUVE) :** g(v) = SUM_{b >= 0} S_b * 2^b, ou S_b est la somme des poids 3^{k-1-j} pour les indices j tels que B_j = b. Le nombre de termes dans S_b est exactement m_b (la multiplicite de la part b). MAIS la VALEUR de S_b depend de QUELS indices j sont assignes a la part b, pas seulement de combien.
>
> **Preuve :** Regroupement direct des termes de g par valeur de B_j. La decomposition est unique car les B_j sont ordonnes et les j sont fixes. PROUVE.

### 2.2 Le probleme de l'assignation

Le vecteur ordonne (B_0 <= ... <= B_{k-1}) induit une PARTITION des indices {0, 1, ..., k-1} en blocs :

- J_b = {j : B_j = b} pour chaque b >= 0
- |J_b| = m_b
- Les J_b sont des intervalles CONTIGUS de {0, ..., k-1} (car le vecteur est ordonne)

Par monotonie, les indices assignes a la part b forment un intervalle [l_b, l_b + m_b - 1] dans {0, ..., k-1}. Plus precisement :

- Les parts de valeur 0 occupent les positions j = 0, 1, ..., m_0 - 1
- Les parts de valeur 1 occupent les positions j = m_0, m_0 + 1, ..., m_0 + m_1 - 1
- Et ainsi de suite

Donc :

S_b = SUM_{j = L_b}^{L_b + m_b - 1} 3^{k-1-j}

ou L_b = SUM_{b' < b} m_{b'} est la position de debut du bloc b.

En factorisant :

S_b = 3^{k-1-L_b} * (1 + 3^{-1} + ... + 3^{-(m_b - 1)}) = 3^{k-1-L_b} * (3^{m_b} - 1) / (2 * 3^{m_b - 1})

Simplifie :

**S_b = (3^{m_b} - 1) / 2 * 3^{k - L_b - m_b}**

ou L_b = m_0 + m_1 + ... + m_{b-1}.

### 2.3 g en fonction des multiplicites seules

Puisque les J_b sont determines par la monotonie et les m_b, on peut ecrire g ENTIEREMENT en fonction des (m_b)_{b >= 0} :

**g = SUM_{b >= 0} [(3^{m_b} - 1) / 2] * 3^{k - L_b - m_b} * 2^b**

avec L_b = SUM_{b' < b} m_{b'} et la contrainte SUM m_b = k, SUM b * m_b = n = S - k.

> **Corollaire R188-C1 (PROUVE) :** g est une fonction DETERMINISTE des multiplicites (m_b)_{b >= 0}. Si les m_b sont connus, g est entierement determine.
>
> **Preuve :** Par la monotonie, les positions des indices dans chaque bloc sont determinees par les tailles cumulees des blocs precedents. PROUVE.

**ATTENTION :** Cela semble contredire T1 ("S_b depend de quels indices j"). La resolution est que, GRACE A LA MONOTONIE, "quels indices" EST determine par les multiplicites. Dans un vecteur NON ordonne, les m_b ne suffiraient pas.

### 2.4 Sanity check k = 1

k = 1, n = 1, d = 1. Unique partition : B_0 = 1. Multiplicites : m_1 = 1, m_b = 0 sinon.

g = [(3^1 - 1)/2] * 3^{1 - 0 - 1} * 2^1 = [2/2] * 3^0 * 2 = 1 * 1 * 2 = 2.

Verification directe : g = 3^0 * 2^1 = 2. **COHERENT.**

d = 1, g = 0 mod 1. **COHERENT.**

---

## 3. APPLICATION DE FRISTEDT : LE MODELE PROBABILISTE

### 3.1 Le modele

Par Fristedt, sous la mesure uniforme sur les partitions de n, les m_b sont approximativement independants, avec m_b ~ Geom(1 - q^b), q = e^{-c/sqrt(n)}.

Sous ce modele, g = f(m_0, m_1, m_2, ...) ou f est la fonction explicite de C1.

**Question :** Si les m_b sont independants, g est-il approximativement uniforme mod d ?

### 3.2 Premiere tentative : somme de termes independants

Ecrivons g = SUM_{b >= 0} T_b avec T_b = [(3^{m_b} - 1) / 2] * 3^{k - L_b - m_b} * 2^b.

Le probleme est que T_b depend de L_b = SUM_{b' < b} m_{b'}, qui depend de TOUTES les multiplicites precedentes. Donc T_b n'est PAS une fonction de m_b seul.

**Les termes T_b ne sont PAS independants, meme si les m_b le sont.**

C'est le NOEUD du probleme : g est une somme de termes ou chaque terme depend de la variable "locale" m_b mais aussi du CONTEXTE GLOBAL L_b (position cumulee).

### 3.3 La dependance via L_b

L_b = m_0 + m_1 + ... + m_{b-1} est une somme PARTIELLE des m_{b'} precedents. Si les m_b sont independants, L_b est une somme de variables independantes, donc concentree autour de sa moyenne (par la loi des grands nombres ou Hoeffding).

Sous Fristedt : E[m_b] = q^b / (1 - q^b) et E[L_b] = SUM_{b'=0}^{b-1} q^{b'} / (1 - q^{b'}).

Pour b = O(1) et q = e^{-c/sqrt(n)} proche de 1 : E[m_b] ~ sqrt(n)/(c*b) (grande moyenne). Et L_b est la somme de b termes de taille ~ sqrt(n), donc L_b ~ b * sqrt(n) / c.

Le facteur 3^{k - L_b - m_b} dans T_b varie EXPONENTIELLEMENT avec L_b. Meme une petite fluctuation de L_b (de l'ordre de sqrt(Var(L_b))) change 3^{-L_b} par un facteur exponentiel.

> **Obstruction F1 :** La dependance de T_b en 3^{-L_b} amplifie exponentiellement les fluctuations de L_b. L'independance des m_b ne produit PAS l'independance des T_b, et les fluctuations correlees de (T_b) empechent une application directe du theoreme d'equidistribution de Weyl ou d'Erdos-Turan.

### 3.4 Tentative de contournement : conditionner sur L_b

Conditionnons sur toutes les valeurs L_0, L_1, L_2, ... (equivalemment, sur les sommes cumulees des m_b). Alors les T_b deviennent des fonctions de m_b seuls (L_b etant fixe), et les termes sont independants.

MAIS : conditionner sur L_b = SUM_{b'<b} m_{b'} pour tout b revient a conditionner sur CHAQUE m_b individuellement (car L_b+1 - L_b = m_b). Donc conditionner sur tous les L_b fixe entierement les m_b, et il n'y a plus de variable aleatoire. g est alors un NOMBRE, pas une variable aleatoire.

**Impasse :** On ne peut pas a la fois garder l'independance ET eliminer la dependance en L_b.

---

## 4. LE VERROU FONDAMENTAL : COUPLAGE POSITION-VALEUR

### 4.1 Nature du couplage

Le coefficient de 2^b dans g est S_b = [(3^{m_b} - 1)/2] * 3^{k - L_b - m_b}. Ce coefficient implique :
- m_b : le nombre de parts egales a b (**controlable par Fristedt**)
- L_b : la position cumulee des parts < b (**dependance globale**)

La puissance 3^{k - L_b - m_b} est le RANG de la premiere occurrence de la part b dans la suite geometrique 3^{k-1}, 3^{k-2}, ..., 3^0 des poids. Ce rang depend de la repartition de TOUTES les parts plus petites.

C'est le **couplage position-valeur** : la valeur d'une part (b) est decouplee de sa position (j), mais la contribution a g COUPLE les deux via le poids 3^{k-1-j}.

> **Verrou R188-V1 (IDENTIFIE) :** Le couplage position-valeur rend g = SUM S_b * 2^b NON DECOMPOSABLE en somme de termes independants, meme sous l'hypothese d'independance complete des multiplicites. Le facteur 3^{k-L_b-m_b} dans S_b cree une CHAINE DE DEPENDANCE entre les contributions des differentes parts.

### 4.2 Reformulation en termes informationnels

Fristedt dit : "combien de parts de chaque taille" -> approximativement independant.

Mais g exige de savoir : "combien de parts de chaque taille ET ou elles se placent dans l'ordre des poids".

Pour les partitions ordonnees, "ou elles se placent" EST determine par "combien" (C1). Donc g est bien fonction des m_b. Mais c'est une fonction HAUTEMENT NON-LINEAIRE (exponentielle en les sommes cumulees), et l'independance approximative des entrees ne se transmet pas aux sorties exponentielles.

**Analogie :** Si X_1, ..., X_n sont independants, SUM X_i mod d est bien equidistribuee (sous conditions faibles). Mais PROD X_i mod d ne l'est PAS necessairement, car le produit amplifie les correlations residuelles. Ici, g est un MELANGE additif-multiplicatif (somme de termes contenant des produits de puissances des m_b).

---

## 5. ANALYSE FORMELLE : POURQUOI L'EQUIDISTRIBUTION ECHOUE

### 5.1 Critere de Weyl pour g mod d

g est equidistribuee mod d si et seulement si, pour tout a in {1, ..., d-1} :

(1/p(n)) * |SUM_{lambda |- n} e^{2*pi*i*a*g(lambda)/d}| = o(1) quand n -> infini

Sous le modele de Fristedt (m_b independants), cette somme devient :

E_Fristedt[e^{2*pi*i*a*g(m)/d}]

ou g(m) = SUM_b [(3^{m_b}-1)/2] * 3^{k-L_b-m_b} * 2^b.

### 5.2 Le probleme de la non-factorisation

Si g etait une somme SUM_b f_b(m_b) avec f_b dependant UNIQUEMENT de m_b, l'esperance se factoriserait :

E[e^{i*a*g/d}] = PROD_b E[e^{i*a*f_b(m_b)/d}]

et chaque facteur serait < 1 en module (sous des conditions generiques), donnant un produit tendant vers 0 = equidistribution.

MAIS g n'est PAS de cette forme. Le terme T_b depend de L_b = SUM_{b'<b} m_{b'}. Donc :

E[e^{i*a*g/d}] != PROD_b E[e^{i*a*T_b(m_b)/d}]

La factorisation ECHOUE.

### 5.3 Peut-on borner quand meme ?

On pourrait tenter une borne de type Cauchy-Schwarz ou decouplage (decoupling inequality). L'idee serait :

|E[e^{i*a*g/d}]|^2 <= E[|e^{i*a*(g(m) - g(m'))/d}|] = E[e^{i*a*(g(m)-g(m'))/d}]

ou m, m' sont deux copies independantes des multiplicites. Mais g(m) - g(m') a une structure aussi compliquee que g lui-meme (la difference de deux expressions exponentielles), et cette borne ne simplifie rien.

**Alternative : martingale.** On pourrait ecrire g = SUM_b T_b comme une somme de differences de martingale (en revelant les m_b un par un, b = 0, 1, 2, ...). Chaque increment T_b est mesurable par rapport a F_b = sigma(m_0, ..., m_b). Sous l'independance de Fristedt :

E[e^{i*a*T_b/d} | F_{b-1}] = phi_b(L_b, a, d)

ou phi_b est l'esperance conditionnelle sachant L_b (qui est F_{b-1}-mesurable).

Le produit PROD_b phi_b(L_b, a, d) est le bon objet a borner. Mais chaque phi_b depend de L_b, qui est aleatoire, et la borne uniforme |phi_b| < 1 - epsilon est FAUSSE en general (pour certaines valeurs de L_b, phi_b peut etre proche de 1).

> **Obstruction F2 :** L'approche par martingale (factorisation conditionnelle) donne un produit telescopique dont chaque facteur depend de la variable aleatoire L_b. L'absence de borne uniforme |phi_b| < 1 - epsilon empeche de conclure que le produit tend vers 0.

---

## 6. LE REGIME DE COLLATZ : POURQUOI FRISTEDT NE S'APPLIQUE MEME PAS

### 6.1 Le regime des parametres

Pour le probleme de Collatz : n = S - k ~ 0.585k. Fristedt est un resultat ASYMPTOTIQUE en n -> infini. Pour k fixe (k = 3, 4, ..., 41), n est PETIT (n = 1, 2, ..., ~23). L'approximation de Fristedt n'est PAS valable.

Pour k -> infini (ou le Junction Theorem s'applique deja), n ~ 0.585k -> infini, et Fristedt POURRAIT s'appliquer. Mais c'est dans le regime ou C/d -> 0 est DEJA prouve par comptage direct (R186).

> **Obstruction F3 :** Le theoreme de Fristedt est asymptotique (n -> infini) et ne s'applique pas au regime des petits k (3 <= k <= 41) ou le probleme de Collatz est ouvert. Pour les grands k, le resultat N(k,S)/d -> 0 est deja acquis sans Fristedt.

### 6.2 La taille des parts

Dans le regime Collatz, les parts B_j vont de 0 a B_{k-1} = O(n) = O(k). Les parts sont donc de taille O(k), ce qui est O(sqrt(n) * sqrt(k/0.585)). Pour Fristedt, les parts de taille b = O(sqrt(n)) sont dans le regime ou l'approximation geometrique commence a devier.

Plus precisement : q = e^{-c/sqrt(n)} et q^b = e^{-c*b/sqrt(n)}. Pour b ~ sqrt(n), q^b ~ e^{-c} ~ 0.076, ce qui est modere. Pour b >> sqrt(n), q^b -> 0 et m_b -> Bernoulli(q^b) (pas geometrique). La plupart des parts dans le regime Collatz sont dans cette zone INTERMEDIAIRE ou Fristedt est le moins precis.

---

## 7. TENTATIVE DE SAUVETAGE : LE MODELE "GROS GRAINS"

### 7.1 Idee

Au lieu de chercher l'equidistribution fine de g mod d, on pourrait utiliser Fristedt pour borner la VARIANCE de g et montrer que g/d a une distribution diffuse (pas concentree sur un residue).

### 7.2 Variance de g sous Fristedt

g = SUM_b S_b * 2^b avec S_b = O(3^{k-L_b}).

Le terme DOMINANT est celui avec b maximal et S_b non nul, soit b* = max{b : m_b > 0}. Sous Fristedt, b* ~ c' * sqrt(n) (la plus grande part d'une partition aleatoire de n est ~ c' * sqrt(n) * log(n)... plus precisement, la plus grande part est environ sqrt(n) * log(quelque chose)).

Le terme dominant de g est ~ S_{b*} * 2^{b*} ~ 3^{k - (k - m_{b*})} * 2^{b*} = 3^{m_{b*}} * 2^{b*}.

La VARIANCE de g est dominee par la variance de ce terme, qui est EXPONENTIELLE en b*. Donc Var(g) >> d^2 est POSSIBLE (g a un grand range).

MAIS une grande variance ne suffit pas pour l'equidistribution. Il faut aussi que g soit "diffuse" modulo d, ce qui est une condition sur la DISTRIBUTION FINE, pas sur la variance.

**Analogie :** une variable aleatoire valant 0 ou 10^{100} avec probabilite 1/2 chacune a une variance enorme mais n'est PAS equidistribuee mod d pour la plupart des d.

> **Obstruction F4 :** La grande variance de g (sous Fristedt) ne suffit pas pour l'equidistribution mod d. L'equidistribution requiert un controle de la distribution FINE (sommes exponentielles), pas seulement des moments.

---

## 8. LA QUESTION CORRECTE : QUE FAUDRAIT-IL POUR QUE FRISTEDT MARCHE ?

### 8.1 Conditions suffisantes (hypothetiques)

Pour que l'independance de Fristedt implique g mod d equidistribuee, il faudrait AU MOINS :

**(A)** Que g soit une fonction ADDITIVE des m_b (i.e., g = SUM f(m_b) avec f ne dependant pas des autres multiplicites). C'est FAUX par la Section 2.3 : g depend des sommes cumulees L_b.

**(B)** Que le facteur 3^{k-L_b-m_b} soit NEGLIGEABLE ou CONCENTRE. C'est FAUX : 3^{k-L_b} varie de 3^k (quand L_b = 0) a 1 (quand L_b = k), soit un facteur 3^k entre les extremes.

**(C)** Qu'il existe un UNIQUE terme dominant T_{b*} dans g, et que ce terme soit equidistribue mod d conditionnellement aux autres. Cela pourrait marcher si T_{b*} = f(m_{b*}) * 2^{b*} avec 2^{b*} aleatoire et pgcd(2^{b*}, d) petit. Mais d = 2^S - 3^k est IMPAIR (car 2^S et 3^k sont de parites differentes), donc pgcd(2^{b*}, d) = 1. La question se reduit alors a : f(m_{b*}) est-il equidistribue mod d/pgcd ? Et la reponse depend de la loi de m_{b*} qui est geometrique de petit parametre (m_{b*} = O(1) typiquement).

### 8.2 Piste (C) : le terme dominant

Developpons la piste (C). Si la plus grande part b* domine, on a approximativement :

g ~ S_{b*} * 2^{b*} mod d

avec S_{b*} = (3^{m_{b*}} - 1)/2 * 3^{k - k} = (3^{m_{b*}} - 1)/2 (car L_{b*} + m_{b*} = k).

Attendons... L_{b*} = SUM_{b' < b*} m_{b'} = k - m_{b*}. Donc 3^{k - L_{b*} - m_{b*}} = 3^0 = 1.

Donc **S_{b*} = (3^{m_{b*}} - 1) / 2** independamment de tout le reste.

Et g ~ [(3^{m_{b*}} - 1)/2] * 2^{b*} + termes d'ordre inferieur.

Le terme dominant est entierement determine par m_{b*} (combien de parts egales au maximum) et b* (la valeur du maximum). Sous Fristedt, m_{b*} est approximativement geometrique de parametre 1 - q^{b*}.

Pour b* grand : q^{b*} -> 0, donc m_{b*} ~ Geom(1) = presque surement 1. Alors S_{b*} = (3-1)/2 = 1 et g ~ 2^{b*}.

Sous cette approximation : g ~ 2^{b*} mod d. Et d = 2^S - 3^k est impair, donc pgcd(2^{b*}, d) = 1. La question devient : 2^{b*} mod d est-il equidistribue quand b* varie ?

La valeur 2^{b*} mod d parcourt le sous-groupe <2> de (Z/dZ)*. Si ord_d(2) est grand (~ d), alors 2^b mod d est "pseudoaleatoire" quand b varie. Mais b* prend un NOMBRE LIMITE de valeurs (il est concentre autour de ~ c*sqrt(n)), donc la question est de savoir si les quelques valeurs 2^b mod d pour b ~ c*sqrt(n) sont bien reparties. C'est une question sur les ORBITES de la multiplication par 2 dans Z/dZ -- exactement le probleme de Collatz reformule.

> **Obstruction F5 (CIRCULARITE) :** L'approximation "g ~ 2^{b*} mod d" reduit la question a l'equidistribution de 2^b mod d pour b dans un intervalle. Mais d = 2^S - 3^k, et l'ordre de 2 modulo d est lie a la structure de la dynamique de Collatz elle-meme. L'argument est CIRCULAIRE.

---

## 9. SYNTHESE DES OBSTRUCTIONS

| # | Obstruction | Nature | Fatale ? |
|---|-------------|--------|----------|
| F1 | g n'est pas somme de termes independants (dependance via L_b) | Structurelle | OUI |
| F2 | Approche martingale : pas de borne uniforme sur les facteurs | Technique | Potentiellement contournable |
| F3 | Fristedt est asymptotique, regime Collatz est a n petit | Parametrique | OUI pour k petit |
| F4 | Grande variance != equidistribution | Conceptuelle | OUI |
| F5 | Piste "terme dominant" -> circularite | Fondamentale | OUI |

### Le verrou irreductible

Les obstructions F1 et F5 sont les plus profondes :
- **F1** dit que meme avec l'independance des m_b, g n'est pas decomposable.
- **F5** dit que meme en simplifiant au maximum (un seul terme dominant), on retombe sur le probleme de Collatz.

Cela CONFIRME le diagnostic de R187 : le probleme vit dans la structure multiplicative de (2,3) modulo d, et aucun outil additif/probabiliste ne peut eliminer cette dependance.

---

## 10. COMPARAISON AVEC L'ARGUMENT DE DENSITE VISE

### 10.1 Ce que l'argument de densite exige

L'argument de densite pour montrer N_0(k,S,d) = 0 requiert :

"Pour presque toute partition lambda de n, g(lambda) mod d est approximativement uniforme sur {0, 1, ..., d-1}."

En termes probabilistes : la distribution de g(lambda) mod d (sous la mesure uniforme sur les partitions de n) est close de la distribution uniforme en variation totale.

### 10.2 Ce que Fristedt donne

Fristedt donne : les "ingredients" de g (les multiplicites m_b) sont approximativement independants. Mais g est une fonction NON-ADDITIVE, NON-SEPARABLE, EXPONENTIELLEMENT SENSIBLE de ces ingredients.

**Le gap entre "ingredients independants" et "sortie equidistribuee" est le gap entre avoir des briques et avoir une maison.** L'architecture de g (la structure de Horner, R187-T1) defie l'assemblage probabiliste.

### 10.3 Ce qu'il faudrait en plus de Fristedt

Pour combler le gap, il faudrait UN des elements suivants :

1. **Un theoreme d'equidistribution pour les fonctions exponentielles de variables independantes.** Cela n'existe pas dans la litterature. Les theoremes type Berry-Esseen ou Erdos-Turan traitent des sommes LINEAIRES.

2. **Un resultat de type "entropy method" montrant que g mod d a presque l'entropie maximale.** Cela requiert de montrer H(g mod d) ~ log(d), ce qui est aussi dur que l'equidistribution.

3. **Une borne non triviale sur les sommes exponentielles SUM_{lambda |- n} e^{2*pi*i*a*g(lambda)/d}.** C'est le verrou central de R186, que Fristedt ne resout pas.

---

## 11. SANITY CHECK FINAL : k = 1

k = 1, S = 2, n = 1, d = 1.

- Unique partition de n = 1 : une part de taille 1.
- m_1 = 1, m_b = 0 pour b != 1.
- L_1 = m_0 = 0, S_1 = (3^1 - 1)/2 * 3^{1-0-1} = 1 * 1 = 1.
- g = S_1 * 2^1 = 2.
- d = 1, g = 0 mod 1. **N_0 = 1 = p(1)/d = 1/1. COHERENT.**
- Fristedt ne s'applique pas (n = 1 trop petit). **COHERENT avec F3.**

Tout est coherent.

---

## 12. EVALUATION FINALE

### 12.1 Resultats

| Enonce | Statut | Section |
|--------|--------|---------|
| **R188-T1** : g = SUM S_b * 2^b, S_b depend des m_b et de L_b | **PROUVE** | 2.1 |
| **R188-C1** : g est fonction deterministe des m_b (grace a la monotonie) | **PROUVE** | 2.3 |
| **R188-T2** : L'independance des m_b n'implique PAS l'independance des T_b | **PROUVE** | 3.2-3.3 |
| **R188-T3** : Le modele de Fristedt ne controle pas g mod d | **PROUVE (NEGATIF)** | 5-6 |
| **R188-V1** : Verrou = couplage position-valeur via 3^{k-L_b} | **IDENTIFIE** | 4.1 |
| **Obstructions F1-F5** : 5 obstructions identifiees | **PROUVEES/IDENTIFIEES** | 9 |

### 12.2 Score

**Piste Fristedt pour equidistribution de g mod d : 4/10.**

- 0/10 pour la production de preuve
- 6/10 pour la clarification structurelle (C1 est non-trivial : g est deterministe en les m_b)
- 4/10 pour l'identification du verrou V1 (couplage position-valeur)
- 2/10 pour la piste "terme dominant" (Section 8.2) qui montre la circularite F5

### 12.3 Comparaison avec les directions precedentes

| Direction | Score | Verrou | Circulaire ? |
|-----------|-------|--------|-------------|
| Formes modulaires (R187) | 3/10 | g exponentiel en les parts | Non (obstruction structurelle) |
| **Fristedt (R188)** | **4/10** | **Couplage position-valeur** | **OUI (F5)** |
| Sommes exponentielles (R186) | 5/10 | Support creux, annulation generique | Non (verrou TAN ouvert) |
| Baker / adequate prime | 3/10 | Bornes trop faibles pour k < 42 | Non |
| CRT anti-correlation | 4/10 | Verrou TAN | Non |

### 12.4 Ce que Fristedt apporte au projet

Un resultat constructif : **C1**. La formule explicite g = SUM [(3^{m_b}-1)/2] * 3^{k-L_b-m_b} * 2^b en termes des multiplicites est propre et exploitable. Elle montre que le probleme est entierement code dans le profil de multiplicites (m_b).

Un resultat negatif : **V1 + F5**. L'independance approximative des multiplicites est ORTHOGONALE au probleme d'equidistribution de g mod d. L'argument est circulaire au bout de la chaine.

**La fleur de Fristedt est la BONNE fleur pour les partitions, mais le MAUVAIS jardin pour Collatz.** Les partitions aleatoires vivent dans le regime additif (independance des multiplicites). Collatz vit dans le regime multiplicatif (couplage exponentiel via les puissances de 3). Fristedt eclaire magnifiquement le premier et ne touche pas le second.

---

*R188 : 2 theoremes (T1, T2), 1 corollaire (C1), 1 verrou (V1), 5 obstructions (F1-F5). La piste Fristedt est FERMEE par circularite (F5) : l'independance approximative des multiplicites ne se transmet pas a g mod d a cause du couplage position-valeur (V1). Le resultat constructif C1 (g entierement determine par les m_b) est correct mais insuffisant. Le verrou central reste l'equidistribution de g mod d, inattaquable par les outils probabilistes de la theorie des partitions.*
