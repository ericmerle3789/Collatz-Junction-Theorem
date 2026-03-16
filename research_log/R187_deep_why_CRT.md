# R187 -- INVESTIGATEUR RACINAIRE : Pourquoi la CRT anti-correlation resiste, et ou se cache la sortie
**Date :** 16 mars 2026
**Mode :** Raisonnement pur, ZERO calcul -- chaine des POURQUOI jusqu'au sol rocheux
**Cible :** CRT anti-correlation (4/10) -- 6 tentatives echouees en R185, verrou confirme en R186
**Philosophie :** Une piste a 4/10 n'est pas une impasse. C'est une piste ou on n'a pas encore trouve la BONNE QUESTION.

---

## 0. RESUME EXECUTIF

Les 6 tentatives de R185 echouent toutes pour la MEME raison profonde : elles essaient de quantifier la non-uniformite de g(v) mod m sur un support CREUX (les partitions monotones) avec des outils concus pour des supports DENSES (intervalles, sous-groupes, varietes). La chaine des POURQUOI descend jusqu'a un sol rocheux inattendu : les partitions ont leurs PROPRES outils (formes modulaires, fonctions theta, identites de Rogers-Ramanujan), et la question "g(v) mod d est-il equidistribue sur les partitions ?" peut se reformuler comme une question sur les COEFFICIENTS DE FOURIER de fonctions modulaires restreintes. Ce n'est plus un probleme de sommes exponentielles standard -- c'est un probleme de theorie des formes modulaires.

---

## 1. CHAINE DES POURQUOI -- PREMIER AXE : L'echec des 6 tentatives

### Niveau 0 : POURQUOI les 6 tentatives echouent-elles ?

Parce qu'elles essaient toutes de quantifier la non-uniformite de g(v) mod m sur les vecteurs monotones (= partitions de S-k).

**Rappel des 6 tentatives (R185 A3) :**
1. Surdetermination (omega(d) > k-1) --> ECHEC : omega(d) ~ log k << k-1
2. Inclusion-exclusion --> ECHEC : bornes trop laches
3. Caracteres additifs croises --> ECHEC : sommes exponentielles sur partitions = probleme ouvert
4. Concentration dans arcs courts --> PARTIEL : marche pour grands p, echoue petits
5. Structure monotone --> ECHEC : qualitatif, pas quantitatif
6. Comptage par fibres --> ECHEC : revient aux sommes expo

Le point commun : chaque tentative se reduit a estimer

> S(a) = SUM_{v in V_k(S)} exp(2*pi*i*a*g(v)/p)

pour a != 0, ou V_k(S) est l'ensemble des partitions de S-k.

### Niveau 1 : POURQUOI cette somme est-elle difficile a estimer ?

Parce que g(v) = SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} est une fonction DOUBLEMENT EXPONENTIELLE des variables B_j (exponentielle en B_j via 2^{B_j}, et les poids 3^{k-1-j} sont eux-memes exponentiels en j). Et la somme porte sur un ensemble V_k(S) qui n'est ni un intervalle, ni un sous-groupe, ni une variete algebrique, mais l'ensemble des PARTITIONS d'un entier -- un objet combinatoire sans structure algebrique evidente.

Les outils classiques pour les sommes exponentielles :
- **Weil/Deligne** : supposent une somme sur F_p ou une variete algebrique sur F_p. Les partitions ne sont ni l'un ni l'autre.
- **Weyl** (differencing) : suppose une fonction polynomiale des variables. 2^{B_j} n'est pas polynomial en B_j.
- **van der Corput** : suppose une somme sur un intervalle. Les partitions ne sont pas un intervalle.
- **Bourgain/Katz/Tao** : supposent des ensembles de taille >> sqrt(p) dans un corps fini. Les partitions p(n) ~ exp(2*sqrt(k)) sont typiquement << p.
- **Vinogradov** : traite les sommes SUM exp(2*pi*i*c*2^b/m) pour b dans un intervalle. La contrainte de somme et de monotonie n'est pas couverte.

### Niveau 2 : POURQUOI les partitions ne sont-elles pas traitees par ces outils ?

Trois raisons structurelles :

**(A) CREUX :** L'ensemble des partitions de n a taille p(n) ~ exp(pi*sqrt(2n/3)), ce qui est sous-exponentiel en n. Les intervalles {0,...,N} ont taille N+1 (lineaire). Les corps finis F_p ont taille p. Pour n ~ 0.585k, p(n) ~ exp(2*sqrt(k)) << 3^k ~ d. Le support est exponentiellement creux par rapport au module.

**(B) NON-ALGEBRIQUE :** Une partition lambda = (lambda_1,...,lambda_r) n'est pas un point d'une variete algebrique. C'est un element d'un monoide libre modulo l'ordre. Il n'y a pas de "coordonnees de Zariski" naturelles. L'anneau des fonctions sur les partitions n'est pas noetherian.

**(C) NON-INDEPENDANT :** Les parts d'une partition sont contraintes par la somme fixe (SUM B_j = S-k) et la monotonie (B_j <= B_{j+1}). Ces contraintes couplent toutes les variables. Dans un intervalle, les coordonnees sont independantes. Dans un corps fini, les elements sont independants. Ici, changer B_0 force des ajustements sur les B_j restants.

### Niveau 3 : POURQUOI ne peut-on pas ADAPTER les outils existants au support creux des partitions ?

C'est la question CLE. Creusons dans trois directions.

#### Direction 3a : Peut-on PLONGER les partitions dans un espace ou les outils s'appliquent ?

**Tentative 3a-1 : Plongement dans Z^k.** Une partition (B_0,...,B_{k-1}) est un point de Z^k. Mais l'ensemble des partitions dans Z^k n'est pas convexe (les combinaisons lineaires de partitions ne sont pas des partitions en general). Il n'est pas non plus un sous-groupe. C'est l'ensemble des points entiers d'un cone (le cone de Weyl de type A_{k-1}), intersecte avec un hyperplan (SUM B_j = S-k).

**POURQUOI le cone de Weyl ne suffit-il pas ?** Parce que les bornes de Weil sur les sommes exponentielles dans un cone requierent que le cone ait un interieur non-vide dans un espace affine, et que la fonction soit polynomiale. Le cone de Weyl est un polyedre rationnel dans Z^k, et g(v) est exponentielle, pas polynomiale. L'obstruction est la MEME que Niveau 1 (la nature doublement exponentielle de g).

**Tentative 3a-2 : Plongement dans F_p^r via la compression spectrale (R185 A2).** La projection sigma(v) = (sigma_0,...,sigma_{r-1}) envoie les partitions dans F_p^r. L'image Sigma est un sous-ensemble de F_p^r. MAIS |Sigma| << p^r (R186 Fait 12), donc l'image est creuse dans F_p^r. Les sommes exponentielles sur Sigma dans F_p^r sont aussi difficiles que les originales.

**Tentative 3a-3 : Plongement dans le tore (R/Z)^k via les caracteres.** On pose theta_j = B_j * alpha mod 1 pour alpha irrationnel. L'ensemble des partitions se projette sur un sous-ensemble du tore. Mais la distribution de cette projection sur le tore depend de la structure diophantienne de alpha, et on retombe sur les sommes exponentielles.

**VERDICT 3a :** Les plongements dans des espaces "classiques" (Z^k, F_p^r, tore) ne resolvent pas le probleme car l'image des partitions est toujours creuse et non-algebrique dans ces espaces.

#### Direction 3b : Les partitions ont-elles des PROPRIETES DE MIXING qui pourraient remplacer les bornes de sommes expo ?

Les partitions aleatoires (tirees uniformement de p(n)) ont ete etudiees par Fristedt (1993), Vershik (1996), Romik (2015). Le resultat principal est la LIMITE SHAPE : pour n grand, une partition typique de n a une forme limite deterministe (la courbe exp(-pi*x/sqrt(6n)) apres normalisation).

**POURQUOI la limite shape ne suffit-elle pas ?** Parce que la limite shape decrit les GRANDES parts (celles de taille ~ sqrt(n)), mais g(v) est domine par les parts avec les poids 3^{k-1-j} les plus grands, i.e., les parts B_j pour les petits j. Les petites parts (B_0, B_1,...) sont les parts du "bord" de la partition, et leur distribution est POISSONIENNE (Fristedt 1993). La distribution de g(v) mod p depend donc de la distribution jointe des petites parts, qui est asymptotiquement independante (!) par le theoreme de Fristedt.

**Theoreme de Fristedt (1993) :** Pour une partition aleatoire uniforme de n, les multiplicites des parts (m_1, m_2, m_3,...) sont asymptotiquement independantes, avec m_j ~ Geometrique(1 - e^{-beta*j}) ou beta = pi/sqrt(6n).

**CONSEQUENCE CRUCIALE :** Si les multiplicites sont independantes, alors g(v) est une somme de termes INDEPENDANTS modulo la contrainte de somme. L'independance asymptotique de Fristedt pourrait donner l'equidistribution de g(v) mod m pour les grands n.

**POURQUOI cela ne marche-t-il pas immediatement ?**

1. **La contrainte de somme CASSE l'independance.** Fristedt travaille en regime "grand canonique" (somme aleatoire). Pour les partitions de n EXACTE, il y a un conditionnement qui introduit des correlations. L'erreur de conditionnement est typiquement O(1/sqrt(n)).

2. **g(v) est une fonction NON-LINEAIRE des multiplicites.** Meme si les m_j sont independants, g(v) = SUM_{j} 3^{k-1-pos(j)} * 2^j * m_j (ou pos(j) est la position de la part j dans la suite ordonnee) est une fonction non-triviale de la suite des multiplicites.

3. **n = S-k ~ 0.585k est PETIT.** L'asymptotique de Fristedt demande n --> infty, et les corrections sont en O(1/sqrt(n)). Pour n ~ 0.585k, la convergence est lente.

**SCORE Direction 3b : 5/10.** L'independance de Fristedt est le meilleur outil adapte aux partitions, mais le passage au regime "canonique" (somme fixe) et la non-linearite de g sont des obstacles non-triviaux.

#### Direction 3c : Les formes modulaires ont-elles quelque chose a dire ?

**Les partitions sont INTRINSEQUEMENT liees aux formes modulaires.** La fonction generatrice des partitions est :

> SUM_{n>=0} p(n) * q^n = PROD_{m>=1} 1/(1-q^m) = q^{1/24} / eta(tau)

ou eta(tau) = q^{1/24} * PROD (1-q^m) est la fonction eta de Dedekind, q = e^{2*pi*i*tau}, et tau est dans le demi-plan superieur H.

La formule de Hardy-Ramanujan-Rademacher pour p(n) est une consequence de la MODULARITE de 1/eta(tau).

**Question cle :** Peut-on obtenir une formule pour le nombre de partitions de n dont la valeur g est dans une classe de residu donnee ?

Soit, formellement :

> N_a(n, d) = #{partition lambda de n : g(lambda) equiv a mod d}

Pour a = 0, c'est exactement le nombre de cycles potentiels. On veut N_0(n, d) = 0 pour n = S-k, d = 2^S - 3^k.

**Reformulation generatrice :** En utilisant les caracteres :

> N_a(n, d) = (1/d) * SUM_{t=0}^{d-1} omega^{-at} * F_t(n)

ou omega = e^{2*pi*i/d} et

> F_t(n) = SUM_{lambda partition de n} omega^{t*g(lambda)}

La fonction generatrice de F_t(n) est :

> SUM_{n>=0} F_t(n) * q^n = SUM_{lambda} omega^{t*g(lambda)} * q^{|lambda|}

Le calcul de cette serie generatrice requiert d'exprimer g(lambda) en termes des parts de lambda.

---

## 2. CHAINE DES POURQUOI -- DEUXIEME AXE : La nature de g sur les partitions

### Niveau 0 : POURQUOI g(v) est-il si complexe sur les partitions ?

g(v) = SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}

ou (B_0,...,B_{k-1}) est la partition ecrite en ordre croissant (certains B_j repetes).

### Niveau 1 : Peut-on ecrire g en termes des MULTIPLICITES plutot que des parts ?

Soit m_b = #{j : B_j = b} = multiplicite de la part b dans la partition. Alors SUM_b m_b = k et SUM_b b * m_b = S-k.

La somme g(v) depend de l'ORDRE des parts : les poids 3^{k-1-j} sont attaches aux positions j, pas aux valeurs b. Quand on ecrit la partition en ordre croissant, le poids 3^{k-1-j} est attache a la j-ieme plus petite part.

Si les parts distinctes de la partition sont b_1 < b_2 < ... < b_l avec multiplicites m_1,...,m_l, alors les positions j correspondant a la part b_i forment le bloc d'indices :

> [M_{i-1}, M_{i-1} + m_i - 1] ou M_i = m_1 + m_2 + ... + m_i

Et la contribution a g de toutes les parts egales a b_i est :

> 2^{b_i} * SUM_{j=M_{i-1}}^{M_i - 1} 3^{k-1-j} = 2^{b_i} * 3^{k-M_i} * (3^{m_i} - 1) / 2

C'est un produit de deux exponentielles : 2^{b_i} * 3^{k-M_i}. La somme totale est :

> **g(v) = (1/2) * SUM_{i=1}^{l} (3^{m_i} - 1) * 3^{k-M_i} * 2^{b_i}**

ou M_i = m_1 + ... + m_i et la somme porte sur les parts DISTINCTES b_1 < ... < b_l.

### Niveau 2 : POURQUOI cette forme est-elle plus exploitable ?

Parce qu'elle separe :
- Les **multiplicites** m_i (qui controlent les facteurs 3^{k-M_i} et 3^{m_i}-1)
- Les **valeurs** b_i (qui controlent les facteurs 2^{b_i})
- Et ces deux ensembles sont lies par les contraintes SUM m_i = k, SUM b_i * m_i = S-k

La forme est un produit de sommes FACTORISEES dans les "lettres" de la partition (a la Horner). Et les multiplicites m_i sont exactement les "compteurs de lettres" de l'automate de Horner (R186 A3).

### Niveau 3 : POURQUOI les multiplicites aident-elles ?

Parce que les multiplicites d'une partition aleatoire sont INDEPENDANTES (Fristedt). Si on pouvait factoriser g en termes de contributions independantes des multiplicites, on pourrait appliquer un theoreme de type "Berry-Esseen modulaire".

**MAIS** la factorisation est INCOMPLETE : le facteur 3^{k-M_i} couple la multiplicite m_i avec les multiplicites precedentes M_{i-1} = m_1 + ... + m_{i-1}. C'est le couplage de Horner.

**POURQUOI le couplage de Horner empeche-t-il la factorisation ?** Parce que M_i est une somme CUMULATIVE des m_j, et le facteur 3^{k-M_i} rend chaque terme dependant de TOUTES les multiplicites precedentes. L'exponentielle 3^{-M_i} est une fonction multiplicative des multiplicites precedentes, ce qui introduit une correlation globale.

### Niveau 4 : POURQUOI ne peut-on pas lineariser le couplage de Horner ?

Le couplage est 3^{-M_i} = PROD_{j<i} 3^{-m_j}. C'est un PRODUIT, pas une somme. Dans le monde additif (Fourier), les produits deviennent des convolutions, qui sont traitables. Mais ici le produit est dans l'EXPOSANT d'une base 3, et la base 3 vit dans (Z/dZ)*.

Si on travaille modulo p | d, alors 3^{-M_i} mod p est bien defini, et c'est un element de <3> dans F_p*. La contribution de la part b_i a g mod p est :

> (3^{m_i} - 1)/2 * 3^{k-M_i} * 2^{b_i} mod p

Cet element de F_p est un produit de trois facteurs :
1. (3^{m_i}-1)/2 mod p -- depend seulement de m_i
2. 3^{k-M_i} mod p -- depend de M_i (cumul de toutes les m_j)
3. 2^{b_i} mod p -- depend seulement de b_i

Le facteur (2) couple tout. C'est l'ITERATION AFFINE de Horner vue au niveau des blocs.

---

## 3. CHAINE DES POURQUOI -- TROISIEME AXE : Les partitions ont-elles leurs propres outils ?

### Niveau 0 : POURQUOI les outils standard ne marchent pas sur les partitions ?

(Repondu aux Niveaux 1-3 de l'Axe 1.)

### Niveau 1 : Quels outils les partitions possedent-elles en propre ?

La theorie des partitions a cinq families d'outils specifiques :

**(O1) Fonctions generatrices modulaires.** La serie generatrice PROD 1/(1-q^m) est essentiellement l'inverse de la fonction eta de Dedekind. La modularite donne la formule de Hardy-Ramanujan-Rademacher (formule EXACTE pour p(n)).

**(O2) Identites de Rogers-Ramanujan et bijections de Garsia-Milne.** Ces identites relient differentes classes de partitions. Exemple : les partitions en parts differant d'au moins 2 sont equinombreuses avec les partitions en parts congrus a 1 ou 4 mod 5.

**(O3) Cranks et rangs (Dyson, Andrews-Garvan).** Le rang d'une partition lambda = (plus grande part) - (nombre de parts). Le crank est un raffinement. Ces statistiques TRIENT les partitions en classes de congruence. La decouverte du crank a prouve les congruences de Ramanujan p(5n+4) equiv 0 mod 5, p(7n+5) equiv 0 mod 7, p(11n+6) equiv 0 mod 11.

**(O4) Formes modulaires de poids demi-entier (Ono, Ahlgren).** Les congruences de Ramanujan se generalisent en une theorie systematique des congruences de partitions mod m, basee sur la theorie des formes modulaires de poids 1/2 et les operateurs de Hecke.

**(O5) Theorie de la representation de S_n et GL_n.** Les partitions de n parametrent les representations irreductibles de S_n. Les fonctions de Schur sont des caracteres. La formule des crochets (hook length formula) compte les tableaux standard.

### Niveau 2 : POURQUOI l'outil (O3) -- cranks et rangs -- est-il le plus pertinent ?

Parce que les congruences de Ramanujan sont des enonces de la forme :

> "Pour certains residus a mod m, TOUTES les partitions de n congru a a mod m ont une propriete P."

C'est structurellement identique a notre probleme :

> "Pour n = S-k, AUCUNE partition de n n'a g(lambda) equiv 0 mod d."

Les congruences de Ramanujan prouvent que CERTAINS coefficients de Fourier de 1/eta(tau) sont nuls modulo 5, 7, 11. Notre probleme demande que CERTAINS "coefficients de Fourier tordus" soient nuls.

**La difference cruciale :** Les congruences de Ramanujan concernent p(n) mod m comme fonction de n. Notre probleme concerne la distribution de g(lambda) mod d pour lambda parcourant les partitions d'un n FIXE. C'est une question INTERNE a l'ensemble des partitions de n, pas une question sur p(n) lui-meme.

### Niveau 3 : POURQUOI la distinction interne/externe est-elle un obstacle ?

Les outils modulaires (O1, O4) donnent des informations sur p(n) comme fonction de n (le "poids total" de la partition). Ils ne donnent pas directement d'informations sur les fonctionnelles f(lambda) evaluees sur les partitions de n fixe.

**SAUF** pour les fonctionnelles qui sont elles-memes des statistiques de partitions avec une structure modulaire. Le rang de Dyson et le crank d'Andrews-Garvan sont de tels exemples : leur fonction generatrice bivariee (en q et en un parametre z qui suit la statistique) est une FORME MODULAIRE ou une FORME DE JACOBI.

**Question CLE :** g(lambda) a-t-il une structure modulaire comme fonction generatrice bivariee ?

### Niveau 4 : g(lambda) a-t-il une structure modulaire ?

Considerons la serie formelle bivariee :

> G(q, z) = SUM_{lambda} z^{g(lambda)} * q^{|lambda|}

Si cette serie etait une forme de Jacobi (ou apparentee), on pourrait utiliser la theorie des formes modulaires pour analyser les coefficients de Fourier.

Le probleme est que g(lambda) depend des POSITIONS des parts (via les poids 3^{k-1-j}), et pas seulement de la "forme" de la partition. L'action du groupe symetrique sur les positions detruit la modularite.

**MAIS** pour les partitions en ordre CROISSANT (notre convention), les positions sont DETERMINEES par les parts elles-memes. Il n'y a pas de symetrie a quotient. La serie G(q,z) est bien definie, mais elle depend du parametre k (le nombre de parts), ce qui brise la structure de produit infini typique des fonctions modulaires.

**DIAGNOSTIC :** g(lambda) n'a pas de structure modulaire evidente. La serie G(q,z) n'est ni une fonction theta, ni une forme de Jacobi, ni l'inverse d'un produit eta. La raison profonde est que g melange ADDITIVEMENT les contributions des parts (via SUM) avec des poids MULTIPLICATIVEMENT structures (3^{k-1-j}), ce qui ne correspond a aucune des formes canoniques de la theorie modulaire (qui privilegient les structures purement multiplicatives -- produits, ou purement additives -- sommes de carres/triangulaires).

### Niveau 5 : Y a-t-il un CHANGEMENT DE VARIABLE qui revelerait une structure modulaire ?

Trois candidats :

**Candidat 5a : Passage aux exposants cumules.** Posons C_j = B_0 + B_1 + ... + B_j (cumuls). Alors C_{k-1} = S-k. La suite C est strictement croissante si les B sont strictement croissants, croissante au sens large sinon. Mais g(v) en termes des C_j est encore plus complique.

**Candidat 5b : Passage a la partition conjuguee.** La partition conjuguee lambda' de lambda echange lignes et colonnes du diagramme de Ferrers. La conjugaison est une involution sur les partitions de n. Si g(lambda') avait une relation simple avec g(lambda), on pourrait exploiter la symetrie. MAIS g n'est pas invariant par conjugaison (les poids 3^{k-1-j} changent quand le nombre de parts change).

**Candidat 5c : Passage a la representation de Frobenius.** Une partition lambda = (a_1,...,a_r | b_1,...,b_r) dans la notation de Frobenius, ou a_i, b_i sont les bras et jambes. Cette representation est symetrique en echange a <-> b (conjugaison). MAIS le nombre de symboles r peut varier, et g depend de k (fixe).

**VERDICT :** Aucun changement de variable canonique ne revele une structure modulaire pour g. Le couplage positionnel (les poids 3^{k-1-j} sont lies aux POSITIONS, pas aux VALEURS des parts) est l'obstacle fondamental.

---

## 4. CHAINE DES POURQUOI -- QUATRIEME AXE : L'allegorie des escaliers

### L'allegorie

Les partitions de n = S-k sont des ESCALIERS a k marches, de hauteur totale S-k. Chaque marche j a une hauteur B_j (en partant du bas). L'escalier est monotone : chaque marche est au moins aussi haute que la precedente.

g(v) est le "poids" de l'escalier : chaque marche j porte un sac de poids 3^{k-1-j} * 2^{B_j}. Les marches du bas portent les sacs les plus LOURDS (poids 3^{k-1}), et les marches du haut portent les sacs les plus LEGERS (poids 1). Mais les marches du haut sont les plus HAUTES (B_{k-1} >= B_{k-2} >= ...).

Le poids total est g(v) = somme des poids de tous les sacs.

### POURQUOI un escalier de poids exact n*d est-il "impossible" ?

**Niveau 0 :** Parce que d est grand (~ 3^k) et les escaliers sont rares (p(S-k) ~ exp(2*sqrt(k))).

**Niveau 1 :** POURQUOI la rarete ne suffit-elle pas ?

Parce que le poids g parcourt un intervalle [g_min, g_max] de taille ~ 3^k (meme ordre que d). Avec ~ 3^k/d ~ 1/(2^epsilon - 1) ~ O(1) multiples de d dans cet intervalle, il SUFFIRAIT qu'un seul des exp(2*sqrt(k)) escaliers tombe pile sur un multiple de d. La rarete ne suffit pas car le "crible" (tomber sur un multiple de d) est a densite 1/d ~ 1/3^k dans l'intervalle de poids, mais les escaliers ne sont pas uniformement distribues dans cet intervalle.

**Niveau 2 :** POURQUOI les escaliers ne sont-ils pas uniformement distribues en poids ?

A cause de l'INEGALITE DE REARRANGEMENT. Puisque les sacs les plus lourds sont en bas (poids 3^{k-1-j} decroissant) et les marches les plus hautes sont en haut (B_j croissant), la configuration est ANTI-ORDONNEE. L'inegalite de Chebyshev dit :

> g(v) <= g_shuffled (pour toute permutation des B_j)

L'escalier monotone MINIMISE le poids total. Tous les escaliers monotones ont un poids BIAISE VERS LE BAS de l'intervalle [g_min, g_max].

**Niveau 3 :** POURQUOI ce biais vers le bas devrait-il eviter les multiples de d ?

Parce que les multiples de d sont espaces de d ~ 3^k dans l'intervalle de poids. Le premier multiple positif est d, le deuxieme est 2d, etc. Le poids minimal g_min est atteint par l'escalier le plus "etale" (B_j ~ n/k pour tous j), et vaut approximativement (3^k - 1) / 2 * 2^{n/k}. Pour n/k ~ 0.585 : g_min ~ (3^k/2) * 2^{0.585} ~ 0.75 * 3^k.

Comparons : d = 2^S - 3^k. Pour epsilon = S - k*log_2(3) ~ 0.5 typique : d ~ 0.41 * 3^k. Donc g_min ~ 0.75 * 3^k > d ~ 0.41 * 3^k. Le poids minimal est SUPERIEUR a d. Donc n = g/d >= g_min/d > 1. Il y a au moins un multiple de d en-dessous de g_min ? Non -- g_min > d signifie que n >= 2, pas n = 0. Le premier multiple de d (a savoir d) est INFERIEUR a g_min.

**Le vrai probleme :** g_min et g_max sont PROCHES (les deux sont ~ C * 3^k pour des constantes differentes). L'intervalle [g_min, g_max] est de taille ~ delta * 3^k, et contient ~ delta * 3^k / d ~ delta / (2^epsilon - 1) multiples de d. Pour epsilon ~ 0.5, cela donne ~ 2.4 * delta multiples de d. Si delta est petit (escaliers tres concentres en poids), peu de multiples sont dans l'intervalle.

**POURQUOI delta est-il petit ?** C'est la question de la DISPERSION des poids g(v) sur les escaliers monotones. La dispersion Var(g) sur une partition aleatoire de n est dominee par les parts les plus grandes.

**Niveau 4 :** Y a-t-il un argument de DISPERSION qui fonctionne ?

**Proposition :** Si la dispersion de g(v) mod d sur les partitions etait TROP PETITE (tous les g(v) concentres dans un arc court modulo d), alors aucun multiple de d ne serait atteint (car les g(v) seraient dans un intervalle de taille < d modulo d).

MAIS la dispersion de g(v) dans Z (avant reduction mod d) est de taille ~ 3^k (car les poids 3^{k-1-j} * 2^{B_j} varient de 1 a ~ 3^{k-1} * 2^n). Apres reduction mod d, la dispersion "enroule" le cercle Z/dZ plusieurs fois (car g_max / d > 1). L'argument de concentration dans un arc ne s'applique donc PAS globalement.

Pour les GRANDS premiers p | d (p > g_max), la reduction mod p n'enroule PAS, et les g(v) restent dans un arc de taille g_max < p. Dans ce cas, l'argument de concentration est applicable (R185 A3, tentative 4, PARTIEL). MAIS pour les PETITS premiers, l'enroulement detruit la concentration.

**VERDICT niveau 4 :** L'argument de dispersion fonctionne pour les grands premiers (p > g_max), echoue pour les petits. Pour un argument complet, il faudrait traiter tous les premiers p | d, y compris les petits.

---

## 5. SOL ROCHEUX : LES DEUX QUESTIONS IRREDUCTIBLES

Apres 4 axes et 15+ niveaux de POURQUOI, le sol rocheux contient exactement DEUX questions irreductibles :

### Question Irreductible Q1 : Distribution de g mod p pour PETITS premiers

> Pour p | d avec p < g_max (typiquement p < 3^k), quelle est la distribution de {g(lambda) mod p : lambda partition de S-k} ?

C'est le probleme des sommes exponentielles sur les partitions. Les outils de TAN standard ne s'appliquent pas. Les outils modulaires ne s'appliquent pas non plus directement (pas de structure modulaire pour g).

**Ce qui POURRAIT marcher :** L'independance de Fristedt (les multiplicites des parts sont asymptotiquement independantes). Si on pouvait montrer que g mod p est une fonction de multiplicites APPROXIMATIVEMENT independantes, un theoreme de Berry-Esseen modulaire donnerait l'equidistribution.

**Obstacles restants :** Le couplage de Horner (3^{k-M_i}) et la petitesse de n = S-k ~ 0.585k (regime non-asymptotique).

### Question Irreductible Q2 : Existe-t-il un premier p | d qui EVITE l'image de g ?

> Existe-t-il p | d tel que 0 n'est pas dans {g(lambda) mod p : lambda partition de S-k} ?

C'est le probleme du "bon premier" (declare MORT en R185). La reformulation via la compression spectrale (R186 A2) le transforme en :

> L'image du cone monotone dans F_p^r evite-t-elle l'hyperplan ker(F) ?

**Ce qui POURRAIT marcher :** Pour p avec r = ord_p(3) tres petit (r = 3, 4, 5), le cone monotone est un objet de PETITE dimension dans F_p^r. Si p est petit (mais pas trop), on pourrait decrire exhaustivement l'image du cone et verifier l'evitement.

**Obstacles restants :** La rarete des p | d avec petit r (R186 Fait 10).

---

## 6. PISTES EMERGENTES -- CE QUI POURRAIT MARCHER

### Piste P1 (5/10) : Berry-Esseen modulaire via Fristedt

**Idee :** Utiliser l'independance approximative de Fristedt pour les multiplicites, combinee avec un theoreme de Berry-Esseen pour les sommes de variables independantes modulo m.

**Theoreme de Berry-Esseen modulaire (folklore, cf. Esseen 1945) :** Si X = SUM X_i ou les X_i sont independants a valeurs dans Z/mZ, et si aucun X_i n'est concentre sur un sous-groupe propre de Z/mZ, alors la distribution de X converge vers l'uniforme exponentiellement vite en le nombre de termes.

**Application :** Decomposer g(v) comme une somme sur les parts distinctes b_1 < b_2 < ... < b_l, chaque terme dependant de (b_i, m_i). Si les paires (b_i, m_i) sont approximativement independantes (Fristedt), et si chaque contribution 2^{b_i} * (...) mod p est non-degeneree, le Berry-Esseen modulaire donne l'equidistribution.

**Obstacle :** Le couplage de Horner (facteur 3^{k-M_i} depend des m_j precedents). Pour contourner : travailler modulo p | d tel que 3^r equiv 1 mod p avec r petit. Alors 3^{k-M_i} mod p ne depend que de M_i mod r, ce qui est une information LOCALE (pas globale). C'est exactement la compression spectrale.

**Plan d'attaque :**
1. Fixer p | d avec r = ord_p(3) petit
2. Decomposer g mod p en termes dependant de (b_i, m_i mod r)
3. Utiliser Fristedt pour l'independance des m_i
4. Appliquer Berry-Esseen modulaire

**Verrou residuel :** Trouver p | d avec r petit (rarete, R186 Fait 10).

### Piste P2 (5/10) : Fonction generatrice tordue et methode du col

**Idee :** Calculer directement

> F_t(n) = SUM_{lambda partition de n} omega^{t*g(lambda)}

par la methode du col (saddle point) appliquee a la fonction generatrice

> SUM_n F_t(n) q^n = PROD_{b>=0} SUM_{m>=0} omega^{t * f(b,m)} * q^{b*m}

ou f(b,m) est la contribution de m parts egales a b. Le PROBLEME est que f(b,m) depend du contexte (les parts precedentes), via le facteur de Horner.

**Simplification :** Si on travaille modulo p avec r petit, f(b,m) mod p ne depend que de m mod r et de la position mod r. La serie generatrice se factorise PARTIELLEMENT en r "tranches" (exactement la decomposition en fibres de R185 A2).

**Plan d'attaque :**
1. Ecrire la serie generatrice tordue comme produit partiel de r facteurs
2. Chaque facteur est une serie theta tordue par omega^{t*...}
3. Estimer chaque facteur par la methode du col
4. Montrer que le produit donne |F_t(n)| << F_0(n) = p(n) pour t != 0

**Verrou residuel :** La factorisation partielle n'est exacte que si les tranches sont INDEPENDANTES, ce qui n'est vrai qu'asymptotiquement.

### Piste P3 (6/10) : Automate de Horner + petits premiers explicites

**Idee :** L'automate de Horner (R186 A3, 12 resultats prouves) donne une description EXPLICITE du graphe des etats z_j dans Z/pZ. Pour p petit (p = 5, 7, 13, ...), ce graphe a TRES PEU d'etats. La condition de cycle (retour a 0 apres k pas avec lettres monotones) peut etre analysee EXHAUSTIVEMENT sur ce petit graphe.

**Argument :** Pour p | d, l'automate projete H_p a p etats et un alphabet effectif de s = ord_p(2) lettres. Un chemin de longueur k partant de 0 et revenant a 0 avec des lettres monotones (alpha_{B_0} <= alpha_{B_1} <= ...) doit satisfaire des contraintes de CHEMIN dans un graphe a p noeuds.

Pour p PETIT (p = 5, 7, 13), on peut lister TOUS les chemins monotones de longueur k et verifier qu'aucun ne revient a 0.

**Ce n'est PAS du calcul** si on prouve un THEOREME de la forme : "Pour p = ... et k >= k_0, aucun chemin monotone de longueur k dans H_p ne revient a 0." Cela peut se prouver par un argument de STRUCTURE du graphe (par exemple, si la monotonie force le chemin a rester dans un sous-graphe qui n'inclut pas 0).

**Verrou residuel :** Trouver UN premier p qui divise d pour TOUT k >= 3 (ou au moins pour un ensemble infini de k). C'est impossible : p | d = 2^S - 3^k depend de k. Il n'y a pas de "premier universel".

**Contournement :** Ne pas chercher un premier universel. Montrer que pour CHAQUE k >= 3, il EXISTE au moins un premier p_k | d(k) tel que l'automate H_{p_k} bloque les chemins monotones. C'est un argument "pour tout k, il existe p" au lieu de "il existe p, pour tout k".

**Difficulte :** Construire p_k explicitement pour chaque k. Cela revient a factoriser d(k) = 2^{S(k)} - 3^k pour chaque k, ce qui est un probleme ouvert en general.

### Piste P4 (4/10) : Restriction aux partitions sans petites parts

**Idee :** Pour les partitions de n = S-k ~ 0.585k, la plupart des parts sont PETITES (0, 1, 2). Les parts b = 0 contribuent 3^{k-1-j} * 1 a g(v), ce qui est un multiple de 1 (trivial mod 2). Les parts b = 1 contribuent 3^{k-1-j} * 2. Seules les parts b >= 2 contribuent des termes non-triviaux (multiples de 4, 8, ...).

Si TOUTES les parts sont 0 ou 1, alors g(v) = SUM_{j: B_j=0} 3^{k-1-j} + 2 * SUM_{j: B_j=1} 3^{k-1-j}. C'est une combinaison lineaire de puissances de 3 avec coefficients 1 ou 2. C'est un nombre en BASE 3 avec chiffres 1 et 2 uniquement. La question g(v) equiv 0 mod d devient : ce nombre base 3 est-il divisible par d ? C'est un probleme de REPRESENTATION en base 3, potentiellement traitable.

**Verrou :** Le nombre de partitions de n en parts 0 et 1 seulement est n+1 (le nombre de 1 parmi les k parts, variant de 0 a n). C'est un nombre LINEAIRE, pas exponentiel. Pour les petits n (n ~ 0.585k), la plupart des partitions ONT des parts 0 et 1 uniquement (ou presque). La restriction n'est donc pas tres restrictive.

### Piste P5 (7/10) : Hardy-Ramanujan-Rademacher pour les partitions ponderees

**Idee :** La formule de Rademacher donne une expression EXACTE pour p(n). Existe-t-il une formule de Rademacher pour

> N_a(n, d) = #{lambda partition de n : g(lambda) equiv a mod d} ?

La methode de Rademacher repose sur la modularite de la fonction generatrice. Si SUM_n N_a(n,d) q^n a une structure modulaire (ou quasi-modulaire), une formule exacte est possible.

Par l'inversion de Fourier : N_a(n,d) = (1/d) SUM_{t=0}^{d-1} omega^{-at} [q^n] F_t(q), ou F_t(q) = SUM_lambda omega^{t*g(lambda)} q^{|lambda|}.

**Le point critique :** F_t(q) est-elle une forme quasi-modulaire ?

Pour t = 0, F_0(q) = SUM_lambda q^{|lambda|} = PROD 1/(1-q^m) = q^{-1/24}/eta(tau). C'est modulaire.

Pour t != 0, F_t(q) est une deformation de 1/eta par les poids omega^{t*g(lambda)}. La question est de savoir si cette deformation preserve une structure modulaire residuelle.

**Ce qui est connu :** Les fonctions de partition "colorees" ou "ponderees" par des statistiques de partitions (comme le rang ou le crank) ont des series generatrices qui sont des formes de Jacobi ou des mock theta functions (Zagier, Zwegers, Bringmann-Ono). Si g(lambda) pouvait etre exprime comme une combinaison de telles statistiques, la machinerie des formes modulaires s'appliquerait.

**Obstacle principal :** g(lambda) est trop structure (depend des poids 3^{k-1-j} specifiques) pour etre une statistique de partition "naturelle". MAIS peut-etre qu'apres reduction modulo p (ou l'ordre de 3 est fini), g mod p devient une statistique PERIODIQUE qui a une structure modulaire.

**CETTE PISTE EST LA PLUS PROMETTEUSE** car elle attaque le probleme avec les outils NATIFS des partitions plutot que d'essayer d'adapter les outils des corps finis.

---

## 7. SYNTHESE DES CHAINES

### Arbre des POURQUOI (resume)

```
POURQUOI les 6 tentatives echouent ?
  -> g(v) mod m sur support creux (partitions)
    -> POURQUOI les outils ne marchent pas sur les partitions ?
      -> Creux + Non-algebrique + Non-independant
        -> POURQUOI ne peut-on pas adapter ?
          -> Plongements tous creux (3a)
          -> Independance de Fristedt = meilleur espoir (3b) --> P1
          -> Formes modulaires : pas de structure pour g (3c) --> P5
            -> POURQUOI pas de structure modulaire ?
              -> Couplage positionnel de Horner
                -> POURQUOI le couplage resiste ?
                  -> 3^{k-M_i} = produit cumulatif
                    -> Compression spectrale reduit MAIS pas assez

POURQUOI la rarete des partitions ne suffit pas ?
  -> g_max / d ~ O(1), plusieurs multiples dans l'intervalle
    -> POURQUOI les escaliers ne sont-ils pas distribues aleatoirement en poids ?
      -> Biais de rearrangement vers le bas
        -> POURQUOI le biais ne suffit-il pas ?
          -> Enroulement mod d pour petits p
            -> L'argument marche pour GRANDS p, pas pour petits --> P3

Existe-t-il un bon premier ?
  -> Pas de premier universel
    -> Pour CHAQUE k, existe-t-il p_k ?
      -> Automate de Horner sur petits graphes --> P3
        -> POURQUOI l'automate ne conclut-il pas ?
          -> Il faut factoriser d(k) pour chaque k
```

### La BONNE QUESTION (identifiee)

Au fond de toutes les chaines, la meme question emerge sous trois formes equivalentes :

**Forme analytique (Q1) :** Les multiplicites d'une partition de n = S-k, vues comme variables aleatoires, rendent-elles g(v) mod p EQUIDISTRIBUE via un Berry-Esseen modulaire ?

**Forme modulaire (Q5) :** La serie generatrice tordue F_t(q) = SUM_lambda omega^{t*g(lambda)} q^{|lambda|} a-t-elle un comportement "mock-modulaire" exploitable ?

**Forme combinatoire (Q3) :** Pour chaque k >= 3, peut-on exhiber un premier p | d(k) tel que le graphe de l'automate de Horner a p etats BLOQUE tous les chemins monotones de longueur k ?

---

## 8. SANITY CHECK k=1

d = 1. Pas de premier. Pas de contrainte modulaire. Un seul vecteur B_0 = 1, g = 2, n = g/d = 2. Cycle trivial. Toute la machinerie est vacuitement satisfaite. **COHERENT.**

Pour k = 2 : d = 7 (premier unique), partition (0,2) donne g = 7 = d, n = 1. Cycle fantome. L'automate H_7 a 7 etats. Le chemin 0 -> 3*0+1 = 1 -> 3*1+4 = 7 = 0 mod 7 est un retour a 0 en 2 pas avec lettres (1, 4), monotone (1 < 4). Le chemin EXISTE. **COHERENT avec le fantome k=2.**

---

## 9. TABLEAU RECAPITULATIF

| Piste | Score | Nouveaute R187 | Verrou restant |
|-------|-------|----------------|----------------|
| P1 : Berry-Esseen modulaire via Fristedt | 5/10 | Identification precise du chemin de preuve | Couplage de Horner + regime non-asymptotique |
| P2 : Serie generatrice tordue + col | 5/10 | Reformulation en produit partiel | Factorisation incomplete |
| P3 : Automate Horner + petits premiers explicites | 6/10 | "Pour tout k, existe p" au lieu de "existe p pour tout k" | Factorisation de d(k) |
| P4 : Partitions sans petites parts | 4/10 | Reduction a representation base 3 | Trop de partitions avec parts 0-1 seulement |
| **P5 : Rademacher tordu** | **7/10** | **Attaquer avec les outils NATIFS des partitions** | Structure mock-modulaire de F_t(q) non etablie |

### Le virage strategique identifie par R187

**Avant R187 :** On essayait d'adapter les outils de TAN (sommes exponentielles, Weil, Deligne) aux partitions.

**Apres R187 :** On devrait adapter les outils DES PARTITIONS (Rademacher, Fristedt, formes modulaires, mock theta functions) au probleme de Collatz.

Le probleme n'est pas dans la theorie analytique des nombres. Il est dans la theorie des partitions, a l'intersection avec la theorie des formes modulaires de poids demi-entier.

---

## 10. QUESTIONS OUVERTES POUR R188

1. **F_t(q) est-elle mock-modulaire ?** Pour t != 0 et g defini par les poids de Collatz, la serie F_t(q) = SUM_lambda omega^{t*g(lambda)} q^{|lambda|} entre-t-elle dans la classification de Zwegers ?

2. **Decomposition en tranches et produits theta.** Peut-on ecrire F_t(q) comme un produit fini de fonctions theta deformees, une par tranche de la compression spectrale ?

3. **Berry-Esseen pour les partitions contraintes.** Existe-t-il un theoreme de Berry-Esseen modulaire pour les partitions de n fixe (regime canonique), utilisant l'independance de Fristedt ?

4. **Automate de Horner pour d = 5 (k=3).** Le graphe H_5 a 5 etats. Peut-on montrer qu'aucun chemin monotone de longueur 3 ne revient a 0 ? (On sait que N(3,5) = 2 partitions : (0,0,2) et (0,1,1). On sait que g(0,0,2) = 9+3+4 = 16, g(0,1,1) = 9+6+2 = 17. g mod 5 : 16 mod 5 = 1, 17 mod 5 = 2. Aucun n'est 0 mod 5. Donc N_0(5) = 0 pour k=3. **L'automate BLOQUE.** Ce cas est RESOLUBLE.)

5. **Generalisation du blocage k=3 :** Le blocage pour k=3 repose sur le fait que les 2 partitions de 2 donnent g mod 5 in {1, 2}, evitant 0. Peut-on montrer un blocage SYSTEMATIQUE pour k >= 3 en exploitant la petitesse de p(S-k) par rapport a d ?

---

## 11. EVALUATION R187

| Critere | Score | Commentaire |
|---------|-------|-------------|
| **Nouveaute** | 7/10 | Virage strategique : TAN --> theorie des partitions. Identification de P5 (Rademacher tordu). Berry-Esseen via Fristedt. |
| **Profondeur** | 8/10 | 4 axes, 15+ niveaux de POURQUOI, sol rocheux atteint sur 2 questions irreductibles |
| **Impact** | 6/10 | Pas de preuve, mais redirection de l'approche. La question est reposee dans le BON cadre. |
| **Rigueur** | 7/10 | Sanity k=1 et k=2 verifies. Diagnostics etayes par les resultats R185/R186. |
| **Honnetete** | 10/10 | Aucun resultat survalorise. Score 4/10 maintenu pour CRT standard, nouvelle piste P5 a 7/10 sous reserve. |

---

*Round R187 : 0 preuve, 0 calcul, 5 pistes emergentes, 1 virage strategique (TAN --> theorie des partitions / formes modulaires), 2 questions irreductibles identifiees (Berry-Esseen modulaire et Rademacher tordu), sanity k=1 et k=2 verifies. La bonne question n'est pas "comment adapter Weil aux partitions" mais "comment adapter Rademacher au probleme de Collatz".*
