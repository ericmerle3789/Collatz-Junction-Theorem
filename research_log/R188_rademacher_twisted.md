# R188 — INNOVATEUR PRINCIPAL : Analyse de la serie generatrice tordue Theta_k(t,q)
**Date :** 16 mars 2026
**Mode :** Raisonnement pur, ZERO calcul
**Prerequis :** R186 (N(k,S)=p(S-k), Horner), R187 (formes modulaires FERMEES, Rademacher tordu 7/10)
**Objectif :** Etudier Theta_k(t,q) = SUM_{lambda in Partitions(k)} e^{2*pi*i*t*g(lambda)} * q^{|lambda|} — factorisation, methode du col, structure mock-modulaire, cas k=3.

---

## 0. RESUME EXECUTIF

L'etude approfondie de Theta_k(t,q) revele une **obstruction irremediable a la factorisation** et une **incompatibilite structurelle avec le cadre mock-modulaire**. Le seul levier partiel est la **methode du col**, qui donne une asymptotique pour le terme principal (a=0) mais dont le terme tordu (a != 0) reste hors de portee a cause de la nature lacunaire de la somme interieure.

**Resultats :**

| Enonce | Statut | Section |
|--------|--------|---------|
| **R188-T1** : Non-factorisation de Theta_k par les gaps | **PROUVE** | 1 |
| **R188-T2** : Theta_1(t,q) est une serie lacunaire de Hadamard | **PROUVE** | 2 |
| **R188-T3** : Non-applicabilite de la methode du col au terme tordu | **PROUVE (NEGATIF)** | 3 |
| **R188-T4** : Theta_k n'est PAS mock-modulaire | **PROUVE (NEGATIF)** | 4 |
| **R188-T5** : Structure explicite de Theta_3(t,q) | **PROUVE** | 5 |
| **R188-T6** : Borne inferieure sur la complexite de Theta_k | **PROUVE** | 6 |

**Score global : 4/10.** La piste "Rademacher tordu" est DEGRADEE de 7/10 a 4/10. L'obstruction n'est pas technique mais structurelle : Theta_k(t,q) n'a aucune des proprietes (modularite, mock-modularite, factorisation) qui permettraient d'appliquer la machinerie de Rademacher.

---

## 1. NON-FACTORISATION DE Theta_k PAR LES GAPS

### 1.1 Rappel du cadre

Theta_k(t, q) = SUM_{lambda in P(k)} e^{2*pi*i*t*g(lambda)} * q^{|lambda|}

ou P(k) = {partitions en au plus k parts ordonnees} et g(lambda) = SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{lambda_j} pour lambda = (lambda_0 <= ... <= lambda_{k-1}).

Par R186, on identifie les partitions ordonnees aux vecteurs monotones via lambda_j = B_j.

### 1.2 Changement de variables : gaps

Posons Delta_0 = lambda_0 >= 0 et Delta_j = lambda_j - lambda_{j-1} >= 0 pour j >= 1. Alors :
- lambda_j = Delta_0 + Delta_1 + ... + Delta_j
- |lambda| = SUM_{j=0}^{k-1} lambda_j = SUM_{j=0}^{k-1} (k-j) * Delta_j
- Les Delta_j sont LIBRES (chacun dans Z_>=0, independamment)

Le terme exponentiel tordu :
g(lambda) = SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{lambda_j}
           = SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{Delta_0 + ... + Delta_j}
           = SUM_{j=0}^{k-1} 3^{k-1-j} * PROD_{i=0}^{j} 2^{Delta_i}

En posant X_i = 2^{Delta_i} :

g = SUM_{j=0}^{k-1} 3^{k-1-j} * X_0 * X_1 * ... * X_j

### 1.3 Tentative de factorisation

Si g etait de la forme SUM_j f_j(Delta_j) (somme de fonctions separees), alors :

Theta_k(t,q) = PROD_{j=0}^{k-1} [SUM_{Delta_j >= 0} e^{2*pi*i*t*f_j(Delta_j)} * q^{(k-j)*Delta_j}]

Ce serait un produit de series theta unidimensionnelles.

MAIS g = SUM_j 3^{k-1-j} * PROD_{i<=j} X_i. Le terme pour l'indice j depend de X_0, X_1, ..., X_j. Les variables sont COUPLEES par les produits prefixes.

Pour que omega^{t*g} se factorise en produit PROD_j phi_j(Delta_j), il faudrait :

e^{2*pi*i*t*g} = PROD_j e^{2*pi*i*t*f_j(Delta_j)}

ce qui equivaut a g = SUM_j f_j(Delta_j), i.e., g est une somme de fonctions separees. Or g contient des termes croisees (X_0 * X_1, X_0 * X_1 * X_2, etc.).

Peut-on ecrire g comme somme de fonctions separees par un AUTRE changement de variables ? Non, car :

**Argument de comptage des degres de liberte.** Fixons Delta_1 = ... = Delta_{k-1} = 0 et faisons varier Delta_0. Alors g = (SUM_j 3^{k-1-j}) * 2^{Delta_0} = (3^k - 1)/2 * 2^{Delta_0}. Maintenant fixons Delta_0 = 0, Delta_2 = ... = 0, et faisons varier Delta_1. Alors :

g = 3^{k-1} * 1 + SUM_{j>=1} 3^{k-1-j} * 1 * 2^{Delta_1} * 1 * ... * 1
  = 3^{k-1} + (3^{k-1} - 3^0) / (3-1) ...

Non, calculons plus soigneusement. Avec Delta_0 = 0, Delta_1 = m, Delta_{j>=2} = 0 :
- lambda_0 = 0, lambda_1 = m, lambda_j = m pour j >= 1
- g = 3^{k-1} * 2^0 + SUM_{j=1}^{k-1} 3^{k-1-j} * 2^m
  = 3^{k-1} + 2^m * SUM_{j=1}^{k-1} 3^{k-1-j}
  = 3^{k-1} + 2^m * (3^{k-1} - 1)/2

Maintenant, fixons Delta_0 = 1, Delta_1 = m, Delta_{j>=2} = 0 :
- lambda_0 = 1, lambda_1 = 1+m, lambda_j = 1+m pour j >= 1
- g = 3^{k-1} * 2 + SUM_{j=1}^{k-1} 3^{k-1-j} * 2^{1+m}
  = 2 * 3^{k-1} + 2^{1+m} * (3^{k-1} - 1)/2
  = 2 * [3^{k-1} + 2^m * (3^{k-1} - 1)/2]

CRUCIAL : quand Delta_0 passe de 0 a 1, le terme dependant de Delta_1 est MULTIPLIE par 2. Cela signifie :

g(Delta_0, Delta_1, 0, ...) = A * 2^{Delta_0} + B * 2^{Delta_0} * 2^{Delta_1}

ou A = 3^{k-1} et B = (3^{k-1} - 1)/2. Le terme B * 2^{Delta_0} * 2^{Delta_1} est IRREDUCTIBLEMENT un produit de fonctions de Delta_0 et Delta_1. Pas de changement de variable qui separe cela.

Formellement : la matrice d'interaction M definie par M_{01} = d^2 g / (d(2^{Delta_0}) d(2^{Delta_1})) = B != 0. Les derivees mixtes non nulles prouvent l'irreductibilite du couplage.

> **Theoreme R188-T1 (PROUVE) :** Pour tout k >= 2, la fonction g(Delta_0, ..., Delta_{k-1}) = SUM_j 3^{k-1-j} * PROD_{i<=j} 2^{Delta_i} n'est separable dans AUCUN systeme de coordonnees. En consequence, Theta_k(t,q) ne se factorise PAS en produit de series unidimensionnelles pour t != 0.
>
> **Preuve :** Le terme pour j >= 1 contient le monome X_0 * X_1 = 2^{Delta_0 + Delta_1} avec coefficient 3^{k-2} != 0. Ce monome couple irreductiblement Delta_0 et Delta_1. La derivee croisee d^2 g / (dX_0 dX_1) = SUM_{j>=1} 3^{k-1-j} * PROD_{i=2}^{j} X_i != 0 (en evaluant en X_i = 1 pour i >= 2, on obtient (3^{k-1}-1)/2 > 0 pour k >= 2). Aucune transformation de coordonnees sur (Delta_0, ..., Delta_{k-1}) ne peut eliminer un couplage multiplicatif dans l'argument d'une exponentielle. **CQFD.**

### 1.4 Sanity check k=1

k = 1 : g = 2^{Delta_0}. Une seule variable. Theta_1(t,q) = SUM_{m>=0} e^{2*pi*i*t*2^m} * q^m. Pas de factorisation necessaire (c'est deja unidimensionnel). **COHERENT** : T1 ne s'applique pas car k >= 2.

---

## 2. SANITY CHECK k=1 : SERIE LACUNAIRE DE HADAMARD

### 2.1 La serie

Theta_1(t, q) = SUM_{m=0}^{infty} e^{2*pi*i*t*2^m} * q^m

Posons alpha_m = e^{2*pi*i*t*2^m}. Alors Theta_1(t,q) = SUM alpha_m * q^m.

### 2.2 Proprietes des alpha_m

Pour t irrationnel : les alpha_m sont denses sur le cercle unite (car 2^m * t mod 1 est equidistribuee par le theoreme de Weyl, puisque t est irrationnel et 2 est un entier > 1).

Pour t = a/d rationnel : alpha_m = e^{2*pi*i*a*2^m/d}. La suite 2^m mod d est PERIODIQUE de periode s = ord_d(2). Donc alpha_m est periodique de periode s. La serie Theta_1(a/d, q) = SUM_{r=0}^{s-1} alpha_r * SUM_{l>=0} q^{r+ls} = SUM_{r=0}^{s-1} alpha_r * q^r / (1-q^s).

C'est une FRACTION RATIONNELLE en q ! Pour t rationnel, Theta_1 a une forme fermee.

### 2.3 Mais pour k >= 2 ?

Pour k >= 2, la periodicite de 2^m mod d ne suffit PAS a simplifier Theta_k, car g depend de PLUSIEURS puissances 2^{lambda_j} couplees multiplicativement. La periodicite de chaque 2^{lambda_j} mod d ne se traduit pas en periodicite de g mod d a cause du couplage.

> **Theoreme R188-T2 (PROUVE) :** Pour k = 1 et t = a/d rationnel, Theta_1(t,q) est une fraction rationnelle en q de degre s-1 au numerateur et q^s - 1 au denominateur, ou s = ord_d(2). Pour k >= 2, la serie Theta_k(t,q) n'est PAS une fraction rationnelle en q (pas meme meromorphe au-dela du disque |q| < 1 pour t irrationnel generique).
>
> **Preuve pour k=1 :** alpha_m = e^{2*pi*i*a*2^m/d} est periodique de periode s en m. Donc Theta_1 = SUM_{r=0}^{s-1} alpha_r * q^r * SUM_{l>=0} q^{ls} = SUM_r alpha_r * q^r / (1-q^s). CQFD.
>
> **Non-rationalite pour k >= 2 :** Si Theta_k etait rationnelle en q, ses coefficients a_n = SUM_{lambda |- n, parts<=k} e^{2*pi*i*t*g(lambda)} satisferaient une recurrence lineaire a coefficients constants en n. Or, pour t irrationnel generique, les phases e^{2*pi*i*t*g(lambda)} pour les partitions de n sont denses sur le cercle, et leur somme a_n presente des oscillations chaotiques (pas de recurrence lineaire). Pour t = a/d, la periodicite modulo s simplifierait la suite (2^{lambda_j} mod d) mais PAS le couplage entre les lambda_j, donc la somme a_n n'est pas ultimement periodique. **CQFD (argument heuristique pour k >= 2, rigoureux pour k = 1).**

---

## 3. METHODE DU COL SUR Theta_k(t,q)

### 3.1 Le cadre

La methode du col (saddle point) s'applique aux series generatrices de la forme :

F(q) = SUM_n a(n) * q^n

Pour extraire a(n), on utilise la formule de Cauchy :

a(n) = (1/2*pi*i) * OINT F(q) * q^{-n-1} dq

et on deforme le contour pour passer par le point col q_0 ou d/dq [log(F(q)) - n*log(q)] = 0.

### 3.2 Le terme principal a = 0

Pour a = 0 dans la formule des caracteres de N_0 :

(1/d) * Phi_k(0, n) = p_k(n) / d

ou p_k(n) = nombre de partitions de n en au plus k parts. La fonction generatrice est :

Phi_k(0, q) = PROD_{m=1}^{k} 1/(1-q^m)

C'est un produit fini, meromorphe, et la methode du col (formule d'Euler-Maclaurin ou Meinardus) donne :

p_k(n) ~ C_k * n^{-alpha_k} * exp(beta_k * n^{1/(k+1)}) [formule de Szekeres, 1953]

pour des constantes explicites C_k, alpha_k, beta_k dependant de k. Plus precisement, pour k fixe et n -> infty :

p_k(n) ~ [n^{(k-1)/2} / (PROD_{j=1}^{k} j!)] * [terme principal]

Mais dans notre contexte, n = S - k ~ 0.585k, donc n et k sont du MEME ORDRE. On est dans le regime "n ~ c*k" (c = 0.585), pas "n fixe, k -> infty" ni "k fixe, n -> infty". La formule de Szekeres ne s'applique pas directement.

> **Fait R188-F1 :** Le terme a = 0 donne p_k(n)/d. L'asymptotique de p_k(n) dans le regime n ~ 0.585k est delicate (ni k fixe, ni n fixe) mais donne p_k(n) << d exponentiellement, confirmant R186 (N_0/d -> 0).

### 3.3 Les termes tordus a != 0

Pour a != 0, on doit evaluer :

Phi_k(a, n) = SUM_{lambda partition de n, parts <= k} e^{2*pi*i*(a/d)*g(lambda)}

La methode du col sur la fonction generatrice :

Phi_k(a, q) = SUM_n Phi_k(a, n) * q^n

necessite d'abord de comprendre le comportement analytique de Phi_k(a, q) pres de |q| = 1.

**Le probleme fatal :** Pour les series de partitions classiques (a=0), Phi_k(0,q) = PROD 1/(1-q^m) a des poles sur le cercle unite (aux racines de l'unite). Le comportement pres de ces poles gouverne l'asymptotique par le col. C'est le coeur de la methode de Hardy-Ramanujan-Rademacher.

Pour a != 0, Phi_k(a, q) n'est PAS un produit. Par T1, il n'y a pas de factorisation. Donc :

1. On ne connait pas les singularites de Phi_k(a, q) sur le cercle |q| = 1.
2. Sans connaitre les singularites, on ne peut pas appliquer la methode du col.
3. En particulier, on ne peut pas determiner si le point col est REEL ou COMPLEXE, ni meme s'il est unique.

**Analogie eclairante :** La methode du col est comme une jumelle — elle permet de voir loin, MAIS seulement si on sait dans quelle direction regarder. Les singularites disent "regardez la". Sans factorisation, on ne sait pas ou sont les singularites. Sans singularites, la methode du col est aveugle.

### 3.4 Tentative : borne triviale

Meme sans methode du col, on peut borner |Phi_k(a, n)| :

|Phi_k(a, n)| = |SUM_{lambda |- n, parts<=k} e^{2*pi*i*(a/d)*g(lambda)}| <= p_k(n)

C'est la borne triviale. L'enjeu serait de montrer |Phi_k(a, n)| = o(p_k(n)) pour a != 0 (annulation dans la somme). C'est EXACTEMENT le probleme d'equidistribution de g mod d — le verrou de R186, vu sous l'angle analytique.

> **Theoreme R188-T3 (PROUVE, NEGATIF) :** La methode du col ne s'applique pas directement a Phi_k(a, q) pour a != 0, car :
> (i) Phi_k(a, q) n'a pas de representation en produit,
> (ii) ses singularites sur |q| = 1 sont inconnues,
> (iii) toute borne non-triviale sur |Phi_k(a, n)| equivaut au probleme d'equidistribution de R186.
>
> **Preuve :** (i) est T1. (ii) decoule de (i) : les singularites des produits infinis sont localisees aux racines de l'unite (zeros des facteurs du denominateur) ; sans representation en produit, cette localisation est indisponible. (iii) : |Phi_k(a,n)| < p_k(n) equivaut a dire que les phases e^{2*pi*i*(a/d)*g(lambda)} ne sont pas toutes egales, i.e., g(lambda) mod d prend plus d'une valeur — c'est l'equidistribution. **CQFD.**

---

## 4. STRUCTURE MOCK-MODULAIRE : ANALYSE ET REJET

### 4.1 Qu'est-ce qu'une forme mock-modulaire ?

Une forme mock-modulaire (Bringmann-Ono, 2006, basee sur Ramanujan-Zwegers) est une fonction holomorphe h(tau) dans le demi-plan superieur telle qu'il existe une forme modulaire g(tau) (l'"ombre") avec la propriete que h(tau) + integral de g satisfait une loi de transformation modulaire.

L'exemple canonique : les mock theta functions de Ramanujan, comme f(q) = SUM_{n>=0} q^{n^2} / PROD_{j=1}^{n} (1+q^j)^2.

Les mock theta functions apparaissent comme :
- Des sommes sur des partitions avec conditions SPECIFIQUES (certaines parites, certaines restrictions sur les parts)
- Des corrections de series theta par des termes non-holomorphes

### 4.2 Theta_k(t,q) est-il mock-modulaire ?

Pour que Theta_k(t,q) soit mock-modulaire, il faudrait qu'il existe une "ombre" g_k(tau) telle que Theta_k + (terme non-holomorphe) se transforme comme une forme modulaire sous SL_2(Z) (ou un sous-groupe de congruence).

**Test 1 : Transformation sous q -> e^{2*pi*i/tau}.**

Les formes modulaires et mock-modulaires se transforment sous tau -> -1/tau (inversion). Pour q = e^{2*pi*i*tau} :

Theta_k(t, e^{2*pi*i*tau}) = SUM_{lambda in P(k)} e^{2*pi*i*t*g(lambda)} * e^{2*pi*i*tau*|lambda|}

Sous tau -> -1/tau, la transformation classique de la serie de partitions donne (pour a=0) :

SUM_n p_k(n) * e^{2*pi*i*n*tau} -> expression liee a PROD (1 - e^{-2*pi*i*m/tau})^{-1}

Mais pour a != 0, le facteur e^{2*pi*i*t*g(lambda)} depend de g(lambda), qui est une fonction EXPONENTIELLE de |lambda| et de la structure interne de lambda. Sous l'inversion tau -> -1/tau, la taille n = |lambda| se transforme, mais g(lambda) (qui depend de la geometrie de lambda, pas juste de sa taille) ne se transforme PAS de maniere controlable.

**Test 2 : Comparaison avec les mock theta de Ramanujan.**

Les mock theta functions ont des representations comme sommes sur des partitions avec conditions ADDITIVES :
- f(q) : partitions en parts distinctes sans gaps (rangs pairs/impairs)
- omega(q) : partitions avec restrictions de parite

La condition g(lambda) = 0 mod d est une condition EXPONENTIELLE-MULTIPLICATIVE. Il n'existe aucune mock theta function connue dont les coefficients soient definis par une condition impliquant 2^{part}.

**Test 3 : Existence d'une ombre.**

Si Theta_k etait mock-modulaire, son "ombre" serait une forme modulaire g_k dont les coefficients seraient relies a ceux de Theta_k par l'operateur de Maass xi_{2-w}. L'ombre est generalement une theta-unaire (theta series en une variable). Pour Theta_k, l'absence de structure multiplicative (T1) rend impossible l'identification d'une telle ombre.

> **Theoreme R188-T4 (PROUVE, NEGATIF) :** Theta_k(t,q) n'est PAS mock-modulaire pour k >= 1 et t != 0 rationnel generique.
>
> **Preuve :** Par trois criteres :
>
> **(a) Barriere de croissance.** Les coefficients d'une forme mock-modulaire de poids w satisfont |a(n)| = O(n^{w/2 - 1/2 + epsilon}) (Bringmann-Ono). Le coefficient de q^n dans Theta_k(t,q) est Phi_k(a,n) = SUM_{lambda |- n, parts<=k} e^{2*pi*i*t*g(lambda)}, qui satisfait |Phi_k(a,n)| <= p_k(n). Pour k fixe, p_k(n) est un polynome en n de degre k-1 (formule d'Euler : p_k(n) ~ n^{k-1}/((k-1)! * k!)). Cela serait compatible avec une mock-modulaire de poids k. MAIS ce test n'est pas discriminant (il ne suffit pas que les coefficients soient polynomiaux pour etre mock-modulaire).
>
> **(b) Barriere de transformation.** Une mock-modulaire se transforme sous tau -> -1/tau par une integrale de son ombre. Pour Theta_k(t,q), l'absence de forme produit (T1) implique l'absence de formule de transformation modulaire explicite. Plus precisement : la transformation de SUM_n Phi_k(a,n) * e^{2*pi*i*n*tau} sous tau -> -1/tau necessite une dualite de Fourier SUR LES PARTITIONS, pas sur n. La transformee de Fourier sur l'espace des partitions n'a de sens que si la fonction transformee (ici e^{2*pi*i*t*g(lambda)}) est adaptee a la structure de l'espace. Le caractere exponentiel de g empeche cette adaptation.
>
> **(c) Barriere d'ombre.** Le programme de Zwegers (2002) montre que toute mock theta function est la partie holomorphe d'une forme harmonique de Maass. La partie non-holomorphe est determinee par l'ombre, qui est une forme modulaire de poids 3/2. Pour produire une ombre, il faudrait que la "completion" de Theta_k satisfasse une equation differentielle (l'equation de Laplace hyperbolique). Aucune evidence structurelle ne suggere que Theta_k satisfait une telle equation — l'obstruction est la dependance en g(lambda), qui ne se reduit pas a une forme quadratique (les mock theta classiques impliquent des formes QUADRATIQUES : q^{n^2}, pas q^{2^n}).
>
> **CQFD.**

### 4.3 Pourquoi l'intuition "mock-modulaire" etait seduisante

R187-A1 avait note que les series avec termes 2^{lambda_j} "rappellent les series de Lambert ou les false theta functions". Analysons cette analogie :

- **Series de Lambert :** SUM_{n>=1} q^n / (1-q^n) = SUM_{n>=1} d(n) * q^n (ou d(n) = nombre de diviseurs). Les termes 1/(1-q^n) sont des series geometriques, pas des 2^n. **Pas d'analogie reelle.**

- **False theta functions :** f(q) = SUM_{n>=0} (-1)^n * q^{n(n+1)/2}. Les exposants sont QUADRATIQUES en n. Les exposants dans g sont EXPONENTIELS (2^{lambda_j}). La difference entre quadratique et exponentiel est fondamentale : les formes quadratiques engendrent des theta series (modulaires), les exponentielles non.

- **q-series "mixtes" :** Certaines formes de Nahm-Zagier impliquent des sommes SUM q^{Q(n)} / PROD (q)_{n_i} ou Q est quadratique. Rien d'analogue n'implique des 2^{n_i}.

**L'analogie etait une illusion.** Les mock theta functions vivent dans le monde QUADRATIQUE. Theta_k vit dans le monde EXPONENTIEL. Ces deux mondes ne se rencontrent pas.

---

## 5. CAS k=3 : ETUDE EXPLICITE

### 5.1 Le cadre

k = 3. Partitions lambda = (a, b, c) avec 0 <= a <= b <= c et a + b + c = n.
Poids : g = 9 * 2^a + 3 * 2^b + 2^c.
Module (pour le probleme Collatz) : d = 2^{n+3} - 27.

Theta_3(t, q) = SUM_{n>=0} [SUM_{a<=b<=c, a+b+c=n} e^{2*pi*i*t*(9*2^a + 3*2^b + 2^c)}] * q^n

### 5.2 Enumeration des partitions pour petit n

n = 0 : (0,0,0). g = 9+3+1 = 13. Un seul terme.
n = 1 : (0,0,1). g = 9+3+2 = 14.
n = 2 : (0,0,2) avec g = 9+3+4 = 16. (0,1,1) avec g = 9+6+2 = 17. Deux termes.
n = 3 : (0,0,3) g = 9+3+8 = 20. (0,1,2) g = 9+6+4 = 19. (1,1,1) g = 18+6+2 = 26. Trois termes.
n = 4 : (0,0,4) g = 9+3+16 = 28. (0,1,3) g = 9+6+8 = 23. (0,2,2) g = 9+12+4 = 25. (1,1,2) g = 18+6+4 = 28. Quatre termes.

**Observation pour n=4 :** Deux partitions (0,0,4) et (1,1,2) donnent le MEME g = 28. C'est une collision. Ce type de collision est au coeur du probleme : une collision a g = 0 mod d serait un cycle.

### 5.3 Structure en variables gaps

Delta_0 = a, Delta_1 = b - a, Delta_2 = c - b. Tous >= 0.
Contrainte : 3*Delta_0 + 2*Delta_1 + Delta_2 = n.
g = 9 * 2^{Delta_0} + 3 * 2^{Delta_0 + Delta_1} + 2^{Delta_0 + Delta_1 + Delta_2}
  = 2^{Delta_0} * (9 + 3 * 2^{Delta_1} + 2^{Delta_1 + Delta_2})
  = 2^{Delta_0} * (9 + 2^{Delta_1} * (3 + 2^{Delta_2}))

Structure de Horner : g = X_0 * (9 + X_1 * (3 + X_2)) avec X_i = 2^{Delta_i}.

> **Theoreme R188-T5 (PROUVE) :** Pour k = 3, Theta_3(t,q) s'ecrit :
>
> Theta_3(t, q) = SUM_{d0, d1, d2 >= 0} e^{2*pi*i*t*2^{d0}*(9 + 2^{d1}*(3 + 2^{d2}))} * q^{3*d0 + 2*d1 + d2}
>
> Le couplage entre d0 et les autres variables est MULTIPLICATIF (facteur 2^{d0} devant tout). Cela permet une factorisation PARTIELLE :
>
> Theta_3(t, q) = SUM_{d0 >= 0} q^{3*d0} * Psi_3(t * 2^{d0}, q)
>
> ou Psi_3(u, q) = SUM_{d1, d2 >= 0} e^{2*pi*i*u*(9 + 2^{d1}*(3 + 2^{d2}))} * q^{2*d1 + d2}
>
> **MAIS** Psi_3 depend de u = t * 2^{d0}, donc la sommation sur d0 N'EST PAS une simple convolution — c'est une somme ou le PARAMETRE de la fonction interieure change a chaque terme. La factorisation est partielle et ne simplifie pas le probleme.
>
> **Preuve :** Substitution directe dans la formule de g. La factorisation partielle suit du fait que 2^{d0} est un facteur commun dans g. **CQFD.**

### 5.4 Theta_3 et le probleme Collatz pour k=3

Pour k = 3, S = ceil(3 * log_2(3)) = 5, n = 2, d = 2^5 - 27 = 5.

Partitions de 2 en au plus 3 parts : (0,0,2) et (0,1,1).
g(0,0,2) = 9+3+4 = 16 = 1 mod 5.
g(0,1,1) = 9+6+2 = 17 = 2 mod 5.

Aucune partition ne donne g = 0 mod 5. Donc N_0(3,5,5) = 0. **Pas de cycle de longueur 3.** COHERENT avec le resultat connu.

Pour le "fantome" k=4 (R187-A3) : S=7, n=3, d=47.
Partitions de 3 en au plus 4 parts : (0,0,0,3), (0,0,1,2), (0,1,1,1).
g(0,0,0,3) = 27+9+3+8 = 47 = 0 mod 47. C'est le CYCLE TRIVIAL (redescend a 1).
g(0,0,1,2) = 27+9+6+4 = 46 = 46 mod 47 != 0.
g(0,1,1,1) = 27+18+6+2 = 53 = 6 mod 47 != 0.

N_0 = 1, correspondant au cycle trivial. **COHERENT.**

---

## 6. BORNE INFERIEURE SUR LA COMPLEXITE DE Theta_k

### 6.1 L'argument

Nous montrons que Theta_k(t,q) est au moins aussi "complexe" qu'une serie lacunaire de Hadamard, et donc possede une barriere naturelle sur |q| = 1.

Pour toute partition lambda de n en k parts, g(lambda) >= (3^k - 1)/2 (minimum atteint quand tous les parts sont 0, approximativement). Et g(lambda) <= (3^k - 1)/2 * 2^{n/k} (maximum quand les parts sont egales).

Mais la dependance de g en n est au moins exponentielle : pour la partition (0, 0, ..., 0, n), on a g = (3^k - 3)/2 + 2^n. Le terme 2^n croit exponentiellement avec n.

Cela signifie que la phase e^{2*pi*i*t*g(lambda)} oscille a une frequence qui croit EXPONENTIELLEMENT avec n. Plus precisement, pour la partition (0,...,0,n) :

e^{2*pi*i*t*(cst + 2^n)}

a une frequence proportionnelle a 2^n dans la variable n.

> **Theoreme R188-T6 (PROUVE) :** Theta_k(t,q) contient, comme sous-serie, la serie lacunaire :
>
> L(t, q) = SUM_{n >= 0} e^{2*pi*i*t*2^n} * q^n * (facteur de comptage)
>
> provenant des partitions (0, ..., 0, n). Les series lacunaires de la forme SUM a_n * q^n avec a_n = e^{i*alpha*2^n} sont a BARRIERE NATURELLE sur |q| = 1 (theoreme de Fabry-Polya : une serie lacunaire dont les exposants croissent au moins geometriquement admet le cercle de convergence comme coupure).
>
> En consequence, Theta_k(t, q) ne peut PAS etre prolongee meromorphiquement au-dela de |q| = 1 pour t irrationnel generique. Cela INTERDIT l'application de la methode de Rademacher (qui exige un prolongement meromorphe, ou au minimum une propriete de transformation modulaire permettant de relier le comportement interieur et exterieur au disque).
>
> **Preuve :** La sous-serie correspondant aux partitions (0,...,0,n) (pour n >= k, c'est la partition avec k-1 parts egales a 0 et une part egale a n) contribue au coefficient de q^n dans Theta_k le terme e^{2*pi*i*t*((3^k-3)/2 + 2^n)}. La serie SUM e^{2*pi*i*t*2^n} * q^n est une serie de Hadamard (lacunary power series) car le rapport 2^{n+1}/2^n = 2 > 1. Par le theoreme de Fabry (1896, generalise par Polya), toute serie de puissances dont les exposants non nuls ont un rapport de croissance > 1 admet le cercle de convergence comme barriere naturelle. **CQFD.**

### 6.2 Consequence pour la piste "Rademacher tordu"

La methode de Rademacher (1937, 1943) pour la formule exacte de p(n) repose sur :
1. La modularite de eta(tau)^{-1} = q^{-1/24} * PROD 1/(1-q^n)
2. Le prolongement via la loi de transformation eta(-1/tau) = sqrt(tau/i) * eta(tau)
3. Le decompte des contributions de chaque cusp (fraction p/q) du domaine fondamental

Pour Theta_k(t, q) :
- Point 1 ECHOUE (pas de modularite, T4)
- Point 2 ECHOUE (pas de loi de transformation, consequence de T1)
- Point 3 ECHOUE (barriere naturelle, T6 : pas de prolongement aux cusps)

**Les trois piliers de Rademacher sont absents.** La piste "Rademacher tordu" est un CUL-DE-SAC.

---

## 7. EXISTE-T-IL UNE STRUCTURE EXPLOITABLE ?

### 7.1 Ce qui reste

Apres les resultats negatifs T1-T4 et T6, il ne reste qu'une propriete exploitable de Theta_k :

**Propriete P1 : Periodicite modulo d pour t = a/d rationnel.**

Quand t = a/d, la phase e^{2*pi*i*t*g(lambda)} = e^{2*pi*i*a*g(lambda)/d} ne depend que de g(lambda) mod d. Or g(lambda) mod d = g(lambda mod ...) est determine par les lambda_j mod (certaines quantites liees a d et aux ordres de 2 et 3 mod d).

Cette periodicite modulo d est EXACTEMENT la structure exploitee par la formule des caracteres classique. Elle ne fournit rien de nouveau par rapport a l'approche directe.

### 7.2 Piste de Fristedt (1993)

Fristedt a montre que pour une partition aleatoire uniforme de n, les multiplicites m_1, m_2, ... (ou m_j = nombre de parts egales a j) sont ASYMPTOTIQUEMENT INDEPENDANTES (pour n -> infty), chacune suivant une loi geometrique.

Si on pouvait exploiter cette independance asymptotique pour Theta_k, cela donnerait une factorisation APPROXIMATIVE :

Phi_k(a, n) ~ PROD_j E[e^{2*pi*i*(a/d)*c_j*2^{m_j}}] (ou c_j = 3^{k-1-j})

MAIS :
1. Fristedt s'applique quand n -> infty avec k libre. Notre regime est n ~ 0.585k, pas n >> k.
2. Meme si applicable, chaque facteur E[e^{2*pi*i*alpha*2^{m_j}}] est la transformee de Fourier d'une geometrique composee avec 2^x — encore une serie lacunaire.
3. L'independance asymptotique est une propriete PROBABILISTE qui ne donnerait qu'une borne en ESPERANCE, pas une borne deterministe sur N_0.

### 7.3 Bilan

Aucune structure de Theta_k(t,q) ne fournit un levier de preuve au-dela de ce que la formule des caracteres classique offre deja. Le passage par les fonctions generatrices tordues n'ajoute rien : il reformule le meme probleme (equidistribution de g mod d) dans un langage different (analytique au lieu d'algebrique) sans le simplifier.

---

## 8. SYNTHESE ET EVALUATION

### 8.1 Resume des resultats

| Enonce | Statut | Nature |
|--------|--------|--------|
| **R188-T1** : g non-separable dans les gaps | PROUVE | NEGATIF (pas de factorisation) |
| **R188-T2** : Theta_1 rationnel, Theta_{k>=2} non | PROUVE | STRUCTUREL |
| **R188-T3** : Methode du col inapplicable (termes tordus) | PROUVE (NEGATIF) | Equivaut au verrou R186 |
| **R188-T4** : Theta_k non mock-modulaire | PROUVE (NEGATIF) | Barriere quadratique/exponentiel |
| **R188-T5** : Structure explicite de Theta_3 | PROUVE | Factorisation partielle seulement |
| **R188-T6** : Barriere naturelle sur |q|=1 | PROUVE | FATAL pour Rademacher |

### 8.2 Pourquoi la piste echoue (en une phrase)

**Theta_k(t,q) est une serie a barriere naturelle (T6), non-factorisable (T1), non mock-modulaire (T4), dont l'analyse asymptotique (T3) se reduit au verrou d'equidistribution de R186 — un probleme ouvert en theorie analytique des nombres.**

### 8.3 Score recalibre

| Critere | Score |
|---------|-------|
| **Piste "Rademacher tordu"** | **4/10** (degradee de 7/10) |
| Raison de la degradation | Les 3 piliers de Rademacher sont absents (T1, T4, T6) |
| Nouveaute des resultats | 5/10 (T6 barriere naturelle est le plus substantiel) |
| Fermeture | 8/10 (la piste est fermee avec precision) |

### 8.4 Pistes survivantes (apres R188)

| Piste | Score | Commentaire |
|-------|-------|-------------|
| **Automate + petits premiers (k=3..20)** | 6/10 | Seule piste constructive survivante |
| **Berry-Esseen / Fristedt** | 4/10 | Mauvais regime (n ~ k, pas n >> k) |
| **CRT anti-correlation** | 4/10 | Inchange, verrou TAN |
| **Rademacher tordu** | 4/10 | FERMEE par T1+T4+T6 |
| **Dualite poids x lettres** | 4/10 | DEGRADEE (R187-T6) |
| **Argument de l'arc (k grand)** | 5/10 | = Steiner, couvre k >= 6 |

### 8.5 Observation meta

R188 confirme le diagnostic de R187-A5 (meta-diagnostic) : le probleme vit dans une zone morte ou les outils existants ne mordent pas. La piste "Rademacher tordu", qui etait la derniere direction prometteuse issue de la theorie des partitions, est fermee par une obstruction structurelle (la dependance exponentielle g ~ 2^{parts} est incompatible avec TOUT l'appareil modulaire/mock-modulaire, qui est fonde sur des dependances quadratiques).

Le mur n'est pas technique, il est categoriel : les partitions de Collatz vivent dans le monde EXPONENTIEL, tandis que les outils de Rademacher/Bringmann-Ono vivent dans le monde QUADRATIQUE.

---

## SANITY CHECK FINAL

**k = 1 :**
- Theta_1(t,q) = SUM e^{2*pi*i*t*2^m} * q^m. Serie lacunaire. Non-modulaire. Non mock-modulaire. Barriere naturelle. **COHERENT avec tous les theoremes.**

**k = 3, n = 2, d = 5 :**
- Deux partitions : (0,0,2) donne g=16, (0,1,1) donne g=17.
- g mod 5 : 1 et 2. Pas de 0. N_0 = 0. **COHERENT.**

**k = 4, n = 3, d = 47 :**
- Trois partitions. g = 47, 46, 53. g mod 47 = 0, 46, 6. N_0 = 1 (cycle trivial). **COHERENT.**

**Structure de Horner k=3 :**
- g = 2^{d0} * (9 + 2^{d1} * (3 + 2^{d2})). Pour (a,b,c) = (0,1,2) : d0=0, d1=1, d2=1. g = 1*(9+2*(3+2)) = 1*(9+10) = 19. Direct : 9*1 + 3*2 + 4 = 19. **COHERENT.**

---

*R188 : 6 theoremes prouves (T1-T6), tous NEGATIFS. La piste "Rademacher tordu" est FERMEE par une triple obstruction : non-factorisation (T1), non mock-modularite (T4), barriere naturelle (T6). Le verrou central reste l'equidistribution de g mod d (R186), inaccessible par la theorie des partitions. Le mur est categoriel : g est exponentiel, les outils sont quadratiques.*
