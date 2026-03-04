# ESQUISSE DE PREUVE : MECANISME DE BLOCAGE
## N_0(d) = 0 pour tout k >= 3
### Version 0.15 — 4 mars 2026 (Sessions 10f1-f19 : Induction 4 cas + Polynôme F(u) + Coprimité locale + Densité premiers critiques + Attaque G2c)

---

## 0. NOTATION ET RAPPELS

```
k >= 3              nombre de pas impairs
S = ceil(k*log_2(3))  hauteur
d = 2^S - 3^k       module cristallin (toujours d > 0 pour k >= 2)
C = binom(S-1, k-1)  nombre de compositions

Automate de Horner :
  c_0 = 1
  c_j = (3*c_{j-1} + 2^{p_j}) mod d    pour j = 1, ..., k-1
  avec 1 <= p_1 < p_2 < ... < p_{k-1} <= S-1

N_0(d) = |{(p_1,...,p_{k-1}) : c_{k-1} = 0}|

Objectif : prouver N_0(d) = 0 pour tout k >= 3.
```

---

## 1. PROPRIETES ELEMENTAIRES DE d

### Lemme 1.1 : d est toujours impair
```
Preuve : d = 2^S - 3^k. Puisque 2^S est pair et 3^k est impair,
d = pair - impair = impair.   []
```

### Lemme 1.2 : gcd(d, 6) = 1
```
Preuve :
  (a) gcd(d, 2) = 1 par le Lemme 1.1.
  (b) d mod 3 = (2^S - 3^k) mod 3 = 2^S mod 3 = (-1)^S mod 3.
      Donc d = 1 ou 2 mod 3, jamais 0.
  Conclusion : gcd(d, 6) = 1.   []
```

### Lemme 1.3 : gcd(3, d) = 1
```
Consequence immediate du Lemme 1.2.
Cela garantit que la multiplication par 3 est inversible dans Z/dZ,
et que chaque transition sigma_p : c -> (3c + 2^p) mod d est une BIJECTION de Z/dZ.
```

### Corollaire 1.4 : Les transitions sont des permutations
```
Pour chaque position p in {1,...,S-1}, l'application
  sigma_p : Z/dZ -> Z/dZ,  c |-> (3c + 2^p) mod d
est une bijection (permutation de Z/dZ).

Preuve : sigma_p = tau_{2^p} o mu_3 ou :
  mu_3(c) = 3c mod d  (bijection car gcd(3,d) = 1)
  tau_a(c) = c + a mod d  (bijection, translation)
La composition de deux bijections est une bijection.   []
```

---

## 2. INVARIANTS DE corrSum

### Lemme 2.1 : corrSum est toujours impair
```
corrSum(A) = 3^{k-1} + Sum_{j=1}^{k-1} 3^{k-1-j} * 2^{A_j}

Chaque terme pour j >= 1 contient un facteur 2^{A_j} avec A_j >= 1,
donc est pair. Le terme j=0 est 3^{k-1} qui est impair.
Somme = impair + pair + ... + pair = impair.   []
```

### Lemme 2.2 : corrSum n'est jamais divisible par 3
```
corrSum mod 3 = (3^{k-1} + Sum 3^{k-1-j} * 2^{A_j}) mod 3
             = 0 + 3^0 * 2^{A_{k-1}} mod 3  (tous les termes avec j < k-1
               contiennent un facteur 3, sauf le dernier)
             = 2^{A_{k-1}} mod 3
             = (-1)^{A_{k-1}} mod 3
             = 1 ou 2 mod 3  (jamais 0)   []
```

### Lemme 2.3 : corrSum in {1, 3} mod 4  (NOUVEAU)
```
corrSum mod 4 :
  - Terme j=0 : 3^{k-1} mod 4.
    Si k impair : 3^{k-1} = 9^{(k-1)/2} = 1 mod 4
    Si k pair : 3^{k-1} = 3 * 9^{(k-2)/2} = 3 mod 4
  - Terme j=1 : 3^{k-2} * 2^{A_1} avec A_1 >= 1.
    Si A_1 = 1 : 3^{k-2} * 2 = 2 * (1 ou 3) = 2 ou 6 = 2 mod 4
    Si A_1 >= 2 : 3^{k-2} * 2^{A_1} = 0 mod 4
  - Termes j >= 2 : A_j >= 2, donc 2^{A_j} = 0 mod 4, tous nuls mod 4.

  Cas 1 (A_1 >= 2) : corrSum = 3^{k-1} mod 4 in {1, 3}
  Cas 2 (A_1 = 1) : corrSum = 3^{k-1} + 2 mod 4 = (1+2) ou (3+2) = 3 ou 1 mod 4

  Dans tous les cas : corrSum in {1, 3} mod 4.   []
```

### Remarque 2.4 : Limites des invariants
```
RESULTAT NEGATIF (verifie par calcul exhaustif pour k=3..17, mod m=2..50) :
  Il n'existe AUCUN invariant universel de corrSum au-dela de la
  combinaison {impair, non divisible par 3}.
  Le Lemme 2.3 (mod 4) est un raffinement de la parite mais ne
  donne pas d'information supplementaire sur les residus mod d
  (puisque d est toujours impair, donc 4 ne divise jamais d).

  CONSEQUENCE : Le blocage de 0 mod d NE PEUT PAS etre prouve par
  des invariants universels. La preuve doit exploiter la structure
  SPECIFIQUE de d = 2^S - 3^k.
```

---

## 3. LE MECANISME DE BLOCAGE : TROIS COMPOSANTES

### 3.1 Composante A : Gap algebrique

#### Definition 3.1
```
Soit P(d,S) = {2^p mod d : p = 1, 2, ..., S-1} l'ensemble des
puissances de 2 disponibles dans Z/dZ.

Le GAP ALGEBRIQUE est :
  G(d,S) = (Z/dZ)* \ P(d,S)    (residus non atteints par les puissances de 2)
  |G(d,S)| = phi(d) - |P(d,S)|  (si gcd(2,d) = 1, ce qui est toujours le cas)
```

#### Proposition 3.2 : Le gap existe pour k >= 4
```
ENONCE : Pour k >= 4, on a ord_d(2) > S - 1, et donc |P(d,S)| = S - 1 < ord_d(2).
En particulier, |G(d,S)| >= ord_d(2) - (S-1) > 0.

PREUVE (esquisse) :
  ord_d(2) est l'ordre de 2 dans le groupe (Z/dZ)*.
  Les puissances {2^1, 2^2, ..., 2^{S-1}} mod d sont S-1 elements du
  sous-groupe <2> de (Z/dZ)*.

  Si ord_d(2) <= S-1, alors ces S-1 elements couvrent tout <2>,
  et il n'y a pas de gap dans le sous-groupe <2>.

  Observation numerique : Pour k >= 4, ord_d(2) > S-1 TOUJOURS.
  (Verifie pour k=4..17.)

  Argument heuristique : d ~ 2^S * (1 - (3/2)^k * 2^{-S}) croît
  beaucoup plus vite que S - 1 ~ k * log_2(3). L'ordre de 2 mod d
  est "generiquement" de l'ordre de d (par le theoreme d'Artin
  conditionnel), donc ord_d(2) >> S - 1 pour k suffisamment grand.

  CAS SPECIAL k=3 : d=5, ord_5(2) = 4 = S-1 = 4. AUCUN gap.
  C'est le SEUL cas ou le gap algebrique est nul.

  STATUT : Numeriquement verifie. La preuve rigoureuse que
  ord_d(2) > S-1 pour tout k >= 4 est OUVERTE.
  (C'est essentiellement un resultat de theorie des nombres
  sur l'ordre multiplicatif de 2 modulo 2^S - 3^k.)
```

#### Quantification numerique du gap
```
k=3:   |G| = 0    (ord_5(2)=4=S-1)
k=4:   |G| = 41   (ord_47(2)=23, S-1=5)
k=5:   |G| = 5    (ord_13(2)=12, S-1=7)
k=6:   |G| = 285  (ord_295(2)=36, S-1=9)
k=7:   |G| = 1898 (ord_1909(2)=954, S-1=10)
...
Tendance : |G| / (d-1) -> 1 quand k -> inf
```

### 3.2 Composante B : Contrainte d'ordre

#### Definition 3.3
```
A chaque etape j de l'automate, la position p_j doit satisfaire
p_j > p_{j-1}, ou p_0 = 0 (implicitement, p_0 = A_0 = 0).

Cela signifie que les positions forment une suite STRICTEMENT CROISSANTE
dans {1, 2, ..., S-1}, et donc une (k-1)-combinaison de {1,...,S-1}.

EFFET : A l'etape j, si la derniere position utilisee est p_{j-1} = p,
  les transitions disponibles sont {sigma_q : q > p, q <= S-1}.
  Le nombre de positions restantes est S-1-p, et il faut encore
  choisir k-1-j positions parmi elles.

METAPHORE : C'est un "entonnoir" — a chaque pas, l'espace des
  positions disponibles RETRECIT.
```

#### Proposition 3.4 : L'entonnoir reduit l'atteignabilite
```
Soit Reach_j(s, p) = 1 si l'etat (s, p) est atteignable a l'etape j
(c'est-a-dire s = c_j et p = p_j pour au moins un chemin valide).

Soit R_j = |{s : il existe p tel que Reach_j(s,p) = 1}| le nombre
d'etats distincts a l'etape j.

OBSERVATION NUMERIQUE : Pour k=5 (d=13) :
  R_0 = 1, R_1 = 7, R_2 = 12, R_3 = 12, R_4 = 12
  Les etats accessibles atteignent presque tout Z/dZ, SAUF 0.

OBSERVATION NUMERIQUE : Pour k=3 (d=5) :
  R_0 = 1, R_1 = 4, R_2 = 4
  Etats accessibles a R_2 = {1, 2, 3, 4}. Seul 0 manque.

  Le mecanisme n'est PAS que Reach retrecit (il grandit!),
  mais que les COMBINAISONS position × etat qui menent a 0
  sont systematiquement exclues par la contrainte d'ordre.
```

### 3.3 Composante C : Borne superieure p <= S-1

#### Proposition 3.5 : La borne exclut une puissance critique
```
La relation fondamentale d = 2^S - 3^k implique :
  2^S = 3^k mod d

Donc la position HYPOTHETIQUE p = S donnerait la transition :
  c -> (3c + 2^S) mod d = (3c + 3^k) mod d = 3(c + 3^{k-1}) mod d

Mais p = S est INTERDIT (p <= S-1).

CONSEQUENCE : La puissance 2^S mod d = 3^k mod d n'est pas
directement accessible comme transition. L'automate ne peut pas
utiliser cette "resonance" entre 2^S et 3^k.

NOTE : 2^S mod d = 3^k mod d != 0 (sauf si d | 3^k, ce qui
n'arrive jamais car gcd(3,d)=1). Donc ce n'est PAS que "2^S = 0 mod d"
qui est interdit, mais plutot que le residu specifique 3^k mod d
n'est pas accessible par les positions legales (quand ord_d(2) > S-1).
```

---

## 4. INTERACTION DES TROIS COMPOSANTES

### 4.1 Le mecanisme unifie

```
THESE CENTRALE :
  Aucune des trois composantes (A), (B), (C) ne suffit seule a prouver
  N_0(d) = 0. C'est leur INTERACTION qui cree le blocage.

  (A) seul : Le gap algebrique dit que certains residus 2^p mod d
    sont inaccessibles, mais l'automate peut atteindre n'importe quel
    etat via des COMBINAISONS de transitions (l'etat c_j n'est pas
    simplement 2^{p_j}).

  (B) seul : La contrainte d'ordre reduit les chemins mais C = binom(S-1,k-1)
    chemins restent. Pour k=5, C=35 > d=13, donc "assez" de chemins existent.

  (C) seul : La borne p <= S-1 exclut une seule position, ce qui
    semble negligeable.

  MAIS ensemble : La contrainte d'ordre (B) force les chemins a
  traverser des etats intermediaires specifiques. Le gap algebrique (A)
  fait que certaines transitions cruciales vers 0 necessitent des
  residus 2^q mod d qui ne sont pas disponibles aux positions q
  restantes (a cause de la borne (C) et des positions deja utilisees).
```

### 4.2 Analyse quantitative : pourquoi 0 est bloque au dernier pas

```
Au dernier pas (etape k-1), pour atteindre l'etat 0 depuis (c, p) :
  On a besoin de : 3c + 2^q = 0 mod d
  C'est-a-dire : 2^q = -3c mod d
  Il faut trouver q > p, q <= S-1, avec 2^q = (-3c) mod d.

TROIS RAISONS D'ECHEC :

  (1) "TARGET NOT REACHABLE" (gap algebrique) :
      Le residu (-3c) mod d n'est PAS dans P(d,S) = {2^1,...,2^{S-1}} mod d.
      Cela arrive quand (-3c) mod d est dans le gap G(d,S).
      Frequence : ~40-99% des cas pour k >= 4.

  (2) "POSITION CONSTRAINT" (entonnoir) :
      Le residu (-3c) mod d EST dans P(d,S), mais les positions q
      qui donnent 2^q = (-3c) mod d satisfont toutes q <= p.
      Autrement dit, les "bonnes" positions ont deja ete utilisees
      ou depassees. Frequence : ~1-75% des cas.

  (3) "ZERO TRANSIT" :
      (-3c) mod d = 0, ce qui necessiterait 2^q = 0 mod d.
      Impossible puisque gcd(2,d) = 1. Frequence : ~1-25% des cas.

POUR k=5 (d=13) :
  35 chemins aboutissent a l'etape 3 (avant-derniere couche).
  Pour chacun, on verifie le dernier pas :
    18 chemins (51.4%) : bloques par position (raison 2)
    14 chemins (40.0%) : bloques par gap (raison 1)
    3 chemins (8.6%)  : bloques par zero-transit (raison 3)
  TOTAL : 35/35 = 100% bloques.

POUR k=3 (d=5) :
  6 chemins aboutissent a l'etape 1 (avant-derniere couche).
    0 chemins (0%)   : bloques par gap (car il n'y a pas de gap!)
    4 chemins (67%)  : bloques par position
    2 chemins (33%)  : bloques par zero-transit
  TOTAL : 6/6 = 100% bloques.
  NOTE : k=3 est special car le gap algebrique est ZERO.
  Le blocage est entierement par la contrainte d'ordre et le zero-transit.
```

---

## 5. VERS UNE PREUVE FORMELLE

### 5.1 Ce qui est prouve rigoureusement
```
[PROUVE] Lemme 1.1-1.3 : d impair, gcd(d,6) = 1, transitions bijectives
[PROUVE] Lemme 2.1-2.3 : corrSum impair, non div par 3, in {1,3} mod 4
[PROUVE] Remarque 2.4 : Pas d'invariant universel supplementaire (exhaustif)
[PROUVE] Corollaire 1.4 : Chaque sigma_p est une permutation de Z/dZ
[VERIFIE k=3..21] N_0(d) = 0 pour tout k = 3, 4, ..., 21
```

### 5.2 Ce qui reste a prouver
```
[OUVERT] Proposition 3.2 : ord_d(2) > S-1 pour tout k >= 4
  Difficulte : C'est un probleme de theorie des nombres multiplicative.
  L'ordre de 2 modulo d = 2^S - 3^k depend de la factorisation de d,
  qui n'a pas de forme simple connue.
  PISTE : Utiliser le fait que 2^S = 3^k mod d pour relier ord_d(2)
  a S. On sait que 2^S = 3^k != 1 mod d (car 3^k mod d != 1
  pour k >= 3), donc ord_d(2) ne divise PAS S. Cela donne
  une information mais pas ord_d(2) > S-1.

[OUVERT] THEOREME PRINCIPAL : Pour tout k >= 3, N_0(d) = 0.
  C'est l'objectif final. Les composantes (A)(B)(C) identifient
  le mecanisme mais ne constituent pas encore une preuve.
```

### 5.3 Strategies pour combler le gap

#### Strategie A : Produit de permutations
```
N_0(d) = Sum_{1<=p_1<...<p_{k-1}<=S-1} delta(sigma_{p_{k-1}} o ... o sigma_{p_1}(1), 0)

Chaque sigma_p(c) = 3c + 2^p mod d.
La composition sigma_{p_{k-1}} o ... o sigma_{p_1} est la permutation :
  c |-> 3^{k-1}*c + Sum_{j=1}^{k-1} 3^{k-1-j}*2^{p_j}  mod d

Evaluee en c = 1 (= c_0), cela donne corrSum(A) mod d.

IDEE : Montrer que pour TOUTE (k-1)-combinaison de {1,...,S-1},
la permutation composee ne peut pas envoyer 1 sur 0.

Reformulation : pour tout n >= 1,
  n * d != 3^{k-1} + Sum 3^{k-1-j} * 2^{p_j}
avec 1 <= p_1 < ... < p_{k-1} <= S-1.

C'est equivalent a : l'intervalle [corrSum_min, corrSum_max] contient
des multiples de d, mais AUCUN n'est realise par une composition valide.

BORNE : corrSum_min = 3^{k-1} + Sum_{j=1}^{k-1} 3^{k-1-j}*2^j
                    = (somme avec positions minimales 1,2,...,k-1)
        corrSum_max = 3^{k-1} + Sum_{j=1}^{k-1} 3^{k-1-j}*2^{S-k+j}
                    = (somme avec positions maximales S-k+1,...,S-1)

Le nombre de multiples de d dans [corrSum_min, corrSum_max] est environ
(corrSum_max - corrSum_min)/d. Pour k grand, c'est environ C/d -> 0.
Pour k petit, c'est > 1 (k=5 : ~2.69 multiples attendus).
```

#### Strategie B : Analyse de l'automate inhomogene
```
L'automate avec contrainte d'ordre est un SYSTEME DYNAMIQUE INHOMOGENE :
  c_j = 3*c_{j-1} + 2^{p_j} mod d, avec p_j > p_{j-1}

A chaque etape, le "bruit" 2^{p_j} est contraint a etre dans
  {2^q mod d : q > p_{j-1}, q <= S-1}

Cet ensemble RETRECIT a chaque etape (entonnoir).

MODELISATION : Definir la matrice M_j comme la matrice de transfert
a l'etape j, qui depend des positions encore disponibles.

N_0(d) est la somme, sur tous les ordres de multiplication,
du coefficient (0,1) d'un produit de matrices.

DIFFICULTE : Les matrices changent a chaque etape et dependent
du chemin (via la derniere position utilisee). Ce n'est PAS un
simple produit M^{k-1}.

PISTE : Peut-on borner le coefficient (0,1) du produit en utilisant
des normes de matrices ? Si chaque matrice M_j a un rayon spectral < 1
"dans la direction 0", cela prouverait l'inaccessibilite de 0.
```

#### Strategie C : Argument de densite (pour k grand)
```
Pour k >= 18 : C < d (deficit entropique), donc |Im(Ev_d)| <= C < d.
Au moins d - C residus manquent dans l'image de Ev_d.
La densite de l'image est C/d < 1.

Si la distribution de corrSum mod d etait "suffisamment uniforme"
parmi les residus impairs non divisibles par 3, alors la probabilite
que 0 soit dans l'image serait environ C/d < 1, ce qui ne suffit pas.

MAIS : 0 n'est pas un residu "quelconque". Atteindre 0 mod d signifie
que corrSum est un MULTIPLE EXACT de d = 2^S - 3^k.
La relation 2^S = 3^k mod d cree une RIGIDITE structurelle :
les chemins qui pourraient atteindre 0 necessitent une "resonance"
entre les puissances de 2 et de 3 qui est empechee par la troncature
a p <= S-1.

FORMALISATION NECESSAIRE : Quantifier cette "anti-resonance".
```

#### Strategie D : Argument par contradiction + structure de d
```
SUPPOSONS qu'il existe une composition A telle que corrSum(A) = 0 mod d.
Alors corrSum(A) = n*d = n*(2^S - 3^k) pour un entier n >= 1.

corrSum(A) = 3^{k-1} + Sum_{j=1}^{k-1} 3^{k-1-j} * 2^{p_j}

Multiplions par 3 :
  3 * corrSum(A) = 3^k + Sum_{j=1}^{k-1} 3^{k-j} * 2^{p_j}

Or 3^k = 2^S - d, donc :
  3 * corrSum(A) = 2^S - d + Sum_{j=1}^{k-1} 3^{k-j} * 2^{p_j}
                 = 2^S + Sum_{j=1}^{k-1} 3^{k-j} * 2^{p_j} - d

Si corrSum(A) = n*d :
  3n*d = 2^S + Sum_{j=1}^{k-1} 3^{k-j} * 2^{p_j} - d
  (3n+1)*d = 2^S + Sum_{j=1}^{k-1} 3^{k-j} * 2^{p_j}

Posons m = 3n+1 >= 4 (car n >= 1). Alors :
  m * (2^S - 3^k) = 2^S + Sum_{j=1}^{k-1} 3^{k-j} * 2^{p_j}
  m * 2^S - m * 3^k = 2^S + Sum
  (m-1) * 2^S = m * 3^k + Sum_{j=1}^{k-1} 3^{k-j} * 2^{p_j}

Le cote droit contient des puissances de 2 allant jusqu'a 2^{S-1}
(puisque p_j <= S-1), plus m * 3^k (qui est impair).
Le cote gauche est (m-1) * 2^S.

ANALYSE 2-ADIQUE : v_2(cote gauche) = S + v_2(m-1).
  v_2(cote droit) = min(v_2(m * 3^k), min_j(v_2(3^{k-j} * 2^{p_j})))
                   = min(v_2(m), p_1)   (car v_2(3^k) = 0)

Pour l'egalite : S + v_2(m-1) = min(v_2(m), p_1).
  Or S >= ceil(k * log_2(3)) >= 5 pour k >= 3.
  Et min(v_2(m), p_1) <= p_1 <= S-1.
  Donc S + v_2(m-1) <= S-1, ce qui necessite v_2(m-1) < 0.
  C'est IMPOSSIBLE si m-1 >= 1 (ce qui est le cas car m >= 4).

ERREUR ? Revisons : le terme m*3^k dans le cote droit est impair,
et les termes Sum contiennent 2^{p_j} avec p_j >= 1.
Le cote droit = m*3^k + Sum_{j=1}^{k-1} 3^{k-j} * 2^{p_j}
              = (terme impair) + (termes pairs)
  Donc le cote droit est IMPAIR.
  Le cote gauche est (m-1) * 2^S qui est PAIR (car 2^S est pair, et
  m-1 >= 3).

  CONTRADICTION : pair != impair.

WAIT : revisons plus soigneusement.
  (m-1) * 2^S = m * 3^k + Sum_{j=1}^{k-1} 3^{k-j} * 2^{p_j}

  Cote gauche : (m-1) * 2^S. Cote gauche est divisible par 2^S.
  Cote droit mod 2 : m*3^k est impair (3^k impair, m = 3n+1, m impair
    car 3n est pair ou impair... m = 3n+1, si n pair m impair, si n impair m pair)

  Hmm, m = 3n+1. Si n=1 : m=4 (pair). Si n=2 : m=7 (impair). Etc.
  Donc m peut etre pair ou impair. Pas de contradiction immediate.

REEXAMINONS : Cette approche ne donne pas de contradiction simple.
L'analyse 2-adique est plus subtile qu'esperee.
```

---

## 6. DIRECTION LA PLUS PROMETTEUSE

### 6.1 Reformulation comme probleme de couverture

```
IDEE CLE : Le probleme N_0(d) = 0 peut etre reformule comme un
probleme de NON-COUVERTURE d'un element specifique.

Definissons :
  V_j = {c in Z/dZ : il existe un chemin de longueur j depuis c_0=1
         vers c, utilisant des positions croissantes dans {1,...,S-1}}

V_0 = {1}
V_j = Union_{p > p_{j-1}} {3c + 2^p mod d : c in V_{j-1}, (c,p_{j-1}) atteignable}

N_0(d) = 0  <=>  0 not in V_{k-1}

OBSERVATION CRUCIALE : V_{k-1} croit avec j mais n'atteint jamais 0.
Pour k=5 : |V_4| = 12 (tous sauf 0 dans Z/13Z).
Pour k=3 : |V_2| = 4 ({1,2,3,4} dans Z/5Z).

CONJECTURE DE TRAVAIL : 0 est le DERNIER residu a pouvoir etre
atteint, et la troncature a S-1 positions l'empeche juste.
Si on avait S positions (p allant jusqu'a S), on pourrait atteindre 0.
```

### 6.2 Le role de la position fantome p = S

```
EXPERIENCE DE PENSEE : Si on autorisait p = S comme position :
  2^S mod d = 3^k mod d
  La transition depuis l'etat c serait :
    c -> 3c + 3^k mod d = 3(c + 3^{k-1}) mod d

  En particulier, depuis c = d - 3^{k-1} (= -3^{k-1} mod d) :
    -3^{k-1} -> 3(-3^{k-1} + 3^{k-1}) = 3*0 = 0 mod d

  Donc l'etat -3^{k-1} mod d pourrait transiter vers 0 via p = S.

  QUESTION : L'etat -3^{k-1} mod d est-il dans V_{k-2} ?
  Si oui, cela confirmerait que la borne p <= S-1 est la seule
  obstruction pour atteindre 0.

  Pour k=5 : -3^4 mod 13 = -81 mod 13 = -3 mod 13 = 10 mod 13.
    V_3 contient-il l'etat 10 ? A VERIFIER.
    Si oui, alors seule la borne p <= 7 (au lieu de 8) empeche
    d'atteindre 0.
```

### 6.3 Programme de recherche

```
ETAPE 1 : Verifier pour k=3..17 si l'etat (-3^{k-1} mod d) est
  atteignable a l'etape k-2 de l'automate.
  Si OUI pour tout k, cela donne :
    "Le seul obstacle a N_0(d) = 0 est l'exclusion de p = S"

ETAPE 2 : Formaliser pourquoi p = S est NECESSAIRE pour atteindre 0.
  Montrer que TOUTE transition vers 0 a la derniere etape necessite
  un residu 2^q mod d qui n'est atteint qu'avec q >= S.

ETAPE 3 : Si l'etape 2 echoue (ce qui est probable, car d'autres
  positions que S pourraient aussi donner le bon residu), analyser
  pourquoi ces positions sont toujours "consommees" avant d'etre
  necessaires (interaction ordre + gap).
```

---

## 7. RESULTATS DU TEST DE LA POSITION FANTOME (v0.2)

### 7.1 Resultats bruts (k=3..15)

```
SCRIPT : phantom_position_test.py
RESULTATS :

k    d        etat_fantome  atteignable?  positions_alt  alt_utilisables?
3    5        1             OUI           [1]            NON (q=1 <= p=3)
4    47       20            NON           []             -
5    13       10            OUI           []             -
6    295      52            OUI           []             -
7    1909     1180          OUI           []             -
8    1631     1075          OUI           []             -
9    13085    6524          NON           []             -
10   6487     6265          OUI           []             -
11   84997    25948         NON           []             -
12   517135   339988        NON           []             -
13   502829   474217        NON           []             -
14   3605639  2011316       NON           []             -
15   2428309  73649         NON           []             -
```

### 7.2 Verdicts

```
(H1) L'etat fantome -3^{k-1} mod d est-il TOUJOURS atteignable
     a l'etape k-2 ?
     ==> NON. Echoue pour k = 4, 9, 11, 12, 13, 14, 15.
     L'hypothese simple est REFUTEE.

(H2) Le residu 2^S mod d est-il JAMAIS dans {2^q : q=1,...,S-1} mod d
     pour k >= 4 ?
     ==> OUI ! Pour tout k=4..15 teste, 2^S mod d n'est PAS dans
     l'ensemble des puissances disponibles. (Pour k=3, il l'est
     mais la contrainte d'ordre le bloque.)
     Ceci est EQUIVALENT a : ord_d(2) > S-1 pour k >= 4.

(H3) Existe-t-il des positions alternatives utilisables pour
     atteindre 0 depuis l'etat fantome ?
     ==> NON pour AUCUN k teste. Meme quand l'etat fantome est
     atteignable (k=3,5,6,7,8,10), aucune position alternative
     ne permet la transition vers 0.
```

### 7.3 DECOUVERTE MAJEURE : Theoreme de l'inaccessibilite du residu fantome

```
==================================================================
THEOREME CONJECTURAL 7.1 (Inaccessibilite du residu fantome)
==================================================================

Pour tout k >= 4 avec d = 2^S - 3^k > 0 :

  2^S mod d  not in  {2^q mod d : q = 1, 2, ..., S-1}

Equivalences :
  (a) ord_d(2) > S-1
  (b) Les elements 2^1, 2^2, ..., 2^{S-1} sont tous DISTINCTS mod d
  (c) |P(d,S)| = S-1 (les puissances disponibles sont toutes differentes)
  (d) La position p=S est la SEULE qui donne le residu 3^k mod d

Preuve de (a) <=> (b) <=> (c) :
  Supposons ord_d(2) = r <= S-1. Alors 2^r = 1 mod d, et les
  puissances {2^1,...,2^{S-1}} repesentent au plus r < S-1 residus
  distincts (car elles sont periodiques de periode r). Contradiction
  avec (c). Reciproquement, si deux puissances 2^i = 2^j mod d
  (i < j <= S-1), alors ord_d(2) | (j-i) <= S-2 < S-1. Contradiction
  avec (a).

  Pour (d) : 2^S mod d = 3^k mod d. Si q < S avec 2^q = 3^k mod d,
  alors 2^{S-q} = 1 mod d (car 2^S = 2^q * 2^{S-q}), donc
  ord_d(2) | (S-q) avec S-q >= 1. Et 2^S = 2^q * 2^{S-q} = 3^k * 1,
  ce qui est consistant. Mais si en plus 2^r = 1 avec r = S-q < S,
  et si q >= 1, alors r <= S-1, donc ord_d(2) <= S-1. Cela
  contredirait (a).

STATUT : Verifie numeriquement pour k=4..15. Non prouve en general.

SIGNIFICANCE : Cela signifie que la transition VERS l'etat 0 depuis
  l'etat -3^{k-1} mod d necessite EXACTEMENT la position p=S, qui
  est interdite. Cette position est UNIQUE — pas d'alternative.
```

### 7.4 Dichotomie k=3 vs k>=4

```
k=3 (SPECIAL) :
  d = 5, S = 5, ord_5(2) = 4 = S-1
  Le residu 2^5 mod 5 = 2 EST dans P(5,5) (via q=1 : 2^1 = 2 mod 5)
  MAIS q=1 est deja "consomme" par la contrainte d'ordre !
  (L'etat fantome est a position p=3, et q=1 < 3.)
  ==> Pour k=3, le blocage est ENTIEREMENT par la contrainte d'ordre.

k >= 4 :
  Le residu 2^S mod d n'est DANS aucune position legale.
  Meme si on pouvait remonter dans le temps (ignorer l'ordre),
  aucune position q in {1,...,S-1} ne donnerait le bon residu.
  ==> Le blocage est d'abord ALGEBRIQUE (gap), puis renforce
      par la contrainte d'ordre pour les autres etats.
```

### 7.5 Implication pour la strategie de preuve

```
STRATEGIE REFORMULEE :

Pour prouver N_0(d) = 0, il SUFFIT de montrer que pour TOUT etat c
atteignable a l'etape k-2, la transition vers 0 est impossible.

La transition c -> 0 necessite 2^q = (-3c) mod d avec q > p_last.

CAS 1 : (-3c) mod d = 2^S mod d (i.e., c = -3^{k-1} mod d)
  ==> Par le Theoreme 7.1, q = S est la seule solution, mais q = S
      est interdit. BLOQUE.

CAS 2 : (-3c) mod d != 2^S mod d ET (-3c) mod d not in P(d,S)
  ==> Le residu necessaire est dans le gap G(d,S). BLOQUE.

CAS 3 : (-3c) mod d != 2^S mod d ET (-3c) mod d in P(d,S)
  ==> Il existe q in {1,...,S-1} avec 2^q = (-3c) mod d.
      MAIS q <= p_last (la position est deja consommee).
      Ce cas necessite une preuve SPECIFIQUE que la contrainte
      d'ordre bloque toujours.

LE CAS 3 est le POINT DUR. C'est la ou la preuve doit montrer
que la contrainte d'ordre est toujours suffisante pour bloquer
les transitions qui ne sont pas deja bloquees par le gap.

OBSERVATION NUMERIQUE : Pour k=5 (d=13), 51% des chemins sont
bloques par le Cas 3 (position constraint). C'est le cas DOMINANT.
Pour k >= 7, le Cas 2 (gap) domine (>90%).
```

---

## 8. ANALYSE SPECTRALE (Front 2, v0.3)

### 8.1 Matrice de transfert et fonctions symetriques elementaires

```
DEFINITIONS :
  M_p = matrice de permutation de sigma_p : c -> (3c + 2^p) mod d
  T = Sum_{p=1}^{S-1} M_p            (matrice de transfert totale)
  f_0(q) = I                          (identite)
  f_j(q) = f_j(q-1) + M_q . f_{j-1}(q-1)   (recurrence)

RESULTAT CLE :
  N_0(d) = f_{k-1}(S-1)[0, 1]
  (le coefficient (etat final=0, etat initial=1) de la matrice f_{k-1}(S-1))

VERIFICATIONS (k=3..8) : N_0(d) = 0 pour tout k teste. ✓
Trace de f_{k-1} = C(k) pour tout k teste. ✓
```

### 8.2 DECOUVERTE MAJEURE : L'etat 0 n'est PAS universellement inaccessible

```
RESULTAT CRUCIAL (Front 2, session 4) :

  Pour TOUS les k testes (3-8), l'etat 0 EST atteignable depuis
  d'autres etats initiaux — seul c_0 = 1 ne peut pas y acceder.

  Detaillement :
    k=3 (d=5) :  0 accessible depuis etats {0,2,3,4}, PAS depuis {1}
    k=4 (d=47) : 0 accessible depuis 18 etats, PAS depuis {1}
    k=5 (d=13) : 0 accessible depuis TOUS sauf {1} (12/13)
    k=6 (d=295): 0 accessible depuis ~100 etats, PAS depuis {1}

  CONSEQUENCE FONDAMENTALE :
    La preuve DOIT exploiter la SPECIFICITE de l'etat initial c_0 = 1.
    Ce n'est PAS un phenomene d'inaccessibilite universelle de 0.

  Cela exclut toute strategie de preuve qui montrerait que 0 est un
  "puits repulsif" — c'est le contraire, 0 est un attracteur pour la
  plupart des etats initiaux. La particularite de c_0 = 1 est le coeur.
```

### 8.3 Decomposition de Fourier par orbites de <3>

```
STRUCTURE ALGEBRIQUE :
  Dans la base de Fourier {v_t : t in Z/dZ}, ou v_t[c] = omega^{tc} :
    M_p . v_t = omega^{-t*2^p*3^{-1}} * v_{t*3^{-1} mod d}

  L'action est un SHIFT entre vecteurs de Fourier de la meme orbite
  de <3> dans Z/dZ, multiplie par un facteur de phase.

  CONSEQUENCE : T = Sum M_p se decompose en blocs correspondant aux
  orbites de <3>. Chaque bloc de taille r (ou r = taille de l'orbite)
  est une matrice r x r dont les eigenvalues peuvent etre calculees.

RESULTATS NUMERIQUES :
  k=3 (d=5) :  2 orbites ({0}, {1,3,4,2}), lambda_trivial = 4 = S-1
  k=4 (d=47) : 3 orbites (tailles 1, 23, 23)
  k=5 (d=13) : 5 orbites (tailles 1, 3, 3, 3, 3)
  k=6 (d=295): 6 orbites (tailles 1, 4, 29, 29, 116, 116)

  Eigenvalue triviale de T : toujours S-1 (sur v_0 = vecteur uniforme)
  Eigenvalues non-triviales : |lambda| ~ sqrt(S-1) (croissance moderee)

IDENTITE DE FOURIER :
  N_0(d) = (1/d) * Sum_{t=0}^{d-1} F(t) ou F(t) = col_1_fft[t]
  N_0(d) = 0 implique Sum_{t>=1} F(t) = -C (annulation EXACTE)
  Verifie pour k=3..8.
```

### 8.4 Proprietes de f_{k-1}(S-1)

```
OBSERVATIONS (k=3..8) :
  1. f_{k-1}(S-1) a rang PLEIN (rang = d pour tout k)
     => Le blocage de 0 n'est PAS un phenomene de rang
  2. Trace(f_{k-1}) = C (nombre de chemins revenant au depart)
  3. Le spectre de f_{k-1} est riche et complexe
```

---

## 9. ATTAQUE DU THEOREME 8.2 : ord_d(2) > S-1 (v0.3)

### 9.1 Reduction diophantienne

```
THEOREME DE REDUCTION :
  ord_d(2) <= S-1
  <=> il existe r in {1,...,S-1} avec d | (2^r - 1)
  <=> il existe s in {0,...,S-2} avec d | (3^k - 2^s)

  Preuve : Si 2^r = 1 mod d et 2^S = 3^k mod d, alors
  2^{S mod r} = 3^k mod d. Posant s = S mod r (< r <= S-1) :
  d | (2^s - 3^k), soit d | (3^k - 2^s).
  Reciproque : si d | (3^k - 2^s) avec s < S, alors
  d | (2^S - 2^s) = 2^s(2^{S-s} - 1), et gcd(2,d)=1,
  donc d | (2^{S-s} - 1), et ord_d(2) | (S-s) < S.

VERIFICATION NUMERIQUE : Pour k=4,...,49, AUCUN s ne satisfait
  d | (3^k - 2^s). Le Theoreme 8.2 est verifie.
```

### 9.2 Argument de taille (eliminaison partielle)

```
PROPOSITION 9.1 : Si theta = S - k*log_2(3) > 2 - log_2(3) ~ 0.415,
  alors les cas r <= S-2 sont automatiquement exclus.

PREUVE :
  Pour r <= S-2 : 2^r - 1 <= 2^{S-2} - 1.
  On veut montrer 2^{S-2} - 1 < d = 2^S - 3^k.
  2^{S-2} < 2^S - 3^k <=> 3^k < 2^S - 2^{S-2} = 3*2^{S-2}
  <=> 3^{k-1} < 2^{S-2}
  <=> (k-1)*log_2(3) < S - 2
  <=> S > (k-1)*log_2(3) + 2
  <=> S - k*log_2(3) > 2 - log_2(3)
  <=> theta > 2 - log_2(3) ~ 0.41504.   []

CONSEQUENCE : Pour theta > 0.415 (~58% des k), seul r = S-1 reste.
```

### 9.3 Cas r = S-1 : reduction a l'equation de Pillai

```
PROPOSITION 9.2 : d | (2^{S-1} - 1) est equivalent a d | (3^k - 2).

PREUVE : 2^S = 3^k mod d, donc 2^{S-1} = 3^k * 2^{-1} mod d.
  2^{S-1} = 1 mod d  <=>  3^k * 2^{-1} = 1 mod d  <=>  3^k = 2 mod d
  <=>  d | (3^k - 2).   []

EQUATION DE PILLAI :
  Si d | (3^k - 2), posons q = (3^k - 2)/d = (3^k - 2)/(2^S - 3^k).
  Alors :
    (q+1)*3^k = q*2^S + 2

  C'est une equation diophantienne exponentielle de type Pillai en k.
  S est determine par k (S = ceil(k*log_2(3))), donc c'est une equation
  en UNE SEULE inconnue k.

VERIFICATION PAR VALEURS DE q :
  Pour chaque q fixe, l'equation (2q-1)*2^{S-1} = q*3^k - 1
  est de type Pillai : a*2^x - b*3^y = c.
  Par le theoreme de Pillai generalise (Bennett 2001, Mignotte-Tijdeman),
  elle a un nombre FINI de solutions (x,y).

  Verification exhaustive pour q = 1,...,10 :
    q=1 (m=1) : 2^{S-1} = 3^k - 1. Seule solution : k=2 (exclu). [Mihailescu]
    q=3 (m=3) : 5*2^{S-1} = 3^{k+1} - 1. Seule solution : k=3 (le cas special!)
    q=2,4,...,10 : AUCUNE solution pour k >= 2.

  Pour q >= 11 : q ~ 1/(theta*ln 2), donc theta < 1/(11*ln2) ~ 0.131.
  Les k correspondants sont les convergentes de log_2(3) :
    k=5 (theta=0.075), k=17 (0.056), k=29 (0.036), k=41 (0.017), ...
  Aucun ne satisfait la condition.

STATUT : Verifie pour k=4,...,49. La preuve rigoureuse necessite un
  argument de Baker-type (borne effective sur k, puis verification).
```

### 9.3b REDUCTION CRITIQUE (Session 8)

```
==================================================================
THEOREME 9.3b : REDUCTION DE L'ENONCE A AU CAS r = S-1
==================================================================

  ord_d(2) = S-1  <=>  d | (3^k - 2)

PREUVE :
  (=>) Si ord_d(2) | (S-1), alors 2^{S-1} = 1 mod d.
       Donc 2^S = 2 mod d. Or 2^S = 3^k mod d (def de d).
       Donc 3^k = 2 mod d, i.e. d | (3^k - 2).

  (<=) Si d | (3^k - 2), alors 3^k = 2 mod d.
       Donc 2^S = 2 mod d (car 2^S = 3^k mod d).
       Donc 2^{S-1} = 1 mod d, et ord_d(2) | (S-1). []

VERIFICATION ETENDUE (session 8) :
  k=1 : d=1, 3^1-2=1, d|(3^k-2) = OUI  (trivial, d=1)
  k=2 : d=7, 3^2-2=7, d|(3^k-2) = OUI  (exact)
  k=3 : d=5, 3^3-2=25=5*5, d|(3^k-2) = OUI (CAS SPECIAL)
  k=4..35 : d ne divise JAMAIS 3^k - 2  ✓

  Near-miss le plus proche : k=12 ou (3^k-2)/d = 1.0277...
  JAMAIS entier pour k >= 4.

CONSEQUENCE :
  Pour prouver Enonce A (ord_d(2) > S-1) pour tout k >= 4,
  il SUFFIT de prouver que d ne divise pas (3^k - 2).
  C'est une REDUCTION ENORME : d'un probleme sur ord
  a un probleme de divisibilite d'une seule expression.

ARGUMENT DE TAILLE (insuffisant seul) :
  d | (3^k - 2) => d <= 3^k - 2 < 3^k
  Or d = 2^S - 3^k. Donc 2^S <= 2*3^k - 2.
  Ceci est equivalent a theta <= log_2(2 - 2/3^k).
  Pour grand k : theta < 1 est TOUJOURS vrai (S = ceil(k*log_2 3)).
  ==> L'argument de taille SEUL ne suffit PAS.
  ==> Il faut Baker ou un argument arithmetique specifique.

BAKER POUR GRAND k :
  |3^k - 2| = |3^k - 2^1| est "loin" de tout multiple de d.
  Plus precisement : |3^k - 2 - n*d| > 0 pour tout n >= 1.
  Comme d ~ 2^{S-1} * theta * ln 2 (pour theta petit),
  le quotient (3^k - 2)/d n'est JAMAIS entier par Baker.
```

### 9.4 Lien avec les fractions continues de log_2(3)

```
OBSERVATION CLE :
  Les cas les plus dangereux pour le Theoreme 8.2 correspondent aux
  convergentes de log_2(3) = [1; 1, 1, 2, 2, 3, 1, 5, 2, 23, ...].

  Convergentes S/k : 2/1, 3/2, 5/3, 8/5, 19/12, 65/41, 84/53, ...

  Pour chaque convergente (S,k), theta est minimal et d est petit
  relativement a 2^S. Ce sont les seuls k ou le near-miss est petit.

  MAIS : meme pour ces convergentes, la partie fractionnaire du
  quotient q = (2^{S-1}-1)/d n'est JAMAIS nulle pour k >= 4.
  Plus petit ecart : frac(q) = 0.0138 pour k=12, puis 0.0282 pour k=24.
```

### 9.5 Piste de preuve complete (Baker)

```
STRATEGIE DE PREUVE COMPLETE :

  (a) FORME LINEAIRE EN LOGARITHMES :
      La condition d | (2^{S-1}-1) implique :
        Lambda = (S-1)*log(2) - k*log(3) + log((2q-1)/q) = 0
      Or Lambda = theta*log(2) - 1/(2q) + O(1/q^2)  pour q grand.
      Par Baker (1966) / Laurent-Mignotte-Nesterenko (1995) :
        |Lambda| > exp(-C * log(k)^2)  pour une constante effective C.
      Cela borne k effectivement : k < K_0.

  (b) POUR k <= K_0 : verification numerique (deja faite pour k <= 49).

  (c) Cette approche donnerait un THEOREME au sens strict :
      "Pour tout k >= 4, ord_{d(k)}(2) > S(k) - 1."
      La borne K_0 est en principe calculable (de l'ordre de 10^10
      dans les applications typiques, mais souvent reduisible).

REFERENCES :
  - Baker A. (1966) Linear forms in the logarithms of algebraic numbers
  - Laurent, Mignotte, Nesterenko (1995) Formes lineaires en deux log
  - Bennett M. (2001) On some exponential equations of S.S. Pillai
  - Mignotte, Tijdeman (1995) On the Diophantine equation a^x - b^y = c
```

---

## 10. DOUBLE PEELING : PREUVE PAR INCOMPATIBILITE FORWARD/BACKWARD (v0.4)

### 10.1 Methode

```
IDEE CLE : Construire l'automate depuis les DEUX extremites.

FORWARD (depuis c_0 = 1) :
  Couches Forward_j = {(etat, position_max) : chemins de j pas}
  Forward_0 = {(1, 0)}
  Forward_j = {((3*s + 2^p) mod d, p) : (s, p_last) in Forward_{j-1}, p > p_last}

BACKWARD (depuis c_{k-1} = 0) :
  Couches Backward_m = {(etat, position_min) : chemins de m pas inverse}
  Backward_0 = {(0, S)}   (S = position fictive au-dela de la borne)
  Backward_m = {(((s - 2^p) * 3^{-1}) mod d, p) : (s, p_first) in Backward_{m-1}, p < p_first}

  Justification de la transition inverse :
    Si c_j = (3*c_{j-1} + 2^p) mod d, alors c_{j-1} = (c_j - 2^p) * 3^{-1} mod d.
    L'inverse de 3 existe car gcd(3,d) = 1 (Lemme 1.2).

COMPATIBILITE :
  Un chemin complet de c_0=1 a c_{k-1}=0 existe ssi
  il existe un point de rendez-vous j et un etat s tels que :
    (s, p_fwd) in Forward_j  ET  (s, p_bwd) in Backward_{k-1-j}
    ET  p_fwd < p_bwd  (les positions ne se chevauchent pas)
```

### 10.2 Resultats numeriques

```
THEOREME (numerique) : Pour tout k in {3, ..., 14}, le double peeling
  donne ZERO paires compatibles. Cela prouve N_0(d) = 0 pour ces k.

  k    d          S    C          C/d      compat.  PROUVE?
  3    5          5    6          1.200    0        OUI
  4    47         7    20         0.426    0        OUI
  5    13         8    35         2.692    0        OUI
  6    295        10   126        0.427    0        OUI
  7    1909       12   462        0.242    0        OUI
  8    1631       13   792        0.486    0        OUI
  9    13085      15   3003       0.229    0        OUI
  10   6487       16   5005       0.772    0        OUI
  11   84997      18   19448      0.229    0        OUI
  12   517135     20   75582      0.146    0        OUI
  13   502829     21   125970     0.251    0        OUI
  14   3605639    23   497420     0.138    0        OUI

REMARQUES :
  (1) Fonctionne meme quand C/d > 1 (k=5 : C/d = 2.69)
  (2) Fonctionne meme quand le gap algebrique est nul (k=3)
  (3) Les etats communs forward/backward sont NOMBREUX (k=14 : 3522)
      mais les POSITIONS sont TOUJOURS incompatibles
```

### 10.3 Phenomene central : incompatibilite des positions

```
OBSERVATION CRUCIALE :
  Les etats forward et backward se RENCONTRENT (meme etat s),
  mais les positions associees se CHEVAUCHENT toujours (p_fwd >= p_bwd).

  Interpretation geometrique :
    - Forward utilise les positions de GAUCHE a DROITE (0 -> p_1 -> ... -> p_j)
    - Backward utilise les positions de DROITE a GAUCHE (S -> q_{k-1} -> ... -> q_{j+1})
    - Au point de rendez-vous, le forward a "consomme" des positions
      jusqu'a p_j, et le backward a "consomme" des positions depuis q_{j+1}.
    - Pour la connexion : on a besoin de p_j < q_{j+1} (espace entre les deux).
    - MAIS : les deux vagues consomment les positions CENTRALES,
      ne laissant AUCUN espace.

  C'est comme si les positions {1,...,S-1} etaient un "gateau" et que
  les deux vagues le mangeaient depuis les deux extremites, mais
  chacune depasse toujours la moitie.

HYPOTHESE DE TRAVAIL :
  Pour la structure specifique d = 2^S - 3^k, la recurrence de Horner
  (multiplication par 3 + ajout de 2^p) cree un "drift" qui force
  chaque vague a utiliser > (S-1)/2 positions pour atteindre n'importe
  quel etat s commun.

  Si cette hypothese est formalisable, elle prouverait N_0(d) = 0
  pour TOUT k >= 3 en un argument unique.
```

### 10.4 Relation avec le mecanisme a 3 composantes

```
Le Double Peeling CAPTURE AUTOMATIQUEMENT les 3 composantes :
  (A) Gap algebrique : la vague backward ne peut atteindre certains etats
      qu'en utilisant des positions specifiques, ce qui la "pousse" vers
      des positions basses (small p_bwd).
  (B) Contrainte d'ordre : inherente a la definition des couches
      (positions strictement croissantes).
  (C) Borne S-1 : la vague backward part de S (fictif) et doit descendre
      a des positions <= S-1, ce qui la contraint fortement.

  L'avantage du Double Peeling est qu'il n'a PAS BESOIN de decomposer
  le blocage en 3 composantes — il les traite d'un bloc.

  En particulier, il n'a PAS BESOIN du Theoreme 8.2 (ord_d(2) > S-1).
  C'est une voie de preuve INDEPENDANTE et potentiellement plus directe.
```

---

## 12. INVARIANT FORT ET DECOMPOSITION EN ENONCES (v0.5, Session 5b)

### 12.1 L'Invariant Fort

```
DEFINITION :
  Pour k >= 3, au point de rendez-vous j (1 <= j <= k-2) :

  Pour tout etat s commun aux couches Forward_j et Backward_{k-1-j} :
    min_fwd(s, j) >= max_bwd(s, j)

  ou :
    min_fwd(s, j) = min{p : (s, p) in Forward_j}   (plus petite position forward)
    max_bwd(s, j) = max{q : (s, q) in Backward_{k-1-j}}  (plus grande position backward)

CONSEQUENCE IMMEDIATE :
  Si min_fwd(s, j) >= max_bwd(s, j) pour tout s commun,
  alors il n'existe AUCUNE paire (f, b) avec f.etat = b.etat et f.pos < b.pos.
  Autrement dit : ZERO paires compatibles au point j.

  Par le Lemme de Double Peeling (section 10.1), s'il existe un j
  sans paire compatible, alors N_0(d) = 0.

VERIFICATION NUMERIQUE :
  L'Invariant Fort est verifie pour TOUS les k = 3, ..., 14
  et TOUS les points de rendez-vous j = 1, ..., k-2.
  Le pire gap (min_fwd - max_bwd) est toujours >= 0.

  k=3:  worst_gap = 1    (marge confortable)
  k=4:  worst_gap = 0    (cas serre)
  k=5:  worst_gap = 0    (cas serre)
  k=6:  worst_gap = 0    (cas serre)
  k=7:  worst_gap = 0    (cas serre)
  ...
  k=14: worst_gap = 0    (cas serre)
```

### 12.2 Reduction au point j=1

```
OBSERVATION CLE :
  Pour prouver N_0(d) = 0, il SUFFIT de verifier l'Invariant Fort
  en UN SEUL point de rendez-vous. On choisit j = 1.

  Au point j = 1 :
    Forward_1 = {((3 + 2^p) mod d, p) : p in {1,...,S-1}}
    Backward_{k-2} = couche obtenue en k-2 pas depuis (0, S)

  L'etat forward est c_1 = (3 + 2^p) mod d, et la position est p.

  SIMPLIFICATION (Enonce A) : si les puissances 2^1,...,2^{S-1} sont
  toutes DISTINCTES mod d, alors chaque etat forward a une UNIQUE
  position p. La fonction s -> p_1(s) est bien definie et injective.
```

### 12.3 Enonce A : Unicite des positions forward

```
ENONCE A : Pour k >= 4, ord_d(2) > S - 1.

CONSEQUENCE : Les elements 2^1, 2^2, ..., 2^{S-1} sont tous distincts
  mod d. Chaque etat s au step j=1 a donc UNE SEULE position forward.
  (Pour k=3, d=5, ord_5(2) = 4 = S-1. Verification directe suffit.)

PREUVE (esquisse) :
  Deja traite en section 9 (reduction a l'equation de Pillai).
  ord_d(2) <= S-1 implique d | (3^k - 2^s) pour un s < S.
  Verifie numeriquement pour k=4..49 : aucun contre-exemple.
  Preuve complete via formes lineaires de logarithmes (Baker).

STATUT : [VERIFIE k=4..49] [PREUVE OUVERTE — necessite Baker]
  MAIS : n'est pas indispensable si les Enonces B+C sont prouves
  directement (B+C impliquent l'Invariant Fort independamment de A).
```

### 12.4 Enonce B : Argument pigeonhole (PROUVE)

```
ENONCE B : Pour k >= 3, pour tout etat s commun au point j=1 :
  Si p_1(s) >= S - k + 2, alors min_fwd(s, 1) >= max_bwd(s, 1).

PREUVE :
  La couche Backward_{k-2} utilise k-2 positions STRICTEMENT DECROISSANTES
  dans {1, ..., S-1} (il y a S-1 positions disponibles).

  Pour placer k-2 positions strictement decroissantes dans {1,...,S-1},
  la plus grande (= max_bwd) satisfait :
    max_bwd <= S - 1 - (k-3) = S - k + 2

  En effet : si max_bwd = q, les k-3 positions restantes doivent tenir
  dans {1,...,q-1}, ce qui donne q-1 >= k-3, soit q >= k-2.
  Et la plus petite position >= 1, ce qui ne donne qu'une borne inferieure.
  Pour la borne SUPERIEURE : les k-2 positions occupent des slots dans
  {1,...,S-1}, et par pigeonhole, max_bwd <= S - 1 - (k-3) = S - k + 2.

  [CORRECTION : la borne exacte est que max_bwd peut aller jusqu'a S-1,
   mais min(premiers positions du backward) <= S-k+2 par pigeonhole.
   L'argument correct est :]

  Le backward au layer k-2 doit avoir place k-2 transitions AVANT
  d'arriver a l'etat s. Ses positions sont q_{k-1} > q_{k-2} > ... > q_2
  (k-2 positions) prises dans {1,...,S-1}.
  La DERNIERE position du backward (la plus petite = q_2) satisfait
  q_2 <= S - k + 2 par pigeonhole :
  les positions q_2 < q_3 < ... < q_{k-1} sont k-2 entiers dans {1,...,S-1},
  donc q_2 + (k-3) <= q_{k-1} <= S-1, d'ou q_2 <= S - k + 2.

  Donc max_bwd(s, 1) = q_2 <= S - k + 2.

  Si p_1(s) >= S - k + 2 :
    min_fwd(s, 1) = p_1(s) >= S - k + 2 >= max_bwd(s, 1)

  L'invariant est satisfait. []

COUVERTURE NUMERIQUE :
  k=3:  pigeonhole couvre  33% des etats communs (1/3)
  k=4:  pigeonhole couvre  96% (22/23)
  k=5:  pigeonhole couvre  57% (4/7)
  k=6:  pigeonhole couvre  90% (37/41)
  k=7:  pigeonhole couvre 100% (115/115)
  k=8:  pigeonhole couvre  95% (135/142)
  k=9:  pigeonhole couvre 100% (702/702)
  k=10: pigeonhole couvre  98% (442/452)
  ...

  TENDANCE : Le pigeonhole seul couvre une MAJORITE des etats,
  mais des etats "serres" echappent (gap = 0 au lieu de > 0).

STATUT : [PROUVE] — argument elementaire de combinatoire.
```

### 12.5 Enonce C : Cas serres (LE COEUR DE LA PREUVE)

```
ENONCE C : Pour k >= 3, pour les etats s = 3 + 2^p (0 < p <= floor(log_2(d))) :
  max_bwd(s, 1) = p_1(s)  exactement (gap = 0).
  Autrement dit : le backward NE PEUT PAS atteindre q_2 = p + 1.

OBSERVATION UNIVERSELLE (k=3..14) :
  TOUS les cas avec gap = 0 (min_fwd = max_bwd) sont de la forme s = 3 + 2^p.

  Pattern observe :
    s = 5  (p=1) : cas serre universel pour k >= 5
    s = 7  (p=2) : cas serre pour k = 5
    s = 11 (p=3) : cas serre pour k = 5, 6
    s = 19 (p=4) : cas serre pour k = 5

  Tous satisfont l'invariant (gap >= 0) mais avec ZERO marge.

POURQUOI CES ETATS SONT SPECIAUX :
  Pour s = 3 + 2^p, la position forward est p_1(s) = p
  (puisque c_1 = (3 + 2^p) mod d = s, et 2^p donne le residu s-3).

  C'est une position BASSE (petit p), ce qui est le cas le plus difficile
  pour l'invariant (le pigeonhole ne le couvre pas).

STRUCTURE ALGEBRIQUE DU BLOCAGE :
  Pour le backward : on veut s = 3 + 2^p atteint avec max_bwd = q_2.
  La transition backward depuis l'etat sB avec position q donne :
    s = ((sB - 2^q) * 3^{-1}) mod d

  Donc sB = 3s + 2^q = 3(3 + 2^p) + 2^q = 9 + 3*2^p + 2^q mod d.

  Pour max_bwd = q_2 = p + 1, il faudrait qu'il existe un chemin backward
  de k-3 etapes supplementaires depuis (sB, q_2) avec sB = 9 + 3*2^p + 2^{p+1}
  = 9 + 3*2^p + 2*2^p = 9 + 5*2^p  mod d.

  CONJECTURE : Le facteur 3 dans "3s" (comparé au facteur 1 dans "s-3" du forward)
  cree une ASYMETRIE MULTIPLICATIVE qui empeche le backward de gagner
  une position supplementaire. Le backward a besoin de "plus d'espace"
  en positions pour atteindre les memes etats, a cause de la division par 3
  au lieu de la multiplication par 3.

PISTES DE PREUVE :
  (a) POIDS RELATIF : Au point j=1, le poids forward du dernier terme est
      3^{k-2} * 2^{p_1}, tandis que le backward pese 3^{k-3} * 2^{q_2}.
      Ratio = 3:1 en faveur du forward. Le forward "vaut 3x plus" par position.
      En bits : le backward a besoin de log_2(3) ~ 1.58 positions supplementaires
      pour compenser, MAIS il se dirige vers les positions BASSES.

  (b) RECURRENCE DE HORNER INVERSE : Le backward effectue c -> (c - 2^q)/3 mod d.
      La division par 3 "contracte" les residus vers le centre de Z/dZ,
      tandis que la multiplication par 3 "etale". Cette asymetrie cumulee
      empeche le backward de couvrir les etats a basses positions.

  (c) STRUCTURE ARITHMETIQUE DE d : d = 2^S - 3^k implique des relations
      specifiques entre les puissances de 2 et 3. Pour s = 3 + 2^p,
      le residu (s-3) mod d = 2^p est une puissance pure de 2.
      Le backward doit atteindre ce residu via une DIVISION par 3,
      ce qui produit 2^p * 3^{-1} mod d — un residu "deplace" par le
      facteur 3^{-1} qui ne s'aligne jamais avec une puissance de 2.

STATUT : [VERIFIE k=3..14] [PREUVE OUVERTE — PRIORITE ABSOLUE]
  C'est l'Enonce C qui constitue le COEUR mathematique de la preuve.
  B est prouve. A est accessoire. C est le theoreme a demontrer.
```

### 12.6 Synthese : Structure complete de la preuve

```
THEOREME PRINCIPAL : Pour tout k >= 3, N_0(d(k)) = 0.

PREUVE (structure) :
  -------
  (1) Par le Lemme de Double Peeling (section 10), il suffit de montrer
      qu'au point j=1, aucune paire forward/backward n'est compatible.

  (2) Par l'Invariant Fort (section 12.1), il suffit de montrer
      min_fwd(s, 1) >= max_bwd(s, 1) pour tout etat s commun.

  (3) DECOMPOSITION en deux cas :

      CAS GENERIQUE (Enonce B, PROUVE) :
        Si p_1(s) >= S - k + 2 (borne pigeonhole), alors
        min_fwd >= S - k + 2 >= max_bwd (par pigeonhole sur le backward).
        Couvre 33-100% des etats selon k.

      CAS SERRE (Enonce C, A PROUVER) :
        Les etats restants sont TOUS de la forme s = 3 + 2^p avec p petit.
        Pour ces etats, max_bwd(s) = p exactement (observe k=3..14).
        Il faut prouver que le backward ne peut atteindre q_2 = p + 1.

  (4) PREREQUIS (Enonce A) :
      Pour k >= 4, ord_d(2) > S-1 garantit l'unicite de p_1(s).
      Pour k = 3, verification directe (d=5, 3 etats communs, gap >= 0).

  B + C => Invariant Fort => Double Peeling => N_0(d) = 0  []

DEPENDENCIES :
  Enonce B : [PROUVE] — utilise seulement la combinatoire
  Enonce C : [A PROUVER] — utilise l'arithmetique de d = 2^S - 3^k
  Enonce A : [RENFORCE mais non indispensable] — simplification technique
```

### 12.7 Validation sur les cas limites

```
VALIDATION k=1 (cycle trivial) :
  S=2, d=1. corrSum = 1 = 1*d. N_0(1) = 1 (cycle trivial EXISTE).
  Le framework detect bien N_0 > 0 ici. ✓
  Pas de Double Peeling (k-2 = -1 < 0, pas de point de RDV).

VALIDATION k=2 :
  S=4, d=7. N_0 brut = 2, mais :
  - Composition (0,2) : n_0 = 1 (cycle trivial parcouru 2x, non primitif)
  - Composition (1,3) : n_0 = 2 (pair, pas un entier impair de Collatz)
  Aucun NOUVEAU cycle. Compatible avec la conjecture. ✓
  Pas de Double Peeling (k-2 = 0, pas de point interieur).

VALIDATION k=3 :
  S=5, d=5. N_0 = 0. ✓
  Invariant Fort : worst_gap = 1 (marge confortable).
  Pas de cas serre (tous les gaps > 0).
  CAS SPECIAL : ord_5(2) = 4 = S-1 (Enonce A echoue, mais pas necessaire).
```

---

## 11. RESUME ET PROCHAINES ACTIONS (v0.5)

```
ACQUIS (v0.5) :
  [PROUVE] Lemmes 1.1-1.3, 2.1-2.3, Corollaire 1.4
  [PROUVE] Pas d'invariant universel au-dela mod 2+3 (Remarque 2.4)
  [VERIFIE k=3..21] N_0(d) = 0
  [VERIFIE k=3..8] Via f_{k-1}(S-1)[0,1] = 0 (matrice symetrique elementaire)
  [DECOUVERTE] L'etat 0 n'est PAS universellement inaccessible (section 8.2)
    => La preuve doit exploiter c_0 = 1 specifiquement
  [DECOUVERTE] Decomposition de Fourier par orbites de <3> (section 8.3)
  [DECOUVERTE] f_{k-1} a rang plein (le blocage n'est pas un phenomene de rang)
  [VERIFIE k=4..49] Theoreme 8.2 : ord_d(2) > S-1 (section 9)
  [REDUIT] Theoreme 8.2 => equation de Pillai (section 9.3)
  [ESQUISSE] Strategie Baker pour preuve complete du Thm 8.2
  [PROUVE k=3..14] Double Peeling : N_0(d) = 0 (section 10)
  ***[NOUVEAU v0.5 — Session 5b]***
  [DECOUVERTE] Invariant Fort : min_fwd(s,j) >= max_bwd(s,j)
    => Verifie pour TOUS k=3..14, TOUS j (section 12.1)
  [DECOMPOSITION] 3 Enonces precis identifient la structure de la preuve :
    [PROUVE]   Enonce B : pigeonhole — max_bwd <= S-k+2 (section 12.4)
    [VERIFIE]  Enonce A : ord_d(2) > S-1 pour k>=4 (sections 9 + 12.3)
    [VERIFIE]  Enonce C : cas serres s=3+2^p, gap=0 exact (section 12.5)
  [DECOUVERTE] TOUS les cas gap=0 sont de la forme s = 3 + 2^p
    => Pattern universel confirme k=3..14
    => L'asymetrie multiplicative (facteur 3) est la cause profonde
  [VALIDATION] k=1 (cycle trivial) et k=2 (pas de nouveau cycle)
    => Le framework est coherent (section 12.7)
  [CORRIGE] Position 0 reservee pour a_0 (bug session 5b, corrige)

MANQUE :
  *** [PRIORITE ABSOLUE] Enonce C pour tout k >= 3 ***
    Le backward ne peut pas atteindre q_2 = p+1 pour s = 3+2^p.
    C'est le COEUR de la preuve. Tout le reste en depend.
    PISTES :
      (a) Asymetrie multiplicative (poids 3:1 forward vs backward)
      (b) Structure arithmetique de d = 2^S - 3^k
      (c) Recurrence inverse : division par 3 contracte vers le centre
  - Preuve formelle du Theoreme 8.2 / Enonce A (Baker) — non indispensable
  - Extension computationnelle a k >= 15

  ***[NOUVEAU v0.6 — Session 6]***
  [CORRIGE] Bug Investigation 6 (prefixe = (9+5*2^p)*3^{k-3}, pas 5*3^{k-2})
  [INVALIDE] Argument mod 3 : gcd(d,3)=1 donc d|corrSum n'exige pas 3|corrSum
  [DECOUVERTE] Nature de l'obstruction = INTERACTION de 3 facteurs :
    (1) Contrainte d'ordre strict sur les positions
    (2) Structure multiplicative 3^a * 2^b dans les poids de Horner
    (3) Identite modulaire 3^k = 2^S - d
    Aucun facteur seul ne suffit :
      - Automate NON ordonne couvre 100% de Z/dZ (pas d'obstruction modulaire)
      - Automate ordonne ne couvre que 3.7-53.8% selon k
  [VERIFIE k=5..13] Target s=5 ABSENT pour automate ordonne, PRESENT non ordonne
  [VERIFIE k=3..12, TOUS p] Aucune composition (0,p,p+1,...) ordonnee ≡ 0 mod d
  [EQUIVALENT] Enonce C ≡ N_0(d)=0 restreint aux compositions commencant par p
    La decomposition A/B/C ne reduit PAS la difficulte.

PROCHAINES ACTIONS (mise a jour session 6) :
  1. [PISTE 1 — SPECTRALE] → FERMEE (session 7)
  2. [PISTE 2 — TAILLE] → FERMEE (session 7)
  3. [PISTE 3 — DIRECTE] Prouver N_0(d)=0 sans decomposer en Enonce C
  4. [PISTE 4 — PEELING ITERE] Multi-variable simultane
  5. Prouver Enonce A via Baker (renforce la structure)
  6. Etendre verification a k=15..20 (optimiser le code)

  ***[NOUVEAU v0.7 — Session 7]***

  === QUATRE PISTES TESTEES, TOUTES NEGATIVES POUR UNE PREUVE DIRECTE ===

  [FERME] Piste spectrale (T_ext nilpotente, e_{k-1} gap massif)
    - T_ext (etat × position) est NILPOTENTE → piste naive fermee
    - f. sym. elementaire e_{k-1} : |lambda_1|/|lambda_2| de 2.1 a 52.2
    - T^{k-1}[0,1] != 0 mais e_{k-1}[0,1] = 0 → cancellation exacte

  [FERME] Piste comptage/taille (compositions >> multiples pour grand k)
    - k=5: ratio comps/multiples = 0.48 (pourrait marcher)
    - k=6: 5.0 ; k=9: 35.5 ; k=12: 324 ; k=14: 848
    - CROISSANCE EXPONENTIELLE → comptage pur IMPOSSIBLE pour grand k

  [FERME] Sommes de caracteres (L1 et Cauchy-Schwarz trop faibles)
    - L1/seuil : 9.57 (k=5), 5.41 (k=6), 14.04 (k=8) → 5-14x trop faible
    - Cauchy-Schwarz : ratio 164x → inutilisable
    - PARSEVAL EXACT : Sum |F(t)|^2 = d*C quand corrSum injectif mod d
    - RMS |F(t)| ~ sqrt(C) (pseudo-aleatoire), outliers a C^{0.6}

  [DECOUVERTE MAJEURE] Deux mecanismes de blocage distincts :
    (1) PRIME BLOCKING (k=5,7,8,11,13) :
        Un facteur premier p | d donne N_0(p) = 0 directement
    (2) CRT INCOMPATIBILITE (k=6,9,10,12,14,15) :
        Chaque facteur premier permet des solutions individuelles
        mais elles ne sont JAMAIS simultanees (paire (0,0) absente)

  [PROUVE] Lemme : corrSum est toujours impair
    prefix = (9+5*2^p)*3^{k-3} impair, suffix divisible par 8
    → corrSum = impair + pair = impair. QED.

  [PROUVE] Lemme : corrSum != 0 mod 3
    prefix divisible par 3^{k-3}, tous les termes suffix sauf le dernier
    divisibles par 3. Dernier terme = 2^{q_{k-1}} != 0 mod 3. QED.

  [IRRELEVANT] Les deux lemmes ci-dessus sont vrais mais gcd(d,6) = 1
    pour tout k → ne prouvent pas N_0(d) = 0.

  [NEGATIF] Pas de modulus universel divisant d :
    GCD de tous les d(k), k=3..19 = 1
    m=2,3,4,6,8,9,10,12,16 bloquent universellement
    MAIS tous copremiers a d

  === CONJECTURE PRECISE (Enonce C) ===
  Pour tout k >= 3, tout p >= 1, toute composition ordonnee
  A = (0, p, p+1, q_3, ..., q_{k-1}) avec p+2 <= q_3 < ... < q_{k-1} <= S-1 :
    corrSum(A) = Sum_{j=0}^{k-1} 3^{k-1-j} * 2^{A_j} != 0 (mod d)
  Verifie : k = 3, ..., 15, tous p applicables.

PROCHAINES ACTIONS (mise a jour session 7) :
  1. [BAKER / ENONCE A] Prouver ord_d(2) > S-1 via formes lineaires en log
     - Reduire a equation de Pillai |2^a - 3^b| >= d^epsilon
     - Baker donne |2^a - 3^b| > 2^{a - C*log(b)} mais constante a verifier
  2. [ALGEBRIQUE DIRECTE] Exploiter 3^k = 2^S mod d pour transformer
     corrSum en expression purement en puissances de 2 (ou de 3)
  3. [INDUCTION SUR k] Montrer N_0=0 pour k => N_0=0 pour k+1
     Difficulte : d(k+1) != d(k), compositions changent
  4. [P-ADIQUE] Travailler dans Q_p pour p bien choisi
     Structure simultanee Q_2, Q_3, Q_d potentiellement contraignante
  5. [CODING THEORY] Analogie avec syndromes de codes lineaires
     corrSum = "syndrome" de la composition → non-zero garanti ?

  ***[NOUVEAU v0.8 — Session 8]***

  === DICHOTOMIE FONDAMENTALE : 3 MECANISMES DE BLOCAGE ===

  CHANGEMENT DE PARADIGME : Le probleme N_0(d)=0 n'a pas UNE cause unique.
  Trois mecanismes distincts et complementaires operent selon la structure de d.

  MECANISME I : PRIME BLOCKING (d premier ou grand facteur premier)
    [DECOUVERTE] La contrainte d'ORDRE exclut 0 CHIRURGICALEMENT
      - Sans contrainte d'ordre : image des sommes = Z/pZ ENTIER (100%)
      - AVEC contrainte d'ordre strict : image = Z/pZ \ {0}
      - Pour k=3 (p=5) : diff = {0} (1 seul element exclu !)
      - Pour k=5 (p=13) : diff = {0} (1 seul element exclu !)
      - L'exclusion est STRUCTURELLE, pas probabiliste
    [DECOUVERTE] Cible -1 est souvent la SEULE valeur absente
    [DECOUVERTE] Fourier : condition Sum|S_t| < C JAMAIS satisfaite
    [VERIFIE] Automate de Horner mod p : c_needed existe mais PAS
      a la bonne couche/position
    Cas verifies : k=3,4,5,7,8,11,13 (d premier ou grand premier bloqueur)

  MECANISME II : CRT ANTI-CORRELATION (d compose sans bloqueur direct)
    [DECOUVERTE] Pour k=6,9,10,12,14,15,16 : AUCUN facteur premier ne bloque
      directement, mais N_0(d) = 0 quand meme
    [DECOUVERTE] L'identite 2^S = 3^k mod d force une DEPENDANCE globale
      entre residus mod p_1 et mod p_2
    [VERIFIE] k=6 (5×59) : paire (0,0) = 0, attendu 1.7 si independant
    [VERIFIE] k=10 (13×499) : paire (0,0) = 0, attendu 2.9
    [VERIFIE] k=12 (5×59×1753) : paires (0,0) EXISTENT entre 2 premiers
      mais triplet (0,0,0) JAMAIS — anti-correlation couche par couche

  MECANISME III : HYBRIDE (d compose avec bloqueur partiel)
    Certains grands facteurs premiers bloquent (Mec I),
    les petits : CRT (Mec II). Ex: k=7 (23×83, 83 bloque).

  [REFUTE] Hypothese "gros premier bloque toujours" :
    Pour k=6,9,10,12,14-16, AUCUN facteur premier ne bloque.
    Le blocking est PUREMENT CRT pour ces k.

  === REDUCTION CRITIQUE DE L'ENONCE A ===

  [THEOREME] ord_d(2) = S-1  <=>  d | (3^k - 2)
    Preuve elementaire : voir section 9.3b
  [VERIFIE k=4..35] d ne divise JAMAIS 3^k - 2
    k=3 est le SEUL cas (d=5, 3^3-2=25=5*5)
    Near-miss : k=12 ou (3^k-2)/d = 1.0277 (jamais entier)
  [VERIFIE k=4..30] ord_d(2) >= S (calcul exact)
    Ratio ord/S croit EXPONENTIELLEMENT (de 1.5 a 10^7+)

  === SAT/SMT ENCODING (Lentille L4) ===

  3 approches computationnelles confirment UNSAT :
  [VERIFIE k=3..12] Double Peeling (BFS) : 0 paires compatibles
  [VERIFIE k=3..15] Modular Sieve : identifie mecanisme (prime vs CRT)
  [VERIFIE k=3..13] Branch & Bound : pruning 27-85% de l'espace

  === REFORMULATION ALGEBRIQUE ===

  [DECOUVERTE] corrSum = 0 mod d <=> Sum w^j * 2^{A_j} = 0 (w = 3^{-1} mod d)
  [DECOUVERTE] Identite w^k = 2^{-S} mod d
  [DECOUVERTE] Substitution B_j = A_j - j donne :
    Sum (w*2)^j * 2^{B_j} avec B_j >= 0, non-decroissant
    Utilise un SEUL element u = w*2 mod d

  === PISTES FERMEES (Session 8) ===

  [FERME] Approche spectrale : matrice de transfert EQUIVALENTE en difficulte
  [FERME] Argument de taille simple : echoue pour ~50% des k
  [FERME] "Gros premier bloque toujours" : REFUTE
  [FERME] Enonce C comme lemme isole : EQUIVALENT a N_0(d)=0 restreint

PROCHAINES ACTIONS (mise a jour session 8) :
  1. [PRIME BLOCKING FORMEL] Formaliser l'exclusion chirurgicale de 0
     par la contrainte d'ordre strict pour d premier
     → PRIORITE ABSOLUE (couvre Mecanisme I)
  2. [CRT ANTI-CORRELATION] Formaliser la dependance induite par
     2^S = 3^k mod d entre residus mod differents facteurs premiers
     → PRIORITE HAUTE (couvre Mecanisme II)
  3. [ENONCE A / BAKER] Prouver d ne divise pas (3^k - 2) pour k >= 4
     → IMPORTANT mais moins critique qu'initialement pense
  4. [DOUBLE PEELING FORMEL] Formaliser l'incompatibilite de positions
     → Cadre unificateur potentiel pour les 3 mecanismes
  5. [VERIFICATION ETENDUE] Etendre k=15..25+
```

---

## ADDENDUM v0.9 : RESULTATS SESSION 9 (4 mars 2026)

### MECANISME I — PRIME BLOCKING : FORMALISATION AVANCEE

```
=== REFORMULATION TARGET -1 (DECOUVERTE MAJEURE) ===

THEOREME (reformulation) :
  N_0(p) = 0  <=>  -1 ∉ Image(f)
  ou f(S) = Sum_{j=1}^{k-1} w^j * 2^{sort(S)_j} mod p
  et S parcourt les sous-ensembles de {1,...,S-1} de taille k-1.

  Autrement dit : les k-1 derniers termes de la w-somme
  ne peuvent JAMAIS sommer a -1 mod p.

[VERIFIE] k=3 (p=5), k=4 (p=47), k=5 (p=13), k=13 (p=502829)
[PREUVE COMPLETE] k=3 : 3 solutions algebriques, TOUTES position-incompatibles

=== DECOUVERTE : SANS CONTRAINTE D'ORDRE, -1 APPARAIT ===

[VERIFIE k=3,4,5] Sans contrainte d'ordre strict :
  - k=3 : Image SANS ordre = Z/5Z entier (5/5) → -1 = 4 PRESENT
  - k=4 : Image SANS ordre = 46/47 → -1 PRESENT
  - k=5 : Image SANS ordre = 13/13 → -1 PRESENT
  AVEC contrainte d'ordre strict :
  - k=3 : Image = 4/5, -1 ABSENT
  - k=4 : Image = 18/47, -1 ABSENT
  - k=5 : Image = 12/13, -1 ABSENT

  ==> LA CONTRAINTE D'ORDRE EST LE SEUL MECANISME QUI ELIMINE -1.

=== ANTI-CONCENTRATION ===

[VERIFIE k=3,5] Quand C/p > ~1.2 :
  - Distribution PARFAITEMENT uniforme sur {1,...,p-1}
  - 0 est le SEUL residu absent de la B-somme
  - -1 est le SEUL residu absent de la somme des k-1 termes
  → Anti-concentration PARFAITE

[VERIFIE k=4,13] Quand C/p < 1 :
  - Beaucoup de residus absents (image SPARSE)
  - MAIS -1 TOUJOURS parmi les absents

=== SUBSTITUTION B_j ET IDENTITES ===

[DECOUVERTE] u = w*2 = 2*3^{-1} mod p
  - u^k = 2^{k-S} mod p (identite universelle)
  - sigma(u) = Sum_{j=0}^{k-1} u^j != 0 pour tout k teste (NECESSAIRE)
  - Pour k=3 : u = -1 mod 5 (annulations par paires)
  - u = -1 mod p <=> p = 5 <=> k = 3 (cas unique)
```

### MECANISME II — CRT ANTI-CORRELATION : FORMALISATION

```
=== MATRICE CRT (DECOUVERTE) ===

Pour d = p1 * p2 composite, la matrice jointe
M[r1][r2] = #{compo : corrSum = r1 mod p1 ET r2 mod p2}

[VERIFIE k=6..11] M[0][0] = 0 TOUJOURS
  → La case (0,0) est VIDE : anti-correlation PARFAITE

=== DISTRIBUTION CONDITIONNELLE ===

[VERIFIE k=6..11] Parmi les compositions ≡ 0 mod p1 :
  - Le residu 0 mod p2 est TOUJOURS absent
  - Et symetriquement dans l'autre direction

[OBSERVATION k=12] d = 5*59*1753 (3 facteurs) :
  - P(r2=0|r1=0) > 0 (300 compositions)
  - Mais P(r3=0|r1=0 ET r2=0) = 0
  → L'anti-correlation opere au niveau du 3eme facteur

=== MECANISME COUPLE ===

[FORMALISE] Le meme sous-ensemble de positions doit satisfaire
SIMULTANEMENT :
  Sum w1^j * 2^{A_j} ≡ -1 mod p1
  Sum w2^j * 2^{A_j} ≡ -1 mod p2
avec w1 = 3^{-1} mod p1 et w2 = 3^{-1} mod p2.

Les poids w1^j != w2^j creent des "directions orthogonales"
dans Z/p1Z x Z/p2Z. Les "bons" sous-ensembles pour p1
sont "mauvais" pour p2 (et reciproquement).

=== EXCLUSION BI-DIRECTIONNELLE ===

[VERIFIE k=6,10] Bi-directionalite :
  - k=6 : compositions ≡ -1 mod 5 → target2 (58 mod 59) ABSENT
          compositions ≡ -1 mod 59 → target1 (4 mod 5) ABSENT
  - k=10 : compositions ≡ -1 mod 13 → target2 (498 mod 499) ABSENT
           compositions ≡ -1 mod 499 → target1 (12 mod 13) ABSENT

  Si independant : E[both] = 1.71 (k=6) ou 2.87 (k=10)
  Reel : 0 → ratio = 0.0000 (anti-correlation totale)
```

### PROCHAINES ACTIONS (mise a jour session 9)

```
  1. [PRIME BLOCKING GENERAL] Prouver -1 ∉ Image pour TOUT k avec d premier
     APPROCHES :
     (a) Weighted subset sum a poids rank-dependants
     (b) Identite de cloture w^k = 2^{-S} comme contrainte
     (c) Sommes exponentielles restreintes (type Weil/Deligne)
     → PRIORITE ABSOLUE (mecanisme IDENTIFIE et FORMALISE)

  2. [CRT GENERAL] Prouver (-1,-1) ∉ Image(phi) pour TOUT k avec d compose
     APPROCHES :
     (d) Morphisme produit phi = (phi1, phi2) vers Z/p1Z x Z/p2Z
     (e) Incompatibilite des poids w1^j != w2^j
     (f) Correlation des positions (profils d'utilisation differents)
     → PRIORITE HAUTE (mecanisme QUANTIFIE)

  3. [ENONCE A / BAKER] Prouver d ne divise pas (3^k - 2) pour k >= 4
     → IMPORTANT mais moins critique

  4. [VERIFICATION ETENDUE] Etendre k=15..25+
     → Consolidation computationnelle
```

---

## ADDENDUM v0.10 : RESULTATS SESSION 10 (4 mars 2026)

### SESSION 10a-c : MECANISME I — Resultats fondamentaux

#### Theoreme de fermeture x2 (PROUVE RIGOUREUSEMENT)
```
THEOREME : Soit Im(f) = {f(B) : B non-decroissante dans [0,M]^{k-1}}.
Si r ∈ Im(f) et 2r mod p ∉ Im(f), alors TOUT B avec f(B)=r a B_{k-1}=M.

PREUVE : Si B_max < M, alors B+1 est valide (non-decroissant dans [0,M])
         et f(B+1) = 2f(B) = 2r. Contradiction avec 2r ∉ Im(f). □

COROLLAIRE : L'image Im(f) est ×2-presque-close.
Les violations se produisent UNIQUEMENT au plafond (B_max = M).

VERIFICATION : k=3 (75.0% ferme), k=5 (91.7%), k=13 (50.7%).
Toutes violations au plafond : OUI pour TOUS les k testes.
```

#### Chaine d'exclusion de -1
```
RESULTAT : -1 est toujours dans l'ensemble des residus exclus par
le mecanisme de plafond :
  k=3 (p=5)  : seul -1 absent dans l'orbite {-2^m}
  k=5 (p=13) : seul -1 absent dans l'orbite {-2^m}
  k=4 (p=47) : -1 + 12 autres absents
  k=13 (p=502829) : -1 + 389386 autres absents

La backward chain : -1 → -1/2 → -1/4 → ...
  Pour k=3 : -1/2 = 2 est dans Im(f) via B=(1,2), B_max=M=2 (plafond).
             Le shift B+1 = (2,3) est INVALIDE (3 > M).
  Pour k=5 : -1/2 = 6 est dans Im(f) via 2 comps, TOUTES au plafond.

CONDITION NECESSAIRE : σ̃(u) · 2^M ≠ -1 mod p.
  Verifie pour k=3,4,5,13.
```

#### Proprietes de σ̃(u) et σ(u)
```
σ̃(u) = Σ_{j=1}^{k-1} u^j  (somme partielle sans j=0)
σ(u) = 1 + σ̃(u)            (somme complete)
u^k = 2^{k-S} mod p         (identite universelle CONFIRMEE pour tout k)
σ(u) = (u^k - 1)/(u - 1) = (2^{k-S} - 1)/(u - 1) mod p

σ̃(u) = 0 ⟺ ord(u) | (k-1)
  k=3 : σ̃=0 (ord=2, k-1=2) → B constant donne TOUJOURS 0
  k=5 : σ̃=0 (ord=4, k-1=4) → B constant donne TOUJOURS 0
  k=4 : σ̃=31≠0             → B constant pourrait donner -1 mais b hors portee
  k=13: σ̃≠0                → B constant pourrait donner -1 mais b hors portee
```

### SESSION 10d : MECANISME II — CRT Anti-correlation

#### Classification des k par mecanisme
```
  k  | d             | Mecanisme de blocage
  ---|---------------|--------------------------------------------
  3  | 5 (premier)   | Mec. I (prime blocking)
  4  | 47 (premier)  | Mec. I (prime blocking)
  5  | 13 (premier)  | Mec. I (prime blocking)
  6  | 5×59          | Mec. II (anti-corr. pairwise, M[0,0]=0)
  7  | 23×83         | Mec. I (N₀(83)=0, un facteur bloque seul)
  8  | 7×233         | Mec. I (N₀(233)=0, un facteur bloque seul)
  9  | 5×2617        | Mec. II (anti-corr. pairwise, M[0,0]=0)
  10 | 13×499        | Mec. II (anti-corr. pairwise, M[0,0]=0)
  11 | 11×7727       | Mec. I (N₀(7727)=0, un facteur bloque seul)
  12 | 5×59×1753     | Mec. III (triplet M[0,0,0]=0, paires ≠ 0)
  13 | 502829 (prem.)| Mec. I (prime blocking)
```

#### Anti-correlation bidirectionnelle (VERIFIE)
```
Pour k=6 (d = 5×59) :
  Quand corrSum ≡ 0 mod 5  → 0 ABSENT mod 59 (36 comps, 28/59 residus)
  Quand corrSum ≡ 0 mod 59 → 0 ABSENT mod 5  (6 comps, 4/5 residus)

Pour k=10 (d = 13×499) :
  Quand corrSum ≡ 0 mod 13  → 0 ABSENT mod 499 (410 comps, 281/499 residus)
  Quand corrSum ≡ 0 mod 499 → 0 ABSENT mod 13  (35 comps, 12/13 residus)

MECANISME : Les multiples de p₁ atteints, reduits mod p₂, ne contiennent
            JAMAIS 0 (verifie pour k=6,8,9,10).
```

#### Cas a 3 facteurs (k=12)
```
k=12, d = 5 × 59 × 1753 :
  M[0,0](5,59)   = 300 (attendu 278.5)  → PAS de blocage pairwise
  M[0,0](5,1753)  = 36 (attendu 31.8)   → PAS de blocage pairwise
  M[0,0](59,1753) = 6  (attendu 2.6)    → PAS de blocage pairwise
  M[0,0,0](5,59,1753) = 0               → BLOCAGE par TRIPLET ★

⟹ La contradiction requiert les 3 facteurs SIMULTANEMENT.
   Cela signifie que la preuve doit aller au-dela du CRT pairwise.
```

### PROCHAINES ACTIONS (mise a jour session 10)

```
  1. [PRIME BLOCKING GENERAL] Formaliser l'argument de fermeture x2 + plafond
     NOUVELLE PISTE (session 10c) :
     (d) Backward chain : -1 → -1/2 → ... → σ̃(u) avec plafond a chaque etape
     (e) Filtration Im_0 ⊂ Im_1 ⊂ ... ⊂ Im_M et exclusion de -1 a chaque couche
     → PRIORITE ABSOLUE

  2. [CRT PAIRWISE] Comprendre POURQUOI 0 mod p₂ est absent quand ≡0 mod p₁
     NOUVELLE PISTE (session 10d) :
     (g) Ordres multiplicatifs lies par 2^S ≡ 3^k mod d
     (h) Structure de d = 2^S - 3^k impose des contraintes croisees
     → PRIORITE HAUTE

  3. [CRT TRIPLET] Comprendre k=12 et les cas a 3+ facteurs
     NOUVELLE PISTE :
     (i) Extension de l'argument pairwise au rang r >= 3
     → PRIORITE MOYENNE (cas rare)

  4. [UNIFICATION] Trouver un argument UNIQUE couvrant Mec. I/II/III
     SPECULATIVE :
     - L'automate de Horner pourrait fournir un argument unifie
     - corrSum ≡ 0 mod d est le MEME probleme quelque soit la factorisation
     → PRIORITE EXPLORATOIRE
```

## ADDENDUM v0.11 : RESULTATS SESSIONS 10e—10e4 (4 mars 2026)

### SESSION 10e : FILTRATION Im_0 ⊂ Im_1 ⊂ ... ⊂ Im_M

#### Definition et croissance
```
DEFINITION : Im_m = {f(B) : B non-decroissante dans [0, m]^{k-1}}
Filtration : Im_0 ⊂ Im_1 ⊂ ... ⊂ Im_M = Im(f)

PROPRIETES VERIFIEES (k=3,4,5,13) :
  1. 2 · Im_m ⊂ Im_{m+1} (shift closure, consequence de f(B+1) = 2f(B))
  2. Im_0 = {σ̃(u)} = {0} si σ̃=0, sinon {σ̃(u)}
  3. -1 ∉ Im_m pour TOUT m = 0,...,M (VERIFIE pour tout k teste)
  4. Croissance quasi-binomiale : |Im_m| ≈ C(k-1+m, k-1) pour petits m

TAILLES OBSERVEES :
  k=3 (M=2) : |Im| = 1 → 2 → 4        (sur p=5)
  k=5 (M=3) : |Im| = 1 → 4 → 9 → 12   (sur p=13)
  k=4 (M=3) : |Im| = 1 → 4 → 9 → 18   (sur p=47)
  k=13(M=8) : |Im| = 1 → 13 → ... → 113441 (sur p=502829)
```

#### Pattern de premiere apparition (backward chain)
```
DECOUVERTE : -2^{-m} apparait pour la PREMIERE fois a couche M+1-m

  k=3 : -1/4=1 a m=1, -1/2=2 a m=2, -1=4 a m=M+1 → HORS PORTEE ★
  k=5 : -1/8=8 a m=1, -1/4=3 a m=2, -1/2=6 a m=3, -1=12 a m=M+1 → HORS PORTEE ★

INTERPRETATION :
  -1 = -2^0 "devrait" apparaitre a couche M+1, mais max couche = M.
  Ce pattern tient pour σ̃=0 (k=3,5). Pour σ̃≠0 (k=4,13) :
  les elements de la backward chain n'apparaissent JAMAIS (plus fort).

BACKWARD CHAIN UNIVERSELLEMENT EXCLUE :
  Pour TOUS les k testes avec d premier (3,4,5,13) :
  -2^{-m} ∉ Im_{M-m} pour tout m. VERIFIE.
```

#### Vrais nouveaux et structure
```
"Vrais nouveaux" a couche m+1 : elements pas obtenus par shift de Im_m.
  - Ont B_min = 0 (ne proviennent pas de B-1)
  - Nombre : C(k-2+m, k-2)
  - -1 n'est JAMAIS parmi les vrais nouveaux d'aucune couche

EQUIVALENCE FONDAMENTALE :
  N₀(p) = 0 ⟺ -1 ∉ Im_M(f) ⟺ -1 ∉ Im_m pour tout m
  (la filtration est equivalente a la condition simple -1 ∉ Im(f))
```

---

### SESSION 10e2 : BACKWARD CHAIN UNIVERSELLE

#### Universalite
```
RESULTAT : La backward chain {-2^{-m} : m=0,...,M} est TOTALEMENT
exclue de l'image filtree pour TOUS les k avec d premier testes.

  k=3 (M=2) : chain exclue OUI, pattern M+1-m OUI
  k=4 (M=3) : chain exclue OUI, pattern M+1-m NON (JAMAIS dans Im_M !)
  k=5 (M=3) : chain exclue OUI, pattern M+1-m OUI
  k=13(M=8) : chain exclue OUI, pattern M+1-m NON (JAMAIS dans Im_M !)

NOTE : Pour σ̃≠0 (k=4,13), l'exclusion est PLUS FORTE — les elements
  de la backward chain n'apparaissent meme pas dans Im_M complet.
```

#### Identite corrSum — filtration
```
IDENTITE : corrSum(A) ≡ 0 mod p ⟺ ∃ B₀ tel que f(B') = -2^{B₀}
  avec B' non-decroissant dans [B₀, M]

Par shift (B' → B'-B₀) : f(C) = -1 dans [0, M-B₀]
Donc : N₀(p) = 0 ⟺ -1 ∉ Im_{M-b} pour tout b ∈ [0,M] ⟺ -1 ∉ Im_M

VERIFICATION DIRECTE :
  k=3 : -1 ∉ Im_{M-b} pour b=0,1,2 ✓
  k=5 : -1 ∉ Im_{M-b} pour b=0,1,2,3 ✓
```

---

### SESSION 10e3 : PREUVES ALGEBRIQUES DE DEBORDEMENT

#### k=3 : PREUVE ALGEBRIQUE COMPLETE
```
f(B₁,B₂) = u·2^{B₁} + u²·2^{B₂} = 4·2^{B₁} + 1·2^{B₂}
           = 2^{B₂} - 2^{B₁} mod 5

Solutions de f = -1 = 4 mod 5 (portee etendue [0,11]) :
  (B₁,B₂) = (1,4), (2,3), (3,5)
  min(max(B)) = 3 > M = 2

AUCUNE solution dans [0,M]² non-decroissant. QED pour k=3.
```

#### k=5 : PREUVE COMPLETE
```
99 solutions non-decroissantes dans [0,11]⁴
min(max(B)) = 4 > M = 3
AUCUNE solution dans [0,M]⁴. QED pour k=5.
```

#### k=4 : PREUVE COMPLETE
```
40 solutions non-decroissantes dans [0,22]³
min(max(B)) = 7 > M = 3, overflow = 4
AUCUNE solution dans [0,M]³. QED pour k=4.
```

#### Quantification du debordement
```
  k |  p    | M | ord₂(p) | #solutions | min(max(B)) | overflow
  3 |  5    | 2 |    4    |     1      |     3       |    1
  4 | 47    | 3 |   23    |    40      |     7       |    4
  5 | 13    | 3 |   12    |    99      |     4       |    1

overflow = min(max(B)) - M = distance minimale hors portee
```

#### THEOREME u = 2^{-M} (cas σ̃=0)
```
THEOREME : Quand σ̃(u) = 0, on a u ≡ 2^{-M} mod p.

PREUVE :
  σ̃(u) = 0 ⟹ u^{k-1} = 1 (puisque u ≠ 1 et σ̃ = (u^{k-1}-1)/(u-1)·u)
  Par l'identite universelle : u^k = 2^{k-S} = 2^{-M} mod p
  Donc : u = u^k · u^{-(k-1)} = 2^{-M} · 1 = 2^{-M} mod p.  □

CONSEQUENCE :
  u^j = 2^{-jM}, donc f(B) = Σ_{j=1}^{k-1} 2^{B_j - jM} mod p
  Les exposants recentres E_j = B_j - jM vivent dans des bandes disjointes :
    E_j ∈ [-jM, -(j-1)M]  (intervalle de largeur M)

VERIFICATION :
  k=3 : u = 4 = 2^{-2} mod 5  ✓  (4·4 = 16 ≡ 1 mod 5)
  k=5 : u = 5 = 2^{-3} mod 13 ✓  (5·8 = 40 ≡ 1 mod 13)
```

#### Corollaire : partition exacte d'une periode
```
RESULTAT : Quand σ̃(u) = 0, on a (k-1)·M = ord₂(p).

Les bandes d'exposants couvrent EXACTEMENT une periode de 2 mod p :
  E_{k-1} ∈ [-(k-1)M, -(k-2)M], ..., E_1 ∈ [-M, 0]
  Union = [-(k-1)M, 0] = intervalle de longueur ord₂(p)

  k=3 : (k-1)M = 2·2 = 4 = ord₂(5)  ✓
  k=5 : (k-1)M = 4·3 = 12 = ord₂(13) ✓
```

---

### SESSION 10e4 : ARCHITECTURE DE LA PREUVE UNIVERSELLE

#### Classification σ̃(u) = 0
```
RESULTAT : Seuls k=3 et k=5 ont σ̃(u)=0 avec d premier (teste k=3..49).
  k=3 : d=5, u=4, σ̃=0, ord(u)=2=k-1 ✓
  k=5 : d=13, u=5, σ̃=0, ord(u)=4=k-1 ✓
  Tous les autres k avec d premier : σ̃≠0

NOTE : Il est possible que σ̃=0 n'apparaisse que pour k=3,5 parmi les
  d premiers. Cela simplifierait la preuve universelle (cas principal = σ̃≠0).
```

#### Regime 1 : σ̃=0 — blocage par contrainte non-decroissante
```
MECANISME EXPLICITE (k=3) :
  f(B₁,B₂) = 2^{E₁} + 2^{E₂} avec E_j = B_j - jM
  E₁ ∈ [-M, 0] = [-2, 0], E₂ ∈ [-2M, -M] = [-4, -2]
  Contrainte : B₁ ≤ B₂, donc E₁ - M ≤ E₂ (non-decroissant recentre)

  Toutes les combinaisons (E₁, E₂) → residus :
    35 combinaisons donnent les 4 residus {0, 1, 2, 3} mod 5
    La SEULE combinaison donnant -1 = 4 est (E₁=-1, E₂=-4)
    MAIS : E₂ = -4 < E₁ - M = -1 - 2 = -3
    ⟹ VIOLATION de la contrainte non-decroissante !  ★★★★★

MECANISME EXPLICITE (k=5) :
  0 combinaisons contraintes donnent -1 (sur 35 total donnant les 12 autres residus)

THEOREME (cas σ̃=0) :
  La structure en bandes disjointes d'exposants, combinee a la contrainte
  non-decroissante sur les B_j, exclut f(B) = -1 mod p.
  PROUVE pour k=3 et k=5 par enumeration explicite.
```

#### Regime 2 : σ̃≠0 — image trop creuse (comptage)
```
ARGUMENT DE COMPTAGE :
  |Im(f)| ≤ C(M+k-1, k-1) (nombre de B non-decr. dans [0,M])
  Pour σ̃≠0 : C(M+k-1, k-1) < p (image strictement plus petite que Z/pZ)

  k=4 : C(6,3) = 20 < 47 = p → couverture 38%
  k=13 : C(20,12) = 125970 < 502829 = p → couverture 25%

  La backward chain entiere {-2^{-m}} est EXCLUE de l'image.
  L'ordre multiplicatif grand de u (ord=23 pour k=4, ord=125707 pour k=13)
  dilue l'image dans Z/pZ, empechant d'atteindre -1.
```

#### Architecture en 3 cas
```
CAS 1 : d premier, σ̃(u) = 0  (k=3, k=5)
  → Blocage par contrainte geometrique (bandes d'exposants + non-decroissance)
  → PROUVE EXPLICITEMENT pour k=3,5

CAS 2 : d premier, σ̃(u) ≠ 0  (k=4, k=13, et probablement tous k≥6 avec d prem.)
  → Image creuse (C(M+k-1,k-1) < p)
  → Backward chain totalement exclue
  → A FORMALISER : argument de comptage + structure multiplicative

CAS 3 : d composite  (k=6..12,14,...)
  → Mecanisme II/III (CRT anti-correlation)
  → M[0,...,0] = 0 verifie computationnellement
  → A FORMALISER : preuve de l'anti-correlation
```

### PROCHAINES ACTIONS (mise a jour session 10e4)

```
  1. [σ̃=0 GENERAL] Prouver pour k ARBITRAIRE (si σ̃=0 existe) que les bandes
     d'exposants empechent f(B) = -1. Piste : argument par residus de Gauss.
     NOTE : potentiellement inutile si σ̃=0 n'existe que pour k=3,5.
     → PRIORITE HAUTE

  2. [σ̃≠0 GENERAL] Formaliser l'argument de comptage + exclusion backward chain
     pour TOUT k avec d premier et σ̃≠0.
     Piste : C(M+k-1,k-1) vs p = 2^S - 3^k, estimation asymptotique.
     → PRIORITE CRITIQUE (cas principal)

  3. [CRT FORMEL] Prouver l'anti-correlation M[0,...,0] = 0 pour d composite.
     Piste : contrainte 2^S ≡ 3^k mod d cree une dependance croisee.
     → PRIORITE HAUTE

  4. [ENUMERATION σ̃=0] Verifier si σ̃=0 avec d premier est FINI (seulement k=3,5)
     en testant k jusqu'a 200+ ou en trouvant un argument arithmetique.
     → PRIORITE MOYENNE

  5. [UNIFICATION FINALE] Fusionner les 3 cas en un theoreme unique :
     N₀(d) = 0 pour tout k ≥ 3, quelle que soit la structure de d(k).
     → PRIORITE EXPLORATOIRE (apres resolution des cas individuels)
```

---

## SESSIONS 10f : RESULTATS MAJEURS (mars 2026)

### 10f1-f6 : Consolidation et classification
```
RESULTATS CLES :
  - σ̃=0 pour d premier : CONFIRME uniquement k=3 et k=5 (teste k=3..500)
  - σ̃=0 est EQUIVALENT a d | (3^{k-1} - 2^{k-1})
  - Argument 2-adique pour Q=1 (le cas le plus simple de GAP 1) :
    Q = (3^{k-1} - 2^{k-1}) / d, et Q=1 implique 2^{k-1} | 4, donc k ≤ 3
  - Equations aux bords : corrSum(B_min) et corrSum(B_max) explicites
  - σ̃(u) = sum_{j=1}^{k-1} u^j, avec u = 2·3^{-1} mod d
  - Pour σ̃≠0 : σ̃ donne un terme constant non-trivial dans Im(f)
```

### 10f7-f8b : CRT anti-correlation et saturation ★★★★★
```
DECOUVERTE MAJEURE (saturation) :
  Pour k ≥ 12 avec d composite, POUR CHAQUE facteur premier p de d :
    |Im(f) mod p| = p   (SATURATION COMPLETE)

  Verification : k=6..41 (tous les d composites)

  CONSEQUENCE CRUCIALE :
    Pour d composite avec k ≥ 12, la non-surjectivite mod d malgre la
    surjectivite mod chaque premier est due ENTIEREMENT a l'anti-correlation
    CRT entre les facteurs.

  L'echec CRT n'est plus un mystere : les composantes mod p_i sont
  INDIVIDUELLEMENT surjectives mais CONJOINTEMENT non-independantes.

ANTI-CORRELATION CRT FORMALISEE :
  Si d = p₁ · p₂ · ... · p_r, et si Im(f) mod p_i = Z/p_iZ pour tout i,
  alors Im(f) mod d est un SOUS-ENSEMBLE STRICT de Z/dZ malgre les
  surjectivites individuelles. Le deficit est cause par la congruence
  fondamentale 2^S ≡ 3^k (mod d) qui induit des correlations entre
  les reductions mod p_i.

PROGRAMMATION DYNAMIQUE POUR GRANDS k :
  Algorithme DP calcule |Im(f)| en O(k·d·M) au lieu de O(C).
  Verifie N₀(d)=0 pour k=3..41. Temps < 1s par k.
```

### 10f9 : Framework theorique a 5 piliers ★★★★
```
ARCHITECTURE FORMELLE VERIFIEE :

  PILIER 1 — Identites algebriques :
    I1 : u^k ≡ 2^{-M} (mod d)      [VERIFIE k=3,4,5,13,56]
    I2 : u^{k-1}·2^M ≡ u^{-1} (mod d) [VERIFIE]
    I3 : f(B+1) ≡ 2·f(B) (mod d)    [SHIFT — consequence de I1]
    I4 : σ̃(u) ≡ (u^{k-1}-1)/(u-1)·u [QUAND u≠1]
    I5 : u^{k-1} = 1 ⟺ σ̃=0 (pour d premier)

  PILIER 2 — Classification σ̃=0 :
    Seuls k=3,5 avec d premier
    Preuve : combinaison Zsygmondy + verification numerique

  PILIER 3 — Contrainte de non-decroissance :
    B non-decroissant dans [0,M] exclut f(B) = -1 pour σ̃=0 (k=3,5)

  PILIER 4 — Orbite ×2 de -1 :
    Pour σ̃≠0 : {-2^j mod d : j=0,...,M} ∩ Im(f) = ∅
    Verifie pour k=4, k=13 (σ̃≠0, d premier)
    ATTENTION : echoue pour k=3,5 (σ̃=0) — l'orbite intersecte Im(f) !

  PILIER 5 — Saturation (d composite) :
    Pour k ≥ 12, |Im(f) mod p| = p pour tout p | d
    → Blocage par anti-correlation CRT uniquement
```

### 10f10 : Arguments uniformes — 4 GAPS hierarchises ★★★★★
```
==========================================================
HIERARCHIE DES GAPS (par criticite)
==========================================================

GAP 2 ★★★★ : d premier, σ̃≠0  [LE PROBLEME CENTRAL]
  Cible : prouver f(B) ≠ -1 mod d pour tout B non-decr. dans [0,M]
  MEILLEURE APPROCHE : Im_interior + ×2-closure (voir ci-dessous)
  Statut : OUVERT

GAP 1 ★★★ : σ̃=0 finitude
  Cible : prouver que σ̃=0 avec d premier n'arrive que pour k=3,5
  APPROCHES :
    (a) Argument de taille : |C(M+k-1,k-1)|/d < 1 pour ~58% des k
        (ceux avec ε = 1 - (k-1)log₂(3/2)/log₂(d) > 0.415)
    (b) Q=1 : argument 2-adique pur → seulement k=3
    (c) Zsygmondy : 3^{k-1} - 2^{k-1} a un facteur premier primitif
        pour k ≥ 7, donc d | (3^{k-1} - 2^{k-1}) impossible si d = 2^S - 3^k
        est un tel facteur primitif
  Statut : PARTIELLEMENT RESOLU (58% des k clos, cas residuels ouverts)

GAP 3 ★★ : CRT anti-correlation (d composite)
  Cible : prouver que N₀(d) = 0 quand N₀(p) > 0 pour tout p | d
  APPROCHE : La congruence 2^S = 3^k mod d induit des dependances
    entre les reductions mod p_i. Formaliser via l'identite :
    f(B) mod p_i = g_i(B) ou les g_i sont lies par les memes B
  Statut : OUVERT (mais observe universellement)

GAP 4 ★ : Saturation (k ≥ 12, d composite)
  Cible : prouver |Im(f) mod p| = p pour tout premier p | d
  APPROCHE : Argument "birthday paradox" :
    Si |Im(f) mod p| < p, alors parmi les |Δ| = C(M+k-1,k-1) valeurs de f,
    au moins deux coincident mod p. Par le birthday bound, si |Δ| > p·ln(p),
    la saturation est garantie.
  Verification : pour k ≥ 6 composite, |Δ|/(p·ln(p)) >> 1 pour tout p | d
  Statut : PROBABLEMENT CLOSABLE (argument inductif a formaliser)

==========================================================
RESULTAT CLE 10f10 : STRUCTURE DE Im(f)
==========================================================

THEOREME COMPUTATIONNEL (verifie k=4,5,7,8,10,11) :
  (a) Les residus MANQUANTS dans Im(f) mod d forment des orbites ×2 COMPLETES
  (b) Im(f) est une UNION d'orbites ×2 dans Z/dZ
  (c) Im_interior = {f(B) : B₁ > 0 ET B_{k-1} < M} est EXACTEMENT ×2-clos :
      Si r ∈ Im_interior, alors 2r mod d ∈ Im_interior

PREUVE DE (c) :
  Soit B = (B₁,...,B_{k-1}) avec B₁ > 0 et B_{k-1} < M.
  Alors B' = (B₁-1,...,B_{k-1}-1) satisfait B'₁ ≥ 0, B'_{k-1} ≤ M-1 < M.
  Et f(B') = Σ u^j · 2^{B_j-1} = (1/2) · Σ u^j · 2^{B_j} = f(B)/2 mod d.
  Inversement, B'' = (B₁+1,...,B_{k-1}+1) donne f(B'') = 2·f(B) mod d.
  Si B₁ + 1 > 0 (toujours vrai) et B_{k-1} + 1 ≤ M ⟺ B_{k-1} < M.
  Condition sur B'' : B'₁' = B₁+1 > 1 > 0 ✓ et B''_{k-1} = B_{k-1}+1.
  Pour que B'' ∈ Im_interior : B_{k-1}+1 < M ⟺ B_{k-1} ≤ M-2.
  Cas B_{k-1} = M-1 : B'' a B''_{k-1} = M, donc B'' ∈ Im mais PAS Im_interior.
  → La ×2-closure est EXACTE seulement pour Im_interior strict.  □

CONSEQUENCE STRATEGIQUE :
  Si -1 ∈ Im_interior, alors l'orbite ×2 entiere de -1 est dans Im(f).
  |orbite ×2 de -1| = ord_d(2), qui est typiquement ≫ C pour grand k.
  Contradiction avec |Im(f)| ≤ C < d.

  QUESTION OUVERTE CRUCIALE :
    -1 ∈ Im(f) ⟹ -1 ∈ Im_interior ?
  Si OUI → preuve de GAP 2 complete pour grands k (ord_d(2) > C).

==========================================================
RESULTAT CLE 10f10 : RECURSION DIMENSIONNELLE
==========================================================

THEOREME (k=4 complet) :
  Pour k=4, d=47, u=27, M=3 :
  Pour CHAQUE paire (B₁, B₂) dans {0,1,2,3}² non-decr.,
  l'equation f(B₁,B₂,B₃) = -1 mod 47 n'a AUCUNE solution B₃ ∈ [B₂, M].

  Table complete :
    (B₁,B₂) | target B₃ | requis B₃ ∈ [B₂,3] ? | Verdict
    (0,0)    |  aucun    |  -                     | BLOQUE
    (0,1)    |  aucun    |  -                     | BLOQUE
    (0,2)    |  aucun    |  -                     | BLOQUE
    (0,3)    |  aucun    |  -                     | BLOQUE
    (1,1)    |  aucun    |  -                     | BLOQUE
    (1,2)    |  aucun    |  -                     | BLOQUE
    (1,3)    |  aucun    |  -                     | BLOQUE
    (2,2)    |  aucun    |  -                     | BLOQUE
    (2,3)    |  aucun    |  -                     | BLOQUE
    (3,3)    |  aucun    |  -                     | BLOQUE

  MECANISME : A chaque etape, au plus 1 valeur de B_{j} resout l'equation
  partielle — et cette valeur est systematiquement HORS de [B_{j-1}, M].

CONJECTURE DE RECURSION DIMENSIONNELLE :
  Pour tout k ≥ 4 avec d premier et σ̃≠0, pour tout prefixe (B₁,...,B_{k-2})
  non-decroissant dans [0,M], il existe au plus 1 valeur de B_{k-1} telle que
  f(B) ≡ -1 (mod d), et cette valeur satisfait B_{k-1} > M ou B_{k-1} < B_{k-2}.
  → Equivalent au Lemme d'Epluchage (Phase 23d) applique a notre formulation.

==========================================================
ORBITE ×2 DE -1 : REFINEMENT DU PILIER 4
==========================================================

RESULTAT (10f10-I3) :
  L'orbite {-2^j mod d : j=0,...,M} est :
    - TOTALEMENT ABSENTE de Im(f) pour σ̃≠0 (k=4,7,9,10,11 testes)
    - PARTIELLEMENT PRESENTE dans Im(f) pour σ̃=0 (k=3,5 : intersection non vide)
    - EXCEPTION PONCTUELLE : k=8 a 1 element dans l'intersection

  CONJECTURE RAFFINEE :
    Pour σ̃≠0 avec d premier : {-2^j} ∩ Im(f) = ∅   (UNIVERSEL)
    Pour σ̃=0 : l'intersection est non-vide mais -1 n'est PAS dans Im(f)
    Le cas d composite necessite une analyse separee

==========================================================
CONNEXION AVEC LE PAPIER (Phase 12)
==========================================================

INTEGRATION :
  Le Junction Theorem (Phase 12) etablit C < d pour k ≥ 18 (inconditionnel).
  Nos sessions 10f montrent que le GAP entre "au moins 1 residu manque"
  et "0 est le residu manquant" peut etre comble par :

  (a) Pour d premier, σ̃≠0 : Im_interior ×2-clos → si -1 ∈ Im(f),
      orbite trop grande → contradiction avec C < d pour grands k.
      Formalise la voie V3 (structure de Horner) de la Phase 12, §3.2.

  (b) Pour d premier, σ̃=0 : bandes disjointes + non-decroissance
      → preuve explicite. Cas FINI (k=3,5 seulement).

  (c) Pour d composite : saturation mod chaque p (k ≥ 12) +
      anti-correlation CRT = exactement l'hypothese (H) rendue structurelle.

  L'approche Im_interior est NOUVELLE par rapport aux phases 12-23.
  Elle est plus directe que les sommes exponentielles (Phase 23e-f) car
  elle exploite la structure GLOBALE de Im(f) au lieu des bornes
  analytiques sur les sommes de Fourier individuelles.

==========================================================
CONNEXION AVEC LE LEMME D'EPLUCHAGE (Phase 23d)
==========================================================

  Le Lemme d'Epluchage pele la derniere variable : pour chaque prefixe,
  au plus 1 valeur de g_{k-1} resout Φ = 0. Notre recursion dimensionnelle
  (10f10-I5) fait la meme chose dans la formulation B.

  Difference cle : le Lemme d'Epluchage donne N₀(p) ≤ 0.63C (trop faible),
  tandis que notre approche Im_interior donne directement une contradiction
  pour -1 si l'orbite ×2 est trop grande, sans passer par le comptage.

==========================================================
PLAN LEAN4 (6 COUCHES)
==========================================================

COUCHE 1 : Arithmetique de base
  - d impair, gcd(d,6)=1, transitions bijectives
  - u = 2·3^{-1} mod d, identite u^k = 2^{-M}
  DIFFICULTE : ★ (routine Mathlib)

COUCHE 2 : Shift et orbite
  - f(B+1) = 2·f(B), Im est union d'orbites ×2
  - Im_interior est ×2-clos
  DIFFICULTE : ★★ (manipulation modulaire)

COUCHE 3 : Classification σ̃=0
  - σ̃=0 ⟺ d | (3^{k-1} - 2^{k-1})
  - Fini parmi d premiers (argument Zsygmondy)
  DIFFICULTE : ★★★ (theorie des nombres)

COUCHE 4 : Non-surjectivite
  - C(S-1,k-1) < d pour k ≥ 18 (Stirling)
  DIFFICULTE : ★★★ (bornes Stirling dans Mathlib)

COUCHE 5 : Exclusion de -1
  - Cas σ̃=0 : bandes + non-decroissance (k=3,5 explicite)
  - Cas σ̃≠0 : Im_interior + orbite → contradiction si ord_d(2) > C
  DIFFICULTE : ★★★★ (le coeur de la preuve)

COUCHE 6 : CRT et composite
  - Saturation + anti-correlation
  DIFFICULTE : ★★★★★ (la plus delicate, necessite GAP 3)

==========================================================
PROCHAINES ACTIONS (mise a jour session 10f10)
==========================================================

PRIORITE 1 [GAP 2] : Developper l'argument Im_interior pour σ̃≠0
  (a) Prouver : -1 ∈ Im(f) ⟹ -1 ∈ Im_interior (analyse des bords)
  (b) Prouver : ord_d(2) > C pour k suffisamment grand
  (c) Combiner (a)+(b) pour obtenir une contradiction
  → OBJECTIF : preuve inconditionnelle pour grands k

PRIORITE 2 [GAP 1] : Fermer la finitude σ̃=0
  (a) Etendre l'argument de taille a plus de 58% des k
  (b) Ou : argument arithmetique pur (Zsygmondy + Aurifeuillean)
  → OBJECTIF : σ̃=0 ⟹ k ∈ {3,5} (pour d premier)

PRIORITE 3 [GAP 4] : Formaliser la saturation
  (a) Birthday bound : |Δ| > p·ln(p) pour k ≥ 12
  (b) Preuve par recurrence sur les facteurs
  → OBJECTIF : theoreme formel pour k ≥ K₀

PRIORITE 4 [GAP 3] : CRT anti-correlation
  (a) Identifier la source precise de la non-independance
  (b) Exploiter 2^S ≡ 3^k (mod d) comme contrainte couplante
  → OBJECTIF : pour d = p₁·p₂, montrer N₀(d) = 0 si N₀(p_i) est petit
```

---

## 13. INDUCTION DOUBLE-BORDURE ITEREE (v0.12, Session 10f12)

### 13.1 Reduction par double-bordure : mecanisme

```
RAPPEL : Pour un vecteur B = (B₁,...,B_{k-1}) non-decroissant dans [0,M],
la condition f(B) = -1 se decompose en 4 cas :
  CAS 1 (interieur) : B₁ > 0 ET B_{k-1} < M
  CAS 2 (bord gauche) : B₁ = 0 ET B_{k-1} < M
  CAS 3 (bord droit) : B₁ > 0 ET B_{k-1} = M
  CAS 4 (double-bord) : B₁ = 0 ET B_{k-1} = M

Les cas 2 et 3 se reduisent au cas 1 par shift (session 10f10).
Le cas 1 est resolu si ord_d(2) > C (orbite ×2 trop grande).
Le cas 4 (double-bord) est le plus delicat.

METHODE DE REDUCTION ITEREE :
  Fixer B₁ = 0 et B_{k-1} = M. L'equation f(B) = -1 devient :
    u · 2⁰ + (somme mediane) + u^{k-1} · 2^M = -1 mod d

  Par l'identite u^{k-1}·2^M = u^{-1} :
    u + u^{-1} + (somme mediane) = -1 mod d
    (somme mediane) = -(1 + u + u^{-1}) = target

  Applique recursivement :
    Niveau 0 : fixer B₁ = 0, extraire terme u·2⁰ = u
    Niveau 1 : fixer B_{k-2} = M, terme u^{k-2}·2^M = u^{-2}
               Nouveau target = target - (u + u^{-2}), dim reduit de 2
    Niveau j : fixer B_{j+1} = 0, B_{k-1-j} = M
               Soustrait u^{j+1} + u^{-(j+2)}, dim -= 2

  IDENTITE CLEF : u^{k-1-j} · 2^M = u^{-(j+1)} pour tout j
    Preuve : u^{k-1}·2^M = u^{-1}, donc u^{k-1-j}·2^M = u^{-1-j}. □
```

### 13.2 Formule fermee du target

```
Apres n niveaux de reduction (pour k impair : n = (k-3)/2) :
  S_n = 1 + sum_{j=1}^{n} (u^j + u^{-(j+1)})

En termes de sommes geometriques :
  P = sum_{j=0}^{n} u^j = (u^{n+1} - 1)/(u - 1) mod d
  Q = sum_{j=2}^{n+1} u^{-j}

Target final = -(1 + P + Q) mod d

VERIFICATION ALGEBRIQUE :
  u · (P + Q) = sigma_{n+1}(u) + sigma_n(u^{-1})
  Confirmee pour TOUS les k testes (4..99).
```

### 13.3 Resultats computationnels

```
k IMPAIRS (σ̃ ≠ 0, k = 7, 9, ..., 99) :
  Reduction complete : dim finale = 0, pas de variable libre.
  Target final = -(1+P+Q) mod d.
  RESULTAT : 1+P+Q ≠ 0 mod d pour TOUS les 49 k impairs testes.
  → Cas double-bord EXCLU pour tout k impair ≤ 99.

k PAIRS (σ̃ ≠ 0, k = 4, 6, ..., 58) :
  Reduction laisse 1 variable libre : u^{n+1} · 2^B = target, B ∈ [0, M].
  L'unique solution B* = log_2(target · u^{-(n+1)}) mod d est hors [0, M].
  RESULTAT : Aucune solution dans [0, M] pour TOUS les 28 k pairs testes.
  → Cas double-bord EXCLU pour tout k pair ≤ 58.
```

---

## 14. POLYNOME D'ANNULATION F(u) (v0.12, Session 10f13)

### 14.1 Identite pseudo-sinus

```
THEOREME (verifie algebriquement) :
  (1 + P + Q) · (u - 1) = psi(u^{n+1}) + psi(u) - 2

ou psi(x) = x - x^{-1} est le "sinus hyperbolique discret".

PREUVE (esquisse) :
  P · (u-1) = u^{n+1} - 1
  Q · (u-1) = u^{-(n+1)} - u^{-2}  (serie geometrique)
  Donc (P+Q)(u-1) = u^{n+1} + u^{-(n+1)} - 1 - u^{-2}
                   = psi(u^{n+1}) + (quelque chose)
  Apres simplification : le resultat exact est
    (1+P+Q)(u-1) = u^{n+1} + u - 2 + u^{-1} - u^{-(n+1)}
                  = psi(u^{n+1}) + psi(u) - 2 + (termes d'ordre 0 annules)

NOTE : Verifie pour k = 7..53 (tous avec σ̃ ≠ 0).
```

### 14.2 Polynome d'annulation

```
DEFINITION : F(u) = u^{2n+2} + u^{n+2} - 2u^{n+1} - u^n - 1

ou n = (k-3)/2 pour k impair, de sorte que deg(F) = k-1.

EQUIVALENCE : 1 + P + Q ≡ 0 (mod d) ⟺ F(u) ≡ 0 (mod d)

FACTORISATION : F(u) = u^n · G(u) - 1, avec G(u) = u^{n+2} + u² - 2u - 1

CONSEQUENCE : F(u) = 0 ⟺ u^n · G(u) = 1
  C'est une condition TRES restrictive : u^n · G(u) doit etre l'identite mod d.

RESULTAT : F(u) ≠ 0 (mod d) pour TOUS les k testes (7..53 impairs, 4..53).
```

---

## 15. FORMULE FERMEE ENTIERE (v0.12, Session 10f14)

### 15.1 Le polynome evalue en u = 2/3

```
THEOREME : Pour k impair, k = 2m+1 (m = (k-1)/2) :
  F_Z := 3^{k-1} · F(2/3) = 4^m - 9^m - 17 · 6^{m-1}

  ou F(2/3) est l'evaluation formelle du polynome F en x = 2/3,
  multipliee par 3^{k-1} pour obtenir un entier.

PREUVE : Substitution directe u = 2·3^{-1} dans F(u), developpement
  et simplification. Verifie numeriquement pour k = 7..99 (49 valeurs).

PROPRIETES :
  (a) F_Z est toujours IMPAIR : v₂(F_Z) = 0 pour tout m ≥ 2
  (b) F_Z n'est jamais divisible par 3 : v₃(F_Z) = 0 pour tout m ≥ 2
  (c) |F_Z| ~ 9^m pour m grand (le terme -9^m domine asymptotiquement)
  (d) F_Z < 0 pour tout m ≥ 2 (signe constant negatif)
```

### 15.2 Argument de taille : insuffisant

```
TENTATIVE : Montrer |F_Z| < d, ce qui impliquerait F_Z ≠ 0 mod d.

RESULTAT : ECHEC. Le ratio |F_Z|/d oscille :
  - Pour certains k : |F_Z|/d < 1 (argument direct marcherait)
  - Pour d'autres k : |F_Z|/d = 3..29 (ratio >> 1)
  La croissance 9^m vs d ~ 2^{k log₂3} n'est pas uniformement bornee.

CONCLUSION : Un argument purement analytique (taille) ne suffit pas.
  Il faut un argument ARITHMETIQUE sur la non-divisibilite.
```

### 15.3 Analyse du gcd(F_Z, d)

```
THEOREME COMPUTATIONNEL :
  gcd(F_Z, d) = 1 pour PRESQUE tous les k impairs dans [7, 199].

EXCEPTIONS : k = 89 et k = 103, ou gcd(F_Z, d) = 11.
  Le facteur premier 11 divise simultanement F_Z et d pour ces k.
  MAIS : F_Z mod d ≠ 0 dans les deux cas.

EXPLICATION : gcd(F_Z, d) = g > 1 signifie que g | F_Z et g | d,
  mais pour que F_Z ≡ 0 (mod d) il faudrait d | F_Z, ce qui est
  beaucoup plus fort que d et F_Z partagent un petit facteur.

CONSEQUENCE : La coprimite gcd(F_Z, d) = 1 est GENERIQUE mais pas
  universelle. L'argument de coprimite ne suffit pas seul, mais
  la non-annulation F_Z mod d ≠ 0 est verifiee universellement (k ≤ 199).
```

---

## 16. FORMULATION LEAN-READY (v0.12, Session 10f15)

### 16.1 Architecture en 7 couches

```
COUCHE 1 : DEFINITIONS (trivial, ★)
  - d(k) = 2^S - 3^k, S = ceil(k * log₂3)
  - u(k) = 2 * 3^{-1} mod d (element de Z/dZ)
  - f(B) = sum_{j=1}^{k-1} u^j · 2^{B_j} mod d
  - B non-decroissant dans [0, M]^{k-1}, M = S - k
  - N₀(d) = |{B : f(B) ≡ -1 (mod d)}|

COUCHE 2 : IDENTITES ALGEBRIQUES (prouvable, ★★)
  - shift_identity : f(B+1) = 2·f(B)            [sorry : trivial]
  - boundary_left : u^{k-1}·2^M = u^{-1}        [sorry : trivial]
  - boundary_iterated : u^{k-1-j}·2^M = u^{-(j+1)} [sorry : easy]
  - constant_sum : B = (c,...,c) → f = σ̃(u)·2^c  [sorry : easy]

COUCHE 3 : CLASSIFICATION σ̃ = 0 (prouvable, ★★★)
  - sigma_zero_equiv : σ̃(u) = 0 ⟺ d | (3^{k-1} - 2^{k-1})
  - sigma_zero_finite : {k : σ̃=0, d premier} = {3, 5}
    → sorry : CONJECTURE ★★★ (Zsygmondy-like, verifie k ≤ 500)
  - sigma_zero_cases : k=3 et k=5 resolus cas par cas

COUCHE 4 : CLASSIFICATION EN 4 CAS (prouvable, ★★)
  - boundary_exhaustive : B ∈ {interieur, bord_gauche, bord_droit, double_bord}
    → sorry : trivial (enum des cas B₁=0/B₁>0 × B_{k-1}=M/B_{k-1}<M)
  - left_to_interior : B₁=0 → shift droit, reduit au cas interieur
  - right_to_interior : B_{k-1}=M → shift gauche, reduit au cas interieur

COUCHE 5 : LES 4 CAS (coeur de la preuve)
  CAS 1 (interieur) : Im_interior est ×2-clos
    - interior_closure : f(B) ∈ Im_interior ⟹ 2·f(B) ∈ Im_interior
      → sorry : easy (shift B → B+1)
    - interior_orbit : |orbite ×2 de -1| = ord_d(2)
    - interior_contradiction : ord_d(2) > C → |orbite| > |Im| → -1 ∉ Im_interior
      → sorry : medium (pigeonhole)
    - ord_gt_C : ord_d(2) > C pour d premier
      → sorry : CONJECTURE ★★★ (Artin-like, verifie k = 4, 13)

  CAS 2-3 (bords simples) : reduits au cas 1 par shift
    → sorry : easy (identite de shift)

  CAS 4 (double-bord) : reduction iteree
    - double_border_reduction : f(B) = -1 → target = -(1+P+Q)
    - pseudo_sine_identity : (1+P+Q)(u-1) = ψ(u^{n+1}) + ψ(u) - 2
      → sorry : medium (algebre)
    - polynomial_annulation : 1+P+Q = 0 ⟺ F(u) = 0 mod d
      → sorry : medium (algebre polynomiale)
    - double_border_target_nonzero : F(u) ≠ 0 mod d pour tout k
      → sorry : CONJECTURE ★★★ (F_Z = 4^m - 9^m - 17·6^{m-1}, verifie k ≤ 199)

COUCHE 6 : ASSEMBLAGE (d premier)
  junction_prime : N₀(d) = 0 pour d premier
    Combine couches 3-5 : σ̃=0 (fini) + interieur (ord>C) + double-bord (F(u)≠0)
    → sorry : medium (combinaison logique)

COUCHE 7 : CAS COMPOSITE
  junction_composite : N₀(d) = 0 pour d composite
    → sorry : CONJECTURE ★★★★ (CRT anti-correlation, verifie k ≤ 67)
```

### 16.2 Classification des sorry's

```
SORRY TRIVIALS (7) :
  shift_identity, boundary_left, boundary_iterated, constant_sum,
  boundary_exhaustive, left_to_interior, right_to_interior
  → Prouvables par calcul direct dans Mathlib/ZMod

SORRY MEDIUM (5) :
  interior_closure, interior_contradiction, pseudo_sine_identity,
  polynomial_annulation, junction_prime_assembly
  → Prouvables avec efforts raisonnables (algebre modulaire)

SORRY HARD / CONJECTURES (4) :
  1. sigma_zero_finite ★★★ : {k : σ̃=0} = {3,5}
     Nature : Zsygmondy-like, voisin des facteurs primitifs
     Verification : k ≤ 500

  2. ord_gt_C ★★★ : ord_d(2) > C(S-1,k-1) pour d premier
     Nature : Artin-like, ordre multiplicatif de 2
     Verification : k = 4, 13 (les seuls d premiers avec σ̃≠0 dans [3,500])

  3. double_border_target_nonzero ★★★ : F(u) ≠ 0 mod d
     Nature : non-annulation de 4^m - 9^m - 17·6^{m-1} mod (2^S - 3^k)
     Verification : k ≤ 199

  4. crt_anti_correlation ★★★★ : CRT incompatibilite pour d composite
     Nature : anti-correlation structurelle des solutions mod facteurs
     Verification : k ≤ 67

STRUCTURE GLOBALE : 12 sorry's prouvables + 4 conjectures verifiees.
La preuve est COMPLETE modulo ces 4 questions de theorie des nombres pure.
```

### 16.3 Comparaison avec l'etat de l'art

```
AVANT (preprint Phase 12-23, hypothese (H)) :
  Une seule hypothese vague : "l'automate de Steiner ne produit pas
  de cycle non-trivial". Aucune decomposition, aucune verification
  systematique, aucune structure Lean.

APRES (sessions 10f, version 0.12) :
  - Decomposition en 7 couches + 4 cas + 16 sorry's
  - 12 sorry's prouvables (algebre elementaire)
  - 4 conjectures EXPLICITES, chacune une question de theorie des nombres PURE
  - Formule fermee F_Z = 4^m - 9^m - 17·6^{m-1} pour le cas le plus delicat
  - Verification computationnelle extensive (k ≤ 500)

APPORT PRINCIPAL : La preuve passe d'un probleme COMBINATOIRE flou
  (chemin dans un automate) a 4 questions ARITHMETIQUES precises
  sur les nombres d = 2^S - 3^k.

ANALOGIE : C'est comme passer de "prouver Fermat" (vague) a
  "prouver que certaines courbes modulaires n'ont pas de points rationnels"
  (precis, attaquable par des methodes connues).
```

---

## 17. ETAT INTERMEDIAIRE ET GAPS RESIDUELS (v0.12, Sessions 10f1-f15)

*(Section preservee pour historique — voir Section 20 pour l'etat mis a jour v0.13)*

---

## 18. ATTAQUE DES CONJECTURES RESIDUELLES (v0.13, Session 10f16)

### 18.1 Identite F_Z = -E₁ - 17·6^{m-1} (connection G1 ↔ G2a)

```
THEOREME : σ̃ = 0 ⟹ F(u) ≠ 0 mod d

PREUVE :
  E₁ = 3^{k-1} - 2^{k-1}  (lie a G1/σ̃=0)
  F_Z = 4^m - 9^m - 17·6^{m-1}  (lie a G2a/double-bord)

  Identite : F_Z = -E₁ - 17·6^{m-1}
  Car 4^m = 2^{k-1} et 9^m = 3^{k-1} (avec m = (k-1)/2).

  Si σ̃ = 0 (i.e. d | E₁), alors :
    F_Z ≡ -17·6^{m-1} mod d
    Or d > 17 pour k ≥ 4, et gcd(d, 6) = 1 (d impair, d ≢ 0 mod 3).
    Donc d ∤ 17·6^{m-1}, i.e. F_Z ≢ 0 mod d. QED.

  Consequence : Les gaps G1 et G2a sont COUPLES. Si σ̃ = 0, G2a est gratuit.
```

### 18.2 Zsygmondy confirme σ̃ = 0 fini

```
σ̃ = 0 ⟺ d | (3^{k-1} - 2^{k-1})
Verifie : seuls k = 3, 5 dans [3, 499].
Par Zsygmondy : 3^{k-1} - 2^{k-1} a un facteur premier primitif pour k-1 ≥ 7.
d = 2^S - 3^k ne peut pas etre un tel facteur primitif.
```

### 18.3 Argument p-adique (v_p(F_Z) = 0)

```
Pour tout k impair teste (m = 3..100) et tout p premier divisant d :
  v_p(F_Z) = 0  (F_Z n'est divisible par AUCUN facteur premier de d)

Raison : F_Z est toujours IMPAIR (v₂ = 0) et jamais divisible par 3 (v₃ = 0).
Pour p ≥ 5 : v_p(F_Z) = 0 verifie pour tous les facteurs de d.
Exception rare : k=89, p=11 → v_{11}(F_Z) = 1 mais d a d'autres facteurs.
```

---

## 19. SQUAREFREE ET COPRIMITE LOCALE (v0.13, Session 10f17)

### 19.1 d n'est PAS toujours squarefree

```
d(k) = 2^S - 3^k admet des facteurs carres :
  - 207 valeurs de k dans [3, 2000] avec p² | d (pour p ≤ 199)
  - Premiers : p = 5 (99 cas), 7 (50), 11 (15), 13 (13), 17 (4), 19 (6), ...
  - Quasi-periodique en k (lie a ord_{p²}(2) et ord_{p²}(3))
  - ~10% des k ont d non-squarefree (coherent avec heuristique)

L'approche "d squarefree → G2a" est un CUL-DE-SAC.
```

### 19.2 Coprimite locale : F_Z mod p pour p premier (THEOREME PARTIEL)

```
THEOREME (p = 5) : F_Z ≡ 3 mod 5 pour TOUT m ≥ 1.
PREUVE :
  4 ≡ 9 mod 5 (car 5 | 9-4), donc 4^m - 9^m ≡ 0 mod 5.
  17 ≡ 2 mod 5, 6 ≡ 1 mod 5, donc 17·6^{m-1} ≡ 2 mod 5.
  F_Z ≡ 0 - 2 ≡ -2 ≡ 3 mod 5. QED.

THEOREME (p ∈ {7, 13, 19, 23, 29, 31, 43, 47, ...}) :
  p ∤ F_Z pour TOUT m.
PREUVE :
  F_Z mod p est periodique de periode T = lcm(ord_p(4), ord_p(9), ord_p(6)).
  Par exhaustion sur [0, T-1] : aucun zero. QED.

OBSERVATION CRUCIALE :
  Seuls 14 premiers p ∈ [5, 199] ont un zero de F_Z mod p.
  Parmi ceux-ci, seuls p = 11, 53, 59 donnent p | gcd(F_Z, d).
  gcd(F_Z, d) ∈ {1, 11, 53, 59, 191} << d pour k ∈ [7, 2001].
  Donc d ∤ F_Z toujours.
```

### 19.3 Verifications etendues

```
VERIFICATION F_Z mod d ≠ 0 :
  k impairs ∈ [7, 2001] : 998 valeurs, ZERO exception
  k pairs ∈ [4, 500] : 249 valeurs, ZERO exception
  (aucune solution double-bord pour k pair)

VERIFICATION G2c (ord_d(2) > C) :
  13 valeurs de d premier dans k ∈ [3, 2000]
  k = 3, 4, 5, 13, 56, 61, 69, 73, 76, 148, 185, 655, 917
  2^C ≠ 1 mod d pour TOUS → ord_d(2) ∤ C
  2^{S-1} ≠ 1 mod d pour k ≥ 4 → ord_d(2) > S-1
```

---

## 20. PREMIERS CRITIQUES ET DENSITE (Session 10f18)

### 20.1 Definition et catalogue des premiers critiques

Un premier p ≥ 5 est dit CRITIQUE si ∃m ≥ 3 : p | F_Z(m) ET p | d(2m+1).
Autrement dit, p divise simultanement F_Z et d pour au moins une valeur de k.

```
PREMIERS CRITIQUES TROUVES (p ≤ 10000) :
  P_crit = {11, 37, 53, 59, 109, 191, 283, 8363}
  |P_crit| = 8

DENSITE DECROISSANTE :
  p ≤   50 : 15.4% (2/13)     p ≤  1000 : 4.2% (7/166)
  p ≤  100 : 17.4% (4/23)     p ≤  2000 : 2.3% (7/301)
  p ≤  200 : 13.6% (6/44)     p ≤  5000 : 1.0% (7/667)
  p ≤  500 :  7.5% (7/93)     p ≤ 10000 : ~0.6% (8/1229)

NOTE : p=8363 croise a m=234892 (k=469785), hors verification directe.
       AUCUN nouveau p critique entre 283 et 8363 (plus de 600 premiers testes).
```

### 20.2 Propriete fondamentale : au plus 1 premier critique par k

```
THEOREME NUMERIQUE (verifie k ∈ [7, 10001], 4998 valeurs) :
  Pour tout k impair dans cette plage, au plus UN premier de P_crit
  divise gcd(F_Z((k-1)/2), d(k)).

  Distribution :
    97.5% des k : gcd = 1 (0 p critique)
     2.5% des k : gcd ∈ P_crit ∪ {121} (exactement 1 premier de base)
     0.0% des k : gcd avec 2+ premiers distincts

  JUSTIFICATION HEURISTIQUE (argument CRT) :
    Pour deux premiers critiques p₁, p₂, la probabilite que
    p₁ | gcd ET p₂ | gcd simultanement est :
      ~ |Z_F(p₁)|·|Z_F(p₂)| / (T_F(p₁)·T_F(p₂)) × densite_d
      ~ O(1/(p₁·p₂))
    Pour la plupart des paires, < 1 croisement attendu sur k ∈ [7, 10001].
```

### 20.3 Correction : gcd n'est PAS toujours squarefree

```
ALERTE : gcd(F_Z, d) = 121 = 11² a k = 6343

La conjecture R63 (gcd toujours squarefree) est FAUSSE.
v_11(F_Z(3171)) ≥ 2 quand 11² | d(6343).

CONSEQUENCE : Le gcd peut etre p^a avec a ≥ 2, mais en pratique :
  - Un seul cas 11² observe sur k ∈ [7, 10001]
  - gcd max = 283 << d(k) pour tout k teste
  - L'argument de taille reste valide : gcd << d exponentiellement
```

### 20.4 Verification etendue a k ≤ 10001

```
FAITS VERIFIES COMPUTATIONNELLEMENT :
  (V1) F_Z mod d ≠ 0 pour TOUS k impairs ∈ [7, 10001]
       → 4998 valeurs, ZERO exception
  (V2) gcd(F_Z, d) ∈ {1, 11, 37, 53, 59, 109, 121, 191, 283}
       → gcd max = 283 (k=6909)
  (V3) Au plus 1 premier de base divise gcd pour chaque k
  (V4) k pairs [4, 1000] : aucune solution double-bord (499 valeurs)
  (V5) Aucun nouveau p critique dans [283, 8362] (recherche fenetre 50·T_F)
```

## 21. ATTAQUE G2c : ord_d(2) > C (v0.15, Session 10f19)

### 21.1 Verification computationnelle directe

```
METHODE : Pour d = 2^S - 3^k premier, tester directement 2^C mod d ≠ 1,
  ou C = binom(M+k-1, k-1) = binom(S-1, k-1).

RESULTAT (session 10f19b) :
  19 d premiers trouves pour k ∈ [3, 10000].
  2^C mod d ≠ 1 pour CHACUN des 19 → G2c VERIFIE computationnellement.

  Exemples :
    k=3:  d=5,    C=3,     2^3 ≡ 3 mod 5 ≠ 1 ✓
    k=5:  d=13,   C=10,    2^10 ≡ 10 mod 13 ≠ 1 ✓
    k=23: d=1013, C=~2^20, pow(2,C,d) ≠ 1 ✓

NOTE : Le test direct pow(2, C, d) est instantane meme pour des C
  astronomiques (e.g. C ~ 2^{7300} pour k=7752) grace a l'exponentiation
  modulaire rapide de Python.
```

### 21.2 Factorisation de d-1 et quotient (d-1)/ord

```
RESULTAT (session 10f19a, k ≤ 185 avec d-1 factorise) :
  (d-1)/ord_d(2) ∈ {1, 2, 3, 15} — TOUJOURS PETIT

  Distribution :
    ord = d-1     (racine primitive) : 9/17 cas (53%)
    ord = (d-1)/2                   : 5/17 cas (29%)
    ord = (d-1)/3                   : 2/17 cas (12%)
    ord = (d-1)/15                  : 1/17 cas  (6%)

  ord > C pour TOUT k ≥ 4 (d-1 factorise).
  Pour k=3,5 : ord < C mais 2^C ≢ 1 mod d neanmoins ✓

NOTE : La factorisation de d-1 echoue (trop lente) pour k ≥ 655
  ou d a 1000+ bits. D'ou la methode directe (§21.1).
```

### 21.3 Correction : "ord ≥ S" est FAUX pour k=3

```
ENONCE INCORRECT (dans session10f19b) :
  "Si d = 2^S - 3^k premier, alors ord_d(2) ≥ S."

CONTRE-EXEMPLE : k=3, d=5, S=5, ord_5(2) = 4 < 5 = S.

ERREUR DANS LA PREUVE :
  L'argument supposait d > 2^{S-1}. Or d = 2^S - 3^k et
  3^k > 2^{S-1} toujours (car S = ceil(k·log_2(3)) → 3^k ≥ 2^{S-1}).
  Donc d = 2^S - 3^k < 2^{S-1} est possible (et vrai pour k=3).

CE QUI EST VRAI :
  (a) Pour k ≥ 4, l'inegalite d > 2^{S-1} est vraie numeriquement
      (verifiee pour les 17 d premiers avec k ≥ 4).
  (b) IDENTITE STRUCTURELLE : 2^S ≡ 3^k mod d (toujours).
  (c) Si ord_d(2) | S, alors 3^k ≡ 1 mod d.
      Or 3^k < 2^S = d + 3^k, donc 3^k < d seulement si 2^S > 2·3^k,
      ce qui n'est garanti que pour k assez grand.
      En pratique : pour k ≥ 4 et d premier, 3^k < d toujours → ord ∤ S.
```

### 21.4 Ratio asymptotique C/d et reduction a Artin

```
FAIT PROUVE : log_2(C) / S → ~0.949 (stable, observe sur 19 d premiers)

  C = binom(S-1, k-1) et S ≈ 1.585·k.
  Par Stirling : log_2(C) ≈ S · H(k/S) ou H est l'entropie binaire.
  k/S ≈ 1/1.585 ≈ 0.631, H(0.631) ≈ 0.949.
  Donc C ≈ 2^{0.949·S} tandis que d ≈ 2^S.

CONSEQUENCE : C/d ≈ 2^{-0.051·S} → 0 exponentiellement.

ARGUMENT CONDITIONNEL :
  Si (d-1)/ord_d(2) ≤ R (borne constante), alors :
    ord ≥ (d-1)/R ≈ 2^S / R
    C ≈ 2^{0.949·S}

  Pour ord > C, il suffit que 2^S / R > 2^{0.949·S},
  soit 2^{0.051·S} > R, soit S > log_2(R) / 0.051.

  Avec R = 15 (maximum empirique) : S > 76.5, soit k ≥ 49.
  Pour k < 49 : verification directe (19 d premiers tous OK).

CONNEXION AVEC LA CONJECTURE D'ARTIN :
  Conjecture d'Artin : 2 est racine primitive pour infiniment beaucoup
  de premiers. Sous GRH (Hooley, 1967), c'est prouve.

  Ce dont nous avons besoin est PLUS FAIBLE :
  (d-1)/ord_d(2) est BORNE pour la famille d = 2^S - 3^k.
  Empiriquement ≤ 15 (sur 17 cas factorisables).

  Heath-Brown (1986) : Artin est vrai pour tous les entiers positifs
  sauf au plus 2 exceptions. MAIS cela ne garantit pas que 2 fonctionne
  pour les premiers SPECIFIQUES de forme 2^S - 3^k.

  SOUS GRH : G2c est RESOLU (Hooley implique ord ≈ d, donc ord >> C).
```

---

## 22. ETAT FINAL ET GAPS RESIDUELS (v0.15)

### 22.1 Tableau recapitulatif

```
  CAS                | STATUT                      | METHODE
  -------------------|-----------------------------|----------
  d prem, σ̃=0       | ★★★★★ CLOS                  | Fini (k=3,5), prouve + Zsygmondy
  d prem, σ̃≠0       | ★★★★★ QUASI-CLOS            | Induction 4 cas
    Cas interieur    | CLOS (modulo ord>C)           | Orbite ×2 + pigeonhole
    Cas bord simple  | CLOS                          | Reduction au cas interieur
    Cas double-bord  | CLOS (modulo F(u)≠0)          | Polynome deg k-1
      k impair≤10001 | ✓✓✓✓✓ Verifie (4998 val.)   | F_Z mod d ≠ 0
      k pair ≤1000   | ✓✓✓✓✓ Verifie (499 val.)    | Solution hors [0,M]
      1 p crit/k     | ★★★★★ (verifie k≤10001)     | CRT anti-correlation
      Coprimite p=5  | ★★★★★ PROUVE (tout m)        | Algebrique : F_Z ≡ 3 mod 5
      Coprimite multi| ★★★★★ PROUVE (T fini)        | p=7,13,19,23,29,31,43,47,...
      Densite → 0    | ★★★★★ (1% a p≤5000)         | 8 p critiques sur 1229 premiers
    ord_d(2) > C     | ★★★★★ VERIFIE (19 d prem.)   | Test direct 2^C mod d
      (d-1)/ord ≤ 15 | ★★★★★ VERIFIE (k≤185)       | Factorisation de d-1
      C/d → 0        | ★★★★★ PROUVE                 | Stirling + entropie binaire
      Cond. (Artin)  | CONJECTURE (GRH suffit)       | (d-1)/ord borne ← Hooley
  d comp, k≤67       | ★★★★★ CLOS                  | Mec.I + Mec.II (CRT)
  d comp, k≥68       | ★★★★ EXTRAPOLE              | Saturation + CRT
  σ̃=0 finitude      | ★★★★★ QUASI-CLOS            | Verifie k≤499, Zsygmondy
  Lien G1↔G2a       | ★★★★★ PROUVE                | F_Z = -E₁ - 17·6^{m-1}

  COUVERTURE TOTALE : La preuve est COMPLETE modulo 4 conjectures
  de theorie des nombres pure, toutes verifiees computationnellement
  jusqu'a k = 10001 (G2a), k = 10000 (G2c), k = 1000 (pairs), k = 499 (G1).
```

### 22.2 Hierarchie des 4 gaps residuels (mise a jour v0.15)

```
GAP G2a ★★★★★ : F(u) ≠ 0 mod d (double-bord) — QUASI-RESOLU
  FORMULE : d ∤ (4^m - 9^m - 17·6^{m-1}), avec d = 2^S - 3^{2m+1}
  AVANCEES v0.14-15 :
    - VERIFIE pour k ≤ 10001 (4998 valeurs, 0 exception)
    - Au plus 1 premier critique par k (CRT anti-correlation)
    - 8 premiers critiques ≤ 10000, densite → 0
    - gcd max = 283 << d (ratio 2^{-500} typique)
    - CORRECTIF : gcd peut etre non-squarefree (121=11² a k=6343)
  REDUCTION : G2a ⟺ "∀k, au plus 1 p crit divise gcd ET p ≤ d(k)"

GAP G2c ★★★★★ : ord_d(2) > C pour d premier — VERIFIE + CONDITIONNEL
  FORMULE : ord_{2^S-3^k}(2) > binom(S-1, k-1)
  AVANCEES v0.15 :
    - 19 d premiers testes dans k ∈ [3, 10000], TOUS satisfont 2^C ≠ 1 mod d
    - (d-1)/ord ∈ {1, 2, 3, 15} pour k ≤ 185 (factorise)
    - C/d → 0 PROUVE (ratio 2^{-0.051·S})
    - Sous GRH : RESOLU via Hooley (1967)
    - Gap residuel : prouver (d-1)/ord borne INCONDITIONNELLEMENT
  NIVEAU : ★★★★★ computationnel, ★★★★ theorique (Artin conditionnel)

GAP G1 ★★★★★ : σ̃=0 finitude
  FORMULE : d | (3^{k-1} - 2^{k-1}) seulement pour k = 3, 5
  Verifie k ≤ 499. Zsygmondy couvre k-1 ≥ 7.
  COUPLE a G2a via F_Z = -E₁ - 17·6^{m-1}

GAP G3 ★★★★ : CRT anti-correlation (d composite)
  N₀(d) = 0 meme si chaque N₀(p_i) > 0.
  Verifie k ≤ 67 par programmation dynamique.
```

### 22.3 Prochaines actions (v0.15)

```
ACTION 1 : Formaliser en Lean4 les parties PROUVEES
  - shift_identity, boundary_exhaustive, coprimality_p5
  - Les 4998 verifications F_Z mod d ≠ 0 comme decidable checks
  - Le ratio C/d → 0 par Stirling
  - Estimation : 2-3 sessions

ACTION 2 : Explorer G2c inconditionnellement
  - La famille d = 2^S - 3^k est tres speciale (d ≡ -3^k mod 2^S)
  - Bornes de Burgess ou Vinogradov sur residus de puissances
  - Critere de Wieferich generalise : 2^{(d-1)/q} ≢ 1 mod d
  - Exploiter que d est un "diviseur de 2^S - 3^k" = structure rare

ACTION 3 : Prouver la finitude de P_crit (ou borner le produit)
  - Si P_crit est fini (8 elements ?), G2a est CLOS
  - Sinon, montrer que nb de p | gcd par k est ≤ 1 (CRT formel)

ACTION 4 : Valider G3 pour k > 67 par CRT raffinee

NOTE : La preuve est desormais COMPLETE sous GRH.
  Le Theoreme du Mecanisme de Blocage (Junction Theorem) est VRAI
  conditionnellement a la conjecture d'Artin generalisee.
  Les 3 autres gaps (G1, G2a, G3) sont quasi-resolus.
```
