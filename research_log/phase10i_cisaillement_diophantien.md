# Phase 10I — Le Cisaillement Diophantien : Topologie du Champ de Collatz

> **Date** : 2026-02-24
> **Statut** : Recherche mathematique pure — Changement de paradigme
> **Auteur** : E. Merle, assist. Claude Opus 4.6
> **Idee directrice** : Ne plus etudier le saumon, mais la montagne.

---

## 0. Le changement de lunettes

### 0.1 L'erreur conceptuelle precedente

Les Phases 10G et 10H etudiaient l'orbite d'un entier n specifique,
ses perturbations epsilon_i, et la coincidence necessaire pour fermer un cycle.
C'est l'approche du **saumon** : suivre une trajectoire particuliere et
esperer qu'elle ne remonte pas la riviere.

Le probleme : parmi les 2^k sequences de parité possibles, il y en a k^7
qui pourraient (en theorie) fermer un cycle. L'approche orbitale ne peut
pas toutes les exclure.

### 0.2 Le nouveau paradigme

L'operateur de Collatz est un **champ de vecteurs discret** sur N (ou Z_2).
Un cycle n'est pas une propriete d'un nombre n — c'est un **lacet ferme**
dans le champ de vecteurs. La question n'est pas "n peut-il revenir a lui-meme ?"
mais "le terrain de Collatz autorise-t-il des lacets fermes loin de l'origine ?"

La reponse vient de la GEOMETRIE du terrain, pas des TRAJECTOIRES individuelles.

### 0.3 L'analogie physique

Un champ de vecteurs sur R^2 autorise des orbites fermees si et seulement si
l'indice de rotation autour du cycle est non nul (Poincare-Bendixson).
En dimension 1 (notre cas, via log(n)), les orbites fermees sont impossibles
SAUF si le champ s'annule — ce qui ne se produit jamais dans un systeme
strictement deterministe comme Collatz.

Mais nous ne sommes pas en dimension 1 continue. Nous sommes dans un systeme
**discret** sur N. La discretude change tout : elle permet les cycles
(la trajectoire "saute" par-dessus les zeros du champ continu).

Le defi : montrer que malgre la discretude, le **cisaillement** impose par
l'irrationalite de log_2(3) rend les lacets fermes impossibles loin de 0.

---

## 1. L'Espace de Collatz

### 1.1 Le plongement mixte

Plongeons N dans l'espace produit :

    X = R_+ x Z_2

via :

    iota : N -> X
    iota(n) = (log(n), n mod 2^infty)

La premiere composante est la **taille archimédienne** (position sur l'echelle log).
La seconde est la **signature 2-adique** (structure modulo puissances de 2).

### 1.2 L'operateur T comme champ de vecteurs sur X

L'operateur de Syracuse accelere T(n) = (3n+1)/2^{v_2(3n+1)} induit :

    T* : X -> X
    T*(r, x) = (r + log3 - a(x)*log2 + epsilon(x),  T_2(x))

ou :
- a(x) = v_2(3x+1) est l'exposant 2-adique (depend de x mod 2^m)
- epsilon(x) = log(1 + 1/(3*exp(r))) est la perturbation (depend de r)
- T_2(x) est l'action de T sur la composante 2-adique

Le **vecteur de deplacement** en un point (r, x) est :

    V(r, x) = T*(r,x) - (r,x) = (log3 - a(x)*log2 + epsilon(r), T_2(x) - x)

### 1.3 La decomposition du champ

    V = V_mult + V_pert

ou :

    V_mult(r, x) = (log3 - a(x)*log2,  T_2(x) - x)     [flux multiplicatif pur]
    V_pert(r, x) = (epsilon(r), 0)                        [perturbation additive]

**Observation fondamentale** :
- V_mult ne depend PAS de r (la taille). C'est un champ "horizontal" sur Z_2.
- V_pert ne depend PAS de x (la structure 2-adique). C'est un champ "vertical" sur R_+.
- V_pert(r) -> 0 quand r -> +infty (evanescence).

---

## 2. Le Cisaillement Diophantien

### 2.1 Definition du cisaillement

**Definition.** Le cisaillement diophantien de l'operateur de Collatz est
la quantite :

    Sigma(k) = k*log3 - S(k)*log2

ou S(k) = sum_{i=0}^{k-1} a_i est la somme des exposants 2-adiques sur k pas.

C'est exactement le gap diophantien Delta, mais vu comme une propriete du
**champ** (via k pas successifs) et non d'un cycle specifique.

### 2.2 Interpretation geometrique

Le flux multiplicatif pur deplace le point (r, x) par :

    r -> r + log3 - a_i*log2

a chaque pas. Apres k pas :

    r -> r + k*log3 - S*log2 = r - Sigma(k)

Pour un cycle (r_k = r_0), il faut Sigma(k) = 0 exactement.
Mais Sigma(k) n'est PAS Delta(k,S) : c'est la somme realisee
par l'orbite effective, pas par le "meilleur" S.

**L'ecart** entre Sigma et 0 est le cisaillement : a chaque tour,
les lignes de flux se **tordent** par un angle Sigma, et cette torsion
est dictee par l'irrationalite de log_2(3).

### 2.3 Propriete fondamentale du cisaillement

**Theoreme (Persistance du cisaillement).**
Soit (a_1, ..., a_k) une suite d'entiers >= 1 avec sum a_i = S.
Alors :

    |k*log3 - S*log2| >= ln2 / k^6     si k >= 2

(c'est Baker, reformule).

**Corollaire (Pas de cisaillement nul).**
Le cisaillement Sigma(k) ne s'annule JAMAIS. Il peut etre petit,
mais jamais nul. C'est la courbure intrinseque de l'espace de Collatz.

### 2.4 Le cisaillement comme courbure

En geometrie differentielle, la courbure d'un fibré mesure l'obstruction
au transport parallele sur un lacet ferme. Ici :

    Transport parallele = flux multiplicatif sur k pas
    Holonomie = Sigma(k) = k*log3 - S*log2

Le cisaillement EST la courbure du fibre de Collatz.
Et cette courbure est non nulle (Baker), ce qui signifie :
**le fibre est courbe, et les sections horizontales ne se referment pas.**

En termes de champ de vecteurs : le champ TOURNE perpetuellement,
et la perturbation V_pert doit compenser cette rotation pour fermer un lacet.

---

## 3. La Competition : Courbure vs Perturbation

### 3.1 Le rayon de courbure

La courbure du fibre en "echelle k" est :

    kappa(k) = |Sigma(k)| >= ln2 / k^6

Le "rayon de courbure" est R(k) = 1/kappa(k) <= k^6/ln2.

Pour refermer un lacet, la perturbation doit "courber" la trajectoire
sur une distance totale egale a 2*pi*R... non, l'analogie est plus precise :

La perturbation totale sur k pas est sum epsilon_i = E_k.
L'equation de fermeture est E_k = |Sigma(k)|.
Le rayon effectif de la boucle est :

    r_boucle = E_k / kappa(k) = (k/(3*n_0)) / (1/k^6) = k^7/(3*n_0)

Pour que la boucle soit "realisable" (r_boucle >= 1 dans un sens a preciser) :

    k^7/(3*n_0) >= 1, soit n_0 <= k^7/3

C'est le Product Bound. La geometrie du cisaillement IMPOSE cette borne.

### 3.2 Le regime asymptotique

Pour r = log(n_0) grand (n_0 >> 1) :

    |V_pert| = epsilon ~ 1/(3*n_0) = e^{-r}/3

La perturbation decroit EXPONENTIELLEMENT en r.

Mais le cisaillement est INDEPENDANT de r :

    |kappa(k)| >= ln2/k^6

Le rapport perturbation/courbure est :

    |V_pert| / kappa = k * e^{-r} / (3 * ln2 / k^6) = k^7 * e^{-r} / (3*ln2)

Pour que ce rapport soit >= 1 (necessaire pour fermer un lacet) :

    r <= log(k^7/(3*ln2)) = 7*log(k) - log(3*ln2)

En termes de n_0 : n_0 <= k^7/(3*ln2).

**Au-dela de ce rayon, la perturbation est trop faible pour courber
la trajectoire : aucun lacet ne peut se fermer.**

### 3.3 La zone de capture

Definissons la **zone de capture** :

    Z(k) = {n : 1 < n < k^7/(3*ln2), n impair}

C'est la seule region de N ou un cycle de parametres (k, S) pourrait exister.
En dehors de Z(k), le cisaillement domine la perturbation.

**Proprietes de Z(k) :**
- |Z(k)| ~ k^7/(6*ln2)  (nombre d'impairs dans la zone)
- Pour k <= 1322 : Z(k) subset [1, 2^71), couvert par Barina
- Pour k > 1322 : Z(k) deborde au-dela de 2^71

---

## 4. L'Impossibilite Topologique (Framework)

### 4.1 L'indice de rotation

Pour un champ de vecteurs continu sur R^2, le theoreme de Poincaré-Bendixson
dit qu'une orbite bornee qui n'atteint pas un point fixe converge vers un cycle limite.
Et l'indice de rotation du cycle est +1.

Dans notre cas discret 1D (sur log(N)), la notion d'indice est :

    I(gamma) = (1/(2*pi)) * sum_{pas du cycle} angle(V, V_{pur})

ou angle(V, V_pur) est l'ecart angulaire entre le champ total et le flux pur.

Pour un cycle de Collatz :

    I = (1/(2*pi)) * sum epsilon_i / |V_mult|

Mais |V_mult| ~ |log3 - a_i*log2| qui change de signe (parfois le flux monte,
parfois il descend). L'indice n'est pas bien defini dans ce cadre 1D.

### 4.2 Reformulation en dimension 2 : le tore de Collatz

Utilisons les deux coordonnees naturelles :

    theta = log(n) mod (S*log2)      [phase archimédienne, cyclique]
    phi = n mod 2^M                  [phase 2-adique, cyclique]

L'operateur T agit sur le tore T^2 = (R/Z) x (Z/2^M Z) par :

    (theta, phi) -> (theta + log3 - a*log2 mod S*log2,  T_2(phi))

Un cycle correspond a un point fixe de T^k sur le tore.

### 4.3 La rotation irrationnelle

Sur la premiere coordonnee, T agit par translation de log3 - a*log2.
La moyenne de ce shift est :

    <shift> = log3 - 2*log2 = log(3/4)

qui est IRRATIONNEL par rapport a S*log2 (car log_2(3) est irrationnel).

Par le theoreme de Weyl sur l'equidistribution des rotations irrationnelles :
les orbites de la composante theta sont DENSES dans R/Z (pour presque tout n).

**Un point fixe de T^k (cycle) sur le tore requiert :**

    k * <shift> = 0 mod S*log2

C'est-a-dire :

    k*log3 - S*log2 = 0

ce qui est IMPOSSIBLE (irrationalite de log_2(3)).

### 4.4 Le defaut : la perturbation modifie le shift

L'argument ci-dessus est incomplet car la perturbation epsilon_i MODIFIE
le shift effectif de theta a chaque pas. Le shift reel est :

    shift_i = log3 - a_i*log2 + epsilon_i

Et la condition de cycle est :

    sum shift_i = 0

ce qui est l'equation maitresse sum epsilon_i = S*log2 - k*log3 = -Sigma.

Donc la perturbation compense exactement le cisaillement. C'est la
reformulation du probleme, pas sa solution.

### 4.5 L'argument de rigidite du tore

**Theoreme (Rigidite modulaire du tore de Collatz).**

Considerons l'action de T^k sur le tore T_M = (R/(S*ln2)*Z) x (Z/2^M Z)
pour M assez grand. Un cycle de longueur k correspond a un point fixe
(theta_0, phi_0) de cette action.

La composante 2-adique : phi_0 doit etre un point fixe de T_2^k sur Z/2^M Z.
Par Bernstein-Lagarias, l'action de T_2 est conjuguee au shift, qui a
tres peu de points fixes (exactement 2^M / ord_M ou ord_M est l'ordre).

La composante archimédienne : theta_0 doit satisfaire l'equation maitresse.

La rigidite vient de l'INDEPENDANCE des deux composantes :
la composante 2-adique impose phi_0 dans un ensemble FINI (les points fixes de T_2^k).
La composante archimédienne impose theta_0 dans un ensemble de mesure ZERO.

L'intersection est generiquement VIDE.

---

## 5. Le Champ de Vecteurs et ses Proprietes Globales

### 5.1 La decomposition de Helmholtz discrete

Tout champ de vecteurs sur un graphe se decompose en :

    V = V_gradient + V_rotationnel + V_harmonique

Pour le champ de Collatz V(n) = T(n) - n :

**Composante gradient** (potentiel) :
V a une composante descendante nette car E[V] ~ n*(3/4 - 1) = -n/4 < 0.
Le "potentiel" est U(n) ~ n^2/8 (l'orbite descend le potentiel en moyenne).

**Composante rotationnelle** (cisaillement) :
C'est la partie qui "tourne" autour de l'espace. Elle est generee par
l'alternance entre multiplication par 3 et division par 2, qui ne commutent pas.

**Le cisaillement diophantien EST la composante rotationnelle.**

### 5.2 Non-commutativite de la multiplication et de la division

L'operateur fondamental est :

    T = D_2^{a} circ M_3 circ A_1

ou M_3(n) = 3n, A_1(n) = n+1, D_2^a(n) = n/2^a.

Les operateurs M_3 et D_2 commutent (3*(n/2) = (3n)/2 si 2|n).
Mais A_1 ne commute avec AUCUN des deux :

    M_3(A_1(n)) = 3n+3  =/=  A_1(M_3(n)) = 3n+1
    D_2(A_1(n)) = (n+1)/2  =/=  A_1(D_2(n)) = n/2 + 1

Ce defaut de commutativite est le +1. Et il produit un **commutateur** :

    [M_3, A_1](n) = M_3*A_1(n) - A_1*M_3(n) = 3n+3 - 3n-1 = 2

Le commutateur est une CONSTANTE : 2. Cela evoque la relation de
commutation de Heisenberg [x, p] = i*hbar. Ici : [3x, x+1] = 2.

### 5.3 L'algebre de Lie du systeme de Collatz

Les operateurs M_3, D_2, A_1 engendrent un mono-ide. En passant aux
logarithmes (continualisation), les generateurs deviennent :

    m_3 = +log3     (multiplication par 3 = translation de +log3)
    d_2 = -log2     (division par 2 = translation de -log2)
    a_1 = +epsilon  (addition de 1 = perturbation de +log(1+1/(3n)))

Les deux premiers generent une algebre abelienne (translations de R).
Le troisieme introduce la non-commutativite via :

    [m_3, a_1] = d(epsilon)/d(log n) * m_3 = -1/(3n) * log3

C'est une algebre de Lie **non nilpotente** (le commutateur depend de n,
pas seulement des generateurs).

### 5.4 Consequence : impossibilite des orbites exactement periodiques

**Theoreme (Obstruction par le commutateur, heuristique).**

Si le commutateur [m_3, a_1] etait nul, l'operateur T serait conjugue a
une rotation pure, et les orbites periodiques correspondraient aux points
de resonance rationnelle. Puisque log_2(3) est irrationnel, il n'y aurait
aucune resonance et aucun cycle.

Le commutateur est NON NUL mais DECROISSANT en n. Pour n grand,
il vaut ~2/(3n) -> 0. Le systeme est "presque abelien" a l'infini.

**Argument** : Dans un systeme "presque abelien" avec rotation irrationnelle,
les orbites sont "presque denses" sur le tore (par Weyl). Les points
periodiques sont les solutions d'une equation diophantienne (l'equation
maitresse) dont le membre gauche est rigide (Baker) et le membre droit
est la contribution du commutateur. Pour n grand, cette contribution -> 0
et ne peut plus compenser la rigidite. Donc pas de cycle.

Le probleme : cette argument heuristique ne donne pas le seuil exact
au-dela duquel les cycles sont impossibles, et la transition
"presque abelien" -> "abelien" n'est pas uniforme.

---

## 6. Le Theoreme de Non-Fermeture (Poincaré-Bendixson discret)

### 6.1 L'enonce cible

**Theoreme (Non-fermeture au-dela du rayon de courbure).**

Soit R_k = k^7/(3*ln2) le rayon de courbure du champ de Collatz
a l'echelle k. Pour tout n_0 impair > R_k et tout k >= 2 :

    T^k(n_0) =/= n_0

Autrement dit : aucun cycle de longueur k n'a son minimum au-dela de R_k.

### 6.2 Preuve

C'est exactement la Product Bound (Phase 56). Si T^k(n_0) = n_0,
alors l'equation maitresse donne :

    |Sigma(k)| = sum epsilon_i <= k/(3*n_0)

Baker : |Sigma(k)| >= ln2/k^6. Donc :

    n_0 <= k^7/(3*ln2) = R_k

Contraposee : si n_0 > R_k, alors T^k(n_0) =/= n_0. CQFD.

### 6.3 Interpretation geometrique

Le rayon de courbure R_k est la DISTANCE MAXIMALE a laquelle la perturbation
peut courber la trajectoire assez pour la refermer en k pas.

Au-dela de R_k, la courbure du cisaillement DOMINE la flexibilite de la
perturbation. Les lignes de flux sont trop "droites" pour se refermer.

### 6.4 Le probleme restant

Pour k <= 1322 : R_k < 2^71, et Barina couvre la zone.
Pour k > 1322 : R_k > 2^71, et la zone R_k \ [0, 2^71) n'est pas couverte.

**La question ouverte est : la zone de capture Z(k) = [1, R_k] contient-elle
des cycles pour k > 1322 ?**

Avec Legendre (non-convergents) + fenetres convergentes : Z(k) ∩ [1, 2^71]
couvre k <= K_max ~ 5*10^10. Mais pour k > K_max, la zone Z(k) est
strictement plus grande que [1, 2^71] et le Product Bound ne suffit pas.

---

## 7. La Courbure Effective : Au-dela de Baker

### 7.1 L'idee centrale

Baker donne kappa(k) >= ln2/k^6. C'est la courbure MINIMALE.
Mais la courbure REELLE, pour un k specifique, est :

    kappa_reel(k) = |k*log3 - S(k)*log2|

et cette quantite est souvent BEAUCOUP plus grande que 1/k^6.

### 7.2 La distribution des courbures

Les fractions continues de log_2(3) = [1; 1, 1, 2, 2, 3, 1, 5, 2, 23, ...]
montrent que les convergents p_n/q_n donnent :

    |log_2(3) - p_n/q_n| ~ 1/(q_n * q_{n+1})

Pour k = q_n : kappa(k) ~ ln2 * k / (q_{n+1}) ~ ln2 / q_{n+1}
(meilleure que Baker si q_{n+1} < k^5).

Pour k =/= q_n : kappa(k) >= ln2/(2k)  (Legendre, bien meilleure que Baker).

**La courbure est HETEROGENE** : tres forte pour la plupart des k,
exceptionnellement faible pour les k convergents.

### 7.3 Le spectre de cisaillement

Definissons le spectre de cisaillement comme la suite :

    {kappa(k) : k = 1, 2, 3, ...}

Ce spectre a la structure suivante :
- Pour "presque tout" k : kappa(k) ~ 1/(2k) >> 1/k^6  (Legendre)
- Pour les k convergents : kappa(k) ~ 1/(k*q_{n+1}) qui peut etre << 1/(2k)
- Borne inferieure uniforme : kappa(k) >= 1/k^6 (Baker)

Le rayon de courbure correspondant :
- Generic : R_k ~ 2k^2/ln2  (couvrable par Barina pour k <= K_max)
- Convergent : R_k ~ k*q_{n+1}/ln2  (potentiellement tres grand)
- Borne superieure uniforme : R_k <= k^7/3  (Product Bound)

### 7.4 Consequence pour les fenetres convergentes

Les denominateurs de convergents de log_2(3) sont :

    q_0=1, q_1=1, q_2=2, q_3=5, q_4=12, q_5=41, q_6=53, q_7=306,
    q_8=665, q_9=15601, q_{10}=31867, ...

Pour chaque k = q_n, le rayon de capture est :

    R_{q_n} ~ q_n * q_{n+1} / ln2

Ces rayons croissent exponentiellement (puisque q_n croit exponentiellement).
Ils depassent 2^71 pour n >= ~25.

MAIS : le nombre de fenetres convergentes est FINI (pour k <= K_max).
Et au-dela de K_max, meme les non-convergents ont R_k > 2^71.

---

## 8. Synthese : La Topographie de l'Impossibilite

### 8.1 La carte du terrain de Collatz

```
                    R_k (rayon de courbure)
                    |
    k^7/3 -----    |===================================== Product Bound
                    |                                     (Regime III : impossible)
                    |
    2^71  -----    |--- Barina (verification) ----
                    |   ELIMINE pour k <= K_max
                    |
    k^2   -----    |--- Legendre (non-convergents) ---
                    |
                    |                 ZONE DE COMBAT
                    |                 k > K_max et
                    |                 n_0 in [2^71, k^7/3]
                    |
    1     -----    |--- Cycles connus ({1}, {-1,-5,...}) ---
                    |
                    +---+---+---+---+---+---+---+---+----> k
                        1322    K_max    ???
```

### 8.2 Les trois barrieres

1. **Barriere de Barina** (r < 2^71) : zone verifiee, pas de cycle.
2. **Barriere de Legendre** (r < k^2/ln2) : pour les k non-convergents.
3. **Barriere du Product Bound** (r < k^7/3) : universelle mais faible.

La zone de combat est l'intersection :
- k > K_max
- n_0 in (2^71, k^7/3)

C'est une region de taille ~ k^7 entiers, pour chaque k > K_max.

### 8.3 Ce que le cisaillement apporte

L'approche topologique par le cisaillement ne ferme PAS le gap.
Mais elle CLARIFIE la structure du probleme :

(A) Le cisaillement est la COURBURE intrinseque de l'espace de Collatz.
    Il ne depend pas de l'orbite, mais des nombres k et S.

(B) La perturbation est le RAYON DE COURBURE du lacet potentiel.
    Il depend de n_0 et decroit quand n_0 croit.

(C) La condition de fermeture est COURBURE * RAYON >= TORSION COMPLETE,
    ce qui donne exactement le Product Bound.

(D) La percee viendrait d'une estimation plus fine de la courbure EFFECTIVE
    qui prenne en compte non seulement Baker (courbure minimale)
    mais aussi les contraintes de COHERENCE entre les k pas du cycle
    (la dynamique ne permet pas n'importe quelle sequence a_i).

### 8.4 L'invariant topologique manquant

Le theoreme de Poincaré-Bendixson en dimension 2 garantit que si l'indice
de rotation est 0, il n'y a pas de cycle. Dans notre cadre discret,
l'invariant analogue serait un **nombre d'enroulement** :

    W(gamma) = (1/2*pi) * sum_{cycle} arctan(V_pert(i) / V_mult(i))

Si on pouvait montrer que W est toujours non entier pour les lacets
potentiels dans la zone de combat, le probleme serait resolu.

Mais calculer W requiert de connaitre V_mult et V_pert en chaque point
du lacet, ce qui revient a l'approche orbitale que nous voulions eviter.

### 8.5 La vraie contribution de l'approche topologique

L'apport n'est pas une preuve nouvelle. C'est un **cadre conceptuel** :

1. Le probleme de Collatz est un probleme de **geometrie du fibre**
   (log(n), n mod 2^M) -> N
2. La courbure du fibre est le cisaillement diophantien
3. Les cycles sont les sections horizontales fermees
4. L'impossibilite des cycles est l'obstruction topologique
   a l'existence de telles sections

Ce cadre suggere que la bonne approche n'est ni l'analyse elementaire
(Product Bound) ni la theorie analytique des nombres (Baker),
mais la **theorie des fibres** et les **classes caracteristiques**
du systeme dynamique de Collatz.

---

## 9. Vers une Classe de Chern du Fibre de Collatz

### 9.1 Construction du fibre

Considerons le fibre E -> Z/dZ (d = 2^S - 3^k) dont la fibre au-dessus
de [corrSum] in Z/dZ est l'ensemble des n_0 tels que :

    n_0 * d = corrSum mod d^2

Ce fibre a une connexion induite par l'operateur T, et sa courbure
est liee au cisaillement Sigma(k).

### 9.2 La classe de Chern (speculatif)

Si le fibre E est non trivial (classe de Chern c_1 =/= 0),
alors il n'admet pas de section globale, ce qui signifierait :
aucun n_0 entier ne satisfait l'equation de cycle.

La classe de Chern c_1 serait :

    c_1(E) = (1/2*pi) * integral Sigma(k) dk = (1/2*pi) * [k*log3 - S*log2]

Mais cette integrale n'a pas de sens tel quel (k est discret).

**C'est la direction de recherche a poursuivre** : donner un sens rigoureux
a la classe de Chern du fibre de Collatz et montrer qu'elle est non triviale
pour les grandes echelles.

---

## 10. Conclusions et Diagnostic

### 10.1 Ce que l'approche topologique PROUVE

- Le Product Bound est une consequence GEOMETRIQUE du cisaillement (section 6)
- La courbure heterogene (Baker vs Legendre) structure la zone de combat (section 7)
- Le cadre conceptuel est propre et suggestif

### 10.2 Ce que l'approche topologique NE PROUVE PAS

- L'absence de cycles dans la zone [2^71, k^7/3] pour k > K_max
- L'inexistence d'un invariant topologique effectif
- Une borne meilleure que le Product Bound

### 10.3 La lecon fondamentale

Le probleme de Collatz est resistant parce que :

1. Le cisaillement (courbure) et la perturbation (rayon) decroissent
   A LA MEME VITESSE en k (tous deux en k^{-6} dans la zone critique).

2. La transition entre "regime perturbatif" (cycles possibles) et
   "regime cisaille" (cycles impossibles) est une TRANSITION DE PHASE
   qui se produit exactement a n_0 ~ k^7, et cette frontiere n'est
   recouverte par aucune verification computationnelle.

3. La discretude de N empeche d'utiliser les outils continus (Poincaré-Bendixson,
   classes de Chern) directement. L'analogie est suggestive mais pas probante.

**Le Saint-Graal reste le meme** (Phase 10H, section 11) :
un exposant delta > 0 dans la decorrelation dynamique des epsilon_i,
ou dans la courbure effective du cisaillement.

---

*Fin du rapport Phase 10I — Le Cisaillement Diophantien*
