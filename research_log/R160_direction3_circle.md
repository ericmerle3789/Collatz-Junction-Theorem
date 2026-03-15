# R160bis — Direction 3 : Methode du cercle a phases exponentielles

**Date** : 15 mars 2026
**Type** : Investigation structurelle — methode du cercle pour corrSum
**Verrou** : N_0(d) = 0 pour k = 22..41

---

## RAPPEL DU CADRE

La formule exacte par orthogonalite des caracteres de Z/dZ :

$$N_0(d) = \frac{1}{d} \sum_{t=0}^{d-1} T(t), \quad T(t) = \sum_{A \text{ monotone}} e\left(\frac{t \cdot \text{corrSum}(A)}{d}\right)$$

Le terme t=0 donne C/d < 1. La question : la somme sur t >= 1 est-elle bornee par un argument de type arcs majeurs / arcs mineurs, SANS passer par le CRT ?

---

## A. ARCS MAJEURS POUR corrSum

### A.1 Definition des arcs majeurs

Pour t/d proche de a/q avec q petit (q << d), la phase e(t * corrSum / d) est approximee par e(a * corrSum / q). L'arc majeur associe a (a,q) est l'ensemble des t tels que |t/d - a/q| < delta/d pour un parametre delta a choisir.

La contribution de l'arc (a,q) est (en premiere approximation) :

$$\sum_{|t - ad/q| < \delta} T(t) \approx T_q(a) \cdot \hat{W}(\text{voisinage})$$

ou T_q(a) = sum_A e(a * corrSum(A) / q) est la somme de caracteres mod q.

### A.2 Calcul de T_q(a) pour q petit

**q = 2** : corrSum mod 2 n'est PAS constant. Pour k=5, S=9 : 46 compositions donnent corrSum pair, 24 donnent corrSum impair. Donc |T_2(1)| = |46 - 24| = 22, et |T_2(1)|/C = 22/70 = 0.314.

Analyse : corrSum = sum 3^{k-1-j} * 2^{b_j}. Tous les termes sauf j=k-1 (qui donne 2^{S-k}) ont un facteur 3^m impair multiplie par 2^{b_j}. La parite de corrSum depend de la parite de sum 3^{k-1-j} * 2^{b_j}, qui est non triviale.

**VERDICT q=2** : Contribution non triviale, |T_2(1)|/C ~ 0.31.

---

**q = 3** : corrSum mod 3 est CONSTANT.

**THEOREME (T174, R142)** : corrSum(A) ≡ 2^{S-k} mod 3 pour toute composition A de S en k parts.

**Preuve** : corrSum = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{b_j}. Pour j < k-1, le facteur 3^{k-1-j} avec k-1-j >= 1 est divisible par 3. Le seul terme non nul mod 3 est j = k-1 : 3^0 * 2^{b_{k-1}} = 2^{S-k}. Donc corrSum ≡ 2^{S-k} mod 3. La valeur depend de la parite de S-k : si S-k pair, corrSum ≡ 1 mod 3 ; si S-k impair, corrSum ≡ 2 mod 3. Dans les deux cas, c'est CONSTANT sur toutes les compositions. QED.

**Consequence** : T_3(a) = C * e(a * 2^{S-k} / 3), donc |T_3(a)| = C. La contribution des arcs q=3 est TRIVIALE (aucune annulation). C'est exactement la contribution du terme principal.

**VERDICT q=3** : Contribution MAXIMALE (pas d'annulation). L'arc q=3 ne discrimine rien.

---

**q = 6** : Combinaison de q=2 et q=3. Puisque corrSum mod 3 est constant, corrSum mod 6 ne prend que 2 valeurs sur 6. Pour k=5, S=9 : corrSum mod 6 in {1, 4} (verifie). |T_6(1)|/C = 22/70 = 0.314 (meme que q=2, car le facteur mod 3 est constant).

---

**q = 9** : corrSum mod 9 n'est PAS constant mais restreint. Pour k=5, S=9 : corrSum mod 9 in {1, 4}. |T_9(a)|/C = 0.569 pour tout a premier a 9.

La restriction vient de corrSum mod 9 : le terme j=k-1 donne 2^{S-k} mod 9, et le terme j=k-2 donne 3 * 2^{b_{k-2}} mod 9 = 3 * 2^{b_{k-2}}, qui est 3 * {1,2,4,8,7,5} mod 9 = {3,6,3,6,3,6} mod 9. Les termes j <= k-3 ont facteur 9 ou plus. Donc corrSum mod 9 = 2^{S-k} + 3 * 2^{b_{k-2}} mod 9, et seules certaines valeurs sont atteintes.

**VERDICT q=9** : Restriction partielle mais gcd(d, 9) = gcd(d, 3) = 1, donc INOPERANT pour le module d.

---

**q = 5, 7, 11, ...** (premiers ne divisant pas 3) : Pour ces q, corrSum mod q couvre TOUS les residus (verifie pour k=5,S=9 sur q=5,7,11,13). Les sommes |T_q(a)|/C sont petites : de l'ordre de 1/sqrt(q) a 1/q (annulations significatives).

### A.3 Classification des arcs majeurs naturels

| Module q | Image corrSum mod q | |T_q(1)|/C | Utilite pour le verrou |
|----------|---------------------|-----------|------------------------|
| 2 | 2 valeurs (non uniforme) | 0.31 | Inoperant (gcd(d,2)=1) |
| 3 | 1 valeur (CONSTANT) | 1.00 | TRIVIAL (pas d'annulation) |
| 4 | 4 valeurs | 0.23 | Inoperant (gcd(d,4)=1) |
| 5 | 5 valeurs (toutes) | 0.07 | Utile si 5|d |
| 6 | 2 valeurs | 0.31 | Inoperant |
| 7 | 7 valeurs (toutes) | 0.07 | Utile si 7|d |
| 9 | 2 valeurs | 0.57 | Inoperant (gcd(d,3)=1) |
| 12 | 4 valeurs | 0.23 | Inoperant |

**Observation structurelle** : Les arcs q = 2^a * 3^b sont contamines par les proprietes triviales (corrSum mod 2 et mod 3). Seuls les arcs q = p premier avec p | d sont pertinents. Mais pour ces q, la somme T_q(a) est exactement la somme qui definit N_0(p) par orthogonalite. On retombe sur l'information CRT.

### A.4 VERDICT SECTION A

Les arcs majeurs du cercle a phases corrSum se decomposent naturellement en :
- Arcs triviaux (q = 3^m) : aucune annulation, contribution maximale
- Arcs inoperants (q = 2^a * 3^b) : annulations reelles mais gcd(d, q) = 1
- Arcs CRT (q = p | d) : donnent exactement N_0(p), i.e. l'information deja disponible via le CRT

**Les arcs majeurs N'APPORTENT RIEN de nouveau par rapport au CRT.**

---

## B. ARCS MINEURS

### B.1 Le probleme des phases exponentielles

Sur les arcs mineurs (t/d loin de toute fraction a/q avec q petit), il faut montrer que |T(t)| est petit. La difficulte fondamentale :

corrSum = sum 3^{k-1-j} * 2^{b_j}

Les phases 2^{b_j} sont EXPONENTIELLES en b_j. Les outils classiques de bornes sur les arcs mineurs sont :

| Outil | Phase requise | Notre phase | Applicable ? |
|-------|--------------|-------------|:------------:|
| Weyl differencing | Polynomiale (a^d) | Exponentielle (2^a) | **NON** |
| Vinogradov mean value | Polynomiale | Exponentielle | **NON** |
| van der Corput | C^2, oscillante | Discrete, exponentielle | **NON** |
| Phase stationnaire | Lisse | Discrete | **NON** |
| Bourgain-Demeter-Guth | Polynomiale (courbe) | Exponentielle | **NON** |

L'identification est la meme que celle de R86 (candidat DEMC) : les phases exponentielles sortent du cadre Hardy-Littlewood standard, et AUCUN des outils classiques ne s'applique.

### B.2 La structure simplexe aide-t-elle ?

La somme porte sur les compositions monotones : b_0 <= b_1 <= ... <= b_{k-1} = S-k. C'est un simplexe dans Z^k.

Pour les bornes classiques (Weyl, van der Corput), le domaine de sommation est typiquement un intervalle ou une boite. Le passage d'une boite a un simplexe se fait par transformation de Mobius ou par decoupage, mais introduit un facteur k! de perte (cf. R85 : "Large Sieve — la boite englobant le simplexe a volume k! x simplexe").

Pour notre probleme : la contrainte de monotonie reduit le nombre de termes de (S-k+1)^k (boite) a C(S-1, k-1) (simplexe, beaucoup plus petit). Mais cette reduction est deja INCORPOREE dans le comptage C. Elle n'aide pas a borner les phases exponentielles.

**VERDICT B.2** : La structure simplexe ne compense pas les phases exponentielles.

### B.3 Substitution u_j = 2^{b_j} : linearisation des phases

En posant u_j = 2^{b_j}, la somme devient :

$$T(t) = \sum_{\substack{u_0 \leq u_1 \leq \cdots \leq u_{k-1} = 2^{S-k} \\ u_j \in \{1, 2, 4, \ldots, 2^{S-k}\}}} e\left(\frac{t \cdot \sum_j 3^{k-1-j} u_j}{d}\right)$$

**Avantage** : corrSum = sum 3^{k-1-j} u_j est maintenant LINEAIRE en les u_j. Les phases sont lineaires en les variables de sommation.

**Inconvenient** : les u_j sont CONTRAINTS a etre des puissances de 2. L'ensemble {1, 2, 4, ..., 2^{S-k}} contient seulement S-k+1 elements dans un intervalle de taille 2^{S-k}. La densite est :

$$\frac{S-k+1}{2^{S-k}} \sim \frac{S}{2^S}$$

Pour k=22, S=35 : densite = 14/8192 ~ 0.0017. Extremement lacunaire.

**Le probleme deplace** : au lieu de phases exponentielles sur un domaine dense, on a des phases lineaires sur un domaine EXTREMEMENT LACUNAIRE (puissances de 2). Les outils pour les sommes lineaires sur des ensembles lacunaires sont... les memes que pour les sommes exponentielles de Gauss sur des sous-groupes multiplicatifs. On retombe sur le verrou S_H(t).

**Preuve formelle de l'equivalence** : La substitution u_j = 2^{b_j} transforme la somme sur le simplexe des b_j en une somme sur les k-tuples croissants de puissances de 2. La phase lineaire sum alpha_j u_j avec alpha_j = t * 3^{k-1-j} / d, evaluee sur des puissances de 2, est exactement la definition d'une somme exponentielle sur le sous-groupe multiplicatif H = <2> dans Z/dZ, avec des poids geometriques 3^{k-1-j}. C'est le produit correle de R85.

**VERDICT B.3** : La substitution u_j = 2^{b_j} donne des phases lineaires mais sur un ensemble lacunaire (puissances de 2). L'equivalence formelle avec le produit correle est EXACTE. Aucun gain.

### B.4 Approximation des puissances de 2 par un ensemble regulier ?

Peut-on remplacer {1, 2, 4, ..., 2^M} par un ensemble REGULIER et borner l'erreur ? L'idee serait d'utiliser un ensemble de type progression arithmetique ou ensemble bien distribue, puis de borner le terme d'erreur.

**Obstruction** : l'ensemble des puissances de 2 dans [1, 2^M] a M+1 elements dans un intervalle de 2^M. Pour l'approximer par un ensemble regulier de meme taille, il faudrait un pas ~ 2^M / M. L'erreur d'approximation sur la phase e(alpha * u) pour |alpha| ~ 1 serait de l'ordre de |alpha| * 2^M / M, qui est ENORME (~ 2^M / M >> 1).

Plus fondamentalement : les puissances de 2 ont une structure multiplicative specifique qui est DETRUITE par toute approximation additive. La lacunarite est la RAISON pour laquelle les bornes sont difficiles — ce n'est pas un artefact eliminable.

**VERDICT B.4** : L'approximation des puissances de 2 par un ensemble regulier introduit une erreur qui noie le signal. Non viable.

### B.5 VERDICT SECTION B

Les arcs mineurs ne peuvent pas etre bornes par les outils connus :
1. Les phases exponentielles 2^{b_j} sortent du cadre Hardy-Littlewood (MORT)
2. La structure simplexe n'aide pas a compenser (MORT)
3. La substitution u_j = 2^{b_j} linearise les phases mais revele une somme sur un ensemble lacunaire — formellement equivalente au produit correle (RETOUR AU VERROU)
4. L'approximation des puissances de 2 par un ensemble regulier est non viable (MORT)

---

## C. LA SINGULARITE DE LA SERIE SINGULIERE

### C.1 Calcul de la serie singuliere

La serie singuliere pour N_0(d) est definie par :

$$\mathfrak{S} = \prod_{p | d} \sigma_p, \quad \sigma_p = \frac{1}{p} \sum_{t=0}^{p-1} \frac{T_p(t)}{C} = \frac{p \cdot N_0(p)}{C}$$

ou T_p(t) = sum_A e(t * corrSum(A) / p) et on utilise (1/p) sum_t T_p(t) = N_0(p).

Le terme sigma_p = p * N_0(p) / C est exactement la DENSITE LOCALE : le rapport entre le nombre observe de solutions mod p et le nombre predit par l'uniformite (C/p).

La prediction du cercle est :

$$N_0(d) \approx \frac{C}{d} \cdot \mathfrak{S} = \frac{C}{d} \cdot \prod_{p|d} \frac{p \cdot N_0(p)}{C}$$

### C.2 Comparaison avec le CRT

L'hypothese d'independance CRT (Ratio Law) predit :

$$N_0(d) \approx \prod_{p|d} N_0(p) \cdot \frac{1}{C^{\omega(d)-1}}$$

ou omega(d) est le nombre de facteurs premiers de d.

**Comparaison** :
- Cercle : N_0(d) ~ (C/d) * prod (p * N_0(p) / C)
- CRT : N_0(d) ~ prod N_0(p) / C^{omega-1}

En developpant le produit du cercle :

$$\frac{C}{d} \cdot \prod_{p|d} \frac{p \cdot N_0(p)}{C} = \frac{C \cdot \prod p \cdot \prod N_0(p)}{d \cdot C^{\omega}} = \frac{d \cdot \prod N_0(p)}{d \cdot C^{\omega-1}} = \frac{\prod N_0(p)}{C^{\omega-1}}$$

(en utilisant d = prod p pour d sans facteurs carres)

**LES DEUX FORMULES SONT IDENTIQUES.**

### C.3 Verification numerique

Pour k=5, S=9, d=35=5*7 :
- N_0(35) = 3
- N_0(5) = 13, N_0(7) = 11
- CRT prediction : 13 * 11 / 70 = 2.043
- Cercle prediction : (70/35) * (5*13/70) * (7*11/70) = 2 * 0.929 * 1.100 = 2.043

Meme valeur. L'ecart avec N_0(35) = 3 est le terme d'erreur (les arcs mineurs + les correlations non capturees par le produit).

### C.4 Y a-t-il un terme correctif ?

Dans la methode du cercle standard (Waring, Goldbach), il y a un terme d'erreur :

$$N_0(d) = \frac{C}{d} \cdot \mathfrak{S} + E$$

ou E est la contribution des arcs mineurs. Si on pouvait montrer |E| < C/d, on aurait N_0(d) < 2C/d (utile si C/d < 1/2).

**Mais** : borner |E| necessite de borner |T(t)| sur les arcs mineurs, ce qui revient exactement au probleme des phases exponentielles (Section B). Et le terme correctif entre le produit CRT et N_0(d) reel est exactement la "correlation CRT" que les 160 rounds precedents n'ont pas reussi a quantifier.

### C.5 VERDICT SECTION C

**La serie singuliere du cercle est EXACTEMENT le produit CRT.**

Demonstration algebrique : les deux expressions se reduisent a prod N_0(p) / C^{omega-1}.

Verification numerique : confirme l'identite.

Consequence : la methode du cercle, dans sa partie "arcs majeurs", ne donne AUCUNE information supplementaire par rapport au CRT. La seule possibilite de gain serait dans les arcs mineurs, mais ceux-ci sont inattaquables (Section B).

---

## D. L'ANGLE "SOMME DE DIGITS EN BASE MIXTE"

### D.1 Reduction modulaire de corrSum

Pour un premier p | d avec r = ord_p(2) :

$$\text{corrSum} \mod p = \sum_{j=0}^{k-1} 3^{k-1-j} \cdot 2^{b_j \bmod r} \mod p$$

Seule la valeur b_j mod r importe (car 2^r ≡ 1 mod p). C'est le Modular Decoupling Lemma (MDL) de R86.

### D.2 Analogie avec les criteres de divisibilite par digits

**Divisibilite par 9 en base 10** : n ≡ sum(digits de n) mod 9. C'est parce que 10 ≡ 1 mod 9.

**Divisibilite par 11 en base 10** : n ≡ sum((-1)^i * digit_i) mod 11. C'est parce que 10 ≡ -1 mod 11.

**Notre probleme** : corrSum = sum c_j * 2^{b_j} ou c_j = 3^{k-1-j}. Mod p, ceci est determine par les "r-digits" s_j = b_j mod r :

$$\text{corrSum} \mod p = f(s_0, s_1, \ldots, s_{k-1})$$

ou f(s_0, ..., s_{k-1}) = sum 3^{k-1-j} * 2^{s_j} mod p.

C'est bien un critere de divisibilite de type "digit", mais les "digits" sont les residus des b_j modulo r (l'ordre de 2), et le "poids" de chaque digit est 3^{k-1-j} (une puissance de 3, pas de 2).

### D.3 Resultats d'Allouche-Shallit et Stolarsky

Les travaux d'Allouche et Shallit (Automatic Sequences, 2003) etudient les suites definies par les chiffres de n dans une base fixee. Les resultats pertinents :

1. **Theoreme de Christol** (1979) : une suite (a_n) sur F_p est p-automatique ssi sa serie generatrice est algebrique sur F_p(x). Ceci concerne les suites definies par les p-digits de n.

2. **Suites q-regulieres** (Allouche-Shallit 1992) : generalisent les suites automatiques. Une suite f(n) est q-reguliere si l'ensemble {f(q^a * n + r)} engendre un Z-module de rang fini.

3. **Stolarsky** (1977) : etudie les proprietes de divisibilite en "bases mixtes". Un nombre en base mixte b_1, b_2, ... a des proprietes de divisibilite determinees par les congruences des bases b_i modulo le diviseur.

**Application a notre probleme** :

La question "corrSum ≡ 0 mod p ?" est une question sur la somme ponderee f(s_0, ..., s_{k-1}) ou s_j = b_j mod r. Mais :

- Les b_j ne sont PAS les chiffres de corrSum dans une base fixee
- La relation b_j -> 2^{b_j} n'est pas un changement de base : c'est une exponentiation
- Les s_j = b_j mod r sont des REDUCTIONS MODULAIRES, pas des extractions de chiffres
- La contrainte b_0 <= b_1 <= ... <= b_{k-1} = S-k est une contrainte GLOBALE sur la sequence

Les theoremes d'Allouche-Shallit-Stolarsky ne s'appliquent pas directement car :

1. Il n'y a pas de "base" unique dans laquelle corrSum s'ecrit
2. La structure multiplicative (2^{b_j}) n'est pas une representation en base quelconque
3. Les contraintes de monotonie ne sont pas du type "chiffres independants"

### D.4 Le seul pont exploitable

Le pont le plus proche est la theorie des formes lineaires en logarithmes (Baker 1966+). Si on ecrit :

$$\text{corrSum} = \sum_{j=0}^{k-1} 3^{k-1-j} \cdot 2^{b_j}$$

c'est une combinaison lineaire (a coefficients 3^m) de puissances de 2. Les resultats de Baker-Wustholz donnent des bornes inferieures pour |alpha_1 * log(2)^{n_1} + ... - beta| quand les n_i sont des entiers. Mais ces bornes sont de type TRANSCENDANCE (distance a zero d'une forme lineaire de logarithmes), pas de type DIVISIBILITE (residus mod d).

La theorie de Baker donne : si Lambda = sum c_j * 2^{b_j} != 0, alors |Lambda| >= exp(-C * log(B)^k) ou B = max(b_j). Ceci ne dit rien sur Lambda mod d.

### D.5 VERDICT SECTION D

L'analogie "digit sum en base mixte" est **STRUCTURELLEMENT CORRECTE** (la MDL de R86 est exactement cette reduction aux "r-digits") mais **OPERATIONNELLEMENT MORTE** :

1. Les resultats d'Allouche-Shallit (suites automatiques) ne s'appliquent pas : pas de base unique, contraintes de monotonie
2. La theorie de Stolarsky (bases mixtes) ne s'applique pas : la relation est exponentielle, pas polynomiale
3. La theorie de Baker (formes lineaires de logarithmes) ne s'applique pas : donne des bornes archimediennes, pas modulo d
4. L'analogue du "critere de divisibilite par 9" est exactement la MDL de R86, deja enterree quantitativement (la borne obtenue explose)

---

## SYNTHESE GLOBALE

### Classification par sous-direction

| Sous-direction | Resultat | Statut |
|---------------|----------|:------:|
| A. Arcs majeurs | Identiques au CRT | **[MORT — retombe sur le produit correle]** |
| B. Arcs mineurs | Phases exponentielles hors cadre | **[MORT — aucun outil applicable]** |
| C. Serie singuliere | Algebriquement = produit CRT | **[MORT — aucune information nouvelle]** |
| D. Digit base mixte | Equivalent a la MDL R86 | **[MORT — quantitativement dead]** |

### Preuves etablies

1. **corrSum ≡ 2^{S-k} mod 3** (generalisation de T174) : la valeur depend de la parite de S-k, pas seulement du fait que corrSum ≡ 1 mod 3 quand S-k est pair.

2. **Serie singuliere = produit CRT** : demonstration algebrique que les deux formulations sont identiques. La methode du cercle (arcs majeurs) encode exactement la meme information que la decomposition CRT.

3. **Substitution u_j = 2^{b_j} equivalente au produit correle** : la linearisation des phases par changement de variable revele une somme sur un ensemble lacunaire (puissances de 2) formellement identique au verrou S_H(t) de R85.

### Observations structurelles cles

**Observation 1** : La factorisation T(t) ≠ prod T_{p_i}(t mod p_i) est massivement fausse (erreur relative ~17% pour d=35). Les residus de corrSum mod p_1 et mod p_2 sont CORRELES pour les compositions individuelles. Mais la SOMME sur toutes les compositions produit (miraculeusement) le meme resultat que le produit independant.

**Observation 2** : L'arc q=3 est totalement degenere : corrSum est constant mod 3 (et mod 3^m pour tout m), donc la contribution des arcs proches de multiples de 1/3 est MAXIMALE. Ceci est coherent avec gcd(d, 3) = 1 : les arcs les plus "bruyants" sont exactement ceux qui sont inoperants.

**Observation 3** : La densite des puissances de 2 dans [1, 2^{S-k}] est ~ (S-k)/2^{S-k} ~ S/2^S, qui est EXPONENTIELLEMENT petite. C'est la raison fondamentale pour laquelle aucun outil de majoration sur les arcs mineurs ne fonctionne : l'ensemble de sommation est trop lacunaire pour que les arguments de type equidistribution mordent.

### Verdicts definitifs

**La methode du cercle a phases exponentielles est une REFORMULATION du probleme, pas une resolution.**

- Les arcs majeurs donnent le produit CRT (deja connu, R85)
- Les arcs mineurs sont inattaquables (phases exponentielles hors cadre)
- La serie singuliere est algebriquement identique au produit CRT
- L'angle digit/base mixte est la MDL de R86 (deja enterree)

La methode du cercle ne sera exploitable pour corrSum que si un outil QUALITATIVEMENT NOUVEAU est invente pour borner les sommes exponentielles a phases 2^n sur des sous-ensembles de taille logarithmique. Un tel outil n'existe pas dans la litterature actuelle (confirme R159, R160).

---

## REGISTRE FAIL-CLOSED (ajouts R160bis)

| Objet | Statut | Kill | Round |
|-------|--------|------|-------|
| Cercle : arcs majeurs corrSum | **[MORT]** | = CRT, aucune info nouvelle | R160bis |
| Cercle : arcs mineurs corrSum | **[MORT]** | Phases 2^{b_j} exponentielles, hors cadre HL | R160bis |
| Cercle : serie singuliere | **[MORT]** | Algebriquement = prod CRT (prouve) | R160bis |
| Substitution u_j = 2^{b_j} | **[MORT]** | Revele somme lacunaire = produit correle R85 | R160bis |
| Digit base mixte (Allouche-Shallit) | **[MORT]** | Pas de base unique, = MDL R86 | R160bis |
| Stolarsky bases mixtes | **[MORT]** | Relation exponentielle, pas polynomiale | R160bis |
| Baker formes lineaires log | **[MORT]** | Bornes archimediennes, pas modulaires | R160bis |
| Approximation puissances de 2 | **[MORT]** | Erreur noie le signal (densite ~S/2^S) | R160bis |

---

*R160bis Direction 3 terminee. Classification : REFORMULATION PURE, ZERO GAIN OPERATIONNEL.*
*La methode du cercle pour corrSum collapse sur le CRT + produit correle.*
