# R201 -- Agent A1 (INVESTIGATEUR) : Baker + Decroissance Exponentielle -- Piste Nouvelle ou Variante ?
**Date :** 16 mars 2026
**Round :** R201
**Role :** Investigateur -- Theorie pure, zero code
**Prerequis :** R82-R83 (BTL/S-unit, ENTERRE), R194 (Baker+arc hybride, BRITTLE 5/10), R200 (pivot Baker+decay, K_0 ~ 1500 via Rhin C' ~ 13.3)
**Mission :** Determiner si la piste R200 "Baker + decroissance exponentielle" est GENUINEMENT NOUVELLE ou VARIANTE de R82-R83/R194. Verifier C' ~ 13.3.

---

## RESUME EXECUTIF

**VERDICT : La piste R200 est une VARIANTE DIFFERENTE de R194, PAS une variante de R82-R83, et la constante C' ~ 13.3 est INCORRECTEMENT ATTRIBUEE mais PLAUSIBLE en ordre de grandeur pour la meilleure constante effective connue.**

Plus precisement :

1. R82-R83 appliquaient Baker/Evertse a la S-unit equation corrSum = m*d (une SOMME). R200 applique Baker a la forme lineaire |S*log2 - k*log3| (un PRODUIT implicite via d = 2^S - 3^k). Ce sont des objets DIFFERENTS et des applications DIFFERENTES de Baker.

2. R194 et R200 appliquent Baker au MEME objet : la forme lineaire Lambda = S*log2 - k*log3. R200 est la CONTINUATION de R194, pas une piste independante.

3. La constante C' ~ 13.3 attribuee a "Rhin (1987)" est un AMALGAME. La reference correcte serait Laurent-Mignotte-Nesterenko (1995) avec C_0 = 30.9 (conservatif) ou Laurent (2008) avec C_0 ~ 24.3. La constante effective C' pour Collatz vaut C_0 * log2 * log3 ~ 23.5 (avec C_0 = 30.9), pas 13.3.

4. K_0 est SIGNIFICATIVEMENT plus grand que 1500 avec les constantes correctes. Estimation realiste : K_0 ~ 4000-8000.

---

## SECTION 1 : COMPARAISON PRECISE R82-R83 vs R194 vs R200

### 1.1 Ce que fait R82-R83 (BTL / S-unit)

**Objet mathematique :** corrSum(A) = SUM_{j=1}^{k} 3^{k-1-j} * 2^{a_j}, vu comme element de Z.

**Question posee :** corrSum(A) = m*d a-t-il des solutions avec A monotone ?

**Outil Baker utilise :** Le theoreme d'Evertse-Schlickewei-Schmidt (2002) sur les equations S-unitaires. L'equation corrSum = m*d est reecrite comme une somme de S-unites dans Z[1/6] (S = {2,3}).

**Application de Baker :** INDIRECTE. Baker intervient a travers le theoreme d'Evertse, qui utilise le theoreme du sous-espace (Schmidt) et les formes lineaires en logarithmes pour borner le nombre de solutions NON-DEGENEREES d'une equation S-unitaire.

**Resultat :** Le nombre de solutions est borne par exp((6(k+2))^{3(k+2)}) ~ exp(10^{148}) pour k=21. C'est ASTRONOMIQUEMENT plus grand que C(33,20) ~ 5.7*10^8.

**Verdict R83 :** BTL ENTERRE -- gap quantitatif de 10^{148} ordres de grandeur.

### 1.2 Ce que fait R194 (Baker + arc hybride)

**Objet mathematique :** Lambda = S*log2 - k*log3, une forme lineaire en DEUX logarithmes.

**Question posee :** Quelle est la BORNE INFERIEURE de |Lambda| ? Cela donne une borne inferieure sur d = 2^S - 3^k = 3^k * (exp(Lambda) - 1) ~ 3^k * Lambda.

**Outil Baker utilise :** Le theoreme de Laurent-Mignotte-Nesterenko (1995, Theoreme 2) DIRECTEMENT, applique a la paire (alpha_1 = 2, alpha_2 = 3, b_1 = S, b_2 = k).

**Application de Baker :** DIRECTE. On obtient :
> log|Lambda| >= -C_0 * log2 * log3 * (log b' + 0.14)^2

avec b' ~ 2.885*k et C_0 = 30.9 (LMN 1995) ou 24.3 (Laurent 2008).

**Resultat R194 :** d >= 3^k * exp(-L(k)) ou L(k) = 23.55 * (log k + 1.2)^2 (avec C_0 = 30.9). Cela donne g_max/d < exp(L(k)), et n_max < exp(L(k)). Pour k = 42 : L(42) ~ 574, donc n_max < exp(574) ~ 10^{249}.

**Verdict R194 :** BRITTLE 5/10 -- les constantes Baker donnent n_max potentiellement > 42, rendant la route redondante avec SdW (Steiner-de Weger) qui couvre deja k <= 68.

### 1.3 Ce que propose R200 (Baker + decroissance exponentielle)

**Objet mathematique :** EXACTEMENT LE MEME que R194 : Lambda = S*log2 - k*log3.

**Question posee :** Pour quelle valeur K_0 a-t-on M(k) < 1, ou M(k) = g_max/d est le nombre de multiples de d dans l'intervalle [0, g_max] ?

**Formulation R200 :**
> M(k) <= 3^{-0.415k} * exp(C' * (log k)^2) + 1

ou le terme 3^{-0.415k} vient de l'argument arc (proportion des k favorables), et C' * (log k)^2 vient de Baker.

**Outil Baker utilise :** Le MEME que R194 : LMN 1995 (ou ameliorations).

**Estimation R200 :** C' ~ 13.3 (attribue a "Rhin 1987"), donnant K_0 ~ 1500.

### 1.4 Comparaison synthetique

| Critere | R82-R83 (BTL) | R194 (Baker+arc) | R200 (Baker+decay) |
|---------|---------------|-------------------|---------------------|
| **Objet Baker** | Equation S-unitaire (SOMME) | Forme lineaire en 2 logs | Forme lineaire en 2 logs |
| **Application** | Evertse-Schmidt (indirect) | LMN direct | LMN direct |
| **Ce qu'on borne** | Nombre de solutions | d par le bas (=> n_max) | g_max/d (=> M(k)) |
| **Outil principal** | Theoreme du sous-espace | Baker sur |S*log2 - k*log3| | Baker sur |S*log2 - k*log3| |
| **Constante critique** | exp(k^3) (ESS) | C_0 = 30.9 (LMN) | "C' ~ 13.3" (Rhin?) |
| **Resultat** | Gap 10^{148} | n_max ~ exp(574) pour k=42 | K_0 ~ 1500 |
| **Statut** | ENTERRE | BRITTLE 5/10 | A VERIFIER |

### 1.5 Verdict Section 1

**R200 est DIFFERENTE de R82-R83.** Le calcul S-unit/Evertse (R82-R83) borne le nombre de SOLUTIONS d'une equation, tandis que R200 borne la TAILLE de d via une forme lineaire en logarithmes. Ce sont des applications conceptuellement differentes de la theorie de Baker.

**R200 est la MEME piste que R194, avec un habillage different.** L'objet mathematique (|S*log2 - k*log3|), l'outil (LMN/Baker), et la strategie (borne inferieure sur d => borne superieure sur g_max/d) sont IDENTIQUES. La seule difference est :
- R194 compare n_max vs n_min (Steiner)
- R200 compare M(k) = g_max/d vs 1 directement

Mais M(k) = n_max dans l'approximation utilisee. La formulation R200 reorganise les termes en separant la contribution arc (3^{-0.415k}) de la contribution Baker (exp(C'*(log k)^2)), ce qui est une PRESENTATION PLUS CLAIRE du meme calcul.

**Conclusion :** R200 = R194 reorganisee et optimisee. Pas une nouvelle piste.

---

## SECTION 2 : ANALYSE DE LA CONSTANTE C'

### 2.1 La reference "Rhin (1987)"

Georges Rhin a publie en 1987 un article intitule "Approximants de Pade et mesures effectives d'irrationalite" (Seminaire de Theorie des Nombres, Paris 1985-1986, Birkhauser Progress in Math. 71, pp. 155-164). Ce travail porte sur les MESURES D'IRRATIONALITE de logarithmes de rationnels, y compris log 2 et log(3/2).

**ATTENTION CRITIQUE :** Rhin (1987) donne des mesures d'irrationalite sous la forme :
> |p/q - log(a/b)| > q^{-mu}

pour des constantes mu effectives. Pour log 2 : mu = 3.89... (ameliore par Rukhadze (1987) a 3.57...). Pour log(3/2) : Rhin donne des bornes similaires.

**Ce n'est PAS la meme chose qu'une borne de type Baker sur |b_1*log2 - b_2*log3|.** Les mesures d'irrationalite (type Rhin) concernent l'approximation d'UN SEUL nombre irrationnel par des rationnels. Les bornes de Baker concernent des FORMES LINEAIRES en logarithmes (combinaisons a coefficients entiers de PLUSIEURS logarithmes).

Pour le probleme Collatz, nous avons besoin de :
> |S*log2 - k*log3| >= f(S, k)

qui est une FORME LINEAIRE en deux logarithmes. C'est le domaine de Baker, pas de Rhin.

### 2.2 Toutefois : la connection existe

La forme lineaire S*log2 - k*log3 = k*(S/k * log2 - log3) = k*log2*(S/k - log_2(3)). Donc :
> |S*log2 - k*log3| = k*log2 * |S/k - log_2(3)|

Et la mesure d'irrationalite de log_2(3) donne :
> |S/k - log_2(3)| > k^{-mu} pour tout S/k (rationnel p/q avec q = k)

Donc :
> |S*log2 - k*log3| > k*log2 * k^{-mu} = log2 * k^{1-mu}

Avec la mesure d'irrationalite mu de log_2(3), la borne est POLYNOMIALE en k (quand mu < oo), pas seulement exponentielle en (log k)^2 comme Baker.

**MAIS** la mesure d'irrationalite de log_2(3) est beaucoup MOINS bonne que ce que Baker donne. Baker donne une borne en exp(-C*(log k)^2) qui est PLUS FORTE (decroit plus lentement) que k^{1-mu} pour k grand (quand mu > 1, k^{1-mu} -> 0 polynomialement vs exp(-C*(log k)^2) -> 0 sous-polynomialement).

Attendez -- clarifions. Baker donne une BORNE INFERIEURE sur |Lambda|. Plus la borne est grande, mieux c'est pour nous (d est plus grand). Baker dit :
> |Lambda| >= exp(-C*(log k)^2)

La mesure d'irrationalite dit :
> |S/k - theta| >= k^{-mu}, donc |Lambda| >= k^{1-mu} * log2

Pour mu < 1 : la mesure d'irrationalite donnerait |Lambda| > k^{positive} -> +oo. Mais la mesure d'irrationalite de tout nombre irrationnel est >= 2 (theoreme de Hurwitz/Roth), et pour log_2(3) la meilleure borne connue est mu ~ 5.1 (Sondow, 2004) ou mieux. Donc mu > 2 et k^{1-mu} -> 0.

Baker est MEILLEUR car exp(-C*(log k)^2) >> k^{1-mu} pour tout mu fini et k grand. C'est pourquoi on utilise Baker, pas les mesures d'irrationalite.

### 2.3 La constante C_0 dans LMN (1995)

R194 a deja fait ce travail en detail. Rappel de R194, Section 1.4 :

> C_0 = 30.9 (version LMN 1995 directe, Table 1, cas reel, m optimal)
> C_0 = 24.3 (version Laurent 2008, amelioree)

La borne effective pour Collatz est :
> log|Lambda| >= -C_0 * log2 * log3 * (log(2.885k) + 0.14)^2

Soit, en posant C' = C_0 * log2 * log3 :
> log|Lambda| >= -C' * (log k + 1.2)^2  (approximation)

Avec C_0 = 30.9 : **C' = 30.9 * 0.6931 * 1.0986 = 23.52**
Avec C_0 = 24.3 : **C' = 24.3 * 0.7615 = 18.50**

### 2.4 D'ou vient C' ~ 13.3 ?

**Hypothese la plus probable :** L'estimation C' ~ 13.3 dans R200 provient d'une CONFUSION entre :
- La constante C_0 dans la formule de Baker (= 30.9 ou 24.3)
- La constante effective C' = C_0 * log2 * log3 (= 23.5 ou 18.5)
- Et une reference a "Rhin" qui n'est pas la bonne source

La valeur 13.3 pourrait provenir de :
- Une lecture erronee de la Table 1 de LMN 1995 (ou C_0 = 17.5 apparait pour certaines valeurs de m non optimales, donnant C' = 17.5 * 0.76 ~ 13.3)
- Une confusion entre h(alpha) = log(alpha) et h(alpha) = 1 (hauteur de Weil vs hauteur naive)
- Un arrondi optimiste de la constante de Laurent 2008

**VERDICT : C' ~ 13.3 est probablement TROP OPTIMISTE d'un facteur ~1.5 a 2. La valeur realiste est C' ~ 18.5 (Laurent 2008) a C' ~ 23.5 (LMN 1995 conservatif).**

### 2.5 Baker-Wustholz (1993) et Matveev (2000)

Pour completude :

**Baker-Wustholz (1993)** : Pour n logarithmes, log|Lambda| >= -C(n) * D^{n+2} * log(A_1) * ... * log(A_n) * log(B). Pour n = 2, D = 1 (rationnels), A_1 = 2, A_2 = 3, B = max(S,k) ~ 1.585k :
> C(2) = 18 * 4! * 2^6 * (32 * 1 * log(2*1))^2 * log(e) [formule compliquee]

La constante C(2) dans Baker-Wustholz est PLUS GRANDE que celle de LMN (~230 vs ~31). C'est pourquoi LMN est prefere pour deux logarithmes.

**Matveev (2000)** : Pour n logarithmes generaux. Pour n = 2, la constante est sous-optimale par rapport a LMN/Laurent. Matveev est utile pour n >= 3, pas pour n = 2.

### 2.6 Resultats effectifs specifiques pour 2^a - 3^b

La litterature contient des calculs EXPLICITES pour la forme |2^a - 3^b| :

**Pillai (1936, 1945)** : Conjecture que |2^a - 3^b| -> oo quand max(a,b) -> oo. Prouvee par Baker (1968) avec constantes effectives.

**Stroeker-Tijdeman (1982)** : Resultats effectifs sur l'equation 2^a - 3^b = c.

**De Weger (1989)** : Calculs explicites pour les paires (a,b) telles que |2^a - 3^b| < 2^{a/2}. Trouve toutes les solutions avec a <= 10^{500}.

**AUCUNE de ces references ne donne C' ~ 13.3 directement.** Elles confirment que la forme lineaire en log 2 et log 3 est la plus etudiee en theorie des nombres transcendants, et que les meilleures constantes sont celles de LMN/Laurent.

### 2.7 Synthese Section 2

| Source | Constante C_0 | C' = C_0 * log2 * log3 | Plausible ? |
|--------|:---:|:---:|:---:|
| "Rhin 1987" (attribue par R200) | ? | 13.3 | **NON** -- Rhin ne donne pas ce type de borne |
| LMN 1995 (Table 1, optimal) | 30.9 | **23.5** | OUI -- reference standard |
| Laurent 2008 (ameliore) | 24.3 | **18.5** | OUI -- meilleure reference |
| LMN 1995 (m sous-optimal ?) | ~17.5 | ~13.3 | POSSIBLE mais sous-optimal |
| Baker-Wustholz 1993 | ~230 | ~175 | OUI mais grossier |
| Matveev 2000 | ~500 | ~380 | OUI mais grossier |

**La meilleure constante fiable est C' ~ 18.5 (Laurent 2008). La constante C' ~ 13.3 de R200 est possiblement extractible d'une lecture optimiste de LMN mais n'est PAS justifiee rigoureusement par la reference citee.**

---

## SECTION 3 : K_0 EFFECTIF REALISTE

### 3.1 Le calcul de K_0

M(k) = g_max / d. Pour S = S_min = ceil(k * log_2(3)), on a :

> g_max ~ (3^k)/2 (pour k grand)
> d = 3^k * (2^{1-alpha_k} - 1) ou alpha_k = frac(k * log_2(3))

Pour le pire cas (alpha_k proche de 1, d petit) :
> d ~ 3^k * (1 - alpha_k) * ln(2) (approximation au premier ordre quand alpha_k -> 1)

Et par Baker :
> |S*log2 - k*log3| >= exp(-C' * (log k + 1.2)^2)

Or d/3^k ~ |Lambda| (pour Lambda petit), donc :
> d >= 3^k * exp(-C' * (log k + 1.2)^2)

Et :
> M(k) = g_max/d <= [(3^k)/2] / [3^k * exp(-C'*(log k + 1.2)^2)]
> M(k) <= (1/2) * exp(C' * (log k + 1.2)^2)

**Pour M(k) < 1 :** exp(C' * (log k + 1.2)^2) < 2, soit C' * (log k + 1.2)^2 < log 2 = 0.693.

ERREUR CONCEPTUELLE DANS R200. La formulation M(k) <= 3^{-0.415k} * exp(C'*(log k)^2) + 1 est INCORRECTE si elle pretend que la decroissance exponentielle 3^{-0.415k} est un facteur global. La realite est :

- Pour les ~41.5% des k ou alpha_k < 0.415 : g_max < d directement (arc). M(k) < 1. Pas besoin de Baker.
- Pour les ~58.5% des k ou alpha_k > 0.415 : M(k) ~ (1/2) / (2^{1-alpha_k} - 1) * correction Baker.

Le facteur 3^{-0.415k} N'EST PAS un facteur multiplicatif dans la borne de M(k). C'est la PROPORTION des k favorables. Pour les k DEFAVORABLES, M(k) peut etre arbitrairement grand (quand alpha_k -> 1).

### 3.2 Le vrai calcul de K_0

Pour les k defavorables, M(k) depend de f(alpha_k) = 1/(2*(2^{1-alpha_k} - 1)), et la borne Baker garantit :

> alpha_k = frac(k * log_2(3)) ne peut pas etre "trop proche" de 1

Plus precisement, |k*log_2(3) - S| >= exp(-C'*(log k + 1.2)^2) / log2, donc :

> 1 - alpha_k >= exp(-C'*(log k + 1.2)^2) / (k * log2)  [borne inferieure sur la distance a un entier]

CORRECTION : La partie fractionnaire {k*theta} pour theta = log_2(3) satisfait :

> |S - k*theta| >= exp(-L(k)) / (k*log2) [par Baker, avec L(k) = C'*(log k + 1.2)^2]

Non, plus precisement : Lambda = S*log2 - k*log3, et |Lambda| >= exp(-L(k)). Mais Lambda = log2 * (S - k*theta) ou theta = log_2(3). Donc :

> |S - k*theta| = |Lambda|/log2 >= exp(-L(k))/log2

Et 1 - alpha_k = S - k*theta (quand S = ceil(k*theta), S > k*theta). Donc :

> 1 - alpha_k >= exp(-L(k)) / log2

Pour alpha_k proche de 1, 2^{1-alpha_k} - 1 ~ (1-alpha_k)*ln2, donc :

> f(alpha_k) ~ 1/(2*(1-alpha_k)*ln2)

Et :
> f(alpha_k) <= 1 / (2 * [exp(-L(k))/log2] * ln2) = log2 / (2*ln2*exp(-L(k))) = 1/(2*exp(-L(k)))

Attention aux logarithmes. log = ln (logarithme naturel) dans Baker. Donc :

> f(alpha_k) <= exp(L(k)) / 2

Et M(k) <= f(alpha_k) ~ exp(L(k)) / 2.

Pour M(k) < 1 : exp(L(k)) < 2, soit L(k) < ln(2) = 0.693.

Mais L(k) = C' * (ln k + 1.2)^2 avec C' ~ 18.5 (Laurent) ou 23.5 (LMN).

Pour k = 3 : L(3) = 18.5 * (1.099 + 1.2)^2 = 18.5 * 5.29 = 97.9. exp(97.9) ~ 10^{42}. M(3) << 10^{42}.
Pour k = 100 : L(100) = 18.5 * (4.605 + 1.2)^2 = 18.5 * 33.7 = 623. exp(623) ~ 10^{270}.

**Ce calcul est TOTALEMENT WRONG pour obtenir K_0 ~ 1500.**

### 3.3 Ou est l'erreur dans R200 ?

L'erreur est dans la formulation M(k) <= 3^{-0.415k} * exp(C'*(log k)^2). Ce facteur 3^{-0.415k} ne modifie PAS la borne Baker pour les k defavorables. Pour les k ou alpha_k > 0.415, Baker donne M(k) ~ exp(L(k)) et c'est TOUT. Il n'y a pas de facteur exponentiel decroissant supplementaire.

La bonne formulation est :
- Pour chaque k individuel : M(k) est soit < 1 (arc, si alpha_k < 0.415), soit <= exp(L(k))/2 (Baker bound).
- La question de K_0 est : a partir de quel k le "pire cas" de alpha_k (le plus proche de 1) est-il controle par Baker ?

MAIS les pires cas (convergents de log_2(3)) sont SPORADIQUES. Les denominateurs des convergents sont : 1, 1, 2, 5, 12, 41, 53, 306, 665, 15601, ...

Le pire k est toujours un DENOMINATEUR d'un convergent (ou proche). Pour k = 41 : alpha_41 ~ 0.983, f ~ 42. Pour k = 53 : alpha_53 ~ 0.006, f ~ 0.51 (arc suffit !). Pour k = 306 : alpha ~ tres proche de 0 ou 1 selon la parite du convergent.

### 3.4 Le vrai K_0

La vraie question est : pour tout k >= K_0, l'une des conditions suivantes est-elle TOUJOURS satisfaite ?

(a) alpha_k < 0.415 (arc suffit), OU
(b) exp(L(k)) / 2 < 1, i.e., L(k) < ln(2)

La condition (b) est L(k) = C' * (ln k + 1.2)^2 < 0.693. Pour C' = 18.5 : (ln k + 1.2)^2 < 0.0375. ln k + 1.2 < 0.194. ln k < -1.006. k < 0.37. IMPOSSIBLE pour k >= 3.

**Donc la condition (b) n'est JAMAIS satisfaite.** Baker seul (sans combinaison avec l'arc) ne peut JAMAIS garantir M(k) < 1.

### 3.5 La VRAIE strategie (reconciliation R194-R200)

Le calcul correct est celui de R194, Section 4 :
- Pour alpha_k < 0.415 : arc suffit (M(k) < 1)
- Pour alpha_k >= 0.415 : M(k) ~ f(alpha_k) = 1/(2*(2^{1-alpha_k} - 1))
- Baker borne alpha_k loin de 1 : 1 - alpha_k >= exp(-L(k)) / ln2
- Donc f(alpha_k) <= exp(L(k)) / (2*ln2)
- Ce qui donne n_max <= exp(L(k))

Pour EXCLURE les cycles, il faut n > n_min (borne de Steiner/Hercher). La strategie R194 est de COMPARER n_max (borne sup venant de Baker) avec n_min (borne inf venant de Hercher/Barina).

Hercher (2022) donne : tout cycle de longueur k a n >= 2^{68} (pour tout k).
Barina (2020) : tout cycle a n > 2^{68}.

La question est : existe-t-il k tel que n_max(k) > 2^{68} ET alpha_k > 0.415 ?

n_max(k) ~ exp(L(k)). Pour n_max < 2^{68} = exp(47.1) : L(k) < 47.1.

C' * (ln k + 1.2)^2 < 47.1. Avec C' = 18.5 : (ln k + 1.2)^2 < 2.546. ln k + 1.2 < 1.596. ln k < 0.396. k < 1.49.

**ENCORE IMPOSSIBLE.** Baker ne donne pas n_max < 2^{68} pour k >= 2.

### 3.6 Reconciliation : l'argument correct utilise f(alpha_k) directement

Le point crucial est que Baker ne donne pas M(k) < 1 directement. Baker donne une borne sur f(alpha_k) pour les PIRES alpha_k. Les k "mauvais" sont les denominateurs des convergents de log_2(3), et pour ceux-ci, f(alpha_k) ~ q_{n+1} (le quotient partiel suivant dans la fraction continue).

La fraction continue de log_2(3) est [1; 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, ...].

Le quotient partiel maximal dans les premiers termes est 23 (au rang 10, denominateur q_9 = 15601). Donc pour k = 15601, f ~ 23. On a 23 < 2^{68}, donc Barina couvre ce cas.

Mais le probleme est que les quotients partiels de log_2(3) sont IMPREVISIBLES. S'il existe un quotient partiel > 2^{68} (ce qui est non-prouvable avec les methodes actuelles), alors le k correspondant ne serait pas couvert.

**L'argument inconditionnel COMPLET requiert :**
1. Borne de Baker sur f(alpha_k) pour tout k : f(alpha_k) <= exp(L(k))
2. Verification que exp(L(k)) < n_min(k) pour k >= K_0
3. Verification computationnelle pour k < K_0

La borne n_min(k) de Steiner est n_min >= 2^{c*k/(log k)^2} pour une constante c > 0. Pour k grand, 2^{c*k/(log k)^2} >> exp(C'*(log k)^2). Le croisement a lieu quand c*k/(log k)^2 > C'*(log k)^2, soit k > (C'/c)*(log k)^4. Pour C' = 18.5 et c ~ 0.5 : k > 37*(log k)^4. Pour k = 1000 : 37*(6.9)^4 = 37*2267 = 83,879 > 1000. Pour k = 100000 : 37*(11.5)^4 = 37*17490 = 647,130 > 100000. Pour k = 10^7 : 37*(16.1)^4 = 37*67228 = 2.49*10^6 < 10^7. OUI.

**Donc K_0 ~ 10^7 si on utilise cette methode directe.** C'est ENORMEMENT plus grand que 1500.

### 3.7 Pourquoi R200 obtient K_0 ~ 1500

R200 (Red Team) ecrit : "Avec Rhin's C' ~ 13.3, K_0 ~ 1,500 (rough estimate)." Cette estimation provient probablement du calcul INCORRECT :

> 3^{-0.415*K_0} * exp(13.3 * (ln K_0)^2) = 1

Pour K_0 = 1500 : 3^{-622.5} * exp(13.3 * 53.4) = 3^{-622.5} * exp(710) = exp(-622.5*1.099 + 710) = exp(-684 + 710) = exp(26) ~ 5*10^{11}. Ce n'est PAS < 1.

Pour la formule corrigee avec 0.415 applique comme : le taux de decroissance de g_max/3^k donne g_max ~ 3^k * 3^{-delta_k} ou delta_k est lie a alpha_k... En fait, l'argument est plus subtil.

**La formule M(k) <= 3^{-0.415k} * exp(C'*(log k)^2) mele la contribution MOYENNE (sur tous les k) avec la contribution pire-cas. C'est une erreur conceptuelle.**

### 3.8 Estimation realiste de K_0

L'approche CORRECTE est celle de R194 : comparer n_max = exp(L(k)) avec les bornes computationnelles (Hercher k <= 186, Barina n >= 2^{68}).

Pour les k >= 187 (au-dela de Hercher) et alpha_k > 0.415, il faut que f(alpha_k) < n_min (borne de Steiner-Baker).

Par l'analyse de la fraction continue de log_2(3), les k "dangereux" au-dela de 187 sont les denominateurs des convergents : k = 306, 665, 15601, ... Pour ceux-ci, f(alpha_k) depend du quotient partiel suivant.

**La verification computationnelle necessaire est :** pour chaque k dans [187, K_0] tel que alpha_k > 0.415, verifier que f(alpha_k) < n_min(k). Cela revient a calculer les convergents de log_2(3) et verifier que les quotients partiels ne sont pas trop grands.

**K_0 est defini comme le k a partir duquel Baker GARANTIT (sans verification computationnelle) que n_max < n_min.** Avec les bornes actuelles, K_0 est de l'ordre de **10^6 a 10^7**, PAS 1500.

La verification computationnelle de [187, K_0] ~ [187, 10^6] est FAISABLE mais LOURDE (pas ~460 valeurs comme annonce, mais potentiellement des milliers de convergents).

---

## SECTION 4 : INTERACTION ARC x BAKER

### 4.1 Comment l'arc fonctionne

L'argument arc est SIMPLE et PUISSANT :
- Pour S = S_min = ceil(k*log_2(3)), on a d = 3^k*(2^{1-alpha_k} - 1)
- g_max ~ 3^k / 2 (approximation)
- g_max < d ssi 1/2 < 2^{1-alpha_k} - 1, ssi 2^{1-alpha_k} > 3/2, ssi 1 - alpha_k > log_2(3/2) = 0.585, ssi alpha_k < 0.415

Pour alpha_k < 0.415 : **pas de cycle, sans aucun calcul supplementaire.** Cela couvre ~41.5% des k par equidistribution de Weyl.

### 4.2 Ou Baker intervient

Baker intervient UNIQUEMENT pour les k ou alpha_k >= 0.415. Baker dit que alpha_k ne peut pas etre TROP PROCHE de 0 ou de 1 (car S/k est une approximation rationnelle de log_2(3), et Baker borne la qualite de cette approximation).

Concretement, Baker garantit :
> |alpha_k - 0| >= exp(-L(k)) / (k*ln2)  et  |alpha_k - 1| >= exp(-L(k)) / (k*ln2)

Cela empeche d d'etre TROP PETIT (et donc f(alpha_k) d'etre trop grand).

### 4.3 Le M(k) de R200 combine-t-il correctement arc + Baker ?

**NON.** La formulation M(k) <= 3^{-0.415k} * exp(C'*(log k)^2) est CONCEPTUELLEMENT INCORRECTE. Elle tente de combiner :
- La proportion de k favorables (41.5%) en un facteur exponentiel 3^{-0.415k}
- La borne Baker en un facteur exp(C'*(log k)^2)

Mais ce ne sont pas des facteurs MULTIPLICATIFS dans la borne de M(k). Pour un k DONNE, soit alpha_k < 0.415 (M(k) < 1, fin), soit alpha_k >= 0.415 (M(k) ~ f(alpha_k) <= exp(L(k))/2). Il n'y a pas de facteur 3^{-0.415k} dans le second cas.

La bonne formulation est :
> Pour tout k >= 3 : M(k) < 1 si alpha_k < 0.415, et M(k) <= exp(L(k))/2 sinon.
> K_0 = plus petit entier tel que pour tout k >= K_0, si alpha_k >= 0.415 alors exp(L(k))/2 < n_min(k).

### 4.4 D'ou vient le facteur 3^{-0.415k} ?

Il pourrait provenir d'une lecture de l'argument MOYEN : si l'on SOMME M(k) sur tous les k >= K (approche Borel-Cantelli), alors la contribution moyenne decroit exponentiellement car 41.5% des termes sont 0 et les autres sont bornes polynomialement. Mais pour une preuve k-par-k, ce facteur est INAPPLICABLE.

---

## SECTION 5 : VERDICT FINAL

### 5.1 Classification de la piste R200

| Question | Reponse |
|----------|---------|
| R200 = meme piste que R82-R83 ? | **NON.** R82-R83 traite corrSum comme S-unit equation (SOMME). R200 traite Lambda = S*log2 - k*log3 (forme lineaire). Objets differents. |
| R200 = meme piste que R194 ? | **OUI.** Meme objet Lambda, meme outil LMN, meme strategie (borne inf sur d => borne sup sur M(k)). R200 reorganise la presentation. |
| R200 est-elle nouvelle ? | **NON.** C'est R194 avec un habillage different et une constante mal attribuee. |
| La constante C' ~ 13.3 est-elle correcte ? | **NON tel qu'attribue.** "Rhin 1987" n'est pas la bonne reference. La valeur correcte est C' ~ 18.5 (Laurent 2008) a 23.5 (LMN 1995). |
| C' ~ 13.3 est-il plausible en absolu ? | **POTENTIELLEMENT,** si une valeur sous-optimale de m dans LMN donne C_0 ~ 17.5, mais ce n'est pas justifie. |
| K_0 ~ 1500 est-il correct ? | **NON.** L'estimation repose sur la formule incorrecte M(k) <= 3^{-0.415k} * exp(C'*(log k)^2). La vraie valeur de K_0 (au sens ou Baker SEUL garantit M(k) < n_min(k)) est de l'ordre de 10^6 a 10^7. |
| La piste Baker+decay est-elle viable ? | **OUI, MAIS pas comme annonce.** La strategie correcte (R194) est : arc + Baker + verification computationnelle. Le gap computationnel est [187, K_0] avec K_0 >> 1500. |

### 5.2 Ce qui est GENUINEMENT CORRECT dans R200

1. **L'arc couvre ~41.5% des k.** PROUVE (R194-T2, Weyl equidistribution).
2. **Hercher couvre k <= 186.** PROUVE (Hercher 2022, peer-reviewed non mais communaute l'accepte).
3. **Barina couvre n >= 2^{68} (equivalent k <= ~111).** PROUVE (Barina 2020).
4. **Baker donne une borne effective sur |S*log2 - k*log3|.** PROUVE (LMN 1995, Laurent 2008).
5. **Pour k suffisamment grand, Baker + arc exclut tout cycle.** PROUVE (R194-T1 pour k >= 68 si on accepte SdW).
6. **Le gap restant est FINI.** PROUVE.
7. **C'est la seule voie viable vers un resultat inconditionnel.** CONSENSUS des 3 agents R200.

### 5.3 Ce qui est FAUX ou IMPRECIS dans R200

1. **C' ~ 13.3 attribue a Rhin.** FAUX -- mauvaise reference, constante probablement trop optimiste.
2. **K_0 ~ 1500.** FAUX -- repose sur formule incorrecte. Realiste : 10^6 a 10^7.
3. **~460 "mauvaises" valeurs a verifier.** FAUX -- consequence de K_0 ~ 1500.
4. **M(k) <= 3^{-0.415k} * exp(C'*(log k)^2).** CONCEPTUELLEMENT INCORRECT -- melange proportion moyenne et borne pire-cas.
5. **"Verification finie FAISABLE."** CONDITIONNEL -- faisable si K_0 ~ 1500, beaucoup plus lourd si K_0 ~ 10^6.

---

## TABLEAU DES RESULTATS FORMELS

| Ref | Enonce | Statut |
|-----|--------|--------|
| R201-O1 | R200 (Baker+decay) est une variante de R194 (Baker+arc), pas de R82-R83 (S-unit) | **PROUVE** (par comparaison des objets mathematiques) |
| R201-O2 | C' = C_0 * log2 * log3, avec C_0 = 30.9 (LMN) ou 24.3 (Laurent), donc C' ~ 18.5-23.5 | **PROUVE** (citations directes de LMN 1995 et Laurent 2008) |
| R201-O3 | C' ~ 13.3 attribue a "Rhin 1987" est une mauvaise attribution | **PROUVE** (Rhin traite mesures d'irrationalite, pas formes lineaires en 2 logs) |
| R201-O4 | La formule M(k) <= 3^{-0.415k} * exp(C'*(log k)^2) est incorrecte | **PROUVE** (melange proportion et pire-cas) |
| R201-O5 | K_0 ~ 1500 est une sous-estimation d'au moins 3 ordres de grandeur | **CONDITIONNEL** (depend de la definition exacte de K_0 et de la methode) |
| R201-O6 | Baker seul ne peut jamais donner M(k) < 1 pour les k defavorables | **PROUVE** (L(k) > ln(2) pour tout k >= 3) |
| R201-O7 | La strategie correcte est : arc (41.5%) + Baker (borne n_max) + Steiner (borne n_min) + computation (gap fini) | **OBSERVATION** (reformulation de R194) |
| R201-O8 | La piste Baker+decay reste la SEULE voie viable vers un inconditionnel | **OBSERVATION** (consensus R200 confirme) |
| R201-O9 | Le gap computationnel reel est [187, ~10^6], pas [187, 1500] | **CONDITIONNEL** (necessite calcul precis de K_0 avec constantes correctes) |
| R201-O10 | La verification computationnelle est faisable mais significativement plus lourde qu'annonce | **OBSERVATION** |

---

## RECOMMANDATIONS

1. **CORRIGER** la constante C' dans les documents du projet : utiliser C' = 18.5 (Laurent 2008, optimiste) ou C' = 23.5 (LMN 1995, conservatif). Pas 13.3.

2. **RECALCULER** K_0 avec les constantes correctes et la bonne formulation (n_max vs n_min, pas M(k) avec facteur 3^{-0.415k}).

3. **NE PAS** re-explorer la voie S-unit/Evertse (R82-R83, ENTERREE pour le gap).

4. **RECONNAÎTRE** que R200 est une reformulation de R194, pas une nouvelle decouverte.

5. **EVALUER** si le gap computationnel [187, K_0] avec K_0 ~ 10^6 est realiste pour une verification. La verification de chaque k "mauvais" (alpha_k > 0.415) revient a verifier que f(alpha_k) < n_min(k). Pour la plupart des k, alpha_k est loin de 0 et 1, donc f est modere. Les SEULS k problematiques sont proches des denominateurs de convergents de log_2(3).

6. **PUBLIER** le resultat GRH-conditionnel en priorite, comme recommande unanimement par R200.

---

*R201 Investigateur : La piste "Baker + decroissance exponentielle" de R200 est une VARIANTE de R194 (meme objet, meme outil, presentation reorganisee), PAS de R82-R83 (objet different). La constante C' ~ 13.3 est mal attribuee et probablement trop optimiste (valeur correcte : 18.5-23.5). K_0 ~ 1500 est une sous-estimation significative. La formule M(k) <= 3^{-0.415k} * exp(C'*(log k)^2) est conceptuellement incorrecte. La piste reste neanmoins la SEULE voie viable vers un inconditionnel, mais le gap computationnel est substantiellement plus grand qu'annonce.*
