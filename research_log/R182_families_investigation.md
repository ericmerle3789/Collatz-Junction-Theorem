# R182 -- Investigation Racinaire : Familles de k et Denominateur Commun
**Date :** 16 mars 2026
**Methode :** Raisonnement structurel pur (aucun calcul)
**Auditeur :** Claude (mode investigateur racinaire)

---

## QUESTION 1 : Pourquoi regrouper les k en familles facilite-t-il le probleme ?

### 1.1 Periodicite des 3-coefficients modulo p

**ENONCE.** Soit p un premier impair, et r = ord_p(3). Alors pour tout j fixe avec 0 <= j <= k-1, le coefficient 3^{k-1-j} mod p ne depend que de (k-1-j) mod r, donc de k mod r (puisque j est fixe).

**PREUVE (elementaire).**

Soit k' = k + r. Alors :

3^{k'-1-j} = 3^{k+r-1-j} = 3^{k-1-j} * 3^r ≡ 3^{k-1-j} * 1 ≡ 3^{k-1-j} (mod p)

car 3^r ≡ 1 mod p par definition de l'ordre. CQFD.

**Statut : PROUVE** (arithmetique elementaire, Fermat/Lagrange).

**CONSEQUENCE DIRECTE.** Pour p fixe, la fonction

g(v) mod p = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} mod p

a ses coefficients 3^{k-1-j} mod p qui ne dependent que de k mod r. Donc pour une classe de congruence k ≡ a mod r fixee, l'ensemble des coefficients {3^{k-1-j} mod p : j = 0,...,k-1} est determine par la position de j relativement a a.

Plus precisement : quand k ≡ a mod r, les coefficients forment la suite periodique

3^{a-1}, 3^{a-2}, ..., 3^0, 3^{r-1}, 3^{r-2}, ..., 3^0, ...

repetee floor(k/r) fois avec un prefixe de longueur a. Les coefficients sont les MEMES elements de F_p* (les puissances de 3 mod p), dans le MEME ordre cyclique.

**Statut : DEDUIT** de la preuve ci-dessus.

### 1.2 Pourquoi cela aide-t-il ? L'argument uniforme

**PRINCIPE.** Si l'on peut prouver N_0(p) = 0 (aucun vecteur v tel que g(v) ≡ 0 mod p) pour tous les k dans une classe k ≡ a mod r, alors cette preuve couvre UNE INFINITE de valeurs de k d'un seul coup.

**Combien de classes faut-il couvrir ?** Exactement r = ord_p(3) classes : k ≡ 0, 1, ..., r-1 mod r. Si on reussit pour chaque classe, on a couvert TOUS les k.

**Primes avec petit ordre :**
- ord_5(3) = 4 (car 3^4 = 81 ≡ 1 mod 5) → 4 classes seulement
- ord_7(3) = 6 (car 3^6 = 729 ≡ 1 mod 7) → 6 classes
- ord_11(3) = 5 (car 3^5 = 243 ≡ 1 mod 11) → 5 classes
- ord_13(3) = 3 (car 3^3 = 27 ≡ 1 mod 13) → 3 classes seulement !
- ord_2(3) = pas applicable (p=2 divise 2^S, pas d)

**Statut : DEDUIT.** Le nombre de classes est fini et petit pour les petits primes.

### 1.3 Descente des POURQUOI : est-ce reellement plus facile ?

**QUESTION CRUCIALE.** Le regroupement par familles reduit-il VRAIMENT la difficulte, ou est-ce une illusion ?

**Argument pour (cas optimiste) :** Dans chaque famille k ≡ a mod r, les coefficients mod p sont les memes. Cela signifie que la structure algebrique de g(v) mod p est "stationnaire" : seul le nombre de termes (k) change, pas leur nature. On pourrait esperer un argument par induction sur k au sein d'une famille : si N_0(p) = 0 pour k = a, peut-on montrer que c'est encore vrai pour k = a + r ?

**Argument contre (cas pessimiste) :** Le probleme POUR CHAQUE k dans une famille est EXACTEMENT aussi dur que le probleme original. Fixer k mod r ne simplifie pas la structure du simplexe monotone B_0 <= ... <= B_{k-1}. Le nombre de vecteurs C(S,k) change avec k, le module d(k) change avec k. La periodicite des coefficients est une regularite LOCALE (dans F_p) qui ne touche pas la difficulte GLOBALE (structure du simplexe, taille de d).

**ANALOGIE.** Imaginez un coffre-fort a k serrures. Savoir que les serrures se repetent avec un motif de periode r ne vous aide que si vous pouvez exploiter ce motif pour crocheter une serrure a partir d'une autre deja crochetee. Si chaque serrure est independante, le motif est decoratif.

**VERDICT HONNETE : CONJECTURE FAIBLE.** Le regroupement par familles est une structure reelle (PROUVE en 1.1), mais son utilite pour prouver N_0 = 0 est NON DEMONTREE. L'argument uniforme fonctionne en theorie mais necessite un mecanisme de preuve au sein de chaque famille. Ce mecanisme n'est pas identifie.

**Le vrai probleme sous-jacent :** Pour que le regroupement soit utile, il faut que la preuve pour un k PETIT dans la famille (disons k = a) se TRANSFERE a tous les k = a + mr pour m >= 1. Cela necessiterait un argument INDUCTIF ou ASYMPTOTIQUE au sein de la famille. L'argument inductif demanderait de relier g(v) pour k = a+r a g(v') pour k = a, ce qui revient a comprendre l'effet d'ajouter r termes supplementaires a la somme. L'argument asymptotique demanderait que C(S,k)/p → ∞ au sein de la famille, ce qui EXPLOSE le module d en meme temps.

**Statut : QUESTION OUVERTE.**

---

## QUESTION 2 : Existe-t-il un denominateur commun a TOUS les k ?

### 2.1 L'irrationalite de log_2(3) comme fait universel

**FAIT.** S = ceil(k * log_2(3)), et log_2(3) est irrationnel (transcendant meme, par Gelfond-Schneider). Donc S/k → log_2(3) sans jamais l'atteindre.

**Consequence pour d(k) = 2^S - 3^k :** Puisque S est le plus petit entier tel que 2^S > 3^k, on a :

0 < d(k) = 2^S - 3^k < 2 * 3^k * (2^{frac(k*log_2(3))} - 1)

ou frac(x) = x - floor(x). La partie fractionnaire {k * log_2(3)} determine la "taille relative" de d par rapport a 3^k.

**Pourquoi c'est universel :** Pour TOUT k, le meme nombre irrationnel log_2(3) gouverne la taille de d. Les k pour lesquels d est petit sont ceux ou k * log_2(3) est proche d'un entier -- ce sont les denominateurs des convergents de la fraction continue de log_2(3). Ces k sont RARES et ESPACES (propriete des fractions continues : les denominateurs croissent exponentiellement).

**Mais est-ce exploitable ?** L'irrationalite de log_2(3) est deja utilisee implicitement dans le Junction Theorem (Bloc 1 : C/d → 0 car log_2(3) irrationnel force d a croitre). Pour les k FINIS (Bloc 2-3), l'irrationalite ne donne rien directement -- elle ne dit pas que d a une structure arithmetique particuliere.

**Statut : FAIT PROUVE (transcendance de log_2(3)), mais UTILITE POUR N_0 = 0 : QUESTION OUVERTE.**

### 2.2 La monotonie comme contrainte universelle

**FAIT.** Pour TOUT k, le vecteur v = (B_0, ..., B_{k-1}) satisfait B_0 <= B_1 <= ... <= B_{k-1}. C'est la MEME contrainte structurelle, independante de k.

**Consequence pour g(v) :** La monotonie force une ANTI-CORRELATION entre les coefficients ternaires 3^{k-1-j} (decroissants en j) et les exposants binaires B_j (croissants en j). Les gros coefficients multiplient les petites puissances de 2, et vice versa.

**Reformulation par inversion :** Posons c_j = 3^{k-1-j} et x_j = 2^{B_j}. Alors g(v) = sum c_j * x_j ou :
- (c_j) est STRICTEMENT decroissante (en j)
- (x_j) est CROISSANTE (au sens large, en j)
- c_j et x_j sont dans des echelles DIFFERENTES (base 3 vs base 2)

C'est un produit scalaire entre un vecteur decroissant et un vecteur croissant. Par l'inegalite de rearrangement de Hardy-Littlewood-Polya, cette somme est MINIMALE parmi toutes les permutations de (x_j).

**THEOREME CANDIDAT 1 (conjecture structurelle).**
*Soit k >= 3. Parmi toutes les affectations (B_0, ..., B_{k-1}) avec sum B_j = S - k (la contrainte de longueur), la valeur de g(v) = sum 3^{k-1-j} * 2^{B_j} sous la contrainte de monotonie est bornee inferieurement de facon a exclure 0 mod d.*

**CRITIQUE IMMEDIATE :** C'est presque certainement FAUX tel qu'enonce. Le minimum de g(v) sous monotonie depend de k, S, et du module d. L'inegalite de rearrangement dit que le minimum est atteint (parmi les permutations) par la configuration anti-alignee (grande avec petite), qui est EXACTEMENT la configuration monotone. Mais le minimum peut quand meme etre 0 mod d.

Pire : l'inegalite de rearrangement donne min_sigma g(sigma(v)) = g(v_monotone). Cela signifie que la monotonie MINIMISE g, ce qui est DEFAVORABLE pour exclure g ≡ 0 -- c'est la configuration qui RAPPROCHE le plus g de 0 !

**RETOURNEMENT D'INTUITION.** La monotonie n'est pas un bouclier contre les cycles -- elle est le PIRE CAS. Si un cycle existe, la configuration monotone est celle qui rend g le plus petit possible. L'argument de monotonie va dans le MAUVAIS SENS pour exclure les cycles.

**Statut : INSIGHT PROUVEE (la monotonie minimise g par rearrangement), mais de SIGNE CONTRAIRE a ce qu'on voudrait. Ce n'est PAS un outil pour exclure les cycles.**

### 2.3 Le noyau impair h(v)

**FAIT (PROUVE, cf. RESEARCH_MAP R182).** Soit v_2(g(v)) = B_0 (la plus petite valuation du vecteur). Alors h(v) = g(v) / 2^{B_0} est toujours IMPAIR.

**PREUVE (sketch).** g(v) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}. Factoriser 2^{B_0} :

g(v) = 2^{B_0} * sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j - B_0}

Le terme j=0 dans la somme interne est 3^{k-1} * 2^0 = 3^{k-1}, qui est IMPAIR. Tous les autres termes (j >= 1) ont B_j - B_0 >= 0, et si B_1 > B_0, ils sont tous pairs. Si B_1 = B_0, le terme j=1 est 3^{k-2} * 2^0 = 3^{k-2}, impair aussi, mais 3^{k-1} + 3^{k-2} = 3^{k-2}(3+1) = 4 * 3^{k-2}, qui est pair -- donc il faut une analyse plus fine.

En fait, v_2(g(v)) = B_0 n'est vrai que si la multiplicite de B_0 dans le vecteur est impaire (car les termes avec B_j = B_0 contribuent chacun un multiple impair de 2^{B_0}, et la somme de m termes impairs est impaire ssi m est impair). Si la multiplicite est paire, v_2(g(v)) > B_0.

**CORRECTION.** L'enonce v_2(g(v)) = B_0 n'est pas universel -- il depend de la multiplicite. Mais h(v) = g(v) / 2^{v_2(g(v))} est TOUJOURS impair par definition (on divise par la plus grande puissance de 2).

**Invariant universel :** h(v) impair pour tout k, tout v.

**Utilite :** Puisque d = 2^S - 3^k est IMPAIR (2^S est pair, 3^k est impair, donc d est impair), la condition g(v) ≡ 0 mod d est equivalente a :

2^{v_2(g(v))} * h(v) ≡ 0 mod d

Puisque gcd(2^{v_2(g(v))}, d) = 1 (car d est impair), cela equivaut a :

h(v) ≡ 0 mod d

Donc le probleme se REDUIT au noyau impair. On cherche h(v) ≡ 0 mod d avec h(v) impair et d impair.

**THEOREME CANDIDAT 2.** *Pour tout k >= 3 et tout vecteur monotone v, le noyau impair h(v) = g(v) / 2^{v_2(g(v))} satisfait h(v) mod d ≠ 0.*

**Statut : CONJECTURE.** La reduction au noyau impair est PROUVEE (triviale : d impair). Mais la non-annulation de h(v) mod d est exactement le probleme original reformule. C'est une reformulation propre, pas un progres. **PIEGE A de Bohm-Sontacchi : REBRANDING potentiel.**

Neanmoins, l'objet h(v) est plus contraint que g(v) : il est impair, donc il vit dans (Z/dZ)*_impair. Cela pourrait etre exploitable si on trouve des proprietes supplementaires de h(v) -- par exemple, h(v) mod 3 a-t-il un signe force ?

**Question subsidiaire :** h(v) = g(v)/2^{v_2(g(v))}. Que vaut h(v) mod 3 ?

g(v) = 3^{k-1} * 2^{B_0} + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{B_j}

Modulo 3, seul le dernier terme (j = k-1) contribue : 3^0 * 2^{B_{k-1}} = 2^{B_{k-1}}. Tous les autres termes sont ≡ 0 mod 3.

Donc g(v) ≡ 2^{B_{k-1}} mod 3, et h(v) ≡ 2^{B_{k-1}} / 2^{v_2(g(v))} ≡ 2^{B_{k-1} - v_2(g(v))} mod 3.

Puisque ord_3(2) = 2 (car 2^2 = 4 ≡ 1 mod 3), h(v) mod 3 ∈ {1, 2} selon la parite de B_{k-1} - v_2(g(v)).

De meme, d = 2^S - 3^k ≡ 2^S mod 3, donc d mod 3 ∈ {1, 2}.

Pour que h(v) ≡ 0 mod d, il faut en particulier h(v) ≡ 0 mod 3 si 3 | d. Mais h(v) mod 3 ∈ {1, 2}, jamais 0. Donc **si 3 | d, alors automatiquement h(v) ≢ 0 mod d**, et N_0(d) = 0.

**Mais 3 | d = 2^S - 3^k est IMPOSSIBLE** car 3^k ≡ 0 mod 3 et 2^S ≢ 0 mod 3, donc d ≡ 2^S ≢ 0 mod 3.

Donc cette piste est VIDE : 3 ne divise jamais d. On ne peut pas utiliser la contrainte mod 3 sur h(v) pour conclure.

**Statut : IMPASSE.** Le noyau impair est un objet propre mais sa reduction ne comprime pas le probleme.

### 2.4 La structure multiplicative de d(k) -- LA PISTE PRINCIPALE

**OBSERVATION CRUCIALE.** d(k) = 2^{S(k)} - 3^k ou S(k) = ceil(k * log_2(3)).

**Identite de factorisation pour les puissances :** Considerons d(mk) pour m entier :

2^{S(mk)} - 3^{mk} = 2^{S(mk)} - (3^k)^m

Si l'on note S' = S(mk) et a = 3^k, b = 2^{S(k)}, alors on veut factoriser b'^m' - a^m pour certains parametres. Mais S(mk) n'est PAS egal a m * S(k) en general (car ceil est non-lineaire).

**Cas special : quand S(mk) = m * S(k).**

Cela arrive quand frac(mk * log_2(3)) a un comportement compatible. Examinons :

Si S(2k) = 2 * S(k), alors :
d(2k) = 2^{2S(k)} - 3^{2k} = (2^{S(k)})^2 - (3^k)^2 = (2^{S(k)} - 3^k)(2^{S(k)} + 3^k) = d(k) * (2^{S(k)} + 3^k)

Donc **d(k) | d(2k)** dans ce cas. Magnifique !

**Mais S(2k) = 2*S(k) est-il vrai ?**

S(k) = ceil(k * alpha) ou alpha = log_2(3). Donc :
- 2*S(k) = 2*ceil(k*alpha) >= ceil(2*k*alpha) (car 2*ceil(x) >= ceil(2x) toujours)
- S(2k) = ceil(2k*alpha)

Donc 2*S(k) >= S(2k) toujours. Egalite ssi 2*ceil(k*alpha) = ceil(2k*alpha), i.e., ssi frac(k*alpha) <= 1/2.

Quand frac(k*alpha) > 1/2, on a 2*S(k) = S(2k) + 1, et :
2^{2S(k)} - 3^{2k} = 2 * 2^{S(2k)} - 3^{2k} = 2 * (2^{S(2k)} - 3^{2k}) + 2 * 3^{2k} - 3^{2k} + (2^{S(2k)+1} - 2*2^{S(2k)})

Cela se complique. Revenons au cas ou l'egalite tient.

**ANALYSE DETAILLEE.** Soit f(k) = frac(k * alpha).

- Si f(k) <= 1/2 : S(2k) = 2*S(k), et d(k) | d(2k) via l'identite a^2 - b^2.
- Si f(k) > 1/2 : S(2k) = 2*S(k) - 1, et l'identite de factorisation donne :

d(2k) = 2^{2S(k)-1} - 3^{2k} = (2^{2S(k)} - 2*3^{2k}) / 2... non, c'est :

2^{2S(k)-1} - 3^{2k}

tandis que d(k)*(2^{S(k)} + 3^k) = (2^{S(k)} - 3^k)(2^{S(k)} + 3^k) = 2^{2S(k)} - 3^{2k}

Donc d(k)*(2^{S(k)} + 3^k) = 2 * d(2k) + 3^{2k} dans ce cas (car 2^{2S(k)} = 2 * 2^{2S(k)-1}).

Autrement dit : 2 * d(2k) = d(k) * (2^{S(k)} + 3^k) - 3^{2k}... ce n'est plus aussi propre.

**REPRENONS plus prudemment.**

En general :
d(2k) = 2^{S(2k)} - 3^{2k}
d(k) = 2^{S(k)} - 3^k

Et (2^{S(k)})^2 - (3^k)^2 = d(k) * (d(k) + 2 * 3^k) = 2^{2S(k)} - 3^{2k}.

Donc : 2^{2S(k)} - 3^{2k} = d(k) * (d(k) + 2 * 3^k).

Maintenant, 2^{2S(k)} - 3^{2k} = 2^{2S(k) - S(2k)} * 2^{S(2k)} - 3^{2k}.

Posons e = 2S(k) - S(2k) ∈ {0, 1} (comme analyse ci-dessus).

Si e = 0 : 2^{2S(k)} - 3^{2k} = d(2k), donc d(k) * (d(k) + 2*3^k) = d(2k), et **d(k) | d(2k)**. **PROUVE.**

Si e = 1 : 2^{2S(k)} - 3^{2k} = 2 * 2^{S(2k)} - 3^{2k} = 2*d(2k) + 2*3^{2k} - 3^{2k} = 2*d(2k) + 3^{2k}.

Donc d(k) * (d(k) + 2*3^k) = 2*d(2k) + 3^{2k}.

Reformulons : 2*d(2k) = d(k)^2 + 2*3^k*d(k) - 3^{2k} = (d(k) + 3^k)^2 - 2*3^{2k}.

Hmm. Cela donne d(k) | (2*d(2k) + 3^{2k}), i.e., 2*d(2k) ≡ -3^{2k} mod d(k), i.e., 2*d(2k) ≡ -(3^k)^2 mod d(k).

Or 3^k ≡ 2^{S(k)} mod d(k) (par definition de d), donc 3^{2k} ≡ 2^{2S(k)} mod d(k).

Donc 2*d(2k) ≡ -2^{2S(k)} mod d(k). Puisque gcd(2, d(k)) = 1 (d est impair), on a :

d(2k) ≡ -2^{2S(k)-1} mod d(k).

C'est une relation de congruence, pas de divisibilite.

**BILAN de la factorisation d(k) → d(2k) :**

| Condition | Relation | Frequence |
|-----------|----------|-----------|
| f(k) <= 1/2 | d(k) \| d(2k) | ~50% des k |
| f(k) > 1/2 | 2*d(2k) + 3^{2k} ≡ 0 mod d(k) | ~50% des k |

**Statut : PROUVE** (les deux cas). La divisibilite d(k) | d(2k) tient pour environ la moitie des k.

### 2.4.1 La piste de la divisibilite : N_0(d(k)) = 0 implique-t-il N_0(d(2k)) = 0 ?

**ATTENTION, c'est le point CRITIQUE.** L'idee semble seduisante : si d(k) | d(2k), et si N_0(d(k)) = 0 (pas de cycle de longueur k), alors N_0(d(2k)) = 0 aussi ?

**NON, CE N'EST PAS CORRECT.** La raison est subtile mais fondamentale :

N_0(d) est le nombre de vecteurs v DE LONGUEUR k tels que g(v) ≡ 0 mod d. Quand on passe de k a 2k, on change AUSSI la longueur du vecteur. Le simplexe de vecteurs pour k et pour 2k sont des objets DIFFERENTS dans des espaces DIFFERENTS.

Concretement :
- N_0(d(k)) = #{v ∈ S(S(k), k) : g_k(v) ≡ 0 mod d(k)}
- N_0(d(2k)) = #{v ∈ S(S(2k), 2k) : g_{2k}(v) ≡ 0 mod d(2k)}

ou g_k et g_{2k} sont des fonctions DIFFERENTES (k termes vs 2k termes), et les simplexes sont de dimensions differentes.

La divisibilite d(k) | d(2k) ne cree PAS de lien entre les vecteurs de longueur k et ceux de longueur 2k.

**CONTRE-ARGUMENT (tentative de sauvetage).** Peut-on concatener deux vecteurs de longueur k pour obtenir un vecteur de longueur 2k ? Si v = (B_0,...,B_{k-1}) est un vecteur de longueur k, peut-on construire un vecteur w de longueur 2k tel que g_{2k}(w) soit lie a g_k(v) ?

Oui, formellement. Si w = (B_0,...,B_{k-1}, B_0',...,B_{k-1}'), alors :

g_{2k}(w) = sum_{j=0}^{2k-1} 3^{2k-1-j} * 2^{w_j}
           = 3^k * sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} + sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j'}
           = 3^k * g_k(v) + g_k(v')

Donc g_{2k}(w) = 3^k * g_k(v) + g_k(v').

**IDENTITE CLE :** g_{2k}(w) ≡ 3^k * g_k(v) + g_k(v') mod d(2k).

Si d(k) | d(2k), alors mod d(k) :
g_{2k}(w) ≡ 3^k * g_k(v) + g_k(v') mod d(k).

Or 3^k ≡ 2^{S(k)} mod d(k), donc :
g_{2k}(w) ≡ 2^{S(k)} * g_k(v) + g_k(v') mod d(k).

Si g_k(v) ≡ 0 mod d(k) et g_k(v') ≡ 0 mod d(k), alors g_{2k}(w) ≡ 0 mod d(k).

Mais g_{2k}(w) ≡ 0 mod d(2k) est plus fort que mod d(k) (car d(k) | d(2k)).

**CONCLUSION IMPORTANTE :** La divisibilite donne une relation NECESSAIRE, pas suffisante. Si N_0(d(k)) = 0, on sait que pour tout v, g_k(v) ≢ 0 mod d(k). Cela implique que pour tout w concatene, g_{2k}(w) ne peut pas etre simultanement ≡ 0 mod d(k) a moins que la combinaison 3^k * g_k(v) + g_k(v') ne s'annule mod d(k). Mais g_k(v) et g_k(v') sont tous deux NON nuls mod d(k), et la combinaison lineaire PEUT s'annuler.

**De plus**, le vecteur w = concatenation ne satisfait PAS necessairement la contrainte de monotonie pour le probleme de longueur 2k (car B_{k-1} peut etre > B_0').

**Statut : IMPASSE PARTIELLE.** La divisibilite d(k) | d(2k) est un FAIT arithmetique reel, mais l'implication N_0(d(k))=0 => N_0(d(2k))=0 est FAUSSE telle qu'enoncee. La relation entre les deux problemes est plus subtile et passe par la decomposition g_{2k} = 3^k * g_k + g_k'. Cette decomposition est un OUTIL potentiel mais pas une conclusion.

### 2.4.2 Structure multiplicative generalisee

**IDENTITE GENERALE.** Pour tout k1, k2 avec k = k1 + k2 :

g_k(v) = 3^{k2} * g_{k1}(v_1) + g_{k2}(v_2)

ou v_1 = (B_0,...,B_{k1-1}), v_2 = (B_{k1},...,B_{k-1}).

(Attention : v_2 doit etre reindexe comme (C_0,...,C_{k2-1}) avec C_j = B_{k1+j}.)

Cette decomposition est EXACTE et universelle. Elle dit que g_k est une forme bilineaire en (g_{k1}, g_{k2}).

**THEOREME CANDIDAT 3 (decomposition hierarchique).**
*Pour tout k >= 3, g_k(v) = 3^{k2} * g_{k1}(v_1) + g_{k2}(v_2) ou k1 + k2 = k. La condition g_k(v) ≡ 0 mod d(k) impose une contrainte COUPLANT g_{k1}(v_1) et g_{k2}(v_2) modulo d(k).*

**Statut : PROUVE** (identite algebrique triviale). Mais l'utilite pour N_0(d) = 0 reste a etablir.

**Le "chef d'orchestre" :** Chaque k est un musicien jouant sa partition. Le chef d'orchestre serait une regle qui contraint SIMULTANEMENT toutes les partitions. Candidat : la relation

3^k ≡ 2^{S(k)} mod d(k)

qui est la MEME structure pour tout k. Elle dit que dans l'arithmetique de d(k), les roles de 2 et 3 sont LIES. C'est le fait que d(k) est defini comme 2^S - 3^k : le module d ENCODE la tension entre les puissances de 2 et de 3.

Mais c'est tautologique : c'est la DEFINITION de d.

### 2.5 Synthese : le vrai denominateur commun

Apres exploration des cinq candidats, voici le bilan :

| Candidat | Universel ? | Exploitable ? | Statut |
|----------|:-----------:|:-------------:|--------|
| Irrationalite de log_2(3) | OUI | DEJA UTILISE (Bloc 1 asymptotique), PAS pour N_0=0 | EPUISE |
| Monotonie (rearrangement) | OUI | SIGNE CONTRAIRE (minimise g, defavorable) | IMPASSE |
| Noyau impair h(v) | OUI | REBRANDING (reformulation propre sans compression) | MARGINAL |
| Divisibilite d(k)\|d(2k) | PARTIEL (50%) | LIEN FAIBLE entre N_0(k) et N_0(2k) | QUESTION OUVERTE |
| Decomposition g_k = 3^{k2}*g_{k1} + g_{k2} | OUI | IDENTITE EXACTE, utilite non demontrée | QUESTION OUVERTE |

**LE DENOMINATEUR COMMUN LE PLUS PROMETTEUR** est la decomposition hierarchique (candidat 5), combinee avec la divisibilite partielle (candidat 4). Voici pourquoi :

La decomposition g_k = 3^{k2} * g_{k1} + g_{k2} est le SEUL fait qui relie STRUCTURELLEMENT les problemes pour differents k. Si on choisit k1 = r (ord_p(3) pour un premier p), alors 3^{k2} ≡ 3^{k-r} mod p, et on retombe dans la periodicite de la Question 1.

Autrement dit : **les Questions 1 et 2 convergent.** La periodicite des familles (Q1) est un CAS SPECIAL de la decomposition hierarchique (Q2) pour k1 = r.

---

## THEOREME CANDIDAT PRINCIPAL

**THEOREME CANDIDAT 4 (decomposition modulaire hierarchique).**

*Hypotheses :*
- Soit p premier, r = ord_p(3).
- Soit k >= r et k = qr + a avec 0 <= a < r.
- Soit v = (B_0,...,B_{k-1}) un vecteur monotone.
- Decomposer v en q+1 blocs : v_0,...,v_{q-1} de longueur r, et v_q de longueur a.

*Alors :*
g_k(v) ≡ sum_{i=0}^{q-1} 3^{a + (q-1-i)*r} * g_r(v_i) + g_a(v_q) mod p
         ≡ 3^a * sum_{i=0}^{q-1} g_r(v_i) + g_a(v_q) mod p

(car 3^r ≡ 1 mod p, donc 3^{(q-1-i)*r} ≡ 1 mod p)

*Conclusion :*
g_k(v) ≡ 3^a * q * G_r + g_a(v_q) mod p

ou G_r est une "moyenne" des g_r(v_i) -- SAUF que les v_i ne sont PAS independants (la monotonie globale contraint les blocs).

**CRITIQUE :** La factorisation 3^{mr} ≡ 1 mod p simplifie enormement l'expression. Modulo p, g_k se reduit a une somme de q termes identiquement structures (les g_r(v_i)) plus un terme residuel g_a(v_q). C'est la periodicite de la Question 1, vue a travers la decomposition de la Question 2.

**MAIS :** Les v_i sont COUPLES par la monotonie. Le dernier element de v_i doit etre <= le premier element de v_{i+1}. Cela detruit l'independance et rend la somme non factorisable.

**Statut : PROUVE** (l'identite modulaire). **UTILITE : QUESTION OUVERTE** (le couplage par monotonie est le verrou restant).

---

## BILAN ET RECOMMANDATIONS

### Ce qui est genuinement PROUVE dans cette investigation

1. **Periodicite des coefficients :** 3^{k-1-j} mod p est periodique en k de periode ord_p(3). [ELEMENTAIRE]
2. **Inegalite de rearrangement :** La monotonie MINIMISE g(v), ce qui est de signe CONTRAIRE a l'intuition. [ELEMENTAIRE, IMPORTANT]
3. **Divisibilite partielle :** d(k) | d(2k) quand frac(k*log_2(3)) <= 1/2. [ELEMENTAIRE]
4. **Decomposition hierarchique :** g_k = 3^{k2} * g_{k1} + g_{k2} pour toute partition k = k1 + k2. [ALGEBRIQUE, TRIVIAL]
5. **Reduction au noyau impair :** g(v) ≡ 0 mod d ssi h(v) ≡ 0 mod d, avec h impair. [TRIVIAL, d est impair]

### Ce qui reste QUESTION OUVERTE

1. Le regroupement par familles (k mod r) facilite-t-il REELLEMENT la preuve ?
2. La divisibilite d(k) | d(2k) implique-t-elle un lien entre N_0(d(k)) et N_0(d(2k)) ?
3. Le couplage par monotonie dans la decomposition hierarchique peut-il etre traite ?
4. Existe-t-il un invariant universel GENUINEMENT nouveau (pas une reformulation) ?

### Pistes les plus prometteuses (par ordre decroissant)

**Piste A (7/10).** Exploiter la decomposition g_k ≡ 3^a * (sum g_r(v_i)) + g_a(v_q) mod p pour p PETIT (p=13 donne r=3 : g_k est une somme de floor(k/3) termes de meme structure mod 13). La petitesse de r = 3 rend le probleme combinatoire tractable pour chaque bloc.

**Piste B (5/10).** Utiliser le retournement d'intuition (section 2.2) : la monotonie minimise g. Donc si le minimum de g sur le simplexe monotone est > 0 (en tant que rationnel, pas mod d), les cycles sont exclus. Mais ce minimum est probablement tres petit pour grand k, donc cette piste ne donne rien asymptotiquement.

**Piste C (4/10).** La divisibilite d(k)|d(2k) pour 50% des k : construire un arbre de divisibilite ou prouver N_0=0 pour les k racines implique N_0=0 pour les 2k, 4k, etc. MAIS l'implication n'est pas prouvee (section 2.4.1).

### Diagnostic final

Le probleme possede une structure reelle (periodicite, decomposition, divisibilite) qui est PROUVABLE et NON TRIVIALE. Mais cette structure ne se convertit pas (pour l'instant) en une preuve de N_0(d) = 0. Le verrou fondamental reste le meme depuis R73 : l'interface entre la structure additive (g est une SOMME) et la structure multiplicative (les coefficients sont des PUISSANCES) dans un regime ou la taille du probleme (k ~ log p) rend les outils standard circulaires.

Le "chef d'orchestre" -- la regle unique qui empecherait toute dissonance -- n'est pas encore identifie. Les candidats les plus plausibles sont :
1. La TENSION entre les bases 2 et 3, encodee dans l'irrationalite de log_2(3) (mais deja exploitee au maximum dans le Bloc 1).
2. La DECOMPOSITION HIERARCHIQUE g_k = 3^r * G + g_a, qui transforme le probleme en un probleme de SOMMES ALEATOIRES CONTRAINTES modulo p.

**Le fait le plus surprenant de cette investigation** est le retournement du role de la monotonie (section 2.2) : elle AIDE les cycles potentiels (en minimisant g) au lieu de les empecher. C'est un anti-invariant, pas un invariant.

---

*Investigation R182 : 5 faits prouves, 4 questions ouvertes, 1 theoreme candidat principal (decomposition modulaire hierarchique), 1 retournement d'intuition (monotonie = anti-invariant). Aucun denominateur commun universel identifie. Piste A (decomposition mod p petit) recommandee pour R183.*
