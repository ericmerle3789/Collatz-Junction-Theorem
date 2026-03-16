# R183 -- Innovation Mathematique : Le Noyau Impair h(v) et ses Transformations
**Date :** 16 mars 2026
**Mode :** Innovateur mathematique -- raisonnement pur
**Fondement :** R182 T203/O1 : v_2(g(v)) = e_0 = B_0 exactement, donc h(v) = g(v)/2^{B_0} est TOUJOURS impair.

---

## RAPPEL DES OBJETS

g(v) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j},  B_0 <= B_1 <= ... <= B_{k-1}, sum B_j = S - k.

h(v) = g(v)/2^{B_0} = 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{Delta_j}

ou Delta_j = B_j - B_0 >= 1 pour j >= 1 (par aperiodicite : au moins un Delta_j >= 1 ; par monotonie : tous les Delta_j >= 0, et la suite est croissante).

**Correction importante.** Delta_j >= 0 pour tout j >= 1, et Delta_j >= 1 pour au moins un j (sinon v est constant, ce qui donnerait un cycle trivial deja exclu). Mais certains Delta_j PEUVENT etre 0 si B_j = B_0. La cle est que la multiplicite de B_0 dans v est telle que h(v) est impair -- c'est garanti par T203/O1 qui prouve v_2(g(v)) = B_0 exactement.

Posons m_0 = #{j : B_j = B_0} = multiplicite de la valeur minimale. Alors :

h(v) = (sum_{j: B_j = B_0} 3^{k-1-j}) + sum_{j: B_j > B_0} 3^{k-1-j} * 2^{Delta_j}

Le premier groupe est une somme de m_0 puissances de 3 distinctes, donc un entier IMPAIR ssi m_0 est impair (car chaque 3^i est impair, et la somme de m_0 entiers impairs est impaire ssi m_0 est impair). Le second groupe est pair (chaque terme a un facteur 2^{Delta_j} >= 2).

Donc h(v) impair <=> m_0 impair. T203/O1 garantit ceci. [PROUVE]

d = 2^S - 3^k est impair. Condition de cycle : g(v) = n*d, soit h(v) = n*d/2^{B_0}. Puisque d est impair et h est impair, il faut 2^{B_0} | n. Posons n = 2^{B_0} * n', alors h(v) = n' * d avec n' >= 1 entier. [PROUVE]

---

## 1. ARITHMETIQUE MODULAIRE DE h(v)

### 1.1 h(v) mod 2^m -- L'Empreinte Binaire

**h(v) mod 2 = 1.** [PROUVE, par definition]

**h(v) mod 4 :** Regardons h(v) = 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{Delta_j}.

Cas 1 : Tous les Delta_j >= 2 pour j avec B_j > B_0. Alors mod 4, seul le "bloc B_0" contribue :
h(v) ≡ sum_{j: B_j = B_0} 3^{k-1-j} mod 4.

Cas 2 : Il existe j_1 avec Delta_{j_1} = 1 (exactement). Alors le terme 3^{k-1-j_1} * 2 contribue mod 4.

**Sous-cas general.** Posons m_1 = #{j >= 1 : Delta_j = 1}. Les termes avec Delta_j = 1 contribuent 2 * (sum 3^{k-1-j}) mod 4, les termes avec Delta_j >= 2 contribuent 0 mod 4.

h(v) mod 4 = [sum_{j: B_j = B_0} 3^{k-1-j}] + 2*[sum_{j: Delta_j = 1} 3^{k-1-j}] mod 4

Notons sigma_0 = sum_{j: B_j = B_0} 3^{k-1-j} et sigma_1 = sum_{j: Delta_j = 1} 3^{k-1-j}.

sigma_0 mod 4 : chaque 3^i mod 4 alterne entre 3 (i impair) et 1 (i pair). Precise : 3^0 = 1, 3^1 = 3, 3^2 = 1, 3^3 = 3 mod 4. Donc 3^i mod 4 = 1 si i pair, 3 si i impair.

sigma_0 est la somme de m_0 termes, chacun dans {1, 3} mod 4. Si on note p_0 = #{j: B_j = B_0, (k-1-j) pair} et q_0 = m_0 - p_0, alors :
sigma_0 ≡ p_0 + 3*q_0 = p_0 + 3*(m_0 - p_0) = 3*m_0 - 2*p_0 mod 4.

Puisque m_0 est impair, 3*m_0 mod 4 ∈ {3, 1} selon m_0 mod 4. Et 2*p_0 mod 4 ∈ {0, 2}.

**Observation :** h(v) mod 4 depend de la GEOMETRIE interne du vecteur v (positions des repetitions de B_0, positions des sauts de 1). Ce n'est pas un invariant universel -- il varie avec v.

**STATUT : DEDUIT.** h(v) mod 4 n'est PAS un invariant de k ; il depend de v. Pas d'obstruction modulaire en puissance de 2. [IMPASSE LOCALE]

### 1.2 h(v) mod 3 -- Confirmation et approfondissement

g(v) mod 3 = 2^{B_{k-1}} mod 3 (seul le terme j = k-1 survit, les autres sont multiples de 3). [PROUVE en R182]

Donc h(v) = g(v)/2^{B_0}, et g(v) ≡ 2^{B_{k-1}} mod 3, d'ou :

h(v) ≡ 2^{B_{k-1}} * (2^{B_0})^{-1} mod 3 = 2^{B_{k-1} - B_0} mod 3 = 2^{Delta_{k-1}} mod 3.

Puisque ord_3(2) = 2 : h(v) mod 3 = 1 si Delta_{k-1} pair, 2 si Delta_{k-1} impair. JAMAIS 0. [PROUVE]

C'est coherent avec le fait connu 3 ∤ g(v), donc 3 ∤ h(v). [PROUVE]

### 1.3 h(v) mod 9 -- La Trace Ternaire Profonde

Je baptise ceci la **TRACE TERNAIRE** de h.

g(v) mod 9 : seuls les termes j = k-1 et j = k-2 survivent (car 3^2 = 9 divise tous les termes avec k-1-j >= 2).

g(v) ≡ 3^0 * 2^{B_{k-1}} + 3^1 * 2^{B_{k-2}} mod 9
     = 2^{B_{k-1}} + 3 * 2^{B_{k-2}} mod 9

Donc h(v) = g(v)/2^{B_0} ≡ (2^{B_{k-1}} + 3 * 2^{B_{k-2}}) * 2^{-B_0} mod 9.

Puisque ord_9(2) = 6 (car 2^6 = 64 = 63 + 1 ≡ 1 mod 9), on a 2^{-1} ≡ 5 mod 9.

h(v) ≡ 2^{Delta_{k-1}} + 3 * 2^{Delta_{k-2}} mod 9

ou Delta_{k-2} = B_{k-2} - B_0, Delta_{k-1} = B_{k-1} - B_0.

**Observation.** h(v) mod 9 ne depend que de Delta_{k-2} mod 6 et Delta_{k-1} mod 6. C'est une fonction de DEUX parametres modulo 6. Les valeurs possibles sont un sous-ensemble de {1, 2, ..., 8} (jamais 0 car 3 ∤ h(v), donc 9 ∤ h(v) ssi...).

ATTENDONS. 3 ∤ h(v) est prouve. Mais 9 | h(v) est-il possible ? 9 | h(v) impliquerait 9 | g(v), donc g(v) ≡ 0 mod 9. Or g(v) ≡ 2^{B_{k-1}} + 3*2^{B_{k-2}} mod 9. Pour que ceci soit 0 mod 9, il faut 2^{B_{k-1}} ≡ -3*2^{B_{k-2}} mod 9, i.e., 2^{Delta_{k-1} - Delta_{k-2}} ≡ -3 ≡ 6 mod 9. Puisque 2^e mod 9 parcourt {2, 4, 8, 7, 5, 1} pour e = 1,...,6, la valeur 6 N'EST PAS atteinte (6 ∉ <2> mod 9, car 6 = 2*3 et 3 ∉ <2> mod 9).

**THEOREME.** 9 ∤ h(v) pour tout vecteur monotone v. [PROUVE]

**Preuve.** 9 | h(v) => 9 | g(v) => g(v) ≡ 0 mod 9 => 2^{B_{k-1}} + 3*2^{B_{k-2}} ≡ 0 mod 9 => 2^{Delta_{k-1} - Delta_{k-2}} ≡ -3 ≡ 6 mod 9. Mais <2> mod 9 = {1, 2, 4, 5, 7, 8}, et 6 ∉ <2> mod 9. Contradiction. CQFD.

Plus generalement : 6 ∉ <2> mod 9 car 6 = 2*3, et si 2^a ≡ 6 mod 9, alors 2^a ≡ 0 mod 3, impossible car gcd(2,3) = 1.

**COROLLAIRE.** 3^m ∤ h(v) pour tout m >= 1. [PROUVE]

**Preuve.** Par recurrence. On sait 3 ∤ h(v). Supposons 3^m ∤ h(v) pour tout m' < m, montrons-le pour m. En fait, c'est plus simple : 3 ∤ h(v) implique directement 3^m ∤ h(v) pour tout m >= 1. CQFD.

**NOTE :** Ce n'est pas nouveau -- c'est la consequence directe de 3 ∤ g(v) (fait connu, cf. R182 Section 2.3). Mais la verification explicite mod 9 via <2> mod 9 est un bon CONTROLE DE COHERENCE.

### 1.4 h(v) mod 27 -- VERIFICATION [DEDUIT]

g(v) mod 27 : termes j = k-1, k-2, k-3 survivent.

g(v) ≡ 2^{B_{k-1}} + 3*2^{B_{k-2}} + 9*2^{B_{k-3}} mod 27

h(v) ≡ 2^{Delta_{k-1}} + 3*2^{Delta_{k-2}} + 9*2^{Delta_{k-3}} mod 27

Et 27 ∤ h(v) decoule encore de 3 ∤ h(v). Rien de nouveau. [CLOS]

---

## 2. L'OPERATEUR INVERSE : Fibres de h

### 2.1 Le Probleme Inverse

**Question.** Etant donne un entier impair h_0 >= 1, combien de vecteurs monotones v = (B_0, ..., B_{k-1}) satisfont h(v) = h_0 ?

**Reformulation.** On cherche les Delta = (Delta_1, ..., Delta_{k-1}) avec Delta_j >= 0 (monotonie des B), au moins un Delta_j >= 1 (aperiodicite), et la suite (0, Delta_1, Delta_2, ..., Delta_{k-1}) croissante (i.e., 0 <= Delta_1 <= Delta_2 <= ... <= Delta_{k-1}), tels que :

3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{Delta_j} = h_0

**Observation immédiate.** h(v) >= 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * 2 (car Delta_j >= 1 pour au moins un j, et >= 0 pour les autres).

Le minimum est atteint quand tous les Delta_j = 0 sauf un qui vaut 1 -- mais la monotonie et l'aperiodicite compliquent. En fait, si tous les Delta_j = 0, h = 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} = 3^{k-1} + (3^{k-1} - 1)/2 = (3^k - 1)/2. Mais h = (3^k - 1)/2 correspond au cas v constant (B_j = B_0 pour tout j), et la multiplicite m_0 = k, qui est impair ssi k est impair.

**L'objet (3^k - 1)/2.** C'est le NOMBRE DE MERSENNE en base 3, que je baptise **NOYAU TRIVIAL** : c'est la valeur de h quand v est constant (pas de variation). Notons-le :

tau_k = (3^k - 1)/2

**VERIFICATION k=1 :** tau_1 = (3-1)/2 = 1. Pour k=1, h(v) = 3^0 = 1 = tau_1. Correct : un seul terme, pas de somme supplementaire.

La condition de cycle pour le noyau trivial : h = tau_k = n'*d => (3^k - 1)/2 = n'*(2^S - 3^k). C'est exactement l'equation des 1-cycles generalisee ! Pour k = 1 : (3-1)/2 = 1 = n'*(2^2 - 3) = n'. Oui, n' = 1, d(1) = 1, et c'est le cycle trivial {1}. [COHERENT]

### 2.2 Le Simplexe Delta et les Valeurs Atteignables

Je definis le **SIMPLEXE DELTA** :

Sigma_k = {(Delta_1, ..., Delta_{k-1}) : 0 <= Delta_1 <= Delta_2 <= ... <= Delta_{k-1}, Delta_{k-1} >= 1}

La contrainte sum B_j = S - k se traduit par : k*B_0 + sum_{j=1}^{k-1} Delta_j = S - k, soit B_0 = (S - k - sum Delta_j)/k. Pour que B_0 soit un entier >= 0, il faut sum Delta_j <= S - k et k | (S - k - sum Delta_j).

**L'application h : Sigma_k -> {entiers impairs} definie par h(Delta) = 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{Delta_j}.**

**Question cruciale : h est-elle INJECTIVE sur Sigma_k ?**

**THEOREME (UNICITE DU DEVELOPPEMENT).** L'application h est INJECTIVE sur N^{k-1} (pas seulement sur Sigma_k).

**Preuve.** C'est un developpement en base mixte. Le terme dominant de h est 3^{k-1} (fixe). Les termes variables sont 3^{k-2} * 2^{Delta_1}, 3^{k-3} * 2^{Delta_2}, ..., 3^0 * 2^{Delta_{k-1}}.

Supposons h(Delta) = h(Delta') avec Delta != Delta'. Soit j_0 le plus grand indice ou ils different. Alors :

3^{k-1-j_0} * (2^{Delta_{j_0}} - 2^{Delta'_{j_0}}) = sum_{j > j_0} 3^{k-1-j} * (2^{Delta'_j} - 2^{Delta_j})

SGDG, supposons Delta_{j_0} > Delta'_{j_0}. Le cote gauche est >= 3^{k-1-j_0} * 2^{Delta'_{j_0}} (car 2^a - 2^b >= 2^b quand a > b).

Le cote droit est <= sum_{j > j_0} 3^{k-1-j} * 2^{max(Delta_j, Delta'_j)}. Mais... l'injectivite n'est PAS evidente car les 2^{Delta_j} croissent sans borne.

**CONTRE-EXEMPLE a l'injectivite.** k = 3, Delta = (0, 3), Delta' = (2, 0).
h(0,3) = 9 + 3*1 + 1*8 = 20. h(2,0) = 9 + 3*4 + 1*1 = 22. Differents. Essayons d'en trouver un egal.
k=3 : h = 9 + 3*2^a + 2^b. Pour a=0, b=3 : 9+3+8=20. Pour a=2, b=1 : 9+12+2=23. Pour a=1, b=2 : 9+6+4=19.

En fait, pour des Delta non monotones, on POURRAIT avoir des collisions, mais la question est complexe. Sur le simplexe monotone (Delta_1 <= Delta_2 <= ... <= Delta_{k-1}), l'injectivite est PLUS PLAUSIBLE car la contrainte de croissance reduit drastiquement l'espace.

**STATUT : QUESTION OUVERTE.** L'injectivite de h sur Sigma_k n'est pas prouvee. Je la note comme CONJECTURE FAIBLE.

### 2.3 Le Noyau Dual -- L'ANTI-NOYAU

Je definis l'**ANTI-NOYAU** : au lieu de diviser par 2^{B_0} (extraire la puissance minimale de 2), divisons par 3^0 (la puissance minimale de 3, qui est toujours 1 -- donc c'est trivial). Plus interessant :

Definissons h*(v) = g(v) / 3^{k-1} (division par la plus grande puissance de 3 dans les coefficients... NON, ce n'est pas un facteur de g(v) en general).

Mieux : **l'anti-noyau naturel** serait d'extraire le facteur 3-adique maximal. Comme 3 ∤ g(v) (fait connu), v_3(g(v)) = 0, et l'anti-noyau 3-adique est g(v) lui-meme. TRIVIAL.

**Conclusion :** Le noyau impair h est le SEUL noyau non trivial extractible de g(v). C'est parce que g(v) a toujours un facteur 2^{B_0} mais jamais de facteur 3. [DEDUIT]

---

## 3. CHANGEMENTS DE FORME

### 3.1 h(v) en base 3

h(v) = 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{Delta_j}

En base 3, chaque coefficient 2^{Delta_j} s'ecrit en base 3. Rappelons :
- 2^0 = 1 -> (1)_3
- 2^1 = 2 -> (2)_3
- 2^2 = 4 -> (11)_3
- 2^3 = 8 -> (22)_3
- 2^4 = 16 -> (121)_3
- 2^5 = 32 -> (1012)_3
- 2^6 = 64 -> (2101)_3

**Pattern remarquable.** Les puissances de 2 en base 3 ont un developpement qui est PUREMENT determine par 2^n mod 3^m pour tout m. Puisque ord_{3^m}(2) = 2*3^{m-1} (pour m >= 1), le developpement en base 3 de 2^n est periodique de periode 2*3^{m-1} pour les m premiers chiffres.

h(v) en base 3 est donc :

h(v) = 1 * 3^{k-1} + [2^{Delta_1}]_3 * 3^{k-2} + [2^{Delta_2}]_3 * 3^{k-3} + ... + [2^{Delta_{k-1}}]_3 * 3^0

Mais cette ecriture est TROMPEUSE car [2^{Delta_j}]_3 a PLUSIEURS chiffres ternaires quand Delta_j >= 2. On ne peut pas simplement juxtaposer -- les retenues PROPAGENT entre les positions.

**Observation.** En base 3, h(v) commence par le chiffre 1 (position 3^{k-1}), suivi de chiffres determines par les 2^{Delta_j} avec propagation de retenues. La STRUCTURE DE RETENUE est l'obstacle a une description propre en base 3.

Je baptise cette structure le **BRUIT DE RETENUE TERNAIRE** (Ternary Carry Noise, TCN).

**STATUT : INVENTION.** Le TCN est un obstacle reel a la representation en base 3, mais ce n'est pas un outil exploitable en l'etat.

### 3.2 h(v) comme Polynome en 2

**Representation polynomiale.** Considerons X = 2 et ecrivons :

h(v) = 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * X^{Delta_j}

C'est une evaluation en X = 2 du POLYNOME :

P_v(X) = 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * X^{Delta_j}

ou les exposants Delta_j forment une suite croissante (0 <) Delta_1 <= Delta_2 <= ... <= Delta_{k-1}.

**Propriete remarquable.** P_v(X) est un polynome a coefficients dans l'ensemble {3^0, 3^1, ..., 3^{k-1}}, avec des exposants dans N. Les coefficients sont des PUISSANCES DE 3 decroissantes, attachees a des exposants CROISSANTS.

**Le degre.** deg(P_v) = Delta_{k-1} = B_{k-1} - B_0.

P_v(0) = 3^{k-1} (le terme constant, toujours non nul).

P_v(1) = 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} = (3^k - 1)/2 = tau_k (le noyau trivial).

**P_v(2) = h(v).** C'est la specialisation qui nous interesse.

P_v(3) = 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * 3^{Delta_j} = sum_{j=0}^{k-1} 3^{k-1-j+Delta_j*[j>=1]}

ou [j>=1] est l'indicatrice. Pour j=0, l'exposant est k-1. Pour j >= 1, c'est k-1-j+Delta_j.

**Observation en X = 3 :** Si Delta_j = j pour tout j (i.e., B_j = B_0 + j, pas equidistribue), alors k-1-j+j = k-1 pour tout j, et P_v(3) = k * 3^{k-1}. C'est un MULTIPLE de k ! Et la condition de cycle h = n'*d deviendrait : en X=3, k * 3^{k-1} = n'*d(k), soit k * 3^{k-1} = n'*(2^S - 3^k). Mais c'est l'evaluation en X=3, pas X=2, donc c'est un OBJET DIFFERENT du probleme original. Neanmoins...

**IDEE : LA FONCTION DE TRANSFERT.** Definissons Phi(X) = P_v(X) pour X variant. Le probleme de cycle est Phi(2) ≡ 0 mod d. Que sait-on de Phi sur d'autres valeurs ?

- Phi(0) = 3^{k-1} (jamais 0 mod d pour k >= 2 car 3^{k-1} < d pour k >= 2 -- VERIFIONS : d = 2^S - 3^k et 3^{k-1} < 2^S - 3^k ssi 3^{k-1} + 3^k < 2^S ssi 4*3^{k-1} < 2^S. Pour k >= 2, S >= 4, et 4*3 = 12 < 16 = 2^4. OK.)
- Phi(1) = tau_k = (3^k - 1)/2.
- Phi(2) = h(v) -- le probleme.
- Phi(3) = somme de puissances de 3 (structure speciale).

**QUESTION PROFONDE.** Peut-on montrer que Phi(2) ≡ 0 mod d est impossible en exploitant les RELATIONS entre Phi(0), Phi(1), Phi(2), Phi(3) ? C'est l'idee d'INTERPOLATION.

Phi est un polynome de degre Delta_{k-1} avec k coefficients non nuls. Par interpolation de Lagrange, il est determine par Delta_{k-1} + 1 points. Si Delta_{k-1} >> k (ce qui est typique : Delta_{k-1} peut atteindre S - k), alors Phi a BEAUCOUP de degres de liberte mais PEU de coefficients non nuls. C'est un POLYNOME CREUX (sparse polynomial).

**STATUT : INVENTION.** Le polynome P_v et la fonction de transfert Phi sont des objets bien definis. L'idee d'exploiter la creusite (sparsity) est PROMETTEUSE mais NON DEVELOPPEE.

### 3.3 h(v) comme Somme de Puissances Ponderees -- Le Point de Vue 2-adique

Dans Z_2 (les entiers 2-adiques), 3 est une unite, et 3^{-1} ≡ ... existe. On peut ecrire :

h(v) = 3^{k-1} * (1 + sum_{j=1}^{k-1} 3^{-j} * 2^{Delta_j})

Le facteur entre parentheses est un element de Z_2 (converge 2-adiquement car les 2^{Delta_j} ont une valuation 2-adique croissante : v_2(3^{-j} * 2^{Delta_j}) = Delta_j >= j pour la convergence... attendons, Delta_j >= 0 seulement, pas necessairement >= j).

En fait, 3^{-j} est une unite 2-adique (|3^{-j}|_2 = 1), et 2^{Delta_j} a valuation Delta_j. Donc le terme general a valuation 2-adique exactement Delta_j. Pour la convergence de la serie, il faut Delta_j -> infini quand j -> infini. Comme Delta_j est croissant et borne par S - k (qui est fini pour k fini), la somme est FINIE, donc converge trivialement. Pas d'apport de la perspective 2-adique ici. [IMPASSE]

### 3.4 h(v) comme Somme Ponderee dans l'Anneau Z[1/3]

h(v) / 3^{k-1} = 1 + sum_{j=1}^{k-1} (2/3)^? -- NON, ce n'est pas la bonne forme. On a :

h(v) / 3^{k-1} = 1 + sum_{j=1}^{k-1} 3^{-j} * 2^{Delta_j} = 1 + sum_{j=1}^{k-1} (2^{Delta_j}/3^j)

Cet objet vit dans Q, pas dans Z. Pour un cycle, h(v) = n'*d, donc :

1 + sum_{j=1}^{k-1} 2^{Delta_j}/3^j = n'*d/3^{k-1}

Le cote droit est n'*(2^S - 3^k)/3^{k-1} = n'*2^S/3^{k-1} - n'*3. Donc :

sum_{j=1}^{k-1} 2^{Delta_j}/3^j = n'*2^S/3^{k-1} - n'*3 - 1

C'est une equation diophantienne en (Delta_1, ..., Delta_{k-1}, n') a coefficients dans Z[1/3].

**STATUT : REFORMULATION.** Pas de compression. [CLOS]

---

## 4. LA RECURRENCE ET LA DYNAMIQUE INVERSE DE COLLATZ

### 4.1 La Recurrence sur k

**THEOREME (RECURRENCE DU NOYAU).** Soit v = (B_0, ..., B_{k-1}) un vecteur de longueur k et v' = (B_0, ..., B_{k-1}, B_k) un vecteur de longueur k+1 (extension par ajout d'un element B_k >= B_{k-1}). Alors :

h_{k+1}(v') = 3 * h_k(v) + 2^{Delta_k}

ou Delta_k = B_k - B_0 >= Delta_{k-1} >= 0, et h_k note le noyau de longueur k.

**Preuve.**

h_{k+1}(v') = 3^k + sum_{j=1}^{k} 3^{k-j} * 2^{B_j - B_0}
            = 3 * [3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{B_j - B_0}] + 3^0 * 2^{B_k - B_0}
            = 3 * h_k(v) + 2^{Delta_k}

CQFD. [PROUVE]

**ATTENTION au cas B_0 qui change.** Si on ajoute un element B_k AU DEBUT (extension par la gauche), le B_0 change ! La recurrence ci-dessus ne vaut que pour l'extension par la DROITE (ajout d'un element >= B_{k-1}).

**Si on ajoute un element B_{-1} <= B_0 au debut :**

v'' = (B_{-1}, B_0, ..., B_{k-1}), nouveau B_0' = B_{-1}.

h_{k+1}(v'') = 3^k + sum_{j=1}^{k} 3^{k-j} * 2^{B_{j-1} - B_{-1}}
             = 3^k + sum_{i=0}^{k-1} 3^{k-1-i} * 2^{B_i - B_{-1}}     (en posant i = j-1)
             = 3^k + 2^{B_0 - B_{-1}} * sum_{i=0}^{k-1} 3^{k-1-i} * 2^{B_i - B_0}

Hmm, ce n'est pas exactement ca. Reprenons proprement.

h_{k+1}(v'') = g_{k+1}(v'') / 2^{B_{-1}}

g_{k+1}(v'') = 3^k * 2^{B_{-1}} + sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}
             = 3^k * 2^{B_{-1}} + g_k(v)

Donc h_{k+1}(v'') = 3^k + g_k(v)/2^{B_{-1}} = 3^k + 2^{B_0 - B_{-1}} * h_k(v).

Posons delta_0 = B_0 - B_{-1} >= 0. Alors :

**h_{k+1}(v'') = 3^k + 2^{delta_0} * h_k(v)** [PROUVE]

### 4.2 Les Deux Dynamiques

On a donc DEUX recurrences selon le sens d'extension :

**(D+) Extension droite :** h_{k+1} = 3 * h_k + 2^{Delta_k}  (Delta_k >= Delta_{k-1} >= 0)

**(D-) Extension gauche :** h_{k+1} = 3^k + 2^{delta_0} * h_k  (delta_0 >= 0)

### 4.3 Connexion avec la Dynamique de Collatz Comprimee

La **dynamique de Collatz comprimee** (Syracuse) est :

T(n) = (3n + 1) / 2^{v_2(3n+1)}   pour n impair.

La recurrence (D+) est h' = 3h + 2^Delta. Comparons :

- Collatz : n -> (3n + 1)/2^a ou a = v_2(3n+1)
- Noyau (D+) : h -> 3h + 2^Delta (sans division par 2)

La difference CRUCIALE : Collatz DIVISE par une puissance de 2, le noyau AJOUTE une puissance de 2. **Ce sont des dynamiques OPPOSEES.**

**THEOREME (DUALITE COLLATZ-NOYAU).** La dynamique (D+) du noyau est la DYNAMIQUE INVERSE de Collatz au sens suivant.

Soit T^{-1}(n) = {m impair : T(m) = n}. Pour n impair donne, les pre-images sont les m tels que (3m + 1)/2^{v_2(3m+1)} = n, i.e., 3m + 1 = n * 2^a pour un certain a >= 1, i.e., m = (n * 2^a - 1)/3 pour les a tels que 3 | (n*2^a - 1).

Or 3 | (n*2^a - 1) ssi n*2^a ≡ 1 mod 3 ssi 2^a ≡ n^{-1} mod 3 (n est impair, donc n mod 3 ∈ {1, 2}, et n^{-1} existe mod 3).

Comparons avec (D+) : h' = 3h + 2^Delta. En inversant : h = (h' - 2^Delta)/3 quand 3 | (h' - 2^Delta).

C'est exactement le meme mecanisme ! m = (n*2^a - 1)/3 dans Collatz correspond a h = (h' - 2^Delta)/3 dans le noyau, avec le decalage de -1 vs pas de decalage.

**OBSERVATION.** La dynamique du noyau est Collatz-1 SANS le "+1". C'est la dynamique 3x (sans +1) dans le sens inverse.

Plus precisement, les pre-images de Syracuse T^{-1}(n) sont de la forme (n*2^a - 1)/3, tandis que l'inversion de (D+) donne (h' - 2^Delta)/3. Si on pose h' = n et 2^Delta = 2^a, on a h = (n - 2^a)/3 dans le noyau vs m = (n*2^a - 1)/3 dans Collatz. CE N'EST PAS la meme chose (produit vs difference).

**CORRECTION.** La connexion est PLUS FAIBLE qu'esperee. Le noyau utilise h' = 3h + 2^Delta (addition), tandis que Collatz-inverse utilise m = (n*2^a - 1)/3 (une relation MULTIPLICATIVE-ADDITIVE differente). Les deux dynamiques partagent la structure "arithmetique mixte base 2 / base 3" mais ne sont PAS isomorphes.

**STATUT : CONJECTURE REFUTEE.** La dynamique du noyau N'EST PAS la dynamique Collatz inversee. C'est une dynamique apparentee mais distincte.

### 4.4 La Dynamique du Noyau comme Objet Propre

Neanmoins, la recurrence (D+) merite d'etre etudiee en tant que telle.

**Definition.** Soit f : N_impair x N -> N_impair definie par f(h, Delta) = 3h + 2^Delta.

**Proprietes immédiates :**
- f(h, 0) = 3h + 1 (tiens, c'est Collatz avant la division !)
- f(h, Delta) est TOUJOURS pair pour Delta >= 1 (car 3h impair + 2^Delta pair = impair + pair = impair). ATTENDONS : 3h est impair (h impair), 2^Delta est pair pour Delta >= 1, donc 3h + 2^Delta est impair. Correct.
- Pour Delta = 0 : 3h + 1 est pair (h impair => 3h impair => 3h + 1 pair). Mais Delta = 0 signifie B_k = B_0, ce qui est permis en monotonie.

**CORRECTION CRUCIALE.** f(h, 0) = 3h + 1 est PAIR, donc h' = 3h + 1 n'est PAS impair. Or h' devrait etre impair (propriete du noyau). Cela signifie que Delta = 0 a l'etape k ne donne PAS un noyau impair directement via la recurrence (D+).

**Explication.** Si B_k = B_0 (Delta_k = 0), alors la multiplicite de B_0 dans v' augmente de 1. Si m_0 etait impair (h_k impair), m_0 + 1 est pair, et h_{k+1} est PAIR. Il faut alors RE-EXTRAIRE le facteur 2 : le vrai noyau de v' n'est pas 3h_k + 1 mais (3h_k + 1)/2^{v_2(3h_k + 1)}.

**Et voici la CONNEXION EXACTE AVEC COLLATZ !**

Quand Delta_k = 0 : le noyau "brut" est 3h_k + 1 (pair), et le vrai noyau est (3h_k + 1)/2^{v_2(3h_k + 1)}. C'est EXACTEMENT l'application de Syracuse T(h_k) = (3*h_k + 1)/2^{v_2(3*h_k + 1)} !

**THEOREME (CONNEXION COLLATZ-NOYAU).** [PROUVE]

Soit v de longueur k avec noyau h_k. L'extension v' = (v, B_0) (ajout de B_0 a la fin, i.e., Delta_k = 0) produit un vecteur de longueur k+1 dont le noyau "vrai" (apres re-extraction du facteur 2) est :

h_{k+1}^{true} = T(h_k) = (3*h_k + 1) / 2^{v_2(3*h_k + 1)}

C'est la MAP DE SYRACUSE appliquee au noyau precedent !

**Preuve.**

g_{k+1}(v') = sum_{j=0}^{k} 3^{k-j} * 2^{B_j}

Avec B_k = B_0, le facteur 2^{B_0} s'extrait de g_{k+1}. Les termes j=0 et j=k contribuent chacun un facteur 2^{B_0}, les autres contribuent 2^{B_j} avec B_j >= B_0.

g_{k+1}(v')/2^{B_0} = 3^k + sum_{j=1}^{k-1} 3^{k-j} * 2^{Delta_j} + 1 = 3 * h_k(v) + 1

(en utilisant h_k(v) = 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{Delta_j}).

Donc g_{k+1}(v')/2^{B_0} = 3*h_k + 1. C'est PAIR (h_k impair). La valuation 2-adique est exactement v_2(3*h_k + 1). Le vrai noyau est (3*h_k + 1)/2^{v_2(3*h_k + 1)} = T(h_k). CQFD.

**COROLLAIRE FONDAMENTAL.** Les extensions par Delta = 0 (repetition de B_0) correspondent EXACTEMENT a l'application de Syracuse. Les extensions par Delta >= 1 correspondent a la dynamique etendue h' = 3h + 2^Delta (qui reste dans les impairs).

**INTERPRETATION.** Un cycle de Collatz de longueur k avec vecteur v encode une ORBITE de la dynamique mixte : alternance d'etapes Syracuse (Delta = 0) et d'etapes "saut" (Delta >= 1). Le noyau h trace cette orbite dans les impairs.

**STATUT : PROUVE et GENUINEMENT NOUVEAU** (a ma connaissance, cette correspondance exacte entre la recurrence du noyau et Syracuse n'est pas dans la litterature standard Bohm-Sontacchi/Steiner).

### 4.5 Consequence pour les Cycles

Un cycle de longueur k correspond a un vecteur v tel que l'orbite du noyau REVIENT a son point de depart. Mais h depend de v entier, pas seulement de h_k. La "boucle" n'est pas une boucle de la dynamique h -> 3h + 2^Delta, mais une condition GLOBALE : le noyau du vecteur complet satisfait h = n'*d.

Neanmoins, la decomposition en etapes est eclairante. Soit v = (B_0, ..., B_{k-1}) un vecteur monotone. La suite des deltas est (Delta_1, ..., Delta_{k-1}). L'orbite du noyau est :

h_1 = 1  (k=1)
h_2 = 3*h_1 + 2^{Delta_1}      si Delta_1 >= 1
    = T(h_1) * 2^{???}          si Delta_1 = 0  (avec re-normalisation)

C'est une complication car les etapes Delta=0 changent la base B_0.

**Simplifions.** Supposons que tous les Delta_j >= 1 (pas de repetition de B_0, i.e., B_0 < B_1 < ... avec inegalite stricte a la premiere position). Alors :

h_k = 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{Delta_j}

et la recurrence est TOUJOURS (D+) : h_{j+1} = 3*h_j + 2^{Delta_j} avec h_1 = 1.

**Verification :** h_1 = 1 = 3^0. h_2 = 3*1 + 2^{Delta_1} = 3 + 2^{Delta_1}. La formule directe donne h_2 = 3^1 + 3^0 * 2^{Delta_1} = 3 + 2^{Delta_1}. OK.

h_3 = 3*h_2 + 2^{Delta_2} = 3*(3 + 2^{Delta_1}) + 2^{Delta_2} = 9 + 3*2^{Delta_1} + 2^{Delta_2}. La formule directe : 3^2 + 3^1 * 2^{Delta_1} + 3^0 * 2^{Delta_2} = 9 + 3*2^{Delta_1} + 2^{Delta_2}. OK. [COHERENT]

---

## 5. L'ANTI-FORME : Le Dual 2<->3

### 5.1 Definition

Le **DUAL** de g(v) est :

g*(v) = sum_{j=0}^{k-1} 2^{k-1-j} * 3^{B_j}

On echange les roles de 2 et 3 : les coefficients decroissants sont des puissances de 2, les exposants croissants sont des puissances de 3.

### 5.2 Le Denominateur Dual

Pour g(v), le "denominateur" est d = 2^S - 3^k. Pour g*(v), le denominateur naturel serait :

d* = 3^{S*} - 2^k  ou S* = ceil(k * log_3(2)) = ceil(k / log_2(3))

**Proprietes de d* :**
- d* = 3^{S*} - 2^k > 0 par definition de S*.
- d* est IMPAIR ssi 2^k est impair, ce qui n'arrive que pour k=0. Donc pour k >= 1, d* est PAIR (car 2^k est pair et 3^{S*} est impair).

**Difference fondamentale :** d est toujours IMPAIR, d* est toujours PAIR (pour k >= 1). Cette asymetrie brise la dualite !

### 5.3 Le Noyau Dual

g*(v) = sum 2^{k-1-j} * 3^{B_j}

La valuation 2-adique : v_2(g*(v)) = min_j(k-1-j) = 0 (atteinte en j = k-1). Donc g*(v) est impair... NON. Le terme j = k-1 est 2^0 * 3^{B_{k-1}} = 3^{B_{k-1}}, qui est impair. Les autres termes sont pairs. Donc g*(v) est impair. Le noyau impair de g* est g* lui-meme (pas de facteur 2 a extraire).

La valuation 3-adique : v_3(g*(v)) = min_j(B_j) = B_0 (car les B_j sont croissants). Donc le **NOYAU TERNAIRE** naturel est :

h*(v) = g*(v) / 3^{B_0} = sum_{j=0}^{k-1} 2^{k-1-j} * 3^{B_j - B_0} = sum_{j=0}^{k-1} 2^{k-1-j} * 3^{Delta_j}

ou Delta_0 = 0, Delta_j = B_j - B_0 >= 0.

h*(v) est un entier avec v_3(h*) = 0 (car le terme j=0 est 2^{k-1} * 3^0 = 2^{k-1}, qui a valuation 3-adique 0). Donc 3 ∤ h*(v)... ATTENDONS : 2^{k-1} mod 3 ∈ {1, 2}, jamais 0. Correct.

**OBSERVATION DUALE.** Dans le probleme original, h(v) est impair et 3 ne le divise jamais. Dans le probleme dual, h*(v) n'est jamais divisible par 3 et... est-il impair ou pair ? h*(v) = 2^{k-1} + sum_{j=1}^{k-1} 2^{k-1-j} * 3^{Delta_j}. Le terme j=0 est 2^{k-1} (pair pour k >= 2). Le terme j = k-1 est 2^0 * 3^{Delta_{k-1}} = 3^{Delta_{k-1}} (impair). Donc h*(v) = (pair) + ... + (impair) = impair ssi le nombre de termes impairs est impair. Le seul terme impair est j = k-1, donc h*(v) est impair pour k >= 2.

VERIFIONS : h*(v) = 2^{k-1} + sum_{j=1}^{k-2} 2^{k-1-j} * 3^{Delta_j} + 3^{Delta_{k-1}}. Tous les termes sauf le dernier sont pairs (contiennent un facteur 2). Le dernier est 3^{Delta_{k-1}}, impair. Donc h* = pair + impair = impair. [PROUVE]

### 5.4 Le Probleme Dual et sa Trivialite

Pour le probleme dual, un "cycle dual" satisferait g*(v) = n * d* = n * (3^{S*} - 2^k). Puisque g* est impair et d* est pair, il faut n impair pour que n*d* soit impair... mais n*d* est toujours pair (d* pair). Donc g*(v) = n*d* est pair, mais g*(v) est impair. CONTRADICTION.

**THEOREME (TRIVIALITE DU DUAL).** Le probleme dual n'a AUCUNE solution pour k >= 1 : g*(v) est toujours impair mais d* est toujours pair, donc g*(v) ≡ 0 mod d* est impossible. [PROUVE]

**INTERPRETATION.** La dualite 2 <-> 3 est BRISEE par la parite. Dans le probleme original (base 2 dans les exposants, base 3 dans les coefficients), d est impair, et le probleme est non trivial. Dans le dual, d* est pair, et le probleme est trivialement vide.

**C'est EXACTEMENT l'asymetrie entre 2 et 3 qui rend le probleme de Collatz difficile.** Si 2 et 3 avaient la meme parite (impossible pour des nombres premiers distincts), le probleme serait soit trivial soit symetrique. L'asymetrie pair/impair est LE facteur structurel fondamental.

**STATUT : PROUVE et CONCEPTUELLEMENT ECLAIRANT.** La trivialite du dual isole PRECISEMENT pourquoi le probleme original est non trivial : c'est parce que d = 2^S - 3^k est impair.

**JE BAPTISE CECI** le **THEOREME DE BRISURE DE PARITE DUALE** (Dual Parity Breaking Theorem, DPBT).

---

## 6. L'ALLEGORIE DE L'ESCALIER ET LA FRICTION STRUCTURELLE

### 6.1 L'Escalier Pondere

h(v) est un escalier a k-1 marches au-dessus du palier 3^{k-1}. Chaque marche j (j = 1, ..., k-1) a :
- une HAUTEUR de 2^{Delta_j} (exponentielle, croissante)
- un POIDS de 3^{k-1-j} (exponentielle, decroissante)
- une contribution poids * hauteur = 3^{k-1-j} * 2^{Delta_j}

L'escalier monte (les hauteurs croissent), mais les poids descendent (la "gravite" diminue avec l'altitude). La contribution de chaque marche est le produit de deux exponentielles de BASES DIFFERENTES (2 et 3) avec des exposants de SIGNES OPPOSES relativement a j.

### 6.2 Pourquoi l'escalier ne peut pas atteindre un palier exact

Pour un cycle, h = n'*d, i.e., l'escalier atteint EXACTEMENT un multiple du denominateur d. La question est : pourquoi cette exactitude est-elle (conjecturalement) impossible ?

**Argument de la FRICTION INCOMMENSURABLE.**

Le ratio entre marches consecutives est :

contribution(j+1)/contribution(j) = [3^{k-2-j} * 2^{Delta_{j+1}}] / [3^{k-1-j} * 2^{Delta_j}]
                                   = (1/3) * 2^{Delta_{j+1} - Delta_j}

Puisque Delta_{j+1} >= Delta_j (monotonie), le ratio est >= 1/3. Le ratio est exactement 1/3 quand Delta_{j+1} = Delta_j, et > 1/3 quand Delta_{j+1} > Delta_j.

Le ratio 2^delta / 3 (ou delta = Delta_{j+1} - Delta_j >= 0) est :
- delta = 0 : 1/3
- delta = 1 : 2/3
- delta = 2 : 4/3
- delta = 3 : 8/3

Le ratio est un NOMBRE RATIONNEL de la forme 2^delta / 3. Ce ratio n'est JAMAIS entier (car 3 ∤ 2^delta). Les ratios entre marches consecutives sont toujours des fractions irréductibles avec denominateur 3.

**L'accumulation de ces fractions irréductibles** au fil des k-1 marches produit une somme qui est TRES SENSIBLE aux choix individuels de Delta_j. Pour atteindre exactement un multiple de d, il faut que ces contributions s'alignent PARFAITEMENT -- une conspiration de k-1 termes, chacun controlé par un paramètre Delta_j discret, dont le produit implique des puissances de 2 et 3 incommensurables.

### 6.3 La Friction Formalisee

**Definition.** La **FRICTION de l'escalier** est la distance minimale de h(v) aux multiples de d, minimisee sur tous les v dans le simplexe monotone :

F(k) = min_{v ∈ Sigma_k} min_{n' >= 1} |h(v) - n'*d|

La conjecture de Collatz (pour un k donne) equivaut a F(k) > 0.

**Encadrement de F(k).** h(v) parcourt un ENSEMBLE DISCRET (les entiers impairs dans un certain intervalle). Le nombre de valeurs distinctes de h(v) est au plus |Sigma_k| = C(S-1, k-1) (taille du simplexe). Le nombre de multiples de d dans l'intervalle [h_min, h_max] est environ (h_max - h_min)/d.

Pour que F(k) = 0 (existence d'un cycle), il faut qu'au moins un des C(S-1, k-1) valeurs de h tombe sur un des ~(h_max - h_min)/d multiples de d. Par un argument probabiliste naif (non rigoureux), la "probabilité" est environ C(S-1, k-1) * 1/d, qui tend vers 0 quand k croit (d croit exponentiellement plus vite que C).

**ATTENTION :** Cet argument probabiliste est EXACTEMENT le Bloc 1 du Junction Theorem, deja connu et exploite. Ce n'est pas nouveau. [CLOS]

### 6.4 L'Allegorie Pousse : Les Escaliers Fantomes

Imaginons TOUS les escaliers possibles (un pour chaque v dans Sigma_k). Chacun a la meme base (le palier 3^{k-1}) mais des profils de marches differents. Le palier-cible (le multiple de d le plus proche) est fixe.

Les escaliers forment un FAISCEAU : ils partent du meme point (la base) et s'etalent vers le haut, chacun selon sa propre sequence de Delta_j. La question est : un rayon de ce faisceau atteint-il exactement le palier-cible ?

L'inegalite de rearrangement (R182 Section 2.2) dit que la configuration monotone MINIMISE la somme. Donc le faisceau est CONFINE du cote BAS : l'escalier le plus bas est l'escalier monotone avec les plus petites marches possibles. Mais le palier-cible d est TRES HAUT (d ~ 2^S - 3^k, qui est du meme ordre que 3^k pour les k pas trop grands).

**L'allegorie finale.** L'escalier est un chemin dans un paysage ou la gravite (les poids ternaires) diminue mais les marches (les puissances binaires) grandissent. La FRICTION entre les deux echelles (binaire et ternaire) empeche l'escalier d'atteindre un palier EXACT car chaque ajustement d'une marche (changer Delta_j de 1 unite) deplace l'altitude de 3^{k-1-j} * 2^{Delta_j} (un quantum INCOMMENSURABLE avec les quantums des autres marches). C'est comme essayer de mesurer une longueur en metres et en pieds simultanement : la double graduation empeche la coincidence exacte.

**STATUT : ALLEGORIE / CONJECTURE.** L'argument d'incommensurabilite est INTUITIF, pas formel. La formaliser reviendrait a prouver un resultat d'approximation diophantienne sur les sommes de la forme sum 3^i * 2^{d_j} mod (2^S - 3^k). C'est exactement le probleme original.

---

## 7. SYNTHESE DES INNOVATIONS

### Resultats PROUVES

| # | Resultat | Section | Nouveaute |
|---|----------|---------|-----------|
| I1 | 9 ∤ h(v) (et plus generalement 3^m ∤ h(v)) | 1.3 | Faible (decoule de 3 ∤ g) |
| I2 | h(v) mod 3 = 2^{Delta_{k-1}} mod 3 | 1.2 | Faible (R182 deja) |
| I3 | h(v) mod 9 = 2^{Delta_{k-1}} + 3*2^{Delta_{k-2}} mod 9 | 1.3 | Modeste |
| I4 | Recurrence (D+) : h_{k+1} = 3*h_k + 2^{Delta_k} | 4.1 | Modeste |
| I5 | Recurrence (D-) : h_{k+1} = 3^k + 2^{delta_0} * h_k | 4.1 | Modeste |
| I6 | **Delta_k = 0 => h_{k+1}^{true} = T(h_k) = Syracuse(h_k)** | 4.4 | **SIGNIFICATIF** |
| I7 | **Trivialite du dual 2<->3** (DPBT) | 5.4 | **SIGNIFICATIF** |
| I8 | h*(v) est toujours impair et 3 ∤ h*(v) | 5.3 | Faible |

### Objets INVENTES

| Nom | Definition | Statut |
|-----|-----------|--------|
| Noyau Trivial tau_k | (3^k - 1)/2, valeur de h quand v est constant | Bien defini |
| Bruit de Retenue Ternaire (TCN) | Structure de propagation des retenues de 2^{Delta_j} en base 3 | Concept, pas outil |
| Polynome de Transfert P_v(X) | sum 3^{k-1-j} * X^{Delta_j}, evalue en X=2 donne h(v) | Bien defini |
| Simplexe Delta Sigma_k | Espace des (Delta_1,...,Delta_{k-1}) monotones | Bien defini |
| Friction F(k) | min distance de h(v) aux multiples de d | Bien defini |
| Brisure de Parite Duale (DPBT) | Le dual est trivial car d* est pair | PROUVE |
| Dynamiques (D+) et (D-) | Extensions droite et gauche du noyau | PROUVE |

### Les DEUX resultats significatifs

**I6 (CONNEXION SYRACUSE-NOYAU) :** L'extension d'un vecteur par repetition de B_0 (Delta = 0) applique EXACTEMENT la map de Syracuse au noyau. C'est un fait structurel prouve qui UNIFIE la dynamique Collatz et la structure algebrique du noyau g(v). Ce n'est PAS du rebranding de Bohm-Sontacchi (qui traite g(v) comme objet statique, pas comme resultat d'une dynamique).

**Verification k=1 :** h_1 = 1. Extension par Delta = 0 : h_2^{true} = T(1) = (3+1)/2^2 = 1. Donc on retombe sur 1 -- c'est le cycle trivial ! Le seul point fixe de T dans les impairs positifs est 1 (modulo la boucle 1->2->1 de Syracuse). COHERENT : le cycle trivial {1, 4, 2} correspond au point fixe h = 1 de Syracuse.

**I7 (DPBT) :** La trivialite du probleme dual isole precisement le role de la PARITE de d. Le probleme original est non trivial parce que et seulement parce que d = 2^S - 3^k est impair. C'est un eclairage conceptuel profond, meme si ce n'est pas un outil de preuve direct.

---

## 8. PISTES POUR R184

### Piste 1 (8/10) : Exploiter I6 pour les cycles longs

Si un cycle de longueur k existe, le noyau h peut etre construit par k-1 etapes de la dynamique mixte :
- Etapes "Syracuse" (Delta = 0) : h -> T(h)
- Etapes "saut" (Delta >= 1) : h -> 3h + 2^Delta

La condition de cycle est que le noyau final satisfasse h_k = n'*d. Cela transforme le probleme en : parmi toutes les orbites de longueur k-1 de la dynamique mixte partant de h_1 = 1, l'une d'elles atteint-elle un multiple de d ?

C'est une REFORMULATION DYNAMIQUE du probleme statique. L'avantage est que les etapes Syracuse sont BIEN ETUDIEES (Tao 2019, etc.), et les etapes "saut" sont plus simples (addition d'une puissance de 2). Cette decomposition pourrait interfacer le noyau avec les resultats de Tao sur la dynamique de Syracuse.

### Piste 2 (6/10) : Le polynome creux P_v(X)

P_v(X) = 3^{k-1} + sum 3^{k-1-j} * X^{Delta_j} est un polynome de degre Delta_{k-1} avec seulement k coefficients non nuls. La condition de cycle est P_v(2) ≡ 0 mod d. Les polynomes creux modulo d ont ete etudies (Canetti, Friedlander, Konyagin, Larsen, Lipton, Shparlinski...). Y a-t-il des bornes sur le nombre de zeros d'un polynome creux mod d qui s'appliqueraient ici ?

### Piste 3 (5/10) : Analyse par regimes de Delta

La decomposition en etapes Syracuse (Delta = 0) vs sauts (Delta >= 1) definit un MOTIF BINAIRE : pour chaque j, soit Delta_j = 0 soit Delta_j >= 1. Ce motif est un mot sur {S, J} (Syracuse ou Jump). Le nombre de motifs possibles est 2^{k-1}, et chaque motif contraint differemment l'orbite du noyau. Peut-on exclure certains motifs a priori ?

---

## CONTROLES DE COHERENCE

**Test k=1 :** g(v) = 3^0 * 2^{B_0} = 2^{B_0}. d(1) = 2^2 - 3 = 1. Cycle : g = n*1, toujours satisfait. h = g/2^{B_0} = 1. tau_1 = 1. Tout coherent.

**Test k=2 :** g(v) = 3*2^{B_0} + 2^{B_1}. S = 4 (pour k=2, S = ceil(2*log_2(3)) = ceil(3.17) = 4). d = 16 - 9 = 7.
h = 3 + 2^{Delta_1} ou Delta_1 = B_1 - B_0 >= 0 et B_0 + B_1 = S - k = 2 (sum B_j = S - k = 2). Si B_0 = 0, B_1 = 2 : h = 3 + 4 = 7. Cycle ? h = 7 = 1*d = 7. OUI, c'est un cycle de longueur 2. Mais... les cycles de longueur 2 n'existent pas dans Collatz positif. VERIFIONS : n = 2^{B_0} * n' = 1 * 1 = 1. g(v) = 3*1 + 4 = 7 = 1*7 = n*d. Cela correspondrait a n=1. Mais en Collatz, le cycle serait n -> ... -> n avec 2 etapes impaires. Le seul cycle connu est {1,4,2}... attendons, pour n=1, le cycle 1 -> 4 -> 2 -> 1 a k=1 etape impaire, pas k=2.

**RESOLUTION :** L'equation g(v) = n*d admet la solution B_0=0, B_1=2 pour k=2, S=4, n=1. Mais n=1 est deja le cycle trivial, et un cycle de longueur k=2 pour n=1 signifierait que 1 a AUSSI un cycle de longueur 2. C'est impossible car 1 -> 4 -> 2 -> 1 est le seul cycle passant par 1.

Le probleme est que n = h*2^{B_0}/d = 7*1/7 = 1. Mais le cycle correspondant serait : n=1, k=2, S=4. L'orbite serait : 1 -> (3*1+1=4, /2^{B_0+1}=4/2=2) -> (3*2... attendons, 2 est pair, pas impair). L'orbite Collatz de 1 est 1 -> 4 -> 2 -> 1, qui a 1 etape impaire (k=1), pas k=2.

L'equation g(v) = n*d pour k=2, n=1 donne une "solution fantome" qui ne correspond pas a un vrai cycle Collatz. Cela est CONNU : les solutions de g(v) = n*d incluent des fantomes. La contrainte supplementaire est que n doit etre impair positif et que l'orbite doit reellement suivre la dynamique Collatz. Ici n=1 avec k=2 est un fantome.

Cela rappelle que h(v) = n'*d est une CONDITION NECESSAIRE mais pas suffisante pour un cycle. La suffisance requiert la coherence de l'orbite. [COHERENT AVEC LA LITTERATURE]

---

*R183 : 8 resultats prouves, 7 objets inventes, 2 resultats significatifs (I6 connexion Syracuse-noyau, I7 DPBT), 3 pistes pour R184. Pas de script Python. Raisonnement pur.*
