# R83 — BILAN : Profondeur autonome contrôlée — BTL ENTERRÉ, innovation suspendue

## Type : X/I/P
## IVS : 8/10

**Justification IVS** :
- Précision du type de lemme visé : 9/10 (type "pont somme→produit" formulé, inutilement faible/haut identifiés)
- Qualité des candidats : 6/10 (4 candidats, tous éliminés — mais éliminations honnêtes et instructives)
- Robustesse anti-redondance : 9/10 (chaque candidat testé contre R67-R82, rebrandings détectés immédiatement)
- Qualité du pipeline autonome : 9/10 (5 sous-rounds, checkpoints respectés, STOP appliqués)
- Honnêteté de la décision finale : 10/10 (suspension propre, BTL quantitativement enterré, pas de fausse percée)

Score 8/10 pour un round qui ENTERRE un candidat et SUSPEND l'innovation — plus élevé que R82 (7/10) car le gain informationnel est décisif : le programme sait désormais que la voie S-unit/Baker est quantitativement inaccessible pour le gap.

---

## 1. Résumé exécutif

R83 teste, avec une autonomie plus profonde que d'habitude, si le front théorique ouvert par R82 (connexion S-unit/Baker via BTL) peut produire un lemme candidat réellement mordant.

**Réponse : NON.**

Le round exécute d'abord la condition de non-boucle imposée par R82 : calculer la borne d'Evertse-Schlickewei-Schmidt N(k) pour k=21 et la comparer avec |Comp_mono(34, 21)| = C(33, 20).

**Résultat quantitatif décisif** :
- Borne ESS (2002) pour k=21 : N_ESS ≤ exp((6·23)^{69}) = exp(138^{69}) ≈ **exp(10^{148})**
- Nombre de compositions monotones : |Comp_mono(34, 21)| = C(33, 20) ≈ **5.73 × 10^8**
- Ratio : N_ESS / |Comp_mono| ≈ **exp(10^{148}) / 10^9** → astronomiquement supérieur
- **BTL est QUANTITATIVEMENT ENTERRÉ pour le gap k=21-41.**

Trois candidats supplémentaires ont été générés et soumis au pipeline autonome (SCR, HSB, BIF). Tous éliminés — aucun ne produit de lemme mordant.

**Conclusion** : l'autonomie plus profonde ne produit PAS de candidat dépassant les limites connues. Le front théorique BTL/S-unit est un PONT STRUCTUREL valide mais QUANTITATIVEMENT INUTILE. L'innovation théorique est SUSPENDUE proprement.

---

## 2. Type du round + IVS

**Type** : X/I/P
- **X** : investigation causale (calcul quantitatif ESS, test de viabilité du front BTL)
- **I** : innovation disciplinée (4 candidats proposés, 4 éliminés)
- **P** : exigence de précision, testabilité, falsifiabilité

**IVS** : 8/10 — Le round produit un résultat DÉCISIF (BTL enterré quantitativement) et une suspension honnête. Le 8 (pas 7) reflète que le gain informationnel est plus fort que celui de R82 : on passe de "BTL qualifié avec réserve" à "BTL enterré avec preuve quantitative".

---

## 3. Méthode

1. Qualification du front et du type de lemme à chercher (Phase 1, Axes A+B)
2. Exécution de la condition de non-boucle R82 : calcul ESS pour k=21 (Phase 2 préalable)
3. Génération contrôlée de 4 candidats de lemmes (Phase 2, Axe C)
4. Définition du protocole agentique (Phase 2, Axe D)
5. Pipeline autonome : 5 sous-rounds avec checkpoints (Phase 3)
6. Audit croisé et tournoi (Phase 4, Axes E+F)
7. Décision stratégique (Phase 5, Axe G)
8. Aucun calcul numérique, aucun k-par-k, aucun cas particulier
9. Seule exception : le calcul SYMBOLIQUE de la borne ESS (requis par R82)

---

## 4. Résultats PHASE 1 / AXE A — Type de lemme utile

### Questions obligatoires et réponses

**Q1. Quel type de lemme manque exactement ?**

Un **lemme-pont somme→produit** : un énoncé qui convertit une information sur la SOMME corrSum = Σ 3^{k-1-i}·2^{A_i} en une information compatible avec les outils de PRODUIT (Baker, Evertse). Plus précisément : un lemme qui exploite la structure spécifique de corrSum (coefficients en progression géométrique, variables monotones, base {2,3}) pour améliorer les bornes S-unit génériques au point de les rendre utiles dans le gap.

**Q2. Quel type de lemme serait trop faible ?**

| Type trop faible | Pourquoi |
|-----------------|----------|
| "corrSum est une S-unit equation" | Déjà établi en R82, c'est un CADRE pas un LEMME |
| "Le nombre de solutions est fini" | Evertse le dit déjà — fini mais astronomique |
| "corrSum a une structure spéciale" | Observation, pas résultat quantitatif |
| "La monotonie contraint les solutions" | Vrai mais ne réduit pas assez la borne |

**Q3. Quel type de lemme serait trop haut ?**

| Type trop haut | Pourquoi |
|---------------|----------|
| "N_0(d) = 0 pour tout k dans le gap" | C'est la CIBLE, pas un lemme intermédiaire |
| "Toute S-unit equation avec coefficients géométriques n'a pas de solution" | Faux en général |
| "Baker exclut tous les p | d" | Requiert une percée en transcendance |

**Q4. Quel lemme serait réellement utile ?**

Un lemme de la forme :

> Pour l'équation corrSum = m·d avec A monotone et coefficients 3^{k-1-i}, le nombre de solutions monotones est borné par C(k) ≤ k^{O(k)}, avec C(k) < C(S-1, k-1) pour k ≥ K_0.

Ceci réduirait la borne Evertse de exp(10^{148}) à quelque chose de comparable à |Comp_mono|. Si C(k) = 0, le gap serait résolu.

**Q5. Formulation minimale autorisée ?**

> **Lemme-pont minimal** : Il existe f(k) << exp((6(k+2))^{3(k+2)}) tel que le nombre de compositions monotones A avec d | corrSum(A) est ≤ f(k), et f(21) < C(33, 20).

### Livrables Phase 1A

- **Type de lemme recherché** : pont quantitatif somme→produit exploitant la structure spécifique de corrSum
- **Types trop faibles** : cadre S-unit générique, observation qualitative de structure
- **Types trop hauts** : preuve directe de N_0(d)=0, exclusion Baker universelle
- **Formulation minimale** : borne f(k) < C(S-1, k-1) sur le nombre de solutions monotones

---

## 5. Résultats PHASE 1 / AXE B — Anti-résurrection

### Tableau anti-résurrection

| Style de lemme déjà fermé | Rounds | Différence minimale requise |
|---------------------------|--------|----------------------------|
| Confinement sumset dans sous-groupe additif | R75 | F_p n'a PAS de sous-groupes additifs non triviaux |
| Suivi de somme dans quotient multiplicatif | R81, R82 (CST) | π(a+b) ≠ f(π(a),π(b)) pour tout hom. multiplicatif π |
| Sparsité → exclusion ponctuelle | R82 (SRF), R29 | |Σ_≤(k)| ≪ p ne cible pas -1 spécifiquement |
| Reformulation dans F_p | R80 (noyau irréductible) | Toute reformulation mod p est isomorphe à SAMC |
| Taille/valuation sur d | R81 (GZD) | v_2(d)=v_3(d)=0, contraintes triviales |
| Horner mod p | R80 (DAS) | Horner mod p = SAMC sous renumérotation |
| Baker sur forme linéaire directe | R82 (BTL-L1 naïf) | Somme ≠ produit, Baker ne s'applique pas directement |

### Test rapide de non-redondance pour R83

Un candidat R83 est recevable SSI :
1. Il produit une BORNE QUANTITATIVE sur le nombre de solutions monotones
2. Cette borne est STRICTEMENT INFÉRIEURE à la borne ESS générique
3. L'amélioration vient de la STRUCTURE SPÉCIFIQUE de corrSum (pas d'un argument générique)
4. Le lemme ne ramène PAS à borner une somme exponentielle courte (mur R73)
5. Le lemme n'est PAS une reformulation de SAMC dans un vocabulaire différent

### Drapeaux rouges prioritaires

1. **DR1** : Tout candidat qui "factorise corrSum dans F_p" = noyau irréductible (R80)
2. **DR2** : Tout candidat qui "utilise la sparsité sans mécanisme d'exclusion" = SRF (R82)
3. **DR3** : Tout candidat qui "applique Baker sans réduire la somme en produit" = BTL-L1 naïf (R82)
4. **DR4** : Tout candidat qui "suit la somme dans un quotient" = CST (R82) + faille add/mult (R81)
5. **DR5** : Tout candidat qui "exploite la récurrence de Horner mod p" = SAMC (R80)

### Angles morts à surveiller

1. Le passage implicite de "fini (Evertse)" à "petit" — la finitude seule ne vaut rien si la borne est exp(10^{148})
2. La tentation de "raffiner Evertse par la structure" sans avoir un théorème raffiné dans la littérature
3. Le risque de confondre "corrSum a une structure spéciale" (vrai) avec "cette structure réduit le nombre de solutions" (non prouvé)

---

## 6. Résultats PHASE 2 préalable — Condition de non-boucle R82

### Calcul de la borne d'Evertse-Schlickewei-Schmidt pour k=21

**L'équation S-unit** :

Σ_{i=0}^{k-1} 3^{k-1-i} · 2^{A_i} - m·2^S + m·3^k = 0

C'est une équation en n = k+2 termes d'S-unités avec S = {2, 3} (|S| = 2 primes).

Pour k = 21 : n = 23, s = 2.

**Théorème (Evertse-Schlickewei-Schmidt, 2002, Annals of Mathematics)** : Le nombre de solutions non-dégénérées de l'équation a_1·x_1 + ... + a_n·x_n = 0 en S-unités (x_i ∈ Z_S* = {±2^a · 3^b : a,b ∈ Z}) est au plus :

> N(n, s) ≤ exp((6n)^{3n} · (s + 1))

### Application numérique pour k = 21

- n = k + 2 = 23
- s = |S| = 2
- 6n = 6 × 23 = 138
- 3n = 3 × 23 = 69
- s + 1 = 3

Borne ESS :
N(23, 2) ≤ exp(138^{69} · 3)

Calcul de 138^{69} :
- ln(138) = 4.927
- 69 × 4.927 = 339.96
- 138^{69} = exp(339.96) ≈ 10^{147.6}

Donc :
- N_ESS ≤ exp(3 × 10^{147.6}) ≈ **exp(10^{148})**

### Comparaison avec |Comp_mono(34, 21)|

Pour k=21, S=34 (le plus petit S admissible : S = ceil(k·log₂3) + 1 = 34) :

|Comp_mono(34, 21)| = C(S-1, k-1) = C(33, 20) = C(33, 13)

C(33, 13) = 33! / (13! × 20!) = **573 166 440** ≈ 5.73 × 10^8

### Verdict quantitatif

| Quantité | Valeur | Ordre de grandeur |
|----------|--------|-------------------|
| Borne ESS N(23, 2) | exp(3 × 10^{147.6}) | **Tour d'exponentielle** |
| |Comp_mono(34, 21)| | 573 166 440 | **10^{8.76}** |
| Ratio N_ESS / |Comp_mono| | exp(10^{148}) / 10^9 | **Astronomiquement > 1** |

**La borne d'Evertse est ASTRONOMIQUEMENT plus grande que le nombre de compositions monotones.**

Même en améliorant la borne par un facteur polynomial (ou même exponentiel en k), le ratio resterait incommensurable. Il faudrait une amélioration de l'ordre de exp(-10^{148} + 9·log 10) ≈ exp(-10^{148}), ce qui est impossible avec les techniques actuelles.

### Améliorations connues dans la littérature

| Amélioration | Référence | Borne | Suffisante ? |
|-------------|-----------|-------|:------------:|
| ESS (2002) générique | Evertse-Schlickewei-Schmidt, Annals | exp((6n)^{3n}·(s+1)) | **NON** |
| Evertse (1984) pour n=2 | Inventiones | 3·7^{s+1} = 1029 | NON APPLICABLE (n=23≠2) |
| Amoroso-Viada (2009) | Compositio | Améliore les solutions dégénérées | **NON** (nos solutions sont non-dégénérées) |
| Evertse-Ferretti (2013) | J. reine angew. Math. | Dépend de la hauteur h | **NON** (h ≈ 2^S ≈ 10^{10}, ne réduit pas assez) |
| Stewart-Tijdeman (1986) | Acta Arith. | Pour n=2 avec |S|=2 | NON APPLICABLE (n=23) |
| Schmidt Subspace Theorem | Schmidt 1972 | Qualitatif (finitude) | **NON** (pas de borne effective) |

**Aucune amélioration connue ne réduit la borne à moins de C(33,20).**

### Conclusion de la condition de non-boucle

> **BTL est QUANTITATIVEMENT ENTERRÉ pour le gap k=21-41.** La borne d'Evertse-Schlickewei-Schmidt est une tour d'exponentielle, tandis que |Comp_mono| est seulement ~10^9. L'écart est si gigantesque qu'aucune amélioration technique raisonnable (polynomiale, exponentielle simple en k, ou même doublement exponentielle) ne suffirait à le combler.

---

## 7. Résultats PHASE 2 / AXE C — Candidats entrants

### CANDIDAT 1 — QCB (Quantitative Comparison Bound)

**Objet** : Calcul explicite de N_ESS(k=21) et comparaison avec |Comp_mono|.

**Lemme candidat** : N/A — ce candidat est le calcul REQUIS par R82, pas un lemme nouveau.

**Résultat** : EXÉCUTÉ (section 6 ci-dessus). BTL enterré quantitativement.

**Statut** : [COMPLÉTÉ] — ce n'est pas un candidat de lemme, c'est une vérification.

---

### CANDIDAT 2 — SCR (Structural Coefficient Rigidity)

**Famille** : Amélioration de la borne S-unit en exploitant la structure des coefficients

**Manque visé** : La borne ESS est générique — elle ne distingue pas les coefficients (1, 1, ..., 1) de (3^{k-1}, 3^{k-2}, ..., 3, 1). La progression géométrique des coefficients pourrait réduire la borne.

**Objet précis** : L'équation Σ c_i · x_i = 0 avec c_i = 3^{k-1-i} (progression géométrique de raison 1/3) et x_i = 2^{A_i} (S-unités monotones).

**Lemme candidat (SCR-L1)** : Pour l'équation S-unitaire avec coefficients en progression géométrique de raison r = 1/3, le nombre de solutions non-dégénérées est au plus g(n, r) < exp((6n)^{3n}·(s+1)), où g est strictement inférieure à la borne ESS.

**Test de réfutation** :
- La borne ESS ne dépend PAS des coefficients a_i. Elle borne le nombre de solutions pour TOUS choix de coefficients uniformément. La preuve passe par le Subspace Theorem qui traite les coefficients comme des constantes.
- Pour que les coefficients améliorent la borne, il faudrait un résultat de type "S-unit equation with structured coefficients has fewer solutions". Un tel résultat N'EXISTE PAS dans la littérature actuelle.
- Les travaux d'Evertse-Győry (2015, monographie Cambridge) examinent les cas structurés (récurrences linéaires, polynômes en progression) mais ne donnent PAS de borne meilleure que ESS pour n ≥ 3 termes.
- **La progression géométrique des coefficients n'est pas exploitable avec les outils existants.**

**Critère de victoire** : Trouver dans la littérature un théorème donnant g(n, r) < exp((6n)^{3n}) pour des coefficients géométriques. AUCUN TEL THÉORÈME N'EXISTE.

**Première faiblesse** : La borne ESS est une borne UNIFORME sur les coefficients. Les coefficients géométriques ne créent pas de "sous-espaces interdits" additionnels dans le cadre du Subspace Theorem.

**Pourquoi mérite d'entrer en tournoi** : L'idée est naturelle et mérite d'être testée et tuée proprement.

**Plausibilité initiale** : FAIBLE (2/10) — aucun résultat structuré connu dans la littérature.

---

### CANDIDAT 3 — HSB (Horner Step Bound)

**Famille** : Décomposition de l'S-unit equation via la structure récursive de Horner

**Manque visé** : L'équation à n=23 termes a une borne exp(138^{69}). Si on la décompose en une chaîne de k-1 équations à 2 ou 3 termes, chacune aurait une borne ~10^3 (Evertse 1984 pour n=2).

**Objet précis** : La récurrence de Horner dans Z :
- H_0 = 3^{k-1} + 2^{c_1} · H_1 → équation 3 termes : H_0 - 3^{k-1} - 2^{c_1}·H_1 = 0
- H_1 = 3^{k-2} + 2^{c_2} · H_2 → équation 3 termes : H_1 - 3^{k-2} - 2^{c_2}·H_2 = 0
- ...
- H_{k-2} = 3 + 2^{c_{k-1}} → équation 2 termes (triviale, solution unique)

Chaque équation a n=3 termes. La borne ESS pour n=3, s=2 est exp(18^9 · 3) = exp(3 × 18^9) ≈ exp(10^{12}).

**Lemme candidat (HSB-L1)** : En décomposant corrSum via Horner en k-1 équations à 3 termes, le nombre total de solutions de la chaîne est au plus [exp(10^{12})]^{k-1} ≈ exp(20 × 10^{12}).

**Test de réfutation** :
- **Problème critique** : les équations sont COUPLÉES. H_1 apparaît dans l'équation 0 ET dans l'équation 1. La variable H_j n'est pas une S-unité libre — elle est DÉTERMINÉE par c_{j+1},...,c_{k-1} via le reste de la récurrence.
- En conséquence, on ne peut PAS simplement multiplier les bornes. Le produit exp(10^{12})^{20} = exp(20 × 10^{12}) serait une borne sur un PRODUIT CARTÉSIEN de solutions indépendantes, ce qui n'est pas le cas.
- Si on essaie de résoudre la chaîne SÉQUENTIELLEMENT (de H_{k-2} vers H_0), chaque étape substitue la valeur de H_{j+1} dans l'équation de H_j. Ceci ramène à une SEULE équation en (c_1,...,c_{k-1}), qui est... l'équation originale de corrSum.
- **La décomposition de Horner ne découple PAS l'S-unit equation.**

**Critère de victoire** : Montrer que la structure de couplage réduit le nombre de solutions. IMPOSSIBLE — le couplage est TOTAL (chaque c_j affecte tous les H_i avec i < j).

**Première faiblesse** : Le couplage entre les H_j empêche toute factorisation de la borne.

**Plausibilité initiale** : TRÈS FAIBLE (1/10) — le couplage tue la décomposition.

---

### CANDIDAT 4 — BIF (Baker-Informed Filtration)

**Famille** : Contrainte sur la factorisation de d via Baker, suivi de SAMC ciblé

**Manque visé** : Les primes p | d(k) ne sont pas quelconques — Baker contraint leurs propriétés. Si on pouvait restreindre les primes à tester, SAMC pourrait devenir tractable pour certains p.

**Objet précis** : Le théorème de Baker sur les formes linéaires en logarithmes p-adiques (Yu Kunrui, 2007) : si p | 2^S - 3^k, alors ord_p(2^S - 3^k) est borné en fonction de p, S, k. Plus précisément, pour v_p(2^S - 3^k) ≥ 1 :

v_p(2^S - 3^k) ≤ C · (log p)^2 · (log S) · (log k)

Ceci borne la puissance de p dans d, mais ne borne PAS p lui-même significativement.

**Lemme candidat (BIF-L1)** : Pour k=21, S=34, les primes p | d(21) satisfont :
1. p ∤ 6 (car d est impair et non divisible par 3)
2. ord_p(2) | S = 34 (car 2^S ≡ 3^k ≡ 3^{21} mod p, donc 2^{34} ≡ 3^{21} mod p)

Wait — ce n'est pas exact. 2^S ≡ 3^k mod p signifie 2^S - 3^k ≡ 0 mod p, ce qui est la DÉFINITION de p | d. Mais ord_p(2) n'est pas forcément un diviseur de S.

En fait : 2^S ≡ 3^k mod p. Cela ne dit rien directement sur ord_p(2) SAUF que 2^S est déterminé mod p une fois qu'on connaît 3^k mod p.

**Test de réfutation** :
- Baker contraint |2^S - 3^k| par le bas : |2^S - 3^k| > exp(-C · (log S)^2 · (log k)). Ceci donne d > exp(-C · ...) · 3^k ≈ 3^k (puisque l'exponentielle est > 1 pour S, k assez grands). Pas informatif — on sait déjà que d > 0.
- Baker p-adique contraint v_p(d) mais pas la FACTORISATION de d en primes.
- Pour restreindre les primes à tester, on aurait besoin d'un résultat du type "d(k) n'a que des 'petits' facteurs premiers" ou "d(k) a un facteur premier > C(S,k)". Aucun tel résultat n'est connu — la factorisation de 2^S - 3^k est un problème ouvert (nombres de Cunningham).
- **Baker ne filtre pas les primes — il borne les valuations.**

**Critère de victoire** : Montrer que Baker/Yu restreint suffisamment les p | d pour rendre SAMC/DP faisable sur les primes restantes. IMPOSSIBLE — Baker ne contrôle pas la factorisation.

**Première faiblesse** : La factorisation de 2^S - 3^k est un problème de théorie des nombres (tables de Cunningham) sans solution analytique connue.

**Plausibilité initiale** : FAIBLE (2/10) — Baker ne s'applique pas à la factorisation.

---

## 8. Résultats PHASE 2 / AXE D — Protocole agentique

### Agents mobilisés pour R83

| Agent | Rôle | Verrouillage |
|-------|------|-------------|
| **Investigateur causal** | Qualifie le type de lemme utile | Ne propose PAS de candidats |
| **Investigateur historique** | Bloque les résurrections R67-R82 | Droit de VETO |
| **Innovateur discipliné** | Propose 4 candidats | Max 4, chaîne complète chacun |
| **Auditeur fail-closed** | Teste réfutation de chaque candidat | Tue les candidats sans borne quantitative |
| **Arbitre de tournoi** | Élimine et sélectionne | Ne "sauve" jamais un candidat faible |
| **Vérificateur de preuve** | Examine la semi-formalisation | Exige un lemme explicite, pas un cadre |
| **Synthétiseur structurel** | Relie au programme sans gonfler | Distingue gain structurel vs gain quantitatif |

### Ordre d'intervention

1. Investigateur causal → type de lemme (Phase 1A)
2. Investigateur historique → anti-résurrection (Phase 1B)
3. Condition de non-boucle R82 → calcul ESS (Phase 2 préalable)
4. Innovateur discipliné → 4 candidats (Phase 2C)
5. Auditeur fail-closed → tests de réfutation (Phase 3, S1-S3)
6. Vérificateur de preuve → semi-formalisation (Phase 3, S4)
7. Arbitre de tournoi → élimination et survivant (Phase 3, S5)
8. Synthétiseur structurel → impact programmatique (Phase 4F)

### Agents en contradiction explicite

- Innovateur ↔ Auditeur : l'innovateur propose, l'auditeur tue
- Investigateur historique ↔ Innovateur : l'historique bloque les rebrandings

### Checkpoints d'arrêt

- Après S1 : si un candidat est un rebranding → STOP immédiat
- Après S2 : si aucun candidat n'a de borne quantitative → suspension du pipeline
- Après S3 : si aucun candidat ne passe l'anti-redondance → suspension
- Après S4 : si aucun candidat n'a de lemme semi-formalisé → résultat = outcome 3
- Après S5 : décision finale

---

## 9. Journal des sous-rounds autonomes S1→S5

### S1 — Qualification initiale des candidats

**Candidats actifs** : QCB, SCR, HSB, BIF

**Objectif** : Vérifier la non-redondance et la cohérence de chaque candidat.

| Candidat | Non-redondant ? | Objet précis ? | Borne quantitative ? | Lien au verrou ? | Statut S1 |
|----------|:-:|:-:|:-:|:-:|------|
| QCB | N/A (vérification, pas candidat) | OUI | OUI (calcul ESS) | DIRECT | **COMPLÉTÉ** |
| SCR | OUI (coefficients géométriques = angle nouveau) | OUI | NON (aucun théorème connu) | INDIRECT (via Evertse) | **QUALIFIÉ POUR S2** |
| HSB | OUI (décomposition Horner dans Z = angle nouveau) | OUI | PARTIEL (bornes par étape) | DIRECT (via récurrence) | **QUALIFIÉ POUR S2** |
| BIF | PARTIEL (Baker déjà mentionné R76/R80) | OUI | NON (Baker ≠ factorisation) | INDIRECT (via filtrage) | **QUALIFIÉ POUR S2** |

**Checkpoint S1** : QCB complété. 3 candidats qualifiés pour S2. Aucun rebranding évident.

**Décision** : CONTINUER.

---

### S2 — Première poussée structurale

**Candidats actifs** : SCR, HSB, BIF

**Objectif** : Tester si chaque candidat a un mécanisme quantitatif viable.

**SCR — Test de mécanisme** :
- La borne ESS est obtenue via le Subspace Theorem (Schmidt). La preuve majore le nombre de sous-espaces propres contenant les solutions. Les coefficients a_i n'interviennent que comme DONNÉES FIXES — ils déterminent l'hyperplan, pas le nombre de sous-espaces.
- La progression géométrique des coefficients signifie que l'hyperplan Σ 3^{k-1-i}·x_i = 0 est un hyperplan SPÉCIFIQUE dans (Q*)^n. Mais le Subspace Theorem ne distingue pas les hyperplans — il borne le nombre de solutions pour TOUT hyperplan uniformément.
- Pour améliorer la borne, il faudrait un résultat de type "pour certains hyperplans spéciaux, il y a moins de sous-espaces solutions". Ce résultat n'existe pas.
- **SCR AFFAIBLI** : aucun mécanisme quantitatif viable.

**HSB — Test de découplage** :
- La récurrence H_j = 3^{k-1-j} + 2^{c_j}·H_{j+1} crée un ARBRE de solutions si on résout de bas en haut.
- Étape k-2 : H_{k-2} = 3 + 2^{c_{k-1}}. C'est un entier déterminé par c_{k-1} seul.
- Étape k-3 : H_{k-3} = 9 + 2^{c_{k-2}}·H_{k-2} = 9 + 2^{c_{k-2}}·(3 + 2^{c_{k-1}}). Déterminé par (c_{k-2}, c_{k-1}).
- En remontant : H_0 est un POLYNÔME en les 2^{c_j}, déterminé par (c_1,...,c_{k-1}).
- La condition H_0 ≡ 0 mod p est UNE SEULE congruence en (c_1,...,c_{k-1}). Elle n'est pas décomposable en k-1 congruences indépendantes.
- **HSB ÉLIMINÉ** : le couplage est total, la décomposition est illusoire.

**BIF — Test de filtrage** :
- Baker p-adique (Yu, 2007) : v_p(2^S - 3^k) ≤ C·p·(log p)^2·log(2S)·log(3k) pour tout prime p ∤ 6.
- Application : si p^e || d(k) avec e ≥ 1, alors e ≤ C·p·(log p)^2·log(2S)·log(3k).
- Ceci borne la puissance de p dans d, mais ne donne AUCUNE information sur QUELS primes divisent d.
- Pour la factorisation de d(21) = 2^34 - 3^21 = 6 719 515 981, il faudrait un algorithme de factorisation (ECM, GNFS), pas Baker.
- **BIF AFFAIBLI** : Baker ne filtre pas les primes.

**Checkpoint S2** :
| Candidat | Renforcé/Affaibli ? | Mordant réel ? | Non-redondance ? | Statut de preuve ? | Décision |
|----------|:---:|:---:|:---:|:---:|------|
| SCR | AFFAIBLI | NON (ESS est uniforme) | OUI | Aucun progrès | TUER |
| HSB | ÉLIMINÉ | NON (couplage total) | OUI | Impossible | TUER |
| BIF | AFFAIBLI | NON (Baker ≠ factorisation) | PARTIEL | Aucun progrès | TUER |

**Décision** : Les 3 candidats sont mortellement affaiblis. Aucun ne progresse.

---

### S3 — Vérification historique + anti-rebranding

**Candidats actifs** : AUCUN (les 3 sont mortellement affaiblis)

**Vérification a posteriori** :

| Candidat | Test anti-rebranding | Résultat |
|----------|---------------------|----------|
| SCR | "Exploiter les coefficients dans ESS" est-il un angle déjà fermé ? | Non fermé explicitement, mais IMPLICITEMENT fermé car ESS est UNIFORME sur les coefficients. Pas un rebranding mais un CUL-DE-SAC structurel |
| HSB | "Décomposer via Horner" est-il un angle déjà fermé ? | Partiellement fermé par R80 (Horner = reformulation dans F_p). Dans Z, c'est un angle NOUVEAU mais le couplage le tue. Mort par STRUCTURE, pas par rebranding |
| BIF | "Baker filtre les primes" est-il un angle déjà fermé ? | Fermé implicitement par R81 (GZD : valuation ne filtre pas) + R76 (Baker = direction, pas outil directement applicable). Mort : REBRANDING PARTIEL de la direction Baker (R80) |

**Checkpoint S3** :
- SCR : cul-de-sac structurel (ESS uniforme)
- HSB : mort par couplage (structure, pas rebranding)
- BIF : rebranding partiel de la direction Baker

**Décision** : TUER les trois. Aucun candidat ne survit pour S4.

---

### S4 — Test de preuve / semi-formalisation

**Candidats actifs** : AUCUN

**Résultat** : Phase S4 est VACANTE. Il n'y a pas de candidat à semi-formaliser.

**Le seul résultat semi-formalisable est le calcul QCB** (section 6), qui est une VÉRIFICATION, pas un lemme nouveau.

**Checkpoint S4** :
- Statut de preuve : AUCUN progrès sur aucun candidat
- Faut-il tuer le pipeline ? OUI — aucun candidat ne survit.

**Décision** : ARRÊTER le pipeline. Outcome 3 : "aucun candidat ne dépasse les limites connues."

---

### S5 — Tournoi final et décision

**Candidats actifs** : AUCUN

**Classement final** :

| Rang | Candidat | Statut | Raison |
|:----:|----------|--------|--------|
| — | QCB | COMPLÉTÉ (vérification, pas candidat) | BTL enterré quantitativement |
| — | SCR | ÉLIMINÉ | ESS uniforme sur les coefficients, cul-de-sac |
| — | HSB | ÉLIMINÉ | Couplage total, décomposition illusoire |
| — | BIF | ÉLIMINÉ | Baker ≠ factorisation, rebranding partiel |

**Aucun survivant. Le tournoi est vide.**

**Décision S5** : SUSPENSION DE L'INNOVATION sur le front S-unit/Baker.

---

## 10. Résultats PHASE 4 / AXE E — Audit fail-closed

### Pour chaque candidat

**QCB** :
- Non redondant ? : N/A (vérification)
- Objet précis ? : OUI
- Lemme général ? : N/A
- Test de réfutation réel ? : N/A
- Statut de preuve progressé ? : OUI (calcul ESS complété)
- Mordant supérieur au cadre conceptuel ? : NON (c'est un calcul, pas un lemme)
- Résiste à l'historique ? : OUI
- **Statut : [COMPLÉTÉ]**
- **Statut de preuve : [CALCULÉ]**

**SCR** :
- Non redondant ? : OUI (angle nouveau)
- Objet précis ? : OUI
- Lemme général ? : NON (requiert un théorème ESS structuré inexistant)
- Test de réfutation réel ? : OUI (ESS est uniforme → SCR n'a pas de base)
- Statut de preuve progressé ? : NON
- Mordant supérieur au cadre conceptuel ? : NON
- Résiste à l'historique ? : OUI
- **Statut : [ÉLIMINÉ — cul-de-sac structurel]**
- **Statut de preuve : [BLOQUÉ]**

**HSB** :
- Non redondant ? : OUI
- Objet précis ? : OUI
- Lemme général ? : NON (couplage empêche la décomposition)
- Test de réfutation réel ? : OUI (couplage total prouvé)
- Statut de preuve progressé ? : NON
- Mordant supérieur au cadre conceptuel ? : NON
- Résiste à l'historique ? : OUI
- **Statut : [ÉLIMINÉ — structurellement bloqué]**
- **Statut de preuve : [BLOQUÉ]**

**BIF** :
- Non redondant ? : PARTIEL (direction Baker déjà identifiée R80)
- Objet précis ? : OUI
- Lemme général ? : NON (Baker ne filtre pas les primes)
- Test de réfutation réel ? : OUI (Baker borne les valuations, pas la factorisation)
- Statut de preuve progressé ? : NON
- Mordant supérieur au cadre conceptuel ? : NON
- Résiste à l'historique ? : NON (rebranding partiel)
- **Statut : [ÉLIMINÉ — rebranding partiel + cible mal identifiée]**
- **Statut de preuve : [BLOQUÉ]**

---

## 11. Résultats PHASE 4 / AXE F — Classement et impact programmatique

### Quel candidat gagne ?

**AUCUN.** Le tournoi est vide. Tous les candidats sont éliminés.

### Le programme a-t-il progressé ?

OUI, mais par ÉLIMINATION, pas par construction :

1. **BTL est définitivement enterré pour le gap** — le calcul ESS ferme cette voie quantitativement.
2. **La borne ESS est un MUR OBJECTIF** — ce n'est pas un diagnostic subjectif mais un calcul (exp(10^{148}) vs 10^9).
3. **La structure spécifique de corrSum (coefficients géométriques, monotonie) n'aide PAS** à améliorer les bornes S-unit — les théorèmes sont uniformes sur les coefficients.
4. **La décomposition de Horner dans Z ne découple PAS** l'équation — le couplage séquentiel est total.
5. **Baker ne filtre pas les primes** — il borne les valuations, ce qui est un problème différent.

### Quel mur a été entamé ?

**AUCUN mur n'a été entamé.** Mais un mur a été QUANTIFIÉ avec précision (la borne ESS), ce qui empêche les futurs rounds de perdre du temps sur le front S-unit/Baker dans sa forme actuelle.

### Seuil minimum pour justifier R84

Pour qu'un futur round théorique soit justifié, il faudrait :
1. Un outil QUANTITATIF réduisant la borne de exp(10^{148}) à ~10^9 (gain de 10^{148} ordres de grandeur)
2. OU un outil QUALITATIVEMENT DIFFÉRENT de la S-unit theory (pas une amélioration, une rupture)
3. OU un retour au front COMPUTATIONNEL (DP étendu au gap, avec factorisation de d(k) et techniques CRT)

---

## 12. Résultats PHASE 5 / AXE G — Décision finale

### Options et verdict

| Option | Applicable ? | Raison |
|--------|:---:|--------|
| Poursuivre (candidat mordant survit) | **NON** | Aucun candidat ne survit |
| Poursuivre avec réserve (candidat fragile) | **NON** | Aucun candidat, même fragile |
| **Suspendre l'innovation** | **OUI** | L'autonomie plus profonde ne produit pas de gain |
| Reformuler le front | PARTIEL | Le front est correctement formulé, c'est l'OUTIL qui manque |

### Décision finale : **SUSPENDRE L'INNOVATION THÉORIQUE SUR LE FRONT S-UNIT/BAKER**

### Questions obligatoires

**Q1. Quel candidat mérite R84 ?**
AUCUN. Il n'y a pas de candidat théorique viable sur le front actuel.

**Q2. Pourquoi n'est-il pas juste le moins mauvais ?**
N/A — le tournoi est vide.

**Q3. Condition de non-boucle pour R84 ?**
R84 ne doit PAS tenter d'améliorer les bornes S-unit/Evertse. Le gap quantitatif (10^{148} ordres de grandeur) est trop immense.

Si un R84 théorique est lancé, il doit :
- Soit trouver un outil QUALITATIVEMENT DIFFÉRENT (pas S-unit, pas Baker, pas sommes exponentielles)
- Soit explorer le front COMPUTATIONNEL (DP étendu, factorisation de d(k) pour k=21-41)
- Soit démontrer que le gap k=21-41 est HORS D'ATTEINTE des techniques actuelles (ce qui serait un résultat de diagnostic final)

**Q4. Qu'a réellement gagné le programme ?**
1. BTL est QUANTITATIVEMENT enterré (plus d'ambiguïté)
2. La borne ESS est un mur objectif et chiffré
3. Les coefficients géométriques et la monotonie ne réduisent PAS les bornes S-unit
4. Le couplage Horner dans Z est total
5. Baker ne filtre pas les primes
6. Le programme sait maintenant que TOUTES les voies théoriques testées (spectrale R72, bilinéaire R73, SAMC R74-R75, multiplicative R77, auto-référence R79, noyau F_p R80, extérieur GZD/APF R81, S-unit/Baker R82-R83) sont FERMÉES ou INSUFFISANTES

**Q5. Qu'est-ce qui doit être enterré sans ambiguïté ?**
| Piste | Statut | Définitif ? |
|-------|--------|:-----------:|
| BTL pour le gap | ENTERRÉ | OUI |
| S-unit bounds pour corrSum | INSUFFISANTES | OUI (tant que ESS ne progresse pas de 10^{148} ordres) |
| Horner décomposition dans Z | ILLUSOIRE | OUI (couplage prouvé) |
| Baker filtrage de primes | MAL CIBLÉ | OUI |
| SCR coefficients géométriques | CUL-DE-SAC | OUI (ESS uniforme) |

---

## 13. Objets concernés + Ladder of Proof

### BTL (Baker-Transcendence Lift) — STATUT FINAL

| Niveau | État |
|--------|------|
| Intuition | ✅ Baker exploite l'indépendance de 2 et 3 |
| Manque visé | ✅ Réduction somme → produit |
| Schéma d'objet | ✅ corrSum = m·d ↔ S-unit equation |
| Semi-formalisation | ✅ Non-dégénérescence prouvée (termes positifs) |
| Lemme candidat | ❌ BTL-L2 formulé mais borne ESS >> |Comp_mono| |
| Test de mordant | ❌ exp(10^{148}) vs 10^9 — insurmontable |
| Possibilité de preuve | ❌❌ Impossible avec techniques actuelles |

**Ladder** : L4 → RÉTROGRADÉ à L3 (semi-formalisé mais quantitativement mort)

### SCR (Structural Coefficient Rigidity)

| Niveau | État |
|--------|------|
| Intuition | ✅ Coefficients géométriques = structure spéciale |
| Schéma d'objet | ✅ Progression 3^{k-1-i} dans ESS |
| Semi-formalisation | ❌ ESS est uniforme, pas de théorème structuré |

**Ladder** : L2 (intuition + objet, bloqué structurellement)

### HSB (Horner Step Bound)

| Niveau | État |
|--------|------|
| Intuition | ✅ Décomposer en petites équations |
| Schéma d'objet | ✅ Récurrence H_j |
| Semi-formalisation | ❌ Couplage total empêche la décomposition |

**Ladder** : L2 (intuition + objet, réfuté par couplage)

### BIF (Baker-Informed Filtration)

| Niveau | État |
|--------|------|
| Intuition | ✅ Baker contraint les primes de d |
| Schéma d'objet | ❌ Baker borne les valuations, pas les primes |

**Ladder** : L1 (intuition, mal ciblé)

---

## 14. Ce qui est appris

1. **La borne ESS est un mur quantitatif chiffré** : exp(10^{148}) solutions autorisées par la théorie pour seulement 5.7×10^8 compositions monotones. Le ratio est astronomique — aucune amélioration technique raisonnable ne le comble.

2. **La théorie S-unit est UNIFORME sur les coefficients** : les progrès sur les bornes ESS (Evertse-Győry 2015, etc.) ne dépendent pas de la forme des coefficients a_i. La progression géométrique 3^{k-1-i} n'est pas exploitable dans ce cadre.

3. **La décomposition de Horner dans Z est illusoire** : le couplage séquentiel des H_j est TOTAL — chaque gap c_j affecte toute la chaîne. On ne peut pas factoriser la borne en un produit de bornes indépendantes.

4. **Baker ne filtre pas les primes** : le théorème de Baker (et ses extensions p-adiques) borne les valuations v_p(2^S - 3^k), pas l'ensemble des primes divisant d. La factorisation de d reste un problème computationnel non informé par Baker.

5. **Le programme a exploré TOUTES les voies théoriques accessibles** : spectrale (R72), bilinéaire (R73), sumset algébrique (R74-R75), causale (R76/R79), multiplicative (R77), noyau F_p (R80), extérieur Z (R81), S-unit/Baker (R82-R83). Toutes sont fermées ou insuffisantes.

6. **L'autonomie plus profonde ne suffit pas** : même avec 5 sous-rounds, 7 agents, et une liberté élargie, le pipeline autonome ne produit pas de candidat dépassant les limites connues. Ce n'est pas un défaut de méthode — c'est un fait sur la difficulté du problème.

---

## 15. Ce qui est fermé utilement

| Piste fermée | Raison | Impact |
|-------------|--------|--------|
| BTL pour le gap k=21-41 | Borne ESS exp(10^{148}) >> |Comp_mono| ≈ 10^9 | **FERME la voie S-unit** pour le gap |
| SCR (coefficients géométriques) | ESS uniforme sur les coefficients | Ferme l'espoir d'amélioration ESS via structure |
| HSB (décomposition Horner Z) | Couplage total des H_j | Ferme l'espoir de décomposition |
| BIF (Baker filtrage primes) | Baker ≠ factorisation | Ferme l'espoir d'utiliser Baker pour sélectionner des primes |
| Innovation théorique sur front S-unit/Baker | Tous les sous-angles épuisés | **SUSPEND** cette direction |

---

## 16. Ce qui est enterré

| Objet | Type de mort | Ce que la mort enseigne |
|-------|-------------|------------------------|
| BTL pour le gap | Trop faible (quantitativement) | Les bornes S-unit actuelles sont inutiles en régime n=23 ; il faudrait un gain de 10^{148} ordres de grandeur |
| SCR | Cul-de-sac structurel | Le Subspace Theorem est UNIFORME sur les hyperplans — la structure des coefficients est invisible |
| HSB | Structurellement bloqué | Le couplage séquentiel de la récurrence de Horner est irréductible dans Z |
| BIF | Mal ciblé | Baker borne des valuations, pas des factorisations — deux problèmes fondamentalement différents |

---

## 17. Autopsie des pistes fermées

### BTL pour le gap (Baker-Transcendence Lift, version quantitative)
- **Nom** : BTL (version gap k=21-41)
- **Type de mort** : Trop faible quantitativement
- **Cause du rejet** : La borne ESS pour n=23 termes et |S|=2 primes est exp(138^{69}·3) ≈ exp(10^{148}). Le nombre de compositions monotones pour k=21 est C(33,20) ≈ 5.73×10^8. Le ratio est exp(10^{148})/10^9, un nombre inconcevable. Aucune amélioration technique (polynomiale, exponentielle, doublement exponentielle en k) ne comble ce gouffre.
- **Ce que la mort enseigne** : Les théorèmes S-unit actuels sont des résultats de FINITUDE QUALITATIVE, pas de BORNE EFFECTIVE UTILE pour n >> 2. Leur force est dans la structure (finitude), pas dans la quantification (borne). Pour n=2, les bornes sont raisonnables (≤ 1029). Pour n ≥ 20, elles explosent en tour d'exponentielles.
- **Où cela redirige** : Vers le front computationnel (DP étendu pour d(k) avec k=21-41), ou vers l'attente de percées mathématiques fondamentales (amélioration de ESS, ou outil qualitativement différent).

### SCR (Structural Coefficient Rigidity)
- **Nom** : SCR
- **Type de mort** : Cul-de-sac structurel
- **Cause du rejet** : Le théorème d'Evertse-Schlickewei-Schmidt borne le nombre de solutions de a_1x_1+...+a_nx_n = 0 en S-unités, et cette borne est INDÉPENDANTE des coefficients a_i. La preuve passe par le Subspace Theorem (Schmidt 1972), qui énumère les sous-espaces propres contenant des solutions, et ce comptage ne dépend pas de l'hyperplan spécifique défini par les a_i. La progression géométrique des 3^{k-1-i} n'est pas visible dans la borne.
- **Ce que la mort enseigne** : Le Subspace Theorem est un outil GÉOMÉTRIQUE (comptage de sous-espaces) qui ignore l'ALGÈBRE des coefficients. Pour exploiter la structure des coefficients, il faudrait un outil algébrique différent — peut-être les formes de Thue, les récurrences linéaires (théorème de Skolem-Mahler-Lech), ou les équations de Pillai — mais aucun ne s'applique directement à notre cas de n >> 2 termes.
- **Où cela redirige** : Confirme que la voie S-unit est un mur pour n >> 2. Pas de redirection utile.

### HSB (Horner Step Bound)
- **Nom** : HSB
- **Type de mort** : Structurellement bloqué
- **Cause du rejet** : La récurrence H_j = 3^{k-1-j} + 2^{c_j}·H_{j+1} crée une chaîne de k-1 équations à 3 termes. Chaque équation contient H_j et H_{j+1} — les variables sont COUPLÉES séquentiellement. Si on résout de bas en haut, chaque substitution produit un H_0 qui est un POLYNÔME en toutes les variables (c_1,...,c_{k-1}). La condition H_0 ≡ 0 mod p est une SEULE congruence sur l'ensemble des gaps, pas k-1 congruences indépendantes. La décomposition produit l'illusion de k-1 petites équations alors qu'il y a une seule grande équation.
- **Ce que la mort enseigne** : Les récurrences linéaires à 2 termes sont décomposables (chaque étape indépendante). Les récurrences à 3 termes avec substitution sont COUPLÉES (chaque étape dépend de la suivante). Pour décomposer corrSum, il faudrait une FACTORISATION MULTIPLICATIVE (produit de termes indépendants), pas une décomposition additive (somme de termes couplés). Or corrSum est une somme, pas un produit — c'est le gap fondamental identifié en R82.
- **Où cela redirige** : Confirme que le gap somme↔produit est irréductible. La structure de Horner ne le franchit pas.

### BIF (Baker-Informed Filtration)
- **Nom** : BIF
- **Type de mort** : Mal ciblé
- **Cause du rejet** : Baker borne |2^S - 3^k| par le bas (archimedean) et v_p(2^S - 3^k) par le haut (p-adic). Ces bornes contraignent la TAILLE et les VALUATIONS de d, pas la liste de ses FACTEURS PREMIERS. La factorisation de nombres de la forme 2^S - 3^k est un problème de théorie algorithmique des nombres (tables de Cunningham, ECM, NFS), pas de transcendance. Baker et la factorisation opèrent dans des espaces conceptuels différents.
- **Ce que la mort enseigne** : La théorie de la transcendance (Baker) et la théorie de la factorisation sont des branches DISTINCTES de la théorie des nombres. Connecter l'une à l'autre (Baker → factorisation) est un problème ouvert en soi (connu sous le nom de "problèmes effectifs" en théorie algébrique des nombres). On ne peut pas espérer utiliser Baker pour informer la factorisation de d sans résoudre d'abord ce problème de connexion.
- **Où cela redirige** : Vers le front computationnel. La factorisation de d(k) pour k=21-41 est un problème NUMÉRIQUE, pas théorique.

---

## 18. Survivant pour R84

**AUCUN survivant théorique.**

Le front S-unit/Baker est épuisé. L'innovation théorique est suspendue.

### Directions possibles pour un éventuel R84

| Direction | Type | Faisabilité | Condition |
|-----------|------|:-----------:|-----------|
| **DP étendu pour k=21** | Computationnel | 8/10 | Factoriser d(21) = 6 719 515 981, puis DP mod chaque facteur premier |
| **MITM sur d(k)** | Computationnel | 6/10 | Implémenter meet-in-the-middle pour d de taille ~10^{10} |
| **Attente de percée mathématique** | Théorique | 0/10 (passif) | Amélioration ESS de 10^{148} ordres, ou outil qualitativement nouveau |
| **Diagnostic de clôture** | Méta | 7/10 | Documenter formellement que le gap k=21-41 est hors d'atteinte des techniques théoriques actuelles |

### Recommandation

Si le projet veut progresser vers la RÉSOLUTION du gap, la voie la plus prometteuse est **COMPUTATIONNELLE** :
1. Factoriser d(k) pour k=21 (nombre ~6.7×10^9, faisable avec ECM)
2. Pour chaque facteur premier p | d(21), exécuter DP mod p
3. Si un facteur premier p bloque (N_0(p) = 0), k=21 est résolu
4. Étendre à k=22, 23, ..., 41

Cette voie est le prolongement naturel du Bloc 2 (qui a résolu k=3..20 par DP+CRT).

---

## 19. Risques / Limites

1. **Risque d'interprétation** : BTL est enterré POUR LE GAP, pas en tant que résultat structurel. La connexion corrSum → S-unit equation reste un pont mathématique valide, potentiellement utile si les bornes ESS progressent massivement à l'avenir.

2. **Risque de conclusion prématurée** : "toutes les voies théoriques sont fermées" pourrait être un artefact de l'espace d'exploration limité. Un mathématicien humain pourrait concevoir une approche qualitativement différente non explorée ici.

3. **Limite de l'autonomie** : R83 montre que l'autonomie plus profonde (5 sous-rounds, 7 agents) ne produit pas de gain quand le problème est fondamentalement HORS DE PORTÉE des outils disponibles. L'autonomie est utile pour EXPLORER et ÉLIMINER, pas pour INVENTER de nouvelles mathématiques.

4. **Factorisation de d(k)** : pour k=21, d(21) ≈ 6.7×10^9 est un nombre de 10 chiffres — facilement factorisable. Pour k=41, d(41) ≈ 2^{65} - 3^{41} ≈ 10^{19}, encore faisable mais les facteurs premiers pourraient être très grands. La faisabilité du DP dépend de la taille des facteurs premiers.

5. **Incertitude fondamentale** : il est possible que le gap k=21-41 ne soit résoluble NI théoriquement NI computationnellement avec les moyens actuels. C'est le cas le plus pessimiste mais il doit être envisagé.

---

## 20. Verdict final

### Score : 8/10

**Justification** :
- Le calcul ESS est un résultat DÉCISIF (10/10) : BTL est enterré quantitativement, fin de l'ambiguïté
- Le pipeline autonome est EXEMPLAIRE (9/10) : 5 sous-rounds, checkpoints respectés, STOP appliqués
- Les candidats sont HONNÊTEMENT éliminés (9/10) : raisons structurelles précises, pas de fausse survie
- La suspension est PROPRE (10/10) : pas de forçage, pas de "candidat de consolation"
- Le gain est par ÉLIMINATION, pas par construction (6/10) : le programme sait ce qui NE MARCHE PAS, mais n'a pas de nouvelle direction

Le 8 (pas 7) reflète que le gain informationnel est PLUS FORT que celui de R82 : on passe de "BTL qualifié avec réserve" à "BTL enterré avec calcul quantitatif". Le programme est désormais DÉCIDÉ sur le front théorique — la voie S-unit/Baker est close.

### Gain net du programme R67→R83

L'arc R67→R83 (17 rounds) a produit :
1. K-lite prouvé universellement pour ⟨g²⟩ (R64-R66), transfert partiel vers Collatz (R67-R68)
2. K-lite non requis par le JT (R69) — requalification définitive
3. SOH objet canonique pour k≥3 (R71), voie spectrale tuée (R72), bilinéaire tuée (R73)
4. SAMC reformulation correcte (R74), aucun mécanisme (R75), causes sources identifiées (R76)
5. Multiplicatif pur insuffisant (R77), auto-référence = cause source (R79)
6. Noyau irréductible dans F_p (R80), faille add/mult (R81)
7. Connexion S-unit (R82), S-unit enterrée quantitativement (R83)

**Bilan honnête** : 17 rounds, ZÉRO percée, mais une CARTE COMPLÈTE des impasses et un diagnostic précis de la difficulté. Le gap k=21-41 est identifié comme un problème dont la difficulté dépasse les outils théoriques actuellement connus dans ce projet.

---

## 21. Registre FAIL-CLOSED

| Objet | Statut |
|-------|--------|
| Borne ESS pour k=21 | [CALCULÉE — exp(10^{148})] |
| BTL pour le gap k=21-41 | [ENTERRÉ — quantitativement insurmontable] |
| BTL comme résultat structurel | [OBJET RÉEL — connexion valide mais inutile quantitativement] |
| SCR (coefficients géométriques) | [ÉLIMINÉ — cul-de-sac structurel] |
| HSB (décomposition Horner Z) | [ÉLIMINÉ — couplage total] |
| BIF (Baker filtrage primes) | [ÉLIMINÉ — mal ciblé] |
| Innovation théorique front S-unit/Baker | [SUSPENDUE] |
| Non-dégénérescence (termes positifs) | [FORTEMENT ÉTAYÉ — résultat de R82 confirmé] |
| Gap somme↔produit | [OBJET RÉEL — confirmé comme verrou irréductible] |
| Voie computationnelle DP étendu | [OUVERTE — recommandée] |
| Factorisation de d(k) pour k=21-41 | [OUVERTE — prérequis computationnel] |
| Diagnostic de clôture théorique | [À CONSIDÉRER] |

---

## 22. Critères de réussite (auto-évaluation)

| Critère | Passé ? | Commentaire |
|---------|:-------:|-------------|
| PASS-1 : type de lemme formulé | ✅ | "Pont quantitatif somme→produit avec f(k) < C(S-1,k-1)" |
| PASS-2 : ≤ 4 candidats dans le pipeline | ✅ | 4 candidats exactement (QCB, SCR, HSB, BIF) |
| PASS-3 : objet + lemme + réfutation + victoire | ✅ | Pour chaque candidat (sauf QCB = vérification) |
| PASS-4 : tri réel et non rhétorique | ✅ | 4 éliminés pour raisons structurelles précises |
| PASS-5 : survivant unique ou suspension propre | ✅ | SUSPENSION propre (outcome 3) |
| PASS-6 : statut de preuve honnête | ✅ | AUCUN candidat n'a progressé en preuve — honnêtement documenté |

**6/6 critères passés.** Le round est méthodologiquement réussi, même si le résultat substantiel est une suspension.
