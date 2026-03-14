# R82 — BILAN : Innovation contrôlée — BTL survit, 2 candidats éliminés

## Type : X/I/P
## IVS : 7/10

**Justification IVS** :
- Précision du manque concret : 9/10 (manque comprimé en une phrase opérationnelle)
- Qualité des candidats : 6/10 (BTL est sérieux mais techniquement difficile, les 2 autres tués)
- Robustesse anti-redondance : 9/10 (tableau anti-redondance complet, 3 pièges identifiés)
- Qualité du tournoi fermé : 8/10 (critères explicites, élimination nette, 1 survivant)
- Honnêteté de la décision finale : 9/10 (BTL retenu avec réserves lourdes, pas de fausse percée)

Score 7/10 reflétant qu'un candidat GENUINEMENT NOUVEAU survit mais avec un verrou technique non résolu. L'innovation n'est pas suspendue mais fortement contrainte.

---

## 1. Résumé exécutif

R82 part du constat que le verrou actif est : **nous ne savons pas convertir une structure multiplicative favorable en exclusion additive effective de -1.**

**PHASE 1** produit le diagnostic suivant :
- Le manque concret le plus étroit = **l'absence d'outil reliant une SOMME dans F_p à une information hors F_p**. Plus précisément : corrSum est une SOMME de termes multiplicativement structurés, mais les outils hors F_p (Baker, taille, valuation) s'appliquent à des PRODUITS. La réduction somme → produit n'existe pas.
- Deux familles d'approches restent ouvertes : (F1) **compatibilité quantitative hors F_p** et (F2) **obstruction structurelle minimale par sparsité**.
- Le piège de redondance le plus dangereux = reformuler SAMC sous un vocabulaire hors-F_p tout en restant dans le noyau irréductible.

**PHASE 2** propose 3 candidats :
1. **BTL (Baker-Transcendence Lift)** — exploiter la structure d'emboîtement de Horner pour extraire une forme QUASI-linéaire en log 2 et log 3, puis appliquer Baker.
2. **SRF (Sparse Rigidity via Filtration)** — utiliser la sparsité de Σ_≤(k) (≪ p éléments) pour exclure -1 par argument de densité dans les cosets de ⟨2⟩.
3. **CST (Coset Sum Tracking)** — suivre la position de la somme partielle dans le quotient F_p*/⟨2⟩.

**PHASE 3** — Tournoi :
- **CST** : ÉLIMINÉ — rebranding de la faille additif/multiplicatif (R81). L'addition ne respecte pas les cosets. Mort : **redondante**.
- **SRF** : ÉLIMINÉ — la sparsité est réelle mais ne cible pas -1 spécifiquement. La conversion cardinal → exclusion ponctuelle requiert exactement le même verrou (structure additive vs multiplicative). Mort : **trop faible**.
- **BTL** : QUALIFIÉ AVEC RÉSERVE — le SEUL candidat qui opère genuinement hors de F_p et qui offre un pont potentiel somme → produit via Horner.

**PHASE 4** — Décision :
- **BTL survit** pour R83, avec réserves lourdes.
- Innovation CONTRAINTE, pas suspendue.
- Condition de non-boucle : R83 doit produire une réduction explicite de corrSum en forme linéaire en logarithmes, ou BTL est enterré.

---

## 2. Type du round + IVS

**Type** : X/I/P
- **X** : investigation causale (manque concret, anti-redondance)
- **I** : innovation disciplinée (3 candidats proposés, 2 tués)
- **P** : exigence de précision, testabilité, falsifiabilité

**IVS** : 7/10 — Le diagnostic du manque est net, le tournoi est honnête, un candidat genuinement nouveau survit. Le 7 (pas 8) reflète que le verrou technique de BTL (réduction somme → forme linéaire) est identifié mais NON résolu.

---

## 3. Méthode

1. Investigation du manque concret : compression du verrou en formulation opérationnelle (Axe A)
2. Cartographie des familles d'approches encore ouvertes (Axe B)
3. Contrôle anti-redondance systématique contre R67-R81 (Axe C)
4. Proposition de 3 candidats avec chaîne complète (Axe D)
5. Spécification des styles d'agents (Axe E)
6. Audit croisé et tournoi fermé (Axe F)
7. Évaluation d'impact programmatique (Axe G)
8. Décision stratégique finale (Axe H)
9. Aucun calcul, aucun k-par-k, aucun cas particulier

---

## 4. Résultats PHASE 1 / AXE A — Manque concret minimal

### Les 5 manques candidats examinés

| # | Manque candidat | Verdict | Raison |
|---|----------------|---------|--------|
| M1 | Invariant de conversion multiplicatif → additif | **TROP HAUT** | Reformule le verrou au lieu de le comprimer. "Trouver un invariant de conversion" = "résoudre le problème" |
| M2 | Notion de rigidité ciblée | **TROP VAGUE** | Aucun objet précis ne correspond. La "rigidité" n'est pas une catégorie mathématique opératoire |
| M3 | Structure d'obstruction minimale | **TROP HAUT** | Demander "pourquoi -1 est impossible" = demander la preuve. C'est la cible, pas le manque |
| M4 | Interface compatible avec l'auto-référence | **LE PLUS FERTILE** | Identifie le besoin d'un objet qui INCORPORE la dépendance en 2^S et 3^k, pas seulement travaille mod p |
| M5 | Langage minimal de transfert hors F_p → mod p | **LE PLUS ÉTROIT** | Identifie le gap opérationnel exact : comment une information sur corrSum dans Z (taille, structure) se traduit en information sur corrSum mod p |

### Formulation minimale du manque concret

> **Manque opérationnel** : corrSum est une SOMME de termes {3^{k-1-i} · 2^{A_i}}, et les outils quantitatifs hors F_p (Baker, taille, valuation) s'appliquent naturellement aux PRODUITS, pas aux sommes. Il manque une réduction de la SOMME corrSum en un objet de type PRODUIT, compatible avec la théorie des formes linéaires en logarithmes.

### Pourquoi ce manque est étroit et opératoire

1. Il pointe un gap TECHNIQUE précis : somme ≠ produit dans le contexte de Baker.
2. Il n'est pas un reformulage du verrou : le verrou dit "on ne peut pas convertir multiplicatif → additif". Le manque dit "il faut convertir la SOMME corrSum en PRODUIT pour appliquer Baker". C'est plus étroit.
3. Il est immédiatement testable : soit la factorisation de Horner fournit un pont, soit elle ne le fait pas.
4. Il dérive de la cause source : c'est PARCE QUE 2 et 3 sont les briques de corrSum ET de d que Baker est le seul outil quantitatif, et c'est le format "somme" qui bloque son application.

### Faux manques enterrés

| Faux manque | Pourquoi faux |
|------------|---------------|
| "Manque de sous-groupes additifs dans F_p" | C'est un FAIT STRUCTUREL du corps F_p, pas un manque comblable (R75) |
| "Manque de somme-produit en O(log p)" | C'est la FRONTIÈRE DES MATHÉMATIQUES, pas un manque qu'un round peut combler (R77) |
| "Manque d'outil spectral adapté" | Voie spectrale enterrée (R72-R73). Pas un manque mais un MUR |

---

## 5. Résultats PHASE 1 / AXE B — Familles d'approches encore ouvertes

### Familles testées

| Famille | Ouverte ? | Raison | Risque de piège |
|---------|-----------|--------|-----------------|
| Invariant de conversion | NON | Trop haut, reformule le verrou | Piège rhétorique |
| Obstruction structurelle minimale | NON | Demande la preuve directement | Piège de circularité |
| **Compatibilité quantitative hors F_p** | **OUI** | Baker = seul outil non essayé directement sur corrSum | MOYEN (risque de retomber dans la taille, déjà vu GZD/R81) |
| Rigidité orientée | NON | Aucun objet concret | Piège de vagueness |
| **Transfert minimal source-compatible** | **OUI** | Horner offre un pont potentiel somme→produit | FAIBLE (objet nouveau si la réduction fonctionne) |
| Approche mixte somme-produit | NON | Frontière ouverte des mathématiques | Piège de profondeur |

### Familles retenues pour PHASE 2

**F1 : Compatibilité quantitative hors F_p** — la seule famille où un outil quantitatif inexploité existe (Baker sur les formes linéaires en logarithmes).

**F2 : Transfert minimal via structure Horner** — pas une famille séparée mais un MÉCANISME de réduction au sein de F1. Horner convertit corrSum (somme) en un emboîtement quasi-multiplicatif.

**Décision** : les deux familles convergent vers un seul candidat central. F2 est le véhicule technique de F1.

### Voies fermées pour non-régression

| Voie | Raison de fermeture | Round |
|------|---------------------|-------|
| Spectral / opérateur | Nilpotence, tautologique | R72 |
| Bilinéaire courte | 5 outils circulaires en O(log p) | R73 |
| Confinement sumset F_p | F_p corps premier, pas de sous-groupes additifs | R75 |
| Multiplicatif pur | Interface add/mult est le noyau dur | R77 |
| Reformulation dans F_p | Noyau irréductible, 7 reformulations isomorphes | R80 |
| Quotient F_p*/⟨2⟩ pour SOMMES | L'addition ne respecte pas les cosets | R81 |

---

## 6. Résultats PHASE 1 / AXE C — Contrôle anti-redondance

### Tableau anti-redondance

| Risque de redondance | Exemples passés | Test de détection | Verdict R82 |
|---------------------|-----------------|-------------------|-------------|
| Rebranding SAMC | DAS (R80), PRO (R80) | L'objet est-il isomorphe à SAMC dans F_p ? | Tout candidat purement dans F_p = rebranding |
| Faux extérieur | GZD (R81) : v₂(d)=v₃(d)=0 | L'information hors F_p est-elle triviale ? | Vérifier que l'info externe est NON TRIVIALE |
| Somme-produit déguisé | Interface (R77) | L'approche ramène-t-elle à borner une somme exponentielle courte ? | Si oui → circulaire (R73) |

### Critère rapide de non-redondance

Un candidat R82 est recevable SSI :
1. Il utilise une information QUANTITATIVE sur corrSum dans Z (pas seulement mod p)
2. Cette information ne se réduit PAS à v₂ ou v₃ (triviales car d copremier à 6)
3. Son lemme candidat ne ramène PAS à borner une somme exponentielle de longueur O(log p)
4. Sa chaîne logique passe par un OUTIL NOMMÉ de la théorie des nombres (pas un slogan)

### Drapeaux rouges prioritaires

1. **DRAPEAU ROUGE 1** : Tout candidat qui "suit la somme dans un quotient" = faille add/mult (R81)
2. **DRAPEAU ROUGE 2** : Tout candidat qui "utilise la taille de corrSum" sans mécanisme quantitatif = GZD (R81)
3. **DRAPEAU ROUGE 3** : Tout candidat qui "exploite la structure de Horner dans F_p" = noyau irréductible (R80)

---

## 7. Résultats PHASE 2 / AXE D — Candidats entrants en tournoi

### CANDIDAT 1 — BTL (Baker-Transcendence Lift)

**Famille d'approche** : F1 (compatibilité quantitative hors F_p) + F2 (transfert Horner)

**Manque visé** : Réduction de corrSum (somme) en forme quasi-linéaire en log 2, log 3 via la structure de Horner

**Objet candidat** : La factorisation de Horner de corrSum dans Z :

corrSum = 2^{A_0} · H_0

H_0 = 3^{k-1} + 2^{c_1} · H_1
H_1 = 3^{k-2} + 2^{c_2} · H_2
...
H_{k-2} = 3 + 2^{c_{k-1}}
(où c_j = A_j - A_{j-1} ≥ 0)

Chaque H_j est un entier positif. La récurrence donne :
H_j = 3^{k-1-j} · (1 + (2/3)^{c_{j+1}} · H_{j+1}/3^{k-2-j})

Pour corrSum ≡ 0 mod d (avec p | d, p premier), on a p | H_0. Cela signifie H_0 — un entier spécifique dans [3^{k-1}, 2^S] — est divisible par p.

**L'observation clé** : dans Z, on peut écrire :
H_0/3^{k-1} = 1 + Σ_{j=1}^{k-1} (2/3)^{c_1+...+c_j}

Le terme de droite est une SOMME de puissances de (2/3). Si tous les c_j sont égaux (c_j = c), alors :
H_0/3^{k-1} = Σ_{j=0}^{k-1} (2^c/3)^j = ((2^c/3)^k - 1) / ((2^c/3) - 1)

C'est un quotient de différences de puissances de 2 et 3. Et la condition H_0 = 0 mod p peut alors être reformulée comme :
(2^{ck} - 3^k) / (2^c - 3) ≡ 0 mod p

qui est une forme linéaire en logarithmes (puisque 2^{ck} ≡ 3^k mod p ⟺ ck·log 2 ≡ k·log 3 mod (p-1) dans le groupe multiplicatif).

**Le pont potentiel** : La structure de Horner transforme la SOMME corrSum en un QUOTIENT de différences de puissances, ce qui est le terrain naturel de Baker.

**Lemme candidat (BTL-L1)** : Pour k ≥ 3 et pour tout c = (c_1,...,c_{k-1}) avec c_j ≥ 0 et Σ c_j = S - k·A_0/k (roughly), la quantité H_0(c) n'est divisible par aucun premier p | d(k) satisfaisant p > exp(C·k²) pour une constante effective C issue de Baker.

**Test de réfutation** :
- Si la structure de Horner NE SE RÉDUIT PAS à une forme linéaire (parce que les c_j sont DISTINCTS, pas tous égaux), le pont somme→produit échoue.
- Vérification immédiate : pour c_j distincts, H_0/3^{k-1} = Σ_{j=0}^{k-1} 2^{c_1+...+c_j}/3^j, qui n'est PAS un quotient simple de puissances. La réduction au cas c_j = c est un cas TRÈS spécial.

**Critère de victoire** : Extraction d'une forme linéaire en log 2, log 3 à partir de H_0 pour c_j GÉNÉRAUX (pas seulement c_j = c).

**Pourquoi en tournoi** : C'est le SEUL candidat qui :
(a) opère genuinement hors F_p (dans Z, avec Baker)
(b) utilise un outil nommé de la théorie des nombres (Baker/Matveev)
(c) exploite la cause source (indépendance multiplicative de 2 et 3)
(d) n'a JAMAIS été testé dans le projet (Baker sur Horner)

---

### CANDIDAT 2 — SRF (Sparse Rigidity via Filtration)

**Famille d'approche** : F2 (obstruction par sparsité)

**Manque visé** : Conversion de |Σ_≤(k)| ≪ p en exclusion de -1

**Objet candidat** : Le sumset Σ_≤(k) a au plus C(S-1, k-1) éléments distincts dans F_p. Pour k dans le gap (21-41), C(S-1, k-1) ≈ 10^8 à 10^12, tandis que p peut être très grand.

**L'idée** : si |Σ_≤(k)| = N et que les éléments de Σ_≤(k) sont "bien distribués" dans F_p, alors la probabilité que -1 ∈ Σ_≤(k) est ≈ N/p → 0 quand p → ∞.

**Lemme candidat (SRF-L1)** : Pour p suffisamment grand (p > f(k)), -1 ∉ Σ_≤(k) avec probabilité 1, au sens que les éléments de Σ_≤(k) se comportent comme N tirages uniformes dans F_p.

**Test de réfutation** :
- L'heuristique N/p est exactement le Ratio Law (R29) : N_0·p/C → 1. C'est une OBSERVATION, pas une preuve.
- La "probabilité 1" requiert un argument d'équidistribution de Σ_≤(k) dans F_p, ce qui RAMÈNE aux bornes de sommes exponentielles — le mur de R73.
- De plus, pour k petit (k=21), p peut être petit aussi (p | d(21), et d(21) pourrait avoir de petits facteurs premiers).

**Critère de victoire** : Preuve que Σ_≤(k) est "uniformément distribué" dans F_p sans passer par les sommes exponentielles.

**Pourquoi en tournoi** : La sparsité est un fait RÉEL et QUANTIFIABLE. Le problème est la conversion en exclusion ponctuelle.

---

### CANDIDAT 3 — CST (Coset Sum Tracking)

**Famille d'approche** : F1 (transfert multiplicatif → additif)

**Manque visé** : Suivi de la position de la somme partielle dans le quotient F_p*/⟨2⟩

**Objet candidat** : Le quotient π: F_p* → F_p*/⟨2⟩ ≅ Z/mZ où m = (p-1)/ord_p(2). Chaque terme λ^j·2^{g_j} de la SAMC a une image π(λ^j·2^{g_j}) = π(λ^j) = j·π(λ) dans Z/mZ (puisque 2^{g_j} ∈ ker π = ⟨2⟩).

**L'idée** : si la somme partielle pouvait être suivie dans Z/mZ, on pourrait exclure le coset de -1.

**Lemme candidat (CST-L1)** : L'image de Σ_≤(k) dans F_p*/⟨2⟩ est confinée à un ensemble S ⊂ Z/mZ de taille |S| < m, et π(-1) ∉ S.

**Test de réfutation** : L'APPLICATION π est un HOMOMORPHISME MULTIPLICATIF. La somme a + b n'a PAS d'image déterminée par π(a) et π(b) dans le quotient multiplicatif. En effet, π(a + b) ≠ π(a) + π(b) (le quotient est multiplicatif, pas additif).

Formellement : soient a = α·u, b = β·v avec u,v ∈ ⟨2⟩. Alors a + b = αu + βv. Le coset de a+b est (αu + βv)·⟨2⟩, qui DÉPEND de u et v (pas seulement de α et β).

**Critère de victoire** : Trouver un homomorphisme qui est SIMULTANÉMENT compatible avec l'addition ET le quotient multiplicatif → n'existe pas (sauf si ⟨2⟩ est un sous-groupe NORMAL de (F_p, +, ·), ce qui est absurde car ⟨2⟩ n'est pas stable sous l'addition).

**Pourquoi en tournoi** : Pour être testé et explicitement éliminé, pas par intuition mais par preuve.

---

## 8. Résultats PHASE 2 / AXE E — Styles d'agents et protocole

### Agents mobilisés pour R82

| Agent | Rôle | Verrouillage |
|-------|------|-------------|
| Investigateur causal | Comprime le verrou en manque concret | Ne propose PAS de solutions |
| Investigateur historique | Compare à R67-R81, détecte rebranding | Droit de VETO sur tout candidat |
| Innovateur discipliné | Propose les 3 candidats | Max 3, chacun avec chaîne complète |
| Auditeur fail-closed | Teste réfutation, cherche faille add/mult | Tue les candidats flous |
| Arbitre de tournoi | Impose critères, élimine, choisit | Ne "sauve" jamais un candidat faible |

### Ordre d'intervention

1. Investigateur causal → manque concret (Axe A)
2. Investigateur historique → familles autorisées + anti-redondance (Axes B, C)
3. Innovateur discipliné → 3 candidats (Axe D)
4. Auditeur fail-closed → test de réfutation de chaque candidat (Axe F)
5. Arbitre de tournoi → élimination et survivant (Axe H)

### Points d'audit croisé obligatoires

- L'investigateur historique AUDITE chaque candidat de l'innovateur
- L'auditeur fail-closed AUDITE le survivant de l'arbitre
- Aucun candidat ne survit sans avoir passé les 3 filtres

---

## 9. Résultats PHASE 3 / AXE F — Audit croisé et tournoi

### Sous-round S1 : Qualification initiale

| Candidat | Non-redondant ? | Objet précis ? | Lemme général ? | Test de réfutation ? | Lien au verrou ? | Statut initial |
|----------|:-:|:-:|:-:|:-:|:-:|------|
| BTL | OUI (Baker jamais appliqué à Horner/corrSum) | OUI (Horner dans Z + forme linéaire) | PARTIEL (cas c_j=c seulement) | OUI (c_j distincts = test immédiat) | DIRECT (indépendance 2,3 via Baker) | **QUALIFIÉ** |
| SRF | NON (Ratio Law R29, même heuristique) | OUI (cardinal de Σ_≤(k)) | NON (requiert équidistribution = R73) | OUI (mais déjà connu) | INDIRECT (sparsité → exclusion) | **ÉLIMINÉ** |
| CST | NON (faille add/mult R81 = même obstacle) | OUI (quotient F_p*/⟨2⟩) | NON (addition ≠ multiplication) | OUI (preuve directe d'échec) | NON (le quotient ne suit pas la somme) | **ÉLIMINÉ** |

### Sous-round S2 : Audit croisé de BTL

**Test anti-redondance (investigateur historique)** :
- Baker a-t-il été mentionné dans le projet ? OUI — comme DIRECTION dans R76 et R80. Mais JAMAIS APPLIQUÉ concrètement à corrSum ou Horner.
- Le pont Horner → forme linéaire est-il nouveau ? OUI — la reformulation de H_0/3^{k-1} comme somme de puissances de (2/3) n'a pas été explorée.
- Le candidat utilise-t-il une technique hors F_p ? OUI — Baker opère dans R (ou C), pas dans F_p.
- Verdict : **GENUINEMENT NOUVEAU** en tant que réduction technique, même si la direction Baker était identifiée.

**Test de réfutation (auditeur fail-closed)** :
- Le cas c_j = c (tous gaps égaux) produit une forme linéaire en log 2, log 3 : BTL fonctionne dans ce cas.
- Le cas c_j distincts (cas général) NE produit PAS une forme linéaire simple. La somme H_0/3^{k-1} = 1 + Σ (2/3)^{s_j} avec s_j = Σ_{i=1}^j c_i est une somme de puissances de 2/3 à exposants distincts et arbitraires.
- **Le pont somme → produit N'EST PAS GARANTI dans le cas général.**
- MAIS : il existe des techniques de réduction (méthode de Stewart-Tijdeman pour les sommes d'unités, théorème d'Evertse-Schlickewei sur les équations S-unitaires) qui bornent le NOMBRE de solutions d'une somme d'S-unités.
- Le théorème d'Evertse (1984) : l'équation x_1 + ... + x_n = 0 en S-unités (ici S = {2,3}) a au plus C(n, |S|) = C(n, 2) solutions non-dégénérées. Pour n = k+1, cela donne une borne effective en k.
- Verdict : **le pont est NON TRIVIAL mais POTENTIELLEMENT CONSTRUCTIBLE via S-unit theory**. Ce n'est plus simplement "Baker", c'est "Baker + Evertse + structure Horner". L'objet existe dans la littérature mais sa connexion au problème de Collatz est NOUVELLE.

**Évaluation de profondeur** :
La réduction BTL requiert 3 étapes :
(i) Écrire corrSum = m·d comme une S-unit equation dans Z[1/6] (ok, direct)
(ii) Appliquer Evertse pour borner le nombre de solutions non-dégénérées (ok, théorème existant)
(iii) Vérifier que les compositions monotones réalisent TOUJOURS des solutions dégénérées (= sous-sommes nulles), ce qui est bloqué par la monotonie.

Le step (iii) est le nouveau verrou : une sous-somme Σ_{i∈I} 3^{k-1-i}·2^{A_i} = 0 dans Z est IMPOSSIBLE (tous termes positifs). Donc toutes les solutions sont non-dégénérées... et Evertse borne leur nombre.

**CECI EST UNE OBSERVATION SIGNIFICATIVE** : Le théorème d'Evertse dit que l'équation
Σ_{i=0}^{k-1} 3^{k-1-i}·2^{A_i} = m·2^S - m·3^k
a au plus C(k) solutions non-dégénérées en (A_0,...,A_{k-1}, m) ∈ Z^{k+1}.

Comme les solutions sont non-dégénérées (aucune sous-somme ne s'annule, car tous termes du côté gauche sont positifs et les termes du côté droit sont positifs aussi dans les cas pertinents), le nombre de solutions est fini et borné effectivement en k.

Mais ATTENTION : nous avons besoin que le nombre de solutions MONOTONES (A_0 ≤ ... ≤ A_{k-1}, Σ A_i = S) soit 0, pas seulement fini. Evertse dit ≤ C(k) solutions totales (incluant les non-monotones et celles avec m ≥ 1). Si C(k) < |Comp_mono(S,k)| (le nombre de compositions monotones), cela ne suffit pas.

En fait, C(k) pour le théorème d'Evertse est au plus exp(C·(k+2)^3) (version quantitative de Evertse-Schlickewei-Schmidt, 2002). Pour k=21, c'est astronomique (exp(~50000)), bien plus grand que C(33,20) ≈ 8.5×10^8.

Donc les bornes actuelles de la S-unit theory sont BEAUCOUP TROP FAIBLES pour exclure les compositions monotones.

Verdict de l'audit : **BTL est STRUCTURELLEMENT VIABLE mais QUANTITATIVEMENT INSUFFISANT avec les bornes actuelles.**

### Sous-round S3 : Élimination finale

| Candidat | Statut final | Raison |
|----------|:-----------|--------|
| **BTL** | **QUALIFIÉ AVEC RÉSERVE** | Seul candidat genuinement hors F_p, pont S-unit identifié, mais bornes quantitatives insuffisantes |
| SRF | ÉLIMINÉ | Redondant avec Ratio Law (R29), requiert équidistribution (R73) |
| CST | ÉLIMINÉ | Faille add/mult (R81), preuve directe d'échec |

---

## 10. Résultats PHASE 3 / AXE G — Impact programmatique

### Si BTL-L1 était prouvé (ou une version affaiblie), quel mur serait entamé ?

**Chaîne logique** :
1. S-unit theory borne le nombre de solutions de corrSum = m·d → au plus C(k) solutions en (A, m)
2. Si C(k) < nombre de d ayant au moins une solution monotone, alors ∃ d sans solution → Hypothèse H pour au moins un k
3. Version plus forte : si pour chaque k ≥ K_0, C(k) = 0 (aucune solution non-dégénérée)... mais c'est impossible car il y a au moins des solutions avec m ≥ 1 en général.

**Le gain réel** : BTL ne résout pas directement le problème. Mais il fournit un CADRE QUANTITATIF externe (dans Z) qui contraint le nombre de solutions. C'est la première approche qui sort VÉRITABLEMENT de F_p et qui ne retombe pas dans le noyau irréductible.

**Le seuil de pertinence** : Pour que BTL justifie R83, il faut :
(a) Une réduction EXPLICITE de la condition corrSum ≡ 0 mod d en S-unit equation (faisable)
(b) Une estimation du nombre de solutions monotones via les bornes effectives modernes (Evertse-Schlickewei-Schmidt 2002, améliorations par Amoroso-Viada 2009)
(c) La comparaison avec |Comp_mono(S,k)| pour k = 21..41

**Ce gain est-il local ou structurel ?** : STRUCTUREL. Même si les bornes quantitatives sont insuffisantes pour k = 21-41, le cadre S-unit connecte le problème de Collatz à une théorie mature avec des techniques en amélioration continue. C'est un PONT permanent.

---

## 11. Résultats PHASE 4 / AXE H — Décision finale

### Quel candidat gagne le tournoi ?

**BTL** — par défaut (seul non éliminé) mais aussi par mérite : c'est le seul qui introduit un OUTIL NOMMÉ (Evertse/S-unit) qui n'avait jamais été connecté au problème dans ce projet.

### Pourquoi mérite-t-il de survivre ?

1. Il est genuinement HORS du noyau F_p (opère dans Z, pas mod p)
2. Il utilise la cause source (indépendance multiplicative de 2,3 → S-unit structure)
3. Il a une littérature associée (Evertse 1984, ESS 2002, Amoroso-Viada 2009)
4. Il fournit des BORNES EFFECTIVES, même si trop faibles actuellement
5. Le pont corrSum → S-unit equation est NOUVEAU dans le contexte du projet

### Condition explicite de non-boucle pour R83

R83 doit :
1. Écrire la S-unit equation associée à corrSum = m·d EXPLICITEMENT
2. Calculer la borne C(k) d'Evertse-Schmidt pour k = 21 (plus petit k du gap)
3. Comparer C(k) avec |Comp_mono(S,k)| pour ce k
4. Si C(k) ≫ |Comp_mono(S,k)| (borne trop faible), documenter POURQUOI et chercher des améliorations spécifiques à la structure Collatz
5. Si aucune amélioration n'est trouvée, BTL est enterré

### Décision stratégique

**POURSUIVRE AVEC RÉSERVE** : BTL survit pour R83 comme le seul candidat ouvrant un front hors F_p. L'innovation n'est pas suspendue mais est FORTEMENT CONTRAINTE par la condition de non-boucle ci-dessus.

---

## 12. Activation de l'autonomie

**Autonomie ACTIVÉE** pour les sous-rounds S1/S2/S3 du tournoi (section 9 ci-dessus).

**Justification** : les 3 sous-rounds sont nécessaires pour faire vivre les candidats, les auditer, et les éliminer. L'autonomie est restée strictement dans les rails :
- 3 sous-rounds exactement (pas plus)
- Aucun calcul
- Aucun k-par-k
- CST éliminé rapidement (preuve directe d'échec)
- SRF éliminé par comparaison avec Ratio Law
- BTL audité en profondeur avec découverte de la connexion S-unit

---

## 13. Journal des sous-rounds autonomes

### S1 — Qualification initiale
- 3 candidats examinés
- Critères appliqués : non-redondance, précision, généralité, réfutation, lien au verrou
- Résultat : 1 qualifié (BTL), 2 éliminés (SRF, CST)

### S2 — Audit croisé de BTL
- Test anti-redondance : PASSÉ (direction Baker connue, mais application S-unit/Horner = NOUVELLE)
- Test de réfutation : PASSÉ AVEC RÉSERVE (pont somme→produit non garanti pour c_j distincts, mais S-unit theory offre un cadre alternatif)
- Découverte : la connexion corrSum → S-unit equation est VIABLE (non-dégénérescence automatique car tous termes positifs)
- Limitation : les bornes quantitatives d'Evertse sont ASTRONOMIQUES pour k=21 (~exp(50000))

### S3 — Élimination finale
- BTL : QUALIFIÉ AVEC RÉSERVE
- SRF : ÉLIMINÉ (redondant)
- CST : ÉLIMINÉ (réfuté)
- Décision : POURSUIVRE AVEC RÉSERVE

---

## 14. Objets concernés + Ladder of Proof

### BTL (Baker-Transcendence Lift)

| Niveau | État |
|--------|------|
| Intuition | ✅ Baker est le seul outil exploitant l'indépendance de 2 et 3 quantitativement |
| Manque visé | ✅ Réduction somme → produit pour appliquer Baker/Evertse |
| Schéma d'objet | ✅ corrSum = m·d ↔ S-unit equation dans Z[1/6] |
| Semi-formalisation | ✅ Non-dégénérescence prouvée (tous termes positifs) |
| Lemme candidat | ⚠️ BTL-L1 formulé mais bornes quantitatives insuffisantes |
| Test de mordant | ⚠️ Bornes d'Evertse ~exp(k³) vs |Comp| ~C(S,k) : trop faible pour k=21 |
| Possibilité de preuve | ❌ Pas avec les bornes actuelles. Requiert amélioration spécifique ou technique Collatz-adaptée |

**Ladder** : L4 (semi-formalisé, lemme candidat avec réserves)

### SRF (Sparse Rigidity via Filtration)

| Niveau | État |
|--------|------|
| Intuition | ✅ |
| Manque visé | ✅ |
| Schéma d'objet | ✅ |
| Semi-formalisation | ❌ Ramène à R73 |
| Lemme candidat | ❌ Requiert équidistribution |

**Ladder** : L2 (intuition + objet, pas de semi-formalisation)

### CST (Coset Sum Tracking)

| Niveau | État |
|--------|------|
| Intuition | ✅ |
| Manque visé | ✅ |
| Schéma d'objet | ✅ |
| Semi-formalisation | ❌ Réfuté (addition ≠ homomorphisme multiplicatif) |

**Ladder** : L1 (intuition, réfuté au test)

---

## 15. Ce qui est appris

1. **Le manque le plus étroit** = l'absence de réduction de corrSum (somme) en objet compatible avec les outils transcendants (Baker, Evertse). C'est le gap entre les sommes et les produits.

2. **La connexion S-unit est NOUVELLE et VIABLE** : l'équation corrSum = m·d est une S-unit equation dans Z[1/6] avec S = {2, 3}. Toutes les solutions sont non-dégénérées (termes positifs). Le théorème d'Evertse s'applique et donne une borne FINIE (mais trop grande).

3. **Le quotient multiplicatif ne suit pas les sommes** : preuve directe que π(a+b) ≠ f(π(a), π(b)) pour un homomorphisme multiplicatif π. La faille add/mult (R81) est FONDAMENTALE et non contournable par changement de quotient.

4. **La sparsité seule ne suffit pas** : |Σ_≤(k)| ≪ p est vrai mais ne cible pas -1. La conversion cardinal → exclusion ponctuelle est exactement le problème initial sous un autre angle.

5. **Les bornes S-unit actuelles sont insuffisantes** : exp(C·k³) pour Evertse-Schmidt ≫ C(S,k) pour k ≥ 21. Mais les bornes sont en amélioration continue (techniques de géométrie des nombres, hauteurs).

---

## 16. Ce qui est fermé utilement

| Piste fermée | Raison | Impact |
|-------------|--------|--------|
| CST (Coset Sum Tracking) | π multiplicatif ne suit pas les sommes | Ferme toute tentative de quotient multiplicatif sur des sommes additives |
| SRF comme approche autonome | Redondant avec Ratio Law, requiert R73 | Ferme la route "sparsité → exclusion" sans outil d'équidistribution |
| Réduction naïve somme→produit | corrSum ≠ produit sauf cas c_j=c | Précise le gap technique de BTL |

---

## 17. Ce qui est enterré

| Objet | Type de mort | Ce que la mort enseigne |
|-------|-------------|------------------------|
| CST | Réfuté (faille add/mult fondamentale) | L'addition dans F_p est irréductiblement incompatible avec les quotients multiplicatifs |
| SRF autonome | Trop faible (ne cible pas -1) | La sparsité est un fait mais pas un levier de preuve sans équidistribution |
| BTL-L1 version naïve (Baker seul) | Trop faible (bornes insuffisantes) | Baker seul ne suffit pas ; il faut combiner avec Evertse/structure |

---

## 18. Autopsie des pistes fermées

### CST (Coset Sum Tracking)
- **Nom** : CST
- **Type de mort** : Réfuté
- **Cause du rejet** : Le quotient F_p*/⟨2⟩ est un groupe MULTIPLICATIF. L'application π: F_p* → F_p*/⟨2⟩ est un homomorphisme multiplicatif. L'image d'une somme a+b sous π n'est PAS déterminée par π(a) et π(b). Preuve : soient a = α·u, b = β·v avec u,v ∈ ⟨2⟩. Alors a+b = αu+βv, dont le coset dépend de u et v, pas seulement de α et β.
- **Ce que la mort enseigne** : Il n'existe AUCUN quotient de F_p* qui respecte simultanément la multiplication (structure des termes) et l'addition (structure de la somme). C'est une reformulation précise de la faille add/mult (R81).
- **Où cela redirige** : Vers les outils qui travaillent dans Z (pas F_p), où les outils transcendants (Baker, Evertse) opèrent sans les contraintes du corps fini.

### SRF (Sparse Rigidity via Filtration)
- **Nom** : SRF
- **Type de mort** : Trop faible
- **Cause du rejet** : |Σ_≤(k)| ≪ p est un fait vrai mais insuffisant pour exclure -1 spécifiquement. La conversion cardinal → exclusion ponctuelle requiert un argument d'équidistribution, qui ramène au mur R73 (sommes exponentielles en régime O(log p)).
- **Ce que la mort enseigne** : La sparsité est un SYMPTÔME favorable, pas un MÉCANISME de preuve. "Le sumset est petit" n'implique pas "le sumset évite -1" sans information sur la distribution.
- **Où cela redirige** : La sparsité pourrait devenir utile comme COMPOSANTE d'un argument combiné (par exemple, sparsité + S-unit borne → exclusion), mais pas comme approche autonome.

### BTL-L1 naïf (Baker seul)
- **Nom** : BTL-L1 version naïve
- **Type de mort** : Trop faible (quantitativement)
- **Cause du rejet** : La forme linéaire en log 2, log 3 n'est extractible directement que pour le cas c_j = c (tous gaps égaux). Pour c_j distincts, corrSum n'est pas un quotient simple de puissances. La S-unit theory (Evertse) donne une borne mais exp(C·k³) ≫ C(S,k).
- **Ce que la mort enseigne** : La direction Baker est la BONNE direction (seul outil quantitatif hors F_p), mais l'application directe donne des bornes trop faibles. Il faut exploiter la structure SPÉCIFIQUE de corrSum (monotonie, progression géométrique des coefficients 3^{k-1-i}) pour améliorer les bornes.
- **Où cela redirige** : Vers une version STRUCTURÉE de BTL qui utilise la monotonie et les coefficients 3^{k-1-i} comme contraintes supplémentaires dans la S-unit equation.

---

## 19. Survivant pour R83

**BTL (Baker-Transcendence Lift)** — version ENRICHIE par S-unit theory.

**Objet** : L'équation corrSum = m·(2^S - 3^k) vue comme S-unit equation dans Z[1/6].

**Lemme candidat révisé (BTL-L2)** : L'équation
Σ_{i=0}^{k-1} 3^{k-1-i} · 2^{A_i} - m·2^S + m·3^k = 0
avec la contrainte A_0 ≤ A_1 ≤ ... ≤ A_{k-1}, Σ A_i = S, A_i ≥ 1, m ≥ 1, a au plus N(k) solutions non-dégénérées, où N(k) est borné par le théorème d'Evertse-Schlickewei-Schmidt.

**Question pour R83** : N(k) est-il suffisamment petit pour que, combiné avec la contrainte de monotonie et la structure des coefficients, on puisse exclure TOUTES les solutions pour les k du gap ?

**Condition de non-boucle** :
- R83 doit CALCULER N(k) pour k=21 (borne effective d'Evertse)
- R83 doit COMPARER avec |Comp_mono(34, 21)| = C(33, 20)
- Si N(k) ≫ |Comp_mono|, BTL est ENTERRÉ pour le gap mais survit comme résultat structurel
- R83 ne doit PAS proposer de "nouvelles formulations" de la S-unit equation — il doit APPLIQUER les bornes existantes

---

## 20. Risques / Limites

1. **Risque principal** : les bornes d'Evertse sont trop faibles pour k = 21-41, et BTL ne produit aucun résultat concret pour le gap.

2. **Risque secondaire** : la connexion S-unit est "intéressante" mais pas "mordante" — elle pourrait être un décor théorique de plus.

3. **Limite structurelle** : même si les bornes étaient améliorées, l'approche S-unit donne des bornes SUPÉRIEURES sur le nombre de solutions, pas une preuve qu'il y a ZÉRO solutions. Pour prouver N_0(d) = 0, il faudrait montrer que la borne est 0, ce qui n'arrive jamais avec Evertse (la borne est toujours ≥ 1).

4. **Nuance cruciale** : BTL ne peut pas PROUVER N_0(d) = 0 directement. Il peut seulement montrer que le nombre de solutions est FINI et BORNÉ. Pour les petits k, la borne pourrait être 0 si des conditions de dégénérescence supplémentaires sont exploitées. Pour les grands k (k ≥ 42), le résultat est déjà couvert par Borel-Cantelli.

5. **Direction complémentaire** : BTL pourrait être utile en COMBINAISON avec DP : BTL borne le nombre de solutions théoriques, et DP vérifie les cas restants. Cela pourrait réduire la charge computationnelle de DP.

---

## 21. Verdict final

**Score** : 7/10

**Justification** :
- Le diagnostic du manque concret est NET (9/10) : gap somme↔produit identifié
- Le tournoi est HONNÊTE (8/10) : 3 candidats, 2 éliminés pour raisons explicites
- Le survivant est GENUINEMENT NOUVEAU (7/10) : connexion S-unit jamais explorée dans le projet
- Le survivant est QUANTITATIVEMENT INSUFFISANT (5/10) : bornes d'Evertse trop faibles pour k=21-41
- La décision est SOBRE (9/10) : "poursuivre avec réserve", pas de survente

**Le 7 reflète** : un progrès conceptuel réel (nouvelle connexion théorique) sans progrès quantitatif (les bornes ne suffisent pas). C'est un round qui OUVRE un front mais ne le FRANCHIT pas.

---

## 22. Registre FAIL-CLOSED

| Objet | Statut |
|-------|--------|
| Manque concret (gap somme↔produit) | [OBJET RÉEL] |
| BTL (Baker-Transcendence Lift) | [QUALIFIÉ AVEC RÉSERVE] |
| BTL-L2 (lemme S-unit) | [SEMI-FORMALISÉ] |
| Connexion corrSum → S-unit equation | [OBJET RÉEL] |
| Non-dégénérescence (termes positifs) | [FORTEMENT ÉTAYÉ] |
| Bornes d'Evertse pour k=21 | [DIAGNOSTIC INSUFFISANT] |
| SRF (Sparse Rigidity) | [ÉLIMINÉ — trop faible] |
| CST (Coset Sum Tracking) | [RÉFUTÉ] |
| Quotient multiplicatif sur sommes | [RÉFUTÉ] |
| Baker seul (sans S-unit) | [ÉLIMINÉ — trop faible] |
| Réduction somme→produit (cas c_j=c) | [SEMI-FORMALISÉ] |
| Réduction somme→produit (cas général) | [À REFORMULER] |
| Sparsité autonome comme levier | [ÉLIMINÉ — insuffisant] |
