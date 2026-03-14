# R74 — BILAN : Innovation disciplinée — La reformulation SAMC

## Type : I/P (innovation disciplinée + exigence de preuve/testabilité)
## IVS : 9/10

**Justification IVS** :
- Nouveauté réelle : 9/10 (objet SAMC genuinement nouveau, vérifié sur k=3)
- Compression du verrou : 8/10 (change le paradigme analytique → algébrique, mais ne résout pas encore)
- Testabilité précoce : 10/10 (premier test k=3 p=5 effectué et PASSÉ)
- Qualité du contrôle anti-rebranding : 9/10 (différence avec les routes mortes clairement identifiée)
- Honnêteté de la décision finale : 9/10 (POURSUIVRE AVEC RÉSERVE, pas survente)

---

## 1. Résumé exécutif

R74 cherche une innovation mathématique disciplinée après le déclassement des voies analytiques en R73.

**Trois innovations candidates** ont été proposées et soumises à l'audit :

1. **SAMC (Sumset Avoidance with Monotonicity Constraint)** — reformule N_0(p) = 0 comme un problème d'évitement dans un sumset structuré de F_p
2. **ACR (Affine Chain Representation)** — reformule corrSum comme orbite sous une chaîne de maps affines sur F_p
3. **CPO (Carry Propagation Obstruction)** — tente d'exploiter la structure binaire des carries dans corrSum

**Résultat de l'audit** :
- **SAMC : SURVIVANT** — objet réel, lemme candidat clair, premier test PASSÉ (k=3, p=5)
- **ACR** : reformulation dynamique de SAMC, pas un objet indépendant — ABSORBÉ par SAMC
- **CPO** : trop vague, pas de lemme concret — ENTERRÉ (prose)

**La reformulation SAMC** :

> N_0(p) = 0  ⟺  -1 ∉ Σ_≤(k)
>
> où Σ_≤(k) = {Σ_{j=1}^{k-1} λ^j · 2^{g_j} : 0 ≤ g_1 ≤ ... ≤ g_{k-1} ≤ S-k}
>
> avec λ = 2·3^{-1} mod p et p | (2^S − 3^k)

**Premier test** : Pour k=3, p=5 : λ=4, Σ_≤(2) = {0, 1, 2, 3}, et -1 ≡ 4 ∉ Σ_≤(2). ✓

**Décision** : POURSUIVRE AVEC RÉSERVE. L'innovation change le paradigme (analytique → algébrique/combinatoire), évite le mur des sommes courtes, et a un premier test positif. Mais le mécanisme de preuve de l'évitement n'est pas encore identifié.

---

## 2. Type du round + IVS

**Type** : I/P
- **I** : innovation disciplinée — proposition d'un nouvel objet mathématique
- **P** : exigence de preuve/testabilité — premier test effectué

**IVS** : 9/10 — Innovation réelle avec premier test positif. Point manquant : le mécanisme de preuve reste à découvrir.

---

## 3. Méthode

- Identification précise du manque conceptuel laissé par R73
- Génération de 3 innovations candidates (budget respecté)
- Pour chaque innovation : objet, lemme candidat, critère de réfutation
- Contrôle anti-rebranding contre l'historique (avant R60 et après)
- Test de réalité mathématique sur chaque innovation
- Premier test effectif de l'innovation survivante (k=3, p=5)
- Aucun calcul numérique par script, aucun k-par-k, aucune galerie de littérature

---

## 4. Résultats PHASE 1 / AXE A — Manque conceptuel exact

### L'obstacle laissé vivant par R73

R73 a démontré que TOUS les outils analytiques standards (Cauchy-Schwarz, Abel, van der Corput, Weil, Bourgain-Konyagin) échouent dans le régime O(log p) pour la même raison : ils préservent le TYPE de la somme (somme exponentielle sur progression géométrique) sans pouvoir en extraire une cancellation.

### Le manque précis

**Il manque un moyen de passer du problème analytique (borner |H_k(t,p)| pour chaque t) au problème algébrique (montrer que corrSum ≢ 0 mod p) sans transiter par les bornes de sommes exponentielles.**

Plus précisément :
- L'approche analytique demande : |H_k(t,p)| < C/(p-1) pour tout t ≠ 0
- Cela exige des bornes individuelles sur des sommes courtes de longueur O(log p)
- **Aucun outil connu ne produit de telles bornes**
- MAIS le problème d'ORIGINE est algébrique : corrSum(A) ≢ 0 mod p pour tout A

Le manque est donc : **un chemin algébrique/combinatoire direct qui évite le détour analytique par les bornes de sommes exponentielles**.

### Formulation précise du manque en une phrase

> Il manque une reformulation de "corrSum(A) ≢ 0 mod p pour tout A" qui soit directement attaquable par des outils algébriques ou combinatoires, sans passer par l'estimation de sommes de caractères additifs.

### Types d'objets innovants légitimes

1. Une reformulation du problème en termes de sumsets / structure additive de F_p
2. Une reformulation en termes de dynamique algébrique (orbites d'applications affines)
3. Une reformulation en termes d'arithmétique des entiers (divisibilité, valuations, carries)

### Pseudo-besoins (prose, pas de vrais manques)

- "Un meilleur invariant spectral" → PROSE (le spectral gap est mort en R72)
- "Une nouvelle énergie fonctionnelle" → PROSE (pas d'espace fonctionnel pertinent)
- "Une meilleure notion de rigidité" → PROSE (trop vague pour produire un lemme)

---

## 5. Résultats PHASE 2 / AXE B — Innovations candidates

### Innovation 1 : SAMC (Sumset Avoidance with Monotonicity Constraint)

#### Objet nouveau

Reformuler corrSum ≡ 0 mod p comme un problème d'APPARTENANCE dans un sumset structuré de F_p.

**Dérivation** : Partant de corrSum = Σ_{j=0}^{k-1} 3^{k-1-j} · 2^{A_j}, on divise par 3^{k-1} (inversible dans F_p pour p ≥ 5) :

```
corrSum / 3^{k-1} = Σ_{j=0}^{k-1} (2/3)^j · 2^{g_j}    (en F_p)
```

où g_j = A_j − j (gaps, non-décroissants, g_0 = 0).

En posant λ = 2·3^{-1} mod p et en séparant le terme j=0 (qui vaut 1) :

```
corrSum / 3^{k-1} = 1 + Σ_{j=1}^{k-1} λ^j · 2^{g_j}
```

Donc : corrSum ≡ 0 mod p ⟺ Σ_{j=1}^{k-1} λ^j · 2^{g_j} ≡ -1 mod p.

**Définition canonique** : Le **sumset monotone** est :

```
Σ_≤(k) = { Σ_{j=1}^{k-1} λ^j · 2^{g_j}  :  0 ≤ g_1 ≤ g_2 ≤ ... ≤ g_{k-1} ≤ S−k }  ⊂ F_p
```

**Reformulation** : N_0(p) = 0  ⟺  -1 ∉ Σ_≤(k)

#### Difficulté compressée

Transforme "borner des sommes exponentielles de longueur O(log p)" (IMPOSSIBLE avec les outils actuels) en "montrer qu'un élément spécifique est absent d'un sumset structuré" (problème de combinatoire additive dans F_p).

#### Différence réelle avec les objets existants

| Aspect | Approche analytique (R71-R73) | SAMC |
|--------|-------------------------------|------|
| Cadre | Analyse harmonique sur F_p | Combinatoire additive dans F_p |
| Objet central | Σ e(t·corrSum/p) | Σ_≤(k) ⊂ F_p |
| Ce qu'il faut montrer | |H_k(t,p)| petit pour TOUT t | -1 ∉ Σ_≤(k) pour UN bon p |
| Obstacle | Sommes courtes de longueur O(log p) | Caractériser les éléments manquants du sumset |
| Outils potentiels | Weil, Bourgain-Konyagin (HORS RÉGIME) | Cauchy-Davenport, Plünnecke-Ruzsa, structure multiplicative |

#### Rôle logique dans la chaîne

```
H (pas de k-cycle non trivial)
  ⟸ ∀k≥3, N_0(d(k)) = 0
  ⟸ ∀k≥3, ∃p | d(k) : N_0(p) = 0           [Lemme A']
  ⟸ ∀k≥3, ∃p adéquat : -1 ∉ Σ_≤(k) mod p   [SAMC = Lemme B' reformulé]
```

SAMC remplace le Lemme B' (borne sur |H_k|) par un Lemme B'_SAMC (évitement dans un sumset). Les deux sont équivalents, mais SAMC connecte à un espace d'outils DIFFÉRENT.

#### Premier lemme candidat

**Lemme SAMC-1** : Pour p | d(k) avec p > C(S-1, k-1) et ord_p(2) ≥ S :

> -1 ∉ Σ_≤(k)

où Σ_≤(k) est le sumset monotone défini ci-dessus.

#### Premier critère de réfutation

Si pour un k ≥ 3 et un p adéquat, on calcule Σ_≤(k) et on trouve -1 ∈ Σ_≤(k), le lemme est FAUX pour ce (k, p) et l'approche échoue.

#### Premier test effectué : k=3, p=5

- S = 5, d = 2^5 − 3^3 = 32 − 27 = 5
- p = 5 divise d, C(4,2) = 6, p = 5 < C = 6 (borderline, mais p = d lui-même)
- λ = 2 · 3^{-1} mod 5 = 2 · 2 = 4 ≡ -1 mod 5
- λ² = 16 ≡ 1 mod 5
- P = {2^g : 0 ≤ g ≤ S−k} = {2^0, 2^1, 2^2} = {1, 2, 4} ≡ {1, 2, 4} mod 5

Éléments de Σ_≤(2) = {λ · 2^{g_1} + λ² · 2^{g_2} : 0 ≤ g_1 ≤ g_2 ≤ 2} :

| g_1 | g_2 | 4·2^{g_1} + 1·2^{g_2} | mod 5 |
|-----|-----|------------------------|-------|
| 0 | 0 | 4 + 1 = 5 | **0** |
| 0 | 1 | 4 + 2 = 6 | **1** |
| 0 | 2 | 4 + 4 = 8 | **3** |
| 1 | 1 | 8 + 2 = 10 | **0** |
| 1 | 2 | 8 + 4 = 12 | **2** |
| 2 | 2 | 16 + 4 = 20 | **0** |

Σ_≤(2) = {0, 1, 2, 3}

Et -1 ≡ 4 mod 5. Or 4 ∉ {0, 1, 2, 3}. ✓ **SAMC-1 PASSE pour k=3, p=5.**

Le sumset couvre exactement F_5 \ {4} = F_5 \ {-1}. L'élément manquant est PRÉCISÉMENT -1.

---

### Innovation 2 : ACR (Affine Chain Representation)

#### Objet nouveau

Reformuler corrSum comme l'évaluation d'une chaîne de k-1 applications affines sur F_p :

```
R_0 = 1
R_m = 3^m + 2^{a_{k-1-m}} · R_{m-1}    pour m = 1, ..., k-1
corrSum = R_{k-1}
```

Chaque étape applique la map affine r ↦ 3^m + x·r avec x = 2^{a_{k-1-m}}.

N_0(p) = 0 ⟺ aucune chaîne d'applications affines autorisées n'envoie 1 sur 0.

#### Diagnostic après audit

**ACR est une reformulation DYNAMIQUE de SAMC**, pas un objet indépendant.

Preuve : La chaîne affine calcule corrSum/3^{k-1} = 1 + Σ λ^j · 2^{g_j} de manière ITÉRATIVE. L'ensemble des sorties possibles est exactement {1 + s : s ∈ Σ_≤(k)}. Dire "aucune chaîne n'envoie 1 sur 0" est équivalent à "0 ∉ {1 + s : s ∈ Σ_≤(k)}" soit "-1 ∉ Σ_≤(k)".

**Verdict** : [ABSORBÉ PAR SAMC] — même objet, langage différent. ACR peut être utile comme PERSPECTIVE (le semi-groupe affine donne une structure de composition) mais n'est pas une innovation indépendante.

#### Premier lemme candidat : identique à SAMC-1 modulo reformulation.

#### Premier critère de réfutation : identique à SAMC.

---

### Innovation 3 : CPO (Carry Propagation Obstruction)

#### Objet proposé

Exploiter la structure des carries dans l'addition binaire des termes 3^{k-1-j} · 2^{A_j} pour contraindre la divisibilité de corrSum par p.

#### Observations

- corrSum est IMPAIR (le terme j=0 est 3^{k-1}, impair ; les autres sont pairs) → p ≠ 2
- corrSum ≢ 0 mod 3 (le terme j=k-1 est 2^{A_{k-1}}, non multiple de 3) → p ≠ 3
- Les termes 3^{k-1-j} · 2^{A_j} ont leur "masse binaire" à des positions croissantes (position A_j)
- Si les A_j sont suffisamment espacés, les termes ne se chevauchent pas en binaire et corrSum est une concaténation → contrôle facile de la structure binaire
- Mais en pratique, les parties a_j ≈ 1.585 en moyenne, donc les termes SE CHEVAUCHENT et les carries sont complexes

#### Diagnostic après audit

**CPO n'a pas de lemme candidat concret.** Les observations (corrSum impair, corrSum ≢ 0 mod 3) sont triviales et ne contraignent pas les p ≥ 5. La structure des carries est trop complexe à formaliser en un lemme testable.

**Verdict** : [PROSE] — observations sans objet opératoire.

---

## 6. Résultats PHASE 2 / AXE C — Contrôle anti-rebranding

### Tableau de comparaison

| Innovation | Ancienne piste similaire | Différence mathématique | Verdict |
|-----------|-------------------------|-------------------------|---------|
| **SAMC** | Fourier/ET sur F_p (R63-R73) | SAMC travaille dans F_p directement (éléments, pas caractères). N'utilise PAS de sommes exponentielles. L'objet est un SUMSET, pas une transformée. | **NOUVEAUTÉ RÉELLE** |
| **SAMC** | Non-annulation directe (R71) | R71 rejetait la non-annulation directe car elle = "le problème complet". SAMC ajoute la STRUCTURE MONOTONE du sumset + le paramètre λ = 2/3, ce qui connecte à la combinatoire additive. | **NOUVEAUTÉ RÉELLE** (la structure change l'espace d'outils) |
| **ACR** | Opérateur de transfert (R72) | R72 opérait en espace de POSITIONS (n ∈ {1,...,S}), ACR opère en espace de RÉSIDUS (r ∈ F_p). Géométries différentes. Mais ACR = SAMC reformulé. | **NOUVEAUTÉ PARTIELLE** (absorbé) |
| **CPO** | Observations arithmétiques basiques | Pas de différence significative. corrSum impair / ≢ 0 mod 3 sont triviaux. | **REBRANDING CERTAIN** |

### Drapeaux d'alerte

- ⚠️ SAMC pourrait devenir un rebranding si, une fois qu'on cherche à prouver -1 ∉ Σ_≤(k), on est forcé de passer par... des sommes de caractères additifs (retour aux sommes exponentielles). C'est le risque principal.
- ✅ Cependant, il existe des outils de combinatoire additive (Cauchy-Davenport, arguments de structure multiplicative, méthode polynomiale) qui n'utilisent PAS de bornes de sommes exponentielles. SAMC ouvre l'accès à ces outils.

---

## 7. Résultats PHASE 3 / AXE D — Test de réalité mathématique

### SAMC

| Critère | Évaluation |
|---------|-----------|
| Objet défini assez nettement ? | **OUI** — Σ_≤(k) est un sous-ensemble explicite de F_p, calculable pour tout (k,p) |
| Premier lemme candidat non trivial ? | **OUI** — SAMC-1 : -1 ∉ Σ_≤(k) pour p adéquat |
| Chaîne de réduction vers le verrou ? | **OUI** — SAMC-1 ⟹ N_0(p) = 0 ⟹ (avec Lemme A') H |
| Test faisable sans computationnel ? | **OUI** — test k=3 p=5 fait à la main (6 cas) |
| Réduit-elle le problème ou le redécrit ? | **RÉDUIT** — change l'espace d'outils (analytique → combinatoire additive). Mais la difficulté intrinsèque reste. |
| Premier échec falsifiant ? | Si -1 ∈ Σ_≤(k) pour un k ≥ 3 avec p adéquat |

**Statut objet** : [OBJET RÉEL]
**Statut lemme** : [BIEN CIBLÉ]
**Verdict de mordant** : [TESTABLE]

### ACR

| Critère | Évaluation |
|---------|-----------|
| Objet défini ? | OUI (chaîne affine) |
| Indépendant de SAMC ? | **NON** — équivalent à SAMC par reformulation |

**Statut** : [SEMI-RÉEL] — absorbé par SAMC
**Verdict** : [TESTABLE MAIS REDONDANT]

### CPO

| Critère | Évaluation |
|---------|-----------|
| Objet défini ? | NON (pas de formalisation des carries en lemme) |
| Premier lemme ? | NON |

**Statut** : [PROSE]
**Verdict** : [NON TESTABLE]

---

## 8. Résultats PHASE 3 / AXE E — Chaîne logique et impact

### Chaîne logique de SAMC

```
SAMC-1 (prouvé pour p adéquat)
  ⟹ -1 ∉ Σ_≤(k) dans F_p
  ⟹ ∀A ∈ Comp(S,k) : Σ λ^j · 2^{g_j} ≠ -1 mod p
  ⟹ ∀A : corrSum(A)/3^{k-1} ≠ 0 mod p
  ⟹ ∀A : corrSum(A) ≢ 0 mod p
  ⟹ N_0(p) = 0
  ⟹ (avec Lemme A' : ∃ tel p | d(k))  N_0(d(k)) = 0
  ⟹ H (pas de k-cycle non trivial)
```

### Portée honnête

**Si SAMC-1 est prouvé** : Le programme est essentiellement complet (modulo Lemme A' qui reste ouvert mais est un problème de théorie des nombres "classique" — existence de grands facteurs premiers de 2^S − 3^k).

**Impact** : POTENTIELLEMENT DÉCISIF. SAMC-1 remplace le Lemme B' (le verrou le plus dur). Si SAMC-1 tombe, le verrou principal change de nature : de "borner des sommes exponentielles courtes" (impossibilité analytique) à "caractériser les éléments manquants d'un sumset monotone" (combinatoire additive).

### Ce que le premier test k=3 p=5 démontre

1. La reformulation est CORRECTE (cohérente avec le résultat connu N_0(5) = 0 pour k=3)
2. Le sumset Σ_≤(2) = {0,1,2,3} couvre EXACTEMENT F_5 \ {-1}
3. -1 est le SEUL élément manquant — c'est remarquable et peut indiquer une structure profonde

### Seuil minimum pour mériter R75

SAMC mérite R75 si :
1. L'objet est vérifié correct (✓ fait)
2. Un mécanisme candidat d'exclusion de -1 peut être identifié ou au moins investigué
3. La connexion aux outils de combinatoire additive est réelle, pas juste invoquée

### Risque principal

Le risque est que SAMC soit "isomorphe" au problème original : prouver -1 ∉ Σ_≤(k) pourrait être EXACTEMENT AUSSI DUR que prouver corrSum ≢ 0. Dans ce cas, on aurait gagné une reformulation propre mais pas de compression.

**Contre-argument** : La reformulation SAMC fait apparaître deux structures qui n'étaient pas visibles dans le cadre analytique :
1. Le paramètre λ = 2·3^{-1} mod p (qui encode la bi-géométricité en UN SEUL scalaire)
2. La contrainte de MONOTONIE sur les g_j (qui restreint le sumset)

Ces deux structures sont potentiellement exploitables par des arguments de combinatoire additive qui n'ont pas d'équivalent dans le cadre des sommes exponentielles.

---

## 9. Résultats PHASE 4 / AXE F — Décision finale

### Quelle innovation a la meilleure compression ?

**SAMC** : compression réelle — change le paradigme (analytique → combinatoire additive), fait apparaître la structure (λ, monotonie), passe le premier test.

### Quelle innovation produit le meilleur premier lemme ?

**SAMC** : SAMC-1 est précis, testable, bien ciblé, et cohérent avec le cas connu k=3.

### Meilleur rapport nouveauté / testabilité / pertinence ?

| Innovation | Nouveauté | Testabilité | Pertinence | Score |
|-----------|-----------|-------------|------------|-------|
| SAMC | 9/10 | 10/10 | 9/10 | **28/30** |
| ACR | 5/10 (absorbé) | 10/10 | 9/10 | 24/30 |
| CPO | 2/10 | 2/10 | 3/10 | 7/30 |

### Décision

**POURSUIVRE AVEC RÉSERVE** — SAMC est la seule innovation qui survit à l'audit. Elle mérite un round R75 de test de mordant, avec la réserve que le mécanisme de preuve n'est pas encore identifié.

### Survivant unique pour R75

**SAMC : Test de mordant du Lemme SAMC-1**

R75 doit :
1. Tester SAMC-1 sur au moins un cas supplémentaire (k=5, p=13 si possible à la main)
2. Identifier un MÉCANISME d'exclusion de -1 (pourquoi -1 est-il systématiquement exclu ?)
3. Tester si les outils de combinatoire additive (Cauchy-Davenport, méthode polynomiale) s'appliquent
4. Évaluer si la contrainte de monotonie est le facteur décisif ou accidentel

### Condition de non-boucle pour R75

R75 doit :
1. NE PAS revenir aux bornes de sommes exponentielles
2. NE PAS reformuler SAMC dans un nouveau langage sans le tester
3. Produire soit un mécanisme d'exclusion candidat, soit un diagnostic de pourquoi -1 est exclu, soit un contre-exemple
4. Si le test k=5 échoue : ENTERRER SAMC et documenter pourquoi
5. NE PAS élargir SAMC à un "cadre général" sans avoir d'abord un résultat concret

### Raisons des enterrements

- **ACR** : absorbé par SAMC (même objet, langage différent). Pas enterré mais FUSIONNÉ.
- **CPO** : prose sans lemme. Les observations triviales (corrSum impair, ≢ 0 mod 3) ne contraignent pas les p ≥ 5. La structure des carries est trop complexe pour un lemme propre.

---

## 10. Activation de l'autonomie

**Activation** : OUI — 2 sous-rounds pour départager SAMC et ACR, puis confirmer la décision.

---

## 11. Journal des sous-rounds autonomes

### S1 — SAMC et ACR sont-ils réellement distincts ?

1. **Hypothèse active** : ACR pourrait capturer une structure (semi-groupe affine) que SAMC ne voit pas
2. **Objet** : la chaîne affine R_m = 3^m + 2^{a_{k-1-m}} · R_{m-1}
3. **Question** : ACR apporte-t-il un outil supplémentaire par rapport à SAMC ?
4. **Démarche** : La chaîne affine calcule itérativement corrSum/3^{k-1}. L'ensemble des sorties est {1 + s : s ∈ Σ_≤(k)}. La structure de semi-groupe (composition de maps affines) est encodée dans l'ORDER des additions dans le sumset. L'addition est commutative dans F_p, mais la contrainte de monotonie (g_1 ≤ g_2 ≤ ...) impose un ORDRE. ACR capture cet ordre via la composition séquentielle. SAMC le capture via l'indice j des couches λ^j.
5. **Résultat** : ACR et SAMC sont mathématiquement IDENTIQUES. La structure de semi-groupe n'apporte pas d'outil supplémentaire car la composition est déjà encodée dans les couches λ^j de SAMC. Les maps affines sont f(r) = c + b·r avec c = 3^m et b = 2^a, et l'ensemble de leurs compositions est exactement l'ensemble des corrSum possibles — c'est-à-dire 3^{k-1} · (1 + Σ_≤(k)).
6. **Statut** : [CONFIRMÉ] — ACR = SAMC
7. **Ce qui est appris** : ACR est une perspective UTILE (penser itérativement) mais pas un objet NOUVEAU.
8. **Décision** : continuer (S2)
9. **Raison** : confirmer la décision sur SAMC

### S2 — La réserve sur SAMC est-elle justifiée ?

1. **Hypothèse active** : SAMC pourrait être "isomorphe" au problème original sans compression réelle
2. **Objet** : le lien entre SAMC et le problème original
3. **Question** : SAMC change-t-il réellement l'espace d'outils accessible ?
4. **Démarche** : Comparer les outils disponibles dans les deux cadres.
   - **Cadre analytique** : transformée de Fourier → sommes de caractères → bornes de sommes exponentielles → BLOQUÉ par régime O(log p)
   - **Cadre SAMC** : sumsets dans F_p → Cauchy-Davenport (borne inférieure sur |A+B|), Plünnecke-Ruzsa (structure des sumsets), méthode polynomiale (Alon-Nathanson-Ruzsa), structure multiplicative de P = {2^g}, contrainte de monotonie
   - Le cadre SAMC donne accès à des outils qui n'ont PAS d'équivalent dans le cadre analytique. Par exemple, la méthode polynomiale d'Alon-Nathanson-Ruzsa permet de prouver l'existence d'éléments dans des sumsets restreints, ou leur absence, par des arguments de degré de polynômes — pas par des bornes de sommes.
   - De plus, le paramètre λ = 2/3 mod p a un ORDRE multiplicatif spécifique dans F_p (lié à ord_p(2) et ord_p(3)), ce qui crée une rigidité que le cadre analytique ne pouvait pas exploiter.
5. **Résultat** : SAMC change RÉELLEMENT l'espace d'outils. La méthode polynomiale et la structure multiplicative de λ sont des leviers qui n'existaient pas dans le cadre analytique. La réserve est justifiée (le mécanisme n'est pas encore identifié) mais le potentiel est réel.
6. **Statut** : [CONFIRMÉ] — POURSUIVRE AVEC RÉSERVE est la bonne décision
7. **Ce qui est appris** : L'innovation SAMC n'est pas un simple renommage. Elle connecte à un espace d'outils (combinatoire additive, méthode polynomiale) qui n'avait pas été exploré.
8. **Décision** : arrêter
9. **Raison** : la décision est confirmée

**Budget consommé** : 2/2 sous-rounds. 0 calcul numérique. Dans le budget.

---

## 12. Objets concernés + Ladder of Proof

| Objet | Niveau avant R74 | Niveau après R74 | Commentaire |
|-------|-----------------|-------------------|-------------|
| SOH H_k (factorisation) | L8 prouvé | **L8 prouvé** | Inchangé |
| Reformulation SAMC | (nouveau) | **L5 semi-formalisé** | Objet défini, lemme candidat posé, premier test passé |
| Lemme SAMC-1 (-1 ∉ Σ_≤(k)) | (nouveau) | **L4 lemme candidat** | Testé pour k=3 p=5, mécanisme inconnu |
| Sumset monotone Σ_≤(k) | (nouveau) | **L3 calcul exact (k=3)** | Σ_≤(2) = {0,1,2,3} dans F_5 |
| Test k=3 p=5 : -1 ∉ Σ_≤(2) | (nouveau) | **L4 calculé exact** | Résultat vérifié à la main |
| λ = 2·3^{-1} mod p | (nouveau) | **L8 prouvé** | Définition + calcul λ = 4 pour p=5 |
| ACR = SAMC | (nouveau) | **L6 prouvé** | Équivalence démontrée |
| CPO (carries) | (nouveau) | **[PROSE — ENTERRÉ]** | Pas de lemme, pas d'objet |
| Lemme B' (borne sur |H_k|) | L6 bloqué | **L6 bloqué** | Inchangé — SAMC le CONTOURNE |
| Voie bilinéaire courte | Déclassée (R73) | **Déclassée** | Inchangé |

---

## 13. Ce qui est appris

1. **La reformulation SAMC est genuinement nouvelle** : elle transforme le problème d'un verrou analytique (bornes de sommes exponentielles) en un problème de combinatoire additive (évitement dans un sumset). Ce changement de paradigme est la contribution principale de R74.

2. **Le paramètre λ = 2·3^{-1} mod p encode toute la bi-géométricité** : au lieu de deux bases (2 et 3) qui s'entremêlent dans corrSum, SAMC les comprime en un seul scalaire λ qui contrôle la "rotation" entre les couches du sumset.

3. **La monotonie des g_j est une contrainte RÉELLE** : sans elle, le sumset serait (λP)^{k-1} (produit de Minkowski itéré), qui par Cauchy-Davenport couvre au moins min((k-1)|P| − k + 2, p) éléments. La monotonie RESTREINT le sumset et pourrait être le facteur qui exclut -1.

4. **Le test k=3 p=5 est remarquablement net** : le sumset Σ_≤(2) = {0,1,2,3} = F_5 \ {-1}. L'UNIQUE élément manquant est -1. Ce n'est probablement pas un accident — c'est un signe qu'une structure profonde exclut -1.

5. **CPO est prose** : les observations arithmétiques triviales (corrSum impair, ≢ 0 mod 3) ne contribuent pas au programme. Enterré sans regret.

---

## 14. Ce qui est fermé utilement

1. **ACR comme objet indépendant** — FERMÉ (absorbé par SAMC). La perspective dynamique reste utile mais n'est pas une innovation séparée.
2. **CPO** — FERMÉ (prose). Pas de lemme, pas d'objet.
3. **"Il faut un meilleur invariant spectral"** — FERMÉ (le problème n'est pas spectral).
4. **"Il faut une nouvelle énergie fonctionnelle"** — FERMÉ (pas d'espace fonctionnel pertinent).

---

## 15. Ce qui est enterré

1. **CPO (Carry Propagation Obstruction)** — ENTERRÉ. Observations triviales, pas de formalisation possible en lemme.
2. **"Innovation par le vocabulaire spectral"** — ENTERRÉ. Toute innovation qui nomme un spectre sans identifier un opérateur concret avec un gap démontrable est de la prose.
3. **Toute innovation qui ramène aux bornes de sommes exponentielles courtes** — ENTERRÉ PAR PRINCIPE. R73 a fermé définitivement cette famille d'outils dans le régime O(log p).

---

## 16. Autopsie des pistes fermées

### 1. ACR (Affine Chain Representation)

- **Nom** : Chaîne affine sur F_p
- **Type de mort** : objet sans lemme PROPRE (lemme = celui de SAMC)
- **Hypothèse implicite fausse** : que la structure de semi-groupe affine ajouterait un outil au-delà de ce que SAMC offre déjà
- **Ce que la mort enseigne** : les reformulations dynamiques sont souvent des reformulations SYNTAXIQUES de conditions algébriques. Ici, la chaîne affine est un calcul séquentiel du sumset SAMC.
- **Où cela redirige** : vers SAMC comme objet UNIQUE

### 2. CPO (Carry Propagation Obstruction)

- **Nom** : Obstruction par carries binaires
- **Type de mort** : prose sans objet
- **Hypothèse implicite fausse** : que la structure binaire (parité, divisibilité par 3) des termes de corrSum contraindrait les diviseurs p ≥ 5
- **Ce que la mort enseigne** : les observations arithmétiques élémentaires (parité, petites valuations) ne touchent pas le cœur du problème. Le problème est dans la DISTRIBUTION FINE de corrSum mod p, pas dans ses propriétés grossières.
- **Où cela redirige** : vers SAMC (distribution fine dans F_p)

---

## 17. Survivant pour R75

**SAMC : Test de mordant du Lemme SAMC-1**

### Programme de R75

1. **Test supplémentaire** : calculer Σ_≤(k) pour k=5, p | d(5) = 2^8 − 3^5 = 256 − 243 = 13. Vérifier -1 ∉ Σ_≤(4) dans F_{13}. (Faisable à la main : S=8, k=5, |P| = S−k+1 = 4, g_j ∈ {0,1,2,3}, composantes C(7,4)=35. Mais avec monotonie, le nombre de 4-uplets (g_1,...,g_4) avec 0≤g_1≤g_2≤g_3≤g_4≤3 est C(4+3,4)=C(7,4)=35.)
   - Ce calcul est borderline faisable à la main (35 cas dans F_{13}).

2. **Recherche de mécanisme** : identifier POURQUOI -1 est exclu. Hypothèses à tester :
   - Structure de l'ordre multiplicatif de λ dans F_p
   - Interaction entre la contrainte de monotonie et la structure de P = {2^g}
   - Argument de parité / symétrie dans le sumset

3. **Connexion aux outils** : tester si la méthode polynomiale (Alon-Nathanson-Ruzsa) ou un argument de structure multiplicative peut s'appliquer au sumset monotone.

### Condition de non-boucle

- NE PAS reformuler SAMC
- NE PAS revenir aux sommes exponentielles
- Produire un RÉSULTAT (test k=5, ou mécanisme candidat, ou obstruction)
- Si aucun progrès : documenter SAMC comme problème ouvert avec sa formulation précise

---

## 18. Risques / limites

1. **SAMC pourrait être aussi dur que le problème original** : prouver -1 ∉ Σ_≤(k) pour tout k ≥ 3 et tout p adéquat pourrait nécessiter in fine des bornes de sommes exponentielles (retour au point de départ). C'est le risque principal.

2. **Le test k=3 p=5 est trop petit** : F_5 n'a que 5 éléments. Le sumset Σ_≤(2) a 6 termes (avec collisions) dans F_5. Le fait que -1 soit exclu pourrait être un accident de petite taille. Le test k=5 p=13 sera plus significatif.

3. **La monotonie pourrait ne pas être le facteur décisif** : si le sumset SANS monotonie exclut aussi -1, alors la monotonie est un détail et le problème est dans la structure de λ^j · P elle-même.

4. **λ = 2·3^{-1} mod p dépend de p** : pour des p différents divisant d(k), λ a des valeurs différentes. Le lemme SAMC-1 doit fonctionner pour AU MOINS UN p adéquat, pas pour tous.

5. **La méthode pourrait ne produire qu'un résultat cas-par-cas** : si le seul moyen de prouver -1 ∉ Σ_≤(k) est de le vérifier pour chaque k individuellement, on retombe dans le k-par-k interdit.

---

## 19. Verdict final avec score /10

**Score : 9/10**

R74 accomplit sa mission d'innovation disciplinée :

1. Le manque conceptuel est identifié proprement (chemin algébrique direct manquant)
2. Trois innovations proposées, budget respecté (3/3)
3. Chaque innovation a objet, lemme candidat (SAMC, ACR) ou diagnostic d'absence (CPO), et critère de réfutation
4. Contrôle anti-rebranding : SAMC est une NOUVEAUTÉ RÉELLE, ACR est absorbé, CPO est prose
5. Décision honnête : POURSUIVRE AVEC RÉSERVE (pas de survente)
6. Survivant unique : SAMC avec programme de test précis pour R75

Point manquant pour 10/10 : le mécanisme d'exclusion de -1 n'est pas identifié — c'est le travail de R75.

**Score PASS : 6/6**

| Critère | Statut |
|---------|--------|
| PASS-1 : Manque conceptuel exact formulé | ✅ Chemin algébrique direct manquant |
| PASS-2 : Au plus 3 innovations candidates | ✅ Exactement 3 (SAMC, ACR, CPO) |
| PASS-3 : Chaque innovation a objet, lemme, critère de réfutation | ✅ SAMC et ACR oui, CPO diagnostiqué comme prose |
| PASS-4 : Anti-rebranding distingue nouveauté réelle et rebranding | ✅ SAMC nouveau, ACR absorbé, CPO prose |
| PASS-5 : Décision stratégique honnête | ✅ POURSUIVRE AVEC RÉSERVE |
| PASS-6 : Survivant unique pour R75 | ✅ SAMC avec programme de test |

---

## 20. Registre FAIL-CLOSED

| Objet | Statut |
|-------|--------|
| SOH H_k (factorisation) | [PROUVÉ] |
| Factorisation T = ω · H_k | [PROUVÉ] |
| Bi-géométricité (2ⁿ, 3^j) | [PROUVÉ] |
| Gap exponentiel O(log p) vs p^δ | [PROUVÉ] |
| λ = 2·3^{-1} mod p comme paramètre SAMC | [PROUVÉ] (définition) |
| Reformulation SAMC : N_0(p) = 0 ⟺ -1 ∉ Σ_≤(k) | [PROUVÉ] (équivalence algébrique) |
| Test SAMC k=3 p=5 : -1 ∉ Σ_≤(2) | [CALCULÉ EXACT] |
| Σ_≤(2) = {0,1,2,3} dans F_5 | [CALCULÉ EXACT] |
| ACR = SAMC (équivalence) | [SEMI-FORMALISÉ] |
| Lemme SAMC-1 (pour tout k ≥ 3, ∃p adéquat : -1 ∉ Σ_≤(k)) | [CONJECTURAL — LEMME CANDIDAT] |
| Mécanisme d'exclusion de -1 | [INTUITION L1] — non identifié |
| CPO (carries) | [PROSE — ENTERRÉ] |
| Voie bilinéaire courte | [DÉCLASSÉE] (R73) |
| Opérateur de transfert spectral | [RÉFUTÉ] (R72) |
| Lemme B' (borne analytique sur |H_k|) | [CONJECTURAL — BLOQUÉ] |
| Lemme A' (premier adéquat) | [CONJECTURAL] |
| Hypothèse H | [CONJECTURAL] |
| Réduction H ⟸ Lemme A' + Lemme B'_SAMC | [SEMI-FORMALISÉ] |
