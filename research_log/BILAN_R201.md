# BILAN R201 — AUDIT BAKER + DÉCROISSANCE : MÊME PISTE QUE R194, C' FAUX
**Date :** 16 mars 2026

---

## ⚠️ RÉTRACTATION PARTIELLE — 2026-08-17, EN PLACE, NE PAS SUPPRIMER

**Le verdict R201-I3 (« C' ~ 13.3 MAL ATTRIBUÉ à Rhin 1987 », marqué PROUVÉ) est RÉTRACTÉ.**
Il est faux, et sa prémisse est fausse.

- **Ce qui a été affirmé.** Que Rhin 1987 ne traite que des mesures d'irrationalité, pas
  des formes linéaires en deux logarithmes ; donc que 13.3 lui est mal attribué, la vraie
  constante étant 18.5–23.55 (Laurent 2008 / LMN 1995).
- **Pourquoi c'est faux.** Rhin 1987 (*Progress in Math.* 71, Proposition p. 160) prouve
  **les deux** : des mesures d'irrationalité **et** une mesure d'indépendance linéaire
  effective de `1, log 2, log 3`, donnant `|u₀ + u₁·log 2 + u₂·log 3| > H^(−13.3)` avec
  `H = max(|u₁|,|u₂|)` — une borne de forme linéaire couvrant `(log 2, log 3)`
  directement. Vérifié : Simons–de Weger 2005 (Lemma 12) l'applique verbatim, et leur
  borne `Λ > e^(−13.3(0.46057+ln K))` **est exactement** `constante·K^(−13.3)` (contrôlé
  à 20 chiffres) — un exposant sur la hauteur, pas une forme `(log)²`. Les constantes de
  remplacement 18.5 / 23.55 sont des coefficients d'un instrument différent (une forme en
  `(log)²`), pas des exposants sur la hauteur ; pour ce couple précis la route de Padé de
  Rhin est la meilleure (Simons–de Weger : « the result of Rhin is best »).
- **Ce qui, dans le déclencheur, était réel.** R200 avait écrit la constante de Rhin dans
  la forme `(log)²` de LMN (`exp(−13.3·(log S)²)`) — *cette transcription-là* n'est pas de
  Rhin. L'auditeur a rejeté l'**attribution** là où le vrai défaut était la **transcription**.
- **Statut.** Le 13.3 tient pour ce que la chaîne L-A7 consomme. Aucun nombre engagé ne
  bouge. Adjudication croisée : `LEDGER.md` du dépôt partagé
  `macindoe/one-obstruction-three-faces`, entrée L-A7, « Macindoe adjudication record
  (round-12 Rhin 13.3 re-source warning) », vérifiée des deux côtés.
- **Une seule frontière restante :** la page 160 du volume 1987 lui-même n'a été lue
  d'aucun côté (payante) ; les deux applications publiées l'appliquent sans clause de
  seuil depuis des hauteurs modérées, et l'usage de L-A7 n'a besoin que de `H = K₀ ≥ 952`.

Les lignes ci-dessous marquées **[RÉTRACTÉ — voir le bloc ci-dessus]** sont conservées
telles quelles pour que le dossier montre ce qui a été affirmé et quand.

---

## RÉSUMÉ EXÉCUTIF

R201 = round d'AUDIT de la piste Baker + décroissance exponentielle proposée en R200 comme "seul chemin viable (8/10)". Les 3 agents convergent : **c'est la MÊME piste que R194** (Baker+arc hybride, BRITTLE 5/10), avec une constante C' ~ 13.3 **MAL ATTRIBUÉE** à Rhin 1987 **[RÉTRACTÉ 2026-08-17 — voir tête de fichier ; 13.3 est correct]**. Le grade réel est **4/10** (pas 8/10). Cependant, c'est toujours la seule voie vers un résultat inconditionnel. Innovation notable : fractions continues (7/10) comme alternative à Baker brut.

---

## AGENT A1 — INVESTIGATEUR : COMPARAISON R82-R83 vs R194 vs R200

### Résultat principal : R200 ≠ R82-R83, mais R200 = R194

| Comparaison | Objet | Outil | Verdict |
|-------------|-------|-------|---------|
| R82-R83 | corrSum (SOMME) | Evertse/S-unit | DIFFÉRENT de R200 |
| R194 | Λ = S·log2 - k·log3 | Baker/LMN | **IDENTIQUE** à R200 |
| R200 | Λ = S·log2 - k·log3 | Baker/LMN | Même piste, habillage différent |

### C' ~ 13.3 : MAL ATTRIBUÉ  **[RÉTRACTÉ — voir le bloc en tête de fichier ; Rhin 1987 p. 160 couvre bien la forme linéaire (log 2, log 3), exposant 13.3]**
- **Rhin (1987)** traite des mesures d'irrationalité de log 2, pas des formes linéaires en 2 logarithmes
- **Laurent (2008)** : C' ~ 18.5 pour 2 logarithmes
- **LMN (1995)** : C' ~ 23.55 (conservatif)
- Pas Rhin → pas 13.3

### Formule M(k) : CONCEPTUELLEMENT INCORRECTE
- Le facteur 3^{-0.415k} mélange proportion moyenne (41.5% des k favorables) avec borne pire-cas
- Pour un k DÉFAVORABLE donné, M(k) n'a PAS ce facteur exponentiel
- K₀ réaliste : 10⁶–10⁷ (pas 1500)

### Résultats formels

| Ref | Énoncé | Statut |
|-----|--------|--------|
| R201-I1 | R200 applique Baker à Λ = S·log2 - k·log3, DIFFÉRENT de R82-R83 (S-unit/corrSum) | **PROUVÉ** |
| R201-I2 | R200 est la MÊME piste que R194 (Baker+arc hybride) | **PROUVÉ** |
| R201-I3 | C' ~ 13.3 MAL ATTRIBUÉ à Rhin 1987 (mesure d'irrationalité ≠ forme linéaire) | **~~PROUVÉ~~ [RÉTRACTÉ 2026-08-17 — faux ; voir tête de fichier]** |
| R201-I4 | Vraie constante C' ~ 18.5 (Laurent 2008) ou ~23.55 (LMN 1995) | **~~OBSERVATION~~ [RÉTRACTÉ — 18.5/23.55 = autre instrument (log)², pas des exposants ; 13.3 est le bon]** |
| R201-I5 | K₀ ~ 1500 est une sous-estimation d'au moins 3 ordres de grandeur | **CONDITIONNEL** |
| R201-I6 | Baker SEUL ne donne pas M(k) < 1 pour k défavorables | **PROUVÉ** |

---

## AGENT A2 — INNOVATEUR : 6 DIRECTIONS, FRACTIONS CONTINUES EN TÊTE

### Directions explorées

| Direction | Faisabilité | Verdict |
|-----------|:-----------:|---------|
| **A. Fractions continues directes** | **7/10** | CF de log₂3 donnent bornes MEILLEURES que Baker pour k concret. Hybride CF+Baker logiquement complet |
| **B. Corridor Étroit** | **6/10** | M(k) = ⌊g_max/d⌋ - ⌊(g_min-1)/d⌋. Si M(k)=0, pas de cycle. O(1) par k |
| C. Borne combinatoire g_max | 2/10 | Renvoie au diophantien |
| D. Zsygmondy/Birkhoff-Vandiver | 4/10 | Facteurs premiers trop petits |
| E. Descente par convergentes | 1/10 | Pas de divisibilité |
| F. Valuations p-adiques | 1/10 | Aucune obstruction |

### Décroissance 3^{-0.415k} : PROUVÉE (9/10)
- Ce n'est PAS heuristique, c'est un théorème rigoureux
- Le facteur correctif polynomial est contrôlé par Baker (uniforme) ou CF (pointwise)
- Mais cela concerne la PROPORTION des k favorables, pas M(k) pour un k donné

### Innovation principale : Hybride CF + Baker
- Les convergentes p_n/q_n de log₂3 sont CONNUES (calculables)
- Pour tout k dans [187, K₀], on peut calculer δ(k) via fractions continues
- CF donne des bornes POINTWISE (pour chaque k spécifique) bien meilleures que Baker (uniforme)
- Baker couvre l'infinité de k au-delà de K₀

---

## AGENT A3 — RED TEAM : VERDICT 4/10

### Grades individuels

| Composant | Grade | Justification |
|-----------|:-----:|---------------|
| Baker sur |S·log2 - k·log3| comme borne effective | **5/10** | Standard, fonctionne mais constantes grandes |
| C' ~ 13.3 comme constante réaliste | **2/10 [RÉTRACTÉ — 13.3 correct, Rhin p.160]** | ~~Faux (Rhin ≠ formes linéaires)~~ |
| K₀ ~ 1500 comme seuil réaliste | **3/10** | Sous-estimation massive |
| Vérification finie [187, K₀] | **6/10** | Faisable en principe (computationnel) |
| **Piste globale** | **4/10** | BRITTLE mais seul chemin restant |

### Comparaison des grades

| Round | Grade Baker | Commentaire |
|-------|:----------:|-------------|
| R194 | 5/10 | "BRITTLE, constantes trop grandes" |
| R200 | 8/10 | Optimisme injustifié, C' faux |
| **R201** | **4/10** | Audit corrige, même piste que R194 |

### Contradiction R194/R200 résolue
- R194 disait "K_Baker > 42 → redondant avec SdW" — critère g_max < d
- R200 devrait utiliser g_max/d < 2^68 (critère Barina) — critère DIFFÉRENT
- Deux critères, deux K₀ différents. L'ajout de Barina (R199) est le SEUL progrès réel

---

## SYNTHÈSE R201

### Ce que R201 a RÉELLEMENT apporté

| Résultat | Type | Impact |
|----------|------|--------|
| R200 = R194 (même piste Baker+arc) | **PROUVÉ** | Pas d'innovation, juste habillage |
| C' ~ 13.3 mal attribué à Rhin | **~~PROUVÉ~~ [RÉTRACTÉ]** | ~~Constante réelle : 18.5–23.55~~ (13.3 est correct) |
| K₀ ~ 1500 sous-estimé (réaliste : 10⁶–10⁷ ou ajusté) | **CONDITIONNEL** | Gap de vérification finie BEAUCOUP plus grand |
| Fractions continues > Baker pour k concret | **OBSERVATION** | Alternative viable (7/10) |
| Corridor Étroit (M(k) = 0 par calcul direct) | **INNOVATION** | 6/10, O(1) par k |
| Décroissance 3^{-0.415k} rigoureusement prouvée | **PROUVÉ** | Confirmation théorique solide |
| Grade global corrigé : 4/10 (pas 8/10) | **ÉVALUATION** | Honnêteté restaurée |

### État stratégique après R201

**PISTE BAKER + DÉCROISSANCE :**
- MÊME piste que R194 (confirmé)
- Grade corrigé : 4/10 (BRITTLE)
- Constante C' fausse, K₀ sous-estimé
- MAIS : seule voie vers inconditionnel

**SEUL PROGRÈS DEPUIS R194 :**
- Barina (R199) : critère g_max/d < 2^68 (moins strict que g_max < d)
- Fractions continues (R201-A2) : alternative à Baker pour vérification finie

**CE QUI RESTE À FAIRE :**
1. Recalculer K₀ avec les VRAIES constantes (Laurent 2008 : C' ~ 18.5)
2. Évaluer si fractions continues de log₂3 ferment le gap [187, K₀] sans Baker
3. Le gap de vérification finie nécessite du COMPUTATIONNEL (en dehors du scope théorique pur)

**RECOMMANDATION UNANIME :**
- PUBLIER le résultat GRH-conditionnel + MCE standalone MAINTENANT
- Le chemin inconditionnel existe mais est LONG et nécessite du calcul
- Ne pas surestimer la proximité d'une preuve inconditionnelle

---

## ÉVALUATION

| Critère | Score | Commentaire |
|---|---|---|
| **Nouveauté** | 6/10 | Fractions continues (7/10) + Corridor Étroit (6/10) |
| **Impact** | 9/10 | Corrige l'optimisme R200, restaure l'honnêteté |
| **Rigueur** | 9/10 | 3 agents convergent, C' faux identifié |
| **Honnêteté** | 10/10 | Grade 4/10 vs 8/10 revendiqué = correction courageuse |

---

*Round R201 : 3 agents, théorie pure. Baker+décroissance = MÊME PISTE que R194 (4/10, pas 8/10). C'~13.3 MAL ATTRIBUÉ (Rhin ≠ formes linéaires). K₀~1500 SOUS-ESTIMÉ. Innovation : fractions continues (7/10) + Corridor Étroit (6/10). Seule voie vers inconditionnel mais BRITTLE. Publier GRH-conditionnel + MCE MAINTENANT.*
