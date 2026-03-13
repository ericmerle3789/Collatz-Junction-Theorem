

TYPE: P
OBJET CIBLÉ: équidistribution utile de d_δ en R3 + D_∞(d_δ) + chaîne D_∞ ⇒ τ<1 ⇒ α<1 ⇒ K-lite
QUESTION CENTRALE: Peut-on faire monter le survivant de R62 d’un cran vers un premier lemme semi-prouvé utile, en réduisant rigoureusement D_∞(d_δ) à une famille précise d’objets analytiques ou combinatoires attaquables en régime R3, suffisamment forte pour soutenir τ(r) ≤ 1/2 + η < 1 ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: identifier clairement si le vrai verrou restant est la réduction de D_∞, l’outil analytique choisi, ou l’adaptation au sous-groupe, et enterrer proprement toute route trop faible ou mal adaptée avec autopsie complète.

# BRIEF CLAUDE CODE — ROUND 63 (R63)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R62.

### Contexte acquis
- R57–R59 ont transformé la base k=2 en problème de théorie des nombres bien posé via :
  - δ = b−a
  - c_δ = 1 + g·2^δ
  - N_r = #{δ : dlog(r/c_δ) ∈ [0, M−δ]}
- R59 a sélectionné la route prioritaire :
  - **Lemme K-lite via barrier counting**
  avec cible réaliste
  - max N_r ≤ C/p + α(M+1), α<1
- R60 a articulé le schéma de preuve en 4 sous-étapes et réduit le verrou unique à :
  - **(c)** contrôle du taux de transition hit-hit
- R61 a sélectionné le bon noyau :
  - **hit-hit-lite pointwise**
  - en priorité dans le régime **R3**
- R62 a fait le resserrement décisif :
  - la géométrie des fenêtres fournit déjà la dilution principale ;
  - le verrou restant est d’obtenir une **équidistribution suffisante de d_δ** ;
  - la chaîne stratégique est désormais :
    D_∞(d_δ) petit ⇒ τ(r) ≤ 1/2 + D_∞ < 1 ⇒ α<1 ⇒ K-lite.
- R62 a aussi enterré les mauvaises routes :
  - faux débats sur la métrique ;
  - auxiliaires seuls ;
  - formulations trop ambitieuses sans régime ni constante réalistes.
- Le risque stratégique est maintenant :
  - refaire une carte abstraite de D_∞ sans réduction utile ;
  - invoquer des outils prestigieux non adaptés au sous-groupe ;
  - ou confondre un bon signal numérique avec une réduction théorique propre.

## Objectif de R63
R63 doit répondre à cette question centrale :

> Peut-on réduire proprement le contrôle de D_∞(d_δ) en R3 à une famille précise d’objets analytiques ou combinatoires attaquables, de sorte que le bridge vers τ<1 ne repose plus sur une simple intuition d’équidistribution mais sur une vraie pièce de preuve intermédiaire ?

R63 doit être un round proof-oriented très centré.
Pas de dispersion.
Pas de campagne computationnelle large.
Le but est de transformer “il faut de l’équidistribution” en “voici exactement l’objet qu’il faut borner”.

---

# ARCHITECTURE GÉNÉRALE

## Pièce principale unique
**Réduction théorique de D_∞(d_δ) en R3**

## Pièces auxiliaires autorisées mais subordonnées
- **hit-hit** comme conséquence directe de la réduction ;
- **nesting** seulement si cela simplifie une étape locale ;
- **cross** conservé comme conséquence stratégique, sans nouvelle attaque frontale.

Le round doit dire explicitement si, après R63, le vrai verrou principal reste la réduction de D_∞ elle-même, ou s’il devient l’outil analytique/combinatoire final nécessaire pour la fermer.

---

# AXE A — INVESTIGATEUR / FORMULATION PRÉCISE DE D_∞
## Nom de travail
Que faut-il exactement contrôler ?

## Mission
Formuler le contrôle de D_∞(d_δ) de manière mathématiquement précise et utile pour la chaîne de preuve, en choisissant la bonne notion de discrepancy et le bon domaine.

### Questions obligatoires
1. Quelle est la formulation canonique la plus utile de D_∞ ici ?
   - discrepancy additive sur les dlogs,
   - discrepancy sur le sous-groupe ⟨2⟩,
   - comptage dans intervalles/fenêtres,
   - autre formulation équivalente plus exploitable
2. Quel est le plus petit énoncé utile déjà assez fort pour obtenir τ(r) ≤ 1/2 + η ?
3. Quel rôle exact joue le régime R3 dans cette formulation ?
4. Quelle dépendance en paramètres est réaliste à ce stade ?
   - borne absolue petite,
   - borne en fonction de ord,
   - borne en fonction de M,
   - autre
5. Quelle partie du problème est déjà absorbée par la structure des fenêtres, et quelle partie relève entièrement de D_∞ ?

### Livrables
- formulation canonique de D_∞ ;
- meilleur énoncé intermédiaire utile ;
- rôle exact de R3 ;
- un premier sous-lemme candidat si possible.

---

# AXE B — INVESTIGATEUR / RÉDUCTION VERS UN OUTIL ATTAQUABLE
## Nom de travail
À quoi réduire D_∞ ?

## Mission
Réduire D_∞ à une famille précise d’objets ou d’estimations réellement attaquables, en évitant les outils déjà enterrés ou non adaptés.

### Questions obligatoires
1. Quelle réduction paraît la plus crédible ?
   - Erdős–Turán / sommes exponentielles adaptées,
   - congruences/incidences sur le sous-groupe,
   - somme bilinéaire restreinte,
   - autre réduction plus naturelle
2. Quel est l’objet final exact à borner ?
   - une somme exponentielle sur c_δ,
   - une corrélation de dlogs,
   - un comptage d’incidences,
   - autre
3. Quels outils sont explicitement morts ou mal adaptés ici ?
   - Weil direct non adapté,
   - pseudo-aléa naïf,
   - large sieve générique,
   - autres
4. Peut-on déjà distinguer ce qui est standard et ce qui demanderait un ingrédient réellement nouveau ?
5. Quelle réduction semble la plus démontrable dans le temps court d’un round ?

### Livrables
- réduction prioritaire clairement écrite ;
- objet final à borner identifié ;
- liste explicite des outils morts à ne pas ressusciter ;
- un premier sous-lemme candidat si possible.

---

# AXE C — INNOVATEUR / PREMIER NOYAU PROUVABLE POUR LE BRIDGE
## Nom de travail
D_∞-lite prouvable

## Mission
Proposer au plus 2 formulations candidates d’un premier noyau prouvable utile pour le bridge de R62.

### Candidat 1
**D_∞-lite par réduction analytique**
D_∞ est réduit à une famille explicite de sommes/corrélations, et cette réduction suffit déjà à faire de la chaîne D_∞ ⇒ τ<1 un vrai schéma de preuve conditionnel propre.

### Candidat 2
**D_∞-lite par réduction combinatoire**
D_∞ est réduit à un problème d’incidences/comptage sur le sous-groupe, moins élégant mais plus démontrable à court terme.

### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait immédiatement ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle ;
6. niveau estimé dans la Ladder of Proof.

## Règle obligatoire
À la fin :
- garder un seul survivant pour R64 ;
- éliminer l’autre explicitement ;
- justifier le choix par démontrabilité réelle, pas par élégance.

---

# AXE D — CONTRÔLE SECONDAIRE / CHAÎNE GLOBALE
## Nom de travail
Ne pas perdre K-lite et le cross de vue

## Mission
Sans faire du cross la cible principale, rappeler brièvement comment une réduction propre de D_∞ se réinjecte dans :
- τ<1,
- α<1,
- K-lite,
- base,
- puis cross.

### Questions obligatoires
1. Quel est le lien minimal “réduction de D_∞ → τ<1 → K-lite” à préserver ?
2. La réduction choisie change-t-elle seulement la pièce locale, ou reconfigure-t-elle la stratégie globale ?
3. Quel rappel concis faut-il conserver pour éviter toute dérive future ?

### Livrables
- rappel propre de la chaîne de conséquences ;
- aucune nouvelle attaque frontale du cross ;
- aucune dérive hors du verrou principal.

---

# CONTRÔLE SECONDAIRE OPTIONNEL
Un seul micro-test ciblé est autorisé si et seulement s’il aide à départager :
- réduction analytique vs combinatoire,
- ou deux formulations concurrentes de D_∞.
Pas de nouvelle base de données.
Pas de campagne de confort.

---

# REGISTRE MÉTHODOLOGIQUE OBLIGATOIRE

## 1. Type du round
Rappeler explicitement : P

## 2. IVS — Information Value Score
Donner une note /10 avec justification courte :
- potentiel de réfutation
- gain de structure
- proximité d’un lemme
- risque d’accumulation

## 3. Ladder of Proof
Pour chaque objet touché, préciser :
- intuition
- observation
- observation répétée
- calcul exact
- semi-formalisation
- schéma de preuve
- lemme candidat
- lemme prouvé
- résultat publiable

## 4. AUTOPSIE DES PISTES FERMÉES (OBLIGATOIRE)
Pour toute piste éliminée, fournir :
- Nom
- Type de mort :
  - contredite
  - mauvaise échelle
  - trop faible
  - non ciblante
  - redondante
  - absorbée
- Hypothèse implicite fausse
- Ce que la mort enseigne
- Où cela redirige

---

# CEC — CONSIGNE
CEC reste inchangé :
- Type A : obstruction première directe
- Type B : exclusion composite exacte
- Type C : exclusion composite par bornes combinées
- Type D : exclusion analytique via SPC / structure monotone composite

---

# CONTRAINTES MÉTHODOLOGIQUES
Tu dois distinguer explicitement :
- prouvé
- semi-prouvé
- calculé exact
- semi-formalisé
- heuristique
- conjectural
- réfuté

Tu ne dois pas :
- ressusciter pseudo-aléa naïf, large sieve générique, Weil direct non adapté, ou L²-hybride sous un autre nom ;
- faire du cross la cible principale du round ;
- lancer une campagne computationnelle large ;
- présenter D_∞ comme contrôlé tant que la réduction utile n’est pas clairement formulée.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : une formulation précise de D_∞ utile à la chaîne de preuve est isolée.
PASS-2 : une réduction prioritaire vers un objet attaquable est sélectionnée.
PASS-3 : un premier noyau de sous-lemme utile pour le bridge est formulé.
PASS-4 : au moins une tentative trop optimiste ou mal adaptée est éliminée avec autopsie complète.
PASS-5 : un survivant unique pour R64 est sélectionné.

# ÉCHEC UTILE
Même en cas d’échec, R63 est utile si :
- le vrai verrou de la réduction de D_∞ est clarifié ;
- une fausse bonne route est éliminée ;
- une version plus pauvre mais plus prouvable de la réduction est isolée.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats AXE A (formulation de D_∞)
5. Résultats AXE B (réduction vers outil)
6. Résultats AXE C (D_∞-lite)
7. Résultats AXE D (chaîne globale)
8. Contrôle secondaire éventuel
9. CEC inchangé
10. Objets concernés + Ladder of Proof
11. Ce qui est appris
12. Ce qui est enterré
13. Autopsie des pistes fermées
14. Survivant pour R64
15. Risques / limites
16. Verdict final avec score /10

---

# CONSIGNE FINALE
R63 doit transformer l’exigence “il faut de l’équidistribution” en réduction mathématique précise vers un objet vraiment attaquable.
Le but n’est pas de mieux raconter D_∞.
Le but est d’identifier exactement quoi borner pour faire tomber hit-hit puis K-lite.
Chercher la prochaine pièce prouvable, pas la théorie finale complète.
TYPE: P
OBJET CIBLÉ: équidistribution utile de d_δ en R3 + réduction de D_∞(d_δ) vers un objet analytique/combinatoire attaquable + chaîne ε-lite → K-lite gardée explicite
QUESTION CENTRALE: Peut-on faire monter le survivant de R62 d’un cran vers un premier schéma semi-prouvé utile, en réduisant rigoureusement le contrôle de D_∞(d_δ) en R3 à une famille précise de sommes, incidences, ou objets combinatoires, suffisamment bien posés pour soutenir ε>0 puis K-lite ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: identifier exactement quelle réduction de D_∞ est la bonne, et enterrer proprement toute route trop faible, trop générale, ou mal adaptée avec autopsie complète.

# BRIEF CLAUDE CODE — ROUND 63 (R63)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R62.

### Contexte acquis
- R57–R59 ont transformé la base k=2 en problème de théorie des nombres bien posé via :
  - δ = b−a
  - c_δ = 1 + g·2^δ
  - N_r = #{δ : dlog(r/c_δ) ∈ [0, M−δ]}
- R59 a sélectionné la route prioritaire :
  - **Lemme K-lite via barrier counting**
  avec cible réaliste
  - max N_r ≤ C/p + α(M+1), α<1
- R60 a articulé le schéma de preuve en 4 sous-étapes et isolé le verrou unique :
  - **(a)** reformulation δ [PROUVÉ]
  - **(b)** injectivité / |S_δ|≤1 [PROUVÉ]
  - **(c)** contrôle du taux de transition hit-hit [VERROU]
  - **(d)** intégration ⇒ α<1 [dépend de (c)]
- R61 a stabilisé la bonne cible locale pour (c) :
  - **Hit-hit-lite pointwise**
  - en priorité dans le régime **R3**
- R62 a clarifié le mécanisme du verrou :
  - la **dilution géométrique** des fenêtres apporte déjà une contribution ~1/2 ;
  - le reste dépend d’un lemme d’**équidistribution suffisante** des d_δ ;
  - la chaîne utile devient :
    D_∞(d_δ) petit ⇒ τ < 1 ⇒ α < 1 ⇒ K-lite.
- Le round optimal suivant n’est donc plus “réétudier hit-hit”, mais :
  - **réduire D_∞(d_δ)** à un objet théorique précis et attaquable.
- Le risque stratégique est maintenant :
  - rester dans l’intuition “d_δ a l’air uniforme” ;
  - ou invoquer de grands outils (Weil, Bourgain, etc.) sans réduction propre au sous-groupe / à la suite affine.

## Objectif de R63
R63 doit répondre à cette question centrale :

> Peut-on réduire proprement le contrôle de D_∞(d_δ) en R3 à une famille précise d’objets analytiques ou combinatoires (sommes exponentielles, incidences, corrélations, etc.), de sorte que le verrou de R62 cesse d’être un principe flou et devienne une cible mathématique nette ?

R63 doit être un round proof-oriented très centré.
Pas de dispersion.
Pas de campagne computationnelle large.
Le but est de transformer le verrou “équidistribution suffisante” en problème technique explicite.

---

# ARCHITECTURE GÉNÉRALE

## Pièce principale unique
**Réduction de D_∞(d_δ) à un objet attaquable**

## Pièces auxiliaires autorisées mais subordonnées
- la géométrie des fenêtres comme contexte, pas comme nouveau moteur ;
- le nesting comme auxiliaire secondaire déjà calibré ;
- le cross comme conséquence stratégique, sans nouvelle attaque frontale.

Le round doit dire explicitement si, après R63, le verrou principal est enfin un objet mathématique assez précis pour justifier une attaque de preuve spécialisée.

---

# AXE A — INVESTIGATEUR / RÉDUCTION DE D_∞
## Nom de travail
À quoi faut-il vraiment réduire l’équidistribution ?

## Mission
Chercher la meilleure réduction rigoureuse du contrôle de D_∞(d_δ) à une famille d’objets mathématiques explicites.

### Questions obligatoires
1. Quelle est la formulation canonique la plus utile de D_∞(d_δ) ?
   - discrepancy sur intervalles du groupe multiplicatif,
   - sommes exponentielles sur les dlogs,
   - corrélations le long de la suite affine c_δ,
   - incidences avec la barrière,
   - autre formulation équivalente plus attaquable
2. Quelle réduction paraît la plus propre ?
   - Erdős–Turán vers sommes exponentielles,
   - argument combinatoire d’incidence,
   - énergie/additive combinatorics,
   - autre
3. Quels paramètres exacts gouvernent la difficulté ?
   - ord_p(2),
   - longueur M,
   - structure de c_δ,
   - régime R3,
   - autre
4. Peut-on isoler un objet “minimal” à contrôler, plus précis que D_∞ lui-même ?
5. Quelle réduction semble trop générale ou mal adaptée malgré son prestige ?

### Livrables
- une formulation canonique de D_∞ ;
- une réduction prioritaire ;
- un objet minimal cible ;
- une hiérarchie honnête des paramètres et difficultés.

---

# AXE B — INVESTIGATEUR / OUTILS VIVANTS VS OUTILS MORTS
## Nom de travail
Quelle boîte à outils reste réellement ouverte ?

## Mission
Distinguer les outils vraiment compatibles avec la réduction choisie de ceux qui sont déjà morts, trop faibles, ou mal adaptés.

### Questions obligatoires
1. Quels outils restent vivants pour la réduction choisie ?
   - sommes exponentielles adaptées au sous-groupe,
   - versions fines d’Erdős–Turán,
   - arguments d’incidence ciblés,
   - structure de récurrence affine c_{δ+1}=2c_δ−1,
   - autre
2. Quels outils sont explicitement morts ou doivent rester interdits ?
   - pseudo-aléa naïf,
   - large sieve brut,
   - L²→L∞ générique,
   - Weil directe hors-cadre,
   - autres
3. Le premier sous-lemme utile doit-il être :
   - analytique,
   - combinatoire,
   - hybride,
   - conditionnel sur un théorème externe bien identifié ?
4. Quel outil paraît le plus démontrable dans le temps court d’un round ?
5. Quelle route paraît séduisante mais serait probablement une redite déguisée ?

### Livrables
- comparaison honnête des outils vivants ;
- liste explicite des outils morts à ne pas ressusciter ;
- sélection de la route prioritaire ;
- un premier sous-lemme candidat si possible.

---

# AXE C — INNOVATEUR / NOYAU PROUVABLE APRÈS R62
## Nom de travail
D_∞-lite prouvable

## Mission
Proposer au plus 2 formulations candidates d’un premier noyau prouvable utile pour le verrou identifié par R62.

### Candidat 1
**D_∞-lite via réduction analytique propre**
Un lemme de réduction explicite ramène D_∞(d_δ) à une famille de sommes ou corrélations bien identifiées, ce qui transforme le verrou en cible technique nette pour R64.

### Candidat 2
**D_∞-lite via réduction combinatoire**
Un énoncé combinatoire sur la suite affine c_δ et les fenêtres suffit à produire une borne faible mais utile sur D_∞, sans passer par un outillage analytique trop lourd.

### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait immédiatement ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle ;
6. niveau estimé dans la Ladder of Proof.

## Règle obligatoire
À la fin :
- garder un seul survivant pour R64 ;
- éliminer l’autre explicitement ;
- justifier le choix par démontrabilité réelle, pas par élégance.

---

# AXE D — CONTRÔLE SECONDAIRE / CHAÎNE GLOBALE
## Nom de travail
Ne pas casser la logique base → cross

## Mission
Sans faire du cross la cible principale, rappeler brièvement comment la réduction choisie pour D_∞ se réinjecte dans :
- ε-lite,
- K-lite,
- base,
- puis cross.

### Questions obligatoires
1. Quel est le lien minimal “réduction de D_∞ → ε>0 → α<1 → K-lite” à préserver ?
2. La réduction choisie modifie-t-elle la stratégie globale, ou seulement la sous-étape (c) ?
3. Quel rappel concis faut-il conserver pour éviter toute dérive future ?

### Livrables
- rappel propre de la chaîne de conséquences ;
- aucune nouvelle attaque frontale du cross ;
- aucune dérive hors du verrou principal.

---

# CONTRÔLE SECONDAIRE OPTIONNEL
Un seul micro-test ciblé est autorisé si et seulement s’il aide à départager :
- réduction analytique vs réduction combinatoire,
- ou deux objets minimaux concurrents pour D_∞.
Pas de nouvelle base de données.
Pas de campagne de confort.

---

# REGISTRE MÉTHODOLOGIQUE OBLIGATOIRE

## 1. Type du round
Rappeler explicitement : P

## 2. IVS — Information Value Score
Donner une note /10 avec justification courte :
- potentiel de réfutation
- gain de structure
- proximité d’un lemme
- risque d’accumulation

## 3. Ladder of Proof
Pour chaque objet touché, préciser :
- intuition
- observation
- observation répétée
- calcul exact
- semi-formalisation
- schéma de preuve
- lemme candidat
- lemme prouvé
- résultat publiable

## 4. AUTOPSIE DES PISTES FERMÉES (OBLIGATOIRE)
Pour toute piste éliminée, fournir :
- Nom
- Type de mort :
  - contredite
  - mauvaise échelle
  - trop faible
  - non ciblante
  - redondante
  - absorbée
- Hypothèse implicite fausse
- Ce que la mort enseigne
- Où cela redirige

---

# CEC — CONSIGNE
CEC reste inchangé :
- Type A : obstruction première directe
- Type B : exclusion composite exacte
- Type C : exclusion composite par bornes combinées
- Type D : exclusion analytique via SPC / structure monotone composite

---

# CONTRAINTES MÉTHODOLOGIQUES
Tu dois distinguer explicitement :
- prouvé
- semi-prouvé
- calculé exact
- semi-formalisé
- heuristique
- conjectural
- réfuté

Tu ne dois pas :
- ressusciter pseudo-aléa naïf, large sieve brut, ou L²→L∞ générique sous un autre nom ;
- faire du cross la cible principale du round ;
- lancer une campagne computationnelle large ;
- présenter D_∞ comme contrôlé tant que la réduction utile n’est pas explicitement formulée.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : une formulation canonique utile de D_∞ est isolée.
PASS-2 : une réduction prioritaire est sélectionnée proprement.
PASS-3 : un objet minimal cible est identifié.
PASS-4 : au moins une route trop générale ou trop faible est éliminée avec autopsie complète.
PASS-5 : un survivant unique pour R64 est sélectionné.

# ÉCHEC UTILE
Même en cas d’échec, R63 est utile si :
- le vrai verrou de D_∞ est clarifié ;
- une fausse bonne réduction est éliminée ;
- une version plus pauvre mais plus prouvable de la réduction est isolée.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats AXE A (réduction de D_∞)
5. Résultats AXE B (outils vivants vs morts)
6. Résultats AXE C (D_∞-lite)
7. Résultats AXE D (chaîne globale)
8. Contrôle secondaire éventuel
9. CEC inchangé
10. Objets concernés + Ladder of Proof
11. Ce qui est appris
12. Ce qui est enterré
13. Autopsie des pistes fermées
14. Survivant pour R64
15. Risques / limites
16. Verdict final avec score /10

---

# CONSIGNE FINALE
R63 doit transformer le verrou identifié par R62 en objet technique explicite.
Le but n’est pas de rediscuter encore la dilution géométrique.
Le but est de réduire D_∞(d_δ) à une cible mathématique précise et attaquable, suffisamment nette pour qu’un round suivant puisse tenter une vraie attaque de preuve.
Chercher la prochaine réduction prouvable, pas la théorie finale complète.