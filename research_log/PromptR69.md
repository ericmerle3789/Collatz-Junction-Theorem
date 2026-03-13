TYPE: P/A
OBJET CIBLÉ: audit de dérivation du Junction Theorem pour déterminer noir sur blanc quelle quantité N_r est réellement requise, puis exploration autonome strictement bornée des seules conséquences légitimes de ce verdict
QUESTION CENTRALE: le Junction Theorem exige-t-il le compteur vrai N_r^true, le compteur indicé N_r^ind, ou une réduction mathématiquement licite entre les deux ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: fermer définitivement l’ambiguïté sur la nature exacte du compteur requis, requalifier proprement la chaîne R62→R68, et empêcher toute poursuite du programme sur un proxy mal identifié.
PRINCIPE D’ÉQUILIBRE: verrouiller les glissements d’objet, de compteur et de quantificateur, tout en autorisant une exploration autonome locale, courte et auditable, si et seulement si elle est déclenchée par le verdict définitionnel principal.

# BRIEF CLAUDE CODE — ROUND 69 (R69)

## Mission
Tu poursuis le projet Collatz après R68.

R69 a un verrou principal unique :
**déterminer avec traçabilité stricte quel compteur N_r est réellement requis par le Junction Theorem et par la chaîne logique menant au verrou de non-trivialité.**

Le round ne doit pas essayer de “sauver” narrativement les rounds précédents.
Le round doit établir le besoin exact, puis seulement ensuite autoriser une courte autonomie contrôlée sur les conséquences immédiates de ce verdict.

---

## Contexte acquis après R68
- R67 a montré qu’il existait une substitution de modèle entre la cible Collatz et le proxy QR.
- R68 a montré que l’obstacle ne porte pas seulement sur le sous-groupe ou le modèle multiplicatif, mais aussi potentiellement sur la **quantité comptée**.
- R68 a isolé une distinction critique entre au moins deux objets de comptage :
  - **N_r^ind** : compteur indicé / proxy simplifié ;
  - **N_r^true** : compteur vrai / multiplicité réellement issue du triangle.
- Le pont QR → Collatz sous forme naïve est fermé.
- La nouvelle question structurante est donc :
  - le théorème de jonction exige-t-il vraiment N_r^true,
  - ou N_r^ind,
  - ou une réduction licite de l’un vers l’autre ?
- Tant que cette question n’est pas résolue, aucun résultat ne doit être promu au rang de progrès décisif vers la non-trivialité.

---

# OBJECTIF DE R69
R69 doit répondre à cette question centrale :

> En retraçant la dérivation complète du Junction Theorem et de ses dépendances, quelle quantité exacte N_r est requise à chaque étape critique, et quelle reformulation finale est mathématiquement légitime ?

Les sorties acceptables du round sont :
1. **Le théorème exige N_r^true** ;
2. **Le théorème exige N_r^ind** ;
3. **Le théorème exige une relation explicite entre N_r^true et N_r^ind** ;
4. **Le théorème tel qu’énoncé est ambigu / mal typé et doit être reformulé avant tout nouveau round mathématique**.

Important :
- aucune sortie n’est recevable sans traçabilité ligne par ligne ou bloc par bloc de la dérivation ;
- aucune reformulation n’est recevable si elle change l’objet sans le déclarer explicitement ;
- aucune conclusion programmatique n’est recevable sans distinguer ce qui est acquis, insuffisant, requalifié ou enterré.

---

# ARCHITECTURE GÉNÉRALE

## Phase principale obligatoire
**PHASE 1 — Audit de dérivation fail-closed du Junction Theorem**

## Phase secondaire conditionnelle
**PHASE 2 — Autonomie contrôlée courte sur les conséquences immédiates du verdict de PHASE 1**

## Ce qui est interdit comme cible principale
- cross-résidu ;
- relance d’un nouveau proxy sans audit ;
- scans numériques larges “pour voir” ;
- reprise des preuves QR comme si elles suffisaient déjà ;
- narration d’avancement global sans clarification du compteur requis.

---

# PHASE 1 — AUDIT DE DÉRIVATION STRICT
## AXE A — INVESTIGATEUR / TRAÇABILITÉ LOGIQUE DU JUNCTION THEOREM
### Nom de travail
Quel N_r entre vraiment dans la machine ?

### Mission
Reprendre le Junction Theorem, son énoncé, ses dépendances, sa dérivation, ses usages dans le programme, et tracer **exactement** où intervient N_r, sous quelle définition, sous quel quantificateur, et avec quel rôle logique.

### Questions obligatoires
1. Quel est l’énoncé canonique actuel du Junction Theorem ?
2. À quels endroits précis N_r intervient-il dans cet énoncé ou sa dérivation ?
3. Chaque occurrence de N_r parle-t-elle du même objet ?
4. Quels indices, doubles indices, multiplicités ou projections sont réellement utilisés ?
5. Y a-t-il un glissement silencieux entre un compteur d’occurrence réelle et un indicateur simplifié ?
6. La dérivation exige-t-elle une borne uniforme, une borne en moyenne, une borne pointwise, ou autre chose ?
7. Quel est le plus petit tableau impossible à mal lire reliant :
   - définition du N_r ;
   - rôle logique ;
   - statut ;
   - dépendances ;
   - conséquence en cas de substitution fautive ?

### Livrables
- énoncé canonique actuel du Junction Theorem ;
- carte bloc-par-bloc de la dérivation ;
- tableau des occurrences de N_r ;
- localisation exacte de toute ambiguïté, substitution, ou collision de notations.

---

## AXE B — INVESTIGATEUR / TYPOLOGIE DES COMPTEURS
### Nom de travail
De quel comptage parle-t-on vraiment ?

### Mission
Formaliser proprement N_r^true, N_r^ind, et tout objet intermédiaire réellement utilisé, puis déterminer leurs relations exactes.

### Questions obligatoires
1. Définition canonique complète de N_r^true.
2. Définition canonique complète de N_r^ind.
3. Existe-t-il un troisième objet implicite (agrégé, projeté, tronqué, moyenné) utilisé sans être nommé ?
4. Quelles implications sont vraies entre ces objets ?
5. Quelles implications ont seulement l’air vraies ?
6. Dans quel sens une borne sur N_r^ind pourrait-elle être insuffisante pour N_r^true ?
7. Peut-on formuler un lemme de réduction licite ?
8. Quel est le meilleur argument pour dire que les deux objets ne sont pas interchangeables ?

### Livrables
- mini dictionnaire des compteurs ;
- tableau “même notation apparente / objets distincts” ;
- catalogue des implications vraies, fausses, ouvertes ;
- au moins un exemple ou mécanisme montrant comment une confusion peut fausser le programme.

---

## AXE C — INVESTIGATEUR / TEST DE SUFFISANCE LOGIQUE
### Nom de travail
Qu’est-ce qui suffit vraiment pour faire tourner le théorème ?

### Mission
Déterminer quel type de borne est logiquement suffisant pour que la chaîne du théorème tienne réellement.

### Questions obligatoires
1. Si l’on ne dispose que d’une borne sur N_r^ind, quelle étape exacte de la chaîne passe ?
2. Quelle étape exacte casse ?
3. Si une réduction N_r^true ≤ F(N_r^ind, ... ) est envisagée, est-elle prouvable ou simplement espérée ?
4. Existe-t-il une version reformulée du Junction Theorem où N_r^ind suffirait honnêtement ?
5. Une telle reformulation garde-t-elle la cible du programme ou change-t-elle le problème ?
6. Quel est le meilleur argument en faveur d’une suffisance de N_r^ind ?
7. Quel est le meilleur argument contre ?

### Livrables
Pour chaque thèse candidate :
- énoncé ;
- statut : [PROUVÉ] / [RÉFUTÉ] / [PARTIEL] / [AMBIGU] ;
- preuve, obstruction ou point exact de rupture ;
- impact sur la chaîne R62→R68.

Tu dois aussi inclure une mini section “contre-suffisance” :
- pourquoi on pourrait croire qu’un proxy suffit ;
- quel mécanisme concret peut invalider cette croyance ;
- ce qui survit après confrontation.

---

## AXE D — CONTRÔLE PROGRAMMATIQUE / REQUALIFICATION DE R62→R68
### Nom de travail
Qu’est-ce qui reste debout, qu’est-ce qui change de nom ?

### Mission
Requalifier proprement les rounds récents à la lumière du verdict de PHASE 1.

### Questions obligatoires
1. Si N_r^true est requis, que valent alors réellement R62→R68 ?
2. Si N_r^ind suffit, lesquels de ces rounds remontent réellement en valeur ?
3. Qu’est-ce qui doit être reclassé comme :
   - preuve valide mais sur proxy insuffisant ;
   - borne utile mais non décisive ;
   - observation numérique ;
   - fausse piste ;
   - pièce stratégique réutilisable ?
4. Quel est le nouveau verrou principal du programme après ce verdict ?
5. Quelle porte a été fermée utilement, et quelle porte nouvelle s’ouvre grâce à cette fermeture ?

### Livrables
- tableau de requalification de R62, R63, R64, R65, R66, R67, R68 ;
- état du programme sans inflation rhétorique ;
- survivant principal conditionné au verdict définitionnel.

---

# PHASE 2 — AUTONOMIE CONTRÔLÉE COURTE (CONDITIONNELLE)

## Activation
La PHASE 2 n’est autorisée qu’après un verdict explicite et motivé de PHASE 1.
Elle sert uniquement à explorer les conséquences immédiates du verdict principal.

## But
Permettre à Claude Code d’enchaîner en autonomie locale sur **au plus 3 sous-rounds internes** très courts, strictement bornés, pour tester la conséquence la plus rationnelle du verdict de PHASE 1.

## Autonomie autorisée
Claude Code peut, sans nouveau checkpoint externe, enchaîner au maximum :
- **S1** : consolidation du verdict ;
- **S2** : test d’un unique lemme conséquence ;
- **S3** : autopsie / clôture / survivant.

## Autonomie interdite
Claude Code ne peut pas, en PHASE 2 :
- changer la cible globale du programme ;
- promouvoir un proxy au rang de cible principale ;
- ouvrir plus d’une nouvelle reformulation innovante ;
- relancer cross-résidu ;
- lancer des scans numériques larges ;
- lancer une nouvelle campagne multi-fronts ;
- reformuler le théorème sans expliciter exactement ce qui est conservé et perdu.

## Événements STOP obligatoires
Arrêt immédiat de l’autonomie si l’un des événements suivants survient :
1. apparition d’un changement d’objet, de quantificateur ou de compteur ;
2. besoin d’une hypothèse nouvelle non prévue par PHASE 1 ;
3. impossibilité de classifier honnêtement un lemme central ;
4. conflit entre deux formulations du théorème ;
5. nécessité de réécrire l’énoncé principal du programme ;
6. absence de gain net sur deux sous-rounds internes successifs ;
7. apparition de plus d’un survivant crédible.

## Condition d’arrêt positive
La PHASE 2 doit aussi s’arrêter dès que l’un des cas suivants est atteint :
- un unique lemme conséquence est classé [PROUVÉ] ou [RÉFUTÉ] ;
- une reformulation minimale suffisante est isolée ;
- un unique survivant rationnel pour R70 est identifié ;
- il devient clair qu’aucune conséquence sûre ne peut être tirée sans audit externe.

## Format obligatoire de chaque sous-round autonome
Pour chaque sous-round interne S1/S2/S3, produire exactement :
1. hypothèse active ;
2. objet exact manipulé ;
3. question précise ;
4. démarche ;
5. résultat net ;
6. statut ;
7. ce qui est appris ;
8. décision : continuer / arrêter / bifurquer ;
9. raison de cette décision.

## Budget de divergence
- au plus **1** reformulation innovante nouvelle au total ;
- au plus **2** lemmes candidats centraux ;
- au plus **1** micro-test numérique secondaire, seulement si nécessaire pour départager deux formulations explicitement nommées.

---

# AXE E — INNOVATEUR / REFORMULATION MINIMALE SI NÉCESSAIRE
### Nom de travail
Nommer juste ce que l’obstacle révèle

### Mission
Si la PHASE 1 ou la PHASE 2 révèle qu’aucune formulation actuelle n’est proprement typée, l’innovateur peut proposer **au plus une** reformulation minimale.

### Règles strictes
- La reformulation doit être déclenchée par un obstacle identifié, pas par goût d’élégance.
- Elle doit préciser ce qu’elle conserve et ce qu’elle perd.
- Elle doit dire si elle rapproche réellement du but de non-trivialité ou si elle ne fait que clarifier un proxy.
- Elle doit avoir un pouvoir explicatif réel ou une démontrabilité supérieure, pas seulement une beauté formelle.

### Livrables
Pour cette reformulation unique éventuelle :
1. énoncé intuitif ;
2. version semi-formelle ;
3. obstacle absorbé ;
4. ce qui devient plus contrôlable ;
5. risque de dérive ;
6. niveau estimé dans la Ladder of Proof.

---

# REGISTRE MÉTHODOLOGIQUE OBLIGATOIRE

## 1. Type du round
Rappeler explicitement : **P/A**
- **P** pour clarification structurelle et preuve de typage logique ;
- **A** pour autonomie locale conditionnelle et auditée.

## 2. IVS — Information Value Score
Donner une note /10 avec justification courte selon :
- réduction d’ambiguïté ;
- gain de traçabilité ;
- impact sur la cartographie réelle du programme ;
- risque résiduel de confusion ;
- utilité des portes fermées.

Une bonne note IVS peut venir d’une destruction nette d’une ambiguïté si elle évite des semaines de faux progrès.

## 3. Ladder of Proof
Pour chaque objet touché, préciser :
- intuition ;
- observation ;
- observation répétée ;
- calcul exact ;
- semi-formalisation ;
- schéma de preuve ;
- lemme candidat ;
- lemme prouvé ;
- résultat publiable.

## 4. AUTOPSIE DES PISTES FERMÉES (OBLIGATOIRE)
Pour toute piste éliminée, fournir :
- Nom ;
- Type de mort :
  - substitution de compteur,
  - substitution de modèle,
  - insuffisance logique,
  - mauvaise échelle,
  - trop faible,
  - non ciblante,
  - ambiguïté d’énoncé,
  - redondance ;
- Hypothèse implicite fausse ;
- Ce que la mort enseigne ;
- Où cela redirige.

## 5. REGISTRE FAIL-CLOSED
Tu dois terminer par un tableau strict :
- [PROUVÉ]
- [CALCULÉ EXACT]
- [OBSERVÉ NUMÉRIQUEMENT]
- [SEMI-FORMALISÉ]
- [HEURISTIQUE]
- [CONJECTURAL]
- [RÉFUTÉ]
- [AMBIGU AVANT REFORMULATION]

---

# CONTRAINTES MÉTHODOLOGIQUES
Tu dois distinguer explicitement :
- objet étudié ;
- compteur étudié ;
- théorème étudié ;
- usage logique ;
- statut.

Tu dois favoriser les formulations minimales suffisantes :
- ni sur-généraliser trop tôt ;
- ni sauver rhétoriquement une chaîne devenue insuffisante ;
- ni fermer artificiellement une porte locale réellement exploitable.

Tu ne dois pas :
- supposer que le compteur utilisé par habitude est le bon ;
- confondre N_r^true et N_r^ind ;
- promouvoir un résultat comme progrès vers la non-trivialité sans préciser quel compteur il borne ;
- utiliser une reformulation comme camouflage d’un changement de problème ;
- laisser l’autonomie poursuivre au-delà des événements STOP ;
- produire un bilan d’autonomie sans raison explicite d’arrêt.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : le Junction Theorem est retracé avec une traçabilité suffisante pour identifier le compteur requis.
PASS-2 : N_r^true, N_r^ind et tout intermédiaire utile sont proprement définis et distingués.
PASS-3 : au moins une thèse de suffisance est classée honnêtement : [PROUVÉE], [RÉFUTÉE], [PARTIELLE] ou [AMBIGUË].
PASS-4 : la chaîne R62→R68 est requalifiée proprement à la lumière du verdict.
PASS-5 : la PHASE 2, si activée, reste dans son budget d’autonomie et s’arrête correctement.
PASS-6 : un unique survivant rationnel pour R70 est sélectionné.
PASS-7 : au moins une porte fermée est transformée en information structurante pour la suite.

# ÉCHEC UTILE
Même en cas d’échec, R69 est utile si :
- l’ambiguïté sur le compteur requis est réduite drastiquement ;
- une reformulation minimale propre devient possible ;
- une chaîne entière est reclassée honnêtement comme proxy insuffisant ;
- l’autonomie s’arrête correctement avant de partir dans le décor.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats PHASE 1 / AXE A (traçabilité du théorème)
5. Résultats PHASE 1 / AXE B (typologie des compteurs)
6. Résultats PHASE 1 / AXE C (test de suffisance logique)
7. Résultats PHASE 1 / AXE D (requalification de R62→R68)
8. Verdict principal sur le compteur requis
9. Activation ou non de la PHASE 2, avec justification
10. Journal des sous-rounds autonomes S1/S2/S3 le cas échéant
11. Résultats AXE E (reformulation minimale éventuelle)
12. Objets concernés + Ladder of Proof
13. Ce qui est appris
14. Ce qui est fermé utilement
15. Ce qui est enterré
16. Autopsie des pistes fermées
17. Survivant pour R70
18. Risques / limites
19. Verdict final avec score /10
20. Registre FAIL-CLOSED

---

# CONSIGNE FINALE
R69 doit d’abord répondre à la question que R68 rend inévitable : quel compteur est réellement requis par le Junction Theorem ?

Ensuite, et seulement ensuite, une autonomie courte est autorisée pour tirer une unique conséquence rationnelle du verdict.

Le but n’est pas de produire du mouvement.
Le but est de supprimer une ambiguïté fondatrice, de requalifier honnêtement le programme, puis de n’autoriser qu’une exploration locale sous surveillance logique.

Chercher la prochaine fermeture fiable.
Et si l’autonomie s’arrête, elle doit s’arrêter proprement.
Pas d’épopée. Une chaîne logique sous contrôle.