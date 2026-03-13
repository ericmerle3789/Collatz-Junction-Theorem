TYPE: P
OBJET CIBLÉ: sous-étape (c) du bridge K-lite + transition hit-hit + régime prioritaire R3, avec base → cross gardé comme chaîne stratégique
QUESTION CENTRALE: Peut-on faire monter le survivant de R60 d’un cran vers un premier lemme semi-prouvé utile, en attaquant directement la sous-étape (c) — le contrôle uniforme du taux de transition hit-hit — en priorité dans le régime R3, sans relancer de métriques ou d’auxiliaires déjà calibrés ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: identifier précisément quelle forme du contrôle hit-hit est réellement prouvable (régime, constante, formulation), et enterrer proprement toute tentative trop ambitieuse avec autopsie complète.

# BRIEF CLAUDE CODE — ROUND 61 (R61)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R60.

### Contexte acquis
- R57–R59 ont transformé la base k=2 en problème de théorie des nombres bien posé via :
  - δ = b−a
  - c_δ = 1 + g·2^δ
  - N_r = #{δ : dlog(r/c_δ) ∈ [0, M−δ]}
- R59 a sélectionné la route prioritaire :
  - **Lemme K-lite via barrier counting**
  avec cible réaliste
  - max N_r ≤ C/p + α(M+1),  α<1
- R60 a articulé le schéma de preuve en 4 sous-étapes et réduit le verrou à une unique pièce restante :
  - **(a)** reformulation δ [PROUVÉ]
  - **(b)** injectivité / |S_δ|≤1 [PROUVÉ]
  - **(c)** contrôle du taux de transition hit-hit [VERROU]
  - **(d)** intégration ⇒ α<1 [dépend de (c)]
- R60 a aussi stabilisé :
  - la **discrepancy pondérée** comme bonne métrique ;
  - le **nesting** comme auxiliaire utile mais insuffisant seul ;
  - le **cross** comme conséquence secondaire bien cadrée.
- Le risque stratégique est maintenant :
  - rouvrir de faux débats sur la métrique ;
  - diluer l’effort sur trop d’auxiliaires ;
  - ou viser un contrôle hit-hit trop fort, trop tôt, sans sous-régime ni constante réalistes.

## Objectif de R61
R61 doit répondre à cette question centrale :

> Peut-on obtenir une première version crédible et utilisable du contrôle hit-hit de la sous-étape (c), au moins dans un sous-régime naturel prioritaire (en particulier R3 si c’est le plus favorable), suffisamment forte pour faire progresser le Bridge-lite pointwise vers un vrai Lemme K-lite ?

R61 doit être un round proof-oriented très centré.
Pas de dispersion.
Pas de campagne computationnelle large.
Le but est d’attaquer le verrou unique identifié par R60.

---

# ARCHITECTURE GÉNÉRALE

## Pièce principale unique
**Sous-étape (c) : contrôle du taux de transition hit-hit**

## Pièces auxiliaires autorisées mais subordonnées
- **nesting** comme renfort structurel seulement ;
- **R3** comme sous-régime prioritaire si cela simplifie réellement la preuve ;
- **cross** conservé comme conséquence stratégique, sans nouvelle attaque frontale.

Le round doit dire explicitement si, après R61, la sous-étape (c) est assez mûre pour faire de K-lite un vrai lemme candidat fort.

---

# AXE A — INVESTIGATEUR / FORMULATION DU CONTRÔLE HIT-HIT
## Nom de travail
Que faut-il exactement borner ?

## Mission
Formuler de manière mathématiquement précise le contrôle hit-hit recherché, en choisissant la meilleure version démontrable à court terme.

### Questions obligatoires
1. Quelle est la formulation canonique du taux de transition hit-hit ?
   - probabilité conditionnelle de hit→hit,
   - densité locale de chaînes de hits,
   - borne sur le nombre de transitions successives,
   - autre formulation équivalente plus exploitable
2. Quel est le plus petit énoncé utile déjà assez fort pour faire avancer la sous-étape (d) ?
3. Quel sous-régime naturel est le meilleur candidat pour commencer ?
   - R3 prioritaire,
   - autre sous-régime si mieux justifié
4. Quel type de constante ou de marge vise-t-on réellement ?
   - strictement < 1,
   - < 1 − ε explicite,
   - autre version utile
5. Quelle partie du verrou provient de la dynamique des hits, et quelle partie provient encore de la géométrie des fenêtres ?

### Livrables
- formulation canonique du contrôle hit-hit ;
- meilleur sous-régime prioritaire ;
- cible réaliste sur la constante ;
- un premier énoncé intermédiaire candidat.

---

# AXE B — INVESTIGATEUR / ROUTES DE PREUVE POUR (c)
## Nom de travail
Quelle route peut vraiment casser le verrou ?

## Mission
Comparer les mécanismes possibles pour contrôler hit-hit, sans rouvrir les outils déjà enterrés ni confondre nesting avec preuve complète.

### Questions obligatoires
1. Quelle route paraît la plus crédible pour contrôler hit-hit ?
   - dynamique locale des fenêtres,
   - argument de rareté des persistance longues,
   - structure affine de c_δ,
   - mélange de ces ingrédients,
   - autre
2. En quoi le nesting aide-t-il exactement, et où s’arrête son pouvoir ?
3. Quelles routes sont explicitement mortes ou trop faibles ici ?
4. Peut-on déjà produire un sous-lemme de type :
   - “les longues chaînes de hits sont rares”,
   - “deux hits consécutifs coûtent structurellement quelque chose”,
   - autre variante utile
5. Quelle route semble la plus démontrable dans le temps court d’un round ?

### Livrables
- comparaison honnête des routes ;
- sélection de la route prioritaire ;
- liste explicite des outils morts à ne pas ressusciter ;
- un premier sous-lemme candidat si possible.

---

# AXE C — INNOVATEUR / PREMIER NOYAU PROUVABLE DE (c)
## Nom de travail
Hit-hit-lite prouvable

## Mission
Proposer au plus 2 formulations candidates d’un premier noyau prouvable utile pour la sous-étape (c).

### Candidat 1
**Hit-hit-lite pointwise**
Dans un sous-régime naturel favorable, le taux de transition hit-hit est uniformément borné par une constante strictement <1, suffisante pour faire avancer le Bridge-lite pointwise.

### Candidat 2
**Hit-hit-lite par chaînes courtes**
Il n’est pas nécessaire de contrôler toutes les transitions ; il suffit de montrer que les chaînes de hits longues sont assez rares pour imposer α<1 après intégration.

### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait immédiatement ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle ;
6. niveau estimé dans la Ladder of Proof.

## Règle obligatoire
À la fin :
- garder un seul survivant pour R62 ;
- éliminer l’autre explicitement ;
- justifier le choix par démontrabilité réelle, pas par élégance.

---

# AXE D — CONTRÔLE SECONDAIRE / CHAÎNE GLOBALE
## Nom de travail
Ne pas casser la stratégie d’ensemble

## Mission
Sans faire du cross la cible principale, rappeler brièvement comment un progrès sur (c) se réinjecte dans :
- (d) ⇒ α<1,
- K-lite,
- base,
- puis cross.

### Questions obligatoires
1. Quel est le lien minimal “(c) → (d) → K-lite” à préserver ?
2. Le sous-régime choisi pour (c) change-t-il la stratégie globale ou seulement la première marche ?
3. Quel rappel concis faut-il conserver pour éviter toute dérive future ?

### Livrables
- rappel propre de la chaîne de conséquences ;
- aucune nouvelle attaque frontale du cross ;
- aucune dérive hors du verrou principal.

---

# CONTRÔLE SECONDAIRE OPTIONNEL
Un seul micro-test ciblé est autorisé si et seulement s’il aide à départager :
- R3 vs autre sous-régime,
- ou hit-hit pointwise vs chaînes courtes.
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
- ressusciter les faux débats sur la métrique ;
- faire du cross la cible principale du round ;
- lancer une campagne computationnelle large ;
- présenter la sous-étape (c) comme réglée tant que la borne hit-hit utile n’est pas réellement formulée.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : une formulation précise du contrôle hit-hit est isolée.
PASS-2 : un sous-régime prioritaire est sélectionné proprement.
PASS-3 : un premier noyau de sous-lemme utile pour (c) est formulé.
PASS-4 : au moins une tentative trop optimiste est éliminée avec autopsie complète.
PASS-5 : un survivant unique pour R62 est sélectionné.

# ÉCHEC UTILE
Même en cas d’échec, R61 est utile si :
- le vrai verrou de la sous-étape (c) est clarifié ;
- une fausse bonne formulation du hit-hit est éliminée ;
- une version plus pauvre mais plus prouvable du contrôle est isolée.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats AXE A (contrôle hit-hit)
5. Résultats AXE B (routes de preuve)
6. Résultats AXE C (hit-hit-lite)
7. Résultats AXE D (chaîne globale)
8. Contrôle secondaire éventuel
9. CEC inchangé
10. Objets concernés + Ladder of Proof
11. Ce qui est appris
12. Ce qui est enterré
13. Autopsie des pistes fermées
14. Survivant pour R62
15. Risques / limites
16. Verdict final avec score /10

---

# CONSIGNE FINALE
R61 doit attaquer le verrou unique identifié par R60.
Le but n’est pas de refaire une carte du bridge.
Le but est d’obtenir le premier contrôle utile sur hit-hit, suffisamment fort pour faire progresser (d) puis K-lite.
Chercher la prochaine sous-pièce prouvable, pas la théorie finale complète.
