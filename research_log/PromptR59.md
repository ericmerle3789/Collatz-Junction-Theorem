

TYPE: P
OBJET CIBLÉ: borne additive pointwise sur max N_r + fenêtres variables / K_linear + cross gardé comme conséquence secondaire
QUESTION CENTRALE: Peut-on faire monter la route prioritaire issue de R58 d’un cran vers un premier lemme semi-prouvé utile, en obtenant une borne additive pointwise crédible sur max N_r via une méthode de fenêtres variables / K_linear pour les dlogs de la suite affine c_δ = 1 + g·2^δ ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: identifier la meilleure forme prouvable du lemme “fenêtres variables / K_linear”, et enterrer proprement toute formulation trop optimiste ou mal calibrée avec autopsie complète.

# BRIEF CLAUDE CODE — ROUND 59 (R59)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R58.

### Contexte acquis
- R56 a confirmé l’architecture post-R55 :
  - **base k=2** comme pièce la plus proche d’un vrai lemme ;
  - **cross** comme pièce plus difficile, à traiter ensuite par route bilinéaire.
- R57 a reformulé le problème de base via
  - δ = b−a
  - c_δ = 1 + g·2^δ
  - et
    N_r = #{δ : dlog(r/c_δ) ∈ [0, M−δ]}
- R58 a transformé ce gap en problème de théorie des nombres bien posé :
  - compter des dlogs d’une suite affine dans des **fenêtres rétrécissantes** ;
  - sélectionner la route prioritaire **fenêtres variables / K_linear** ;
  - rejeter les modèles trop naïfs : second moment seul, pseudo-aléa naïf, Weil directe, Weyl qualitative seule.
- L’objet intermédiaire stabilisé est :
  - K_linear = (max N_r − C/p)/(M+1)
- La cible privilégiée est :
  - une borne additive du type
    max N_r ≤ C/p + K·√(M+1)
    ou une variante légèrement plus faible mais réellement prouvable.
- R58 a aussi montré un gain stratégique très important :
  - une borne additive pointwise sur la base aide aussi à contrôler le cross.
- Le risque stratégique est maintenant :
  - choisir une borne trop ambitieuse sans preuve ;
  - ou rester trop descriptif sur K_linear sans faire émerger un vrai lemme.

## Objectif de R59
R59 doit répondre à cette question centrale :

> Peut-on formuler et défendre un premier lemme “fenêtres variables / K_linear” suffisamment fort pour améliorer la base k=2 de façon semi-rigoureuse, même si la borne finale optimale max N_r ≤ C/p + K·√(M+1) reste encore hors d’atteinte ?

R59 doit être un round proof-oriented très centré.
Pas de dispersion.
Pas de campagne computationnelle large.
Le but est de transformer la bonne formulation théorique de R58 en premier noyau de preuve utilisable.

---

# ARCHITECTURE GÉNÉRALE

## Pièce principale unique
**Fenêtres variables / K_linear pour la base k=2**

## Pièce secondaire maintenue mais non prioritaire
**Cross gardé comme conséquence stratégique, sans nouvelle attaque frontale**

Le round doit dire explicitement si, après R59, le verrou principal reste la base k=2, ou si elle devient assez mûre pour laisser la priorité au cross.

---

# AXE A — INVESTIGATEUR / LEMME FENÊTRES VARIABLES
## Nom de travail
Que faut-il prouver exactement ?

## Mission
Transformer la formulation “dlogs de la suite affine dans des fenêtres rétrécissantes” en énoncé mathématique précis, avec la meilleure cible de borne réaliste à court terme.

### Questions obligatoires
1. Quelle est la formulation canonique la plus utile du problème des fenêtres variables ?
   - borne pointwise sur max N_r,
   - borne uniforme sur K_linear,
   - borne moyenne sur les fenêtres,
   - autre
2. Quelle cible paraît réellement prouvable à court terme ?
   - max N_r ≤ C/p + K·√(M+1)
   - max N_r ≤ C/p + K·(M+1)^θ avec θ<1
   - max N_r ≤ C/p + K·log(M+1)
   - autre variante utile
3. Quelle partie du problème vient des fenêtres variables elles-mêmes, et quelle partie vient de la suite affine c_δ ?
4. Quel est le meilleur sous-régime naturel à viser en premier ?
   - cas générique uniquement,
   - séparation stricte du cas dégénéré,
   - M petit devant ord_p(2),
   - autre
5. Quel est le plus petit énoncé semi-formel utile déjà assez fort pour améliorer la base ?

### Livrables
- formulation canonique du lemme “fenêtres variables” ;
- meilleure cible de borne réaliste ;
- hiérarchie honnête des sous-régimes ;
- un premier noyau de lemme si possible.

---

# AXE B — INVESTIGATEUR / ROUTES DE PREUVE POUR K_linear
## Nom de travail
Quelle route peut vraiment marcher ?

## Mission
Comparer les approches disponibles pour contrôler K_linear sans retomber dans les outils déjà enterrés.

### Questions obligatoires
1. Quelle route paraît la plus crédible pour le premier lemme ?
   - argument combinatoire sur fenêtres emboîtées,
   - large sieve / variante discrète,
   - incidence additive,
   - dlog + progression affine,
   - autre
2. Quel outil semble explicitement hors-jeu à ce stade, même s’il paraît élégant ?
3. Le bon premier lemme doit-il être pointwise, moyen, ou hybride ?
4. Peut-on déjà isoler une structure monotone/nichée des fenêtres qui remplace une pseudo-aléa absente ?
5. Quelle route semble la plus démontrable dans le temps court d’un round ?

### Livrables
- comparaison honnête des routes ;
- sélection de la route prioritaire ;
- liste explicite des outils morts à ne pas ressusciter ;
- un premier sous-lemme candidat si possible.

---

# AXE C — INNOVATEUR / PREMIER NOYAU PROUVABLE DE LA BASE APRÈS R58
## Nom de travail
K_linear-lite prouvable

## Mission
Proposer au plus 2 formulations candidates d’un premier noyau prouvable utile pour la base k=2.

### Candidat 1
**K_linear-lite pointwise**
Une borne additive pointwise affaiblie mais explicite sur max N_r suffit déjà à transformer la base en quasi-lemme utile pour la machine globale.

### Candidat 2
**K_linear-lite hybride**
Un contrôle hybride (par exemple moyen + pointwise partiel, ou par sous-régimes) suffit déjà à produire une version utile de la base-lite.

### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait immédiatement ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle ;
6. niveau estimé dans la Ladder of Proof.

## Règle obligatoire
À la fin :
- garder un seul survivant pour R60 ;
- éliminer l’autre explicitement ;
- justifier le choix par démontrabilité réelle, pas par élégance.

---

# AXE D — CONTRÔLE SECONDAIRE / CROSS CONSÉQUENCE
## Nom de travail
Garder le cross au chaud, pas au centre

## Mission
Sans faire du cross la cible principale, rappeler explicitement comment une amélioration de la base pointwise réinjecte du contrôle sur le cross.

### Questions obligatoires
1. Quel est le lien minimal base → cross qu’il faut conserver ?
2. La stratégie cross reste-t-elle inchangée après le nouveau lemme visé ?
3. Quel rappel concis évite de repartir de zéro au round suivant ?

### Livrables
- rappel court et propre du lien base → cross ;
- aucune nouvelle attaque frontale ;
- aucune dérive analytique inutile.

---

# CONTRÔLE SECONDAIRE OPTIONNEL
Un seul micro-test ciblé est autorisé si et seulement s’il aide à départager :
- borne pointwise vs borne hybride,
- ou deux formulations concurrentes du lemme fenêtres variables.
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
- relancer une modélisation “presque aléatoire” sans justification ;
- faire du cross la cible principale du round ;
- lancer une campagne computationnelle large ;
- présenter la base k=2 comme prouvée tant que le lemme fenêtres variables n’est pas suffisamment verrouillé.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : une formulation mathématique précise du lemme fenêtres variables est isolée.
PASS-2 : une route de preuve prioritaire pour K_linear est sélectionnée.
PASS-3 : un meilleur noyau de base-lite est formulé.
PASS-4 : au moins une formulation trop optimiste ou naïve est éliminée avec autopsie complète.
PASS-5 : un survivant unique pour R60 est sélectionné.

# ÉCHEC UTILE
Même en cas d’échec, R59 est utile si :
- le vrai verrou du lemme fenêtres variables est clarifié ;
- une fausse bonne route sur K_linear est éliminée ;
- une version plus pauvre mais plus prouvable de la base-lite est isolée.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats AXE A (lemme fenêtres variables)
5. Résultats AXE B (routes de preuve)
6. Résultats AXE C (base-lite)
7. Résultats AXE D (cross conséquence)
8. Contrôle secondaire éventuel
9. CEC inchangé
10. Objets concernés + Ladder of Proof
11. Ce qui est appris
12. Ce qui est enterré
13. Autopsie des pistes fermées
14. Survivant pour R60
15. Risques / limites
16. Verdict final avec score /10

---

# CONSIGNE FINALE
R59 doit faire monter la bonne formulation issue de R58 vers un premier lemme de base réellement utilisable.
Le but n’est pas de mieux raconter K_linear.
Le but est d’identifier la première version prouvable du lemme fenêtres variables, tout en gardant le cross comme conséquence secondaire bien cadrée.
Chercher la prochaine pièce prouvable, pas la théorie finale complète.