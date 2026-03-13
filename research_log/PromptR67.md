TYPE: P
OBJET CIBLÉ: audit de portée de K-lite + validation ou correction du claim “K-lite universel” + sélection propre du prochain verrou actif (cross-résidu si validation, sinon portée hors R3)
QUESTION CENTRALE: Peut-on transformer la conclusion forte de R66 en énoncé mathématique de portée exactement correcte, en vérifiant ligne par ligne que la chaîne R64–R66 n’utilise réellement aucune hypothèse cachée de régime, et en décidant proprement si K-lite est universellement prouvé ou seulement prouvé sur une portée plus restreinte ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: identifier exactement où une dépendance de régime survit encore, corriger l’énoncé final de K-lite sans glissement de statut, et enterrer proprement toute sur-généralisation avec autopsie complète.

# BRIEF CLAUDE CODE — ROUND 67 (R67)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R66.

### Contexte acquis
- R57–R59 ont transformé la base k=2 en problème de théorie des nombres bien posé via :
  - δ = b−a
  - c_δ = 1 + g·2^δ
  - N_r = #{δ : dlog(r/c_δ) ∈ [0, M−δ]}
- R59 a sélectionné la route prioritaire :
  - **Lemme K-lite via barrier counting**
  avec cible réaliste
  - max N_r ≤ C/p + α(M+1), α<1
- R60–R62 ont réduit le verrou à la sous-étape (c), puis au contrôle utile de τ<1 en R3.
- R63 a réduit le verrou d’équidistribution à :
  - S_h = Σ_{t∈⟨g²⟩} χ_h(1+t)
- R64 a fermé le verrou analytique principal en R3 :
  - décomposition exacte de S_h,
  - réduction à somme de Jacobi standard,
  - borne racine carrée.
- R65 a formalisé la sous-étape (d) et clos **K-lite en R3**, avec constantes explicites et cas fini absorbé.
- R66 a lancé une red team de portée et a conclu que la dépendance au régime R3 était probablement illusoire :
  - la preuve utiliserait en réalité **QR_p = ⟨g²⟩**, non pas une couverture complète de ⟨2⟩,
  - ce qui ferait de **K-lite un résultat universel pour tout p≥5**.
- Cependant, ce saut de portée est très fort. Avant de l’utiliser comme base pour les rounds suivants, il faut un **audit final de portée**.
- Le risque stratégique est maintenant :
  - accepter trop vite “K-lite universel PROUVÉ” sans vérifier la dépendance réelle de chaque maillon de la chaîne ;
  - ou au contraire repartir sur R1/R2 alors que le faux verrou a déjà été éliminé.

## Objectif de R67
R67 doit répondre à cette question centrale :

> La chaîne complète R64–R66 est-elle réellement indépendante du régime, au point de justifier rigoureusement l’énoncé “K-lite prouvé pour tout p≥5”, ou bien subsiste-t-il une dépendance cachée qui oblige à reformuler la portée exacte du théorème ?

R67 doit être un round proof-oriented très centré.
Pas de dispersion.
Pas de campagne computationnelle large.
Le but est d’auditer la portée exacte de K-lite, pas de relancer un nouveau verrou par réflexe.

---

# ARCHITECTURE GÉNÉRALE

## Pièce principale unique
**Audit de portée de K-lite après R66**

## Pièces secondaires autorisées mais subordonnées
- mini-vérification sur quelques cas symboliques si nécessaire pour détecter une hypothèse cachée ;
- cross-résidu uniquement comme survivant potentiel si la portée universelle est validée ;
- aucune nouvelle attaque frontale sur S_h, D_∞, ou hit-hit sauf si l’audit révèle une dépendance non vue.

Le round doit dire explicitement lequel des deux énoncés est correct à la fin :
1. **K-lite universel [PROUVÉ] pour tout p≥5**
2. **K-lite [PROUVÉ] sur une portée plus restreinte**, à reformuler précisément.

---

# AXE A — INVESTIGATEUR / AUDIT LIGNE PAR LIGNE DE LA CHAÎNE
## Nom de travail
Où la preuve dépend-elle encore du régime ?

## Mission
Relire et vérifier, maillon par maillon, la chaîne R64–R66 pour déterminer si une hypothèse de régime (R3, couverture complète, arc total, etc.) subsiste réellement ou non.

### Questions obligatoires
1. Dans la réduction via Erdős–Turán, y a-t-il une dépendance implicite à un régime de couverture ?
2. Dans le passage S_h → D_∞, les constantes ou objets utilisés dépendent-ils de R3, ou seulement de QR_p / p ?
3. Dans le passage D_∞ → τ<1, existe-t-il une hypothèse cachée sur la longueur d’arc, la couverture, ou la densité des hits ?
4. Dans l’intégration finale τ<1 → α<1, une hypothèse de régime survit-elle ?
5. Le cas fini utilisé en R65 repose-t-il sur un tri par régime, ou seulement sur une liste de petits p ?
6. Quelle est la portée exacte, mathématiquement correcte, du théorème K-lite obtenu ?

### Livrables
- audit maillon par maillon de la chaîne ;
- tableau “dépendance de régime : oui/non” pour chaque maillon ;
- formulation exacte du théorème valide ;
- identification du premier maillon qui casserait si la portée universelle était fausse.

---

# AXE B — INVESTIGATEUR / CORRECTION DE PORTÉE SI NÉCESSAIRE
## Nom de travail
Quel théorème a-t-on vraiment prouvé ?

## Mission
Si une dépendance cachée subsiste, reformuler proprement K-lite sans glissement de statut ni ambiguïté sur les quantificateurs.

### Questions obligatoires
1. La phrase “pour tout p≥5” est-elle exactement correcte telle quelle ?
2. Si non, quelle version correcte faut-il écrire ?
   - pour tout p≥5 en R3,
   - pour tout p≥5 satisfaisant telle condition,
   - autre
3. Quelle est la différence entre :
   - portée prouvée,
   - portée observée,
   - portée conjecturée ?
4. Y a-t-il un faux verrou hérité (R1/R2) qui peut être enterré proprement ?
5. Quel est le texte minimal de correction à apporter aux bilans / RESEARCH_MAP si nécessaire ?

### Livrables
- verdict net : universel ou non ;
- reformulation exacte si correction nécessaire ;
- distinction propre des statuts ;
- texte de correction minimal si besoin.

---

# AXE C — INNOVATEUR / SUIVANT OPTIMAL APRÈS L’AUDIT
## Nom de travail
Quel est le vrai verrou après R66 ?

## Mission
À partir du verdict d’audit, proposer au plus 2 directions sérieuses pour la suite.

### Candidat 1
**Si K-lite universel est validé : cross-résidu**
Le prochain verrou actif devient le bootstrap inter-résidus / cross-résidu, car la base k=2 est alors proprement fermée au niveau utile.

### Candidat 2
**Si la portée universelle échoue : correction de K-lite hors R3**
Le vrai verrou reste la reformulation correcte hors R3 / couverture partielle.

### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait immédiatement ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle ;
6. niveau estimé dans la Ladder of Proof.

## Règle obligatoire
À la fin :
- garder un seul survivant pour R68 ;
- éliminer l’autre explicitement ;
- justifier le choix par démontrabilité réelle, pas par enthousiasme.

---

# AXE D — CONTRÔLE SECONDAIRE / CHAÎNE GLOBALE
## Nom de travail
Ne pas casser la logique du projet

## Mission
Rappeler brièvement, après audit, quelle est la nouvelle chaîne active du projet.

### Questions obligatoires
1. Si K-lite universel est validé, quelle est la nouvelle chaîne active ?
2. Si K-lite universel est refusé, quel maillon exact redevient actif ?
3. Quel rappel concis faut-il conserver pour éviter toute dérive future de statut ?

### Livrables
- chaîne active mise à jour ;
- aucun nouveau verrou fantôme ;
- aucune dérive hors du périmètre d’audit.

---

# CONTRÔLE SECONDAIRE OPTIONNEL
Un seul micro-test ciblé est autorisé si et seulement s’il aide à trancher une dépendance de régime cachée dans un maillon précis.
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
- sur-vendre “K-lite universel” sans audit maillon par maillon ;
- réouvrir S_h, D_∞, ou hit-hit comme nouvelles cibles tant que l’audit de portée n’a pas échoué ;
- lancer une campagne computationnelle large ;
- glisser entre “pour tout p≥5” et “pour tout p en R3” sans le dire explicitement.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : un audit maillon par maillon de la portée est produit.
PASS-2 : la dépendance ou non-dépendance au régime est tranchée proprement.
PASS-3 : le théorème K-lite exact est formulé sans ambiguïté.
PASS-4 : au moins une illusion de portée est enterrée avec autopsie complète.
PASS-5 : un survivant unique pour R68 est sélectionné.

# ÉCHEC UTILE
Même en cas d’échec, R67 est utile si :
- la dépendance cachée de régime est localisée ;
- une formulation trop forte est corrigée proprement ;
- la nouvelle chaîne active est plus honnête qu’avant.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats AXE A (audit de chaîne)
5. Résultats AXE B (portée exacte de K-lite)
6. Résultats AXE C (survivant post-audit)
7. Résultats AXE D (chaîne globale)
8. Contrôle secondaire éventuel
9. CEC inchangé
10. Objets concernés + Ladder of Proof
11. Ce qui est appris
12. Ce qui est enterré
13. Autopsie des pistes fermées
14. Survivant pour R68
15. Risques / limites
16. Verdict final avec score /10

---

# CONSIGNE FINALE
R67 doit auditer la portée exacte du résultat issu de R66.
Le but n’est pas de produire un nouveau verrou artificiel.
Le but est de décider proprement si K-lite est universellement fermé ou seulement fermé sur une portée restreinte, puis de sélectionner le vrai verrou suivant.
Chercher la vérité de portée, pas l’optimisme narratif.
