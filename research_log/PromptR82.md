

TYPE: X/I/P
OBJET CIBLÉ: construire le round R82 comme un brief d’innovation contrôlée à partir de tout ce qui manque encore concrètement, en combinant investigation profonde, créativité disciplinée et sélection stricte d’un candidat de percée, sans computationnel, sans k-par-k, sans rebranding, sans redondance et sans régression vers les voies déjà enterrées
QUESTION CENTRALE: qu’est-ce qui manque concrètement pour franchir le verrou restant — la conversion d’une structure multiplicative favorable en exclusion additive effective — et quel nouvel objet, quelle nouvelle approche, quels styles d’agents et quel protocole d’exploration verrouillé faut-il mobiliser pour faire émerger un candidat réellement plus mordant ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: soit faire émerger un candidat de percée réellement nouveau, muni d’un premier lemme candidat, d’une chaîne logique explicite et d’un test de réfutation ; soit démontrer qu’aucune approche proposée ne dépasse les limites déjà cartographiées et suspendre proprement l’innovation au lieu d’imiter la nouveauté.
PRINCIPE D’ÉQUILIBRE: autoriser fortement la créativité, mais uniquement dans une arène méthodologique fermée ; chaque idée doit être dérivée d’un manque concret, testée contre l’historique des échecs, soumise à des investigateurs spécialisés et à un audit fail-closed, puis éliminée ou retenue dans un tournoi strict de candidats. Liberté tactique locale, verrouillage stratégique global.

# BRIEF CLAUDE CODE — ROUND 82 (R82)

## Mission
Tu poursuis le projet Collatz après R81 et après toute la séquence R67→R81.

R82 est un round de **créativité disciplinée à haut niveau de sécurité**.

Il part d’un constat simple :
- nous avons beaucoup fermé ;
- nous avons beaucoup clarifié ;
- nous avons enfin un diagnostic assez net du verrou restant ;
- mais nous n’avons pas encore de levier véritablement mordant.

Le verrou actif actuel peut être résumé ainsi :

> **nous ne savons pas encore convertir une structure multiplicative favorable en exclusion additive effective de -1.**

R82 doit donc commencer par répondre à trois questions concrètes :
1. **Que manque-t-il exactement ?**
2. **Quelle famille d’approches pourrait réellement combler ce manque ?**
3. **Quels styles d’agents sont nécessaires pour explorer cela sans retomber dans les voies déjà enterrées ?**

Ensuite seulement, R82 doit autoriser une innovation contrôlée.

Le but n’est pas de forcer une percée verbale.
Le but est de fabriquer, si possible, un **candidat de percée** réellement nouveau, testable, dérivé d’un manque concret, et immédiatement soumis à élimination stricte.

---

## Contexte acquis avant R82
- Les rounds récents ont successivement fermé ou borné :
  - la substitution de modèle,
  - la confusion des compteurs,
  - l’illusion que k=2 pouvait porter la cible,
  - la voie spectrale,
  - les bornes analytiques standards dans le régime O(log p),
  - plusieurs mécanismes SAMC,
  - le multiplicatif pur comme faux sauveur,
  - puis plusieurs reformulations internes au noyau irréductible de F_p.
- R79 a proposé l’auto-référence arithmétique comme meilleure cause source candidate accessible.
- R80 a mis au jour un noyau irréductible dans F_p : beaucoup de reformulations internes sont trop proches pour produire une vraie prise nouvelle.
- R81 a réussi à produire un premier candidat externe structuré, mais fragile, et a clarifié le verrou restant :
  **la conversion d’une structure multiplicative favorable en exclusion additive effective.**
- Donc :
  - l’espace d’innovation n’est pas fermé ;
  - mais il est extrêmement contraint ;
  - toute nouvelle approche doit être testée contre ce diagnostic, contre l’historique, et contre le noyau irréductible déjà cartographié.

---

# OBJECTIF DE R82
R82 doit répondre à cette question centrale :

> Quel candidat de percée peut être construit à partir du manque concret actuellement identifié, en utilisant une créativité verrouillée, des agents spécialisés et un tournoi strict de sélection, sans retomber dans le computationnel, le k-par-k, le rebranding ou les impasses déjà fermées ?

Les sorties acceptables du round sont :
1. **Un candidat de percée crédible survit, avec objet précis, lemme candidat, chaîne logique et test de réfutation** ;
2. **Deux candidats sérieux sont comparés, mais un seul survit après tournoi strict** ;
3. **Aucun candidat ne dépasse les limites déjà connues : innovation suspendue proprement** ;
4. **Le manque concret a été mieux formulé, mais un verrou préparatoire manque encore avant tout vrai candidat.**

Important :
- aucune sortie n’est recevable si le candidat n’est pas dérivé d’un manque concret explicite ;
- aucune sortie n’est recevable si le candidat dépend de petites valeurs de k, d’expériences numériques, ou d’accumulations de cas ;
- aucune sortie n’est recevable si elle ressuscite une voie enterrée sous un langage plus neuf ;
- aucune sortie n’est recevable sans critère clair de victoire, de défaite et de réfutation.

---

# CE QU’IL NOUS MANQUE CONCRÈTEMENT (À EXAMINER D’ABORD)
R82 doit traiter explicitement les manques suivants comme hypothèses de travail à tester, et non comme slogans.

## Manques concrets candidats
1. **Un invariant de conversion** : un objet qui relie réellement confinement multiplicatif et exclusion additive, au lieu de seulement constater leur disjonction.
2. **Une notion de rigidité ciblée** : plus forte que la simple sparsité, mais plus légère qu’une exclusion complète du sumset.
3. **Une structure d’obstruction minimale** : qui dise pourquoi -1 serait impossible, non pas “en général”, mais à cause d’un mécanisme exact de non-réalisation.
4. **Une interface compatible avec l’auto-référence arithmétique** : pas seulement un objet externe au noyau F_p, mais un objet qui incorpore vraiment la dépendance profonde en 2^S et 3^k.
5. **Un langage minimal de transfert** : permettant de passer d’une information hors F_p à une conséquence pertinente modulo p sans retomber dans le noyau irréductible.

R82 doit tester lesquels de ces “manques” sont réels, lesquels sont trop vagues, et lequel est le plus fertile.

---

# ARCHITECTURE GÉNÉRALE

## PHASE 1 — DIAGNOSTIC DU MANQUE CONCRET
Objectif : transformer le verrou restant en un manque précis, étroit, opératoire.

## PHASE 2 — GÉNÉRATION CONTRÔLÉE D’APPROCHES ET D’OBJETS CANDIDATS
Objectif : proposer peu d’approches, peu d’objets, mais bien motivés et réellement nouveaux.

## PHASE 3 — TOURNOI FERMÉ DE CANDIDATS
Objectif : faire comparaître les candidats sous audit croisé, élimination stricte et critères explicites.

## PHASE 4 — DÉCISION STRATÉGIQUE
Objectif : ne garder qu’un seul survivant pour R83, ou suspendre proprement l’innovation.

## Ce qui est interdit comme cible principale
- computationnel ;
- k-par-k ;
- petites valeurs comme colonne vertébrale ;
- preuves ou quasi-preuves par accumulation d’exemples ;
- toute reformulation purement interne à F_p ;
- toute voie déjà enterrée : spectral, bilinéaire courte standard, faux multiplicatif pur, cardinalité seule, anti-concentration circulaire, récurrence locale, rebranding SAMC, etc. ;
- toute innovation sans objet précis, lemme candidat, test de réfutation, et preuve de non-redondance.

---

# PHASE 1 — DIAGNOSTIC DU MANQUE CONCRET

## AXE A — INVESTIGATEUR PARALLÈLE 1 / QUEL EST LE MANQUE LE PLUS ÉTROIT ?
### Nom de travail
De quoi manque-t-on exactement, et pas en général ?

### Mission
Prendre le verrou actif et le comprimer au maximum : ne pas parler d’un “grand manque”, mais d’un manque aussi étroit que possible, susceptible d’engendrer un objet minimal.

### Questions obligatoires
1. Quel manque exact empêcherait de convertir une structure multiplicative favorable en exclusion additive effective ?
2. Ce manque porte-t-il sur un invariant, une compatibilité, une rigidité, une obstruction, une géométrie, une énergie, un transfert, ou autre chose ?
3. Quel “manque” apparent est trop vague pour être utile ?
4. Quel manque est trop haut et ne fait que reformuler le verrou ?
5. Quelle formulation minimale du manque peut servir de base à R82 ?

### Livrables
- manque concret minimal ;
- faux manques enterrés ;
- formulation opérationnelle autorisée.

---

## AXE B — INVESTIGATEUR PARALLÈLE 2 / QUELLES FAMILLES D’APPROCHES SONT ENCORE OUVERTES ?
### Nom de travail
Quelles portes ne sont pas déjà murées ?

### Mission
Lister les styles d’approches encore légitimes, en excluant explicitement tout ce qui est déjà clos, hors-régime, ou redondant.

### Familles d’approches autorisées à tester
- approche par **invariant de conversion** ;
- approche par **obstruction structurelle minimale** ;
- approche par **compatibilité quantitative hors F_p** ;
- approche par **rigidité orientée** ;
- approche par **transfert minimal source-compatible** ;
- approche mixte si elle est plus précise que le slogan somme-produit.

### Questions obligatoires
1. Quelle famille d’approches est encore réellement ouverte ?
2. Laquelle est la plus proche du manque concret identifié ?
3. Laquelle risque le plus de retomber dans un ancien piège ?
4. Quelle famille semble nouvelle, mais ne l’est pas ?
5. Faut-il restreindre immédiatement le champ à 2 familles maximum ?

### Livrables
- 2 familles d’approches maximum autorisées pour la phase suivante ;
- justification ;
- voies explicitement fermées pour non-régression.

---

## AXE C — INVESTIGATEUR HISTORIQUE / CONTRÔLE ANTI-REDONDANCE GLOBAL
### Nom de travail
Sommes-nous en train de rebrasser le passé ?

### Mission
Comparer le manque concret et les familles d’approches retenues à toute la carte mentale R67→R81.

### Questions obligatoires
1. Quelle partie de l’historique risquerait d’être réemballée si l’on n’est pas strict ?
2. Quelle différence minimale une nouvelle approche doit-elle montrer pour être recevable ?
3. Quel piège de redondance est le plus dangereux à ce stade ?
4. Quel “nouveau” langage a déjà été vu sous une autre forme ?
5. Quel est le test rapide de non-redondance ?

### Livrables
- tableau anti-redondance ;
- critère rapide de non-redondance ;
- drapeaux rouges prioritaires.

---

# PHASE 2 — GÉNÉRATION CONTRÔLÉE D’APPROCHES ET D’OBJETS CANDIDATS

## AXE D — INNOVATEUR DISCIPLINÉ / PROPOSITION D’AU PLUS 3 CANDIDATS ENTRANT EN TOURNOI
### Nom de travail
Inventer peu, mais inventer ce qui peut vivre

### Mission
Proposer au maximum **3 candidats**. Pas davantage.
Chaque candidat doit être formulé comme un ensemble cohérent :
- approche,
- objet,
- lemme candidat,
- test de réfutation,
- et raison d’entrer en tournoi.

### Règle absolue
Un candidat n’est recevable que si la chaîne suivante est explicite :

manque concret → famille d’approche autorisée → objet candidat → lemme candidat → critère de réfutation → critère de victoire.

### Questions obligatoires pour chaque candidat
1. Quelle famille d’approche incarne-t-il ?
2. Quel objet précis propose-t-il ?
3. Quel manque exact vise-t-il à combler ?
4. Quel premier lemme candidat engendre-t-il ?
5. Quel test rapide montrerait qu’il est vide, redondant, ou trop faible ?
6. Pourquoi mérite-t-il d’entrer en tournoi contre les autres ?

### Livrables
Pour chaque candidat :
- nom de travail ;
- famille d’approche ;
- définition ou schéma semi-formel de l’objet ;
- premier lemme candidat ;
- premier critère de réfutation ;
- premier critère de victoire.

---

## AXE E — STYLES D’AGENTS À MOBILISER
### Nom de travail
Qui faut-il faire travailler, et sur quoi ?

### Mission
Déterminer explicitement quels styles d’agents sont nécessaires pour explorer les candidats sans bruit ni dérive.

### Styles d’agents autorisés
1. **Investigateur causal** : remonte les chaînes de blocage, vérifie que le candidat part d’un manque réel.
2. **Investigateur historique** : compare au passé, détecte le rebranding et la redondance.
3. **Innovateur discipliné** : propose les objets, mais sous contrainte stricte.
4. **Auditeur fail-closed** : force les statuts, détruit les objets flous ou invérifiables.
5. **Arbitre de tournoi** : impose les critères de victoire / élimination.
6. **Synthétiseur structurel** : relie l’objet au verrou réel sans rhétorique.

### Questions obligatoires
1. Quels agents sont indispensables ?
2. Quel agent risque le plus de dériver et doit être le plus verrouillé ?
3. Quels agents doivent travailler en parallèle ?
4. Quels agents doivent obligatoirement se contredire / s’auditer ?
5. Quel ordre opératoire minimise les hallucinations et la redondance ?

### Livrables
- protocole d’agenterie pour R82 ;
- ordre d’intervention ;
- points d’audit croisé obligatoires.

---

# PHASE 3 — TOURNOI FERMÉ DE CANDIDATS

## AXE F — AUDIT CROISÉ ET TEST DE RÉALITÉ
### Nom de travail
Quels candidats méritent de rester vivants ?

### Mission
Faire comparaître les candidats dans un tournoi fermé sous critères explicites.

### Critères de tournoi obligatoires
1. Le candidat est-il réellement non redondant ?
2. Son objet est-il assez précis ?
3. Son lemme candidat est-il général ?
4. Son test de réfutation est-il proche ?
5. Le candidat compresse-t-il mieux le manque concret que ses concurrents ?
6. Son lien au verrou est-il explicite ?
7. Résiste-t-il à l’audit historique et fail-closed ?

### Livrables
Pour chaque candidat :
- statut : [QUALIFIÉ] / [ÉLIMINÉ] / [QUALIFIÉ AVEC RÉSERVE] ;
- raison précise ;
- axe de victoire ou de défaite.

---

## AXE G — INVESTIGATEUR SYNTHÈSE / IMPACT PROGRAMMATIQUE RÉEL
### Nom de travail
Quel candidat ouvre quelque chose de vrai ?

### Mission
Évaluer ce que le meilleur candidat ferait vraiment gagner au programme.

### Questions obligatoires
1. Si le lemme candidat était prouvé, quel mur exact serait entamé ?
2. Ce gain est-il local, structurel, ou potentiellement décisif ?
3. Le candidat est-il seulement élégant, ou réellement utile ?
4. Quel seuil minimum faut-il atteindre pour justifier R83 ?
5. Quel candidat “intéressant” faut-il refuser comme encore trop faible ?

### Livrables
- chaîne logique explicite ;
- portée honnête ;
- seuil de pertinence pour continuer.

---

# PHASE 4 — DÉCISION STRATÉGIQUE

## AXE H — DÉCISION FINALE
### Nom de travail
A-t-on un vrai candidat de percée ?

### Mission
Décider si le tournoi fermé de R82 a produit un vrai candidat de percée, ou seulement une meilleure formulation du manque.

### Options possibles
- **Poursuivre** : un candidat réel survit avec lemme crédible et test de réfutation clair.
- **Poursuivre avec réserve** : le candidat est sérieux mais encore fragile.
- **Suspendre l’innovation** : aucun candidat ne dépasse le filtre.
- **Reformuler** : le manque a été mieux compris, mais aucun objet n’est encore le bon.

### Questions obligatoires
1. Quel candidat gagne le tournoi ?
2. Pourquoi mérite-t-il de survivre ?
3. Quelle est la condition explicite de non-boucle pour R83 ?
4. Que doit-on traiter comme progrès réel, et que doit-on refuser comme simple élégance ?
5. Quelles pistes doivent être enterrées sans ambiguïté ?

### Livrables
- décision stratégique finale ;
- survivant unique pour R83 ;
- condition de non-boucle ;
- raison des enterrements ou de la suspension.

---

# AUTONOMIE CONTRÔLÉE (COURTE ET TRÈS SUR RAILS)

## Activation
Une mini-autonomie est autorisée seulement entre la PHASE 2 et la PHASE 4 :
- pour faire vivre brièvement les candidats ;
- organiser l’audit croisé ;
- puis trancher le tournoi.
Jamais pour explorer librement.

## Budget maximal
Au plus **3 sous-rounds internes** :
- **S1** : qualification initiale des candidats ;
- **S2** : audit croisé, test de réalité et anti-redondance ;
- **S3** : élimination finale et choix du survivant.

## Événements STOP obligatoires
Arrêt immédiat si :
1. plus de 3 candidats sont proposés ;
2. un candidat n’a ni lemme candidat ni critère de réfutation ;
3. la réflexion dérive vers computationnel ou k-par-k ;
4. un candidat s’avère essentiellement redondant ;
5. aucun critère explicite de victoire n’apparaît ;
6. le vocabulaire devient plus riche que la chaîne logique ;
7. aucun seuil explicite de pertinence n’apparaît.

## Format obligatoire de chaque sous-round autonome
1. candidat(s) actif(s) ;
2. objet exact ;
3. question précise ;
4. chaîne de dérivation ou d’audit ;
5. résultat net ;
6. statut ;
7. critère de victoire ou d’élimination ;
8. ce qui est appris ;
9. décision : continuer / arrêter ;
10. raison explicite.

## Interdictions
- pas de calcul ;
- pas de Monte Carlo ;
- pas de k-par-k ;
- pas d’accumulation de micro-cas ;
- pas de sauvetage rhétorique d’un candidat faible.

---

# REGISTRE MÉTHODOLOGIQUE OBLIGATOIRE

## 1. Type du round
Rappeler explicitement : **X/I/P**
- **X** pour investigation causale et anti-redondance ;
- **I** pour innovation disciplinée ;
- **P** pour exigence de précision, testabilité et falsifiabilité.

## 2. IVS — Information Value Score
Noter /10 selon :
- précision du manque concret ;
- qualité des candidats ;
- robustesse anti-redondance ;
- qualité du tournoi fermé ;
- honnêteté de la décision finale.

## 3. Ladder of Proof
Pour chaque candidat, préciser :
- intuition ;
- manque visé ;
- schéma d’objet ;
- semi-formalisation ;
- lemme candidat ;
- test de mordant ;
- possibilité de preuve.

## 4. AUTOPSIE DES PISTES FERMÉES (OBLIGATOIRE)
Pour toute piste écartée, fournir :
- Nom ;
- Type de mort :
  - redondante,
  - faux dehors,
  - objet flou,
  - lemme trop haut,
  - critère de réfutation absent,
  - décor théorique,
  - trop faible ;
- Cause du rejet ;
- Ce que la mort enseigne ;
- Où cela redirige.

## 5. REGISTRE FAIL-CLOSED
Tu dois terminer par un tableau strict :
- [OBJET RÉEL]
- [SEMI-RÉEL]
- [QUALIFIÉ]
- [QUALIFIÉ AVEC RÉSERVE]
- [ÉLIMINÉ]
- [REDONDANT]
- [FAUX EXTÉRIEUR]
- [SEMI-FORMALISÉ]
- [FORTEMENT ÉTAYÉ]
- [HEURISTIQUE]
- [PROSE]
- [RÉFUTÉ]
- [À REFORMULER]
- [DIAGNOSTIC INSUFFISANT]

---

# CONTRAINTES MÉTHODOLOGIQUES
Tu dois distinguer explicitement :
- manque concret ;
- famille d’approche ;
- objet candidat ;
- lemme candidat ;
- critère de réfutation ;
- critère de victoire ;
- statut.

Tu dois favoriser les formulations minimales suffisantes :
- ni sauter de la compréhension à la solution ;
- ni inventer trop haut ;
- ni traiter une idée élégante comme une percée ;
- ni réemballer une voie fermée ;
- ni poursuivre un candidat qui ne gagne pas son tournoi.

Tu ne dois pas :
- proposer un candidat sans objet ;
- proposer un candidat sans lemme ;
- proposer un candidat sans critère de réfutation ;
- recycler une route enterrée sous un langage plus profond ;
- laisser l’autonomie dépasser ses STOP ou son budget.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : le manque concret est formulé proprement.
PASS-2 : au plus 3 candidats entrent en tournoi.
PASS-3 : chaque candidat a un objet, un lemme, un critère de réfutation et un critère de victoire.
PASS-4 : le filtre anti-redondance distingue clairement vraie nouveauté et résurrection d’impasse.
PASS-5 : le tournoi fermé produit une décision stratégique honnête.
PASS-6 : un unique survivant pour R83 est sélectionné, ou l’innovation est suspendue proprement.

# ÉCHEC UTILE
Même en cas d’échec, R82 est utile si :
- il montre qu’aucun candidat proposé n’est réellement nouveau ;
- il évite une fausse percée ;
- il clarifie mieux ce qui manque concrètement ;
- il remplace une créativité diffuse par une créativité auditée.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats PHASE 1 / AXE A (manque concret)
5. Résultats PHASE 1 / AXE B (familles d’approches autorisées)
6. Résultats PHASE 1 / AXE C (contrôle anti-redondance)
7. Résultats PHASE 2 / AXE D (candidats entrants en tournoi)
8. Résultats PHASE 2 / AXE E (styles d’agents et protocole)
9. Résultats PHASE 3 / AXE F (audit croisé et test de réalité)
10. Résultats PHASE 3 / AXE G (chaîne logique et impact)
11. Résultats PHASE 4 / AXE H (tournoi, élimination et décision finale)
12. Activation ou non de l’autonomie, avec justification
13. Journal des sous-rounds autonomes éventuels
14. Objets concernés + Ladder of Proof
15. Ce qui est appris
16. Ce qui est fermé utilement
17. Ce qui est enterré
18. Autopsie des pistes fermées
19. Survivant pour R83
20. Risques / limites
21. Verdict final avec score /10
22. Registre FAIL-CLOSED

---

# CONSIGNE FINALE
R82 doit être créatif, mais créatif sous contrôle.

Le but n’est pas de produire des idées “intéressantes”.
Le but est de fabriquer un vrai candidat de percée, ou d’enterrer proprement ceux qui n’en sont pas.

Chercher un manque concret, peu de candidats, un tournoi strict, et un survivant réel.
Pas une promesse de solution. Une innovation qui supporte l’audit.