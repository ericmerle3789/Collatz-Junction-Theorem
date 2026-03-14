

TYPE: I/P
OBJET CIBLÉ: tester si la reformulation SAMC issue de R74 compresse réellement le verrou du front k≥3, en cherchant un mécanisme général d’exclusion de -1 dans le sumset monotone, sans basculer dans le k-par-k, le cas-par-cas, ni le computationnel comme moteur principal
QUESTION CENTRALE: existe-t-il un mécanisme général, démontrable et non computationnel d’exclusion de -1 dans Σ≤(k), ou bien SAMC n’est-elle qu’une reformulation élégante sans compression réelle du problème ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: soit identifier un premier lemme général crédible sur Σ≤(k) relié explicitement au verrou du programme, soit démontrer que SAMC ne fournit pas encore de prise générale suffisante et doit être abaissée ou reformulée.
PRINCIPE D’ÉQUILIBRE: autoriser uniquement les tests locaux comme sondes secondaires de cohérence, jamais comme colonne vertébrale du round ; interdire le k-par-k, le cas-par-cas, le computationnel, et toute régression vers des validations par accumulation d’exemples.

# BRIEF CLAUDE CODE — ROUND 75 (R75)

## Mission
Tu poursuis le projet Collatz après R74.

R75 doit décider si la voie **SAMC** est une vraie compression du verrou, ou seulement une reformulation propre mais encore stérile.

Le round ne doit pas devenir :
- une étude successive de k=3, puis k=5, puis k=7, etc. ;
- une collection de cas particuliers ;
- une exploration computationnelle du sumset monotone ;
- une validation par exemples ;
- ni une dérive vers “ça a l’air de marcher sur plusieurs cas, donc on continue”.

**Le moteur du round doit être général, démontrable, et structurel.**

Les tests locaux sont autorisés seulement comme contrôles de cohérence secondaires, strictement subordonnés à une stratégie générale déjà formulée.

---

## Contexte acquis après R74
- Les voies analytiques standards sur les sommes courtes dans le régime exact du projet ont été jugées insuffisantes.
- R74 a proposé une innovation sérieuse : reformuler la condition de non-annulation en un problème d’évitement de -1 dans un **sumset monotone** :
  Σ≤(k) = { Σ_{j=1}^{k-1} λ^j 2^{g_j} mod p : 0 ≤ g_1 < ... < g_{k-1} ≤ S-1 }.
- La chaîne logique vers le verrou est propre :
  corrSum ≡ 0 ⇔ -1 ∈ Σ≤(k),
  donc N_0(p)=0 ⇔ -1 ∉ Σ≤(k).
- Le bilan R74 suggère que SAMC est une vraie nouveauté structurelle, mais laisse ouverte la question centrale :
  **SAMC compresse-t-elle réellement le verrou, ou redécrit-elle seulement le problème ?**
- Le danger immédiat est de retomber dans le réflexe :
  - tester k=3, puis k=5, puis k=7 ;
  - observer des régularités ;
  - et transformer cela en pseudo-preuve par cas.
- R75 doit donc forcer une montée en généralité :
  **quel mécanisme général peut exclure -1 de Σ≤(k) ?**

---

# OBJECTIF DE R75
R75 doit répondre à cette question centrale :

> Existe-t-il un premier mécanisme général, non computationnel et démontrable, qui permette d’exclure -1 de Σ≤(k) ou de réduire ce problème à un lemme général plus mordant ?

Les sorties acceptables du round sont :
1. **Un lemme général crédible sur Σ≤(k) est identifié, avec chaîne logique explicite vers le verrou** ;
2. **Un mécanisme partiel général est identifié, mais encore insuffisant pour conclure** ;
3. **Aucun mécanisme général n’émerge : SAMC doit être abaissée ou reformulée** ;
4. **Le bon objet préparatoire manque encore : la formulation SAMC n’est pas encore la bonne compression.**

Important :
- aucune sortie n’est recevable si elle repose sur une succession de valeurs de k ;
- aucune sortie n’est recevable si elle tire sa force de calculs, d’exemples, ou d’une impression statistique ;
- aucune sortie n’est recevable si elle confond “propriété observée sur quelques cas” et “mécanisme général”.

---

# ARCHITECTURE GÉNÉRALE

## PHASE 1 — FIXER LE VRAI PROBLÈME GÉNÉRAL DE SAMC
Objectif : expliciter ce qu’il faudrait démontrer en général sur Σ≤(k), indépendamment des petites valeurs de k.

## PHASE 2 — CHERCHER DES MÉCANISMES GÉNÉRAUX D’EXCLUSION
Objectif : identifier au plus quelques mécanismes structurels crédibles pour exclure -1 sans tomber dans le cas-par-cas.

## PHASE 3 — TEST DE MORDANT ET FILTRE ANTI-k-PAR-k
Objectif : vérifier que les mécanismes proposés sont réellement généraux et non des leurres déguisés.

## PHASE 4 — DÉCISION STRATÉGIQUE
Objectif : garder un seul survivant pour R76, ou déclassement honnête de SAMC si aucun mécanisme général ne tient.

## Ce qui est interdit comme cible principale
- étude de k=3, k=5, k=7, etc. ;
- preuves ou quasi-preuves par accumulation de cas ;
- computationnel, Monte Carlo, balayage de primes ;
- arguments fondés sur de petits exemples comme support principal ;
- retour masqué à des routes analytiques déjà fermées ;
- inflation de vocabulaire combinatoire sans lemme précis.

---

# PHASE 1 — FIXER LE VRAI PROBLÈME GÉNÉRAL DE SAMC

## AXE A — INVESTIGATEUR / FORMULATION GÉNÉRALE DU VERROU SAMC
### Nom de travail
Qu’est-ce qu’il faudrait vraiment montrer, pour tout k, et non pour quelques-uns ?

### Mission
Définir proprement la propriété générale qu’on voudrait établir sur Σ≤(k), sans aucune dépendance à une liste de petites valeurs de k.

### Questions obligatoires
1. Quelle est la propriété générale candidate sur Σ≤(k) qui serait réellement utile au programme ?
2. Est-ce une propriété d’évitement, de taille, de rigidité, de structure du support, de non-recouvrement, ou autre ?
3. Quel est le quantificateur correct : pour tout k, pour une famille de k, pour tout p admissible, sous quelles conditions exactes ?
4. Quelle formulation est assez générale pour éviter le cas-par-cas, mais assez précise pour être prouvable ?
5. Quel serait le premier énoncé trop faible à interdire ?

### Livrables
- formulation générale canonique du verrou SAMC ;
- liste des formulations trop faibles ou trop locales à bannir ;
- version minimale de l’énoncé qu’un lemme sérieux devrait viser.

---

# PHASE 2 — CHERCHER DES MÉCANISMES GÉNÉRAUX D’EXCLUSION

## AXE B — INNOVATEUR DISCIPLINÉ / PROPOSITION DE MÉCANISMES GÉNÉRAUX
### Nom de travail
Quel type de structure pourrait vraiment exclure -1 ?

### Mission
Proposer au maximum **3 mécanismes généraux** possibles, pas davantage.
Chaque mécanisme doit être formulé comme une vraie idée mathématique structurée, pas comme une intuition vague.

### Types de mécanismes autorisés
- rigidité d’un sumset monotone restreint ;
- invariants de support ou de poids empêchant certains recouvrements ;
- principe de non-collision ou de non-saturation ;
- phénomène de dispersion non analytique classique ;
- réduction algébrique/combinatoire nouvelle ;
- contrainte d’ordre transformée en contrainte structurelle exploitable.

### Types de mécanismes interdits
- “sur les petits k on observe…” ;
- “il semble que…” sans lemme ;
- réemballage de la bilinéarité courte ou d’outils standards ;
- mécanisme dépendant d’une exploration explicite des cas ;
- innovation sans test de réfutation rapide.

### Questions obligatoires pour chaque mécanisme
1. Quel est le mécanisme exact ?
2. Quel aspect du verrou compresse-t-il ?
3. Quelle différence réelle a-t-il avec les routes déjà fermées ?
4. Quel premier lemme général engendre-t-il ?
5. Quel premier signe montrerait qu’il est vide ou trop faible ?

### Livrables
Pour chaque mécanisme candidat :
- nom de travail ;
- formulation semi-formelle ;
- verrou visé ;
- premier lemme candidat ;
- premier critère de réfutation.

---

## AXE C — INVESTIGATEUR HISTORIQUE / CONTRÔLE ANTI-REBRANDING ET ANTI-k-PAR-k
### Nom de travail
Vraie généralité ou vieux cas particuliers masqués ?

### Mission
Vérifier que chaque mécanisme proposé n’est ni un recyclage d’une route morte, ni une méthode qui ne vit que sur quelques petites valeurs de k.

### Questions obligatoires
1. À quelle ancienne piste ce mécanisme ressemble-t-il ?
2. Quelle différence porte sur le cœur du problème, et non sur le langage ?
3. Ce mécanisme dépend-il en pratique d’une compréhension des petits k ?
4. Si oui, peut-on l’arracher à cette dépendance et le reformuler en général ?
5. Doit-on le classer comme :
   - général réel,
   - général apparent,
   - rebranding,
   - cas-par-cas déguisé ?

### Livrables
- tableau “ancienne piste / dépendance cachée aux petits k / verdict” ;
- drapeau rouge sur tout mécanisme pseudo-général.

---

# PHASE 3 — TEST DE MORDANT ET FILTRE ANTI-k-PAR-k

## AXE D — AUDITEUR FAIL-CLOSED / TEST DE GÉNÉRALITÉ RÉELLE
### Nom de travail
Le mécanisme vit-il sans béquilles locales ?

### Mission
Tester chaque mécanisme candidat selon trois exigences :
- généricité réelle,
- testabilité logique,
- pertinence pour le verrou.

### Critères obligatoires pour chaque mécanisme
1. Le mécanisme produit-il un lemme réellement général ?
2. Ce lemme évite-t-il toute dépendance structurelle aux petites valeurs de k ?
3. La chaîne de réduction vers le verrou est-elle explicite ?
4. Le test de mordant est-il faisable sans computationnel ?
5. Le mécanisme réduit-il le problème ou ne fait-il que le reformuler ?
6. Quel premier échec l’invaliderait ?

### Livrables
Pour chaque mécanisme :
- statut : [GÉNÉRAL RÉEL] / [SEMI-GÉNÉRAL] / [LOCAL DÉGUISÉ] / [PROSE] ;
- statut du lemme : [BIEN CIBLÉ] / [TROP FLOU] / [TROP FORT] / [TROP LOCAL] ;
- verdict de mordant : [TESTABLE] / [TESTABLE MAIS FAIBLE] / [NON TESTABLE].

---

## AXE E — INVESTIGATEUR / CHAÎNE DE RÉDUCTION ET SEUIL DE PERTINENCE
### Nom de travail
Même si le lemme est vrai, qu’est-ce qu’il donnerait vraiment ?

### Mission
Évaluer honnêtement l’impact programmatique du meilleur mécanisme restant.

### Questions obligatoires
1. Si le lemme candidat était prouvé, qu’est-ce qui deviendrait acquis ?
2. Quel morceau exact du mur serait entamé ?
3. Est-ce un pas décisif, structurel, local, ou seulement exploratoire ?
4. Quel est le seuil minimal à atteindre pour justifier R76 ?
5. Que faut-il refuser explicitement comme “joli mais insuffisant” ?

### Livrables
- chaîne logique explicite ;
- portée honnête du meilleur lemme ;
- seuil de pertinence pour continuer.

---

# PHASE 4 — DÉCISION STRATÉGIQUE

## AXE F — DÉCISION FINALE
### Nom de travail
SAMC tient-elle comme vraie compression ?

### Mission
Décider si la voie SAMC doit être poursuivie, reformulée, ou déclassée.

### Options possibles
- **Poursuivre** : un mécanisme général réel produit un lemme bien ciblé et testable.
- **Poursuivre avec réserve** : le mécanisme est sérieux mais encore partiellement trop fort ou trop flou.
- **Reformuler** : l’idée de SAMC est bonne, mais le mécanisme trouvé n’est pas encore le bon.
- **Déclasser** : aucun mécanisme général ne dépasse le cas-par-cas ou la prose.

### Questions obligatoires
1. Quel mécanisme compresse le mieux le verrou ?
2. Quel mécanisme est réellement général ?
3. Quelle est la condition explicite de non-boucle pour R76 ?
4. Quel unique survivant faut-il garder ?
5. Quelles pistes doivent être enterrées sans ambiguïté ?

### Livrables
- décision stratégique finale ;
- survivant unique pour R76 ;
- condition explicite de non-boucle ;
- raison des enterrements.

---

# AGENTS ET RÔLES

## Investigateur principal
- fixe la formulation générale ;
- interdit les glissements de quantificateurs ;
- exige un vrai lemme.

## Innovateur discipliné
- propose au plus 3 mécanismes ;
- n’a pas le droit d’utiliser les petits k comme moteur ;
- doit fournir immédiatement lemme candidat + critère de réfutation.

## Investigateur historique
- compare à l’historique ;
- empêche le rebranding ;
- détecte toute dépendance masquée aux cas particuliers.

## Auditeur fail-closed
- teste la généricité réelle ;
- refuse tout mécanisme local déguisé ;
- refuse toute innovation sans prise démontrable.

---

# AUTONOMIE CONTRÔLÉE (EXTRÊMEMENT COURTE)

## Activation
Une mini-autonomie est autorisée seulement en PHASE 4 pour départager deux mécanismes proches, jamais pour explorer librement.

## Budget maximal
Au plus **2 sous-rounds internes** :
- **S1** : comparaison finale de 2 mécanismes survivants ;
- **S2** : décision stratégique finale.

## Événements STOP obligatoires
Arrêt immédiat si :
1. plus de 3 mécanismes sont proposés ;
2. un mécanisme dépend en pratique des petits k ;
3. la réflexion dérive vers du computationnel ;
4. la réflexion dérive vers une accumulation de cas ;
5. la nouveauté est surtout lexicale ;
6. aucun lemme général testable n’émerge.

## Format obligatoire de chaque sous-round autonome
1. hypothèse active ;
2. mécanisme exact ;
3. question ;
4. démarche ;
5. résultat net ;
6. statut ;
7. ce qui est appris ;
8. décision : continuer / arrêter ;
9. raison explicite.

## Interdictions
- pas de calcul ;
- pas de Monte Carlo ;
- pas de k-par-k ;
- pas d’accumulation de micro-cas ;
- pas de sauvetage rhétorique d’un mécanisme vide.

---

# REGISTRE MÉTHODOLOGIQUE OBLIGATOIRE

## 1. Type du round
Rappeler explicitement : **I/P**
- **I** pour innovation disciplinée ;
- **P** pour preuve, testabilité et généralité réelle.

## 2. IVS — Information Value Score
Noter /10 selon :
- compression réelle du verrou ;
- généralité réelle ;
- testabilité précoce ;
- robustesse anti-k-par-k ;
- honnêteté de la décision finale.

Une bonne note IVS peut venir d’un enterrement propre si le round démontre que SAMC ne fournit pas encore de mécanisme général réel.

## 3. Ladder of Proof
Pour chaque mécanisme candidat, préciser :
- intuition ;
- schéma d’objet ;
- semi-formalisation ;
- lemme candidat ;
- test de mordant ;
- possibilité de preuve ;
- potentiel publiable.

## 4. AUTOPSIE DES PISTES FERMÉES (OBLIGATOIRE)
Pour toute piste écartée, fournir :
- Nom ;
- Type de mort :
  - cas-par-cas déguisé,
  - prose sans mécanisme,
  - lemme trop local,
  - lemme trop fort,
  - rebranding d’une route morte,
  - dépendance cachée aux petits k,
  - non-falsifiable ;
- Hypothèse implicite fausse ;
- Ce que la mort enseigne ;
- Où cela redirige.

## 5. REGISTRE FAIL-CLOSED
Tu dois terminer par un tableau strict :
- [PROUVÉ]
- [PARTIELLEMENT PROUVÉ]
- [CALCULÉ EXACT]
- [SEMI-FORMALISÉ]
- [FORTEMENT ÉTAYÉ]
- [HEURISTIQUE]
- [CONJECTURAL]
- [RÉFUTÉ]
- [À REFORMULER]
- [PROSE]
- [LOCAL DÉGUISÉ]

---

# CONTRAINTES MÉTHODOLOGIQUES
Tu dois distinguer explicitement :
- verrou général ;
- mécanisme général ;
- lemme candidat ;
- test de mordant ;
- rôle logique ;
- statut.

Tu dois favoriser les formulations minimales suffisantes :
- ni passer par les petits k ;
- ni utiliser des exemples comme colonne vertébrale ;
- ni survivre par style ;
- ni poursuivre une voie qui ne donne qu’une généralité apparente ;
- ni enterrer trop vite une vraie idée générale testable.

Tu ne dois pas :
- proposer un mécanisme sans définition ;
- proposer un mécanisme sans lemme ;
- proposer un mécanisme sans critère de réfutation ;
- rouvrir une route morte sous un nom neuf ;
- laisser l’autonomie dépasser ses STOP ou son budget.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : le verrou SAMC est formulé proprement à un niveau général.
PASS-2 : au plus 3 mécanismes candidats sont proposés.
PASS-3 : chaque mécanisme a un lemme général et un critère de réfutation.
PASS-4 : le filtre anti-k-par-k distingue clairement généralité réelle et cas locaux déguisés.
PASS-5 : une décision stratégique finale honnête est prise.
PASS-6 : un unique survivant pour R76 est sélectionné, ou bien tout est enterré proprement.

# ÉCHEC UTILE
Même en cas d’échec, R75 est utile si :
- une fausse généralité est reconnue avant de boucler ;
- une dépendance cachée aux petits k est mise à nu ;
- une innovation vide est enterrée proprement ;
- le programme apprend mieux quel type de mécanisme général manque réellement.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats PHASE 1 / AXE A (verrou SAMC général)
5. Résultats PHASE 2 / AXE B (mécanismes candidats)
6. Résultats PHASE 2 / AXE C (contrôle anti-rebranding et anti-k-par-k)
7. Résultats PHASE 3 / AXE D (test de généralité réelle)
8. Résultats PHASE 3 / AXE E (chaîne logique et impact)
9. Résultats PHASE 4 / AXE F (décision finale)
10. Activation ou non de l’autonomie, avec justification
11. Journal des sous-rounds autonomes éventuels
12. Objets concernés + Ladder of Proof
13. Ce qui est appris
14. Ce qui est fermé utilement
15. Ce qui est enterré
16. Autopsie des pistes fermées
17. Survivant pour R76
18. Risques / limites
19. Verdict final avec score /10
20. Registre FAIL-CLOSED

---

# CONSIGNE FINALE
R75 doit refuser la pente du k-par-k et du cas-par-cas, même si cette pente paraît rassurante.

Le but est de savoir si SAMC porte un mécanisme général réel, pas si quelques petites instances se comportent bien.

Chercher une vraie généralité, un vrai lemme, et un vrai test de mordant.
Pas une collection d’exemples. Une structure qui tienne pour de bon.