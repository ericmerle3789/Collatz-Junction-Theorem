

TYPE: X/I/P
OBJET CIBLÉ: pousser l’investigation jusqu’à la cause racine de la cause racine des blocages du programme, puis n’autoriser l’innovation qu’à partir de cette source première, avec un couplage strict investigation profonde → innovation disciplinée, sans computationnel, sans k-par-k, sans prose, sans rebranding et sans arrêt prématuré au niveau d’un simple outil insuffisant
QUESTION CENTRALE: quel est le mécanisme source le plus profond qui engendre les blocages observés sur les voies additifs, multiplicatives, bilinéaires et SAMC, et quel objet minimal vraiment nouveau peut être construit à partir de cette source première plutôt qu’à partir d’un symptôme ou d’un outil raté ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: soit identifier une cause source plus profonde que tout ce qui a déjà été formulé, avec un objet minimal testable qui en découle, soit démontrer qu’on a effectivement atteint la racine conceptuelle la plus profonde accessible à ce stade et que tout nouvel objet proposé n’est encore qu’un réemballage d’étage intermédiaire.
PRINCIPE D’ÉQUILIBRE: considérer que la complexité n’est qu’une accumulation de simplicités mal isolées ; remonter sans pitié les chaînes causales jusqu’au mécanisme source, puis n’autoriser l’innovation qu’à partir de cette source et sous contrainte de définition, lemme candidat, test de réfutation et chaîne logique explicite.

# BRIEF CLAUDE CODE — ROUND 79 (R79)

## Mission
Tu poursuis le projet Collatz après R78 et après toute la séquence d’autopsies récente.

R79 est un round d’**investigation radicale puis d’innovation sous source**.

Le but n’est pas de proposer encore un meilleur outil.
Le but n’est pas de changer une représentation ou de déplacer la difficulté d’un étage à un autre.
Le but n’est pas non plus de faire un bilan rhétorique du type “on a compris beaucoup de choses”.

Le but exact est :

> **remonter jusqu’à la cause racine de la cause racine, vérifier que nous ne nous sommes pas arrêtés à un étage outillage/méthode/forme, puis n’autoriser une innovation que si elle est construite à partir de cette source première et non à partir d’un symptôme.**

Autrement dit :
- ne pas s’arrêter à “outil trop faible” ;
- ne pas s’arrêter à “cadre additif insuffisant” ;
- ne pas s’arrêter à “cadre multiplicatif insuffisant” ;
- ne pas s’arrêter à “interface somme-produit” comme nouveau slogan si cette interface n’est elle-même qu’un étage intermédiaire ;
- remonter encore, jusqu’à la simplicité primitive qui, en s’additionnant, produit la complexité observée.

R79 doit être extrêmement exigeant.
Toute innovation qui n’est pas reliée à une cause source documentée doit être traitée comme prématurée.

---

## Contexte acquis avant R79
- Les voies analytiques standards sur les sommes courtes dans le régime exact du projet ont été déclassées.
- SAMC a constitué une innovation sérieuse, mais sans compression démontrée du verrou.
- R75 a testé plusieurs mécanismes et a conclu trop vite ; R76 a corrigé cela en exigeant une autopsie causale.
- R76 a isolé des causes importantes :
  - perte de localisation dans le cadre additif de F_p ;
  - insuffisance structurelle du support de taille O(log p) ;
  - faux statut de certains verrous comme la monotonie.
- R77 a montré que le déplacement vers le multiplicatif pur ne suffit pas non plus, et a suggéré que le manque réel pourrait vivre à une interface plus profonde entre structures additives et multiplicatives.
- Cependant, il reste possible que même cette “interface somme-produit” soit encore un étage intermédiaire, pas encore la cause racine.
- Le danger majeur est donc maintenant :
  1. prendre une couche intermédiaire pour la source première ;
  2. innover à partir d’un symptôme raffiné ;
  3. fabriquer un nouvel objet élégant mais encore trop haut dans la chaîne causale.

---

# OBJECTIF DE R79
R79 doit répondre à cette question centrale :

> Avons-nous réellement atteint la cause racine la plus profonde accessible du blocage, ou nous sommes-nous encore arrêtés à un étage intermédiaire ? Et, si cette cause racine peut être isolée, quel est l’objet minimal nouveau qui en découle directement ?

Les sorties acceptables du round sont :
1. **Une cause source plus profonde est identifiée, et un objet minimal testable en découle** ;
2. **La cause source la plus profonde accessible est confirmée, et toute innovation candidate au-dessus d’elle est reclassée comme étage intermédiaire** ;
3. **Deux causes profondes concurrentes subsistent, clairement séparées et bornées, sans confusion rhétorique** ;
4. **L’investigation reste insuffisante : le round est non concluant et ne doit pas lancer d’innovation.**

Important :
- aucune sortie n’est recevable si elle se contente d’un nouveau slogan ;
- aucune sortie n’est recevable si elle conclut à une “source profonde” sans chaîne de remontée causale ;
- aucune sortie n’est recevable si l’objet innovant proposé ne naît pas explicitement de la cause source ;
- aucune sortie n’est recevable si elle repose sur computationnel, k-par-k, cas particuliers, ou exemples accumulés.

---

# ARCHITECTURE GÉNÉRALE

## PHASE 1 — REMONTÉE CAUSALE JUSQU’À LA SOURCE PREMIÈRE
Objectif : vérifier si les diagnostics actuels sont ultimes ou encore intermédiaires.

## PHASE 2 — FILTRE ANTI-ÉTAGE INTERMÉDIAIRE
Objectif : distinguer cause source, mécanisme intermédiaire, symptôme, outil raté et faux verrou.

## PHASE 3 — INNOVATION SOUS CONTRAINTE DE SOURCE
Objectif : n’autoriser que des objets minimaux dérivés directement de la cause source.

## PHASE 4 — DÉCISION STRATÉGIQUE
Objectif : garder au plus un objet survivant pour R80, ou suspendre l’innovation si la source n’est pas encore suffisamment comprise.

## Ce qui est interdit comme cible principale
- toute exploration computationnelle ;
- tout k-par-k ;
- toute galerie de théories ;
- tout rebranding d’un étage déjà diagnostiqué ;
- toute innovation sans chaîne causale source → objet → lemme ;
- toute clôture rhétorique du type “on a atteint la frontière” sans preuve causale de racine.

---

# PHASE 1 — REMONTÉE CAUSALE JUSQU’À LA SOURCE PREMIÈRE

## AXE A — INVESTIGATEUR PARALLÈLE 1 / LES DIAGNOSTICS ADDITIFS SONT-ILS FINAUX OU INTERMÉDIAIRES ?
### Nom de travail
Le cadre additif est-il la cause ou seulement le premier révélateur ?

### Mission
Reprendre les diagnostics liés au cadre additif de F_p et déterminer s’ils constituent une cause source, ou seulement une manifestation plus visible d’une cause plus profonde.

### Questions obligatoires
1. La perte de localisation dans F_p additif est-elle la cause du blocage, ou un effet d’un désalignement plus profond ?
2. Si elle n’est qu’un effet, quel mécanisme plus simple l’engendre ?
3. Quels diagnostics additifs doivent être reclassés comme symptômes ?
4. Quel faux verrou additif doit être définitivement enterré ?
5. Peut-on résumer en une phrase ce que le cadre additif ne fait que révéler sans l’expliquer ?

### Livrables
- tri : [CAUSE] / [SYMPTÔME] / [RÉVÉLATEUR] ;
- chaîne de remontée causale ;
- diagnostics additifs reclassés.

---

## AXE B — INVESTIGATEUR PARALLÈLE 2 / LES DIAGNOSTICS MULTIPLICATIFS SONT-ILS FINAUX OU INTERMÉDIAIRES ?
### Nom de travail
Le multiplicatif pur manque-t-il la source profonde ?

### Mission
Tester si la géométrie multiplicative de <2> est une couche causale terminale ou elle aussi un étage intermédiaire.

### Questions obligatoires
1. Qu’est-ce que le cadre multiplicatif pur explique mieux que l’additif ?
2. Qu’est-ce qu’il n’explique toujours pas ?
3. Son échec provient-il d’un manque proprement multiplicatif, ou d’une structure encore plus primitive ?
4. Quels diagnostics multiplicatifs doivent être reclassés comme insuffisants mais révélateurs ?
5. Quel est le point précis où le multiplicatif pur cesse d’être une explication et redevient un outil ?

### Livrables
- tri : [CAUSE] / [MÉCANISME INTERMÉDIAIRE] / [OUTIL] ;
- chaîne de remontée ;
- requalification du cadre multiplicatif.

---

## AXE C — INVESTIGATEUR PARALLÈLE 3 / L’INTERFACE ADDITIF-MULTIPLICATIF EST-ELLE VRAIMENT LA RACINE ?
### Nom de travail
L’interface est-elle la source ou encore un étage ?

### Mission
Prendre l’hypothèse survivante de R77 — “le blocage vit à l’interface additif/multiplicatif” — et la soumettre à une autopsie plus profonde.

### Questions obligatoires
1. Cette interface est-elle une cause primitive ou un résumé pratique de plusieurs mécanismes plus simples ?
2. Peut-on la décomposer en composants plus élémentaires ?
3. Quelle est la plus petite interaction irréductible réellement nécessaire pour produire le blocage ?
4. Qu’est-ce qui, dans l’interface actuelle, est encore trop macro ?
5. À quel niveau exact s’arrête la compression de l’explication ?

### Livrables
- décomposition de l’interface ;
- composant irréductible candidat ;
- diagnostic : [RACINE PLAUSIBLE] / [ÉTAGE INTERMÉDIAIRE] / [FORMULATION TROP MACRO].

---

# PHASE 2 — FILTRE ANTI-ÉTAGE INTERMÉDIAIRE

## AXE D — INVESTIGATEUR SYNTHÈSE / CARTE SOURCE → MÉCANISME → SYMPTÔME
### Nom de travail
Sommes-nous encore arrêtés à un étage ?

### Mission
Fusionner les trois investigations précédentes pour construire une carte causale hiérarchique complète.

### Niveaux à distinguer explicitement
- cause source ;
- mécanisme intermédiaire ;
- symptôme structurel ;
- faux verrou ;
- outil insuffisant.

### Questions obligatoires
1. Quel est le plus profond niveau causal actuellement justifiable ?
2. Quelles couches supérieures doivent être déclassées comme intermédiaires ?
3. Y a-t-il une seule source, ou deux causes profondes indépendantes ?
4. Quel faux “niveau ultime” doit être explicitement refusé ?
5. La carte causale réduit-elle vraiment l’espace des innovations futures ?

### Livrables
- carte hiérarchique complète ;
- cause source candidate ;
- couches intermédiaires reclassées ;
- faux niveau ultime enterré.

---

## AXE E — AUDITEUR FAIL-CLOSED / TEST DE RACINE RÉELLE
### Nom de travail
Avons-nous vraiment touché la racine ?

### Mission
Vérifier si la cause source candidate mérite vraiment ce statut.

### Critères obligatoires
1. La cause candidate explique-t-elle plusieurs échecs auparavant séparés ?
2. Réduit-elle vraiment la complexité au lieu de seulement la renommer ?
3. Est-elle formulable simplement et précisément ?
4. A-t-elle un pouvoir discriminant pour refuser de fausses innovations ?
5. Quel premier fait montrerait qu’elle n’est encore qu’un étage intermédiaire ?

### Livrables
- statut : [CAUSE SOURCE CREDIBLE] / [CAUSE SOURCE PARTIELLE] / [ÉTAGE INTERMÉDIAIRE] / [DIAGNOSTIC INSUFFISANT] ;
- justification ;
- test de falsification de la prétendue racine.

---

# PHASE 3 — INNOVATION SOUS CONTRAINTE DE SOURCE

## AXE F — INNOVATEUR DISCIPLINÉ / OBJETS MINIMAUX DÉRIVÉS DE LA CAUSE SOURCE
### Nom de travail
Que peut-on construire directement depuis la source ?

### Mission
Seulement après validation de la cause source candidate, proposer au maximum **2 objets minimaux** qui en découlent directement. Pas 3. Pas plus.

### Règle absolue
Un objet n’est recevable que si l’on peut tracer explicitement :

cause source → besoin structurel → objet minimal → premier lemme candidat → critère de réfutation.

### Formes d’objets autorisées
- invariant minimal ;
- pseudo-norme ou énergie minimale ;
- structure de compatibilité minimale ;
- décomposition élémentaire issue de la source ;
- filtration ou contrainte minimale directement dérivée de la cause source.

### Formes interdites
- théorie générale prématurée ;
- vocabulaire nouveau sans réduction du problème ;
- objet “inspiré” par la source mais non dérivé d’elle ;
- objet dépendant des petits k ;
- objet sans lemme candidat ou sans réfutation rapide.

### Questions obligatoires pour chaque objet
1. Quel besoin exact de la cause source l’objet incarne-t-il ?
2. En quoi l’objet est-il minimal ?
3. Quel premier lemme candidat produit-il ?
4. Quel premier signe montrerait qu’il est vide ou encore trop haut ?
5. Pourquoi n’est-il pas seulement un nouvel habillage d’un mécanisme intermédiaire ?

### Livrables
Pour chaque objet candidat :
- définition ou schéma semi-formel ;
- dérivation depuis la cause source ;
- premier lemme candidat ;
- premier critère de réfutation.

---

## AXE G — INVESTIGATEUR HISTORIQUE / CONTRÔLE ANTI-RÉGRESSION ET ANTI-REBRANDING
### Nom de travail
Objet source ou vieux fantôme ?

### Mission
Comparer les objets minimaux candidats à l’historique complet pour s’assurer qu’ils ne sont pas des réapparitions d’anciens outils sous un langage plus profond.

### Questions obligatoires
1. À quelle ancienne route chaque objet ressemble-t-il superficiellement ?
2. Quelle différence réelle vient du fait qu’il dérive de la cause source ?
3. Cette différence suffit-elle à rendre l’objet réellement nouveau ?
4. Y a-t-il une dépendance cachée au computationnel, aux petits k, ou à un ancien cadre insuffisant ?
5. Faut-il classer l’objet comme :
   - nouveauté réelle,
   - nouveauté partielle,
   - rebranding risqué,
   - rebranding certain ?

### Livrables
- tableau “ancienne piste / ressemblance / différence source / verdict” ;
- drapeau rouge sur toute régression masquée.

---

# PHASE 4 — DÉCISION STRATÉGIQUE

## AXE H — DÉCISION FINALE
### Nom de travail
Avons-nous enfin la bonne source, et un bon premier objet ?

### Mission
Décider si :
- la cause source la plus profonde accessible est bien identifiée ;
- un objet minimal en dérive proprement ;
- ou si l’innovation doit être suspendue faute de racine assez nette.

### Options possibles
- **Poursuivre** : une cause source crédible est isolée et un objet minimal réel en dérive.
- **Poursuivre avec réserve** : la source est plausible mais pas encore totalement stabilisée, l’objet minimal est sérieux mais fragile.
- **Suspendre l’innovation** : la source n’est pas encore assez nette pour justifier un nouvel objet.
- **Déclasser** : les objets proposés ne dérivent pas réellement de la source et doivent être enterrés.

### Questions obligatoires
1. La cause source candidate est-elle réellement plus profonde que les diagnostics précédents ?
2. Quel objet minimal en dérive le plus proprement ?
3. Quelle est la condition explicite de non-boucle pour R80 ?
4. Quel unique survivant faut-il garder ?
5. Quelles couches intermédiaires faut-il désormais traiter comme stabilisées, et non plus comme objectifs ?

### Livrables
- décision stratégique finale ;
- survivant unique pour R80 ;
- condition explicite de non-boucle ;
- raison des enterrements et suspensions.

---

# AGENTS ET RÔLES

## Investigateur parallèle 1
- requalifie le blocage additif ;
- distingue cause, symptôme, révélateur.

## Investigateur parallèle 2
- requalifie le blocage multiplicatif ;
- distingue cadre utile et étage intermédiaire.

## Investigateur parallèle 3
- dissèque l’interface additif/multiplicatif ;
- cherche le composant irréductible.

## Investigateur synthèse
- construit la carte hiérarchique source → mécanisme → symptôme ;
- refuse les faux niveaux ultimes.

## Innovateur discipliné
- n’intervient qu’après la validation d’une cause source crédible ;
- propose au plus 2 objets minimaux ;
- doit fournir immédiatement lemme candidat + critère de réfutation.

## Investigateur historique
- compare à l’historique ;
- empêche le rebranding ;
- détecte toute dépendance masquée aux anciens cadres.

## Auditeur fail-closed
- teste la crédibilité de la racine ;
- refuse toute innovation non dérivée de la source ;
- refuse toute conclusion terminale sans chaîne causale complète.

---

# AUTONOMIE CONTRÔLÉE (COURTE ET TRÈS SUR RAILS)

## Activation
Une mini-autonomie est autorisée seulement entre la PHASE 2 et la PHASE 4 :
- pour fusionner les diagnostics de racine,
- puis départager au plus 2 objets minimaux.
Jamais pour explorer librement.

## Budget maximal
Au plus **3 sous-rounds internes** :
- **S1** : fusion des diagnostics de racine ;
- **S2** : test des objets minimaux dérivés ;
- **S3** : décision finale.

## Événements STOP obligatoires
Arrêt immédiat si :
1. la cause source n’est pas plus profonde que les diagnostics déjà connus ;
2. plus de 2 objets minimaux sont proposés ;
3. un objet n’a ni lemme candidat ni critère de réfutation ;
4. le raisonnement dérive vers computationnel ou k-par-k ;
5. le vocabulaire devient plus riche que la chaîne causale ;
6. aucune condition explicite de non-boucle n’apparaît.

## Format obligatoire de chaque sous-round autonome
1. hypothèse de racine active ;
2. niveau causal étudié ;
3. question précise ;
4. chaîne de remontée ou de dérivation ;
5. résultat net ;
6. statut ;
7. ce qui est appris ;
8. décision : continuer / arrêter ;
9. raison explicite.

## Interdictions
- pas de calcul ;
- pas de Monte Carlo ;
- pas de k-par-k ;
- pas de théorie générale prématurée ;
- pas de sauvetage rhétorique d’un faux objet profond.

---

# REGISTRE MÉTHODOLOGIQUE OBLIGATOIRE

## 1. Type du round
Rappeler explicitement : **X/I/P**
- **X** pour investigation jusqu’à la racine ;
- **I** pour innovation sous contrainte de source ;
- **P** pour exigence de précision, testabilité et falsifiabilité.

## 2. IVS — Information Value Score
Noter /10 selon :
- profondeur réelle de la remontée causale ;
- clarté du niveau source ;
- minimalité et réalité de l’objet dérivé ;
- qualité du contrôle anti-régression ;
- honnêteté de la décision finale.

Une bonne note IVS peut venir d’une suspension propre de l’innovation si la source n’est pas encore assez nette.

## 3. Ladder of Proof
Pour la cause source candidate et chaque objet dérivé, préciser :
- intuition ;
- symptôme expliqué ;
- mécanisme intermédiaire absorbé ;
- formulation minimale ;
- lemme candidat ;
- test de mordant ;
- possibilité de preuve.

## 4. AUTOPSIE DES PISTES FERMÉES (OBLIGATOIRE)
Pour toute piste écartée, fournir :
- Nom ;
- Type de mort :
  - étage intermédiaire pris pour racine,
  - objet non dérivé de la source,
  - lemme trop haut,
  - décor théorique,
  - rebranding,
  - dépendance cachée à un ancien cadre,
  - non-falsifiable ;
- Cause du rejet ;
- Ce que la mort enseigne ;
- Où cela redirige.

## 5. REGISTRE FAIL-CLOSED
Tu dois terminer par un tableau strict :
- [CAUSE SOURCE CRÉDIBLE]
- [CAUSE SOURCE PARTIELLE]
- [MÉCANISME INTERMÉDIAIRE]
- [SYMPTÔME]
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
- cause source ;
- étage intermédiaire ;
- symptôme ;
- objet minimal dérivé ;
- lemme candidat ;
- critère de réfutation ;
- statut.

Tu dois favoriser les formulations minimales suffisantes :
- ni s’arrêter trop haut ;
- ni inventer avant la racine ;
- ni survivre par style ;
- ni traiter un étage intermédiaire comme la source première ;
- ni poursuivre un objet qui n’est pas réellement dérivé de la cause source.

Tu ne dois pas :
- proposer un objet sans dérivation explicite depuis la source ;
- proposer un objet sans lemme ;
- proposer un objet sans critère de réfutation ;
- recycler une route fermée sous un langage plus profond ;
- laisser l’autonomie dépasser ses STOP ou son budget.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : une carte hiérarchique complète source → mécanisme → symptôme est produite.
PASS-2 : le filtre anti-étage intermédiaire distingue clairement les faux niveaux ultimes.
PASS-3 : au plus 2 objets minimaux dérivés sont proposés.
PASS-4 : chaque objet dérivé a un lemme candidat et un critère de réfutation.
PASS-5 : une décision stratégique finale honnête est prise.
PASS-6 : un unique survivant pour R80 est sélectionné, ou l’innovation est suspendue proprement.

# ÉCHEC UTILE
Même en cas d’échec, R79 est utile si :
- il montre que nous n’avions pas encore atteint la racine ;
- il empêche une innovation future de naître d’un symptôme ;
- il réduit fortement l’espace des faux objets profonds ;
- il remplace un diagnostic “profond” flou par un diagnostic de niveau causal plus net.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats PHASE 1 / AXE A (requalification du cadre additif)
5. Résultats PHASE 1 / AXE B (requalification du cadre multiplicatif)
6. Résultats PHASE 1 / AXE C (autopsie de l’interface additif/multiplicatif)
7. Résultats PHASE 2 / AXE D (carte hiérarchique de causalité)
8. Résultats PHASE 2 / AXE E (test de racine réelle)
9. Résultats PHASE 3 / AXE F (objets minimaux dérivés)
10. Résultats PHASE 3 / AXE G (contrôle anti-régression)
11. Résultats PHASE 4 / AXE H (décision finale)
12. Activation ou non de l’autonomie, avec justification
13. Journal des sous-rounds autonomes éventuels
14. Objets concernés + Ladder of Proof
15. Ce qui est appris
16. Ce qui est fermé utilement
17. Ce qui est enterré
18. Autopsie des pistes fermées
19. Survivant pour R80
20. Risques / limites
21. Verdict final avec score /10
22. Registre FAIL-CLOSED

---

# CONSIGNE FINALE
R79 doit aller jusqu’à la racine de la racine avant d’innover à nouveau.

Le but n’est pas de trouver un meilleur outil parmi d’autres.
Le but est d’identifier la simplicité primitive qui, en s’additionnant, produit la complexité actuelle — puis de construire, si possible, un objet minimal directement issu de cette source.

Chercher une cause première, un objet dérivé minimal, et un test de réalité immédiat.
Pas une couche de plus. Pas un slogan de plus. Une descente jusqu’à la source.