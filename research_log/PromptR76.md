

TYPE: X/P
OBJET CIBLÉ: autopsier causalement les mécanismes bloquants rencontrés sur la voie SAMC afin d’identifier, de façon générale et non computationnelle, où la compression du verrou échoue, pourquoi elle échoue, et quel type exact d’objet ou de mécanisme manque encore
QUESTION CENTRALE: quels sont les mécanismes bloquants profonds qui font échouer GSE, ALO et RP sur Σ≤(k), et que nous apprennent-ils sur la forme précise de l’innovation encore manquante ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: produire une cartographie causale fiable des blocages, avec chaîne explicative complète, points de rupture localisés, faux remèdes éliminés, et un unique besoin conceptuel survivant pour la suite.
PRINCIPE D’ÉQUILIBRE: avancer à petits pas, mais des pas sûrs ; interdire toute clôture prématurée, tout computationnel, tout k-par-k, toute pseudo-explication vague, et exiger des diagnostics causaux remontant jusqu’au mécanisme source, comme un investigateur technique qui remonte une panne jusqu’au disjoncteur plutôt que de s’arrêter au symptôme.

# BRIEF CLAUDE CODE — ROUND 76 (R76)

## Mission
Tu poursuis le projet Collatz après R75.

R76 n’est **pas** un round de consolidation finale.
R76 n’est **pas** un round de nouveaux jolis concepts en roue libre.
R76 n’est **pas** un round de tests locaux, ni de k-par-k, ni de computationnel.

R76 est un round d’**investigation causale profonde**.

Son but est simple et sévère :

> **comprendre précisément pourquoi les mécanismes testés sur la voie SAMC échouent, où ils échouent, ce qui manque exactement, et quel besoin conceptuel réel reste vivant après autopsie.**

Autrement dit :
- ne pas seulement constater “ça bloque” ;
- ne pas seulement dire “outil insuffisant” ;
- mais remonter la chaîne causale complète du blocage jusqu’au mécanisme source.

Comme pour une panne technique :
- le PC ne démarre pas ;
- on vérifie l’alimentation ;
- puis l’entrée secteur ;
- puis la prise ;
- puis le disjoncteur ;
- puis la raison de son déclenchement.

**R76 doit faire cela mathématiquement.**

---

## Contexte acquis après R75
- Les voies analytiques standards sur le régime court ont été déclassées.
- La reformulation SAMC a été reconnue comme une innovation structurelle sérieuse, mais sa capacité réelle de compression reste non démontrée.
- Trois mécanismes ont été testés en R75 :
  - GSE,
  - ALO,
  - RP.
- Le bilan R75 conclut qu’aucun de ces trois mécanismes ne fournit à ce stade un mécanisme général crédible d’exclusion de -1 dans Σ≤(k).
- L’audit de R75 accepte globalement ce tri, mais critique fortement sa conclusion trop terminale.
- Ce qui manque encore n’est pas seulement “une autre idée” ;
  c’est une **compréhension causale du blocage** :
  - pourquoi GSE est structurellement trop faible,
  - où ALO devient circulaire,
  - pourquoi RP reste local déguisé,
  - quel trait de F_p, de la monotonie, des poids λ^j, ou de la réduction modulo p empêche la fermeture.
- Sans cette compréhension, toute innovation future risque soit :
  - de refaire la même chose sous un autre nom,
  - soit de partir dans la prose.

---

# OBJECTIF DE R76
R76 doit répondre à cette question centrale :

> Quelle est la chaîne causale exacte des blocages rencontrés sur la voie SAMC, et quel besoin conceptuel unique survit après autopsie complète de ces blocages ?

Les sorties acceptables du round sont :
1. **Les blocages sont autopsiés proprement, et un besoin conceptuel unique est isolé** ;
2. **Les blocages sont partiellement autopsiés, avec 2 besoins conceptuels concurrents mais clairement bornés** ;
3. **L’autopsie montre qu’un blocage supposé profond n’était qu’un faux verrou** ;
4. **L’autopsie reste insuffisante : le round doit être déclaré non concluant plutôt que rhétoriquement fermé**.

Important :
- aucune sortie n’est recevable si elle se contente de dire “outil trop faible” sans expliquer pourquoi ;
- aucune sortie n’est recevable si elle conclut “impossible” ou “frontière des mathématiques” sans chaîne causale précise ;
- aucune sortie n’est recevable si elle repose sur des cas, du calcul, ou de petites valeurs de k ;
- aucune sortie n’est recevable si elle produit plus de questions nouvelles qu’elle ne clarifie de mécanismes.

---

# ARCHITECTURE GÉNÉRALE

## PHASE 1 — AUTOPSIE CAUSALE DES MÉCANISMES TESTÉS
Objectif : comprendre exactement pourquoi GSE, ALO et RP ne ferment pas le verrou.

## PHASE 2 — LOCALISATION DU MÉCANISME SOURCE
Objectif : déterminer si le blocage provient de l’objet Σ≤(k), du corps F_p, de la monotonie, des poids, de la réduction modulo p, ou d’une interaction entre ces éléments.

## PHASE 3 — FILTRE ANTI-FAUX-VERROU
Objectif : distinguer blocage profond, blocage contingent, et faux problème.

## PHASE 4 — BESOIN CONCEPTUEL SURVIVANT
Objectif : extraire un seul besoin conceptuel ou, au maximum, deux besoins clairement distincts et bornés pour guider l’innovation suivante.

## Ce qui est interdit comme cible principale
- toute innovation libre non précédée par l’autopsie ;
- tout computationnel ;
- tout k-par-k ;
- tout test par accumulation de cas ;
- tout verdict terminal de type “impossible”, “frontière atteinte”, “consolidons” sans autopsie causale ;
- toute nouvelle théorie non reliée à un mécanisme bloquant clairement identifié.

---

# PHASE 1 — AUTOPSIE CAUSALE DES MÉCANISMES TESTÉS

## AXE A — INVESTIGATEUR PARALLÈLE 1 / AUTOPSIE DE GSE
### Nom de travail
Pourquoi la taille ne devient-elle pas du contenu ?

### Mission
Ne pas se contenter de dire que GSE est “trop faible”.
Il faut expliquer **pourquoi** une information de cardinalité / sparsité ne se convertit pas ici en information ciblée sur -1.

### Questions obligatoires
1. Quel est exactement le type d’information que GSE contrôle ?
2. Quel type d’information manque pour parler spécifiquement de -1 ?
3. La perte vient-elle de l’absence de localisation additive, de la structure de F_p, de la réduction modulo p, ou d’un autre point ?
4. Quel serait l’axiome ou l’invariant supplémentaire qui aurait rendu GSE utile ?
5. Le défaut de GSE est-il accidentel ou structurel ?

### Livrables
- chaîne causale complète du blocage de GSE ;
- diagnostic : [ACCIDENTEL] / [STRUCTUREL] ;
- type exact d’information manquante.

---

## AXE B — INVESTIGATEUR PARALLÈLE 2 / AUTOPSIE DE ALO
### Nom de travail
Où la circularité démarre-t-elle vraiment ?

### Mission
Identifier précisément où ALO devient circulaire, et quel mécanisme mathématique force cette circularité.

### Questions obligatoires
1. À quel moment exact le passage harmonique/Fourier retransforme-t-il le problème au lieu de le réduire ?
2. La circularité vient-elle du support 2^g, de la monotonie, des poids λ^j, ou du corps fini lui-même ?
3. Existe-t-il une forme d’anti-concentration non harmonique qui aurait évité cette boucle ?
4. Le défaut de ALO porte-t-il sur l’outil, sur l’objet, ou sur leur mauvais appariement ?
5. Quelle propriété précise devrait posséder un substitut d’ALO pour ne pas retomber dans la circularité ?

### Livrables
- carte de circularité d’ALO ;
- point exact de rupture ;
- propriété minimale requise pour éviter cette boucle.

---

## AXE C — INVESTIGATEUR PARALLÈLE 3 / AUTOPSIE DE RP
### Nom de travail
Pourquoi la récurrence ne se ferme-t-elle pas ?

### Mission
Comprendre pourquoi RP reste locale et ne se ferme pas uniformément.

### Questions obligatoires
1. Quelle information RP transmet-elle réellement d’un niveau à l’autre ?
2. Pourquoi cette information n’est-elle pas stable uniformément en k ?
3. La dépendance locale est-elle intrinsèque, ou due à un mauvais choix d’état/invariant ?
4. Quel invariant aurait été nécessaire pour fermer la récurrence ?
5. Le défaut de RP est-il un défaut de méthode ou un symptôme d’un blocage plus profond ?

### Livrables
- chaîne causale du non-fermeture ;
- invariant manquant ;
- diagnostic : [MÉTHODE MAL CHOISIE] / [BLOCAGE PLUS PROFOND].

---

# PHASE 2 — LOCALISATION DU MÉCANISME SOURCE

## AXE D — INVESTIGATEUR SYNTHÈSE / OÙ LE BLOCAGE PREND-IL NAISSANCE ?
### Nom de travail
Quel composant du système met le disjoncteur en défaut ?

### Mission
Fusionner les autopsies de GSE, ALO et RP pour localiser le mécanisme source du blocage.

### Dimensions à examiner explicitement
- géométrie de Σ≤(k) ;
- monotonie des g_j ;
- hétérogénéité des poids λ^j ;
- réduction modulo p ;
- absence de sous-groupes additifs utiles dans F_p ;
- perte d’ordre après réduction ;
- interaction additif/multiplicatif ;
- échelle logarithmique du support.

### Questions obligatoires
1. Quel composant est source du blocage principal ?
2. Quels composants sont seulement aggravants ?
3. Y a-t-il un couplage de deux causes plutôt qu’une cause unique ?
4. Quel faux coupable faut-il explicitement innocenté ?
5. Peut-on résumer le mécanisme source en une phrase mathématique précise ?

### Livrables
- carte causale globale du blocage ;
- composante source ;
- composantes secondaires ;
- faux verrou explicitement innocenté.

---

# PHASE 3 — FILTRE ANTI-FAUX-VERROU

## AXE E — AUDITEUR FAIL-CLOSED / BLOCAGE PROFOND OU MAUVAISE FORMULATION ?
### Nom de travail
Le mur est-il réel, ou regarde-t-on au mauvais endroit ?

### Mission
Vérifier si les blocages détectés sont :
- réellement profonds,
- seulement contingents,
- ou créés par une formulation encore inadaptée.

### Questions obligatoires
1. Quel blocage est prouvé profond ?
2. Quel blocage est seulement plausible ?
3. Quel blocage disparaîtrait si l’on changeait de niveau intermédiaire de structure ?
4. Y a-t-il un faux verrou que R75 avait traité comme terminal alors qu’il est seulement local ?
5. L’autopsie réduit-elle réellement l’espace des innovations futures ?

### Livrables
Pour chaque blocage identifié :
- statut : [PROFOND] / [CONTINGENT] / [LIÉ À LA FORMULATION] / [FAUX VERROU] ;
- justification ;
- conséquence pour la suite.

---

# PHASE 4 — BESOIN CONCEPTUEL SURVIVANT

## AXE F — INVESTIGATEUR + INNOVATEUR SOUS CONTRAINTE / QU’EST-CE QUI MANQUE EXACTEMENT ?
### Nom de travail
Quel outil devrait exister pour que le courant repasse ?

### Mission
À partir de l’autopsie, extraire le besoin conceptuel exact. Pas encore une théorie complète ; juste le type d’objet ou de mécanisme dont l’absence explique l’échec actuel.

### Formes acceptables de besoin conceptuel
- un invariant manquant ;
- une notion de rigidité manquante ;
- une décomposition absente ;
- une notion de localisation ciblée ;
- un couplage additif/multiplicatif mieux adapté ;
- un espace intermédiaire ou une pseudo-norme absente ;
- une structure d’ordre compatible qui manque après réduction.

### Questions obligatoires
1. Quel besoin conceptuel unique expliquerait le mieux les trois échecs ?
2. Si deux besoins subsistent, sont-ils vraiment indépendants ?
3. Ce besoin est-il formulable sans repartir dans la prose ?
4. Quel premier objet pourrait incarner ce besoin dans un round futur ?
5. Quel besoin apparent faut-il refuser comme trop vague ?

### Livrables
- besoin conceptuel survivant ;
- formulation minimale ;
- premier objet possible pour le round suivant ;
- faux besoins enterrés.

---

# AGENTS ET RÔLES

## Investigateur parallèle 1
- autopsie GSE ;
- remonte la chaîne causale ;
- identifie l’information manquante.

## Investigateur parallèle 2
- autopsie ALO ;
- localise la circularité ;
- identifie la propriété minimale non circulaire qui manquerait.

## Investigateur parallèle 3
- autopsie RP ;
- identifie l’invariant manquant pour la fermeture ;
- distingue défaut de méthode et blocage profond.

## Investigateur synthèse
- fusionne les trois autopsies ;
- localise le mécanisme source ;
- identifie les faux coupables.

## Innovateur sous contrainte
- n’invente pas librement ;
- formule seulement le besoin conceptuel survivant ;
- n’a pas le droit de proposer plus d’un premier objet possible pour la suite.

## Auditeur fail-closed
- interdit tout diagnostic vague ;
- exige une chaîne causale ;
- refuse toute conclusion terminale sans mécanisme source identifié.

---

# AUTONOMIE CONTRÔLÉE (COURTE ET SUR RAILS)

## Activation
Une mini-autonomie est autorisée seulement entre la PHASE 2 et la PHASE 4 pour fusionner les diagnostics causaux, jamais pour explorer librement de nouvelles théories.

## Budget maximal
Au plus **3 sous-rounds internes** :
- **S1** : fusion des autopsies GSE/ALO/RP ;
- **S2** : tri blocage profond / contingent / faux verrou ;
- **S3** : extraction du besoin conceptuel survivant.

## Événements STOP obligatoires
Arrêt immédiat si :
1. le raisonnement dérive vers du computationnel ;
2. le raisonnement dérive vers des cas particuliers ;
3. une conclusion “impossible / frontière” apparaît sans chaîne causale complète ;
4. plus de deux besoins conceptuels survivent ;
5. le vocabulaire devient plus riche que l’explication causale ;
6. aucune cause source n’est localisée.

## Format obligatoire de chaque sous-round autonome
1. hypothèse causale active ;
2. mécanisme étudié ;
3. question précise ;
4. chaîne de remontée ;
5. résultat net ;
6. statut ;
7. ce qui est appris ;
8. décision : continuer / arrêter ;
9. raison explicite.

## Interdictions
- pas de calcul ;
- pas de Monte Carlo ;
- pas de k-par-k ;
- pas de nouveau grand cadre théorique ;
- pas d’enterrement terminal sans autopsie complète.

---

# REGISTRE MÉTHODOLOGIQUE OBLIGATOIRE

## 1. Type du round
Rappeler explicitement : **X/P**
- **X** pour investigation causale ;
- **P** pour exigence de précision, preuve partielle, et testabilité des diagnostics.

## 2. IVS — Information Value Score
Noter /10 selon :
- profondeur de l’autopsie ;
- clarté de la cause source ;
- réduction réelle de l’espace des fausses innovations ;
- qualité du besoin conceptuel survivant ;
- honnêteté des distinctions profond / contingent / faux verrou.

Une bonne note IVS peut venir d’un diagnostic causal très net, même sans nouvel objet encore construit.

## 3. Ladder of Proof
Pour chaque diagnostic causal, préciser :
- intuition ;
- symptôme ;
- mécanisme local ;
- chaîne causale ;
- diagnostic stable ;
- conséquence programmatique.

## 4. AUTOPSIE DES PISTES FERMÉES (OBLIGATOIRE)
Pour chaque mécanisme bloquant ou faux remède, fournir :
- Nom ;
- Type de mort :
  - trop faible structurellement,
  - circulaire,
  - local déguisé,
  - faux verrou,
  - formulation inadéquate,
  - composante aggravante seulement ;
- Cause source ;
- Ce que la mort enseigne ;
- Où cela redirige.

## 5. REGISTRE FAIL-CLOSED
Tu dois terminer par un tableau strict :
- [PROUVÉ]
- [PARTIELLEMENT PROUVÉ]
- [SEMI-FORMALISÉ]
- [FORTEMENT ÉTAYÉ]
- [HEURISTIQUE]
- [CONTINGENT]
- [FAUX VERROU]
- [RÉFUTÉ]
- [À REFORMULER]
- [DIAGNOSTIC INSUFFISANT]

---

# CONTRAINTES MÉTHODOLOGIQUES
Tu dois distinguer explicitement :
- symptôme ;
- mécanisme local ;
- cause source ;
- faux coupable ;
- besoin conceptuel ;
- statut.

Tu dois favoriser les formulations minimales suffisantes :
- ni conclure trop vite ;
- ni noyer l’autopsie dans le vocabulaire ;
- ni inventer avant d’avoir compris ;
- ni traiter un blocage contingent comme un mur fondamental ;
- ni sous-estimer une vraie cause structurelle profonde.

Tu ne dois pas :
- dire seulement “outil trop faible” ;
- dire seulement “c’est ouvert” ;
- dire seulement “c’est impossible” ;
- proposer un round suivant sans cause source identifiée ;
- laisser l’autonomie dépasser ses STOP ou son budget.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : GSE, ALO et RP sont autopsiés causalement, pas seulement évalués.
PASS-2 : une carte causale globale du blocage est produite.
PASS-3 : au moins un faux verrou est explicitement innocenté ou déclassé.
PASS-4 : le besoin conceptuel survivant est formulé proprement.
PASS-5 : un unique survivant programmatique pour R77 est sélectionné, ou au maximum deux besoins clairement bornés.
PASS-6 : aucune dérive computationnelle, locale ou terminale n’a contaminé le round.

# ÉCHEC UTILE
Même en cas d’échec, R76 est utile si :
- il montre qu’on ne comprenait pas encore assez bien le blocage ;
- il réduit l’espace des diagnostics faux ;
- il empêche une innovation future de partir dans la mauvaise direction ;
- il remplace un “ça bloque” par un “voici exactement pourquoi ça bloque”.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats PHASE 1 / AXE A (autopsie GSE)
5. Résultats PHASE 1 / AXE B (autopsie ALO)
6. Résultats PHASE 1 / AXE C (autopsie RP)
7. Résultats PHASE 2 / AXE D (mécanisme source)
8. Résultats PHASE 3 / AXE E (tri profond / contingent / faux verrou)
9. Résultats PHASE 4 / AXE F (besoin conceptuel survivant)
10. Activation ou non de l’autonomie, avec justification
11. Journal des sous-rounds autonomes éventuels
12. Objets concernés + Ladder of Proof
13. Ce qui est appris
14. Ce qui est fermé utilement
15. Ce qui est enterré
16. Autopsie des pistes fermées
17. Survivant pour R77
18. Risques / limites
19. Verdict final avec score /10
20. Registre FAIL-CLOSED

---

# CONSIGNE FINALE
R76 doit comprendre avant d’inventer à nouveau.

Le but n’est pas de trouver immédiatement la prochaine théorie brillante.
Le but est d’identifier où le courant se coupe, pourquoi il se coupe, et quel composant manque pour que le système puisse enfin fonctionner.

Chercher une cause source, un faux verrou, et un besoin conceptuel net.
Pas une clôture. Pas une fuite. Une autopsie mathématique utile.