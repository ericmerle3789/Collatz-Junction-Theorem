# PROTOCOLE INTÉGRAL DE RECHERCHE — CAMPAGNES COLLATZ / JUNCTION THEOREM

## 0. Esprit général

Ce protocole repose sur une idée simple :

> Un mur n’est pas une preuve d’impossibilité. C’est un signal qu’il faut mieux localiser le verrou, mieux distinguer les faux verrous, et fabriquer l’outil adapté plutôt qu’insister avec les mauvais outils.

Le programme ne doit donc jamais confondre :
- difficulté actuelle,
- impossibilité mathématique,
- plafond d’une famille d’outils,
- et clôture du problème.

La méthode générale est la suivante :
1. **comprendre avant d’innover** ;
2. **innover sous contrainte** ;
3. **auditer avant de croire** ;
4. **enterrer proprement les fausses pistes** ;
5. **ne garder qu’un survivant réel** ;
6. **mettre à jour la carte des morts, des survivants et des verrous**.

---

# 1. Cible réelle du programme

La cible logique du programme n’est pas :
- un joli proxy,
- un indicateur expérimental,
- un laboratoire local,
- un cas particulier séduisant,
- ni une reformulation esthétique.

La cible réelle est le progrès vers :

> **N_0(d) = 0**

ou toute chaîne rigoureuse qui rapproche réellement de ce verrou, sans confusion entre :
- **cible**,
- **outil**,
- **laboratoire**,
- **proxy**,
- **heuristique**.

## Doctrine cible / outil / laboratoire
- **Cible** : ce qui est directement relié au verrou mathématique central.
- **Outil** : ce qui aide à regarder, reformuler, filtrer, réduire, mais n’est pas la cible.
- **Laboratoire** : ce qui est utile pour apprendre, tester, falsifier, mais ne porte pas la conclusion finale.

### Règle absolue
Aucun round ne doit traiter un **laboratoire** comme s’il était la **cible**.
Aucun round ne doit traiter un **outil** comme s’il était une **preuve**.

---

# 2. Les grandes interdictions méthodologiques

## 2.1 Anti-computationnel
Le computationnel n’est pas interdit absolument, mais il est **strictement borné**.

### Autorisé uniquement si :
- il ferme un résidu explicitement identifié ;
- il sert de **certification locale** ou de **sonde secondaire de cohérence** ;
- il est reproductible, archivé, journalisé et auditable.

### Interdit si :
- il remplace la pensée théorique ;
- il devient le moteur principal du round sans justification programmatique ;
- il sert à accumuler des cas sans gain conceptuel ;
- il dérive en scan libre ou en force brute.

## 2.2 Anti-k-par-k
Les petits k et cas particuliers ne doivent **jamais** devenir la colonne vertébrale théorique.

### Autorisé uniquement si :
- test local de cohérence ;
- exemple pédagogique ;
- validation secondaire d’un mécanisme général déjà formulé.

### Interdit si :
- le raisonnement dépend structurellement des petits k ;
- le round devient une montée k=3,5,7,… ;
- une propriété observée est présentée comme mécanisme général.

## 2.3 Anti-rebranding
Toute idée nouvelle doit être comparée à la carte mentale / Research Map et à l’historique complet.

### Une idée est éliminée si :
- elle reformule une voie morte sans différence mathématique réelle ;
- elle remplace un ancien objet par un nouveau nom seulement ;
- elle rejoue un vieux mécanisme avec une rhétorique plus profonde ;
- elle change de décor sans changer de levier.

## 2.4 Anti-prose
Aucun candidat ne doit survivre sur la base de :
- profondeur apparente,
- beauté formelle,
- prestige bibliographique,
- intuition séduisante,
- ou promesse vague.

### Règle absolue
Pas d’idée sans objet.
Pas d’objet sans lemme candidat.
Pas de lemme sans critère de réfutation.
Pas de survivant sans audit croisé.

## 2.5 Anti-régression
Toute voie déjà enterrée doit être traitée comme morte tant qu’une différence mathématique réelle n’est pas explicitement démontrée.

---

# 3. Méthode standard d’un round

Chaque round doit suivre, autant que possible, la séquence suivante :

1. **Rappeler le verrou actif**
2. **Rappeler ce qui est déjà mort**
3. **Rappeler ce qui est déjà acquis**
4. **Formuler le manque concret du round**
5. **Construire peu de candidats**
6. **Les faire auditer**
7. **Tuer rapidement les faux candidats**
8. **Garder un survivant unique ou suspendre honnêtement**
9. **Mettre à jour la carte des morts, survivants et verrous**

### Un round réussi n’est pas forcément un round “positif”
Un round peut être très bon s’il :
- ferme proprement une voie ;
- réduit l’espace des illusions ;
- localise plus précisément le verrou ;
- remplace un faux progrès par un diagnostic net.

---

# 4. Structure des agents

## 4.1 Investigateur causal
Mission : comprendre **pourquoi** ça bloque.

Il doit remonter la chaîne causale :
- symptôme,
- mécanisme local,
- cause source,
- faux coupables,
- condition manquante.

### Questions typiques
- Où le raisonnement casse-t-il exactement ?
- Le blocage est-il structurel ou contingent ?
- Quel ingrédient manque ?
- Est-ce un vrai verrou ou un faux verrou ?
- Quelle couche du problème est cause, et quelle couche est symptôme ?

## 4.2 Investigateur historique
Mission : empêcher toute résurrection des morts.

### Questions typiques
- À quelle ancienne voie cette piste ressemble-t-elle ?
- La différence est-elle réelle ou lexicale ?
- Quelle branche morte est en train de revenir masquée ?
- Quel test rapide de non-redondance appliquer ?

## 4.3 Innovateur discipliné
Mission : construire **peu**, mais construire **utile**.

### Règle absolue
L’innovateur ne propose jamais d’objet “pour voir”.
Chaque objet doit venir d’un **manque concret clairement identifié**.

### Tout objet proposé doit fournir immédiatement :
- définition ou schéma semi-formel ;
- lemme candidat ;
- critère de réfutation ;
- rôle logique ;
- raison d’entrer en tournoi.

## 4.4 Auditeur fail-closed
Mission : tuer les illusions.

Il doit imposer des statuts explicites et empêcher tout gonflement abusif.

### Il peut tuer un candidat si :
- l’objet est flou ;
- le lemme est trop haut, trop faible ou trop local ;
- la preuve est absente ;
- la non-redondance est perdue ;
- le lien au verrou devient rhétorique ;
- le candidat survit par prestige ou profondeur apparente.

## 4.5 Vérificateur de preuve
Mission : classer honnêtement le statut mathématique.

### Statuts autorisés
- [HEURISTIQUE]
- [SEMI-FORMALISÉ]
- [PARTIELLEMENT PROUVÉ]
- [PROUVÉ]
- [BLOQUÉ]
- [RÉFUTÉ]

### Règle absolue
Ne jamais appeler “prouvé” ce qui n’est que :
- plausible,
- cadré,
- semi-formalisé,
- ou validé sur un sous-cas.

## 4.6 Arbitre de tournoi
Mission : organiser la compétition entre candidats.

Il impose :
- critères de victoire ;
- critères d’élimination ;
- comparaison locale ;
- élimination stricte ;
- survivant unique ou suspension.

## 4.7 Synthétiseur structurel
Mission : relier les résultats du round au programme global.

Il distingue :
- progrès local,
- progrès structurel,
- progrès de preuve,
- élégance trompeuse,
- et blocage préparatoire.

---

# 5. Binômes recommandés

## Binôme A — Investigateur + Innovateur sur le survivant courant
- comprendre le verrou précis du survivant ;
- proposer des raffinements utiles ;
- éviter les faux gains.

## Binôme B — Investigateur + Innovateur sur le verrou résiduel
- disséquer la conditionnalité ;
- proposer des objets minimaux de déverrouillage ;
- tester si un sous-verrou plus fondamental existe.

## Variante en cas de campagne mixte
Si un axe computationnel méthodique de fermeture locale est maintenu :
- **Binôme Gap** : Investigateur Gap + Innovateur Gap,
- **Binôme Théorie** : Investigateur Théorie + Innovateur Théorie,
- avec comparaison explicite des deux axes.

---

# 6. Formats obligatoires

## 6.1 Format minimal d’un candidat recevable
Un candidat n’est recevable que si la chaîne suivante est explicite :

**verrou actif → manque concret → objet précis → lemme candidat → critère de réfutation → critère de victoire**

## 6.2 Format obligatoire d’un round
1. Résumé exécutif
2. Verrou actif
3. Axes actifs
4. Candidats actifs
5. Travail des agents / binômes
6. Résultats nets
7. Candidats éliminés et pourquoi
8. Candidats survivants et pourquoi
9. Statut de preuve / statut de conditionnalité
10. Checkpoint final
11. Décision : continuer / arrêter / bilan

## 6.3 Checkpoint obligatoire à la fin de chaque round
Claude Code doit répondre explicitement :
1. Quel axe a réellement progressé ?
2. Quel candidat a gagné en mordant ?
3. Quel candidat a gagné en statut de preuve ?
4. Quel candidat a perdu sa non-redondance ?
5. Quel candidat doit être tué maintenant ?
6. Pourquoi un round supplémentaire est-il justifié ?

Si ces réponses ne sont pas nettes, il faut stopper la campagne.

---

# 7. Pipeline fermé d’autonomie

L’autonomie est autorisée, mais uniquement en **pipeline fermé**.

## Principe
Plus l’autonomie augmente, plus les contrôles augmentent.

## Structure standard
Chaque round autonome peut contenir au maximum :
- 1 phase de qualification,
- 1 phase de poussée,
- 1 phase d’audit croisé,
- 1 phase de vérification de preuve,
- 1 synthèse courte.

Pas de dérive en branches illimitées.
Pas de safari théorique.
Pas d’exploration sans checkpoints.

## Événements STOP immédiats
Arrêt d’un candidat ou d’un round si :
1. retour au computationnel libre ;
2. retour au k-par-k théorique ;
3. rebranding d’une voie morte ;
4. disparition du lemme candidat ;
5. disparition du critère de réfutation ;
6. stagnation du statut de preuve sur plusieurs rounds ;
7. lien au verrou devenu rhétorique.

---

# 8. Registre fail-closed

Statuts autorisés à utiliser systématiquement :
- [QUALIFIÉ]
- [QUALIFIÉ AVEC RÉSERVE]
- [ÉLIMINÉ]
- [OBJET RÉEL]
- [SEMI-RÉEL]
- [REDONDANT]
- [FAUX EXTÉRIEUR]
- [SEMI-FORMALISÉ]
- [PARTIELLEMENT PROUVÉ]
- [HEURISTIQUE]
- [PROSE]
- [RÉFUTÉ]
- [BLOQUÉ]
- [À REFORMULER]
- [DIAGNOSTIC INSUFFISANT]

### Règle absolue
Le statut le plus fort ne doit jamais être attribué par optimisme.
Il doit être **mérité** par le contenu mathématique réel.

---

# 9. Comment traiter un “mur”

Quand un mur apparaît, il faut appliquer la séquence suivante :

1. **Nommer le mur** proprement
2. **Dire ce qu’il empêche exactement**
3. **Distinguer symptôme, mécanisme intermédiaire, cause source**
4. **Vérifier si le mur est déjà connu sous un autre nom**
5. **Tester si le mur est fondamental ou local aux outils actuels**
6. **Décider s’il faut :**
   - le contourner,
   - le factoriser,
   - fabriquer un sous-lemme préparatoire,
   - ou suspendre la piste

### Règle absolue
Un mur ne signifie jamais automatiquement “impossible”.
Il signifie seulement :
- “avec cet outillage, ça ne mord pas encore”.

---

# 10. Ce qu’un résultat inconditionnel change — et ne change pas

Un résultat inconditionnel intermédiaire peut :
- fermer une famille de cas ;
- réduire le front ;
- stabiliser un cadre exact ;
- produire un filtre réel ;
- clarifier le mur restant.

Mais il ne résout pas automatiquement :
- les cas résiduels ;
- le passage moyen → pointwise ;
- la preuve uniforme finale ;
- ni l’objectif global.

### Règle absolue
Toujours demander :
> Ce résultat inconditionnel ferme-t-il le verrou principal, ou seulement un étage du verrou ?

---

# 11. Quand prolonger une campagne

Une campagne peut être prolongée seulement si :
1. un survivant reste [QUALIFIÉ] ou [QUALIFIÉ AVEC RÉSERVE] ;
2. son statut de preuve a progressé ;
3. il n’est ni redondant ni rhétorique ;
4. l’objectif du round suivant est mathématiquement précis ;
5. l’auditeur fail-closed valide la poursuite ;
6. une condition explicite de non-boucle est écrite.

Sinon : arrêt et bilan final.

---

# 12. Condition de non-boucle

Toute suite de rounds doit expliciter :
- ce qui est désormais considéré comme acquis ;
- ce qui est enterré définitivement ;
- ce qui reste vivant ;
- ce qui serait un signe clair de redondance ;
- ce qui rend le round suivant légitime.

Sans cela, il y a risque de tourner en rond avec des noms nouveaux pour de vieux objets.

---

# 13. En résumé : ce qu’il faut dire à Claude Code

Tu ne dois pas :
- raconter une percée ;
- survivre par rhétorique ;
- rouvrir les morts ;
- te reposer sur le computationnel libre ;
- t’appuyer sur les petits k ;
- appeler “preuve” ce qui ne l’est pas.

Tu dois :
- partir du verrou actif réel ;
- construire peu de candidats ;
- les faire auditer durement ;
- les comparer ;
- en tuer la plupart ;
- garder un survivant réel ou suspendre honnêtement.

---

# 14. Conclusion opérationnelle

Le programme a déjà montré qu’un mur pouvait être entamé, déplacé, factorisé, puis parfois franchi partiellement.
La bonne attitude n’est donc ni le découragement, ni l’emballement.

La bonne attitude est :
- **lucidité sur le verrou actif**,
- **créativité sous contrainte**,
- **preuves classées honnêtement**,
- **morts bien enterrées**,
- **un seul survivant réel à la fois**.

Si un nouvel outil doit apparaître, il apparaîtra plus sûrement de cette discipline que d’une liberté sans garde-fous.