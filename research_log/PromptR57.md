

TYPE: P
OBJET CIBLÉ: base-lite k=2 + max N_r + cross-lite bilinéaire
QUESTION CENTRALE: Peut-on faire monter l’architecture post-R56 d’un cran vers un premier schéma semi-prouvé utile, en verrouillant un lemme de base k=2 via une borne sur max N_r, tout en cadrant proprement la future route bilinéaire pour V_cross sans retomber dans des outils structurellement morts ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: identifier clairement si le prochain verrou réel est encore la base k=2 ou déjà le terme croisé V_cross, et enterrer proprement toute formulation trop optimiste avec autopsie complète.

# BRIEF CLAUDE CODE — ROUND 57 (R57)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R56.

### Contexte acquis
- R55 a montré que la machine inductive naïve n’existe pas sous forme universelle simple ; le vrai verrou est le terme croisé V_cross.
- R56 a confirmé l’architecture post-R55 :
  - **base k=2** comme pièce la plus proche d’un vrai lemme ;
  - **contrôle de V_cross** comme pièce plus difficile, nécessitant une vraie route bilinéaire / oscillatoire.
- R56 a aussi corrigé une surestimation précédente :
  - le claim A(2) ≤ 1.22 universel est FAUX ;
  - la bonne lecture distingue cas générique et cas dégénéré g ≡ −1 (mod p).
- R56 a prouvé un résultat dur :
  - cas dégénéré identifié et expliqué par l’effondrement de la diagonale P_(a,a)=0.
- Le gap sur la base k=2 est maintenant très concret :
  - il faut contrôler
    max_r N_r
  pour les solutions de
    2^a + g·2^b ≡ r (mod p)
  dans le régime R1.
- Le terme croisé reste actif, mais Cauchy-Schwarz est [RÉFUTÉ] comme outil suffisant ; la bonne route future est de type bilinéaire / cancellation de phases.
- Le risque stratégique est maintenant :
  - vouloir attaquer V_cross trop tôt alors que la base n’est pas encore verrouillée ;
  - ou au contraire fétichiser la base k=2 sans préparer le passage au cross.

## Objectif de R57
R57 doit répondre à cette question centrale :

> Peut-on transformer la base k=2 en premier lemme quasi-rigoureux utile, en ramenant tout le problème à une borne explicite sur max N_r, et en cadrant proprement la route bilinéaire future pour V_cross sans rouvrir d’outils déjà enterrés ?

R57 doit être un round proof-oriented très centré.
Pas de dispersion.
Pas de campagne computationnelle large.
Le but est de verrouiller la pièce la plus proche du théorème, puis de préparer lucidement la suivante.

---

# ARCHITECTURE GÉNÉRALE

## Pièce principale
**Base-lite k=2 via borne sur max N_r**

## Pièce secondaire cadrée mais non prioritaire
**Cross-lite via route bilinéaire**

Le round doit dire explicitement si, après R57, la base est enfin assez solide pour cesser d’être le verrou principal.

---

# AXE A — INVESTIGATEUR / BASE k=2 VIA max N_r
## Nom de travail
Peut-on fermer le gap de la base ?

## Mission
Étudier le problème de comptage

N_r = #{(a,b) : 2^a + g·2^b ≡ r mod p}

et déterminer si une borne utile sur max_r N_r peut être obtenue dans le régime R1, en distinguant proprement les cas générique et dégénéré.

### Questions obligatoires
1. Quelle est la reformulation canonique la plus exploitable de max N_r ?
   - via orbites de shift,
   - via collisions de paires (a,b),
   - via structure cyclique de 2 mod p,
   - via somme exponentielle ou autre,
   - autre
2. Quel est le meilleur découpage du problème ?
   - cas générique vs g ≡ −1,
   - orbites complètes vs bords,
   - autre
3. Peut-on obtenir une vraie borne rigoureuse, même grossière, sur max N_r ?
4. Quelle forme de borne serait déjà suffisante pour conclure un lemme de base utile ?
5. Quel est l’obstacle principal restant pour transformer cette base en lemme prouvable ?

### Livrables
- reformulation canonique de max N_r ;
- stratégie la plus crédible pour le cas générique ;
- stratégie la plus crédible pour le cas dégénéré ;
- meilleur lemme de base atteignable immédiatement.

---

# AXE B — INVESTIGATEUR / CADRAGE BILINÉAIRE POUR V_cross
## Nom de travail
Préparer le vrai outil du cross sans dériver

## Mission
Sans faire de V_cross la cible principale du round, formaliser la meilleure route future de type bilinéaire / oscillatoire, en explicitant pourquoi elle est différente des outils déjà enterrés.

### Questions obligatoires
1. Quelle est la reformulation bilinéaire la plus propre de V_cross ?
2. En quoi cette reformulation échappe-t-elle exactement à l’échec structurel de Cauchy-Schwarz ?
3. Quelles variables / phases semblent porter la cancellation ?
4. Quel serait le plus petit énoncé cross-lite utile à viser plus tard ?
5. Quel est le danger principal à attaquer cette pièce trop tôt ?

### Livrables
- une reformulation canonique de V_cross adaptée à une future route bilinéaire ;
- un mini-plan théorique crédible pour plus tard ;
- la liste explicite des outils morts à ne pas ressusciter.

---

# AXE C — INNOVATEUR / PREMIER NOYAU PROUVABLE POST-R56
## Nom de travail
Base-first ou cross-first ?

## Mission
Proposer au plus 2 formulations candidates d’un premier noyau de preuve réaliste après R56.

### Candidat 1
**Base-lite verrouillée**
Une borne explicite sur max N_r suffit à transformer k=2 en lemme quasi-rigoureux, ce qui retire définitivement la base de la liste des verrous actifs.

### Candidat 2
**Base suffisante + cross préparé**
La base n’a pas besoin d’être parfaite ; une version suffisamment propre, combinée à un cadrage bilinéaire précis du cross, est déjà le meilleur schéma de progression pour R58.

### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait immédiatement ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle ;
6. niveau estimé dans la Ladder of Proof.

## Règle obligatoire
À la fin :
- garder un seul survivant pour R58 ;
- éliminer l’autre explicitement ;
- justifier le choix par démontrabilité réelle, pas par élégance.

---

# CONTRÔLE SECONDAIRE OPTIONNEL
Un seul micro-test ciblé est autorisé si et seulement s’il aide à :
- départager cas générique vs dégénéré dans la base k=2, ou
- vérifier qu’une reformulation bilinéaire du cross est bien distincte des outils déjà enterrés.
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
- relancer une pseudo-récurrence universelle déjà enterrée ;
- faire de V_cross la cible principale du round ;
- lancer une campagne computationnelle large ;
- présenter la base k=2 comme déjà prouvée tant que max N_r n’est pas verrouillé.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : une reformulation exploitable de max N_r est isolée.
PASS-2 : un meilleur lemme de base k=2 est formulé.
PASS-3 : la route bilinéaire future pour V_cross est cadrée proprement sans résurrection d’outils morts.
PASS-4 : au moins une formulation trop optimiste est éliminée avec autopsie complète.
PASS-5 : un survivant unique pour R58 est sélectionné.

# ÉCHEC UTILE
Même en cas d’échec, R57 est utile si :
- le vrai gap de la base k=2 est mieux localisé ;
- la route bilinéaire future est clarifiée ;
- une formulation trop ambitieuse de la base ou du cross est éliminée proprement.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats AXE A (base k=2)
5. Résultats AXE B (cadrage cross)
6. Résultats AXE C (arbitrage)
7. Contrôle secondaire éventuel
8. CEC inchangé
9. Objets concernés + Ladder of Proof
10. Ce qui est appris
11. Ce qui est enterré
12. Autopsie des pistes fermées
13. Survivant pour R58
14. Risques / limites
15. Verdict final avec score /10

---

# CONSIGNE FINALE
R57 doit verrouiller la pièce la plus proche d’un vrai lemme sans perdre de vue la suivante.
Le but n’est pas de tout résoudre à la fois.
Le but est de transformer la base k=2 en pièce quasi-rigoureuse, puis de préparer lucidement le cross.
Chercher la prochaine pièce prouvable, pas la théorie finale complète.