TYPE: P
OBJET CIBLÉ: TQL (Tail Quasi-uniformity Lemma) + Z-lite via phase shift
QUESTION CENTRALE: Peut-on faire monter TQL d’un cran, de cible structurelle unificatrice vers premier lemme semi-formalisé utile, dans un sous-régime naturel où les distributions tail N^{tail}_{b0,r} sont suffisamment proches de l’uniforme pour contrôler Z puis V_between ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: identifier la meilleure version prouvable de TQL-lite, et enterrer proprement toute formulation trop forte ou mal ciblée avec autopsie complète.

# BRIEF CLAUDE CODE — ROUND 51 (R51)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R50.

### Contexte acquis
- R48 a reformulé SDL comme **ANOVA exacte**.
- R49 a montré que la moitié **between** de ACaL est plus attaquable que la moitié within.
- R50 a produit la percée structurelle suivante :
  - **phase shift reformulation**
  - Z_{b0,b0'} = excès de collisions inter-tranches vu comme cross-corrélation décalée de distributions tail
  - la bonne cible n’est pas ρ-lite direct, mais **Z-lite via phase shift**
- R50 a fortement suggéré une réunification :
  - **between** et **within** semblent gouvernés par le même mécanisme de quasi-uniformité des tails
- Le survivant naturel est désormais :
  - **TQL = Tail Quasi-uniformity Lemma**
- Le risque stratégique est maintenant :
  - viser TQL trop fort trop tôt,
  - ou retomber dans une reformulation descriptive sans levier démontrable.

## Objectif de R51
R51 doit répondre à cette question centrale :

> Peut-on formuler et défendre une première version prouvable de TQL-lite dans un sous-régime naturel, suffisamment forte pour contrôler Z-lite via phase shift, et donc faire monter une partie réelle de ACaL ?

R51 doit être un round proof-oriented centré.
Pas de dispersion.
Pas de campagne computationnelle large.
Le but est de transformer TQL d’idée unificatrice en premier levier de preuve utilisable.

---

# ARCHITECTURE GÉNÉRALE

## Route unique
**TQL** est l’unique route principale de R51.

## Deux sous-axes concurrents à départager
- **Sous-axe A** : TQL-lite par quasi-uniformité directe des tails
- **Sous-axe B** : TQL-lite par induction k→k−1 / structure récursive des tails

Le round doit trancher quelle formulation est la plus démontrable et la plus utile pour R52.

---

# AXE A — INVESTIGATEUR / QUASI-UNIFORMITÉ DES TAILS
## Nom de travail
À quel niveau les tails sont-elles déjà uniformes ?

## Mission
Étudier les distributions

N^{tail}_{b0,r}

et déterminer quelle notion de quasi-uniformité est réaliste à court terme.

### Questions obligatoires
1. Quelle est la meilleure quantité pour mesurer la quasi-uniformité des tails ?
   - max_r |N^{tail}_{b0,r} − C_{b0}/p|
   - variance L²
   - second moment M₂^{tail}
   - corrélation décalée moyenne
   - autre
2. Quelle version de TQL-lite paraît réaliste ?
   - uniforme en r pour un b0 fixé
   - moyenne en r
   - moyenne sur b0
   - seulement dans un sous-régime (ord_p(2) grand, p fixé, k grand, etc.)
3. Quel est le plus petit sous-régime où une quasi-uniformité non triviale paraît prouvable ?
4. Quel lien exact entre TQL-lite et Z-lite via phase shift peut déjà être écrit proprement ?
5. Quelle formulation de TQL-lite serait suffisante pour donner un vrai progrès sur V_between ?

### Livrables
- une hiérarchie claire des versions possibles de TQL-lite ;
- sélection du meilleur sous-régime naturel ;
- formulation précise du premier TQL-lite candidat.

---

# AXE B — INVESTIGATEUR / INDUCTION SUR LES TAILS
## Nom de travail
TQL par récurrence k→k−1

## Mission
Étudier si les tails se comportent suffisamment comme des sous-problèmes de taille k−1 pour permettre une induction utile.

### Questions obligatoires
1. Quelle est la relation exacte entre une tranche fixée b0 et le problème Collatz monotone de taille k−1 ?
2. Quels paramètres changent vraiment en passant à la tail ?
   - C_{b0}
   - max_B restant
   - polynôme tronqué T(B_tail)
   - normalisation
3. Peut-on transporter une borne de type TQL-lite d’un niveau k−1 vers k ?
4. Quelle obstruction principale casse la récurrence naïve ?
5. Quel est le plus petit lemme inductif crédible ?

### Livrables
- reformulation canonique de la tail comme sous-problème ;
- verdict honnête sur la viabilité de l’induction ;
- un noyau de lemme récursif si possible.

---

# AXE C — INNOVATEUR / PREMIER NOYAU PROUVABLE DE TQL
## Nom de travail
TQL-lite prouvable

## Mission
Proposer au plus 2 formulations candidates d’un premier noyau prouvable pour TQL.

### Candidat 1
**TQL-lite direct**
Dans un sous-régime naturel favorable, les distributions tail sont assez proches de l’uniforme pour donner directement un contrôle non trivial sur Z-lite.

### Candidat 2
**TQL-lite inductif**
Une version récursive faible de quasi-uniformité des tails se transporte de k−1 à k, avec perte contrôlée, et suffit déjà à améliorer ACaL-between-lite.

### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait immédiatement ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle ;
6. niveau estimé dans la Ladder of Proof.

## Règle obligatoire
À la fin :
- garder un seul survivant pour R52 ;
- éliminer l’autre explicitement ;
- justifier le choix par démontrabilité réelle, pas par élégance.

---

# CONTRÔLE SECONDAIRE OPTIONNEL
Un seul micro-test ciblé est autorisé si et seulement s’il départage deux versions de TQL-lite ou deux sous-régimes.
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
- revenir à ρ-lite direct comme route principale ;
- relancer une campagne computationnelle large ;
- présenter TQL comme quasi-prouvé ;
- confondre un bon alignement numérique avec une induction valide.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : une version crédible de TQL-lite est formulée proprement.
PASS-2 : un sous-régime naturel favorable est sélectionné.
PASS-3 : le lien exact TQL-lite → Z-lite est écrit proprement.
PASS-4 : au moins une formulation trop forte de TQL est éliminée avec autopsie complète.
PASS-5 : un survivant unique pour R52 est sélectionné.

# ÉCHEC UTILE
Même en cas d’échec, R51 est utile si :
- la bonne notion de quasi-uniformité des tails est clarifiée ;
- une induction naïve est réfutée proprement ;
- une version plus pauvre mais plus prouvable de TQL est isolée.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats AXE A (quasi-uniformité)
5. Résultats AXE B (induction)
6. Résultats AXE C (arbitrage)
7. Contrôle secondaire éventuel
8. CEC inchangé
9. Objets concernés + Ladder of Proof
10. Ce qui est appris
11. Ce qui est enterré
12. Autopsie des pistes fermées
13. Survivant pour R52
14. Risques / limites
15. Verdict final avec score /10

---

# CONSIGNE FINALE
R51 doit transformer TQL d’idée unificatrice en premier levier de preuve utilisable.
Le but n’est pas de mieux raconter les tails.
Le but est d’identifier la première version démontrable utile de TQL-lite.
Chercher le bon noyau de quasi-uniformité, pas la théorie finale complète.

