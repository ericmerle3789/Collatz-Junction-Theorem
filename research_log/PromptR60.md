

TYPE: P
OBJET CIBLÉ: Lemme K-lite + bridge entre la suite affine c_δ = 1 + g·2^δ et une équidistribution suffisante des d_δ + nesting comme auxiliaire + cross gardé comme conséquence secondaire
QUESTION CENTRALE: Peut-on faire monter la route prioritaire issue de R59 d’un cran vers un premier schéma semi-prouvé utile, en construisant le bridge entre la suite affine c_δ et une équidistribution suffisante des d_δ pour soutenir un Lemme K-lite de comptage sous barrière avec α<1 ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: identifier précisément quel morceau du bridge manque encore (suite affine, dlogs, fenêtres, ou nesting), et enterrer proprement toute tentative trop optimiste avec autopsie complète.

# BRIEF CLAUDE CODE — ROUND 60 (R60)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R59.

### Contexte acquis
- R56–R57 ont confirmé que la **base k=2** est la pièce la plus proche d’un vrai lemme, tandis que le **cross** doit rester secondaire tant que la base n’est pas mieux verrouillée.
- R57 a donné la reformulation clé :
  - δ = b−a
  - c_δ = 1 + g·2^δ
  - N_r = #{δ : dlog(r/c_δ) ∈ [0, M−δ]}
- R58 a transformé le gap de la base en problème de théorie des nombres bien posé :
  - distribution des dlogs d’une suite affine dans des **fenêtres rétrécissantes**.
- R59 a sélectionné la route prioritaire :
  - **Lemme K-lite via barrier counting**
  - avec cible réaliste :
    max N_r ≤ C/p + α(M+1),   α < 1
  - et diagnostic structurel majeur :
    **la difficulté vient surtout des fenêtres, pas d’une concentration pathologique de la suite**.
- R59 a enterré les routes trop faibles ou mal calibrées :
  - large sieve direct
  - cible logarithmique
  - décomposition dyadique seule
  - hybride L²
- Il manque maintenant le bridge théorique central :
  - pourquoi la suite d_δ = dlog(r/c_δ) est-elle suffisamment bien répartie pour que la barrière d ≤ M−δ ne capture pas trop de points ?
- Le risque stratégique est maintenant :
  - rester bloqué au niveau descriptif “barrier counting” ;
  - ou réintroduire des outils faux/enterrés sous un autre nom.

## Objectif de R60
R60 doit répondre à cette question centrale :

> Peut-on construire une première version crédible du bridge “suite affine → distribution des d_δ → peu de points sous la barrière”, suffisamment forte pour soutenir un Lemme K-lite, même si la constante optimale α<1 n’est pas encore entièrement prouvée ?

R60 doit être un round proof-oriented très centré.
Pas de dispersion.
Pas de campagne computationnelle large.
Le but est de transformer la bonne route choisie en schéma de preuve articulé.

---

# ARCHITECTURE GÉNÉRALE

## Pièce principale unique
**Bridge vers le Lemme K-lite par barrier counting**

## Pièces auxiliaires autorisées
- **nesting** comme renfort structurel, pas comme moteur principal ;
- **cross** gardé comme conséquence stratégique, sans nouvelle attaque frontale.

Le round doit dire explicitement si, après R60, le vrai verrou principal reste la base k=2, ou si le bridge est assez mûr pour préparer le passage au cross.

---

# AXE A — INVESTIGATEUR / LE BRIDGE THÉORIQUE
## Nom de travail
Pourquoi les d_δ ne tombent-ils pas trop souvent sous la barrière ?

## Mission
Construire la meilleure reformulation théorique du bridge entre :
- la suite affine c_δ = 1 + g·2^δ,
- les d_δ = dlog(r/c_δ),
- et le comptage sous la barrière d_δ ≤ M−δ.

### Questions obligatoires
1. Quelle est la meilleure reformulation du bridge ?
   - problème d’équidistribution additive des d_δ,
   - rareté des hits sous une barrière décroissante,
   - structure affine + fenêtres emboîtées,
   - autre
2. Quelle partie du bridge dépend vraiment de la suite affine c_δ, et quelle partie dépend seulement de la géométrie des fenêtres ?
3. Peut-on écrire un énoncé intermédiaire crédible du type :
   - “pour tout r, les d_δ ne peuvent pas rester trop longtemps sous la barrière”,
   - ou une variante plus faible mais utile ?
4. Quel est le plus petit sous-régime où ce bridge paraît démontrable ?
5. Quelle est l’obstruction principale restante ?

### Livrables
- une formulation canonique du bridge ;
- un énoncé intermédiaire candidat ;
- une hiérarchie honnête des difficultés ;
- un verdict clair sur la partie déjà attaquable.

---

# AXE B — INVESTIGATEUR / NESTING COMME AUXILIAIRE
## Nom de travail
Le nesting peut-il aider sans porter la preuve ?

## Mission
Étudier comment la structure emboîtée des fenêtres peut servir de levier auxiliaire pour le Lemme K-lite, sans redevenir une fausse route autonome.

### Questions obligatoires
1. Quelle est la formulation la plus utile du nesting ici ?
2. Le nesting aide-t-il à contrôler :
   - la persistance des hits,
   - la fréquence des sauts,
   - la taille des grappes de solutions,
   - autre
3. Peut-on dériver du nesting un sous-lemme quantitatif faible mais utile ?
4. Quelle est la frontière entre “nesting utile” et “nesting insuffisant” ?
5. Comment intégrer proprement ce levier au bridge principal sans lui donner un rôle qu’il n’a pas ?

### Livrables
- une formulation auxiliaire du nesting ;
- un possible sous-lemme renfort ;
- une autopsie claire si le nesting est trop faible seul.

---

# AXE C — INNOVATEUR / PREMIER SCHÉMA DE PREUVE POUR K-LITE
## Nom de travail
K-lite via bridge

## Mission
Proposer au plus 2 formulations candidates d’un premier noyau prouvable utile.

### Candidat 1
**Bridge-lite pointwise**
Un énoncé intermédiaire sur la rareté des hits sous la barrière, combiné au barrier counting, suffit déjà à produire une borne additive utile sur max N_r.

### Candidat 2
**Bridge-lite + nesting**
Le bridge seul est trop faible, mais renforcé par un lemme de nesting il devient suffisant pour obtenir une première version utile de K-lite.

### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait immédiatement ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle ;
6. niveau estimé dans la Ladder of Proof.

## Règle obligatoire
À la fin :
- garder un seul survivant pour R61 ;
- éliminer l’autre explicitement ;
- justifier le choix par démontrabilité réelle, pas par élégance.

---

# AXE D — CONTRÔLE SECONDAIRE / CROSS CONSÉQUENCE
## Nom de travail
Ne pas perdre la machine globale de vue

## Mission
Sans faire du cross la cible principale, rappeler brièvement comment un Lemme K-lite renforcerait automatiquement la stratégie globale (base → cross → bootstrap).

### Questions obligatoires
1. Quel est le lien minimal à conserver entre K-lite et le contrôle futur du cross ?
2. Le nouveau schéma de bridge change-t-il quelque chose dans la préparation bilinéaire du cross ?
3. Quel rappel concis faut-il préserver pour éviter toute dérive future ?

### Livrables
- rappel court et propre du lien base → cross ;
- aucune nouvelle attaque frontale ;
- aucune dérive analytique inutile.

---

# CONTRÔLE SECONDAIRE OPTIONNEL
Un seul micro-test ciblé est autorisé si et seulement s’il aide à départager :
- bridge seul vs bridge+nested,
- ou deux formulations concurrentes du lemme intermédiaire.
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
- ressusciter large sieve, pseudo-aléa naïf, ou L²-hybride sous un autre nom ;
- faire du cross la cible principale du round ;
- lancer une campagne computationnelle large ;
- présenter K-lite comme prouvé tant que le bridge reste ouvert.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : une formulation précise du bridge est isolée.
PASS-2 : un énoncé intermédiaire utile pour K-lite est formulé.
PASS-3 : le rôle exact du nesting est clarifié.
PASS-4 : au moins une tentative trop optimiste est éliminée avec autopsie complète.
PASS-5 : un survivant unique pour R61 est sélectionné.

# ÉCHEC UTILE
Même en cas d’échec, R60 est utile si :
- le vrai verrou du bridge est clarifié ;
- une fausse bonne formulation du lemme intermédiaire est éliminée ;
- une version plus pauvre mais plus prouvable de K-lite est isolée.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats AXE A (bridge)
5. Résultats AXE B (nesting auxiliaire)
6. Résultats AXE C (K-lite)
7. Résultats AXE D (cross conséquence)
8. Contrôle secondaire éventuel
9. CEC inchangé
10. Objets concernés + Ladder of Proof
11. Ce qui est appris
12. Ce qui est enterré
13. Autopsie des pistes fermées
14. Survivant pour R61
15. Risques / limites
16. Verdict final avec score /10

---

# CONSIGNE FINALE
R60 doit transformer la bonne route choisie en premier schéma de preuve articulé pour la base k=2.
Le but n’est pas de mieux décrire encore le barrier counting.
Le but est de construire le bridge théorique suffisant pour viser un vrai Lemme K-lite, tout en gardant le cross comme conséquence secondaire bien cadrée.
Chercher la prochaine pièce prouvable, pas la théorie finale complète.