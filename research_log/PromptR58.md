TYPE: P
OBJET CIBLÉ: base k=2 + distribution des dlogs de la suite affine c_δ = 1 + g·2^δ + cross préparé en second plan
QUESTION CENTRALE: Peut-on faire monter la base k=2 d’un cran vers un vrai lemme utile, en obtenant une borne additive crédible sur max N_r via la distribution des logarithmes discrets de la suite affine c_δ, tout en gardant le cross proprement cadré sans en faire encore la cible principale ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: identifier la bonne formulation théorique du gap dlog de la base, et enterrer proprement toute modélisation trop naïve de la suite affine avec autopsie complète.

# BRIEF CLAUDE CODE — ROUND 58 (R58)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R57.

### Contexte acquis
- R56 a confirmé l’architecture post-R55 :
  - **base k=2** comme pièce la plus proche d’un vrai lemme ;
  - **cross** comme pièce plus difficile, à traiter ensuite par route bilinéaire.
- R57 a produit la percée structurelle majeure sur la base :
  - **δ-reformulation**
  - avec c_δ = 1 + g·2^δ
  - et
    N_r = #{δ : dlog(r / c_δ) ∈ [0, M−δ]}
- R57 a aussi prouvé / stabilisé plusieurs briques :
  - chaque δ contribue au plus une solution ;
  - les c_δ sont distincts en R1 ;
  - au plus un δ dégénéré ;
  - borne triviale N_r ≤ M+1 ;
  - formule exacte de N_0 ;
  - récurrence affine c_{δ+1} = 2c_δ − 1.
- Le gap de la base k=2 est désormais unique et très net :
  - **contrôler max_r N_r**
  - autrement dit : comprendre la distribution des logarithmes discrets de la suite affine c_δ.
- R57 a aussi clarifié la bonne stratégie globale :
  - **base suffisante + cross préparé**
  - et non pas base parfaite puis cross, ni cross-first.
- Le risque stratégique est maintenant :
  - traiter la suite c_δ comme si elle était “presque aléatoire” sans justification ;
  - ou choisir une métrique / modélisation trop naïve qui ne capture pas le vrai verrou additif.

## Objectif de R58
R58 doit répondre à cette question centrale :

> Peut-on identifier une formulation théorique crédible et utilisable du problème “distribution des dlogs de c_δ = 1+g·2^δ”, suffisamment forte pour viser une borne additive du type max N_r ≤ C/p + K·√(M+1) (ou variante utile), tout en gardant le cross comme pièce secondaire préparée ?

R58 doit être un round proof-oriented très centré.
Pas de dispersion.
Pas de campagne computationnelle large.
Le but est de transformer le gap de la base en problème de théorie des nombres bien posé et attaquable.

---

# ARCHITECTURE GÉNÉRALE

## Pièce principale
**Base k=2 via distribution des dlogs de la suite affine**

## Pièce secondaire cadrée mais non prioritaire
**Cross-lite bilinéaire préparé, sans nouvelle attaque frontale**

Le round doit dire explicitement si, après R58, le vrai verrou est encore la base k=2, ou si elle est assez mûre pour laisser la priorité au cross.

---

# AXE A — INVESTIGATEUR / FORMULATION THÉORIQUE DU GAP DLOG
## Nom de travail
Que faut-il vraiment prouver sur c_δ ?

## Mission
Étudier la suite affine

c_δ = 1 + g·2^δ

et déterminer quelle formulation théorique est la plus crédible pour contrôler la multiplicité max N_r.

### Questions obligatoires
1. Quelle est la meilleure reformulation du problème ?
   - discrepancy additive des dlogs,
   - distribution dans des fenêtres variables,
   - ensembles de Bohr,
   - corrélation affine dans le groupe multiplicatif,
   - autre
2. Quelle métrique paraît la plus pertinente ?
   - borne additive sur max N_r,
   - second moment de N_r,
   - discrepancy L∞ / L²,
   - autre
3. La structure affine
   c_{δ+1} = 2c_δ − 1
   donne-t-elle un levier théorique réel, ou seulement une jolie écriture ?
4. Quel est le meilleur sous-régime où attaquer en premier ?
   - cas générique uniquement,
   - cas dégénéré traité séparément,
   - p grand vs M,
   - autre
5. Quel est le plus petit énoncé crédible qui ferait réellement progresser la base ?

### Livrables
- reformulation canonique du gap dlog ;
- meilleure métrique cible ;
- hiérarchie honnête des sous-régimes ;
- un premier noyau d’énoncé semi-formel utile.

---

# AXE B — INVESTIGATEUR / ROUTES DE PREUVE POUR max N_r
## Nom de travail
Quelle route a une chance de marcher ?

## Mission
Comparer les voies théoriques possibles pour contrôler max N_r, sans tomber dans des outils déjà enterrés ou dans une pseudo-aléa non justifiée.

### Questions obligatoires
1. Quelle route paraît la plus crédible à court terme ?
   - sommes exponentielles sur dlogs,
   - méthode additive / fenêtres,
   - théorie d’incidence,
   - argument combinatoire sur collisions,
   - autre
2. Quels outils sont explicitement morts ou suspects ici ?
   - équidistribution multiplicative naïve,
   - orbites complètes comme mécanisme central,
   - autres illusions à éviter
3. Peut-on viser une borne du type
   max N_r ≤ C/p + K·√(M+1)
   ou faut-il une cible intermédiaire plus faible mais prouvable ?
4. Quel est le premier sous-lemme réaliste sur la suite c_δ ?
5. Quelle route semble trop ambitieuse aujourd’hui malgré son élégance ?

### Livrables
- comparaison honnête des routes de preuve ;
- sélection de la route prioritaire ;
- liste explicite des outils morts à ne pas ressusciter ;
- un premier sous-lemme candidat si possible.

---

# AXE C — INNOVATEUR / NOYAU PROUVABLE DE LA BASE APRÈS R57
## Nom de travail
Base-lite renforcée

## Mission
Proposer au plus 2 formulations candidates d’un premier noyau prouvable utile pour la base k=2.

### Candidat 1
**Base-lite additive**
Une borne explicite du type
max N_r ≤ C/p + K·√(M+1)
ou une variante additive affaiblie, suffit à transformer la base en quasi-lemme utilisable pour la machine globale.

### Candidat 2
**Base-lite de second moment**
Un contrôle du second moment des N_r, même sans borne pointwise optimale, suffit déjà à produire un lemme de base utile et plus démontrable.

### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait immédiatement ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle ;
6. niveau estimé dans la Ladder of Proof.

## Règle obligatoire
À la fin :
- garder un seul survivant pour R59 ;
- éliminer l’autre explicitement ;
- justifier le choix par démontrabilité réelle, pas par élégance.

---

# AXE D — CONTRÔLE SECONDAIRE / CROSS PRÉPARÉ
## Nom de travail
Ne pas perdre le cross de vue

## Mission
Sans faire du cross la cible principale, vérifier que la préparation bilinéaire issue de R57 reste propre et cohérente avec l’évolution de la base.

### Questions obligatoires
1. La préparation bilinéaire du cross reste-t-elle intacte après la nouvelle lecture de la base ?
2. Y a-t-il une interaction nouvelle base ↔ cross à noter ?
3. Quel est le plus petit rappel utile à conserver pour éviter de repartir de zéro plus tard ?

### Livrables
- confirmation courte que la route cross reste bien cadrée ;
- aucune nouvelle attaque frontale ;
- aucune dérive analytique inutile.

---

# CONTRÔLE SECONDAIRE OPTIONNEL
Un seul micro-test ciblé est autorisé si et seulement s’il aide à départager :
- borne additive vs second moment,
- ou deux formulations concurrentes du gap dlog.
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
- relancer une équidistribution naïve “presque aléatoire” sans justification ;
- faire du cross la cible principale du round ;
- lancer une campagne computationnelle large ;
- présenter la base k=2 comme prouvée tant que le gap sur max N_r reste ouvert.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : une formulation théorique crédible du gap dlog est isolée.
PASS-2 : une route de preuve prioritaire pour max N_r est sélectionnée.
PASS-3 : un meilleur noyau de base-lite est formulé.
PASS-4 : au moins une modélisation naïve ou trop optimiste est éliminée avec autopsie complète.
PASS-5 : un survivant unique pour R59 est sélectionné.

# ÉCHEC UTILE
Même en cas d’échec, R58 est utile si :
- le vrai verrou théorique de la base est clarifié ;
- une fausse bonne route sur les dlogs est éliminée ;
- une version plus pauvre mais plus prouvable de la base-lite est isolée.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats AXE A (gap dlog)
5. Résultats AXE B (routes de preuve)
6. Résultats AXE C (base-lite)
7. Résultats AXE D (cross préparé)
8. Contrôle secondaire éventuel
9. CEC inchangé
10. Objets concernés + Ladder of Proof
11. Ce qui est appris
12. Ce qui est enterré
13. Autopsie des pistes fermées
14. Survivant pour R59
15. Risques / limites
16. Verdict final avec score /10

---

# CONSIGNE FINALE
R58 doit transformer le gap de la base k=2 en problème de théorie des nombres bien posé et attaquable.
Le but n’est pas de raconter encore mieux c_δ.
Le but est d’identifier la bonne formulation théorique et le bon noyau de lemme pour verrouiller la base, tout en gardant le cross proprement préparé.
Chercher la prochaine pièce prouvable, pas la théorie finale complète.
