

TYPE: P
OBJET CIBLÉ: sous-étape (c) du bridge K-lite + preuve de ε>0 en R3 + dynamique locale hit-hit, avec chaînes courtes comme renfort auxiliaire et cross gardé comme conséquence stratégique
QUESTION CENTRALE: Peut-on faire monter le survivant de R61 d’un cran vers un premier sous-lemme semi-prouvé utile, en obtenant une preuve crédible que le taux de transition hit-hit est uniformément strictement inférieur à 1 en régime R3, avec une marge ε>0 exploitable pour faire avancer (d) puis K-lite ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: identifier précisément quelle partie du contrôle hit-hit manque encore (géométrie des fenêtres, dynamique de c_δ, chaînes, ou constante), et enterrer proprement toute tentative trop ambitieuse avec autopsie complète.

# BRIEF CLAUDE CODE — ROUND 62 (R62)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R61.

### Contexte acquis
- R57–R59 ont transformé la base k=2 en problème de théorie des nombres bien posé via :
  - δ = b−a
  - c_δ = 1 + g·2^δ
  - N_r = #{δ : dlog(r/c_δ) ∈ [0, M−δ]}
- R59 a sélectionné la route prioritaire :
  - **Lemme K-lite via barrier counting**
  avec cible réaliste
  - max N_r ≤ C/p + α(M+1), α<1
- R60 a articulé le schéma de preuve en 4 sous-étapes et isolé le verrou unique :
  - **(a)** reformulation δ [PROUVÉ]
  - **(b)** injectivité / |S_δ|≤1 [PROUVÉ]
  - **(c)** contrôle du taux de transition hit-hit [VERROU]
  - **(d)** intégration ⇒ α<1 [dépend de (c)]
- R61 a stabilisé la bonne cible pour (c) :
  - **Hit-hit-lite pointwise**
  - en priorité dans le régime **R3**
  - avec signal observé fort :
    τ_moyen = 0.317,
    τ_max ≤ 0.529,
    donc ε = 1−τ_max ≥ 0.47 sur l’échantillon.
- R61 a aussi clarifié :
  - la géométrie des fenêtres fait l’essentiel du travail ;
  - les chaînes longues sont rares ;
  - le nesting est un renfort utile, mais pas le moteur principal.
- Le risque stratégique est maintenant :
  - viser trop vite une forme universelle sur tous les régimes ;
  - ou se contenter de nouveaux constats numériques sans formuler le bon sous-lemme prouvable.

## Objectif de R62
R62 doit répondre à cette question centrale :

> Peut-on formuler et défendre une première preuve crédible que, dans le régime R3, le taux de transition hit-hit est uniformément borné par 1−ε avec ε>0, sous une forme suffisamment propre pour faire avancer la sous-étape (d), même si la meilleure constante finale reste ouverte ?

R62 doit être un round proof-oriented très centré.
Pas de dispersion.
Pas de campagne computationnelle large.
Le but est d’attaquer directement la marge ε>0 en R3.

---

# ARCHITECTURE GÉNÉRALE

## Pièce principale unique
**Preuve / quasi-preuve de ε>0 pour hit-hit en R3**

## Pièces auxiliaires autorisées mais subordonnées
- **chaînes courtes** comme renfort structurel ;
- **nesting** comme renfort secondaire ;
- **cross** conservé comme conséquence stratégique, sans nouvelle attaque frontale.

Le round doit dire explicitement si, après R62, la sous-étape (c) est assez mûre pour faire de K-lite un lemme candidat très fort.

---

# AXE A — INVESTIGATEUR / FORMULATION PRÉCISE DE ε>0
## Nom de travail
Que faut-il vraiment prouver pour fermer (c) ?

## Mission
Transformer le contrôle hit-hit en un énoncé mathématique précis, avec la bonne marge, le bon régime, et la bonne dépendance éventuelle en paramètres.

### Questions obligatoires
1. Quelle est la formulation canonique la plus utile de la propriété visée ?
   - τ(r) ≤ 1−ε uniforme en r,
   - τ(r) ≤ 1−ε(R3),
   - version moyenne renforcée + passage pointwise,
   - autre formulation équivalente plus démontrable
2. Quel est le plus petit énoncé utile déjà assez fort pour faire avancer (d) ?
3. La marge ε doit-elle être :
   - constante absolue en R3,
   - explicite en fonction de ord,
   - seulement strictement positive,
   - autre
4. Quelle partie du problème relève encore de la dynamique des hits, et quelle partie est déjà absorbée par la géométrie des fenêtres ?
5. Quel est l’obstacle principal restant dans la formulation elle-même ?

### Livrables
- formulation canonique de ε>0 ;
- meilleure cible réaliste pour ε ;
- distinction nette entre ce qui est déjà sous contrôle et ce qui ne l’est pas ;
- un premier sous-lemme candidat.

---

# AXE B — INVESTIGATEUR / ROUTE DE PREUVE POUR ε>0
## Nom de travail
Quelle mécanique impose τ<1 ?

## Mission
Comparer les mécanismes réellement capables d’imposer une marge strictement positive sur hit-hit en R3.

### Questions obligatoires
1. Quelle route paraît la plus crédible ?
   - géométrie locale des fenêtres,
   - rareté des longues chaînes,
   - coût structurel des doubles hits consécutifs,
   - dynamique affine de c_δ,
   - mélange de ces ingrédients,
   - autre
2. Peut-on déjà écrire un sous-lemme du type :
   - “deux hits consécutifs imposent une contrainte rare”,
   - “les longues chaînes sont exponentiellement rares”,
   - “la persistance locale est uniformément bornée”,
   - autre
3. En quoi les chaînes courtes aident-elles vraiment, et où s’arrête leur pouvoir ?
4. Quelles routes sont explicitement mortes ou trop faibles à ce stade ?
5. Quelle route semble la plus démontrable dans le temps court d’un round ?

### Livrables
- comparaison honnête des routes ;
- sélection de la route prioritaire ;
- liste explicite des outils morts à ne pas ressusciter ;
- un sous-lemme candidat si possible.

---

# AXE C — INNOVATEUR / NOYAU PROUVABLE POUR (c)
## Nom de travail
ε-lite prouvable

## Mission
Proposer au plus 2 formulations candidates d’un premier noyau prouvable utile pour la sous-étape (c).

### Candidat 1
**ε-lite pointwise**
Dans le régime R3, le taux hit-hit est uniformément borné par 1−ε avec ε>0, sous une forme suffisamment propre pour être injectée directement dans (d).

### Candidat 2
**ε-lite via chaînes**
Il n’est pas nécessaire de contrôler toutes les transitions individuellement ; il suffit de montrer que la structure des chaînes impose une marge globale strictement positive après intégration.

### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait immédiatement ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle ;
6. niveau estimé dans la Ladder of Proof.

## Règle obligatoire
À la fin :
- garder un seul survivant pour R63 ;
- éliminer l’autre explicitement ;
- justifier le choix par démontrabilité réelle, pas par élégance.

---

# AXE D — CONTRÔLE SECONDAIRE / CHAÎNE GLOBALE
## Nom de travail
Ne pas perdre K-lite de vue

## Mission
Sans faire du cross la cible principale, rappeler brièvement comment une borne utile sur ε>0 se réinjecte dans :
- (d) ⇒ α<1,
- K-lite,
- base,
- puis cross.

### Questions obligatoires
1. Quel est le lien minimal “ε>0 → α<1 → K-lite” à préserver ?
2. Le passage par R3 change-t-il la stratégie globale ou seulement la première marche ?
3. Quel rappel concis faut-il conserver pour éviter toute dérive future ?

### Livrables
- rappel propre de la chaîne de conséquences ;
- aucune nouvelle attaque frontale du cross ;
- aucune dérive hors du verrou principal.

---

# CONTRÔLE SECONDAIRE OPTIONNEL
Un seul micro-test ciblé est autorisé si et seulement s’il aide à départager :
- ε-lite pointwise vs ε-lite via chaînes,
- ou deux formulations concurrentes de la marge ε en R3.
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
- ressusciter de faux débats sur la métrique ;
- faire du cross la cible principale du round ;
- lancer une campagne computationnelle large ;
- présenter ε>0 comme prouvé tant que le sous-lemme utile n’est pas réellement formulé.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : une formulation précise de ε>0 est isolée.
PASS-2 : une route de preuve prioritaire est sélectionnée.
PASS-3 : un premier noyau de sous-lemme utile pour (c) est formulé.
PASS-4 : au moins une tentative trop optimiste est éliminée avec autopsie complète.
PASS-5 : un survivant unique pour R63 est sélectionné.

# ÉCHEC UTILE
Même en cas d’échec, R62 est utile si :
- le vrai verrou de la sous-étape (c) est clarifié ;
- une fausse bonne formulation de ε est éliminée ;
- une version plus pauvre mais plus prouvable du contrôle est isolée.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats AXE A (formulation de ε)
5. Résultats AXE B (routes de preuve)
6. Résultats AXE C (ε-lite)
7. Résultats AXE D (chaîne globale)
8. Contrôle secondaire éventuel
9. CEC inchangé
10. Objets concernés + Ladder of Proof
11. Ce qui est appris
12. Ce qui est enterré
13. Autopsie des pistes fermées
14. Survivant pour R63
15. Risques / limites
16. Verdict final avec score /10

---

# CONSIGNE FINALE
R62 doit transformer le verrou unique identifié par R60–R61 en première marge prouvable utile.
Le but n’est pas de refaire une carte du hit-hit.
Le but est d’obtenir une version démontrable de ε>0 en R3, suffisamment forte pour faire progresser (d) puis K-lite.
Chercher la prochaine sous-pièce prouvable, pas la théorie finale complète.