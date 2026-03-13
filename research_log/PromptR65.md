

TYPE: P
OBJET CIBLÉ: sous-étape (d) du schéma K-lite + intégration quantitative de τ<1 vers α<1 + fermeture de K-lite en R3, avec cas fini p<37 en clôture technique secondaire
QUESTION CENTRALE: Peut-on faire monter le survivant de R64 d’un cran vers un vrai lemme prouvé utile, en formalisant rigoureusement le passage quantitatif τ<1 ⇒ α<1 ⇒ K-lite en régime R3, avec constantes explicites, sans rouvrir le verrou analytique déjà fermé sur S_h ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: identifier exactement quelle micro-inégalité ou quelle perte de constante bloque encore l’intégration (d), et enterrer proprement toute tentative de réouvrir les anciens verrous avec autopsie complète.

# BRIEF CLAUDE CODE — ROUND 65 (R65)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R64.

### Contexte acquis
- R57–R59 ont transformé la base k=2 en problème de théorie des nombres bien posé via :
  - δ = b−a
  - c_δ = 1 + g·2^δ
  - N_r = #{δ : dlog(r/c_δ) ∈ [0, M−δ]}
- R59 a sélectionné la route prioritaire :
  - **Lemme K-lite via barrier counting**
  avec cible réaliste
  - max N_r ≤ C/p + α(M+1), α<1
- R60 a articulé le schéma de preuve en 4 sous-étapes :
  - **(a)** reformulation δ [PROUVÉ]
  - **(b)** injectivité / |S_δ|≤1 [PROUVÉ]
  - **(c)** contrôle hit-hit [VERROU initial]
  - **(d)** intégration ⇒ α<1 [restait à formaliser]
- R61–R62 ont fixé la bonne cible locale pour (c) :
  - hit-hit-lite pointwise en régime R3,
  - avec ε>0 comme marge utile.
- R63 a réduit le verrou d’équidistribution à un objet explicite :
  - S_h = Σ_{t∈⟨g²⟩} χ_h(1+t).
- R64 a fermé le verrou analytique principal en R3 :
  - décomposition exacte de S_h,
  - réduction à somme de Jacobi standard,
  - borne racine carrée
    |S_h| ≤ (1+√p)/2,
  - puis chaîne semi-formelle vers D_∞ petit, τ<1, et ε-lite.
- Il reste désormais le dernier verrou principal :
  - **formaliser complètement la sous-étape (d)**
  - i.e. passer rigoureusement d’un contrôle local sur τ à une borne globale
    α < 1
  - donc à un vrai **K-lite prouvé en R3**.
- Le risque stratégique est maintenant :
  - rouvrir inutilement S_h ou D_∞ alors qu’ils sont déjà fermés au niveau utile ;
  - ou glisser de “chaîne plausible” à “preuve complète” sans écrire proprement les constantes et la sommation finale.

## Objectif de R65
R65 doit répondre à cette question centrale :

> Peut-on écrire rigoureusement le passage quantitatif (d), c’est-à-dire intégrer le contrôle local hit-hit / τ<1 pour obtenir une borne globale α<1, puis en déduire un vrai K-lite en régime R3, avec constantes explicites et sans aucune zone grise de statut ?

R65 doit être un round proof-oriented très centré.
Pas de dispersion.
Pas de campagne computationnelle large.
Le but est de fermer le dernier maillon logique avant un vrai lemme de base en R3.

---

# ARCHITECTURE GÉNÉRALE

## Pièce principale unique
**Sous-étape (d) : intégration quantitative τ<1 ⇒ α<1 ⇒ K-lite**

## Pièces auxiliaires autorisées mais subordonnées
- cas fini **p<37** comme clôture technique secondaire uniquement ;
- rappel propre de la chaîne S_h → D_∞ → τ<1, sans nouvelle attaque frontale ;
- cross conservé comme conséquence stratégique, sans nouvelle attaque frontale.

Le round doit dire explicitement si, après R65, K-lite passe de semi-formel à prouvé en R3.

---

# AXE A — INVESTIGATEUR / FORMULATION EXACTE DE (d)
## Nom de travail
Que faut-il exactement sommer / intégrer ?

## Mission
Écrire la formulation mathématique précise du passage local → global qui transforme le contrôle sur τ en borne sur α.

### Questions obligatoires
1. Quelle est la formulation canonique exacte de la sous-étape (d) ?
   - sommation sur δ,
   - intégration sur la barrière,
   - récurrence de densité locale,
   - autre formulation équivalente plus propre
2. Quelle est la quantité exacte à intégrer / sommer ?
3. Quel est le lien minimal explicite entre :
   - τ(r) ≤ 1−ε,
   - la densité de hits,
   - et α < 1 ?
4. À quel endroit exact les constantes se perdent-elles ?
5. Quel est le plus petit énoncé complètement rigoureux déjà assez fort pour conclure K-lite ?

### Livrables
- formulation canonique de (d) ;
- chaîne exacte des inégalités ;
- localisation précise des pertes de constante ;
- un premier sous-lemme candidat si possible.

---

# AXE B — INVESTIGATEUR / CONSTANTES EXPLICITES ET CAS FINI
## Nom de travail
Peut-on fermer R3 proprement ?

## Mission
Vérifier si la chaîne avec constantes explicites suffit réellement à obtenir α<1 en R3, et cadrer le cas fini restant sans en faire un nouveau sujet principal.

### Questions obligatoires
1. Quelle constante explicite sur τ<1 est réellement disponible après R64 ?
2. Quelle constante explicite sur α en découle ?
3. La borne obtenue ferme-t-elle vraiment K-lite en R3 ?
4. Que reste-t-il à faire pour le cas fini p<37 ?
5. Quel est le plus petit traitement du cas fini compatible avec une clôture propre ?

### Livrables
- constantes explicites de la chaîne ;
- verdict honnête “R3 fermé ou pas encore” ;
- cadrage minimal du cas fini ;
- un sous-lemme de clôture si possible.

---

# AXE C — INNOVATEUR / K-LITE PRÊT OU PAS ?
## Nom de travail
K-lite prouvé en R3 ?

## Mission
Proposer au plus 2 formulations candidates du résultat final atteignable après R64.

### Candidat 1
**K-lite prouvé en R3**
La chaîne complète est fermée : (a)+(b)+(c)+(d) donnent un vrai lemme K-lite en régime R3.

### Candidat 2
**K-lite presque fermé**
Le verrou analytique et la quasi-totalité de l’intégration sont fermés, mais une micro-inégalité ou un cas fini explicite reste à verrouiller pour finaliser R3.

### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait immédiatement ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle ;
6. niveau estimé dans la Ladder of Proof.

## Règle obligatoire
À la fin :
- garder un seul survivant pour R66 ;
- éliminer l’autre explicitement ;
- justifier le choix par démontrabilité réelle, pas par enthousiasme.

---

# AXE D — CONTRÔLE SECONDAIRE / CHAÎNE GLOBALE
## Nom de travail
Ne pas casser la logique d’ensemble

## Mission
Sans faire du cross la cible principale, rappeler brièvement comment la fermeture éventuelle de K-lite en R3 se réinjecte dans :
- la base k=2,
- le schéma global,
- puis la préparation future du cross et du bootstrap.

### Questions obligatoires
1. Quel est le lien minimal “K-lite fermé en R3 → base renforcée → cross préparé” à préserver ?
2. La clôture de R3 change-t-elle seulement la base, ou aussi la hiérarchie stratégique globale ?
3. Quel rappel concis faut-il conserver pour éviter toute dérive future ?

### Livrables
- rappel propre de la chaîne de conséquences ;
- aucune nouvelle attaque frontale du cross ;
- aucune dérive hors du verrou principal.

---

# CONTRÔLE SECONDAIRE OPTIONNEL
Un seul micro-test ciblé est autorisé si et seulement s’il aide à départager :
- “K-lite prouvé” vs “K-lite presque fermé”,
- ou deux pertes de constante concurrentes dans la sous-étape (d).
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
- rouvrir S_h ou D_∞ comme cible principale ;
- relancer des scans numériques larges ;
- présenter K-lite comme prouvé tant que (d) n’est pas écrit proprement ;
- sur-vendre R64 si une micro-inégalité reste en réalité ouverte.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : une formulation exacte de (d) est isolée.
PASS-2 : les constantes explicites sont clarifiées proprement.
PASS-3 : un résultat net “K-lite prouvé” ou “K-lite presque fermé” est établi honnêtement.
PASS-4 : au moins une illusion résiduelle est éliminée avec autopsie complète.
PASS-5 : un survivant unique pour R66 est sélectionné.

# ÉCHEC UTILE
Même en cas d’échec, R65 est utile si :
- la micro-inégalité réellement bloquante est isolée ;
- une perte de constante cachée est révélée ;
- une version plus pauvre mais complètement rigoureuse de K-lite en R3 est isolée.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats AXE A ((d) : intégration)
5. Résultats AXE B (constantes et cas fini)
6. Résultats AXE C (K-lite prouvé ou presque)
7. Résultats AXE D (chaîne globale)
8. Contrôle secondaire éventuel
9. CEC inchangé
10. Objets concernés + Ladder of Proof
11. Ce qui est appris
12. Ce qui est enterré
13. Autopsie des pistes fermées
14. Survivant pour R66
15. Risques / limites
16. Verdict final avec score /10

---

# CONSIGNE FINALE
R65 doit fermer le dernier maillon logique laissé semi-formel par R64.
Le but n’est pas de réouvrir le verrou analytique.
Le but est d’écrire proprement l’intégration quantitative qui mène à α<1 puis à K-lite en R3.
Chercher la prochaine fermeture rigoureuse, pas la théorie finale complète.