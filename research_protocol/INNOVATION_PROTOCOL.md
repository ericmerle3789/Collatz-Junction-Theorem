# PROTOCOLE D'INNOVATION MATHEMATIQUE ASSISTEE PAR LLM v1.0
## Cadre scientifique pour la creation de concepts mathematiques nouveaux
### Auteur : Eric Merle (assiste par Claude) — 6 mars 2026

---

## RESUME EXECUTIF

Ce protocole formalise une methodologie pour **creer des concepts mathematiques
nouveaux** en exploitant la capacite des LLM a relier des structures abstraites
entre domaines. Il s'agit d'un cadre d'**invention**, pas simplement de
**decouverte** : nous ne cherchons pas un theoreme existant, nous cherchons a
construire des outils mathematiques qui n'existent pas encore.

**Idee fondatrice** (Eric Merle, 6 mars 2026) :
> Les LLM possedent une capacite unique de *pontage conceptuel* : comme
> l'addition repetee (3+3+3+3) peut etre reexprimee en multiplication (4x3)
> par un acte de *renommage structural*, un LLM peut identifier des patterns
> repetitifs dans une preuve et les *condenser* en un nouvel operateur ou concept.
> C'est ainsi que naissent les mathematiques : par **compression linguistique
> de structures**.

---

## TABLE DES MATIERES

1. [Fondements theoriques](#1-fondements-theoriques)
2. [Le modele BRIDGE : 6 phases d'innovation](#2-le-modele-bridge)
3. [Phase B — Bilan structural](#phase-b)
4. [Phase R — Reseaux d'analogies](#phase-r)
5. [Phase I — Incubation et melange conceptuel](#phase-i)
6. [Phase D — Distillation en concept formel](#phase-d)
7. [Phase G — Garantie formelle (Lean 4)](#phase-g)
8. [Phase E — Extension et generalisation](#phase-e)
9. [Operateurs d'innovation](#3-operateurs-dinnovation)
10. [Garde-fous anti-hallucination](#4-garde-fous)
11. [Application au projet Collatz/Artin](#5-application)
12. [Criteres de publication et reception academique](#6-publication)
13. [Bibliographie](#7-bibliographie)

---

## 1. FONDEMENTS THEORIQUES

### 1.1 La creativite mathematique : trois traditions

La litterature identifie trois cadres complementaires pour comprendre
l'innovation mathematique :

**Tradition cognitive (Poincare-Hadamard-Wallas)**
- Preparation → Incubation → Illumination → Verification
- L'inconscient genere des combinaisons ; seules celles avec une "elegance
  esthetique" remontent a la conscience (Poincare, 1908)
- Hadamard (1945) : la pensee mathematique creative utilise des images
  mentales non-verbales, pas des symboles formels

**Tradition dialectique (Lakatos)**
- Conjecture → Tentative de preuve → Contre-exemple → Raffinement conceptuel
- Les **concepts generes par la preuve** : les definitions emergent des echecs
  de preuve, pas avant (Lakatos, 1976)
- Monster-barring, lemma-incorporation : mecanismes de correction conceptuelle

**Tradition computationnelle (Boden)**
- Creativite **combinatoire** : combinaisons nouvelles d'idees connues
- Creativite **exploratoire** : exploration systematique d'un espace conceptuel
- Creativite **transformationnelle** : changer les regles de l'espace conceptuel
  lui-meme — la plus rare et la plus puissante (Boden, 1990/2004)

### 1.2 L'apport specifique des LLM

Les LLM ne sont ni des calculateurs ni des mathematiciens. Leur apport unique
est **l'analogie structurale a grande echelle** :

| Capacite LLM | Mecanisme | Valeur pour l'innovation |
|---|---|---|
| Pontage inter-domaines | Embedding semantique | Relier algebre et topologie |
| Reformulation linguistique | Generation conditionnelle | "Voir" autrement |
| Pattern completion | Attention multi-tete | Deviner la structure manquante |
| Compression conceptuelle | Abstraction emergente | Addition → multiplication |

**Limitation critique** : les LLM ne *verifient* pas. Toute conjecture generee
doit passer par un verificateur independant (Lean 4, script numerique, ou
demonstration humaine rigoureuse).

> **Theoreme d'inevitabilite** (OpenAI, 2025) : il est mathematiquement prouve
> que les LLM hallucinent inevitablement. La verification >> la generation.
> Notre protocole integre cette realite en separant strictement creation et
> validation.

### 1.3 Le spectre de l'innovation mathematique

```
 Degre d'innovation    Exemple               Methode
 ──────────────────────────────────────────────────────────
 0. Application        Calculer 17! = ...     Algorithme
 1. Extension          Factorielle → Gamma    Analogie + prolongement
 2. Transfert          Fourier → nombres      Pontage de domaines
 3. Condensation       +++ → ×               Compression linguistique
 4. Inversion          f(x) → f⁻¹(x)        Renversement de perspective
 5. Unification        Geometrie + algebre    Melange conceptuel (Descartes)
 6. Transcendance      Axiome du choix        Changement d'espace conceptuel
```

Notre protocole cible principalement les niveaux 1-5.

---

## 2. LE MODELE BRIDGE : 6 PHASES D'INNOVATION

```
    B ────→ R ────→ I ────→ D ────→ G ────→ E
    │       │       │       │       │       │
  Bilan   Reseau  Incu-  Distil- Garan-  Exten-
  struc-  d'ana-  bation  lation  tie     sion
  tural   logies  + blend formel  Lean4
```

Le modele est **iteratif** : chaque echec en phase G renvoie a la phase I ou R.
Chaque succes en phase E peut generer un nouveau cycle B→R→I→D→G→E.

---

<a name="phase-b"></a>
## Phase B — Bilan structural

**Objectif** : Cartographier le probleme dans un espace multi-dimensionnel.

### B.1 Decomposition en contradictions (inspire de TRIZ)

Identifier les **contradictions fondamentales** du probleme :

> *Qu'est-ce qui rend ce probleme DIFFICILE ? Quelle propriete souhaitee
> entre en conflit avec quelle contrainte ?*

Format :
```
CONTRADICTION C1 : On veut [P1] mais [P2] l'empeche.
CONTRADICTION C2 : [P3] est necessaire mais implique [P4] indesirable.
...
```

Les 5 principes TRIZ les plus pertinents en mathematiques :
1. **Segmentation** (#1) : decomposer en sous-cas
2. **Inversion** (#13) : prouver le contraire, raisonner par l'absurde
3. **Changement de dimension** (#17) : monter en dimension/abstraction
4. **Auto-service** (#25) : utiliser la structure du probleme contre elle-meme
5. **Dynamisation** (#15) : rendre parametrique ce qui est fixe

### B.2 Graphe conceptuel

Construire le graphe des concepts impliques :
- Noeuds : definitions, theoremes, structures
- Aretes : "utilise", "generalise", "est dual de", "contredit"
- Identifier les **trous structurels** : paires de noeuds qui *devraient*
  etre connectes mais ne le sont pas

### B.3 Questions generatrices (Polya)

Appliquer systematiquement :
1. Quel est l'inconnu ? Quelles sont les donnees ? Quelle est la condition ?
2. Connaissez-vous un probleme apparente ? Un theoreme utile ?
3. Pouvez-vous reformuler le probleme ?
4. Pouvez-vous resoudre un cas particulier ?
5. Pouvez-vous resoudre un probleme plus general ?

---

<a name="phase-r"></a>
## Phase R — Reseaux d'analogies

**Objectif** : Chercher systematiquement des domaines a structure similaire.

### R.1 Mapping structural (Gentner)

Pour chaque concept cle du probleme, chercher des **analogies structurales**
dans des domaines distants :

```
DOMAINE SOURCE          STRUCTURE PARTAGEE         DOMAINE CIBLE
─────────────────────────────────────────────────────────────────
Theorie des groupes     Action + orbites           Dynamique de Collatz
Theorie de l'info       Entropie + compression     Densite des chemins
Analyse de Fourier      Decomposition spectrale    Residus mod puissances
Theorie des graphes     Chemins + arbres           Arbre de Syracuse
```

**Regle de Gentner** : mapper les *relations* (pas les objets). Le fait que
les groupes et Collatz n'ont rien en commun en surface est IRRELEVANT si
la structure relationnelle est similaire.

### R.2 Recherche d'analogies par LLM

Prompt systematique au LLM :

> "Voici la structure formelle de mon probleme : [description].
> Identifie 5 domaines mathematiques avec une structure relationnelle
> similaire. Pour chaque domaine, precise EXACTEMENT quel objet correspond
> a quel objet, et quelle relation correspond a quelle relation."

**Critere de qualite** : l'analogie doit mapper au moins 3 relations
(pas juste 1 objet).

### R.3 Differences alignables (Gentner & Markman)

Apres avoir identifie une analogie, explorer **la ou elle se brise** :

> Les differences *a l'interieur* d'une structure partagee sont les sites
> les plus productifs pour l'innovation.

Si dans le domaine source A, la propriete P est vraie, mais dans la cible B,
P est fausse — POURQUOI ? La reponse peut reveler un concept manquant.

---

<a name="phase-i"></a>
## Phase I — Incubation et melange conceptuel

**Objectif** : Generer des concepts candidats par melange, compression et
renversement.

### I.1 Melange conceptuel (Fauconnier-Turner)

Combiner deux espaces mathematiques en un "espace melange" :

```
ESPACE 1           ESPACE MELANGE           ESPACE 2
(Source)            (Innovation)             (Cible)
   •────────────────→ ◆ ←────────────────•
   │                  │                   │
Topologie        "Espace Melange"     Combinatoire
 Ouverts          ???                  Sous-ensembles
 Continuite       ???                  Monotonie
 Compacite        ???                  Finitude
                  │
          PROPRIETES EMERGENTES
          (absentes des deux sources)
```

L'etape critique est d'identifier les **proprietes emergentes** du melange
qui n'existaient dans aucun des deux espaces initiaux.

### I.2 Operateurs de compression linguistique

L'idee fondatrice d'Eric : la **compression linguistique** comme moteur
d'innovation. Protocole :

1. Identifier un pattern repetitif dans le raisonnement
2. Le nommer (acte linguistique de creation)
3. Formaliser le nom comme operateur/definition
4. Verifier que le nouveau concept simplifie REELLEMENT la preuve

**Exemples historiques** :
- 3+3+3+3 → 4×3 (compression additive → multiplication)
- f(f(f(x))) → f³(x) (composition repetee → iteration)
- Σ aᵢxⁱ → serie formelle (somme infinie → objet algebrique)
- det(A-λI) = 0 → spectre (equation polynomiale → concept geometrique)

### I.3 Les 7 operateurs d'innovation

(detailles en section 3)

### I.4 Incubation deliberee

Suivant Poincare-Hadamard :
- Apres 2h de travail focalise sans progres, ARRETER
- Changer d'activite (autre probleme, exercice physique, musique)
- Tenir un carnet d'idees (les illuminations viennent souvent au reveil)
- L'incubation n'est PAS de la paresse — c'est un processus cognitif actif

---

<a name="phase-d"></a>
## Phase D — Distillation en concept formel

**Objectif** : Transformer l'intuition en definition mathematique precise.

### D.1 Du vague au formel (Lakatos)

Processus de raffinement :

```
Intuition vague
    │
    ▼
Formulation naive
    │
    ▼
Test sur exemples ──→ Contre-exemple → Raffinement (monster-barring)
    │                                      │
    ▼                                      │
Definition candidate ◄─────────────────────┘
    │
    ▼
Premiers theoremes
    │
    ▼
Definition finale (stabilisee par l'usage)
```

### D.2 Criteres de qualite d'un concept nouveau

Un concept mathematique nouveau est UTILE s'il satisfait au moins 3/5 :

| Critere | Description | Test |
|---|---|---|
| **Compression** | Simplifie des enonces existants | La preuve raccourcit-elle ? |
| **Unification** | Relie des phenomenes disparates | Implique-t-il des cas speciaux connus ? |
| **Prediction** | Suggere de nouveaux theoremes | Genere-t-il des conjectures testables ? |
| **Naturalite** | S'integre dans la theorie existante | Les operations standard se generalisent-elles ? |
| **Calculabilite** | Peut etre evalue concretement | Peut-on le calculer sur des exemples ? |

### D.3 Anti-pattern : le concept fantome

Un concept qui NE satisfait AUCUN critere est un **concept fantome** —
une hallucination formalisee. L'eliminer immediatement.

Signes d'alerte :
- Le concept ne simplifie rien
- Aucun theoreme non-trivial n'en decoule
- Il est equivalent a une definition existante (renommage inutile)
- Sa definition est circulaire ou vacuitement satisfaite

---

<a name="phase-g"></a>
## Phase G — Garantie formelle (Lean 4)

**Objectif** : Verifier rigoureusement que le concept nouveau est coherent.

### G.1 Formalisation minimale

Avant d'investir dans une preuve complete :

1. **Ecrire la definition en Lean 4** — si elle ne type-checke pas,
   le concept est incoherent
2. **Enoncer les theoremes cles** — les ecrire comme `theorem ... := sorry`
3. **Prouver un cas simple** — si meme le cas k=1 echoue, reculer
4. **Verifier la compatibilite** avec Mathlib — le concept s'integre-t-il ?

### G.2 Boucle G-V-R (Aletheia)

Pour chaque theoreme impliquant le concept nouveau :

```
Generate : LLM propose une esquisse de preuve
Verify   : Lean 4 verifie chaque etape (ou script numerique)
Revise   : Si echec, revenir a l'etape qui a echoue
```

**Regle cardinale** : le verificateur a TOUJOURS raison. Si Lean dit non,
c'est non — meme si l'intuition dit oui.

### G.3 Test de robustesse du concept

- Permuter les hypotheses : la definition est-elle sensible a l'ordre ?
- Specialiser : le concept trivialise-t-il pour des cas connus ?
- Generaliser : peut-on affaiblir les hypotheses ?
- Dualiser : le concept "dual" est-il interessant ?

---

<a name="phase-e"></a>
## Phase E — Extension et generalisation

**Objectif** : Developper le concept en une mini-theorie.

### E.1 Arbre de generalisation

```
Concept nouveau C
    │
    ├── C en dimension superieure ?
    ├── C pour des structures plus generales (groupes → monoides → ...) ?
    ├── C "quantique" (non-commutatif) ?
    ├── C "stochastique" (version probabiliste) ?
    └── C dual ?
```

### E.2 Connexions

Pour chaque domaine D dans la bibliotheque Mathlib :
- Le concept C a-t-il un analogue naturel dans D ?
- Le foncteur "oubli" D → C est-il interessant ?
- Le concept C eclaire-t-il un probleme ouvert dans D ?

### E.3 Critere de publication (voir section 6)

---

## 3. OPERATEURS D'INNOVATION

Sept operateurs formels pour generer des concepts nouveaux a partir
de concepts existants. Chaque operateur a un **patron** et un **anti-patron**.

### OP1 : Compression (Addition → Multiplication)

**Patron** : Identifier une operation repetee et la nommer.
```
AVANT : a + a + a + ... + a  (n fois)
APRES : n × a
GAIN  : Passage de O(n) a O(1) dans l'enonce
```

**Anti-patron** : Nommer une operation qui n'apparait qu'une fois.

### OP2 : Inversion (Analyse → Synthese)

**Patron** : Si le probleme demande "A → B ?", essayer "B → A ?".
```
AVANT : Prouver que f(x) = y a une solution
APRES : Construire l'ensemble des y atteignables et montrer qu'il est tout
GAIN  : Parfois plus facile de construire la surjection inverse
```

**Anti-patron** : Inverser quand les deux sens sont aussi durs.

### OP3 : Parametrisation (Fixe → Dynamique)

**Patron** : Rendre un parametre fixe variable et etudier la famille.
```
AVANT : Prouver P(3)
APRES : Etudier P(t) pour t ∈ ℝ et montrer que P(3) decoule par continuite
GAIN  : Acces a l'analyse (derivees, limites, continuite)
```

**Anti-patron** : Parametriser quand le parametre n'a pas de sens naturel.

### OP4 : Categorification (Element → Structure)

**Patron** : Remplacer une egalite par un isomorphisme, un nombre par un objet.
```
AVANT : |A| = |B| (egalite de cardinalites)
APRES : A ≅ B (bijection explicite)
GAIN  : La bijection porte de l'information structurale
```

**Anti-patron** : Categorifier quand la structure supplementaire est vide.

### OP5 : Spectralisation (Direct → Transforme)

**Patron** : Passer a un espace de transformees (Fourier, Mellin, Z, ...).
```
AVANT : Etudier f(n) directement
APRES : Etudier F(s) = Σ f(n)n⁻ˢ et utiliser l'analyse complexe
GAIN  : Convolutions → produits, recurrences → equations fonctionnelles
```

**Anti-patron** : Spectraliser quand la transformee ne converge pas.

### OP6 : Probabilisation (Deterministe → Stochastique)

**Patron** : Remplacer "pour tout x" par "pour x aleatoire uniforme".
```
AVANT : Prouver ∀x, P(x)
APRES : Montrer P(P(x)) ≥ 1 et conclure que ∀x, P(x)
GAIN  : Acces aux outils probabilistes (esperance, concentration)
```

**Anti-patron** : Probabiliser quand aucune mesure naturelle n'existe.

### OP7 : Pontage (Domaine A ↔ Domaine B)

**Patron** : Etablir un dictionnaire formel entre deux domaines.
```
AVANT : Probleme P dans le domaine A (bloque)
APRES : Traduire P en probleme P' dans le domaine B (resolu), puis
        retraduire la solution de P' en solution de P
GAIN  : Acces aux outils d'un autre domaine
```

**Anti-patron** : Ponter quand la traduction perd l'information essentielle.

---

## 4. GARDE-FOUS ANTI-HALLUCINATION

### 4.1 Niveaux de confiance

Tout concept ou conjecture est etiquete :

| Niveau | Signification | Action |
|---|---|---|
| **L0 — Speculation** | Intuition non testee | Tester numeriquement |
| **L1 — Conjecture** | Verifie pour k ≤ 1000 | Ecrire la preuve |
| **L2 — Esquisse** | Preuve informelle complete | Formaliser en Lean |
| **L3 — Preuve** | Lean compile sans sorry | Publier |

### 4.2 Regles de securite

1. **Regle du verificateur** : Le verificateur (Lean / script) a TOUJOURS
   raison. L'intuition est faillible. Le `#check` ne l'est pas.

2. **Regle du contre-exemple** : Avant toute conjecture, chercher
   ACTIVEMENT des contre-exemples pendant au moins 30 minutes.

3. **Regle de la surprise** : Si un resultat est "trop beau", c'est
   probablement faux. Verifier avec acharnement.

4. **Regle du renommage** : Si votre "concept nouveau" est un renommage
   trivial d'un concept existant, l'eliminer. Chercher dans Mathlib.

5. **Regle de Lakatos** : Si une preuve echoue, c'est une INFORMATION.
   Le contre-exemple pointe vers le concept manquant.

### 4.3 Journal d'innovation

Tenir un journal structure pour chaque cycle B→R→I→D→G→E :

```markdown
## Cycle [N] — [Date]
### B : Contradictions identifiees
### R : Analogies trouvees (avec scores de qualite)
### I : Concepts candidats generes
### D : Concept retenu + justification
### G : Statut Lean (compile / sorry / erreur)
### E : Extensions identifiees
### DECISION : [CONTINUER / PIVOTER / ABANDONNER]
```

---

## 5. APPLICATION AU PROJET COLLATZ/ARTIN

### 5.1 Collatz Junction Theorem — sorry's restants

Les sorry's actuels dans la formalisation Lean suggerent des sites
potentiels d'innovation :

| Sorry | Contradiction sous-jacente | Operateur candidat |
|---|---|---|
| `gamma_ge_twentieth` | Precision numerique vs preuve formelle | OP3 (intervalle → borne) |
| `gap_implies_crystal_lower` | Estimation reelle → borne entiere | OP7 (pontage R→Z) |
| `crystal_bound_non_convergent` | Union de 3 lemmes | OP1 (compression) |
| `crystal_bound_convergent` | Factorisation → borne | OP4 (structure factorisee) |

### 5.2 Conjecture d'Artin

La conjecture d'Artin sur les racines primitives est un terrain ideal
pour le protocole BRIDGE :
- **B** : Contradiction entre "presque tous les nombres premiers" et
  "aucun cas prouve individuellement"
- **R** : Analogie avec la conjecture de Goldbach (presque-partout vs individuel)
- **I** : Melange theorie des nombres / geometrie algebrique / crible
- **D** : Concept a inventer pour passer du "generique" a l'"individuel"

### 5.3 Innovation potentielle : le "module cristallin"

Le concept de `crystalModule S k = 2^S - 3^k` dans notre formalisation est
deja un exemple de OP1 (compression) : au lieu de manipuler `2^S - 3^k`
partout, nous l'avons nomme et etudie comme un objet a part entiere.
L'etape suivante serait OP4 (categorification) : l'ensemble des
(S,k) tels que `crystalModule S k > 0` forme-t-il une structure
algebrique interessante ?

---

## 6. CRITERES DE PUBLICATION ET RECEPTION ACADEMIQUE

### 6.1 Qu'est-ce qui constitue une contribution publishable ?

Un concept mathematique nouveau assiste par LLM est publishable si :

1. **Il est CORRECT** (formalise en Lean 4, 0 sorry)
2. **Il est NON-TRIVIAL** (pas un renommage, pas une consequence immediate)
3. **Il est UTILE** (simplifie des preuves, unifie des resultats, predit)
4. **Il est REPRODUCTIBLE** (le protocole qui l'a genere est documente)
5. **Il est TRANSPARENT** (le role du LLM est explicitement decrit)

### 6.2 Venues de publication

| Venue | Focus | Niveau |
|---|---|---|
| *Experimental Mathematics* | Decouverte computationnelle | Q1 |
| *Journal of Automated Reasoning* | Preuve formelle | Q1 |
| *Artificial Intelligence* | Methodes IA | Q1 |
| *Mathematical Intelligencer* | Innovation + vulgarisation | Grand public |
| arXiv (math.CO, math.LO, cs.AI) | Preprints | Immediat |

### 6.3 Precedents

- **Davies et al. (Nature, 2021)** : IA decouvre des conjectures en theorie
  des noeuds, humains prouvent ensuite → publie dans Nature
- **FunSearch (Nature, 2024)** : LLM decouvre de nouvelles constructions
  pour les cap sets → publie dans Nature
- **LeanAgent (ICLR, 2025)** : 162 theoremes non prouves par des humains
  decouverts par IA → publie en conference top-tier
- **Tao + AlphaEvolve (arXiv, 2025)** : Fields Medalist utilise l'IA
  pour explorer 67 problemes ouverts → resultats publies

La communaute mathematique ACCEPTE les contributions assistees par IA
a condition que la preuve soit correcte et l'apport clairement attribue.

---

## 7. BIBLIOGRAPHIE

### Tradition classique
- Polya, G. (1945). *How to Solve It*. Princeton University Press.
- Polya, G. (1954). *Mathematics and Plausible Reasoning*. Vols. I-II. Princeton.
- Polya, G. (1962). *Mathematical Discovery*. Wiley.
- Hadamard, J. (1945). *The Psychology of Invention in the Mathematical Field*. Princeton.
- Poincare, H. (1908). *Science et Methode*. Flammarion.
- Wallas, G. (1926). *The Art of Thought*. Jonathan Cape.
- Lakatos, I. (1976). *Proofs and Refutations*. Cambridge University Press.

### Science cognitive de la creativite
- Boden, M. A. (1990/2004). *The Creative Mind: Myths and Mechanisms*. Routledge.
- Boden, M. A. (1998). "Creativity and Artificial Intelligence." *AI*, 103, 347-356.
- Gentner, D. (1983). "Structure-Mapping: A Theoretical Framework for Analogy." *Cog. Sci.*, 7(2), 155-170.
- Gentner, D. & Markman, A. B. (1997). "Structure Mapping in Analogy and Similarity." *Am. Psych.*, 52(1), 45-56.
- Fauconnier, G. & Turner, M. (2002). *The Way We Think: Conceptual Blending*. Basic Books.
- Lakoff, G. & Nunez, R. (2000). *Where Mathematics Comes From*. Basic Books.
- Csikszentmihalyi, M. (1996). *Creativity: Flow and the Psychology of Discovery*. HarperCollins.

### Innovation systematique
- Altshuller, G. S. (1984). *TRIZ: Theory of Inventive Problem Solving*.
- SIT — Systematic Inventive Thinking (derive de TRIZ).

### IA et mathematiques (2021-2026)
- Davies, A. et al. (2021). "Advancing Mathematics by Guiding Human Intuition with AI." *Nature*, 600, 70-74.
- Romera-Paredes, B. et al. (2024). "FunSearch: Mathematical Discoveries from Program Search with LLMs." *Nature*, 625, 468-475.
- Trinh, T. H. et al. (2024). "AlphaGeometry: Solving Olympiad Geometry." *Nature*, 625, 476-482.
- AlphaProof team (2025). "Olympiad-level formal reasoning with RL." *Nature*.
- Novikov, A. et al. (2025). "AlphaEvolve: A Coding Agent for Scientific Discovery." arXiv:2506.13131.
- Tao, T. et al. (2025). "Mathematical Exploration and Discovery at Scale." arXiv:2511.02864.
- Yang, K. et al. (2024). "LeanDojo: Theorem Proving with Retrieval-Augmented LMs." *NeurIPS 2023*.
- Song, P. et al. (2024). "Lean Copilot: LLMs as Copilots for Theorem Proving." arXiv:2404.12534.
- Kumaravel, A. et al. (2025). "LeanAgent: Lifelong Learning for Formal Theorem Proving." *ICLR 2025*.
- DeepSeek AI (2025). "DeepSeek-Prover-V2: Advancing Formal Reasoning." arXiv:2504.21801.
- Zheng, K. et al. (2024). "LLEMMA: An Open Language Model for Mathematics." *ICLR 2024*.

### Surveys
- Li, Y. et al. (2026). "AI for Mathematics: Progress, Challenges, and Prospects." arXiv:2601.13209.
- Liang, S. et al. (2024). "Mathematics and Machine Creativity." arXiv:2412.16543.
- Trinh, D. et al. (2026). "Towards Autonomous Mathematics Research." arXiv:2602.10177.
- Avigad, J. (2026). "Mathematicians in the Age of AI." arXiv:2603.03684.
- Sivakumar, J. A. et al. (2025). "Conjecturing: An Overlooked Step." arXiv:2510.11986.

### Collatz et approximation diophantienne
- Abascal, J. M. (2025). "Unfolding the Collatz Tree." *Contemporary Mathematics*.
- Cheng, C. (2024). "Operator Theory for the Collatz Conjecture." arXiv:2411.08084.
- Getachew & Assefa (2025). "Algorithmic Framework for Collatz Verification." arXiv:2501.04032.
- Elkies, N. & Bober, J. W. (2024). "Diophantine Equations: Open Problems." arXiv:2404.08518.

---

## ANNEXE A : TEMPLATE DE CYCLE D'INNOVATION

```markdown
# CYCLE D'INNOVATION N°[X]
## Date : [JJ/MM/AAAA]
## Probleme cible : [description en 1 ligne]

### PHASE B — Bilan structural
- Contradiction C1 : ...
- Contradiction C2 : ...
- Graphe conceptuel : [noeuds et aretes cles]
- Trous structurels identifies : ...

### PHASE R — Reseaux d'analogies
- Analogie A1 : [source] ↔ [cible], score [1-5]
  - Mapping : [objet1] ↔ [objet2], [relation1] ↔ [relation2]
  - Ou l'analogie se brise : ...
- Analogie A2 : ...

### PHASE I — Incubation
- Operateur(s) applique(s) : [OP1-OP7]
- Concept candidat CC1 : [definition informelle]
- Concept candidat CC2 : ...
- Illumination(s) apres incubation : ...

### PHASE D — Distillation
- Concept retenu : [nom + definition formelle]
- Score de qualite (criteres D.2) :
  - Compression : [oui/non]
  - Unification : [oui/non]
  - Prediction : [oui/non]
  - Naturalite : [oui/non]
  - Calculabilite : [oui/non]
- Score total : [X/5]
- Concept fantome ? : [oui/non]

### PHASE G — Garantie Lean 4
- Definition en Lean : [OK / erreur de type / ...]
- Theoreme principal : [compile / sorry / erreur]
- Cas simple prouve : [oui/non]

### PHASE E — Extension
- Generalisations identifiees : ...
- Connexions Mathlib : ...

### DECISION
[ ] CONTINUER : le concept est prometteur
[ ] PIVOTER : modifier l'approche (retour phase R ou I)
[ ] ABANDONNER : concept fantome, aucun gain
```

---

## ANNEXE B : PROMPT SYSTEMATIQUE POUR AGENT INNOVATEUR

A utiliser comme prompt systeme pour un agent LLM dedie a l'innovation :

```
Tu es un agent d'innovation mathematique. Ton role est de CREER
des concepts mathematiques nouveaux, pas de prouver des theoremes existants.

METHODE :
1. Analyse le probleme en termes de CONTRADICTIONS (qu'est-ce qui le rend dur ?)
2. Cherche des ANALOGIES STRUCTURALES dans 5+ domaines differents
3. Applique les 7 OPERATEURS D'INNOVATION :
   OP1-Compression, OP2-Inversion, OP3-Parametrisation,
   OP4-Categorification, OP5-Spectralisation, OP6-Probabilisation,
   OP7-Pontage
4. Pour chaque concept candidat, verifie les 5 CRITERES DE QUALITE :
   Compression, Unification, Prediction, Naturalite, Calculabilite
5. Elimine les CONCEPTS FANTOMES (renommages, definitions circulaires)

REGLE ABSOLUE : Tu generes des idees. Tu ne PROUVES rien.
La verification est faite par un autre agent (Lean 4 / script).
Tu as le droit d'halluciner des conjectures — c'est ton travail.
Mais etiquette chaque affirmation avec son niveau de confiance (L0-L3).

FORMAT DE SORTIE :
Pour chaque concept propose :
- NOM : [nom du concept]
- DEFINITION : [informelle, en 2-3 phrases]
- OPERATEUR : [OP1-OP7 utilise]
- ANALOGIE SOURCE : [d'ou vient l'idee]
- PREDICTION : [qu'est-ce que ce concept implique de nouveau ?]
- CONFIANCE : [L0/L1/L2/L3]
- TEST : [comment verifier si le concept est utile ?]
```

---

*Fin du protocole v1.0*
*Prochaine revision prevue apres le premier cycle d'application complet.*
