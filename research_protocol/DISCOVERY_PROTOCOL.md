# PROTOCOLE DE DECOUVERTE MATHEMATIQUE v2.2
## Pour la preuve de N₀(d) = 0 universel (Collatz Junction Theorem)
### Auteur : Eric Merle (assisté par Claude) — 4 mars 2026
### v2.2 : Enrichissement méthodologique (Aletheia, AlphaProof, Tao/AlphaEvolve, Lean4)

---

## OBJECTIF FONDAMENTAL (rappel permanent)

> **Prouver que N₀(d) = 0 pour TOUT k ≥ 1 → ∞.**
>
> Ceci n'est PAS un objectif computationnel limité à k=3..15.
> La preuve DOIT être universelle : un argument qui fonctionne
> pour k ARBITRAIRE, sans vérification cas par cas.

---

## SOURCES FONDATRICES

Ce protocole synthétise 14 méthodologies + 20 idées originales + garde-fous anti-hallucination :

### Sources classiques
1. **Pólya** — *How to Solve It* (1945) : 4 étapes + 67 heuristiques
2. **Lakatos** — *Proofs and Refutations* (1976) : dialectique conjecture-preuve-réfutation
3. **Hadamard** — *Psychology of Invention* (1945) : préparation-incubation-illumination-vérification
4. **Tao** — Blog *What's New* : spécialisation, généralisation, analogie, abstraction
5. **Houston** — *How to Think Like a Mathematician* : arsenal systématique de techniques

### Sources IA/Computationnelles (2024-2026)
6. **Aletheia/DeepMind** — *Towards Autonomous Mathematics Research* (2026) : boucle G-V-R
7. **AlphaProof/DeepMind** — *Olympiad-level formal reasoning with RL* (Nature 2025) : Lean4 + Test-Time RL
8. **FunSearch/DeepMind** — *Mathematical discoveries from program search* (Nature 2024) : pool évolutif
9. **AlphaGeometry 2** — *Gold-medalist geometry* (2025) : moteur symbolique + constructions auxiliaires LLM
10. **Tao + AlphaEvolve** — *Mathematical exploration at scale* (2025) : scoring conservateur + résultats négatifs
11. **Safe + Lean4** — Chain-of-thought → vérification formelle étape par étape (2025)
12. **OpenAI** — Preuve mathématique de l'inévitabilité des hallucinations (2025) : vérification >> génération

### Source spécifique au projet
13. **QUASAR** — Protocole Eric Merle (2026) : multi-lentille, niveaux de conviction, synthétiques calibrés
14. **Sessions 1-9** — Mécanismes I/II/III, TARGET -1, CRT anti-corrélation, identités u/w

---

## PROCESSUS FONDAMENTAL : BOUCLE G-V-R (v2.2)

> Inspiré d'Aletheia (DeepMind 2026), AlphaProof, et de la littérature anti-hallucination.
>
> **Principe cardinal** : "Le script est le juge, pas le raisonnement." (AlphaProof)
> Les hallucinations théoriques sont ACCEPTÉES tant que le juge computationnel les filtre.

### Boucle itérative pour CHAQUE investigation :

```
    ┌──────────────┐
    │  1. GENERATE  │  Formuler une conjecture/approche
    │  (créatif)    │  (hypothèse, borne, identité)
    └──────┬───────┘
           │
    ┌──────▼───────┐
    │  2. VERIFY    │  Tester avec un script INDÉPENDANT
    │  (le juge)    │  (force brute, k=3..15+, cas limites)
    └──────┬───────┘
           │
    ┌──────▼───────┐      ┌──────────────┐
    │  3. REVISE    │──NO──▶ 4. CIMETIÈRE  │
    │  (améliorer)  │      │  (documenter) │
    └──────┬───────┘      └──────────────┘
           │ OUI (partiel ou prometteur)
    ┌──────▼───────┐
    │  ITERATE      │  Maximum 5 itérations par branche
    └──────────────┘  Si aucun progrès → Cimetière
```

### Séparation Générateur/Juge (AlphaProof) :
- Le **Générateur** = raisonnement théorique, conjectures, analogies
- Le **Juge** = scripts Python, force brute, régression tests
- Le Juge a le DERNIER MOT. Toujours.
- Un résultat théorique sans validation numérique = [CONJECTURÉ], jamais [PROUVÉ]

### Pool évolutif (FunSearch) :
- La MIND_MAP maintient le pool des meilleures approches
- Chaque session sélectionne et améliore les branches les plus prometteuses
- Les branches mortes vont au Cimetière (sélection naturelle)
- Les nouvelles idées sont testées CONTRE les meilleures existantes

### Scoring conservateur (Tao/AlphaEvolve) :
- Toujours tester AU-DELÀ de la plage connue (pas seulement k=3..15)
- Arithmétique EXACTE (entiers Python, jamais de flottants pour les congruences)
- Détecter les "exploits" : résultats qui marchent pour de mauvaises raisons
- Documenter les résultats négatifs aussi soigneusement que les positifs

### Constructions auxiliaires (AlphaGeometry) :
- Quand l'approche directe échoue → introduire des objets auxiliaires
- Lemmes intermédiaires, substitutions, reformulations
- Notre TARGET -1 et la substitution B_j sont des exemples de ce principe

### Chain-of-Verification renforcée (v2.2) :
- Chaque résultat vérifié par **3 méthodes indépendantes** minimum
- Chaque MAILLON de la chaîne logique a son propre test
- Self-consistency : si 3 méthodes ne concordent pas → STOP

---

## NIVEAU 0 : AXIOMES INVIOLABLES (Socle dur)

Ces vérités ne peuvent JAMAIS être violées. Tout résultat qui les contredit est FAUX.

### 0.A Axiomes mathématiques
- **A1** : d = 2^S − 3^k, S = ⌈k·log₂3⌉. C'est une DÉFINITION, pas une approximation.
- **A2** : corrSum(A) = Σ_{j=0}^{k-1} 3^{k-1-j}·2^{A_j}. Formule EXACTE.
- **A3** : gcd(d, 6) = 1 pour tout k ≥ 3. Conséquence : AUCUN argument mod 2 ou mod 3 ne prouve N₀(d)=0.
- **A4** : corrSum est TOUJOURS impair. (Prouvé session 7, lemme algébrique.)
- **A5** : N₀(d) = 0 vérifié numériquement pour k = 3, ..., 15. Tout script doit confirmer.
- **A6** (v2.2) : L'objectif est k ≥ 1 → ∞. Tout argument limité à une plage FINIE de k est INSUFFISANT pour la preuve finale. Les arguments doivent être UNIFORMES en k.

### 0.B Axiomes méthodologiques (adaptés de QUASAR + v2.2)
- **M1** : Un pattern sur k=3..15 N'EST PAS une preuve. C'est une conjecture.
- **M2** : Toute borne doit être EFFECTIVE : donner un nombre, pas juste "petit".
- **M3** : Un argument modulaire EXIGE gcd(d,m) > 1 pour le modulus m utilisé.
- **M4** : La preuve est COUPABLE (fausse) jusqu'à démonstration du contraire.
- **M5** : Chaque idée théorique DOIT avoir un test numérique correspondant (Pont Théorie-Calcul).
- **M6** (v2.2) : Le script est le JUGE, pas le raisonnement. Séparation stricte Générateur/Juge. (AlphaProof)
- **M7** (v2.2) : Chaque résultat vérifié par ≥ 3 méthodes indépendantes. (Chain-of-Verification)

### 0.C Niveaux de conviction (promotion stricte)
Chaque résultat a un statut unique :
- **[CONJECTURÉ]** : observé numériquement, pas de preuve
- **[ESQUISSÉ]** : argument heuristique, failles possibles
- **[PROUVÉ_PARTIEL]** : preuve correcte mais hypothèses non vérifiées
- **[PROUVÉ]** : preuve complète, toutes hypothèses vérifiées
- **[VÉRIFIÉ_k=a..b]** : vrai numériquement dans cette plage exacte
- **[INVALIDÉ]** : était cru vrai, s'est révélé faux (GARDER l'historique)
- **[FERMÉ]** : approche testée, prouvée insuffisante, leçon documentée

Promotion : un résultat monte d'un niveau SEULEMENT avec une preuve ou vérification nouvelle.
Dégradation : un résultat descend IMMÉDIATEMENT si une faille est trouvée.

---

## PHASE 0 : CARTOGRAPHIE (Pólya : "Comprendre le problème")

### 0.1 Inventaire exhaustif
- [ ] Lister TOUS les objets mathématiques en jeu
- [ ] Pour chaque objet : définition formelle, propriétés connues, relations
- [ ] Construire le GRAPHE DE DÉPENDANCES (qui dépend de quoi)
- [ ] Identifier les INVARIANTS (propriétés qui ne changent pas)
- [ ] Identifier les DEGRÉS DE LIBERTÉ (ce qu'on peut faire varier)

### 0.2 Frontière du connu
- [ ] Tracer la LIGNE DE FRONT : qu'est-ce qui est prouvé vs conjecturé vs inconnu
- [ ] Pour chaque résultat connu : quelle méthode ? quelles limites ?
- [ ] Identifier les BARRIÈRES : pourquoi les méthodes existantes échouent

### 0.3 Reformulations
- [ ] Écrire le problème sous AU MOINS 5 formes différentes
- [ ] Pour chaque reformulation : quels outils deviennent disponibles ?
- [ ] Chercher la reformulation qui rend le problème "presque évident"

---

## PHASE 1 : SPÉCIALISATION (Tao : "Try simpler cases first")

### 1.1 Cas dégénérés
- [ ] k = 1, 2, 3 : calculer à la main, comprendre POURQUOI N₀(d) = 0
- [ ] d premier vs d composé : qu'est-ce qui change ?
- [ ] d petit (d = 5, 13) : énumérer tous les corrSum, voir la structure

### 1.2 Cas extrêmes
- [ ] Que se passe-t-il quand C/d → 0 ? (k grand)
- [ ] Que se passe-t-il quand C/d > 1 ? (k = 3, 5, 17)
- [ ] Le pire cas : quel k maximise C/d ? (k = 5, C/d = 2.69)

### 1.3 Analogie structurelle
- [ ] Le problème ressemble-t-il à un problème CONNU d'un autre domaine ?
- [ ] Sous-sommes dans Z/dZ — lien avec la cryptographie ?
- [ ] Sommes exponentielles — lien avec Weil, Deligne, Kloosterman ?
- [ ] Distribution des polynômes mod p — lien avec les courbes algébriques ?

---

## PHASE 2 : SCISSION (Pólya : "Décomposer en sous-problèmes")

### 2.1 Décomposition verticale (par la taille de k)
- [ ] k ≤ 68 : couvert par Simons-de Weger (externe)
- [ ] k ≥ 69, C/d < 1 : régime "cristallin" — argument probabiliste possible
- [ ] k ∈ {3, 5, 17} où C/d > 1 : cas STRUCTURELS — nécessitent preuve algébrique
- [ ] k → ∞ : limite asymptotique

### 2.2 Décomposition horizontale (par la structure de d)
- [ ] d premier : cas le plus simple, un seul modulus
- [ ] d = p·q : deux facteurs, exploiter le CRT
- [ ] d très composé : beaucoup de petits facteurs
- [ ] d avec facteur premier > C : le Peeling Lemma s'applique

### 2.3 Décomposition par la méthode
- [ ] Argument de TAILLE : corrSum ∈ [min, max], multiples de d dans l'intervalle
- [ ] Argument de CONGRUENCE : structure mod d exploitant 2^S ≡ 3^k
- [ ] Argument SPECTRAL : sommes exponentielles, Parseval, Fourier
- [ ] Argument COMBINATOIRE : structure des compositions, comptage
- [ ] Argument ALGÉBRIQUE : anneau Z/dZ, groupes multiplicatifs

---

## ARCHITECTURE MULTI-LENTILLE (adapté de QUASAR)

Attaquer N₀(d)=0 avec 4 lentilles INDÉPENDANTES. Un résultat n'est
crédible que s'il est vu par ≥ 2 lentilles.

### L1 — Algébrique : structure de Z/dZ, orbites de ⟨2⟩ et ⟨3⟩, CRT
### L2 — Analytique : caractères, Fourier, bornes de Weil, Baker
### L3 — Combinatoire : comptage, peeling, induction, automates
### L4 — Computationnelle : scripts exhaustifs, SAT/SMT, vérification k par k

**Convergence** : Si L1 dit "prime blocking" ET L4 confirme pour k=3..15 → [VÉRIFIÉ].
Si L2 donne une borne ET L3 la confirme par comptage → [PROUVÉ_PARTIEL].

### Pré-engagement (avant chaque investigation)
Avant de tester une piste, écrire dans le scratch :
1. L'hypothèse précise (formule)
2. Le critère de succès (borne, identité, calcul)
3. Le critère d'échec (quand abandonner)
Toute analyse post-hoc est marquée [EXPLORATOIRE].

### Synthétiques calibrés (terrain de vérité)
Pour tester un argument, construire un PROBLÈME MODIFIÉ où on CONNAÎT la réponse :
- Retirer la contrainte d'ordre strict → corrSum couvre Z/dZ (N₀ > 0). ✓ Vérifié.
- Changer d en d' = 2^S − 3^k ± 1 → N₀(d') peut être > 0. Comparer.
- Fixer k=3 (d=5) → on SAIT que N₀=0 avec 1 seule composition. Tester.
Si l'argument échoue sur le synthétique → il est FAUX.

---

## PHASE 3 : ATTAQUE PAR MÉCANISMES (v2.1 — Lakatos : conjecture → tentative → réfutation → amélioration)

> **Architecture de preuve** (découverte sessions 8-9) :
> La preuve procède par DISJONCTION sur la structure de d :
>   (I)  d premier → PRIME BLOCKING (exclusion de -1 par l'ordre strict)
>   (II) d composé, aucun facteur ne bloque → CRT ANTI-CORRÉLATION (couplage des poids)
>   (III) d composé, un facteur bloque → HYBRIDE (I + II)
>
> **Reformulation clé** : N₀(d)=0 ⟺ -1 ∉ Image(f) pour TOUT facteur premier de d.

### 3.1 Mécanisme I — PRIME BLOCKING (d premier)

**Théorème à prouver** : Pour tout k ≥ 3 où d est premier (p = d) :
  -1 ∉ Image(f),  où f(S) = Σ_{j=1}^{k-1} w^j · 2^{sort(S)_j} mod p

**Faits établis** (session 9) :
- [PROUVÉ k=3] Preuve algébrique complète (3 solutions, toutes position-incompatibles)
- [VÉRIFIÉ k=3,4,5,13] -1 toujours absent de l'image ordonnée
- [VÉRIFIÉ k=3,4,5] SANS ordre, -1 APPARAÎT → l'ordre strict est le SEUL mécanisme
- [VÉRIFIÉ] σ(u) = Σ u^j ≠ 0 (condition nécessaire) et u^k = 2^{k-S} (identité)
- [VÉRIFIÉ k=3,5] Anti-concentration parfaite quand C/p > 1.2

**Plan d'attaque** :
- [ ] (a) Weighted subset sum à poids rank-dépendants dans Z/pZ
- [ ] (b) Exploiter l'identité de clôture w^k = 2^{-S} mod p comme contrainte
- [ ] (c) Sommes exponentielles restreintes aux ensembles ordonnés (Weil/Deligne adaptées)
- [ ] (d) Analyser le cas u = w·2 mod p via la substitution B_j = A_j - j
- [ ] (e) Prouver que la distribution ordonnée est UNIFORME sur {1,...,p-1} sauf 0
- [ ] (f) Caractérisation géométrique de l'image ordonnée vs non-ordonnée

**Statut** : [AVANCÉ] Mécanisme IDENTIFIÉ et FORMALISÉ, preuve générale EN COURS.

### 3.2 Mécanisme II — CRT ANTI-CORRÉLATION (d composé)

**Théorème à prouver** : Pour tout k ≥ 3 où d = p₁ · p₂ · ... · pᵣ :
  (-1, -1, ..., -1) ∉ Image(φ),  où φ = (f₁, f₂, ..., fᵣ) : Comp → Z/p₁Z × ... × Z/pᵣZ

**Faits établis** (session 9) :
- [VÉRIFIÉ k=6..11] M[0][0] = 0 dans la matrice CRT jointe (anti-corrélation parfaite)
- [VÉRIFIÉ k=6..11] P(r₂=0 | r₁=0) = 0 (conditionnelle zéro)
- [VÉRIFIÉ k=6,10] Exclusion BI-DIRECTIONNELLE : chaque facteur exclut la cible de l'autre
- [VÉRIFIÉ k=12] d à 3 facteurs : anti-corrélation opère au niveau du 3ème facteur

**Plan d'attaque** :
- [ ] (d) Morphisme produit φ = (φ₁, φ₂) → caractériser Image(φ) dans Z/p₁Z × Z/p₂Z
- [ ] (e) Incompatibilité structurelle des poids w₁^j ≠ w₂^j ("orthogonalité")
- [ ] (f) Analyse des profils de position par facteur (positions bonnes pour p₁ ≠ pour p₂)
- [ ] (g) Prouver que la corrélation croisée exclut toujours le point (-1, -1)
- [ ] (h) Extension aux d à ≥ 3 facteurs (induction sur le nombre de facteurs)

**Statut** : [AVANCÉ] Mécanisme QUANTIFIÉ, preuve générale EN COURS.

### 3.3 Mécanisme III — HYBRIDE (d composé avec blocage partiel)

**Observation** (session 9) : Beaucoup de cas composites sont en fait HYBRIDES :
- k=7 : N₀(p₂=83) = 0 (prime blocking) + CRT
- k=8 : N₀(p₂=233) = 0 (prime blocking) + CRT
- k=11 : N₀(p₂=7727) = 0 (prime blocking) + CRT

**Stratégie** : Si au moins un facteur pᵢ a N₀(pᵢ)=0 (Mécanisme I),
  alors par CRT : N₀(d) ≤ N₀(pᵢ) = 0. Preuve terminée par Mécanisme I seul.

**Plan d'attaque** :
- [ ] Classifier tous les k ≤ 21 par type (I pur, II pur, III hybride)
- [ ] Pour chaque k composé : identifier si un facteur suffit (réduction à I)
- [ ] Quantifier la proportion de k où Mécanisme III s'applique

**Statut** : [CONJECTURÉ] Pour beaucoup de k composites, un facteur bloque déjà.

### 3.4 Front auxiliaire — Argument de taille (Steiner amélioré)
**Observation** : corrSum ∈ [3^k − 2^k, max_corrSum]
- [ ] Calculer min/max corrSum exactement pour chaque k
- [ ] Pour k=5 (d=13, C/d=2.69) : comprendre POURQUOI 0 est évité malgré C/d > 1

### 3.5 Front auxiliaire — Double Peeling BFS (session 8)
**Reformulation** : N₀(d) = #{chemins de longueur k-1 de c₀=1 à c_{k-1}=0}
- [ ] Forward BFS depuis c₀=1 (atteignabilité couche par couche)
- [ ] Backward BFS depuis c_{k-1}=0 (pré-images)
- [ ] Prouver que Forward∩Backward = ∅ au point de rencontre

---

## PHASE 4 : OUTILS SUR MESURE (Tao : "Abstraction + Construire ses propres outils")

### 4.1 Outils numériques à construire
- [ ] Script : distribution complète de corrSum mod d pour k petit
- [ ] Script : vérification CRT (N₀(d) vs C·∏(N₀(p)/C))
- [ ] Script : matrice de transfert et spectre pour d petit
- [ ] Script : "heat map" de corrSum mod d — visualiser la non-uniformité
- [ ] Script : recherche exhaustive de motifs/invariants dans les données

### 4.2 Invariants à découvrir
- [ ] corrSum(A) mod 2 = 1 toujours (connu) → quels autres invariants ?
- [ ] corrSum(A) mod 3 = 2^{A_{k-1}} mod 3 ∈ {1, 2} (connu)
- [ ] corrSum(A) mod 4, mod 8, ... → chaîne de congruences ?
- [ ] Paritédes positions : ∑(-1)^{pⱼ} a-t-il un lien avec corrSum mod d ?
- [ ] Invariant de Horner : y a-t-il une quantité conservée dans la récurrence ?

### 4.3 Transformations
- [ ] Involution sur Comp(S,k) : A → A' avec corrSum(A') = f(corrSum(A))
- [ ] Dualité : échanger les rôles de 2 et 3
- [ ] Complémentarité : A → (S-A) (positions complémentaires)
- [ ] Rotation : shift cyclique des positions

---

## PHASE 5 : INCUBATION + ILLUMINATION (Hadamard)

### 5.1 Changement de perspective
- [ ] Voir le problème comme un graphiste : dessiner la "carte" de corrSum
- [ ] Voir le problème comme un physicien : énergie, entropie, mécanique stat
- [ ] Voir le problème comme un informaticien : automates, langages formels
- [ ] Voir le problème comme un cryptographe : attaque par structure algébrique

### 5.2 Questions provocatrices
- [ ] POURQUOI 0 est-il spécial mod d ? Qu'a-t-il de différent des autres résidus ?
- [ ] Si N₀(d) > 0 pour un seul k, quel serait ce k ? Quelles propriétés aurait-il ?
- [ ] L'espace Comp(S,k) a une géométrie — quelle est la "distance" au résidu 0 ?
- [ ] corrSum est une fonction de {0,1}^{S-1} → Z/dZ — quelle est son image ?

---

## 20 IDEES ORIGINALES SPECIFIQUES AU PROBLEME

### Idée 1 : Le "théorème du résidu évité"
corrSum(A) ≡ 1 mod 2 toujours, et corrSum(A) ≢ 0 mod 3 toujours (Remark 2.5 du preprint).
**Hypothèse** : pour d = 2^S − 3^k, le résidu 0 est STRUCTURELLEMENT évité
par une chaîne de congruences analogues. Trouver d'autres résidus "interdits".

### Idée 2 : L'argument de comptage par orbites
L'action de la multiplication par 2 dans Z/dZ partitionne les résidus en orbites.
corrSum utilise des puissances de 2 → les valeurs de corrSum mod d sont
CONTRAINTES par la structure orbitale de ⟨2⟩ dans (Z/dZ)*.
**Action** : calculer les orbites de ⟨2⟩ mod d, voir si 0 est dans un "bassin" inaccessible.

### Idée 3 : La borne par l'énergie additive
Si l'énergie additive E(corrSum) = #{(A,B,C,D) : corrSum(A)+corrSum(B) = corrSum(C)+corrSum(D)}
est "petite" (par rapport à C²·d), alors corrSum est bien distribué mod d.
La structure de Horner CONTRAINT l'énergie additive.
**Action** : borner E(corrSum) via la structure récursive.

### Idée 4 : Le polynôme de Steiner
Définir P(x) = Σ_{A∈Comp} x^{corrSum(A)} (polynôme générateur formel).
N₀(d) = coefficient de x^0 dans P(x) mod (x^d − 1), évalué via les racines d-ièmes.
P(x) a une STRUCTURE MULTIPLICATIVE due au Horner.
**Action** : factoriser P(x) et exploiter sa structure.

### Idée 5 : L'inégalité de Turán pour corrSum
Si corrSum prend ses valeurs dans un ensemble "structuré" (progression géométrique pondérée),
l'inégalité de Turán (power sum method) donne des bornes sur la concentration.
**Action** : appliquer la méthode de Turán aux sommes de puissances de corrSum.

### Idée 6 : Le lemme de peeling SYMÉTRIQUE
Le Peeling Lemma pèle la DERNIÈRE position. Mais on peut aussi peler la PREMIÈRE.
Mieux : peler simultanément les deux extrémités (sandwich peeling).
Pour N₀(d), fixer A₀=0 et A_{k-1}, et montrer que le "tube" intermédiaire ne peut
pas atteindre 0 mod d.
**Action** : formaliser le double-peeling et calculer la borne résultante.

### Idée 7 : La descente modulaire
Si corrSum(A) ≡ 0 mod d, alors en particulier corrSum(A) ≡ 0 mod chaque facteur premier.
Mais aussi : corrSum(A)/d = n₀ (l'élément minimal du cycle), et n₀ satisfait
la DYNAMIQUE de Collatz. Donc n₀ est soumis à des contraintes supplémentaires
(parité des successeurs, convergence locale).
**Action** : extraire les contraintes dynamiques sur n₀ et montrer leur incompatibilité.

### Idée 8 : L'approche p-adique / valuations
v₂(corrSum) = 0 (toujours impair). Et v₂(d) = 0 (d impair).
Mais v_p(corrSum) pour p | d donne des contraintes. Si corrSum ≡ 0 mod p^a
(où p^a || d), la structure de la valuation p-adique de corrSum impose des
conditions sur les positions.
**Action** : analyser les valuations p-adiques de corrSum pour les premiers p | d.

### Idée 9 : L'automate de Horner
La récurrence c → 3c + 2^p mod d définit un automate à d états.
Le langage L = {séquences de positions menant à l'état 0} est un langage REGULIER.
Sa taille peut être bornée par les propriétés spectrales de l'automate.
**Action** : construire l'automate, analyser son graphe, prouver que l'état 0 est inaccessible en exactement k-1 pas depuis l'état 1.

### Idée 10 : Le principe de Pigeonhole modulaire inverse
Pour N₀(d) = 0, il suffit de trouver d ensembles S₁,...,S_d ⊂ Comp(S,k)
couvrant toutes les compositions, tels que S_r ⊂ {A : corrSum(A) ≡ r mod d}
avec r ≠ 0 pour chaque ensemble. Si |S₁|+...+|S_d| = C et aucun S₀ n'est nécessaire,
alors 0 est évité.
**Action** : construire cette partition explicitement via les orbites de ⟨2⟩·⟨3⟩ dans Z/dZ.

### Idée 11 : Théorie des codes — corrSum comme syndrome
corrSum(A) = Σ 3^{k-1-j}·2^{A_j} ressemble à un **syndrome** de code linéaire.
Les positions A_j sont les coordonnées du mot, les poids 3^{k-1-j}·2^{A_j}
forment une matrice de parité. N₀(d)=0 signifie que le syndrome 0 est
inaccessible — comme un code sans mot de poids k contenant le mot nul.
**Action** : reformuler en termes de codes sur Z/dZ, chercher une borne
type Gilbert-Varshamov inversée.

### Idée 12 : Information et entropie de corrSum
La distribution de corrSum mod d a une entropie H. Si H < log₂(d) − ε,
l'image de corrSum est "concentrée" et certains résidus sont évités.
L'entropie est liée à l'énergie additive (Idée 3) via Plünnecke-Ruzsa.
**Action** : calculer H(corrSum mod d) pour k=5..12, comparer à log₂(d),
estimer le nombre de résidus manquants.

### Idée 13 : Géométrie tropicale et valuations
Définir val_p(corrSum) pour chaque p | d. Les valuations vivent dans Z^r
(r = nombre de facteurs premiers). L'image de Comp(S,k) sous val dessine
un **polytope tropical**. Si ce polytope ne contient pas le point (v_p(d))_{p|d},
alors N₀(d) = 0.
**Action** : calculer l'enveloppe tropicale pour k=6 (d=5×59).

### Idée 14 : Dynamique ergodique de l'automate de Horner
L'itération c ↦ 3c + 2^q mod d est un système dynamique sur Z/dZ.
Pour k-1 pas avec des "inputs" 2^q croissants, c'est un système
**non-autonome** (le forçage change à chaque pas). La théorie du
**mixing** donne des bornes sur le temps nécessaire pour atteindre un état.
Si l'automate ne "mixe" pas assez vite pour atteindre 0 en k-1 pas → N₀=0.
**Action** : estimer le temps de mixing de l'automate de Horner mod d.

### Idée 15 : Induction forte sur la structure de d
Au lieu d'une induction sur k, induire sur la **structure arithmétique de d** :
- Cas de base : d premier (prime blocking, potentiellement prouvable)
- Pas inductif : si N₀(p)=0 ou N₀(q)=0 pour les facteurs, alors N₀(pq)=0
- Si les deux permettent des solutions : prouver l'incompatibilité CRT
  (la paire (0,0) est toujours absente).
**Action** : formaliser la disjonction prime_blocking ∨ CRT_incompatibilité
et prouver chaque branche séparément.

### Idée 16 : Analyse de Fourier non-abélienne
Le groupe (Z/dZ)* agit sur les compositions par multiplication des poids.
Au lieu de la transformée de Fourier standard (caractères additifs),
utiliser les **représentations** du groupe multiplicatif. L'action du
sous-groupe ⟨2⟩ décompose l'espace en orbites → contraintes spectrales
plus fines que Parseval.
**Action** : décomposer F(t) par orbites de ⟨2⟩ et ⟨3⟩ dans (Z/dZ)*.

### Idée 17 : Bootstrapping computationnel + SAT/SMT solvers
Reformuler "corrSum ≡ 0 mod d" comme un problème SAT sur les bits des positions.
Pour k fixé, c'est une formule booléenne. Un solver SAT peut prouver
l'insatisfiabilité et fournir un **certificat vérifiable** (preuve DRAT).
**Action** : encoder le problème en CNF pour k=5..10 et extraire la structure
des certificats d'insatisfiabilité.

### Idée 18 : Reformulation TARGET -1 (session 9 — DÉCOUVERTE MAJEURE)
Séparer le premier terme (j=0, fixé à w⁰·2⁰=1) des k-1 termes restants.
N₀(p) = 0 ⟺ -1 ∉ Image(f) où f(S) = Σ_{j=1}^{k-1} w^j · 2^{sort(S)_j} mod p.
La cible n'est plus 0 mais **-1**. Avantage : f est maintenant une somme de k-1 termes
à poids rank-dépendants, plus facile à analyser.
**Vérifié** : k=3 (p=5), k=4 (p=47), k=5 (p=13), k=13 (p=502829).
**Synthétique calibré** : SANS ordre strict, -1 APPARAÎT pour k=3,4,5 → l'ordre est LE mécanisme.
**Action** : prouver que l'image ordonnée exclut -1 pour tout p de la forme d(k) premier.

### Idée 19 : Exclusion bi-directionnelle CRT (session 9 — DÉCOUVERTE)
Pour d = p₁·p₂ composé, le même ensemble de positions doit satisfaire
SIMULTANÉMENT : Σ w₁^j·2^{A_j} ≡ -1 mod p₁ ET Σ w₂^j·2^{A_j} ≡ -1 mod p₂.
Les poids w₁^j ≠ w₂^j créent des "directions orthogonales" dans le produit Z/p₁Z × Z/p₂Z.
Les positions "bonnes" pour p₁ sont systématiquement "mauvaises" pour p₂.
**Vérifié** : M[0][0] = 0 pour TOUS k=6..11 (anti-corrélation parfaite).
**Action** : formaliser l'orthogonalité des poids et prouver l'exclusion pour d composite arbitraire.

### Idée 20 : Substitution B_j et identité de clôture (session 9)
Poser B_j = A_j − j (composition → ensemble non-décroissant dans [0, S-k]) et u = w·2 mod p.
La w-somme devient une somme en u^j · 2^{B_j} avec contrainte B_j non-décroissante.
**Identité universelle** : u^k = 2^{k-S} mod p (toujours).
**Condition nécessaire** : σ(u) = Σ_{j=0}^{k-1} u^j ≠ 0 mod p (vérifiée pour tout k testé).
**Cas spécial** : k=3 donne u = -1 mod 5, provoquant des annulations par paires.
**Action** : exploiter l'identité u^k = 2^{k-S} pour contraindre l'image de la somme ordonnée.

---

## PHASE 6 : VÉRIFICATION RIGOUREUSE (Pólya : "Look Back")

### 6.1 Avant de revendiquer un résultat
- [ ] Le résultat est-il cohérent avec TOUTES les données numériques ?
- [ ] Les cas spéciaux (k=3, k=5 avec C/d>1) sont-ils couverts ?
- [ ] La preuve utilise-t-elle des hypothèses non démontrées ?
- [ ] Un contre-exemple est-il IMAGINABLE ? Si oui, pourquoi n'existe-t-il pas ?

### 6.2 Renforcement
- [ ] Le résultat peut-il être RENFORCÉ ? (borne plus serrée, cas plus général)
- [ ] La méthode s'applique-t-elle à d'AUTRES problèmes ?
- [ ] Peut-on formaliser en Lean 4 ?

---

## PHASE 7 : GARDE-FOUS (Anti-hallucination, Anti-régression, Red Team)

> *"La moitié de la recherche est de ne pas se tromper soi-même."* — Feynman

### 7.1 Anti-hallucination : 5 tests obligatoires

Avant d'accepter TOUT résultat (numérique ou théorique) :

1. **Test du contre-exemple fabriqué** : Modifier légèrement les hypothèses
   (ex: retirer la contrainte d'ordre, changer d en d±1) et vérifier que
   le résultat CESSE d'être vrai. Si le résultat tient encore → il est
   probablement trivial ou l'argument est faux.

2. **Test de la boîte noire** : Recalculer le résultat avec un script
   INDÉPENDANT (autre algorithme, autre langage si possible). Deux codes
   donnant le même résultat ≠ garantie mais un code donnant un résultat
   différent = alarme immédiate.

3. **Test de la limite** : Vérifier les cas limites k=3 (trivial) et
   k→∞ (asymptotique). Si le résultat ne couvre pas les deux, il est
   incomplet. Si une borne diverge quand k→∞, elle est probablement
   inutile.

4. **Test du sceptique** : Formuler l'argument le plus fort CONTRE le résultat.
   Jouer l'avocat du diable. Identifier LE maillon le plus faible de la chaîne
   logique et l'attaquer directement.

5. **Test du gcd(d,m)** : Pour tout argument modulaire, vérifier immédiatement
   que le modulus divise d. (Leçon session 7 : les preuves mod 2 et mod 3
   sont correctes mais inutiles car gcd(d,6)=1.)

### 7.2 Anti-régression : le filet de sécurité

1. **Suite de tests immuables** : Maintenir un script `regression_test.py`
   vérifiant TOUS les résultats prouvés. Le lancer au début de chaque session.
   Si un test échoue → STOP, investiguer avant de continuer.

2. **Registre des résultats** : Chaque résultat prouvé a un statut :
   - [PROUVÉ] : preuve complète, vérifiée, pas d'hypothèse cachée
   - [VÉRIFIÉ k=a..b] : vrai numériquement dans cette plage
   - [CONJECTURÉ] : pas de preuve, pas de contre-exemple
   - [INVALIDÉ] : était cru vrai, s'est révélé faux (garder l'historique !)

3. **Delta de session** : Chaque log de session commence par :
   - Qu'est-ce qui a CHANGÉ depuis la dernière session ?
   - Quels résultats sont TOUJOURS VALIDES ?
   - Quels résultats ont été INVALIDÉS ou AFFINÉS ?

4. **Invariants structurels** : Certaines vérités ne changent jamais :
   - d = 2^S − 3^k, S = ⌈k·log₂3⌉
   - corrSum est TOUJOURS impair
   - gcd(d, 6) = 1 pour tout k ≥ 3
   - N₀(d) = 0 vérifié numériquement pour k=3..15
   Toute manipulation qui viole un invariant structural est FAUSSE.

### 7.3 Red Team : attaquer ses propres résultats

Après chaque avancée significative, appliquer le protocole Red Team :

1. **Étape 1** : Identifier la revendication centrale
2. **Étape 2** : Lister les 3 hypothèses les plus fragiles
3. **Étape 3** : Pour chaque hypothèse, construire un scénario où elle échoue
4. **Étape 4** : Tester numériquement ce scénario
5. **Étape 5** : Si le scénario produit un contre-exemple → la revendication
   est fausse. Sinon → documenter pourquoi le scénario est impossible.

### 7.4 Signaux d'alarme (STOP immédiat)

Si l'un de ces signaux apparaît, ARRÊTER et investiguer :
- 🔴 Un résultat "prouvé" échoue sur un nouveau cas test
- 🔴 Deux scripts indépendants donnent des résultats différents
- 🔴 Un argument utilise gcd(d,m)=m mais m ne divise pas d
- 🔴 Une borne asymptotique diverge au lieu de converger
- 🔴 Un résultat est "trop beau" : il marchepour des raisons triviales
- 🔴 L'approche fonctionne aussi si on retire une hypothèse clé

---

## PHASE 8 : CRITÈRES DE CONVERGENCE (v2.1 — Nouveau)

> *Quand saurons-nous que la preuve est "presque là" ?*

### 8.1 Jalons vers la preuve complète

| Jalon | Description | Statut |
|-------|-------------|--------|
| J1 | Preuve k=3 (d=5 premier) | ✅ PROUVÉ (session 9) |
| J2 | Preuve pour AU MOINS 2 autres k premiers | ❌ EN COURS |
| J3 | Preuve générale Mécanisme I (tout d premier) | ❌ EN COURS |
| J4 | Preuve M[0][0]=0 pour d = p₁·p₂ arbitraire | ❌ EN COURS |
| J5 | Preuve Mécanisme II général (CRT anti-corrélation) | ❌ EN COURS |
| J6 | Unification I+II+III : N₀(d)=0 pour tout k ≥ 3 | ❌ OBJECTIF FINAL |

### 8.2 Indicateurs de proximité
- **Densité des preuves** : # de k avec preuve complète / # de k testés
- **Profondeur mécanistique** : le "pourquoi" est-il compris à chaque niveau ?
- **Généricité** : l'argument fonctionne-t-il pour k ARBITRAIRE ou juste des cas spécifiques ?
- **Indépendance des vérifications** : ≥ 2 méthodes confirment chaque résultat ?

### 8.3 Critères d'arrêt (quand changer de stratégie)
- Si après 3 sessions consécutives un mécanisme ne progresse PAS → réévaluer
- Si un contre-exemple structurel est trouvé → STOP, réévaluer la conjecture
- Si le seul progrès est computationnel (k plus grand) sans insight → changer d'angle

---

## MÉTA-RÈGLES (v2.2 — enrichies)

### Règles originales (v1.0-v2.0)
1. **JAMAIS de calcul sans compréhension** — chaque nombre doit avoir un sens
2. **TOUJOURS chercher le POURQUOI** — pas seulement le QUOI
3. **ALTERNER zoom/dézoom** — détails techniques ↔ vue d'ensemble
4. **VALORISER les échecs** — chaque approche qui échoue INFORME sur la structure (Tao)
5. **DOCUMENTER systématiquement** — chaque observation, même mineure
6. **CROISER les perspectives** — au moins 3 points de vue sur chaque question
7. **CONSTRUIRE ses outils** — ne pas attendre que les outils existent
8. **ATTAQUER ses propres résultats** — Red Team systématique (Phase 7.3)
9. **VÉRIFIER les prérequis modulaires** — gcd(d,m) avant tout argument mod m
10. **UN résultat = TROIS vérifications** — 3 méthodes indépendantes (v2.2, renforcé)
11. **NE JAMAIS extrapoler** — un pattern sur k=3..15 N'EST PAS une preuve
12. **PREFERER la preuve qui explique** — une preuve qui dit POURQUOI N₀=0
    vaut plus qu'une preuve technique qui ne donne aucune intuition

### Règles v2.2 (inspirées de la littérature 2024-2026)
13. **LE SCRIPT EST LE JUGE** — le raisonnement propose, le calcul dispose (AlphaProof)
14. **BOUCLE G-V-R bornée** — Generate → Verify → Revise, max 5 itérations (Aletheia)
15. **SCORING CONSERVATEUR** — tester AU-DELÀ de la plage connue, détecter les exploits (Tao)
16. **ARITHMÉTIQUE EXACTE** — jamais de flottants pour les congruences (Tao/AlphaEvolve)
17. **CONSTRUCTIONS AUXILIAIRES** — quand l'approche directe échoue, introduire des objets nouveaux (AlphaGeometry)
18. **POOL ÉVOLUTIF** — maintenir et faire évoluer les meilleures approches (FunSearch)
19. **UNIVERSALITÉ PERMANENTE** — chaque argument doit viser k ≥ 1 → ∞, pas une plage finie
20. **RÉSULTATS NÉGATIFS = RÉSULTATS** — documenter avec la même rigueur (Tao)

---

## CHECKLIST DE SESSION (v2.2 — enrichie)

### Au début :
1. Relire la carte mentale (MIND_MAP.md)
2. Relire ce protocole (sections pertinentes)
3. Lancer `regression_test.py` — vérifier que TOUT est encore valide
4. Écrire le "delta" : qu'est-ce qui a changé depuis la dernière session ?
5. Choisir UN front d'attaque (pas deux), avec PRÉ-ENGAGEMENT :
   - Hypothèse précise
   - Critère de succès
   - Critère d'échec (quand abandonner)

### Pendant :
6. Appliquer la boucle G-V-R : Generate → Verify (script) → Revise
7. Pour chaque résultat : appliquer les 5 tests anti-hallucination (Phase 7.1)
8. Pour chaque résultat : vérifier par ≥ 3 méthodes indépendantes (M7)
9. Documenter résultats positifs ET négatifs au fil de l'eau (méta-règle 20)
10. Écrire dans un fichier scratch AVANT de mettre à jour les documents principaux
11. Vérifier que chaque argument vise l'UNIVERSALITÉ (k → ∞), pas une plage finie
12. Budget G-V-R : max 5 itérations par branche, sinon → Cimetière

### À la fin :
13. Mettre à jour MIND_MAP + PROOF_SKETCH + ce protocole si nécessaire
14. Lancer `regression_test.py` à nouveau — rien ne doit avoir régressé
15. Identifier la prochaine action la plus prometteuse
16. Écrire le research log de session (obligatoire)
17. Mettre à jour le Cimetière avec les approches fermées dans cette session

---

## CIMETIÈRE DES APPROCHES (pour ne pas refaire les mêmes erreurs)

| Approche | Session | Pourquoi elle échoue | Leçon retenue |
|----------|---------|---------------------|---------------|
| Mod 3 seul | 6 | gcd(d,3)=1 | Vérifier gcd(d,m) AVANT |
| Spectrale (T_ext) | 7 | Nilpotente | Ordre strict + poids = cancellation |
| Comptage pur | 7 | comps >> multiples | Croissance exponentielle empêche |
| L₁ character sums | 7 | ratio 5-14× | Outliers \|F(t)\| trop grands |
| Cauchy-Schwarz | 7 | ratio 164× | Parseval exact mais C-S trop faible |
| Modulus universel | 7 | GCD(d(k))=1 | Pas de structure modulaire globale |
| CRT naïf (∏N₀(pᵢ)=0) | 8 | N₀(pᵢ)>0 pour k≥6 | Tous les premiers permettent des solutions |
| Invariants universels mod m | 7-8 | Rien au-delà mod 2+3 | Le blocage est SPÉCIFIQUE à d, pas universel |
| Induction sur k | 9 | p change à chaque k | Corps différents, pas de transfert inductif |
| Bornes sur corrSum seules | 9 | Bornes trop larges | Exclure 0 requiert plus qu'un encadrement |
| Fourier + Parseval (borne √C) | 7-8 | √C >> 1 toujours | Barrière √C infranchissable par Fourier seul |
| Peeling simple (1 variable) | 8 | Borne C/d sur N₀(p) | Insuffisant quand C/d > 1 (k=3,5,17) |

> **Règle** : Avant de tester une approche, vérifier ce cimetière.
> Si l'approche y figure, il faut une NOUVELLE idée pour la rendre viable.
>
> **Règle v2.1** : Si une approche échouée est PARTIELLEMENT relancée par une
> nouvelle idée (ex: CRT naïf → CRT anti-corrélation), documenter la DIFFÉRENCE.
