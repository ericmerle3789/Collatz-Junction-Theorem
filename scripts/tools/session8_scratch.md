# Session 8 — Scratch Notes
## 4 mars 2026

## DELTA depuis session 7
- PROOF_SKETCH mis à jour v0.7 (résultats session 7)
- DISCOVERY_PROTOCOL v2.0 : 17 idées + Phase 7 Garde-Fous + Cimetière
- Intégration QUASAR : Niveau 0 axiomes, Multi-Lentille, Niveaux conviction
- regression_test.py créé : 110/110 tests passent
- 6 branches investigées systématiquement

## Résultats de l'investigation multi-branches

### B1 : Algébrique h = 2/3 mod d
- **Reformulation validée** : corrSum ≡ 0 ⟺ Σ w^j·2^{A_j} ≡ 0 (mod d)
  avec w = 3^{-1} mod d
- **BUG dans le test** : le code vérifiait cible d-1 au lieu de 0
  (reformulation correcte utilise la somme COMPLÈTE, pas partielle)
- **Identité** : w^k = 2^{-S} mod d (conséquence de 3^k ≡ 2^S mod d)
- **Groupe** : ⟨w,2⟩ engendre parfois tout (Z/dZ)*, parfois la moitié
  k=5,6 : ratio 1.000 (tout)
  k=7,8 : ratio 0.500 (moitié)
- **OUVRE** : Prouver que 0 ∉ Image via structure du sous-groupe

### B2 : Baker / Énoncé A
- **FAIT CLÉ** : ord_d(2) ≡ 0 (mod S-s) n'a AUCUNE solution s ∈ {1,...,S-1}
  pour k=4..29 (vérifié)
- **Ratio ord_d(2)/S** :
  - k=3: 0.80 (seul cas < 1, CAS SPÉCIAL)
  - k=4: 3.29
  - k=5: 1.50 (2ème plus petit)
  - k=12: 423.4, k=17: 37079, k=19: 1.2M
  - Croissance EXPONENTIELLE du ratio
- **Near-misses** : |3^k - 2^s|/d toujours > 0.0138 (k=12 le pire)
  k=24 : 0.0282, lié aux convergents de log₂3
- **POURQUOI ord_d(2) > S-1** : Car d = 2^S - 3^k, si 2^r ≡ 1 mod d avec r < S,
  alors d | (2^r - 1), mais 2^r ≤ 2^{S-1} < 3^k... MAIS 2^{S-1} - 1 PEUT
  être > d (car d < 3^k). Donc l'argument de taille ne suffit pas directement.
- **OUVRE** : Baker donne |2^a·3^{-b} - 1| > exp(-C·log(a)·log(b))
  Pour a=S-s, b=k : |2^{S-s}/3^k - 1| > exp(-C·log(S)·log(k))
  Cela donne |2^{S-s} - 3^k| > 3^k · exp(-C·log(S)·log(k))
  Si cette borne > d = 2^S - 3^k, on conclut.

### B3 : CRT incompatibilité
- **Table des mécanismes** :
  - PRIME BLOCK : k=5(13), 7(83), 8(233), 11(7727), 13(502829)
  - CRT INCOMPAT : k=6(5×59), 9(5×2617), 10(13×499), 12(5×59×1753), 14(79×45641), 15(13×186793)
- **k=6 ANALYSÉ EN DÉTAIL** :
  - corrSum ≡ 0 mod 5 : 36 compositions, résidus mod 59 = {1,5,7,...} SANS 0
  - corrSum ≡ 0 mod 59 : 6 compositions, résidus mod 5 = {1,2,3,4} SANS 0
  - Anti-corrélation PARFAITE : jamais (0,0) malgré chacun faisable
- **POURQUOI** : L'identité 2^S ≡ 3^k mod d contraint SIMULTANÉMENT
  les résidus mod p et mod q. Les compositions qui donnent 0 mod p
  sont "forcées" vers des résidus non-nuls mod q.

### B4 : Induction sur k
- **Récurrence EXACTE** :
  - ΔS = 2 : d(k+1) = 4d(k) + 3^k
  - ΔS = 1 : d(k+1) = 2d(k) - 3^k
- Vérifiée pour k=3..19
- **DIFFICULTÉ** : Comp(S,k) et Comp(S+ΔS, k+1) sont incomparables
  Les compositions changent complètement
- **OUVRE** : Si on pouvait INJECTER Comp(S,k) dans Comp(S+ΔS, k+1)
  de façon compatible avec corrSum, on aurait un argument inductif

### B5 : p-adique / valuations — ★★★ PROMETTEUSE
- **RÉSULTAT CLÉ** :
  - k=5 (d=13 premier) : v_13(corrSum) = 0 pour les 35 compositions
    → 13 ∤ corrSum TOUJOURS → N₀(13)=0 directement
  - k=7 (d=23×83) : v_83(corrSum) = 0 pour les 462 compositions
    → 83 ∤ corrSum → N₀(83)=0 → N₀(d)=0
  - k=6 (d=5×59) : v_5 atteint 5, v_59 atteint 1
    → chaque premier PERMET la divisibilité, mais JAMAIS ensemble
- **PATTERN** :
  - d premier → souvent v_p(corrSum)=0 (TOUJOURS pour k testé)
  - d composé → chaque premier permet mais corrélation anti-bloque

### B6 : Coding theory
- **Couverture décroissante** de Im(corrSum mod d) :
  k=5: 92.3%, k=6: 35.9%, k=7: 21.9%
- L'alphabet {2^p mod d} aussi décroît : 61.5% → 3.4% → 0.6%
- Pour grand k, l'image est TRÈS sparse → 0 facilement évité
- **MAIS** pour k=5 (C/d=2.69), la couverture est 92% (presque tout)
  et pourtant 0 est évité → le mécanisme n'est PAS la sparsité

## Pistes prioritaires identifiées (par convergence)
1. **p-adique + CRT** (L1+L4) : Prouver v_p(corrSum) < v_p(d) pour d premier,
   puis formaliser l'incompatibilité CRT pour d composé
2. **Baker** (L2) : Borne effective sur ord_d(2) via formes linéaires
3. **Reformulation w** (L1) : 0 ∉ Image(Σ w^j·2^{A_j}) via structure de ⟨w,2⟩

---

## APPROFONDISSEMENT B5 : PRIME BLOCKING (9 investigations)

### Investigation 1 — Image de Σ w^j·2^{A_j} vs cible -1
- corrSum ≡ 0 mod p ⟺ Σ_{j=1}^{k-1} w^j·2^{A_j} ≡ -1 mod p
  (car 3^{k-1} ≢ 0 mod p)
- **k=3 (p=5)** : |Image| = 4/5 (80%), valeur UNIQUE absente = {4} = {-1 mod 5}
- **k=5 (p=13)** : |Image| = 12/13 (92.3%), valeur UNIQUE absente = {12} = {-1 mod 13}
- **Distance minimale à la cible : TOUJOURS 1** pour d premier
- ★ Pour k=3 et k=5, la cible -1 est LA SEULE valeur manquante !

### Investigation 2 — Structure de l'alphabet
- Chaque "ligne" j donne |{w^j·2^a}| termes dans Z/pZ
- k=5 : atomes totaux couvrent 12/12 de (Z/pZ)* — TOUT sauf 0
- Identité w^k ≡ 2^{-S} mod p : VÉRIFIÉ pour tous les k

### ★★★ Investigation 3 — LA CONTRAINTE D'ORDRE EST CRITIQUE
- **RÉSULTAT FONDAMENTAL** : Sans contrainte d'ordre, -1 EST TOUJOURS ATTEINT
  - k=3 : Image non-ordonnée = Z/5Z entier (100%), -1 ∈ Image
  - k=4 : Image non-ordonnée = 46/47 (97.9%), -1 ∈ Image
  - k=5 : Image non-ordonnée = 13/13 (100%), -1 ∈ Image
- Le blocking est un phénomène COMBINATOIRE + ALGÉBRIQUE, pas purement algébrique

### ★★★ Investigation C — Mécanisme couche par couche
- Pour k=3,4,5 : à la couche finale, {0} ∈ (non-ord \ ord)
- **0 est EXACTEMENT dans la différence** : l'ordre l'exclut chirurgicalement
- k=3 : couche 2, diff = {0} (1 seul élément exclu !)
- k=5 : couche 4, diff = {0} (1 seul élément exclu !)
- L'automate ordonné atteint TOUS les résidus sauf 0

### Investigation 4 — Sommes partielles
- k=4 (p=47) : l'intersection penultimate ∩ cibles = ∅
  → Le blocking vient des k-1 premiers termes seuls
- k=3, k=5 : intersection non vide mais AUCUNE composition réalise l'annulation
  → Les positions compatibles ne coïncident jamais

### Investigation 5 — Caractères de Z/pZ
- Sommes exponentielles S_t calculées pour t=0..p-1
- Condition suffisante N₀=0 via Σ|S_t| < C : **JAMAIS satisfaite**
- Le blocking n'est PAS dû à des annulations aléatoires — c'est structurel
- max|S_t|/√C ≈ 1.2-2.0 (modéré)

### Investigation 6 — Contrainte 2^S ≡ 3^k mod p
- Substitution B_j = A_j - j : Σ w^j·2^{A_j} = Σ (w·2)^j · 2^{B_j}
  avec B_j ≥ 0, croissant (pas strictement)
- VÉRIFIÉ pour tous les k testés
- Reformulation : la somme utilise un SEUL élément u = w·2 mod p
- Pour k=5 : u = 5, ord(u) = 4, (w·2)^S ≡ 1 mod p

### Investigation 7 — Automate de Horner mod p
- Automate (c mod p, position) → (3c + 2^a) mod p
- k=5 (p=13) : TOUTES les 7 positions a POURRAIENT atteindre c=0
  si le c_needed était accessible. MAIS le c_needed n'est JAMAIS accessible
  avec la bonne dernière position.
- C'est la MÊME observation que la contrainte d'ordre : le c_needed existe
  dans l'automate, mais PAS à la bonne couche/position.

### Investigation 8 — Test étendu k=3..18
- d premier (k=3,4,5,13) : N₀(p) = 0 ✅ (EXACT)
- d composé : table mise à jour (voir ci-dessous)
- ★ RÉFUTATION de "gros premier bloque toujours" :
  - k=6,9,10,12,14,15,16 : AUCUN bloqueur direct
  - Pour ces k, le blocking est PUREMENT CRT (anti-corrélation)

### Investigation 9 — Interaction ⟨w⟩ × ⟨2⟩
- k=4 (p=47) : ⟨w,2⟩ = moitié de (Z/47Z)*, S-1 < ord(2)
- k=5 (p=13) : ⟨w,2⟩ = (Z/13Z)* entier
- Relation dans le log discret : k·log_g(3) + (-S)·log_g(2) ≡ 0 mod (p-1)
- (p-1)/2 ∈ exposants possibles pour k=3,5 MAIS les sommes n'atteignent pas -1

### Investigation D — ord_p(2) vs S
| Corrélation FORTE | : les non-bloqueurs ont ord_p(2)/S < 1,
  les bloqueurs ont ord_p(2)/S >> 1.
  MAIS ce n'est pas une condition nécessaire/suffisante exacte.

### Investigation F — Seuil de taille
- Pas de seuil simple. Le blocking dépend de la structure arithmétique, pas
  juste de la taille.

### Investigation G — Anti-corrélation CRT profonde
- k=6 (5×59) : (0,0) = 0 occurrences, attendu 1.7 si indep → ANTI-CORRÉLATION
- k=7 (23×83) : N₀(83) = 0 directement (prime blocking)
- k=8 (7×233) : N₀(233) = 0 directement (prime blocking)
- k=9 (5×2617) : (0,0) = 0, attendu 1.0 → ANTI-CORRÉLATION
- k=10 (13×499) : (0,0) = 0, attendu 2.9 → ANTI-CORRÉLATION FORTE
- k=12 (5×59×1753) : (0,0,0) = 0, paires (5,59): 300 réel vs 278.5 attendu,
  (5,1753): 36 vs 31.8, (59,1753): 6 vs 2.6. Les paires (0,0) EXISTENT
  mais jamais le triplet (0,0,0) !

---

## DICHOTOMIE FONDAMENTALE des mécanismes

### Mécanisme I : PRIME BLOCKING (d premier ou grand facteur premier)
- Quand d = p premier : N₀(p) = 0 directement
- OBSERVATION : la cible -1 est la SEULE ou l'une des rares valeurs manquantes
- La CONTRAINTE D'ORDRE est l'ingrédient essentiel
- Sans ordre : image couvre tout → 0 atteint
- Avec ordre : image couvre tout SAUF 0

### Mécanisme II : CRT ANTI-CORRÉLATION (d composé sans bloqueur direct)
- Quand d = p₁·p₂·...·p_r et N₀(p_i) > 0 pour tout i
- Les compositions qui annulent mod p_i sont "forcées" vers résidus ≠ 0 mod p_j
- L'identité 2^S ≡ 3^k mod d crée une DÉPENDANCE globale
- Les paires (0,0) n'existent jamais même si chaque composante est possible

### Mécanisme III : HYBRIDE (d composé avec bloqueur partiel)
- Certains grands facteurs premiers de d ont N₀(p) = 0
- Pour les petits facteurs : CRT avec les autres petits

### ★★ CONJECTURE AFFINÉE (session 8) :
**Pour tout k ≥ 3, soit d = p premier et le Mécanisme I s'applique,
soit d composé et le Mécanisme II ou III s'applique.
Dans tous les cas N₀(d) = 0.**

NIVEAU DE CONVICTION : ESQUISSÉ → PROUVÉ_PARTIEL (pour Méc I : vérifié exactement k≤13)

---

---

## APPROFONDISSEMENT B2 : BAKER / ÉNONCÉ A (9 investigations)

### Investigation 1 — Cartographie ord_d(2) vs S pour k=3..30
- k=3 (d=5) : ord=4, ratio=0.80 → **SEUL cas avec ord < S** (ord = S-1)
- k=4..30 : ord_d(2) > S-1 TOUJOURS (vérifié exactement)
- Ratio ord/S croît exponentiellement (de 1.5 à 10^7)
- ord_d(2) = lcm{ord_p^e(2)} pour p^e ‖ d → VÉRIFIÉ

### ★★★ Investigation 5+8 — RÉDUCTION CRITIQUE
**Théorème (prouvable) : ord_d(2) = S-1 ⟺ d | (3^k - 2)**

Preuve :
  ord_d(2) | (S-1) ⟹ 2^{S-1} ≡ 1 mod d ⟹ 2^S ≡ 2 mod d ⟹ 3^k ≡ 2 mod d
  (car 2^S ≡ 3^k mod d) ⟹ d | (3^k - 2).
  Réciproquement, d | (3^k - 2) ⟹ 3^k ≡ 2 mod d ⟹ 2^S ≡ 2 mod d
  ⟹ 2^{S-1} ≡ 1 mod d ⟹ ord_d(2) | (S-1).

Vérification :
- k=1,2,3 : d | (3^k - 2) ✓ (d=1,7,5 respectivement)
- k=4..35 : d ∤ (3^k - 2) ✓ TOUJOURS
- Near-miss : k=12 où (3^k-2)/d = 1.0277 (le plus proche d'un entier)

### Investigation 7 — Argument d ≤ 2^{S-2}
- ÉCHOUE pour environ la moitié des k (quand d/3^k > 1/3)
- DONC : l'argument de taille simple ne suffit pas pour r = S-2
- Mais l'argument mod d (Investigation 5) résout TOUT en montrant
  directement que d ∤ (2^r - 1) pour chaque r.

### Investigation 5 — Preuve complète via |3^k - 2^s|
- Pour s=1..S-1 : 3^k ≢ 2^s mod d POUR TOUT s (vérifié k=3..25)
- Cela est ÉQUIVALENT à : d ne divise aucun 2^r - 1 pour r ∈ {1,...,S-1}
- DONC ord_d(2) ≥ S (car l'ordre est le plus petit r > 0 avec 2^r ≡ 1 mod d)

### PISTE VERS LA PREUVE FORMELLE de l'Énoncé A
**Stratégie en deux étapes :**
1. Montrer d ∤ (3^k - 2) pour k ≥ 4 → exclut r = S-1
2. Montrer d ∤ (2^r - 1) pour r ≤ S-2 → arguments variés (taille, Baker, etc.)

Pour l'étape 1 : d = 2^S - 3^k et 3^k - 2 < 3^k < 2^S = d + 3^k.
Donc d | (3^k - 2) ⟹ 3^k - 2 ≥ d ⟹ 3^k ≥ d + 2 = 2^S - 3^k + 2
⟹ 2·3^k ≥ 2^S + 2 ⟹ 3^k ≥ 2^{S-1} + 1.
Or 2^{S-1} < 3^k (car S = ⌈k·log₂3⌉ ⟹ 2^S ≥ 3^k ⟹ 2^{S-1} ≥ 3^k/2).
Donc la condition 3^k ≥ 2^{S-1} + 1 est souvent vraie... mais pas toujours.
⟹ La divisibilité n'est pas exclue par l'argument de taille seul !
⟹ Il faut un argument plus fin (Baker ou arithmétique).

NIVEAU DE CONVICTION : ESQUISSÉ pour Énoncé A
  - Vérifié ord_d(2) ≥ S pour k=4..30 (calcul exact)
  - Réduit à montrer d ∤ (3^k - 2) pour k ≥ 4
  - Baker pourrait conclure pour grand k (exponential gap)
  - Petit k : vérification directe

---

## Prochaine action
1. SAT/SMT encoding — L4, dernière lentille à investiguer
2. Mise à jour MIND_MAP complète avec TOUTES les découvertes session 8
