# CARTE MENTALE EXHAUSTIVE — Fermeture du Gap Collatz
# Date : 3 mars 2026
# Auteur : Eric Merle (assisté par Claude)
# Statut : Document de travail — carte complète de tous les chemins

---

## 0. DIAGNOSTIC DU GAP

### Score actuel : 4.85/5

### Les deux gaps résiduels

**Gap 1 — Cas 3b-ii** (le gap principal) :
- Conditions : n₃ petit (2 ≤ n₃ ≤ 3m·ln(p)), 3 ∉ ⟨2⟩ mod p, p ≥ m⁴, m > 130
- Besoin : n₃ ≥ 4q (pour garantir k_crit < n₃)
- Acquis : n₃ ≥ 0.631q (Lemme L13.1, barrière de taille)
- **Facteur manquant : 6.3×** entre le besoin et la preuve
- Alternative : c ≥ 0.36 dans Konyagin → fermerait tout
- L12 : 20/20 premiers de Régime B (m ≤ 130) satisfont (Q)
- L13 : ρ(M_q) → 2^{-1/4} ≈ 0.84 — approche spectrale ÉPUISÉE

**Gap 2 — Cas 3c** (secondaire) :
- Conditions : 3 ∈ ⟨2⟩ mod p, p ≥ m⁴
- Statut : Heuristiquement VIDE (0/427 cas observés)
- Non prouvé formellement

### Deux cadres théoriques parallèles

| Cadre | Objet | Formulation | Phase |
|-------|-------|-------------|-------|
| **Condition (Q)** | Sommes exp. sur ⟨2⟩ | (p-1)·ρ^{k-17} < 0.041 | SP10/L12/L13 |
| **Hypothèse H** | corrSum mod d | 0 ∉ Im(Ev_d) | Phase 20-23f |

Ces deux cadres attaquent le MÊME problème (absence de cycles positifs)
par des angles différents. Le Junction Theorem les relie.

---

## 1. CHEMINS VIA CONDITION (Q) — Cadre SP10

### Q1 : Effectiviser Konyagin/BGK ★★★☆☆

**Objectif** : Extraire c ≥ 0.36 de la borne ρ ≤ exp(-c·(log p)^{1/3})

| Sous-chemin | Description | Difficulté | Impact |
|-------------|-------------|------------|--------|
| Q1a | Extraire c de Konyagin (2003) | TRÈS HAUTE | Ferme tout Rég.B |
| Q1b | Extraire c de BGK (2006) | TRÈS HAUTE | Ferme tout Rég.B |
| Q1c | Borne NOUVELLE pour ⟨2⟩ spécifiquement | HAUTE | Potentiel unique |

**Blocage** : 10+ étapes avec pertes dans BGK (Balog-Szemerédi-Gowers, etc.)
**Estimation** : 6-12 mois spécialiste, 40-60% succès
**Verdict** : Problème OUVERT de classe mondiale. Pas dans notre scope immédiat.
**MAIS** : c = 0.36 est MODESTE — les experts attendent c ~ 1.

### Q2 : Vérification finie étendue ★★★★★

**Objectif** : Étendre m de 130 à 500+ via tables de Cunningham

| Extension | Couverture | Faisabilité | Formalité |
|-----------|------------|-------------|-----------|
| m ≤ 500 | Tous Mersenne connus, E ≤ 10^{-145} | HAUTE | Computationnelle |
| m ≤ 1200 | Tables Cunningham, E ≤ 10^{-355} | MOYENNE | Computationnelle |
| m ≤ 2000+ | Trial division partielle | BASSE | Computationnelle |

**Limitation fondamentale** : Vérification finie ≠ preuve infinie.
**Mais** : Combinée avec E ≤ 10^{-355}, rend le gap "au-delà de toute mesure".
**Action immédiate** : Faisable, progrès garanti.

### Q3 : Bornes spectrales pour sous-groupes ⛔ IMPASSE

**Statut** : MORT. L13 prouve définitivement :
- ρ(M_q) → 2^{-1/4} ≈ 0.8409 (convergence super-polynomiale)
- C(q) ~ q²/2 (croissance quadratique de la concentration)
- TOUTE approche par moments (4ème, 6ème, r-ème) est intrinsèquement limitée
- Le gap est NON-SPECTRAL

### Q4 : Borne inférieure sur n₃ ★★☆☆☆

**Objectif** : Montrer n₃ ≥ 4q (au lieu de 0.631q actuellement prouvé)

| Sous-chemin | Idée | Blocage |
|-------------|------|---------|
| Q4a | Bornes sur ord(3 mod ⟨2⟩/p) | Pas d'outils connus |
| Q4b | GRH + Artin pour n₃ | GRH couvre 37.4% seulement |
| Q4c | Diophantien : 3^j ≡ 2^a (mod M_q) | Baker ne contrôle pas les résidus |

**Diagnostic** : n₃ dépend de la position de 3 dans (Z/pZ)*/⟨2⟩.
Aucune théorie ne contrôle cette position pour p = M_q.
Le facteur 6.3× semble irréductible par les outils actuels.

### Q5 : Vide structurel du Régime B pour d(k) ★★★☆☆

**Observation clé** : 0/427 cas observés de p | d(k) sont en Régime B.

| Sous-chemin | Idée | Potentiel |
|-------------|------|-----------|
| Q5a | d(k) = 2^S - 3^k n'a pas de grands p avec petit ord | ÉLEVÉ si prouvable |
| Q5b | Cunningham numbers structure | Littérature existante |
| Q5c | Densité → 0 des Rég.B primes parmi div(d(k)) | MOYEN |

**Connexion** : Si d(k) est "lisse" (pas de grands facteurs avec petit ordre),
alors le Régime B est VIDE pour les diviseurs de d(k). C'est l'observation empirique.
**Outils potentiels** : Théorie des nombres de Fermat/Mersenne, ABC, S-unitaires.
**C'est probablement le chemin le plus sous-exploré.**

### Q6 : Théorème des Trois Distances amélioré ★☆☆☆☆

Déjà intégré dans la borne N ≤ floor(3·ln(p)/n₃) + 1.
Amélioration marginale possible. Pas un game-changer.

### Q7 : Comptage arithmétique via caractères ★★★☆☆

**Idée** : Utiliser des sommes de caractères pour compter #{k : p | d(k)}.
**Méthode** : Vinogradov / van der Corput.
**Difficulté** : Double exponentielle (2^{kθ} et 3^k).
**Rating L8c** : 4/5 en faisabilité.
**Sous-exploré** dans les phases récentes.

### Q8 : Baker / Transcendance ⛔ NON APPLICABLE

Baker borne |2^S - 3^k| par le bas. Mais p | d(k) concerne la divisibilité,
pas la taille. NOT APPLICABLE directement.
Exception : combiné avec Q5 (si |d(k)| est contrôlé ET p est borné).

---

## 2. CHEMINS VIA HYPOTHÈSE H — Cadre Phase 20-23f

### H1 : CRT + Vérification exhaustive ★★★★☆

**Acquis** :
- k = 3,4,5,7,8,11,13 exclus par CRT (7/16)
- k = 5 exclus chirurgicalement (Piste B, arc tronqué)
- k ≤ 17 : vérifiable exhaustivement (C fini)
- k ≥ 18 : déficit entropique γ = 0.0500 → C < d

| Action | Couverture | Faisabilité |
|--------|------------|-------------|
| k = 18..25 exhaustif | Extension preuve | HAUTE (C ~ 10^6 à 10^10) |
| k = 26..30 exhaustif | Données nouvelles | MOYENNE (C ~ 10^{12}) |

### H2 : Structure algébrique (Type I/II) ★★★☆☆

**Acquis** : Classification décidable, offset additif identifié.
**Succès unique** : Exclusion chirurgicale de q₃ (k=5, p=13).
**Limitation** : Les cas critiques k=6,9,10,15 sont TOUS Type I → n'aide pas.

| Extension | Potentiel | Difficulté |
|-----------|-----------|------------|
| Exclure q₄=12, q₅=41 | MOYEN (gros C) | HAUTE (C/p < 1) |
| Prouver Type I → N₀ < C/p | ÉLEVÉ si faisable | TRÈS HAUTE |

### H3 : Mixing / Random Walk ★★☆☆☆

**Diagnostic Phase 20** : Mixing prédit N₀ ~ C/p, PAS N₀ = 0.
Le trou spectral est positif (Δ > 0.48) mais ne suffit pas seul.
Utile en COMBINAISON avec H2 (synergie B+C identifiée Phase 20).

### H4 : Condition Q — le fossé le plus petit ★★★★☆

**Formulation** : |Σ T(t)| ≤ 0.041·C
**Fossé** : 2^{0.75k} (le PLUS PETIT de tous les fossés identifiés)
**Comparaison** :
- Phase 23 (pointwise) : 2^{1.585k}
- Phase 23b (CS) : 2^{0.835k}
- Phase 23d (Q) : **2^{0.75k}** ← ici
- Phase 23f (EO+PU) : **0** (conditionnel)

**C'est la formulation la plus accessible du problème ouvert.**

### H5 : Lemme d'Épluchage (Peeling) ★★☆☆☆

**Acquis** : N₀(p) ≤ 0.63·C (inconditionnel)
**Multi-couches** : Gain √k par couche, mais polynomial vs exponentiel.
**Sum-product** : Rep(α) ≤ |H|^{1/2+o(1)} en moyenne.
**Après r couches** : Gains polynomiaux, besoin exponentiels.
**Verdict** : Ne ferme pas le gap seul. Peut contribuer en combinaison.

### H6 : Propagation de retenues (Carry) ⛔ IMPASSE

La contrainte corrSum ≡ 0 (mod d) est GLOBALE.
L'analyse des retenues est LOCALE.
Le passage local → global n'est pas réalisable en l'état.

### H7 : Énergie additive + Mélange (Phase 23f) ★★★★★

**LE CHEMIN LE PLUS PROMETTEUR DE TOUT LE PROJET.**

Acquis INCONDITIONNELS :
- (P) E₄(H) = 2S² - S + O(S·log S) — H est quasi-Sidon [PROUVÉ]
- (P) |G(u)| ≈ √S typiquement [PROUVÉ par Parseval + E₄]
- (P) Paucité des grandes valeurs : |B_α| ≤ O(p·log S/(α⁴S²)) [PROUVÉ]
- (P) E_{2r}(H) ≈ r!²·C(S,r) dans Z [PROUVÉ, Lemme 9]

Acquis CONDITIONNELS :
- (EO) |μ̂_k(t)| ≤ S^{-k/2+O(√k)} [sous EO]
- (EO) Mélange pour k ≥ 3 [sous EO]
- (EO+PU) N₀ ≤ (1+0.041)·C/p pour k ≥ 18 [sous EO+PU]
- (EO+PU) **FERMETURE COMPLÈTE** — pas de cycles positifs [sous EO+PU]

| Sous-chemin | Objectif | Hypothèse éliminée | Difficulté |
|-------------|----------|--------------------|------------|
| H7a | Éliminer EO | EO | ★★★☆☆ |
| H7b | Prouver PU | PU | ★★★★☆ |

#### H7a : Éliminer EO (équidistribution orbitale)

**Méthode Weyl ordre 2** : Mixing pour k ≥ 5 si E₈(H) borné.
**Approche combinée** (énergie + paucité) : |μ̂_k| ≤ S^{-k/3+o(k)} sans EO.
**Blocage** :
- E₈(H) mod p : besoin estimation rigoureuse des termes modulaires
- Argument de découplage pour produits de Riesz sur orbites multiplicatives

**Pièces à construire** :
1. Estimer E₈(H) = #{octuplets : Σ4 = Σ4 mod p} rigoureusement
2. Argument de découplage (Bourgain-Demeter adapté à F_p)
3. Borne uniforme max_t |μ̂_k(t)| sans EO

#### H7b : Prouver PU (proportion uniformity)

**Énoncé** : π(A,0)/k! ≈ 1/p uniformément en A "typique"
**Idée** : Les k! permutations de corrSum donnent des images quasi-indépendantes
car les coefficients 3^j sont en "position générale" dans F_p^k.
**Connexion** : Marche aléatoire sur S_k induite par les poids 3^j.
**Outils potentiels** : Théorie des représentations de S_k, Cayley graphs.

### H8 : Vinogradov-Korobov pour sommes lacunaires ★★☆☆☆

|G(u)| ≤ S^{1-1/2^r} · p^{1/2^r+ε} (sommes incomplètes).
Faible quand S << p (notre régime !).
Utile en combinaison avec l'énergie additive (Phase 23f, §7.4-7.5).

---

## 3. CHEMINS "CONSTRUIRE NOS PROPRES OUTILS"

### T1 : Bornes explicites pour sommes exp. sur ⟨2⟩ ★★★★☆

**Spécificité de ⟨2⟩** : C'est une progression géométrique {1, 2, 4, ..., 2^{m-1}}.
Pas un sous-groupe "générique" — structure binaire exploitable.
**Lacunarité** : Les éléments croissent exponentiellement → annulations forcées.
**Lien avec Q1c** mais en développement propre (notre outil, pas effectivisation).

**Cahier des charges** :
- Input : p premier, m = ord_p(2), H = ⟨2⟩ = {2^0, ..., 2^{m-1}} mod p
- Output : ρ(p) ≤ f(m, p) avec f explicite et f < 1 - 1/m
- Cible : f assez petit pour que k_crit(p) < 69 pour m > M_0

### T2 : Formaliser le filtre en cascade ★★★☆☆

**Filtre en cascade** :
1. Filtre n₃ : k ≡ 0 (mod n₃)
2. Filtre Beatty : ⌈n₃jθ⌉ ≡ Lj (mod m)
3. Barrière de taille : k ≤ ⌊(q-1)/θ⌋ → p ∤ d(k)
4. Filtre de divisibilité : p | d(k) effectivement

**Insight clé** : p | d(k) ⟺ (filtre n₃) ET (filtre Beatty) — EXACT.
Cette ÉQUIVALENCE arithmétique est déterministe. Le nombre exact de k
satisfaisants est contrôlé par la discrepance de {jδ}.

**Théorème à formaliser** : Le nombre total N de k ∈ [69, k_crit] tel que
p | d(k) est EXACTEMENT le nombre de j satisfaisant les deux filtres.

### T3 : Découplage pour orbites multiplicatives ★★★★☆

**Nouveau résultat en analyse harmonique sur F_p**.
- La "courbe" a ↦ 2^a mod p a courbure non dégénérée (Δ² ≠ 0 pour h < S)
- Bourgain-Demeter (2015) pour courbes dans R^n → adapter à F_p
- Donnerait une borne inconditionnelle sur |μ̂_k(t)| sans EO

**Pièces nécessaires** :
1. Notion de courbure discrète dans F_p (Δ² ≠ 0 : fait)
2. Inégalité de découplage discrète
3. Application aux produits de Riesz

### T4 : Weyl combiné avec énergie (sans EO) ★★★★☆

**Le chemin le plus court** :
1. E₄(H) PROUVÉ (quasi-Sidon, Théorème 3)
2. |G(u)| ≈ √S PROUVÉ (Parseval + E₄)
3. E₈(H) à borner (extension du Lemme 9 à r=4)
4. Weyl ordre 2 → mixing pour k ≥ 5 si E₈ borné
5. Passage L² → L∞ via moments ou découplage

### T5 : PU via marche sur S_k ★★★☆☆

**Modèle** : Considérer la marche sur S_k définie par les poids 3^j.
La convergence de cette marche impliquerait PU.
**Outils** : Théorie des représentations de S_k (Diaconis, 1988).
**Difficulté** : Les poids 3^j ne génèrent pas S_k de manière standard.

---

## 4. CLASSIFICATION DES IMPASSES CONFIRMÉES ⛔

| Chemin | Raison de l'impasse | Phase |
|--------|---------------------|-------|
| Q3 (Spectral) | ρ → 0.84, C(q) ~ q² | L13 |
| H6 (Retenues) | Local vs global | Phase 23d |
| Q8 (Baker seul) | Borne inférieure ≠ divisibilité | Phase 8 |
| Phase 13 (Baker-Kolmo) | 3 faux prémisses | Audit Phase 13 |
| Phase 23b (Barrière √) | 2^{0.835k} infranchissable en moments | Phase 23b |
| Tao extension (Piste D) | "Presque tout" ≠ "tout" | Phase 20 |
| Probabiliste (Borel-Cantelli) | Somme harmonique diverge (non-Mersenne) | L13 Phase 6 |
| Skolem (S-unitaire) | Paramétrique, pas fixe | Phase 8d |

---

## 5. HIÉRARCHIE DES CHEMINS PAR PROMESSE

### TIER 1 — Les plus prometteurs (action immédiate)

| # | Chemin | Raison | Faisabilité | Impact |
|---|--------|--------|-------------|--------|
| 1 | **H7a** (Éliminer EO) | Tout sauf EO est prouvé ou en place | ★★★☆☆ | 5/5 |
| 2 | **Q2** (Vérif. m→500+) | Computationnel, progrès garanti | ★★★★★ | 2/5 |
| 3 | **H1a** (k=18..25 exhaustif) | Données manquantes, faisable | ★★★★★ | 2/5 |
| 4 | **T4** (Weyl + Énergie) | Le plus court chemin inconditionnel | ★★★★☆ | 5/5 |

### TIER 2 — Prometteurs mais plus difficiles

| # | Chemin | Raison | Faisabilité | Impact |
|---|--------|--------|-------------|--------|
| 5 | **H7b** (Prouver PU) | Nécessaire après EO | ★★☆☆☆ | 5/5 |
| 6 | **Q5** (Vide structurel) | Sous-exploré, potentiel | ★★☆☆☆ | 5/5 |
| 7 | **T3** (Découplage) | Nouveau résultat math | ★★☆☆☆ | 5/5 |
| 8 | **T1** (Bornes pour ⟨2⟩) | Spécifique, pas générique | ★★★☆☆ | 4/5 |

### TIER 3 — Long shot

| # | Chemin | Raison | Faisabilité | Impact |
|---|--------|--------|-------------|--------|
| 9 | **Q1** (Effectiviser BGK) | Problème ouvert mondial | ★☆☆☆☆ | 5/5 |
| 10 | **Q4** (Borne inf. n₃) | Pas d'outils connus | ★☆☆☆☆ | 5/5 |
| 11 | **Q7** (Comptage caractères) | Sous-exploré, double exp. | ★★☆☆☆ | 3/5 |

---

## 6. STRATÉGIE RECOMMANDÉE — LE PROGRAMME EN 3 AXES

### AXE A : Inconditionnel computationnel (IMMÉDIAT)
- **Q2** : Étendre vérification m → 500 (Cunningham tables)
- **H1a** : Vérifier k = 18..25 exhaustivement
- Renforce : la base empirique, les données pour calibrer les autres axes
- Livrable : extension de L12, nouvelles tables dans le preprint

### AXE B : Conditionnel théorique (MOYEN TERME)
- **H7a** + **T4** : Éliminer EO via Weyl + Énergie additive
  - Étape 1 : Borner E₈(H) mod p rigoureusement
  - Étape 2 : Argument de découplage ou Weyl ordre 2
  - Étape 3 : Borne uniforme |μ̂_k(t)| ≤ S^{-k/3+o(k)}
- **H7b** : Si AXE B réussit, attaquer PU
- Livrable : nouveaux théorèmes pour le preprint, score → 4.95+ si EO éliminé

### AXE C : Exploration structurelle (PARALLÈLE)
- **Q5** : Investiguer pourquoi d(k) n'a JAMAIS de facteurs Régime B
- **T2** : Formaliser le filtre en cascade comme théorème
- **T1** : Développer des bornes spécifiques pour ⟨2⟩ (vs sous-groupe quelconque)
- Livrable : potentiellement le chemin le plus élégant si Q5 aboutit

### Diagramme de flux

```
                    ┌──────────────────────┐
                    │  AXE A (computations) │
                    │  Q2 + H1a             │
                    │  ★★★★★ faisabilité    │
                    └──────────┬───────────┘
                               │ données + confiance
                               ▼
    ┌──────────────────────────────────────────────┐
    │  AXE B (énergie additive → mélange incond.)  │
    │  H7a → T4 → H7b                              │
    │  ★★★★☆ faisabilité, ★★★★★ impact             │
    │                                                │
    │  E₄ PROUVÉ → E₈ à borner → Weyl/Découplage   │
    │  → Mixing incond. → PU → COLLATZ              │
    └──────────────────────┬───────────────────────┘
                           │ si bloqué
                           ▼
    ┌──────────────────────────────────────────────┐
    │  AXE C (structure d(k) → vide Régime B)      │
    │  Q5 + T2 + T1                                 │
    │  ★★★☆☆ faisabilité, ★★★★★ impact             │
    │                                                │
    │  Pourquoi d(k) n'a pas de facteurs Rég.B ?    │
    │  → Cunningham structure → S-unitaire → ABC ?   │
    └──────────────────────────────────────────────┘
```

---

## 7. PIÈCES À CONSTRUIRE (CAHIER DES CHARGES FUSÉE)

### Pièce 1 : E₈(H) mod p [pour AXE B]
- **Spécification** : Borner #{octuplets (a₁..a₄,b₁..b₄) : Σ2^{aᵢ} ≡ Σ2^{bᵢ} mod p}
- **Dans Z** : Seules solutions = permutations (Lemme 9 généralisé)
- **Mod p** : Solutions supplémentaires via j·p avec |j| ≤ 4·2^S/p
- **Livrable** : E₈(H) = 4!²·C(S,4) + O(correction mod p) avec correction bornée

### Pièce 2 : Découplage discret [pour AXE B]
- **Spécification** : Borne sur Σ_t |∏ G(3^jt)/S|^{2^r} sans EO
- **Input** : E_{2r}(H) borné (Pièce 1 pour r=4)
- **Output** : |μ̂_k(t)| ≤ S^{-δk} pour δ > 0 uniforme
- **Livrable** : Théorème nouveau en analyse harmonique discrète

### Pièce 3 : PU ou substitut [pour AXE B]
- **Spécification** : N₀/C ≈ N̄₀/S^k ≈ 1/p
- **Approche A** : Marche sur S_k (Diaconis)
- **Approche B** : Argument direct via structure de Horner
- **Livrable** : Transfert ordonné → non-ordonné

### Pièce 4 : Structure de d(k) [pour AXE C]
- **Spécification** : Montrer que d(k) = 2^S - 3^k n'a pas de facteurs en Régime B
- **Outils** : Théorie des nombres de Fermat, factorisations de Cunningham
- **Observable** : 0/427 cas, heuristique forte
- **Livrable** : Théorème structural ou conjecture fortement supportée

### Pièce 5 : Extension computationnelle [pour AXE A]
- **Spécification** : Vérifier (Q) pour m = 131..500
- **Input** : Tables de Cunningham, factorisation de 2^m-1
- **Output** : Table de (p, m, ρ, k_crit, (Q)) pour tous les premiers
- **Livrable** : Extension de L12 de 20 à ~200+ premiers

### Pièce 6 : Vérification exhaustive k=18..25 [pour AXE A]
- **Spécification** : Calculer N₀(d(k)) pour k = 18..25
- **Méthode** : Énumérer toutes les C(S,k) compositions, calculer corrSum mod d
- **Pour k=18** : C ≈ 2.2×10⁶, faisable en minutes
- **Pour k=25** : C ≈ 10¹⁰, faisable en heures avec parallélisation
- **Livrable** : Preuve exhaustive k=3..25, données β(p) dans nouveaux régimes

---

## 8. CONNEXIONS ENTRE CHEMINS

### Synergie AXE A → AXE B
Les données de H1a (k=18..25) fournissent :
- Vérification numérique de E₄(H) mod p pour de vrais d(k)
- Distribution de |G(u)| pour calibrer les bornes théoriques
- Valeurs de |μ̂_k(t)| pour tester les prédictions de mélange

### Synergie AXE B → AXE C
Si l'énergie additive basse de H force le mélange, alors :
- Les diviseurs de d(k) en Régime B seraient les "pires" pour le mélange
- Mais ρ → 0.84 pour Mersenne → le mélange est PLUS DUR pour Régime B
- Paradoxe résolu si d(k) n'a simplement pas de facteurs Régime B

### Le cercle vertueux
```
Computations (AXE A) ──données──→ Théorie (AXE B)
     ↑                                    │
     │                              si bloqué
     │                                    ↓
     └──────── confiance ←───── Structure (AXE C)
```

---

## 9. RISQUES ET MITIGATION

| Risque | Probabilité | Impact | Mitigation |
|--------|-------------|--------|------------|
| E₈ mod p trop complexe | 30% | Bloque AXE B | Estimation numérique d'abord |
| Découplage ne s'adapte pas à F_p | 40% | Bloque AXE B | Méthode Weyl alternative |
| PU faux pour certains A | 10% | Bloque AXE B complet | Vérification numérique |
| Q5 : d(k) a des facteurs Rég.B grands | 5% | Invalide AXE C | Preuve par l'absurde |
| Gap irréductible (théorie insuffisante) | 20% | Score reste 4.85 | Document conditionnel |

---

## 10. COMPARAISON AVEC LA LITTÉRATURE

### Ce qui a été prouvé dans l'histoire de Collatz

| Résultat | Auteur(s) | Date | Technique |
|----------|-----------|------|-----------|
| Pas de cycle de longueur 1 | Folklore | — | Direct |
| Pas de cycle de longueur 2 | Folklore | — | Direct |
| Pas de cycles k ≤ 17 | Simons-de Weger | 2003 | Computation |
| Pas de cycles k ≤ 68 | D17 (étendu) | 2017 | Computation + Baker |
| "Presque tous" convergent | Tao | 2022 | Ergodicité |
| **Déficit entropique γ = 0.0500** | **Merle (ce travail)** | **2025** | Shannon + Steiner |
| **Junction Theorem [1,67]∪[18,∞)** | **Merle (ce travail)** | **2025** | Entropie + D17 |
| **Condition (Q) Rég.A FERMÉ** | **Merle (ce travail)** | **2025** | Di Benedetto + comp. |
| **Condition (Q) Rég.B générique FERMÉ** | **Merle (ce travail)** | **2025** | SP10a Beatty |
| **E₄(H) quasi-Sidon** | **Merle (ce travail)** | **2026** | Parité + mod p |
| **Mélange sous EO+PU** | **Merle (ce travail)** | **2026** | Phase 23f |

### Ce qui reste ouvert

1. Constante de Konyagin explicite (problème ouvert mondial)
2. Bornes non-triviales pour |H| ≤ p^{1/4} (problème ouvert mondial)
3. PU pour sommes de Horner sur compositions ordonnées
4. Structure des diviseurs de 2^S - 3^k en Régime B

---

## CONCLUSION

La carte mentale identifie **18 chemins** dont **4 impasses confirmées**.
Le chemin le plus prometteur est **H7a+T4** (énergie additive → mélange inconditionnel),
qui ne nécessite que **3 pièces à construire** (E₈, découplage, PU).

Le Programme en 3 axes (A: computationnel, B: théorique, C: structurel)
permet de progresser en parallèle avec des synergies naturelles.

**La question stratégique** : dans quel ordre attaquer les 3 axes ?

---
