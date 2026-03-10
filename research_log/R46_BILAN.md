# BILAN R46 — Pourquoi μ→1 et premier noyau prouvable du MSL

**Date** : 2026-03-10
**Type** : P (proof-oriented)
**Scripts** : `r46_mu_analysis.py` (Agent A), `r46_msl_kernel.py` (Agent B)
**Tests** : 160/160 PASS (61 + 99)
**Commits** : 2d88c24 (scripts), 5558322 (RESEARCH_MAP)
**IVS** : 8/10 — premier résultat prouvé sur la structure fine des collisions,
route de preuve prioritaire identifiée, deux fausses routes éliminées avec autopsie.

---

## 1. Contexte et objectif

R45 a établi que le verrou central est **μ = M₂·p/C² → 1** (la multiplicité
de collision tend vers 1), et que le MSL modéré (V ≤ A(p)·C) est le lemme
conjectural survivant. R46 devait répondre à :

> Peut-on formuler une première charpente théorique crédible pour le MSL modéré,
> en expliquant pourquoi μ tend vers 1 ?

---

## 2. Agent A — Pourquoi μ→1

### 2.1 Reformulation optimale de μ−1 [PROUVÉ]

**Théorème T50** : Identité exacte décomposant μ−1 en deux termes :
```
μ − 1 = (p−1)/C + p·E_excess/C²
```
où :
- **(p−1)/C** = terme structurel (inévitable, vient du diagonal M₂ = C)
- **p·E_excess/C²** = terme dynamique, avec E_excess = (M₂−C) − C(C−1)/p
  = excès de collisions hors-diagonale au-delà de l'espérance aléatoire

Cette reformulation est optimale car elle sépare ce qui est inévitable
(le diagonal) de ce qui doit être contrôlé (l'excès).

**Trois reformulations équivalentes** [toutes PROUVÉES] :

| Reformulation | Expression | Mécanisme exposé |
|---------------|-----------|------------------|
| (A) Spectrale | μ−1 = (1/C²)·Σ_{r≥1}|S(r)|² | Annulation des sommes exp. |
| (B) Déviation | μ−1 = (p/C²)·Σ(N_r−C/p)² | Variance de la distribution |
| (C) Collision | μ−1 = (p−1)/C + p·E_excess/C² | Excès structurel vs dynamique |

**Verdict** : (C) est la plus exploitable car elle isole le mécanisme.

### 2.2 Weyl differencing pour k≥4 : ÉLIMINÉ [T51]

**Question** : Peut-on "différencier" la somme S(r) = Σ_B ω^{r·P_B(g)}
par un shift B → B + eᵢ comme dans Weyl classique ?

**Réponse : NON pour k ≥ 4.**

Le simplexe monotone Δ = {B : 0 ≤ B₀ ≤ ... ≤ B_{k-1} = max_B}
n'est PAS invariant par translation. Si B_i = B_{i+1} (palier),
alors B → B + eᵢ viole la monotonie.

**Analyse par k** :
- k = 2 : Δ est un intervalle [0, max_B]. Weyl **MARCHE** (somme géom.).
- k = 3 : Δ est un triangle 2D. Shifts partiels possibles mais la
  factorisation se brise à la frontière B₀ = B₁.
- k ≥ 4 : Δ est un simplexe de dimension k−2. Aucun shift uniforme
  ne préserve la monotonie. **BLOQUÉ.**

**Micro-test** (autorisé) : pour k=3, max|S(r)|/C ∈ [0.48, 0.58]
(annulation réelle mais pas de mécanisme Weyl propre).
Pour k≥6, max|S(r)|/C tombe à 0.01−0.20 par un mécanisme **autre que Weyl**.

### 2.3 Cinq routes de preuve comparées

| # | Route | Mécanisme | Verdict |
|---|-------|-----------|---------|
| (a) | Spreading monotone | Pseudo-aléa multiplicatif de 2^{Bᵢ} mod p | CRÉDIBLE (heuristique) |
| (b) | Mixing Markov | Convolution itérée, indépendance des termes | **FRAGILE** — dépendances sous monotonie |
| (c) | Large Sieve adaptée | Σ|S(r)|² ≤ (N+Q²)·... | **FRAGILE** — pas de LS pour simplexe |
| (d) | Erdős-Turán | Discrepancy ≤ (1/R)·Σ|S(r)|/r | **ÉLIMINÉ** — plus faible que ACL |
| **(e)** | **Horner Telescoping** | Induction sur k via condition sur B₀ | **CRÉDIBLE (MEILLEUR)** |

### 2.4 Route prioritaire : Horner Telescoping [SEMI-FORMEL]

**Idée** : P_B est une somme de Horner. Conditionner sur B₀ = b₀
et faire une récurrence de dimension k à k−1.

**Base k = 2** : S(r) est une somme géométrique distordue sur
l'intervalle [0, max_B]. Bornée par ~max_B/ord_p(2).
Essentiellement prouvable.

**Pas inductif k → k+1** : Conditionner sur B₀ = b₀.
Pour chaque b₀, la somme interne est une somme sur {B₁,...,B_{k-1}}
avec B₁ ≥ b₀, un sous-simplexe. La structure de Horner se reproduit.

**Point dur identifié** : montrer que les contributions spectrales
des différentes "tranches" B₀ = b₀ ne s'ajoutent pas constructivement
(non-résonance entre tranches).

**Données numériques** : la décomposition en tranches est exhaustive,
chaque tranche couvre des résidus multiples.

### 2.5 Cible de preuve réaliste

| Cible | Énoncé | Difficulté | Route |
|-------|--------|:----------:|-------|
| **Target 1** | μ−1 = o(1) (qualitatif) | BASSE-MOYENNE | Horner qualitativa |
| Target 2 | μ−1 = O(1/C^δ), δ>0 | MOYENNE | Horner quantifié |
| Target 3 | μ−1 = O(p/C) | HAUTE | Horner + spreading |

**Recommandation** : viser Target 1 d'abord (WEL). Il suffit pour
f_p → 1/p via ACL, car C croît exponentiellement.

### 2.6 WEL — Plus petit énoncé semi-formel utile [CONJECTURAL]

**Lemme (WEL — Weak Equidistribution Lemma)** :
> Pour tout premier p ≥ 5 avec gcd(3,p) = 1 :
> lim_{k→∞, p|d(k)} μ(k,p) = 1.

**Équivalences** [PROUVÉES] :
```
μ → 1  ⟺  V/C² → 0  ⟺  Σ_{r≥1}|S(r)|²/C² → 0  ⟺  f_p → 1/p (via ACL)
```

---

## 3. Agent B — Premier noyau prouvable

### 3.1 Candidat 1 : MSL-lite (Convolution Mixing)

**Idée** : P_B est une somme de k termes Xⱼ = gʲ·2^{Bⱼ} mod p.
Quand k croît, le "mixing" convolutif devrait uniformiser la distribution.

**Résultats** :
- Convergence empirique confirmée : μ−1 ~ 1.91·C^{−0.65}
- Chi² marginal décroissant avec k

**Gaps fatals** :
- G1 : Pas de taux quantitatif
- G2 : Dépendance forte des Xⱼ sous monotonie (B₀ ≤ ... ≤ B_{k-1})
- G3 : Structure de Horner crée un couplage multiplicatif incompatible
  avec le mixing additif standard
- G4 : Les théorèmes classiques (Erdős-Turán, Weyl) exigent l'indépendance

**ÉLIMINÉ** — voir autopsie §4.

### 3.2 Candidat 2 : LSD (Lemme de Spreading des Différences) [SURVIVANT]

**Idée** : Décomposer les collisions par distance de Hamming h(B,B').
Les paires "proches" (h petit) collisionnent pour des raisons algébriques
contrôlables. Les paires "lointaines" (h grand) ont une différence
pseudo-aléatoire et collisionnent avec probabilité ~1/p.

### 3.3 NOYAU PROUVÉ : LSD h=1 [T52]

**Théorème** : Pour deux B-vecteurs monotones différant en une seule
coordonnée j, avec Δ = |Bⱼ − B'ⱼ| :
```
P_B ≡ P_{B'} mod p  ⟺  ord_p(2) | Δ
```

**Preuve** :
D(B,B') = gʲ · 2^{min(Bⱼ,B'ⱼ)} · (2^Δ − 1) mod p.
Comme gcd(gʲ · 2^{min}, p) = 1 (p impair, gcd(p,6)=1),
D ≡ 0 mod p ssi 2^Δ ≡ 1 mod p ssi ord_p(2) | Δ. ∎

**Vérification exhaustive** :
- (k=3, p=5) : ord₅(2)=4, max_B=2, aucun Δ≥4 → 0 collisions h=1 ✓
- (k=6, p=5) : ord₅(2)=4, exactement 5 paires avec |Δ|=4 ✓
- (k=6, p=59) : ord₅₉(2)=58, max_B=4 < 58 → 0 collisions h=1 ✓
- (k=7, p=23) : ord₂₃(2)=11, max_B=5 < 11 → 0 collisions h=1 ✓

### 3.4 Données empiriques : decomposition par h

**(k=6, p=5, C=126, M₂=3396)** :
| Type | h | Collisions | Attendu random | Excès |
|------|---|-----------|----------------|-------|
| Diagonal | 0 | 126 | 126 | 0 |
| Near | ≤2 | 786 | 648 | +138 (=1.10·C) |
| Far | ≥3 | 2484 | 2502 | −18 |
| **Total** | | **3396** | **3276** | **+120** |

**Observation clé** : les collisions far-pair ont un taux ≈ 1/p
(ratio 0.99 pour p=5, 0.86 pour p=59, 1.01 pour p=23).
L'excès vient exclusivement des near-pairs.

### 3.5 Feuille de route LSD

| Étape | Description | Statut |
|-------|-------------|--------|
| 1 | Lemme h=1 exact (ord_p(2)\|Δ) | **PROUVÉ** |
| 2 | Compter les paires monotones h=1 | FAISABLE (combinatoire pure) |
| 3 | Borner les collisions h=2 via Weil | DIFFICILE |
| 4 | Montrer far-pair rate ≈ 1/p | CONJECTURAL |

### 3.6 Head-to-head (5 critères)

| Critère | MSL-lite | LSD | Gagnant |
|---------|----------|-----|---------|
| Maturité Ladder | semi-formalisation | semi-formel + h=1 prouvé | **LSD** |
| Taille des gaps | 4 gaps majeurs ouverts | 1 fermé, 1 faisable, 1 dur | **LSD** |
| Connexion outils | ET échoue (indépendance) | ord_p(2), Weil, pair correlation | **LSD** |
| Ce que ça donne via ACL | f_p→1/p qualitatif | f_p ≤ 1/p+O(1/√C) potentiel | **LSD** |
| Démontrabilité | BASSE | MODÉRÉE | **LSD** |

**Verdict : LSD gagne 5/5.**

---

## 4. Autopsies des pistes fermées

### Piste 1 : Weyl differencing k≥4

| Champ | Contenu |
|-------|---------|
| **Type de mort** | Non ciblante (outil inadapté au domaine) |
| **Hypothèse fausse** | Que le simplexe monotone Δ est invariant par translation |
| **Ce que la mort enseigne** | Les outils classiques (Weyl, Weil, LS) présupposent un domaine régulier. Le simplexe monotone a une structure rigide incompatible. Il faut des outils qui exploitent la monotonie, pas qui la combattent. |
| **Redirection** | Vers Horner Telescoping (induction sur k, qui utilise la structure récursive) |

### Piste 2 : MSL-lite (Convolution Mixing)

| Champ | Contenu |
|-------|---------|
| **Type de mort** | Trop faible + non ciblante |
| **Hypothèse fausse** | Que les termes Xⱼ = gʲ·2^{Bⱼ} sont "suffisamment indépendants". Sous monotonie, les paliers B_i=B_{i+1} créent des corrélations déterministes : X_{i+1}/X_i = g (exact). Les sous-sommes deviennent géométriques, pas pseudo-aléatoires. |
| **Ce que la mort enseigne** | (1) L'indépendance est le mauvais paradigme pour B monotones. (2) Le mixing est un résultat observé, pas un mécanisme prouvable. (3) Il faut un argument structurel sur les paires (B,B'), pas statistique sur les contributions individuelles. |
| **Redirection** | Vers LSD (analyse des différences P_B − P_{B'}, qui opère sur les paires, pas les individus) |

### Piste 3 : Erdős-Turán pour MSL

| Champ | Contenu |
|-------|---------|
| **Type de mort** | Absorbée dans meilleur concept (ACL) |
| **Hypothèse fausse** | Que ET donnerait une borne plus fine que ACL. En fait ET est strictement plus faible que ACL car ACL utilise directement Plancherel, tandis que ET perd un facteur 1/r dans la sommation. |
| **Redirection** | Non pertinent — ACL est déjà disponible |

---

## 5. Ladder of Proof (objets touchés en R46)

| Objet | Niveau avant R46 | Niveau après R46 |
|-------|-----------------|-----------------|
| μ−1 reformulation | observation | **calcul exact** (identité prouvée) |
| Weyl pour simplexe | intuition (suggéré R44) | **réfuté** (obstruction prouvée) |
| MSL-lite mixing | observation | **réfuté** (indépendance fausse) |
| LSD h=1 | — (nouveau) | **lemme prouvé** |
| LSD h≥2 | — | observation (taux ≈ 1/p) |
| Horner Telescoping | intuition | **semi-formalisation** (base + structure inductive) |
| WEL (μ→1 qualitatif) | observation | **lemme candidat** (formulation précise) |
| MSL modéré | conjectural | conjectural (inchangé, mais route clarifiée) |

---

## 6. Ce qui est appris (synthèse R46)

1. **Le bon paradigme n'est pas l'indépendance mais la structure des paires.**
   MSL-lite cherchait à montrer que les termes individuels se mélangent.
   LSD montre qu'il faut analyser les différences P_B−P_{B'} par distance.

2. **Les outils classiques (Weyl, LS, ET) ne marchent PAS sur le simplexe monotone.**
   C'est un résultat négatif important qui élimine 3 routes séduisantes d'un coup.

3. **La structure de Horner est l'alliée, pas l'ennemie.**
   La route Horner Telescoping (induction sur k, condition sur B₀) est la
   seule qui exploite la structure de P_B au lieu de la combattre.

4. **Le noyau h=1 du LSD est le premier résultat exact sur la collision.**
   La caractérisation ord_p(2) | |Δ| est une percée modeste mais propre :
   c'est le premier lemme prouvé qui explique quand et pourquoi deux
   B-vecteurs collisionnent.

5. **WEL (μ→1 qualitatif) est la bonne cible à court terme.**
   C'est suffisant pour f_p→1/p, et strictement plus faible que MSL modéré.

---

## 7. Survivants pour R47

| Objet | Statut | Prochaine étape |
|-------|--------|-----------------|
| **LSD** | h=1 prouvé, h≥2 observé | Compter les paires h=1 monotones (combinatoire), borner h=2 via Weil |
| **Horner Telescoping** | Base k=2 semi-formel, structure inductive identifiée | Formaliser la base k=2, analyser la non-résonance des tranches B₀ |
| **WEL** | Lemme candidat (formulation précise) | Prouver via Horner ou LSD |

Les deux routes (LSD et Horner) sont complémentaires, pas concurrentes :
- Horner attaque μ→1 par le haut (spectral, induction sur k)
- LSD attaque par le bas (collision, stratification par h)

---

## 8. Risques et limites

- **Non-résonance B₀-slices** : c'est le point dur de Horner. Si les
  tranches interfèrent constructivement, l'induction ne donne rien.
- **LSD h≥2** : le passage de h=1 (exact, algébrique) à h=2 (deux
  coordonnées qui changent) est un saut de complexité important.
  D = gʲ¹·δ₁ + gʲ²·δ₂ est une forme bilinéaire, pas linéaire.
- **Far-pair rate ≈ 1/p** : observé mais pas prouvé. C'est le cœur
  du MSL — pourquoi les paires lointaines sont-elles quasi-aléatoires ?

---

## 9. Verdict final

**Score : 8/10**

- **PASS-1** ✅ : reformulation canonique μ−1 = (p−1)/C + p·E_excess/C²
- **PASS-2** ✅ : route prioritaire = Horner Telescoping (5 routes comparées)
- **PASS-3** ✅ : premier noyau prouvable = LSD h=1 (ord_p(2) | |Δ|)
- **PASS-4** ✅ : 3 fausses routes éliminées (Weyl k≥4, MSL-lite, ET)

R46 fait monter le MSL d'un cran : de "conjectural pur" à "semi-formel
avec noyau prouvé (h=1) et route de preuve identifiée (Horner + LSD)".

---

## 10. Chaîne logique complète (R42-R46)

```
N₀(p) = C/p + (1/p)·Σ S(r)                    [R42, PROUVÉ]
  → f_p = 1/p + (1/(pC))·Σ S(r)
  → ACL: f_p ≤ 1/p + √((p-1)V/(pC²))          [R44, PROUVÉ]
  → V = M₂ - C²/p = collision excess            [R45, PROUVÉ]
  → μ−1 = (p-1)/C + p·E_excess/C²              [R46, PROUVÉ]
  → LSD h=1: collision ssi ord_p(2) | |Δ|       [R46, PROUVÉ]
  → MSL: V ≤ A(p)·C                             [CONJECTURAL]
  → WEL: μ → 1                                  [CONJECTURAL, cible]
  → f_p → 1/p quand k → ∞                       [conséquence immédiate]
```

---

*Bilan rédigé par Claude Opus 4.6, Round 46, 2026-03-10.*
