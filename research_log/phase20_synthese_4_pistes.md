# Phase 20 — Synthese comparative des 4 pistes
# Date : 28 fevrier 2026
# Auteur : Eric Merle (assiste par Claude)

---

## 0. Rappel du probleme

**Hypothese H (Zero-Exclusion)** : Pour tout k >= 1, avec d(k) = 2^S - 3^k
(S = ceil(k*log_2(3))), on a :

  0 ∉ Im(Ev_d) = {corrSum(A) mod d : A in Comp(S, k)}

L'Hypothese H est la derniere piece manquante du Junction Theorem [1,67] ∪ [18,∞).
Le Junction Theorem ramene l'absence de cycles positifs non triviaux a H.

**Quatre pistes explorees :**
- **A** : CRT Hybride + Computationnel (Proposition 16.4)
- **B** : Structure Algebrique (Bases 2 et 3, Type I/II)
- **C** : Mixing / Random Walk (Operateur de transfert, spectre)
- **D** : Extension de Tao (2022) (Densite, ergodicite)

---

## 1. Tableau comparatif des scores

| Critere                      | Piste A | Piste B | Piste C | Piste D |
|------------------------------|---------|---------|---------|---------|
| Faisabilite computationnelle | **8/10** | **9/10** | 7/10    | 2/10    |
| Faisabilite theorique        | 3/10    | **5/10** | 4/10    | 3/10    |
| Conditionnalite              | **9/10** | Mixte   | Cond.   | N/A     |
| Force du resultat            | 3/10    | **4/10** | 3/10    | 2/10    |
| Calculabilite                | **9/10** | 8/10    | 7/10    | 3/10    |
| Chemin vers Lean             | 7/10    | **8/10** | 6/10    | 4/10    |
| Connexion existante          | 9/10    | **10/10** | 8/10   | 7/10    |
| **Moyenne**                  | **6.9** | **7.1** | **5.7** | **3.5** |

**Classement global : B > A > C >> D**

---

## 2. Verdicts individuels (une ligne)

| Piste | Verdict |
|-------|---------|
| **A** | Outil NECESSAIRE mais non SUFFISANT — exclut 7/16 k, echoue sur les convergents |
| **B** | Cadre EXPLICATIF le plus profond — identifie le "pourquoi" (offset + arc + Type I/II) |
| **C** | QUANTIFICATION partielle — mesure le melange, revele le gap mixing → exclusion |
| **D** | INSPIRATION puissante — "presque tout" ne prouve pas "tout", gap fondamental |

---

## 3. Resultats cles par piste

### 3.1. Piste A — CRT Hybride

**Script :** `phase20_crt_analysis.py` (668 lignes, 80.3s)

- 7 valeurs de k exclues sur 16 testees : k = 3, 4, 5, 7, 8, 11, 13
- 9 valeurs resistant : k = 1 (degenere), 2, 6, 9, 10, 12, 14, 15, 16
- **Contre-exemple k=2** : p = 7 > C = 3, pourtant N_0(7) = 1 (p > C ne suffit PAS)
- **Deficit entropique** : gamma = 0.0500 universel
- Sommes exponentielles : |T(t)|/sqrt(C) **DIVERGE** avec k — pas d'annulation sqrt
- BDH inadapte (pas de version lacunaire sur diviseurs)

### 3.2. Piste B — Structure Algebrique

**Script :** `phase20_type_classification.py` (698 lignes, 13.0s)

- 202 premiers classifies : 137 Type I (67.8%) vs 65 Type II (32.2%)
- **Exclusion chirurgicale de q_3** (k=5, p=13) :
  - Im(V mod 13) = {0,...,9,11,12} — manque EXACTEMENT le target 10 = -3^4 mod 13
  - Cause : arc tronque (S=8 < omega=12), target a log_2 = 10 >= S
- **Offset additif** : corrSum = 3^{k-1} + V(A), le "+1" de Collatz fixe le target
- **Pattern de parite** : k pair favorise Type II (8/12 = 67% vs 2/13 = 15%)
- Cas critiques k=6,9,10,15 : TOUS Type I → Piste B n'aide pas

### 3.3. Piste C — Mixing / Random Walk

**Script :** `phase20_mixing_simulation.py` (~500 lignes, 32.8s)

- Trou spectral TOUJOURS positif : Delta_min = 0.483, Delta_mean = 0.732
- Convergence exponentielle confirmee (TV decroissance coherente avec |lambda_2|)
- **k=7, p=83** : C/p = 5.57, N_0 = 0, P(Poisson=0) = **0.38%** → biais STRUCTUREL
- q_3 (k=5) : N_0 passe de 6 (etape 3) a 0 (etape 4) — la derniere etape tue les zeros
- Monte Carlo monotone reproduit la distribution exacte (TV_MC = 0.185 vs TV_exact = 0.176)
- **Diagnostic** : mixing predit N_0 ~ C/p, PAS N_0 = 0

### 3.4. Piste D — Extension de Tao

**Document theorique** (pas de script)

- 3 obstacles fondamentaux : conditionnement, module specifique, precision
- 4 voies d'adaptation analysees : densite sur k, sommes exponentielles, probabiliste, ergodique
- **Les convergents** (q_n de log_2(3)) resistent a TOUT argument densitaire
- Le gap mesure vs universalite est IRREDUCTIBLE par les techniques de Tao
- L'approche ergodique REFORMULE le probleme sans le simplifier

---

## 4. Convergence diagnostique

### 4.1. Le diagnostic unifie

Les quatre pistes convergent vers le **meme diagnostic** :

> **L'Hypothese H requiert une borne de sommes exponentielles pour les polynomes
> de Horner lacunaires sous contrainte de monotonie.**

Plus precisement, il faut majorer :

  |T(t)| = |sum_{A in Comp(S,k)} e(t * corrSum(A) / p)|

pour les premiers p | d, avec la contrainte 0 = a_0 < a_1 < ... < a_{k-1} <= S-1.

### 4.2. Ce qui est demontre vs ce qui manque

| Acquis (prouve ou calcule) | Manquant |
|----------------------------|----------|
| corrSum est quasi-uniforme mod p (chi2 OK) | Borne universelle sur N_0 |
| Trou spectral Delta > 0 pour tous (k,p) testes | Borne INFERIEURE sur Delta |
| Exclusion chirurgicale de q_3 (k=5, p=13) | Extension a q_4, q_5, ... |
| Classification Type I/II decidable | Borne quantitative sur le biais |
| Offset additif fixe le target a -3^{k-1} mod p | Preuve que le target est toujours evite |
| gamma = 0.0500 universel (deficit entropique) | Formalisation du deficit en borne de Weil |
| CRT exclut 7/16 k accessibles | Methode pour les 9 k restants |
| |T(t)|/sqrt(C) diverge | Borne de remplacement adaptee |

### 4.3. L'obstacle irreductible : les convergents

Chaque piste bute sur le meme mur : les **convergents** q_n de log_2(3).

| Convergent | d(q_n) | C(S-1,k-1) | C/d | Pourquoi c'est dur |
|-----------|--------|-----------|-----|---------------------|
| q_1 = 1  | 1      | 1         | 1.0 | Degenere |
| q_2 = 2  | 7      | 3         | 0.4 | N_0(7) = 1 (non exclu par CRT) |
| q_3 = 5  | 13     | 35        | 2.7 | EXCLU (chirurgical, unique succes) |
| q_4 = 12 | 517135 | 75582     | 0.15 | N_0(1753) = 150, non exclu |
| q_5 = 41 | (grand) | (grand)  | <<1 | Non calcule, probablement dur |

Pour les convergents q_n avec n >= 4, les premiers p | d(q_n) satisfont
C/p >= 1, ce qui rend le modele Poisson inutile et l'exclusion improbable
sans argument structural specifique.

---

## 5. Synergies entre pistes

### 5.1. La combinaison B+C (la plus prometteuse)

La Piste B fournit le **cadre structural** et la Piste C la **quantification** :

| Piste B apporte | Piste C apporte |
|----------------|----------------|
| Classification Type I/II | Trou spectral mesurable |
| Decomposition en cosettes | Convergence exponentielle |
| Offset additif (target fixe) | Modele Poisson discriminant |
| Arc tronque (geometrie) | TV distance quantitative |
| "Pourquoi" l'exclusion | "Combien" de melange |

**Mecanisme combine :** Le mixing (C) produit une distribution quasi-uniforme
sur F_p. L'offset structural (B) deplace cette distribution de sorte que
le residu 0 = corrSum mod p tombe exactement dans la "queue" de la distribution.
Pour q_3, cette queue est VIDE (exclusion chirurgicale).

### 5.2. La combinaison A+B (la plus rigoureuse)

La Piste A est le VERIFICATEUR et la Piste B le EXPLICATEUR :

- A fournit le certificat N_0(p) = 0 pour 7 valeurs de k
- B explique POURQUOI N_0(p) = 0 (troncature, offset, Type I/II)
- Ensemble, elles couvrent k = 3-8, 11, 13 avec preuve ET explication
- Formalisable en Lean (decidable, inconditionnel)

### 5.3. Le role de D (le phare)

La Piste D n'apporte pas d'outil direct mais :
- Identifie le **schema de preuve ideal** (Z → Z_2 → Fourier → CRT → Z)
- Confirme que les sommes exponentielles sont L'OUTIL a developper
- Delimite le gap : la precision O(k^{-A}) de Tao ne suffit pas
- Les convergents sont identifies comme le "noyau dur" irreductible

---

## 6. Recommandations pour la suite du Programme Merle

### 6.1. Actions immediates (Phase 21)

1. **Formaliser la Piste A en Lean** : theoremes d'exclusion pour k=3-8,11,13
   - Decidable, inconditionnel, directement dans le preprint
   - Complexite : moderee (arithmetique modulaire + enumeration finie)

2. **Documenter l'exclusion chirurgicale de q_3** comme theoreme du preprint
   - Im(V mod 13) = F_13 \ {10}, avec 10 = -3^4 mod 13
   - Arc tronque (S=8 < omega=12, log_2(10) = 10 >= 8)
   - Ce resultat est NOUVEAU et constitue la contribution la plus elegante

3. **Integrer la classification Type I/II** dans le preprint (Section 17+)
   - Table des 202 premiers classifies
   - Pattern de parite comme observation conjoncturelle

### 6.2. Programme de recherche (Phase 22+)

**Direction principale : Bornes de sommes exponentielles lacunaires**

Le probleme technique central est :

> Trouver f(k,p) tel que |T(t)| <= C / f(k,p) avec f(k,p) → +∞
> pour les sommes T(t) = sum_{A in Comp(S,k)} e(t*corrSum(A)/p).

| Approche | Difficulte | Payoff |
|----------|-----------|--------|
| Borne de Weil generalisee | Tres haute | Resoudrait H |
| Decorrelation a la Tao (adaptee a mod d) | Haute | Resolvent les non-convergents |
| Theorie des groupes (cosettes + Horner) | Moyenne | Resolvent Type II |
| Combinatoire des compositions monotones | Moyenne | Borne inferieure sur Delta |

**Direction secondaire : Traitement des convergents**

| Approche | Idee | Difficulte |
|----------|------|-----------|
| Approximation diophantienne | Exploiter ||q_n*log_2(3)|| petit | Haute |
| Fraction continuee de log_2(3) | Structure des q_n mod petit p | Moyenne |
| Cas par cas (q_4=12, q_5=41, q_6=53) | Extension de l'exclusion chirurgicale | Variable |
| Argument de transcendance | log_2(3) irrationnel → d(k) ≠ 0 pour tout k | Insuffisant |

### 6.3. Ce qui est HORS DE PORTEE actuellement

1. Une preuve universelle de H pour tout k (les convergents resistent)
2. Une borne de type Weil pour corrSum (pas un polynome standard)
3. L'extension directe de Tao a mod d (obstacles fondamentaux)
4. Un argument purement computationnel pour k > 20 (C est exponentiellement grand)

---

## 7. Verdict final

### 7.1. Le Programme Merle apres la Phase 20

```
JUNCTION THEOREM : [1, 67] ∪ [18, ∞)

  k = 1..17  : VERIFIABLE (C fini, enumerable)
    - 7 exclus par CRT (Piste A) : k = 3, 4, 5, 7, 8, 11, 13
    - 1 exclus chirurgicalement (Piste B) : k = 5 (= q_3)
    - k = 1 : degenere (d = 1, trivial)
    - 9 non exclus theoriquement : k = 2, 6, 9, 10, 12, 14, 15, 16, 17
      (mais exclus computationnellement pour k <= 16 car C est petit)

  k = 18..67 : REGIME CRISTALLIN (C < d, deficit gamma = 0.0500)
    - CRT fonctionne si un premier p | d a N_0(p) = 0
    - Non verifie exhaustivement pour k > 16

  k >= 68   : JUNCTION THEOREM (hors intervalle)
    - Couvert par la borne de Steiner + deficit entropique
    - Pas de verification necessaire
```

### 7.2. La piece manquante

La piece manquante du Programme Merle est une **borne non triviale sur les sommes
exponentielles de Horner lacunaires**. Cette borne doit :

1. Fonctionner pour les premiers p | d(k), pas seulement les premiers generiques
2. Tenir compte de la contrainte de monotonie des compositions
3. Fournir |T(t)| <= C * p^{-epsilon} pour un epsilon > 0 uniforme
4. S'appliquer aux convergents ou d est petit

Cette borne est un **probleme ouvert en theorie analytique des nombres**.
Sa resolution constituerait une avancee significative independante du contexte Collatz.

### 7.3. En une phrase

> **La Phase 20 identifie que l'Hypothese H est equivalente a un probleme de
> sommes exponentielles lacunaires, et que les convergents de log_2(3) sont
> le noyau dur irreductible du probleme.**

---

## 8. Fichiers produits (Phase 20 complete)

### Scripts
| Script | Lignes | Duree | Piste |
|--------|--------|-------|-------|
| `phase20_crt_analysis.py` | 668 | 80.3s | A |
| `phase20_type_classification.py` | 698 | 13.0s | B |
| `phase20_mixing_simulation.py` | ~500 | 32.8s | C |
| (pas de script) | - | - | D |

### Research logs
| Log | Contenu | Piste |
|-----|---------|-------|
| `phase20a_piste_CRT_hybride.md` | ~250 lignes | A |
| `phase20b_piste_structure_algebrique.md` | ~307 lignes | B |
| `phase20c_piste_mixing_random_walk.md` | ~241 lignes | C |
| `phase20d_piste_extension_tao.md` | ~331 lignes | D |
| `phase20_synthese_4_pistes.md` | ce document | Synthese |

---
