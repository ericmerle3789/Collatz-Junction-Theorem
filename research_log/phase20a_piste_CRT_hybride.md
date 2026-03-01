# Phase 20A — Piste CRT Hybride + Computationnel
# Date : 27 fevrier 2026
# Auteur : Eric Merle (assiste par Claude)

---

## 1. Objectif

Explorer la strategie CRT (Proposition 16.4) : pour chaque d(k) = 2^S - 3^k,
trouver un premier p | d tel que N_0(p) = 0, ce qui impliquerait 0 notin Im(Ev_d)
et donc l'absence de cycle de longueur k.

## 2. Cadre theorique

### 2.1. Rappels

**Equation de Steiner (1977)** : n_0 * d = corrSum(A) ou d = 2^S - 3^k, S = ceil(k*log2(3)).

**Proposition 16.4 (CRT)** : Si il existe un premier p | d avec
N_0(p) := |{A in Comp(S,k) : corrSum(A) = 0 mod p}| = 0,
alors 0 notin Im(Ev_d).

**Formule d'orthogonalite** : N_0(p) = C/p + (1/p) * sum_{t=1}^{p-1} T(t)
ou C = C(S-1,k-1) et T(t) = sum_A exp(2*pi*i*t*corrSum(A)/p).

### 2.2. Strategies potentielles

1. **Victoire triviale** : trouver p | d avec p > C => au plus C residus touches mod p,
   mais ATTENTION : p > C ne garantit PAS N_0(p) = 0 (contre-exemple ci-dessous).
2. **Bornes de Weil** : majorer |T(t)| pour montrer |R(p)| < C/p.
3. **BDH (Barban-Davenport-Halberstam)** : borne en moyenne sur les ecarts.

---

## 3. Resultats computationnels

### 3.1. Table des modules cristallins

Script : `scripts/phase20_crt_analysis.py`, 7 sections, 668 lignes.
Execution : 80.3s. SHA256 : 0f452b0a1588a1c0.

**Classification des 67 valeurs de k :**

| Regime      | Comptage | Definition                           |
|-------------|----------|--------------------------------------|
| Residuel    | 4        | C >= d (k = 1, 3, 5, 17)            |
| Frontiere   | 13       | k < 18 et C < d (k = 2,4,6..16)     |
| Cristallin  | 50       | k >= 18 (non-surjectivite C < d)     |

**Deficit entropique universel :** gamma = 0.0500444728.

### 3.2. Calcul exhaustif de N_0(p) (C <= 5*10^6)

16 valeurs de k testees exhaustivement (k = 1 a 16).

**Zero exclu par CRT (7 valeurs) :**

| k  | S  | C      | p victoire | N_0(p) | Mecanisme                       |
|----|----|--------|------------|--------|----------------------------------|
| 3  | 5  | 6      | 5          | 0      | p > C (5 < 6 MAIS N_0 = 0)      |
| 4  | 7  | 20     | 47         | 0      | p > C (47 > 20)                  |
| 5  | 8  | 35     | 13         | 0      | N_0 = 0 malgre C/p = 2.69       |
| 7  | 12 | 462    | 83         | 0      | N_0 = 0 malgre C/p = 5.57       |
| 8  | 13 | 792    | 233        | 0      | N_0 = 0 malgre C/p = 3.40       |
| 11 | 18 | 19448  | 7727       | 0      | N_0 = 0 malgre C/p = 2.52       |
| 13 | 21 | 125970 | 502829     | 0      | p > C (502829 > 125970)          |

**Zero NON exclu par CRT (9 valeurs) :**

| k  | S  | C        | d          | Facteurs p | N_0 minimal     |
|----|----|---------:|------------|------------|-----------------|
| 1  | 2  | 1        | 1          | (aucun)    | d=1, degenere   |
| 2  | 4  | 3        | 7          | 7          | N_0(7) = 1      |
| 6  | 10 | 126      | 295        | 5, 59      | N_0(59) = 6     |
| 9  | 15 | 3003     | 13085      | 5, 2617    | N_0(2617) = 6   |
| 10 | 16 | 5005     | 6487       | 13, 499    | N_0(499) = 35   |
| 12 | 20 | 75582    | 517135     | 5,59,1753  | N_0(1753) = 150 |
| 14 | 23 | 497420   | 3605639    | 79, 45641  | N_0(45641) = 28 |
| 15 | 24 | 817190   | 2428309    | 13, 186793 | N_0(186793) = 50|
| 16 | 26 | 3268760  | 24062143   | 7,233,14753| N_0(14753) = 984|

### 3.3. Contre-exemple fondamental : k = 2

**Fait observe :** Pour k = 2, p = 7 > C = 3, pourtant N_0(7) = 1 != 0.

Les 3 compositions de Comp(4, 2) = {(0,1), (0,2), (0,3)} donnent :
- corrSum(0,1) = 3 + 2 = 5 (mod 7)
- corrSum(0,2) = 3 + 4 = 7 = 0 (mod 7)  <--- ZERO ATTEINT
- corrSum(0,3) = 3 + 8 = 11 = 4 (mod 7)

**Consequence :** L'affirmation "p > C implique N_0(p) = 0" est FAUSSE.
La non-surjectivite ne garantit pas l'exclusion de 0 specifiquement.
Il faut une analyse structurelle supplementaire.

---

## 4. Analyse des sommes exponentielles

### 4.1. Bornes de Weil

Pour q_3 (k=5, S=8, p=13, C=35) :
- max|T(t)| = 8.0254 (atteint pour t=2 et t=11)
- max|T(t)|/C = 0.2293
- max|T(t)|/sqrt(C) = 1.3565 > 1

**Borne de Weil naive** : (k-1)*sqrt(p) = 4*sqrt(13) = 14.42.
L'observation (8.03) est inferieure, ratio 0.56.

### 4.2. Absence d'annulation en racine carree

| k  | p    | C     | max|T|/sqrt(C) | Verdict            |
|----|------|-------|---------------|---------------------|
| 2  | 7    | 3     | 0.82          | Annulation OK       |
| 5  | 13   | 35    | 1.36          | Pas d'annulation    |
| 8  | 7    | 792   | 0.28          | Bonne annulation    |
| 9  | 2617 | 3003  | 7.78          | TRES mauvais        |
| 11 | 7727 | 19448 | 5.56          | TRES mauvais        |
| 12 | 1753 | 75582 | 15.24         | Catastrophique      |

**Observation critique :** Le ratio max|T|/sqrt(C) DIVERGE avec k pour les
grands premiers. Il n'y a PAS d'annulation en racine carree pour les sommes
de Horner lacunaires. Cela reflete les correlations induites par la contrainte
de monotonie 0 = a_0 < a_1 < ... < a_{k-1} <= S-1.

### 4.3. Analyse structurelle de la divergence

Pour les compositions A in Comp(S,k), la "convolution" de Horner :
  c_{j+1} = 3 * c_j + 2^{A_j} (mod p)
est une composition d'applications affines f_a : x -> 3x + 2^a.

La contrainte de monotonie A_0 < A_1 < ... < A_{k-1} cree des correlations :
- 57.1% des gaps sont de taille 1
- Le gap moyen est 1.60 (vs 2.00 attendu pour uniforme)
- log2(3) = 1.5850, donc gap moyen proche de log2(3) — coherent avec gamma

Ces correlations empechent le decouplage necesssaire pour l'annulation sqrt.

---

## 5. Analogue de Barban-Davenport-Halberstam

### 5.1. Enonce du probleme

L'analogue BDH serait :
  sum_{p | d} sum_{r mod p} |N_r(p) - C/p|^2 <= c * C * (...)

### 5.2. Resultats numeriques

| k  | p    | C     | sum|N_r-C/p|^2 | C^2/p    | ratio   |
|----|------|-------|----------------|----------|---------|
| 5  | 13   | 35    | 22.77          | 94.23    | 0.2416  |
| 8  | 7    | 792   | 54.86          | 89609.14 | 0.0006  |
| 9  | 2617 | 3003  | 2865.07        | 3445.93  | 0.8314  |
| 11 | 7727 | 19448 | 14417.55       | 48948.45 | 0.2945  |
| 12 | 1753 | 75582 | (non calc)     | (large)  | -       |

### 5.3. Conclusion BDH

L'analogue BDH **n'est pas applicable** pour trois raisons :
1. Sommation sur les diviseurs de d (ensemble creux), pas sur tous q <= Q
2. corrSum n'est pas une fonction arithmetique standard (pas multiplicative)
3. La structure de Horner lacunaire cree des correlations specifiques

La quasi-equidistribution est confirmee (chi2 accepte) mais ne suffit pas
pour prouver N_0 = 0 quand C/p >> 1.

---

## 6. Diagnostic : pourquoi la Piste A echoue pour les convergents

### 6.1. Les convergents p_n/q_n de log2(3)

Les "convergents" sont les k tels que d(k) est petit (k/S proche de 1/log2(3)).
Pour ces k, d = 2^S - 3^k est exponentiellement plus petit que C = C(S-1,k-1).

Exemples :
- k=5 : d = 13, C = 35, ratio C/d = 2.69
- k=10 : d = 6487, C = 5005, ratio C/d = 0.77 (proche du seuil)
- k=17 : d = 5013485, C = 5311735, ratio C/d = 1.06 (residuel !)

### 6.2. L'obstacle fondamental

Pour un convergent k avec d petit, les facteurs premiers p de d satisfont
TOUS p <= d < C^{1+epsilon}. Donc C/p >= 1 pour tout p | d, et la prediction
naive donne N_0(p) ~ C/p >= 1.

Prouver N_0(p) = 0 pour un tel p revient exactement a prouver l'Hypothese H
pour ce k specifique — il n'y a pas de raccourci CRT.

### 6.3. Quantification

Les cas critiques non resolus par CRT (k = 2, 6, 9, 10, 12, 14, 15, 16)
correspondent EXACTEMENT aux k ou le plus petit N_0(p) est strictement > 0
pour tous les p | d. La distribution des residus est quasi-uniforme, et
le residue 0 est "generiquement" represente a hauteur de C/p.

---

## 7. Verdict

### 7.1. Forces

1. **Inconditionnelle** : la strategie CRT ne depend d'aucune conjecture
2. **Constructive** : fournit un certificat verifiable (le p avec N_0(p) = 0)
3. **Efficace pour 7/16 k** : exclut directement k = 3,4,5,7,8,11,13
4. **Formalisable en Lean** : l'algorithme est decidable pour k fixe

### 7.2. Limites

1. **Echoue pour 9/16 k accessibles** : les convergents resistent
2. **Non scalable** : C croit exponentiellement, exhaustif impossible pour k > 20
3. **Bornes de Weil inapplicables** : corrSum n'est pas polynomiale
4. **BDH inadapte** : pas de version pour sommes lacunaires sur diviseurs
5. **Contre-exemple k=2** : p > C ne garantit pas N_0(p) = 0

### 7.3. Grille d'evaluation

| Critere                    | Score | Commentaire                          |
|----------------------------|-------|--------------------------------------|
| Faisabilite computationnelle | 8/10 | Exhaustif pour k <= ~20              |
| Faisabilite theorique       | 3/10 | Bornes de Weil inapplicables         |
| Conditionnalite             | 9/10 | Inconditionnel (pour k testes)       |
| Force du resultat           | 3/10 | Partiel (k par k, pas universel)     |
| Calculabilite               | 9/10 | Algorithmique, verifiable            |
| Chemin vers Lean            | 7/10 | decidable pour k fixe                |
| Connexion existante         | 9/10 | Utilise directement Phase 16         |

### 7.4. Conclusion

**La Piste A est un outil NECESSAIRE mais NON SUFFISANT.**

Elle fournit la verification computationnelle la plus directe possible et
confirme l'exclusion pour 7 des 16 valeurs accessibles. Mais elle ne peut
pas resoudre le probleme pour les convergents (d petit), qui constituent
precisement les cas les plus delicats.

**Questions ouvertes pour les pistes suivantes :**
1. Existe-t-il une structure algebrique (Piste B) qui distingue 0 des autres residus ?
2. La marche de Horner (Piste C) a-t-elle un biais anti-zero mesurable ?
3. Un argument de densite (Piste D) peut-il contourner les convergents ?

---

## 8. Fichiers produits

- `scripts/phase20_crt_analysis.py` (668 lignes, 7 sections)
- `research_log/phase20a_piste_CRT_hybride.md` (ce document)

---
