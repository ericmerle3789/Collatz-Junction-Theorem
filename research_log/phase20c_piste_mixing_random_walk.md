# Phase 20C — Piste Mixing / Random Walk
# Date : 28 fevrier 2026
# Auteur : Eric Merle (assiste par Claude)

---

## 1. Objectif

Explorer la Piste C : modeliser la recurrence de Horner c_{j+1} = 3*c_j + 2^{A_j}
comme une marche aleatoire dans F_p, mesurer le melange vers l'uniformite, et
determiner si le mixing seul suffit a expliquer l'exclusion du zero.

## 2. Cadre theorique

### 2.1. Operateur de transfert

La recurrence de Horner definit un operateur L sur les distributions dans F_p :

  (L*f)(s) = (1/S) * sum_{a=0}^{S-1} f(3^{-1}*(s - 2^a) mod p)

L est une matrice p x p, colonne-stochastique. Sa valeur propre dominante est
lambda_1 = 1, et le trou spectral Delta = 1 - |lambda_2| controle la vitesse
de convergence vers la distribution stationnaire.

### 2.2. Vitesse de melange

Apres j applications de L :

  ||L^j * f_0 - pi||_TV <= C * |lambda_2|^j

ou pi est la distribution stationnaire. Le temps de melange est t_mix ~ 1/|log|lambda_2||.

### 2.3. Modele Poisson

Si la distribution de corrSum mod p est quasi-uniforme, N_0 ~ Poisson(C/p).
P(N_0 = 0) = exp(-C/p). Si C/p >> 1, cette probabilite est exponentiellement petite.

---

## 3. Resultats computationnels

### 3.1. Spectre de l'operateur de transfert

Script : `scripts/phase20_mixing_simulation.py`, 7 sections.
Execution : 32.8s. SHA256 : 878eeca1f53abe07.

| (k, p) | omega | S/omega | |lambda_2| | Delta | t_mix (etapes) |
|--------|-------|---------|-----------|-------|---------------|
| (5, 13) q3 | 12 | 0.667 | 0.225 | 0.775 | 0.67 |
| (2, 7) q1 | 3 | 1.333 | 0.527 | 0.473 | 1.56 |
| (7, 23) | 11 | 1.091 | 0.219 | 0.781 | 0.66 |
| (8, 7) | 3 | 4.333 | 0.473 | 0.527 | 1.34 |

**Observation :** Le trou spectral est TOUJOURS positif (Delta > 0.47).
Le melange est le plus rapide pour p=13 et p=23 (Delta ~ 0.78), et le plus
lent pour p=7 (Delta ~ 0.48). Cela reflete le fait que omega=3 pour p=7
(petit sous-groupe <2>) offre moins de "randomisation" par etape.

### 3.2. Trou spectral systematique (k=2..19)

| k | S | p | omega | S/omega | |lambda_2| | Delta | t_mix |
|---|---|---|-------|---------|-----------|-------|-------|
| 2 | 4 | 7 | 3 | 1.333 | 0.517 | 0.483 | 1.52 |
| 3 | 5 | 5 | 4 | 1.250 | 0.374 | 0.626 | 1.02 |
| 4 | 7 | 47 | 23 | 0.304 | 0.302 | 0.698 | 0.83 |
| 5 | 8 | 13 | 12 | 0.667 | 0.232 | 0.768 | 0.68 |
| 10 | 16 | 13 | 12 | 1.333 | 0.136 | 0.864 | 0.50 |
| 15 | 24 | 13 | 12 | 2.000 | 0.083 | 0.917 | 0.40 |
| 16 | 26 | 7 | 3 | 8.667 | 0.469 | 0.531 | 1.32 |
| 19 | 31 | 19 | 18 | 1.722 | 0.065 | 0.935 | 0.37 |

**Statistiques globales (16 paires testees) :**
- min(Delta) = 0.483
- max(Delta) = 0.935
- mean(Delta) = 0.732
- **Tous Delta > 0 : le melange est UNIVERSEL pour ces (k,p)**

**Pattern :** |lambda_2| diminue quand S/omega augmente (plus de puissances de 2
disponibles → meilleur melange). Le pire cas est p=7 avec omega=3.

### 3.3. Convergence empirique de c_j

**q3 (k=5, S=8, p=13) — etape par etape :**

| Etape j | Residus atteints | N_0/C | TV distance |
|---------|-----------------|-------|-------------|
| 1 | 4/13 | 0.000 | 0.741 |
| 2 | 8/13 | 0.029 | 0.530 |
| 3 | 11/13 | 0.171 | 0.310 |
| 4 (final) | 12/13 | **0.000** | 0.176 |

**Observation remarquable :** A l'etape 3, N_0 = 6 (sur-represente !). Puis
a l'etape 4, N_0 **tombe a 0**. La derniere etape de la recursion de Horner
DETRUIT les zeros existants. C'est coherent avec l'exclusion chirurgicale
de la Piste B : l'offset 3^{k-1} + V(A) place le "point final" corrSum
hors du residu 0 malgre le bon melange des etapes precedentes.

**k=8, S=13, p=7 — convergence exponentielle :**

| Etape | TV | N_0/C |
|-------|------|-------|
| 1 | 0.607 | 0.274 |
| 2 | 0.391 | 0.073 |
| 3 | 0.174 | 0.111 |
| 4 | 0.074 | 0.138 |
| 5 | 0.030 | 0.141 |
| 6 | 0.014 | 0.141 |
| 7 (final) | 0.009 | **0.152** |

Taux de decroissance moyen : 0.50 (coherent avec |lambda_2| ~ 0.47 pour p=7).
**N_0 converge vers C/p = 0.143** — le melange predit bien le resultat.

### 3.4. Distance TV au terme final

| k | p | C | N_0 | N_0/C | 1/p | TV finale |
|---|---|---|-----|-------|-----|-----------|
| 2 | 7 | 3 | 1 | 0.333 | 0.143 | 0.571 |
| 5 | 13 | 35 | 0 | 0.000 | 0.077 | 0.176 |
| 7 | 83 | 462 | 0 | 0.000 | 0.012 | 0.117 |
| 8 | 7 | 792 | 120 | 0.152 | 0.143 | **0.009** |
| 10 | 13 | 5005 | 410 | 0.082 | 0.077 | **0.013** |
| 14 | 79 | 497420 | 6342 | 0.013 | 0.013 | **0.002** |
| 16 | 7 | 3268760 | 467096 | 0.143 | 0.143 | **0.0001** |

**Pattern :** Pour les petits premiers (p=7, p=13), la TV diminue avec k car
S/omega augmente → melange de plus en plus fort. Pour les grands premiers
(p=83, p=2617), la TV reste elevee car S/omega est petit.

### 3.5. Modele Poisson et biais structurel

| k | p | C/p | N_0 | P(Poisson=0) | Verdict |
|---|---|-----|-----|---------------|---------|
| 3 | 5 | 1.20 | 0 | 30.1% | Attendu |
| 4 | 47 | 0.43 | 0 | 65.3% | Attendu |
| 5 | 13 | 2.69 | 0 | 6.8% | Plausible |
| **7** | **83** | **5.57** | **0** | **0.38%** | **STRUCTUREL** |
| 8 | 233 | 3.40 | 0 | 3.3% | Plausible |
| 11 | 7727 | 2.52 | 0 | 8.1% | Plausible |
| 13 | 502829 | 0.25 | 0 | 77.8% | Attendu |

**Resultat cle :** Pour k=7, p=83, C/p = 5.57 et N_0 = 0. La probabilite
Poisson de cet evenement est **0.38%** — statistiquement significatif (z > 2.9).
L'exclusion du zero pour k=7 n'est PAS un phenomene de fluctuation aleatoire.
Il y a un **biais structurel anti-zero** au-dela du simple melange.

Ce biais est exactement ce que la Piste B identifie : l'offset additif
3^{k-1} et la troncature d'arc.

### 3.6. Comparaison Horner vs marche uniforme

**q3 (k=5, p=13) — distributions comparees :**

Le Monte Carlo avec contrainte monotone reproduit fidelement la distribution
exacte (TV_MC_mono = 0.185 vs TV_exact = 0.176). La contrainte de monotonie
N'EST PAS la source principale du biais — c'est la structure de Horner elle-meme
(l'offset 3^{k-1}) qui biaise.

Le Monte Carlo uniforme (sans monotonie) donne une distribution quasi-uniforme
(TV ~ 0.015, bruit d'echantillonnage seulement), confirmant que c'est la
structure des compositions qui cree le biais.

---

## 4. Diagnostic

### 4.1. Le melange est reel mais insuffisant

Le trou spectral positif (Delta > 0.48 pour tous les cas testes) signifie que
la recurrence de Horner converge exponentiellement vers une distribution
quasi-uniforme. Cela explique pourquoi N_0 ~ C/p dans la plupart des cas.

Mais le melange predit N_0 ~ C/p, pas N_0 = 0. Pour les cas ou C/p > 1,
le modele Poisson predit N_0 >= 1 avec haute probabilite.

### 4.2. Le gap mixing → exclusion

La distance entre "N_0 ~ C/p" et "N_0 = 0" est exactement l'Hypothese H.
Le melange fournit le background (quasi-uniformite), mais l'exclusion
du zero requiert un ingredient supplementaire : le biais structural de la Piste B.

### 4.3. Convergents : le pire cas

Pour les convergents (d petit, C ~ d), les seuls premiers p | d disponibles
satisfont C/p >= 1. Le modele Poisson predit N_0 ~ C/p >= 1. L'exclusion
N_0 = 0 pour ces cas est la partie la plus difficile du probleme, et ni
le mixing (Piste C) ni l'algebre seule (Piste B) ne la resout.

---

## 5. Verdict

### 5.1. Forces

1. **Quantification du melange** : trou spectral mesurable pour tout (k,p)
2. **Convergence exponentielle verifiee** empiriquement et coherente avec la theorie
3. **Modele Poisson discriminant** : distingue exclusion "attendue" vs "structurelle"
4. **Confirmation du biais** : k=7 (P=0.38%) est statistiquement significatif
5. **Operateur de transfert formalisable** en Lean (matrice p x p finie)

### 5.2. Limites

1. **Pas de borne universelle** sur le trou spectral (depend de p)
2. **Mixing ≠ exclusion** : predit N_0 ~ C/p, pas N_0 = 0
3. **Contrainte de monotonie** brise l'hypothese i.i.d.
4. **Calcul matriciel** infaisable pour p > 50
5. **Ne resout pas les convergents** (C/p > 1)

### 5.3. Grille d'evaluation

| Critere | Score | Commentaire |
|---------|-------|-------------|
| Faisabilite computationnelle | 7/10 | Exact pour p<=50, estimation pour p>50 |
| Faisabilite theorique | 4/10 | Prouvable pour p fixe, pas universel |
| Conditionnalite | Conditionnel | Bornes sur lambda_2 non demontrees |
| Force du resultat | 3/10 | Quasi-uniformite, pas exclusion |
| Calculabilite | 7/10 | Operateur matriciel |
| Chemin vers Lean | 6/10 | Operateur formalisable |
| Connexion existante | 8/10 | Phase 16 (operateur de transfert, Parseval) |

### 5.4. Conclusion

**PISTE C = QUANTIFICATION PARTIELLE, REVELE LE GAP MIXING vs EXCLUSION**

La Piste C montre que le melange est reel (trou spectral > 0) et produit
une quasi-uniformite (TV → 0 exponentiellement). Mais elle revele aussi
que le mixing SEUL ne suffit pas : l'exclusion du zero est un phenomene
**structurel** (Piste B) amplifie par le melange (Piste C).

La combinaison B+C donne le cadre le plus complet : le mixing fournit
le fond quasi-uniforme, et le biais structural de l'offset "+1" de
Collatz + la troncature d'arc font tomber N_0 a zero.

---

## 6. Fichiers produits

- `scripts/phase20_mixing_simulation.py` (~500 lignes, 7 sections)
- `research_log/phase20c_piste_mixing_random_walk.md` (ce document)

---
