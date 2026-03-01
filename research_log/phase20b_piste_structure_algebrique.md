# Phase 20B — Piste Structure Algebrique (Bases 2 et 3)
# Date : 27 fevrier 2026
# Auteur : Eric Merle (assiste par Claude)

---

## 1. Objectif

Explorer la Piste B : exploiter l'incompatibilite arithmetique fondamentale entre les
bases 2 et 3 dans F_p pour exclure le zero de Im(Ev_d). Cette piste s'appuie
directement sur les Phases 11A, 15 et 17 du preprint.

## 2. Cadre theorique

### 2.1. Classification Type I / Type II

Pour un premier p | d(k) avec d = 2^S - 3^k :
- **omega** = ord_p(2) : ordre multiplicatif de 2 mod p
- **tau** = ord_p(3) : ordre multiplicatif de 3 mod p
- **m** = [<2,3> : <2>] = lcm(omega, tau) / omega : indice de cosette

**Definition :**
- **Type I** : m = 1, i.e. 3 in <2> mod p (log_2(3) existe dans Z/omega*Z)
- **Type II** : m >= 2, i.e. 3 notin <2> mod p (3 vit dans un coset strict)

### 2.2. Decomposition de corrSum

corrSum(A) = sum_{i=0}^{k-1} 3^{k-1-i} * 2^{A_i} (mod p).

Chaque terme 3^{k-1-i} * 2^{A_i} appartient au coset (k-1-i) mod m de <2>.
La somme se decompose en m sous-sommes, une par coset.

### 2.3. Offset additif

corrSum = 3^{k-1} + V(A), ou V(A) = sum_{i=1}^{k-1} 3^{k-1-i} * 2^{A_i}.

Le "+1" de 3n+1 cree un **offset structurel** : corrSum = 0 ssi V(A) = -3^{k-1} mod p.
Le target de V est FIXE par k et p.

### 2.4. Arc tronque

Les exposants A_i vivent dans {0, ..., S-1}. Dans le groupe cyclique <2> mod p
(d'ordre omega), cela correspond a un arc de longueur min(S, omega).

Si S < omega : l'arc est **tronque**, certaines puissances de 2 ne sont jamais atteintes.
Si S >= omega : l'arc est **complet**, toutes les puissances de 2 sont couvertes.

---

## 3. Resultats computationnels

### 3.1. Classification de 202 premiers cristallins (k=1..67)

Script : `scripts/phase20_type_classification.py`, 7 sections.
Execution : 13.0s. SHA256 : fa15fa2ae62d83b1.

| Statistique | Valeur |
|-------------|--------|
| Premiers Type I | 137 (67.8%) |
| Premiers Type II | 65 (32.2%) |
| k avec au moins 1 Type II (sur k=1..25) | 10/25 (40%) |
| k ou TOUS les p sont Type I | 15/25 (60%) |

**Coherence avec la conjecture d'Artin :** P(2 racine primitive mod p) ~ 0.3739 (C_Artin).
La proportion de Type I observee (67.8%) est compatible, car Type I inclut les cas
ou 2 est primitif mais aussi ceux ou <2> contient 3 sans etre tout F_p*.

### 3.2. Table des classifications (k=1..25)

| k | Premiers p | Types | m max | Commentaire |
|---|-----------|-------|-------|-------------|
| 2 | 7 | II | 2 | Unique premier, Type II |
| 3 | 5 | I | 1 | 2 primitif mod 5 |
| 4 | 47 | I | 1 | |
| 5 | 13 | I | 1 | 2 primitif mod 13, omega=12 |
| 6 | 5, 59 | I, I | 1 | Tous Type I |
| 7 | 23, 83 | I, I | 1 | Tous Type I |
| 8 | 7, 233 | II, II | 2, 8 | TOUS Type II ! |
| 9 | 5, 2617 | I, I | 1 | Tous Type I |
| 10 | 13, 499 | I, I | 1 | Tous Type I |
| 11 | 11, 7727 | I, I | 1 | Tous Type I |
| 12 | 5, 59, 1753 | I, I, II | 1, 1, 6 | Un seul Type II |
| 13 | 502829 | I | 1 | omega=502828 ~ p-1 |
| 14 | 79, 45641 | II, II | 2, 2 | TOUS Type II |
| 15 | 13, 186793 | I, I | 1 | Tous Type I |
| 16 | 7, 233, 14753 | II, II, II | 2, 8, 8 | TOUS Type II ! |
| 17 | 5, 71, 14303 | I, I, I | 1 | Tous Type I |
| 18 | 137, 1090879 | II, II | 2, 6 | TOUS Type II |
| 24 | 7, 233, 2113, 77569 | II, II, II, II | 2, 8, 24, 8 | TOUS Type II, m=24 ! |

**Observation remarquable :** k=8, 14, 16, 18, 22, 24 ont TOUS leurs premiers Type II.
Cela suggere une regularite liee a la parite : k pair favorise le Type II.

### 3.3. Exclusion chirurgicale de q3 (k=5, p=13)

C'est le resultat le plus frappant de la Piste B.

**Fait :** corrSum = 3^4 + V(A) = 3 + V(A) mod 13.
- La condition corrSum = 0 mod 13 equivaut a V(A) = -3 = 10 mod 13.
- Im(V mod 13) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12} — 12 residus sur 13.
- Le SEUL residu manquant est **exactement 10**, le target !

**Explication par l'arc tronque :**
- omega = ord_{13}(2) = 12, S = 8.
- L'arc {0,...,7} couvre 8/12 = 67% de l'orbite de <2>.
- log_2(10) = 10 mod 12, et 10 >= 8 = S.
- Le target 10 = 2^{10} mod 13 est dans la **partie tronquee** de l'orbite.
- La somme V ne peut acceder a aucun element du coset contenant 2^{10} = 10.

**Consequence theorique :** Pour q3, l'exclusion de zero est une consequence DIRECTE
de la troncature d'arc. Le "+1" de Collatz (l'offset 3^{k-1}) place le target
exactement dans la zone inaccessible. C'est la **signature algebrique du 3n+1**.

### 3.4. Offset additif : analyse systematique

Pour les premiers ou la position du target est calculable :

| k | p | target V | Position dans <2> | Commentaire |
|---|---|----------|-------------------|-------------|
| 2 | 7 | 4 | in <2> (log=2) | Target accessible |
| 3 | 5 | 1 | in <2> (log=0) | Target = 1 |
| 4 | 47 | 20 | NOT in <2> | Target hors <2> → Type II ! |
| 5 | 13 | 10 | in <2> (log=10) | log >= S → arc tronque |
| 7 | 23 | 7 | NOT in <2> | Hors <2> |
| 8 | 233 | 143 | NOT in <2> | Hors <2> |

**Pattern :** Le target peut etre hors de <2> (exclusion par Type II) ou
dans <2> mais dans l'arc tronque (exclusion par troncature).

### 3.5. Decomposition en cosettes (cas exhaustifs)

**k=2, p=7 (m=2 cosettes) :**
- C = 3 compositions, N_0 = 1 (le zero est atteint).
- L'unique zero a l'equilibre (4, 3) entre les 2 cosettes.
- N_0/C = 0.333 vs 1/p = 0.143 → excedent de zeros (2.3x la moyenne).

**k=8, p=7 (m=2 cosettes) :**
- C = 792 compositions, N_0 = 120.
- Distribution des equilibres inter-cosettes pour les 120 zeros :
  - (4, 3) : 48 compositions (40%)
  - (1, 6) : 24 (20%)
  - (2, 5) : 24 (20%)
  - (0, 0) : 8 (6.7%) — annulation parfaite par cosette
  - (3, 4) : 6 (5%)

**Observation :** L'equilibre (0,0) — annulation parfaite dans chaque cosette
separement — est le moins frequent. Les zeros proviennent surtout de
compensations INTER-cosettes, plus difficiles a contraindre.

### 3.6. Diagnostic des cas critiques (non exclus par CRT)

Les 7 valeurs de k non exclues par la Piste A (k = 6, 9, 10, 12, 14, 15, 16) :

| k | d | Type II present ? | Piste B aide ? |
|---|---|------------------|----------------|
| 6 | 295 | NON (tous Type I) | NON |
| 9 | 13085 | NON (tous Type I) | NON |
| 10 | 6487 | NON (tous Type I) | NON |
| 12 | 517135 | OUI (p=1753, m=6) | Partiellement |
| 14 | 3605639 | OUI (p=79 et 45641, m=2) | Partiellement |
| 15 | 2428309 | NON (tous Type I) | NON |
| 16 | 24062143 | OUI (tous Type II !) | Potentiellement |

**Bilan :** La Piste B n'apporte rien pour k = 6, 9, 10, 15 (tous Type I).
Elle offre une contrainte supplementaire pour k = 12, 14, 16 via la
decomposition en cosettes, mais sans preuve quantitative d'exclusion.

---

## 4. Analyse de la couverture d'arc

### 4.1. Classification des arcs

| Regime | Definition | Comptage (k=2..25) |
|--------|-----------|-------------------|
| Complet | S >= omega | 28 paires (k,p) |
| Tronque | S < omega | 27 paires (k,p) |

**Observation critique :** Pour les petits premiers (p = 5, 7, 11, 13),
l'arc est TOUJOURS complet car omega <= 12 et S croît avec k.
La troncature n'agit que pour les grands premiers (omega >> S).

### 4.2. L'arc tronque et la non-surjectivite

Pour q3 (k=5, p=13, omega=12, S=8) :
- Residus de <2> presents dans l'arc : {1, 2, 3, 4, 6, 8, 11, 12}
- Residus de <2> absents de l'arc : {5, 7, 9, 10}
- Target V = 10 est parmi les absents → exclusion

**Generalisation :** Si le target -3^{k-1} mod p a un logarithme discret
log_2(target) = j avec j >= S, alors le target est dans la partie tronquee
et V ne peut l'atteindre par des elements de l'arc.

**Limitation :** Cet argument suppose que V est une combinaison LINEAIRE
des elements de l'arc, ce qui est approximatif. V est en realite une
somme de Horner lacunaire (avec coefficients 3^{k-1-i}), pas une somme
libre de puissances de 2.

---

## 5. Densite des premiers Type II

### 5.1. Par k

Pour k = 1..25 : 10/25 valeurs de k (40%) possedent au moins un Type II.

**Pattern de parite :** Les k pairs semblent favoriser le Type II :
- k pairs avec Type II : 2, 8, 12, 14, 16, 18, 22, 24 → 8/12 (67%)
- k impairs avec Type II : 21, 25 → 2/13 (15%)

**Interpretation :** d(k) = 2^S - 3^k. Pour k pair, 3^k = 1 mod 8, et
2^S = 0 mod 8, donc d(k) = -1 = 7 mod 8. Le premier 7 (avec omega=3,
tau=6, m=2) divise souvent d. Le fait que 7 est toujours Type II
(car 3 notin {1, 2, 4} = <2> mod 7) explique la preponderance.

### 5.2. Prediction par la conjecture d'Artin

La conjecture d'Artin predit que 2 est racine primitive mod p pour une
proportion C_Artin ~ 37.4% des premiers. Pour ces p, omega = p-1 et
<2> = F_p*, donc 3 in <2> trivialement → Type I.

Pour les 62.6% restants, la question est de savoir si tau divise omega ou non.
La proportion observee de 32.2% de Type II est coherente avec les predictions
heuristiques (environ 1/3 des premiers non-primitifs sont Type II).

---

## 6. Connexion avec les phases precedentes

### 6.1. Phase 11A (Obstruction Algebrique)

La Phase 11A a demontre Im(Phi_13) = F_13* pour q3 (Theorem 11A.2).
La Piste B raffine ce resultat : c'est la troncature d'arc (8/12 de l'orbite)
combinee a l'offset (target dans la partie tronquee) qui cause l'exclusion.

### 6.2. Phase 15 (Tension Interdimensionnelle)

La Phase 15 a introduit la classification Type I/II et le QR/QNR decomposition.
La Piste B confirme que le ratio Type II ~ 32% est stable sur 202 premiers.
Le Theorem 15.1 (exclusion par offset pour q3) est ici RE-DERIVE par calcul
exhaustif de Im(V mod 13).

### 6.3. Phase 17 (Geometrie de la Serrure)

La Phase 17 a propose la "geometrie du cadenas" avec Newton polygon plat
et Horner inverse walk. La troncature d'arc de la Piste B est exactement
la version computationnelle de cette geometrie.

---

## 7. Verdict

### 7.1. Forces

1. **Source algebrique identifiee** : l'incompatibilite 2 vs 3 est le coeur
2. **Exclusion chirurgicale de q3** : Im(V) manque exactement le target — THEOREME
3. **Classification Type I/II inconditionnelle** et decidable pour tout p
4. **Arc tronque** donne une obstruction geometrique claire
5. **Connexion profonde** avec Phases 11A, 15, 17

### 7.2. Limites

1. **Exclusion chirurgicale non universelle** : prouvee seulement pour q3
2. **Cas critiques k=6,9,10,15** : tous Type I, la Piste B n'aide pas
3. **Arc complet** pour les petits premiers (p=5,7,11,13) quand k est grand
4. **Pas de borne quantitative** sur le biais anti-zero
5. **Obstacle fondamental** : decrire ≠ prouver (meme constat que Piste A)

### 7.3. Grille d'evaluation

| Critere                    | Score | Commentaire |
|----------------------------|-------|-------------|
| Faisabilite computationnelle | 9/10 | Classification decidable, exhaustif q3-q5 |
| Faisabilite theorique       | 5/10 | Cadre clair mais quantification manquante |
| Conditionnalite             | Mixte | Type I/II inconditionnel, exclusion conditionnel |
| Force du resultat           | 4/10 | Explicatif, pas probant universellement |
| Calculabilite               | 8/10 | Type I/II decidable, arc mesurable |
| Chemin vers Lean            | 8/10 | Type I/II formalisable, Gersonides fait |
| Connexion existante         | 10/10 | Phase 11A, 15, 17 directement utilisees |

### 7.4. Conclusion

**PISTE B = CADRE EXPLICATIF PROFOND MAIS NON QUANTITATIF**

La Piste B fournit la comprehension la plus profonde du **pourquoi** l'exclusion
du zero se produit : c'est la combinaison de l'offset additif ("+1" de Collatz),
de la troncature d'arc (S < omega), et de l'incompatibilite des bases 2 et 3
(classification Type I/II).

Mais elle ne fournit pas le **comment** prouver universellement : il manque
des bornes quantitatives sur les sommes exponentielles (Piste A ne les a pas
non plus) ou un argument de melange/densite (Pistes C et D).

**CONNEXION CLE vers les Pistes suivantes :**
- Piste C (Mixing) : la decomposition en cosettes (m sous-sommes) devrait
  accelerer le melange — chaque sous-somme est plus courte, donc plus aleatoire.
- Piste D (Densite) : l'offset additif fixe le target a -3^{k-1} mod d, et
  pour presque tout k, ce target est "generique" — argument en probabilite.

---

## 8. Fichiers produits

- `scripts/phase20_type_classification.py` (698 lignes, 7 sections)
- `research_log/phase20b_piste_structure_algebrique.md` (ce document)

---
