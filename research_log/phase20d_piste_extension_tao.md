# Phase 20D — Piste Extension de Tao (2022)
# Date : 28 fevrier 2026
# Auteur : Eric Merle (assiste par Claude)

---

## 1. Objectif

Explorer la Piste D : evaluer dans quelle mesure le resultat de Tao (2022) —
"presque toutes les orbites de Collatz atteignent des valeurs presque bornees" —
peut etre adapte ou etendu pour prouver l'absence de cycles positifs non triviaux,
c'est-a-dire l'Hypothese H (exclusion du zero dans Im(Ev_d)).

## 2. Le resultat de Tao (2022)

### 2.1. Enonce

**Theoreme (Tao, 2022).** Pour toute fonction f : N → R+ avec f(n) → +∞,
l'ensemble {n in N : Col^k(n) > f(n) pour tout k >= 0} a densite logarithmique
nulle.

Autrement dit : pour presque tout entier n (au sens de la densite logarithmique),
l'orbite de Collatz de n finit par descendre en dessous de n'importe quelle
borne croissante. En particulier, Col_min(n) = 1 pour une proportion 1 des entiers.

### 2.2. Methode de Tao

La preuve utilise trois ingredients :

1. **Completions 2-adiques (Z_2).** Les iterations de Collatz s'ecrivent naturellement
   dans Z_2 : le choix entre n/2 et (3n+1)/2 est determine par la parite, i.e.
   par le chiffre 2-adique a_j de n. Tao travaille avec la mesure de Haar sur Z_2.

2. **Syracuse map et sommes exponentielles.** La variable de Syracuse
   Syrac_k(n) = sum_{m=1}^{k} 3^{k-m} * 2^{-(a_m+...+a_k)} (mod 3^k)
   est analysee via des sommes exponentielles sur Z/3^k Z.

3. **Decorrelation polynomiale.** Tao montre que les correlations entre les
   a_j decroissent polynomialement : |E[e(xi*Syrac_k/3^k)]| << k^{-A} pour
   tout A, si 3 ne divise pas xi. Cela signifie que la distribution de Syracuse
   converge vers l'uniformite sur Z/3^k Z a vitesse polynomiale.

### 2.3. Forces de l'approche

- **Inconditionnelle** : aucune conjecture n'est requise.
- **Universelle** : s'applique a "presque tous" les n, pas a un n specifique.
- **Analytique** : utilise les sommes exponentielles — outil le plus puissant connu.
- **En mesure** : travaille avec la densite, pas avec des elements individuels.

### 2.4. Limites fondamentales

- **"Presque tout" ≠ "tout"** : le resultat ne dit RIEN sur un n specifique.
- **"Presque borne" ≠ "atteint 1"** : il ne prouve pas la conjecture de Collatz.
- **Regime non conditionne** : Tao travaille avec des n GENERIQUES, pas avec
  des n satisfaisant une equation arithmetique (corrSum = 0 mod d).

---

## 3. Le gap entre Tao et l'Hypothese H

### 3.1. Formulation du probleme

L'Hypothese H affirme : pour tout k >= 1 et tout d = d(k) = 2^S - 3^k :

  0 ∉ Im(Ev_d) = {corrSum(A) mod d : A in Comp(S, k)}

Equivalemment : il n'existe aucune composition A = (0 = a_0 < a_1 < ... < a_{k-1})
dans {0, ..., S-1} telle que corrSum(A) := sum_{j=0}^{k-1} 3^{k-1-j} * 2^{a_j} = 0 mod d.

### 3.2. Les trois obstacles a l'extension de Tao

**Obstacle 1 : Conditionnement**

Tao travaille avec des n GENERIQUES (distribution quasi-uniforme de la parite).
L'Hypothese H demande une propriete sur des compositions A CONTRAINTES par :
- Monotonie stricte (a_0 < a_1 < ... < a_{k-1})
- Borne superieure (a_{k-1} <= S-1)
- Equation de Steiner : corrSum = 0 mod d

Le conditionnement sur corrSum = 0 mod d est un evenement de probabilite ~1/d,
et les techniques "en mesure" de Tao ne s'appliquent pas directement a un
sous-ensemble aussi rarefie.

**Obstacle 2 : Module specifique**

Tao travaille modulo 3^k (la puissance de 3 dans l'equation de Collatz).
L'Hypothese H travaille modulo d = 2^S - 3^k, un entier COMPOSITE dont la
structure arithmetique depend de k. Le passage de "mod 3^k" a "mod d" est
non trivial car :
- d n'est pas une puissance de premier
- Les facteurs premiers de d dependent de k de maniere erratique
- La theorie des caracteres sur Z/dZ est plus complexe (CRT)

**Obstacle 3 : Precision requise**

Le resultat de Tao donne une convergence en O(k^{-A}) pour la distance
entre la distribution de Syracuse et l'uniformite. Mais l'Hypothese H
requiert une precision ABSOLUE : N_0 = 0, pas N_0 ≈ 0.

Pour les convergents (d petit, C ~ d), C/p ~ 1 pour les petits premiers
p | d. La prediction "quasi-uniforme" donne N_0 ~ C/p ~ 1, et la
difference entre N_0 = 0 et N_0 = 1 requiert une precision superieure
a celle fournie par Tao.

### 3.3. Quantification du gap

| Aspect | Tao (2022) | Hypothese H |
|--------|-----------|-------------|
| Regime | Presque tout n | Pour TOUT k |
| Module | 3^k (puissance de premier) | d = 2^S - 3^k (composite) |
| Precision | O(k^{-A}) | Exacte (N_0 = 0 ou ≠ 0) |
| Conditionnement | Inconditionnel | Conditionne sur corrSum = 0 mod d |
| Monotonie | Non contrainte | a_0 < a_1 < ... < a_{k-1} |
| Nature | Densitaire (mesure) | Universelle (pour chaque k) |

---

## 4. Voies d'adaptation possibles

### 4.1. Voie 1 : Argument de densite sur les k

**Idee :** Adapter l'argument "presque tout" de Tao aux k (longueurs de cycle)
au lieu des n (entiers). Montrer que N_0(k) = 0 pour "presque tout k" (au sens
de la densite), puis gerer les k exceptionnels separement.

**Analyse :** Cette voie est la plus prometteuse car :
- Le deficit entropique gamma = 0.0500 est UNIVERSEL : C/d < exp(-gamma*k) pour k grand.
- Pour k >= 18 (regime cristallin), C < d, donc N_0 <= C < d.
- Le Junction Theorem [1,67] ∪ [18, ∞) couvre deja TOUS les k.
- Il ne reste que les convergents (d petit) ou l'argument echoue.

**Obstacle residuel :** Les convergents p_n/q_n de log_2(3) forment un ensemble
DISCRET et CREUX. On ne peut pas appliquer un argument de densite a un ensemble
de densite zero. Les convergents sont precisement les k "exceptionnels" que
l'argument de Tao ne couvre pas.

### 4.2. Voie 2 : Bornes de sommes exponentielles conditionnelles

**Idee :** Appliquer les techniques de sommes exponentielles de Tao
(decorrelation, completion, stationary phase) a la somme :

  T(t) = sum_{A in Comp(S,k)} e(t * corrSum(A) / p)

pour les premiers p | d.

**Analyse :** La difficulte est la CONTRAINTE DE MONOTONIE. La somme T(t)
n'est pas une somme multiplicative ni une somme le long d'une courbe algebrique.
C'est une somme sur des combinaisons {k-1 parmi S-1}, avec une fonction
corrSum qui est un polynome de Horner lacunaire.

Les bornes de Weil (pour les sommes sur les varietes algebriques) ne s'appliquent
pas directement. Les bornes de type Weyl (pour les sommes trigonometriques)
requieraient que corrSum soit un polynome en une variable, ce qui n'est pas le cas.

**Observation (Piste A) :** max|T(t)|/sqrt(C) DIVERGE avec k pour les grands
premiers, confirmant l'absence d'annulation en racine carree. Les techniques
standard de sommes exponentielles sont donc INSUFFISANTES pour le cadre Horner.

### 4.3. Voie 3 : Argument probabiliste sur d(k)

**Idee :** Exploiter le fait que d(k) = 2^S - 3^k croît exponentiellement
(sauf pour les convergents) et que ses facteurs premiers "typiques" sont
grands. Pour un premier p | d typique, C/p << 1, donc N_0 = 0 par le
modele Poisson (Piste C).

**Analyse :** C'est essentiellement l'argument du regime cristallin deja
presente dans le preprint. Pour k >= 18 (et k different d'un convergent),
il existe un premier p | d avec p > C, et le modele Poisson predit
P(N_0 ≥ 1) << C/p << 1.

**Obstacle :** Ce n'est pas une PREUVE car le modele Poisson est heuristique.
Le transformer en preuve requiert exactement les bornes de sommes
exponentielles de la Voie 2, qui ne sont pas disponibles.

### 4.4. Voie 4 : Approche par la theorie ergodique

**Idee :** La mesure de Haar mu sur Z_2 (entiers 2-adiques) est invariante
par la dynamique de Collatz. Tao exploite cette ergodicite. Peut-on
conditionner sur l'evenement "corrSum = 0 mod d" et montrer que cet
evenement a mu-mesure zero ?

**Analyse :** L'evenement "corrSum = 0 mod d" est un evenement
CYLINDRIQUE dans Z_2 (il ne depend que de k chiffres de la decomposition
2-adique). Sa mu-mesure est exactement N_0(d) / 2^S, ou N_0(d) est le
nombre de compositions avec corrSum = 0 mod d.

Montrer que cette mu-mesure est 0 revient exactement a prouver N_0(d) = 0,
i.e. l'Hypothese H. L'approche ergodique REFORMULE le probleme mais ne le
simplifie pas.

---

## 5. Analyse des convergents : le noyau dur

### 5.1. Le probleme des convergents

Les convergents q_n de log_2(3) (q_1=1, q_2=2, q_3=5, q_4=12, q_5=41,
q_6=53, q_7=306, ...) sont les k ou d(k) est "anormalement petit" :

  d(q_n) ~ 3^{q_n} * ||q_n * log_2(3)||

ou ||x|| = min(x - floor(x), ceil(x) - x) est la distance a l'entier
le plus proche.

Pour ces k, d est du meme ordre que C (ou meme plus petit), ce qui signifie
que TOUS les premiers p | d satisfont C/p >= 1. Le modele Poisson predit
N_0 ~ C/p >= 1, et l'exclusion N_0 = 0 est donc IMPROBABLE dans le modele
aleatoire.

### 5.2. Resultats des Pistes A-C sur les convergents

| k (convergent) | d | C | C/d | Piste A | Piste B | Piste C |
|----------------|---|---|-----|---------|---------|---------|
| q_3 = 5 | 13 | 35 | 2.69 | N_0=0 (p=13) ✓ | Excl. chirurgicale ✓ | P(Poisson)=7% |
| q_4 = 12 | 517135 | 75582 | 0.15 | N_0(1753)=150 ✗ | Type II p=1753 | P=86% |
| q_5 = 41 | (grand) | (grand) | <<1 | Non calcule | Non calcule | Attendu |

**Observation :** q_3 est le SEUL convergent exclu par les Pistes A-C.
Les convergents q_4 et au-dela resistent a toutes les approches.

### 5.3. Pourquoi Tao ne resout pas les convergents

Pour un convergent q_n :
1. d(q_n) est petit → pas de "grand premier" p | d pour l'argument cristallin.
2. C(S-1, k-1) ~ d → le regime cristallin (C << d) ne s'applique pas.
3. Le resultat "presque tout" de Tao porte sur les n, pas sur les k.
   Les convergents q_n forment un ensemble de densite zero parmi les entiers,
   donc meme un argument "presque tout k" les laisserait non resolus.

**Analogie :** Les convergents sont les "nombres premiers" du probleme de Collatz.
Comme les premiers resistent aux arguments de densite (il faut la theorie
analytique des nombres pour les etudier individuellement), les convergents
resistent aux arguments en mesure.

---

## 6. Synthese : ce que Tao apporte et ce qu'il manque

### 6.1. Contributions de l'approche Tao

1. **Outil technique** : les sommes exponentielles sur Z_2 avec decorrelation
   polynomiale sont l'outil le plus puissant disponible.

2. **Philosophie** : l'idee que "presque toutes" les orbites sont bornees
   est coherente avec l'inexistence de cycles — mais ne la prouve pas.

3. **Paradigme** : la preuve de Tao montre qu'il FAUT travailler en mesure
   sur un espace de type 2-adique, pas element par element.

4. **Inspiration** : la structure de la preuve (passage Z → Z_2 → bornes
   de Fourier → retour a Z via CRT) est exactement le schema du Programme Merle.

### 6.2. Le gap irreductible

Le gap entre Tao et l'Hypothese H est FONDAMENTAL :

- Tao prouve un resultat EN MESURE (pour presque tout n).
- L'Hypothese H requiert un resultat UNIVERSEL (pour tout k).

Ce gap est celui entre "les entiers typiques n'ont pas de grands iterates de
Collatz" et "il n'existe aucun cycle de longueur k pour aucun k". Le premier
est un theoreme (Tao 2022), le second est la conjecture de Collatz pour les
cycles positifs.

La Piste D montre que les outils de Tao sont NECESSAIRES (sommes exponentielles,
analyse 2-adique) mais INSUFFISANTS (precision, conditionnement, convergents).
Le passage de "presque tout" a "tout" est le coeur du probleme.

---

## 7. Verdict

### 7.1. Forces

1. **Cadre theorique le plus avance** : Tao (2022) est le resultat inconditionnellement
   le plus fort sur la conjecture de Collatz
2. **Outils puissants** : sommes exponentielles, analyse 2-adique, ergodicite
3. **Inspiration directe** pour le Programme Merle (schema de preuve similaire)
4. **Identifie clairement le gap** : mesure vs universalite

### 7.2. Limites

1. **Non adaptable directement** : les trois obstacles (conditionnement, module,
   precision) sont fondamentaux, pas techniques
2. **Les convergents resistent** : l'ensemble de densite zero q_n echappe a tout
   argument "presque tout"
3. **Precision insuffisante** : O(k^{-A}) ne suffit pas pour prouver N_0 = 0
4. **Module different** : mod 3^k (Tao) vs mod d (Hypothese H)
5. **Aucun nouveau calcul possible** : la Piste D est purement theorique

### 7.3. Grille d'evaluation

| Critere | Score | Commentaire |
|---------|-------|-------------|
| Faisabilite computationnelle | 2/10 | Pas de calcul direct possible |
| Faisabilite theorique | 3/10 | Gap fondamental mesure vs universalite |
| Conditionnalite | N/A | La piste evalue une extension, pas un resultat |
| Force du resultat | 2/10 | "Presque tout" ne prouve pas "tout" |
| Calculabilite | 3/10 | Analyse theorique, pas algorithmique |
| Chemin vers Lean | 4/10 | Sommes exponentielles formalisables |
| Connexion existante | 7/10 | Programme Merle, Phase 16 (Parseval) |

### 7.4. Conclusion

**PISTE D = INSPIRATION PUISSANTE MAIS GAP FONDAMENTAL NON COMBLE**

Le resultat de Tao (2022) est le phare qui eclaire le chemin, mais il ne
mene pas jusqu'a la destination. Le gap entre "presque tout" et "tout" est
le meme gap que celui entre "quasi-uniforme" (Piste C) et "zero exclu"
(Hypothese H).

Les quatre pistes convergent vers le meme diagnostic : **l'Hypothese H requiert
une borne de sommes exponentielles pour les polynomes de Horner lacunaires
sous contrainte de monotonie.** C'est un probleme ouvert en theorie
analytique des nombres, et sa resolution constituerait le "Graal" du
Programme Merle.

**Questions ouvertes identifiees par la Piste D :**
1. Peut-on adapter la decorrelation 2-adique de Tao au module d = 2^S - 3^k ?
2. Les convergents admettent-ils un traitement special (approche diophantienne) ?
3. Existe-t-il un analogue du theoreme de Weil pour les sommes de Horner lacunaires ?

---

## 8. Fichiers produits

- `research_log/phase20d_piste_extension_tao.md` (ce document)
- Pas de script computationnel (piste purement theorique)

---
