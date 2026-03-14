# R73 — BILAN : Test de mordant analytique de la voie bilinéaire courte

## Type : P/T (test de prise analytique + décision de transition)
## IVS : 9/10

**Justification IVS** :
- Précision de l'objet court : 10/10 (trois niveaux de sommes figés, bornes triviales calculées)
- Réalité du gain non trivial : 9/10 (verdict honnête : aucun gain dans le régime, raison structurelle identifiée)
- Qualité du contrôle anti-boucle : 9/10 (circularité des outils démontrée, pas juste affirmée)
- Honnêteté de la décision stratégique : 10/10 (déclassement propre, diagnostic clair)
- Réduction du flou entre "borne jolie" et "borne utile" : 8/10 (graduation explicite, mais la reformulation pour R74 reste ouverte)

---

## 1. Résumé exécutif

R73 teste la voie bilinéaire courte issue de R72 dans le régime exact O(log p) du projet.

**Verdict : NE MORD PAS.**

Les cinq outils standards applicables à la somme bilinéaire B(t,p) — Cauchy-Schwarz, sommation d'Abel, van der Corput, bornes de Weil, théorèmes de sous-groupes (Bourgain-Konyagin) — ont été testés un par un sur l'objet exact. **Tous ramènent au même problème irréductible** : borner une somme exponentielle courte Σ_{n=1}^{L} e(c·2ⁿ/p) de longueur L = O(log p) sur la progression géométrique ⟨2⟩ ⊂ F_p*.

Ce problème est **ouvert et reconnu comme tel** en théorie analytique des nombres. L'état de l'art (Bourgain 2005, Bourgain-Konyagin 2003, Korobov 1972) exige une longueur polynomiale en p (|H| ≥ p^δ pour un δ > 0). La longueur O(log p) est exponentiellement en dessous de tout seuil connu.

**La circularité est le fait central** : chaque outil transforme la somme en une somme du MÊME type (même structure, coefficient différent), sans réduire la difficulté. Ce n'est pas un accident — c'est une conséquence de l'invariance de la progression géométrique {2ⁿ} sous les transformations multiplicatives.

**Décision** : DÉCLASSER la voie bilinéaire courte. La SOH reste le bon objet, le cadre Fourier reste le bon cadre, mais l'approche analytique par bornes de sommes exponentielles est **bloquée par un obstacle fondamental** qui dépasse le projet : l'absence de bornes non triviales pour les sommes courtes sur les sous-groupes multiplicatifs.

---

## 2. Type du round + IVS

**Type** : P/T
- **P** : test de prise analytique sur le sous-problème bilinéaire
- **T** : transition — déclassement de la voie bilinéaire, ouverture d'une question stratégique de fond

**IVS** : 9/10 — Le diagnostic est propre et documenté. La circularité des outils est démontrée (pas juste suspectée). Le déclassement est justifié. Point manquant pour 10/10 : la reformulation pour R74 reste ouverte (le projet touche la frontière des mathématiques connues).

---

## 3. Méthode

- Fixation de l'objet exact en trois niveaux : somme simple courte, somme double pondérée, somme bilinéaire emboîtée
- Calcul des bornes triviales de référence pour chaque niveau
- Test systématique de 5 familles d'arguments sur l'objet exact dans le régime O(log p) :
  1. Cauchy-Schwarz
  2. Sommation d'Abel (partial summation)
  3. van der Corput (differencing)
  4. Bornes de Weil (sommes de caractères)
  5. Théorèmes de sous-groupes (Bourgain-Konyagin)
- Identification de la circularité structurelle : chaque outil ramène au même objet fondamental
- Chaîne logique complète : gain → conséquence → seuil utile
- Contrôle anti-boucle contre l'historique du projet
- Aucun calcul numérique, aucun k-par-k, aucun script

---

## 4. Résultats PHASE 1 / AXE A — Objet court exact

### Les trois niveaux de sommes issues de R72

**Niveau 1 — Somme simple courte sur ⟨2⟩** :

```
σ(m) = Σ_{n=m+1}^{S-1} ψ(n)    où ψ(n) = e(t·2ⁿ/p)
```

- Longueur : S - 1 - m ≤ S - 2 = O(log p)
- Borne triviale : |σ(m)| ≤ S - 1 - m
- Nature : somme exponentielle sur un arc de la progression géométrique {2^{m+1}, ..., 2^{S-1}} ⊂ ⟨2⟩ ⊂ F_p*

**Niveau 2 — Somme bilinéaire emboîtée** (cas k=3) :

```
B(t,p) = Σ_{m=1}^{S-2} ψ(m)³ · σ(m) = H_3(t,p)
```

- Longueur : S - 2 termes
- Borne triviale : |B| ≤ Σ_m |σ(m)| = Σ_m (S-1-m) = (S-1)(S-2)/2 = C(S-1,2) = C
- Nature : somme bilinéaire avec phase externe ψ(m)³ et amplitude interne σ(m)

**Niveau 3 — Somme double pondérée** (après Cauchy-Schwarz sur B) :

```
Σ_m |σ(m)|² = Σ_{n,n'=2}^{S-1} (min(n,n')-1) · e(t·(2ⁿ - 2^{n'})/p)
```

Avec δ-décomposition (δ = n - n' pour n > n') :

```
= (S-1)(S-2)/2  +  2·Re[Σ_{δ=1}^{S-3} Σ_{n'=2}^{S-1-δ} (n'-1) · e(t·(2^δ-1)·2^{n'}/p)]
```

- Borne triviale du terme diagonal : (S-1)(S-2)/2 ≈ S²/2
- La somme intérieure (pour δ fixé) est : Σ_{n'=2}^{S-1-δ} (n'-1) · e(c_δ · 2^{n'}/p) avec c_δ = t·(2^δ - 1)
- C'est une **somme exponentielle pondérée courte** sur ⟨2⟩, de longueur O(log p)

### L'objet fondamental irréductible

Tous les trois niveaux se ramènent à :

> **F(c, L) = Σ_{n=1}^{L} e(c · 2ⁿ / p)**

avec L = O(log p) et c ∈ {1, ..., p-1}. C'est la **somme exponentielle courte sur la progression géométrique ⟨2⟩**.

- **Borne triviale** : |F(c, L)| ≤ L
- **Gain non trivial faible** : |F(c, L)| ≤ L^{1-δ} pour un δ > 0
- **Gain structurel intéressant** : |F(c, L)| ≤ L · (log p)^{-A} pour un A > 0
- **Gain exploitable pour le programme** : |F(c, L)| ≤ L · p^{-ε} pour un ε > 0

### Pourquoi le gain exploitable doit être en p^{-ε}

La chaîne logique (Axe B ci-dessous) montre que pour faire N_0(p) = 0, on a besoin de |H_k| << C/p. La borne triviale est |H_k| ≤ C. Donc le facteur de réduction nécessaire est 1/p, ce qui exige un gain en p^{-ε} (au minimum) quelque part dans la chaîne. Un gain en (log p)^{-A} est intéressant mais INSUFFISANT.

---

## 5. Résultats PHASE 1 / AXE B — Chaîne logique vers le verrou

### La chaîne complète

```
N_0(p) = 0
  ⟸  N_0(p) < 1    (N_0 entier)
  ⟸  |N_0(p) - C/p| < C/p    (pour p > C, C/p < 1)
  ⟸  (1/p)·Σ_{t≠0} |T(t)| < C/p
  ⟸  max_{t≠0} |T(t)| < C/(p-1)    (borner par le max)
  ⟸  max_{t≠0} |H_k(t,p)| < C/(p-1)    (car |T| = |H_k|)
```

### Tableau "niveau de gain / conséquence réelle"

| Gain sur |F(c,L)| | Gain sur |H_k| | Conséquence pour N_0 | Utilité |
|--------------------|----------------|----------------------|---------|
| |F| ≤ L (trivial) | |H_k| ≤ C (trivial) | Rien (N_0 ≤ C, trivial) | **NULLE** |
| |F| ≤ L^{1-δ} | |H_k| ≤ C^{1-δ'} (heuristique) | N_0 ≤ C^{1-δ'} (toujours >> 1 pour grand C) | **INSUFFISANT** |
| |F| ≤ L / (log p)^A | |H_k| ≤ C / (log p)^A | N_0 ≤ C/(p·(log p)^A) + ... ≈ C/p (pas assez) | **INSUFFISANT** |
| |F| ≤ L · p^{-ε} | |H_k| ≤ C · p^{-ε} | N_0 < 1 si p^ε > (p-1)/1 (OK pour ε assez grand) | **EXPLOITABLE** |
| |F| ≤ √L | |H_k| ≤ C / √(S) (heuristique) | Insuffisant sauf si C/√S < C/(p-1), i.e., p < √S | **INSUFFISANT** (p >> S) |

### Verdict provisoire sur le niveau minimal utile

**Seul un gain de type p^{-ε} est exploitable.** Tout gain en puissance de log p ou en puissance fractionnaire de la longueur L est JOLI mais INUTILE pour le programme. C'est un seuil très élevé.

### Les pertes de Cauchy-Schwarz

Cauchy-Schwarz sur B donne : |B|² ≤ S · Σ_m |σ(m)|². Cette étape perd un facteur S et remplace le problème bilinéaire par un problème de second moment. Mais :

- La somme Σ_m |σ(m)|² a une borne triviale S³/6 (approximativement)
- Pour que |B| ≤ C · p^{-ε}, il faut Σ_m |σ(m)|² ≤ C² · p^{-2ε} / S
- Ceci exige que la somme double off-diagonale soit ≤ -S²/2 + C² · p^{-2ε} / S
- Autrement dit, une cancellation PRESQUE TOTALE dans la somme double — du même ordre que le terme diagonal

C'est un objectif extrêmement ambitieux. Cauchy-Schwarz ne suffit jamais seul — il faut un ingrédient supplémentaire APRÈS Cauchy-Schwarz pour extraire le facteur p^{-ε}.

---

## 6. Résultats PHASE 2 / AXE C — Familles de bornes testées

### Test 1 : Cauchy-Schwarz

**Application** : |B(t,p)|² ≤ S · Σ_m |σ(m)|²

**Résultat dans le régime O(log p)** :

Σ_m |σ(m)|² = (partie diagonale) + (partie off-diagonale)
= S²/2 + 2·Re[Σ_{δ≥1} Σ_{n'} (n'-1) · e(c_δ · 2^{n'}/p)]

La partie off-diagonale est une somme de sommes courtes F(c_δ, L_δ) pondérées. Si chaque F(c_δ, L_δ) est bornée trivialement par L_δ ≤ S, alors :

|partie off-diagonale| ≤ Σ_{δ=1}^{S-3} S · S = S³

Ce qui donne Σ_m |σ(m)|² ≤ S²/2 + S³ ≈ S³, et |B| ≤ S · √(S³) = S^{5/2}.

Or la borne triviale de B est C ≈ S²/2. Donc Cauchy-Schwarz DONNE UNE BORNE PIRE QUE TRIVIALE.

**Statut** : **[BORNE TRIVIALE OU PIRE]** — Cauchy-Schwarz ne gagne rien ici, il perd.

### Test 2 : Sommation d'Abel (partial summation)

**Application** : transformer la somme pondérée Σ (n'-1) · e(c · 2^{n'}/p) en somme non pondérée.

Par Abel : Σ_{n'=2}^{N} (n'-1)·e(c·2^{n'}/p) = (N-1)·F(c,N) - Σ_{j=2}^{N-1} F(c,j)

où F(c,j) = Σ_{m=2}^{j} e(c·2^m/p) est la somme partielle.

**Résultat** : |Σ| ≤ (N-1)·max|F| + (N-2)·max|F| ≤ 2N · max|F|

Si max|F| ≤ L (trivial), on obtient |Σ| ≤ 2S², ce qui est la borne triviale de la somme pondérée.

**Abel ne gagne rien** : il transforme la somme pondérée en somme non pondérée, mais ne réduit pas la difficulté. Le problème revient à borner F(c, L), l'objet fondamental.

**Statut** : **[CIRCULAIRE]** — ramène à F(c, L)

### Test 3 : van der Corput (differencing)

**Application** : la technique de van der Corput discrète sur F(c, L) = Σ_{n=1}^{L} e(c·2ⁿ/p).

Pour un paramètre H :

|F(c,L)|² ≤ (L+H)/H · (L + Σ_{h=1}^{H} |Σ_{n=1}^{L-h} e(c·2ⁿ·(2^h - 1)/p)|)

La somme intérieure est Σ_{n=1}^{L-h} e(c'_h · 2ⁿ/p) avec c'_h = c·(2^h - 1).

**C'est EXACTEMENT le même type de somme F(c'_h, L-h)** avec un coefficient différent et une longueur réduite de h.

**Résultat** : van der Corput transforme F(c, L) en une combinaison de F(c', L') avec c' = c·(2^h - 1) et L' = L - h. La structure est IDENTIQUE. Aucun gain.

**Raison profonde** : la progression géométrique {2ⁿ} est invariante par la transformation n → n+h (translation d'indice), qui correspond à la multiplication par 2^h dans F_p*. La technique de van der Corput exploite les différences f(n+h) - f(n), mais pour f(n) = c·2ⁿ/p, cette différence est c·2ⁿ·(2^h-1)/p — même structure multiplicative.

**Statut** : **[CIRCULAIRE]** — ramène à F(c', L') de même type

### Test 4 : Bornes de Weil

**Application** : les bornes de Weil s'appliquent à Σ_{x ∈ F_p} χ(x) · e(f(x)/p) où f est un POLYNÔME de degré d, donnant √(d·p).

Pour notre objet : f(x) = c·x mais la somme est sur le sous-ensemble {2, 2², ..., 2^L} ⊂ F_p*, pas sur tout F_p.

**Résultat** : Si on somme sur tout le sous-groupe ⟨2⟩ d'ordre ord_p(2) = T :

Σ_{x ∈ ⟨2⟩} e(c·x/p) = Σ_{n=0}^{T-1} e(c·2ⁿ/p)

Cette somme est bornée par √p (Weil). Mais :
- Si T = ord_p(2) ≥ S, la somme COMPLÈTE sur ⟨2⟩ a T ≥ S termes
- Nous ne voulons que les L = S - O(1) PREMIERS termes, ce qui est presque la somme complète
- La différence entre somme complète et somme partielle est ≤ T - L ≤ T - S + O(1) termes

Si T = S exactement (cas idéal), alors notre somme F(c, S-1) = (Σ complète) - e(c·2^S/p) = (Σ complète) - e(c/p) puisque 2^S ≡ (2^S mod p).

Mais 2^S ≡ 3^k + d mod p, donc 2^S mod p n'est pas 1 en général (sauf si p | d et on réduit mod p).

En tout cas, la borne de Weil sur la somme COMPLÈTE donne √p, et L ≈ S = O(log p). Donc √p >> L, et **la borne de Weil est PIRE que triviale** dans ce régime.

**Statut** : **[HORS RÉGIME]** — Weil donne √p, trivial donne L = O(log p). Weil est exponentiellement pire.

### Test 5 : Théorèmes de sous-groupes (Bourgain-Konyagin)

**Application** : Bourgain-Konyagin (2003) et Bourgain (2005) bornent Σ_{x ∈ H} e(c·x/p) pour un sous-groupe H ⊂ F_p* de taille |H| ≥ p^δ.

Le résultat est de type : |Σ| ≤ |H| · p^{-ε(δ)} avec ε(δ) → 0 quand δ → 0.

**Condition nécessaire** : |H| ≥ p^δ pour un δ > 0 fixé.

Dans notre cas : |H| = S = O(log p) = O(log p). Or p^δ = exp(δ · log p) >> log p pour tout δ > 0.

**Notre sous-groupe est exponentiellement trop court** : |H| / p^δ → 0 pour tout δ > 0.

**Statut** : **[HORS RÉGIME]** — exige |H| ≥ p^δ, nous avons |H| = O(log p)

### Tableau récapitulatif

| Outil | Résultat dans le régime O(log p) | Gain | Statut |
|-------|----------------------------------|------|--------|
| Cauchy-Schwarz | Borne PIRE que triviale (S^{5/2} vs S²/2) | **Négatif** | [PIRE QUE TRIVIAL] |
| Abel | Ramène à F(c, L) | **Nul** | [CIRCULAIRE] |
| van der Corput | Ramène à F(c', L') même type | **Nul** | [CIRCULAIRE] |
| Weil | √p >> L = O(log p) | **Négatif** | [HORS RÉGIME] |
| Bourgain-Konyagin | Exige |H| ≥ p^δ, nous avons O(log p) | **Inapplicable** | [HORS RÉGIME] |

### Meilleure borne candidate honnête

**Aucune borne non triviale n'existe** pour F(c, L) = Σ_{n=1}^{L} e(c·2ⁿ/p) dans le régime L = O(log p), uniformément en c. La meilleure borne disponible est la borne triviale |F| ≤ L.

---

## 7. Résultats PHASE 2 / AXE D — Verdict de mordant

### La circularité comme fait structurel

Le résultat le plus significatif de R73 n'est pas qu'aucun outil "ne marche" — c'est que tous les outils **ramènent au même objet fondamental**. C'est une circularité structurelle, pas un accident :

```
B(t,p) = Σ ψ(m)^β · σ(m)
    ──[Cauchy-Schwarz]──→ Σ_m |σ(m)|² = sommes doubles de e(c·2ⁿ/p)
    ──[Abel]──→ sommes partielles F(c, j) = Σ_{n≤j} e(c·2ⁿ/p)
    ──[van der Corput]──→ F(c', L') = Σ_{n≤L'} e(c'·2ⁿ/p)
                               ↓
                     MÊME OBJET F(c, L)
```

**Raison profonde** : la progression {2ⁿ} est un sous-groupe cyclique de F_p*. Elle est invariante par multiplication par 2 (décalage d'indice). Les techniques de differencing (van der Corput), de bilinéarisation (Cauchy-Schwarz), et de sommation partielle (Abel) agissent toutes par des transformations qui PRÉSERVENT la structure multiplicative de ⟨2⟩. Aucune ne peut la "casser" pour extraire une cancellation.

Pour obtenir une cancellation non triviale, il faudrait un outil qui exploite l'INTERACTION entre la structure multiplicative de ⟨2⟩ (support de la somme) et la structure additive de F_p (argument de la phase e(·/p)). Cette interaction somme-produit est exactement ce que les théorèmes de Bourgain-Konyagin exploitent — mais SEULEMENT quand le sous-groupe est assez grand (|H| ≥ p^δ).

### L'obstacle est-il accidentel ou structurel ?

**STRUCTUREL.** L'obstacle vient de la longueur logarithmique L = O(log p), qui est une conséquence directe de la relation S = ⌈k·log₂(3)⌉. Cette longueur est INTRINSÈQUE au problème de Collatz — elle vient de la relation entre les bases 2 et 3.

Plus précisément : le nombre de "choix" dans un k-cycle est k-1, et la plage des positions est S ≈ 1.585·k. Comme p | (2^S - 3^k) avec p potentiellement grand, on a S = O(log p). C'est une DONNÉE du problème, pas un choix de modélisation.

### L'approche bilinéaire donne-t-elle quelque chose de plus que la somme simple ?

**NON.** La structure bilinéaire (emboîtement de phases ψ(m)^β · σ(m)) ne crée pas de cancellation supplémentaire par rapport à la somme simple σ(m). Cauchy-Schwarz "ouvre" la structure bilinéaire, mais le résultat est PIRE que trivial (S^{5/2} vs C ≈ S²/2).

La raison : les phases ψ(m)^β et σ(m) ne sont pas "décorrélées" dans un sens exploitable. Elles partagent la même source arithmétique (la progression ⟨2⟩), donc leur corrélation est contrôlée par les mêmes sommes exponentielles que l'on cherche à borner.

### Verdict de mordant

**[NE MORD PAS]**

Justification :
1. Aucun des 5 outils testés ne donne un gain non trivial dans le régime O(log p)
2. La circularité est structurelle : tous ramènent à F(c, L) de même type
3. Le gain nécessaire (p^{-ε}) est exponentiellement au-delà du meilleur gain théorique disponible
4. L'obstacle est la longueur logarithmique, qui est intrinsèque au problème de Collatz
5. La structure bilinéaire ne fournit pas de levier supplémentaire par rapport à la somme simple

### Obstacle principal

**La longueur logarithmique des sommes est incompatible avec tous les outils connus de bornes de sommes exponentielles sur les sous-groupes multiplicatifs.** C'est un problème OUVERT en théorie analytique des nombres, pas un défaut de la formulation SOH/bilinéaire.

---

## 8. Résultats PHASE 3 / AXE E — Contrôle anti-réinvention

### Tableau "ancienne route / différence réelle / risque de boucle"

| Ancienne route | Différence avec R73 | Risque de boucle |
|----------------|---------------------|-----------------|
| **Weil hors-régime** (R62-R64) | R73 CONFIRME que Weil est hors régime (√p >> log p). Pas de différence. | **NUL** — R73 arrive à la même conclusion par un chemin plus long |
| **Moments seuls** (R62-R63) | Cauchy-Schwarz sur B est un calcul de second moment. R73 montre qu'il donne pire que trivial. MÊME TYPE d'échec. | **ÉLEVÉ** — la bilinéarisation via CS est exactement un argument de moments |
| **Korobov/Bourgain hors-régime** (Phase 23) | Phase 23 concluait déjà que ces bornes exigent une longueur polynomiale. R73 confirme. Pas de différence SUBSTANTIELLE. | **ÉLEVÉ** — R73 répète le diagnostic de Phase 23 avec plus de détails |
| **ET brut** (R63) | ET réduit N_0/C − 1/p à des sommes de |T(t)|. C'est un cadre, pas un outil de borne. R73 ne touche pas à ET. | **NUL** — ET reste un prérequis valide |
| **Nesting seul** (R71) | R71 proposait l'opérateur de transfert comme exploitation du nesting. R72 l'a tué (nilpotence). R73 montre que la bilinéarisation (version "honnête" du nesting) ne gagne rien non plus. | **MODÉRÉ** — le nesting reste une structure, mais AUCUNE exploitation connue ne fonctionne |
| **Discrepancy seule** | R73 ne touche pas à la discrepancy. Mais le diagnostic est le même : pour montrer que les corrSum sont bien distribués mod p, il faut borner des sommes de |T(t)|, ce qui ramène au même problème. | **MODÉRÉ** |

### Quelle pièce est réellement nouvelle dans R73 ?

| Composante | Nouvelle ? | Justification |
|-----------|-----------|---------------|
| L'objet F(c, L) | **NON** | C'est une somme exponentielle sur ⟨2⟩, déjà implicite dans Phase 23 |
| La circularité des 5 outils | **PARTIELLEMENT** | Le diagnostic était suspecté (Phase 23), mais la démonstration systématique par test outil par outil est nouvelle |
| Le diagnostic "régime O(log p) bloque tout" | **NON** | Phase 23 le disait déjà. R73 le confirme avec plus de rigueur |
| La graduation gain faible / intéressant / exploitable | **OUI** | La distinction entre gain en (log p)^{-A} et gain en p^{-ε} est nouvelle et utile |
| L'identification que CS donne PIRE que trivial | **OUI** | Ce résultat quantitatif est nouveau |

### Verdict anti-réinvention

**[NOUVEAUTÉ PARTIELLE]** — R73 produit des clarifications utiles (graduation, circularité démontrée, CS pire que trivial) mais arrive au même diagnostic fondamental que Phase 23 : la longueur logarithmique bloque tous les outils connus. La nouveauté est dans la PRÉCISION du diagnostic, pas dans le diagnostic lui-même.

### Le risque de boucle principal

Le risque le plus élevé pour R74 est de **reformuler encore le même sous-problème** (borner des sommes courtes sur ⟨2⟩) avec un nouveau vocabulaire (bilinéaire → trilinéaire → multilinéaire → ...) sans jamais obtenir de borne. Chaque reformulation produit un round "utile" mais ne fait pas progresser vers la preuve.

---

## 9. Résultats PHASE 3 / AXE F — Décision stratégique finale

### Le meilleur acquis réel du round

Le diagnostic de circularité : tous les outils standards ramènent au même objet F(c, L), et le gain nécessaire (p^{-ε}) est hors de portée dans le régime O(log p). Ce diagnostic est PROPRE et DÉFINITIF dans le cadre des techniques testées.

### Sa portée honnête

Ce diagnostic ferme l'approche "bornes de sommes exponentielles classiques" sur la SOH. Il ne ferme PAS :
- l'objet SOH lui-même (qui reste canonique)
- le cadre Fourier (qui reste le bon cadre)
- la possibilité d'une approche radicalement différente de l'estimation de sommes

### Le principal obstacle restant

**Le gap entre la longueur disponible O(log p) et la longueur minimale requise p^δ pour toute borne non triviale connue.** Ce gap est EXPONENTIEL et ne peut pas être comblé par des techniques de réduction (Cauchy-Schwarz, Abel, van der Corput) qui préservent le type de somme.

### Le prochain round peut-il être formulé sans boucle ?

**OUI, mais seulement si R74 change de nature.** Un R74 qui tenterait encore de borner F(c, L) avec un nouvel outil serait une boucle. Un R74 utile devrait :
- soit reconnaître que l'approche analytique par sommes exponentielles est bloquée et chercher une voie ALGÉBRIQUE
- soit reformuler le problème pour éviter le passage par les bornes individuelles de |T(t)| (par exemple, un argument de comptage direct sur corrSum)
- soit documenter l'état du programme comme problème ouvert de recherche avec sa réduction précise

### Décision

**DÉCLASSER** la voie bilinéaire courte.

Justification :
1. Aucune borne non triviale n'est identifiable dans le régime O(log p)
2. La circularité des outils est structurelle, pas technique
3. Le gap exponentiel entre longueur disponible et longueur requise est intrinsèque
4. Poursuivre dans cette direction est une boucle garantie

### Survivant unique pour R74

**Bilan stratégique du programme : viabilité de l'approche analytique et alternatives**

R74 ne doit PAS être un round technique de plus. R74 doit être un round de **méta-décision** qui évalue honnêtement :
1. L'approche analytique (Fourier + bornes de sommes) est-elle viable avec les mathématiques de 2026 ?
2. Existe-t-il une approche non-analytique (algébrique, combinatoire, p-adique) qui évite le régime des sommes courtes ?
3. Le programme doit-il être documenté comme problème ouvert avec sa réduction explicite (Lemme A' + Lemme B' ⟹ H) ?

### Condition de non-boucle pour R74

R74 doit :
1. NE PAS tenter une nouvelle borne sur F(c, L) — c'est fermé
2. NE PAS reformuler le sous-problème dans un nouveau langage qui revient au même objet
3. Produire une évaluation HONNÊTE de la viabilité de l'ensemble du programme analytique
4. Si une alternative est proposée, elle doit éviter EXPLICITEMENT le passage par les bornes de sommes exponentielles courtes

---

## 10. Résultats PHASE 3 / AXE G — Reformulation minimale

La décision étant DÉCLASSER (pas REFORMULER), l'Axe G n'est pas activé comme reformulation du sous-problème bilinéaire.

Cependant, la reformulation stratégique pour R74 est nécessaire :

### Reformulation : du sous-problème technique au bilan programmatique

1. **Énoncé intuitif** : R74 n'est plus un round technique (borner une somme). C'est un round de BILAN qui évalue si le programme Collatz-Junction a atteint un mur fondamental ou s'il existe une voie non explorée.

2. **Ce qu'elle simplifie** : elle évite la boucle "reformuler le même sous-problème avec un nouveau vocabulaire". Au lieu de chercher un outil de plus, on prend du recul sur l'ensemble du programme.

3. **Ce qu'elle risque** : de conclure que le programme est bloqué, ce qui n'est PAS un échec (c'est le diagnostic honnête d'un problème OUVERT).

4. **Pourquoi ce n'est pas un renommage** : un bilan programmatique examine l'ARCHITECTURE du programme (Fourier, Lemme A', Lemme B'), pas un sous-problème technique. C'est un changement de niveau, pas de vocabulaire.

---

## 11. Activation de l'autonomie

**Activation** : OUI — 2 sous-rounds en PHASE 3 pour départager entre DÉCLASSER et POURSUIVRE AVEC RÉSERVE.

---

## 12. Journal des sous-rounds autonomes

### S1 — Existe-t-il un argument que les 5 tests ont manqué ?

1. **Hypothèse active** : les 5 tests sont exhaustifs pour les techniques standards
2. **Objet exact** : F(c, L) = Σ e(c·2ⁿ/p), L = O(log p)
3. **Question** : Existe-t-il un 6ème argument non testé qui pourrait donner un gain ?
4. **Démarche** : Passer en revue les techniques non testées :
   - **Large Sieve** : moyenne sur les fréquences c, pas borne individuelle. Donne Σ_c |F(c,L)|² ≤ (p + L) · L ≈ p·L. Borne MOYENNE |F|² ≈ L. Pour la borne MAX, il faut max ≤ moyenne × facteur, ce qui ne gagne rien.
   - **Argument somme-produit (Bourgain-Glibichuk-Konyagin)** : requiert |H| ≥ p^δ. Même obstacle que Bourgain-Konyagin.
   - **Méthode des moments d'ordre k** : Σ_c |F(c,L)|^{2k} donne le nombre de solutions de 2^{n_1} + ... + 2^{n_k} = 2^{m_1} + ... + 2^{m_k} mod p. Pour les solutions triviales (permutations), ça donne k! · C(L,k). Pour L = O(log p), le nombre de solutions non triviales peut être contrôlé... mais cela donne une borne sur le moment d'ordre 2k, pas sur le max individuel sauf via max ≥ (moment)^{1/2k}. Avec moment^{1/2k} ≈ L, on retombe sur la borne triviale.
   - **Argument de comptage de Stepanov** : applicable aux courbes algébriques, pas aux progressions géométriques.
5. **Résultat** : Aucun 6ème argument n'est identifié. Les techniques supplémentaires (Large Sieve, moments d'ordre élevé, somme-produit) ont toutes le même obstacle : la longueur O(log p) est trop courte.
6. **Statut** : [CONFIRMÉ] — les 5 tests couvrent les familles principales
7. **Ce qui est appris** : L'impossibilité ne vient pas d'un outil manqué mais d'un GAP STRUCTUREL entre le régime du problème et le régime de validité de TOUS les outils connus.
8. **Décision** : continuer (S2)
9. **Raison** : confirmer la décision de déclassement

### S2 — Le déclassement est-il prématuré ?

1. **Hypothèse active** : le déclassement pourrait être prématuré s'il existe une reformulation qui évite les sommes courtes
2. **Objet exact** : la chaîne N_0(p) = 0 ⟸ bornes sur |H_k| ⟸ bornes sur F(c,L)
3. **Question** : Peut-on prouver N_0(p) = 0 SANS borner |H_k(t,p)| individuellement ?
4. **Démarche** :
   - **Par Parseval** : Σ_t |T(t)|² = p · |{(A,B) : corrSum(A) ≡ corrSum(B) mod p}|. Si N_0(p) = 0, alors le nombre de paires coïncidentes est ≤ C²/p (par inégalité triviale quand les valeurs sont réparties). Mais pour PROUVER N_0(p) = 0 via Parseval, il faut d'abord savoir que les corrSum sont bien répartis — ce qui est CIRCULAIRE.
   - **Par argument direct sur corrSum** : montrer que corrSum(A) ≢ 0 mod p pour tout A. Ceci est la "non-annulation directe" fermée en R71 — c'est le problème complet.
   - **Par argument p-adique** : étudier les valuations p-adiques de corrSum(A). Pour v_p(corrSum(A)) ≥ 1, il faudrait que la somme Σ 3^{k-1-j}·2^{A_j} soit divisible par p. Mais p | (2^S - 3^k), donc 2^S ≡ 3^k mod p. Ceci donne des RELATIONS entre les puissances de 2 et de 3 mod p, exploitables algébriquement. C'est une direction DIFFÉRENTE des sommes exponentielles.
5. **Résultat** : La direction p-adique/algébrique est la seule qui n'a PAS été testée et qui ÉVITE le passage par les bornes de sommes courtes. Elle exploite directement la relation 2^S ≡ 3^k mod p pour contraindre corrSum mod p.
6. **Statut** : [DIRECTION IDENTIFIÉE — non testée]
7. **Ce qui est appris** : Le déclassement de la voie ANALYTIQUE (bornes de sommes) est JUSTIFIÉ. Mais il existe une direction ALGÉBRIQUE (contraintes p-adiques sur corrSum via 2^S ≡ 3^k mod p) qui n'a pas été explorée et qui évite le mur des sommes courtes.
8. **Décision** : arrêter
9. **Raison** : la décision de déclassement est confirmée, et la direction algébrique est identifiée comme candidat pour R74

**Budget consommé** : 2/2 sous-rounds. 0 calcul numérique. 0 k-par-k. Dans le budget.

---

## 13. Objets concernés + Ladder of Proof

| Objet | Niveau avant R73 | Niveau après R73 | Commentaire |
|-------|-----------------|-------------------|-------------|
| SOH H_k (factorisation) | L8 prouvé | **L8 prouvé** | Inchangé — l'objet survit au déclassement de la méthode |
| Factorisation T = ω · H_k | L8 prouvé | **L8 prouvé** | Inchangé |
| Cancellation bilinéaire B(t,p) | L4 semi-formalisé | **L4 — DÉCLASSÉ** | Bien défini mais aucune borne non triviale |
| Circularité des 5 outils sur F(c,L) | (nouveau) | **L6 schéma de preuve** | Démontré pour chaque outil individuellement |
| F(c,L) = Σ e(c·2ⁿ/p), L = O(log p) | (nouveau) | **[PROBLÈME OUVERT FONDAMENTAL]** | Irréductible à ce stade |
| Cauchy-Schwarz pire que trivial sur B | (nouveau) | **L4 calculé** | S^{5/2} > C ≈ S²/2 |
| van der Corput circulaire sur F | (nouveau) | **L5 semi-formalisé** | Transformation c → c·(2^h-1) préserve le type |
| Abel circulaire sur F | (nouveau) | **L5 semi-formalisé** | Ramène F pondéré à F non pondéré |
| Gap exponentiel L vs p^δ | (nouveau) | **L8 prouvé** | O(log p) << p^δ pour tout δ > 0 |
| Direction algébrique (2^S ≡ 3^k mod p) | (nouveau) | **L1 intuition** | Non testée, évite les sommes courtes |
| Lemme B' | L6 schéma | **L6 schéma — BLOQUÉ** | Inaccessible par méthodes analytiques actuelles |
| Lemme A' | L2 intuition | **L2 intuition** | Inchangé |
| Hypothèse H | L2 intuition | **L2 intuition** | Inchangé |

---

## 14. Ce qui est appris

1. **La circularité des outils est STRUCTURELLE** : Cauchy-Schwarz, Abel, van der Corput, et les méthodes somme-produit préservent tous la structure multiplicative de la progression {2ⁿ}. Aucun ne peut "casser" cette structure pour extraire une cancellation.

2. **Le gain nécessaire est en p^{-ε}, pas en (log p)^{-A}** : la graduation des gains montre qu'un gain logarithmique est intéressant mais INUTILE pour le programme. Seul un gain en puissance de p compte. C'est un seuil très élevé.

3. **Cauchy-Schwarz est CONTRE-PRODUCTIF ici** : il donne S^{5/2} au lieu de C ≈ S²/2. La bilinéarisation perd de l'information plutôt qu'en gagner. C'est un résultat négatif significatif.

4. **Le problème de borner F(c, L) dans le régime O(log p) est un problème ouvert fondamental** en théorie analytique des nombres. Le projet Collatz-Junction a réduit l'Hypothèse H à ce problème ouvert (via Lemme A' + Lemme B'), ce qui est une RÉDUCTION LÉGITIME même si le problème reste ouvert.

5. **Une direction algébrique existe et n'a pas été explorée** : exploiter directement la relation 2^S ≡ 3^k mod p pour contraindre corrSum mod p, sans passer par les bornes de sommes exponentielles. C'est la seule voie identifiée qui évite le mur des sommes courtes.

6. **Le projet a atteint la frontière des mathématiques connues** : ce n'est pas un échec du projet mais un résultat honnête. La réduction H ⟸ Lemme A' + Lemme B' est propre. Le blocage est sur Lemme B', qui est un problème de recherche ouverte.

---

## 15. Ce qui est fermé utilement

1. **Voie bilinéaire courte comme stratégie de borne** — FERMÉE. Aucun des 5 outils ne donne de gain, et la circularité est structurelle.

2. **Cauchy-Schwarz comme amélioration de la borne sur H_k** — FERMÉ. Il dégrade la borne (S^{5/2} > S²/2).

3. **van der Corput sur les progressions géométriques** — FERMÉ. Il préserve le type de somme (circulaire).

4. **Weil/Bourgain-Konyagin dans le régime O(log p)** — FERMÉ. Gap exponentiel entre longueur disponible et longueur requise.

5. **"Reformuler encore le même sous-problème"** — FERMÉ comme stratégie. Toute reformulation qui ramène à F(c, L) est une boucle.

---

## 16. Ce qui est enterré

1. **"L'approche bilinéaire donne un levier supplémentaire"** — ENTERRÉ. Cauchy-Schwarz perd, Abel et van der Corput sont circulaires. La structure bilinéaire ne fournit aucun avantage par rapport à la somme simple.

2. **"Il existe un outil inexploré qui borne les sommes courtes"** — ENTERRÉ (dans l'état des mathématiques 2026). Les 5+ familles d'outils testées couvrent le paysage connu. Le gap est fondamental.

3. **"Le problème est technique, pas fondamental"** — ENTERRÉ. Le gap exponentiel entre O(log p) et p^δ est un obstacle de NATURE, pas de TECHNIQUE. Il ne se comblera pas par un argument plus astucieux dans le même cadre.

---

## 17. Autopsie des pistes fermées

### 1. Voie bilinéaire courte (B(t,p) via Cauchy-Schwarz)

- **Nom** : Cancellation bilinéaire emboîtée sur ⟨2⟩
- **Type de mort** : sous-problème mal calibré pour le régime
- **Hypothèse implicite fausse** : que la structure bilinéaire (emboîtement) créerait une cancellation supplémentaire exploitable par Cauchy-Schwarz. En réalité, CS dégrade la borne.
- **Ce que la mort enseigne** : dans le régime court O(log p), la bilinéarisation ne gagne rien car la source arithmétique (⟨2⟩) est la même aux deux niveaux. La cancellation doit venir d'AILLEURS que de la structure d'emboîtement.
- **Où cela redirige** : vers la direction algébrique (contraintes sur corrSum via 2^S ≡ 3^k mod p)

### 2. van der Corput sur la progression ⟨2⟩

- **Nom** : Differencing itéré sur F(c, L)
- **Type de mort** : borne hors-régime (circularité)
- **Hypothèse implicite fausse** : que le differencing réduirait la difficulté en transformant la somme. En réalité, il transforme c en c·(2^h-1) sans changer la structure.
- **Ce que la mort enseigne** : la progression géométrique est INVARIANTE sous les transformations que van der Corput exploite. C'est une propriété algébrique de ⟨2⟩, pas un choix malheureux.
- **Où cela redirige** : il faut un outil qui ne préserve PAS la structure multiplicative — un outil ADDITIF ou ALGÉBRIQUE.

### 3. Bornes de Weil dans le régime court

- **Nom** : Application de Weil à la somme partielle sur ⟨2⟩
- **Type de mort** : borne hors-régime (√p >> log p)
- **Hypothèse implicite fausse** : que la borne √p serait utile pour des sommes courtes. Elle est utile pour des sommes de longueur ≥ √p, pas O(log p).
- **Ce que la mort enseigne** : les bornes de Weil sont des bornes de SOMME COMPLÈTE. Pour les sommes partielles courtes, elles sont pires que triviales.
- **Où cela redirige** : même direction que ci-dessus.

### 4. Bourgain-Konyagin dans le régime O(log p)

- **Nom** : Théorèmes somme-produit pour sous-groupes courts
- **Type de mort** : borne hors-régime (exige |H| ≥ p^δ)
- **Hypothèse implicite fausse** : que les techniques somme-produit s'étendraient au régime logarithmique. Elles ne le font pas — le gap est exponentiel.
- **Ce que la mort enseigne** : le régime O(log p) est QUALITATIVEMENT différent du régime p^δ. Ce n'est pas un cas limite mais un monde séparé.
- **Où cela redirige** : vers des approches qui n'exigent pas de borne sur les sommes exponentielles individuelles.

---

## 18. Survivant pour R74

**Bilan programmatique et direction algébrique**

R74 doit :

1. **Dresser le bilan honnête du programme analytique** :
   - La réduction H ⟸ Lemme A' + Lemme B' est propre
   - Lemme B' est bloqué par le problème ouvert des sommes courtes (régime O(log p))
   - L'approche analytique par bornes de sommes exponentielles est ÉPUISÉE dans l'état de l'art 2026

2. **Explorer la direction algébrique identifiée en S2** :
   - La relation 2^S ≡ 3^k mod p contraint les valeurs de corrSum mod p
   - Cette contrainte est ALGÉBRIQUE, pas analytique — elle ne passe pas par les bornes de sommes
   - Premier test : pour p | d(k) avec p > C, la structure algébrique de corrSum mod p permet-elle d'exclure 0 directement ?

3. **Décider du format final du programme** :
   - Si la direction algébrique mord : formuler un nouveau sous-problème algébrique précis
   - Si la direction algébrique ne mord pas : documenter le programme comme problème ouvert avec réduction explicite

### Ce qui est acquis pour R74

- L'objet SOH H_k est canonique (L8 prouvé)
- Le cadre Fourier reste valide mais son exploitation analytique est bloquée
- La réduction H ⟸ Lemme A' + Lemme B' est propre
- Lemme B' est équivalent à borner des sommes courtes sur ⟨2⟩ — problème ouvert fondamental
- La direction algébrique (contraintes sur corrSum via 2^S ≡ 3^k mod p) est le seul candidat non exploré

### Condition de non-boucle pour R74

R74 doit :
1. NE PAS tenter une nouvelle borne sur des sommes exponentielles courtes
2. NE PAS reformuler le sous-problème bilinéaire/trilinéaire/multilinéaire dans un nouveau langage
3. Si la direction algébrique est testée : produire un CALCUL ou une CONTRAINTE concrète, pas une analogie
4. Si le bilan conclut "problème ouvert" : le documenter proprement et arrêter la boucle technique

---

## 19. Risques / limites

1. **Le diagnostic "problème ouvert fondamental" peut être prématuré** : il est possible qu'une technique très spécifique à la structure corrSum (et non aux sommes génériques sur ⟨2⟩) existe. Le projet n'a pas exploré cette possibilité car les rounds R71-R73 sont restés au niveau des sommes génériques.

2. **La direction algébrique identifiée en S2 n'est pas testée** : c'est une intuition (L1), pas une méthode. Elle pourrait s'effondrer immédiatement face à un examen sérieux.

3. **Le projet pourrait être dans une boucle de méta-niveaux** : R70 (doctrine), R71 (formulation), R72 (test opérateur → tautologique), R73 (test bilinéaire → circulaire). Chaque round diagnostique l'échec du précédent sans progresser vers la preuve. R74 risque d'être un 5ème round de diagnostic.

4. **Le déclassement est CORRECT mais pourrait être trop large** : il ferme la voie "bornes analytiques de sommes sur ⟨2⟩", ce qui est une grande famille. Mais peut-être que la structure SPÉCIFIQUE de corrSum (somme de termes 3^{k-1-j}·2^{A_j} avec contrainte de monotonie) offre des propriétés algébriques que les bornes de sommes génériques ne voient pas.

5. **Le risque de conclure "problème ouvert" trop tôt** : c'est la conclusion la plus confortable mais aussi la plus stérile. R74 doit résister à cette tentation si la direction algébrique n'a pas été honnêtement testée.

---

## 20. Verdict final avec score /10

**Score : 9/10**

R73 accomplit sa mission de test de mordant analytique :

1. **PHASE 1** : L'objet court exact est figé en trois niveaux (somme simple, bilinéaire, somme double), avec bornes triviales et graduation des gains (non trivial / intéressant / exploitable). La chaîne logique vers le verrou est tracée : seul un gain en p^{-ε} est exploitable.

2. **PHASE 2** : Cinq familles d'outils testées systématiquement. Résultat UNANIME : aucune ne fonctionne dans le régime O(log p). Cauchy-Schwarz dégrade, Abel et van der Corput sont circulaires, Weil et Bourgain-Konyagin sont hors régime. Le verdict de mordant est **NE MORD PAS**.

3. **PHASE 3** : Contrôle anti-boucle identifie la nouveauté partielle (précision du diagnostic) et le risque élevé de boucle. Décision : DÉCLASSER. Survivant pour R74 : bilan programmatique + direction algébrique.

Point manquant pour 10/10 : la direction algébrique (2^S ≡ 3^k mod p → contraintes sur corrSum) n'est pas testée — c'est le travail de R74.

**Score PASS : 6/6**

| Critère | Statut |
|---------|--------|
| PASS-1 : Objet court exact et type de gain figés | ✅ Trois niveaux, graduation explicite |
| PASS-2 : Chaîne logique gain → conséquence | ✅ Seul p^{-ε} est exploitable |
| PASS-3 : Au moins une borne candidate évaluée honnêtement | ✅ 5 familles testées, toutes échouent |
| PASS-4 : Contrôle anti-boucle clair | ✅ Circularité structurelle identifiée |
| PASS-5 : Décision honnête sur la voie bilinéaire | ✅ DÉCLASSER |
| PASS-6 : Survivant unique pour R74 | ✅ Bilan programmatique + direction algébrique |

---

## 21. Registre FAIL-CLOSED

| Objet | Statut |
|-------|--------|
| SOH H_k (factorisation) | [PROUVÉ] — inchangé |
| Factorisation T = ω · H_k | [PROUVÉ] — inchangé |
| Bi-géométricité (2ⁿ, 3^j) | [PROUVÉ] — inchangé |
| Gap exponentiel O(log p) vs p^δ | [PROUVÉ] — fait arithmétique |
| Cauchy-Schwarz dégrade la borne sur B | [CALCULÉ EXACT] — S^{5/2} > C ≈ S²/2 |
| Circularité de van der Corput sur F(c,L) | [SEMI-FORMALISÉ] — c → c·(2^h-1), même type |
| Circularité d'Abel sur F(c,L) | [SEMI-FORMALISÉ] — ramène F pondéré à F non pondéré |
| Weil hors régime (√p >> L) | [PROUVÉ] |
| Bourgain-Konyagin hors régime (|H| << p^δ) | [PROUVÉ] |
| Voie bilinéaire courte | [DÉCLASSÉE] — aucun gain dans le régime O(log p) |
| Opérateur de transfert (R71) | [RÉFUTÉ] — nilpotent (R72) |
| « Trou spectral » de L_j | [RÉFUTÉ] — spectre = {0} (R72) |
| Direction algébrique (2^S ≡ 3^k mod p) | [INTUITION L1] — non testée |
| Lemme B' (borne sur |H_k|) | [CONJECTURAL — BLOQUÉ] — requiert bornes de sommes courtes |
| Lemme A' (premier adéquat) | [CONJECTURAL] — inchangé |
| N_0(d) = 0 pour k ≥ 3 (Hypothèse H) | [CONJECTURAL] — inchangé |
| Somme courte F(c,L) bornée non trivialement | [PROBLÈME OUVERT] — au-delà de l'état de l'art 2026 |
| Réduction H ⟸ Lemme A' + Lemme B' | [SEMI-FORMALISÉ] — chaîne logique complète |
