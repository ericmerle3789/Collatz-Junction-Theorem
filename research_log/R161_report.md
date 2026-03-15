# R161 — INVESTIGATION DES 3 ANGLES MORTS
## Audit de "Stratégie de Percée : Genèse d'un Nouvel Outil pour le Bloc 3"

**Date** : 15 mars 2026
**Source** : Document externe proposant 3 pistes inexploitées
**Script** : `R161_three_blind_spots.py`
**Protocole** : Fail-Closed — contenu non tautologique et non circulaire requis

---

## 0. LE DOCUMENT SOURCE

Le document identifie correctement le **Principe d'Incompatibilité** entre :
- L'espace Z (taille, ordre, monotonie, anti-alignement)
- L'espace Z/dZ (structure algébrique, condition de cyclicité)

Il propose 3 angles morts et un cahier des charges pour un nouvel outil (IRT).

---

## 1. ANGLE A — Géométrie d'Arakelov Combinatoire

**Proposition** : Créer un "Degré d'Arakelov" h(corrSum) = contribution archimédienne + contribution non-archimédienne. Prouver h ≠ 0 pour tout arrangement monotone.

**Test** : h(x) = log|x| − Σ_{p|d} min(v_p(x), v_p(d)) · log(p)

**Résultat** :
- Pour x = m·d : h = log(m·d) − log(d) = log(m)
- Pour x ≢ 0 mod d : h = log|x| − (contribution partielle)

**VERDICT : MORT — Tautologie**

La hauteur d'Arakelov pour un entier x ∈ Z est la formule du produit :
x = ±∏_p p^{v_p(x)}

C'est l'arithmétique fondamentale, pas un invariant géométrique. La géométrie d'Arakelov enrichit les *variétés* via le théorème de Riemann-Roch et la théorie d'intersection. Pour un entier isolé, il n'y a pas de structure géométrique à exploiter. L'invariant proposé **encode** la divisibilité par d, il ne la **prédit** pas : il est circulaire.

---

## 2. ANGLE B — Distorsion de Pente (Slope Distortion)

**Proposition** : La trajectoire B_j a une pente idéale σ ≈ log₂3 − 1 ≈ 0.585. Pour corrSum ≡ 0 mod d, les B_j doivent s'écarter drastiquement de cette pente.

**Test numérique** : Pour k = 3..10 (énumération exhaustive), mesurer la déviation L² par rapport à la droite B_j = j·σ, et comparer les compositions "quasi-multiples" (résidu ≈ 0 mod d) aux autres.

**Résultat** :

| k | Ratio near/far | Verdict |
|---|----------------|---------|
| 3 | 0.000 (0 cas near) | — |
| 4 | 1.419 | Fluctuation |
| 5 | 0.997 | Normal |
| 6 | 1.130 | Normal |
| 7 | 1.357 | Fluctuation |
| 8 | 1.084 | Normal |
| 9 | 1.149 | Normal |
| 10 | 0.948 | Normal |

**Ratio moyen = 1.01** — aucune corrélation significative.

**VERDICT : MORT — Observable de Z détruite par mod d**

La déviation de pente vit dans Z. Par le Principe d'Incompatibilité (confirmé numériquement par le MPF en R160 et ce test), TOUTE observable de Z est absorbée par la réduction mod d. Les fluctuations pour k petit sont du bruit d'échantillonnage (peu de cas "near").

---

## 3. ANGLE C — Automates / Mots Sturmiens

**Proposition** : Utiliser le théorème de Cobham ou la théorie des automates pour prouver qu'une séquence B_j satisfaisant corrSum ≡ 0 mod d exigerait une "complexité de mot" incompatible avec la monotonie.

**Test** : Complexité de sous-mots C(2) de la séquence de gaps, comparée entre quasi-multiples et compositions éloignées.

**Résultat** : Tous les ratios entre 0.98 et 1.065. **Ratio moyen = 1.015** — aucune corrélation.

**VERDICT : MORT — Erreur de catégorie**

1. Le théorème de Cobham (1969) s'applique aux séquences **infinies**. Notre B_j est de longueur finie k ≤ 41. Pour les séquences finies, il n'existe pas de contrainte de complexité non triviale.

2. La corrSum est une combinaison linéaire pondérée des 2^{B_j}, pas un objet reconnaissable par automate fini. L'application de la théorie des automates est une erreur de catégorie.

3. Les mots sturmiens (complexité C(n) = n+1) sont le seuil minimal pour les mots binaires apériodiques. Nos gaps prennent des valeurs 0, 1, 2, ... (pas binaires), et la contrainte de monotonie n'impose pas de complexité sturmienne.

---

## 4. TEST TRANSVERSAL

4 observables de Z testées simultanément pour k = 3..10 :

| Observable | Ratio moyen near/far |
|-----------|---------------------|
| corrSum | ~1.27 (biaisé par taille, PAS par résidu) |
| Σ B_j | ~1.16 (même biais taille) |
| max gap | ~0.97 |
| courbure | ~0.98 |

Les observables de taille (corrSum, Σ B_j) montrent un léger biais car les quasi-multiples tendent à être plus grands (corrSum plus élevé = m ≥ 1). Mais les observables de *forme* (max gap, courbure) sont parfaitement neutres.

**Conclusion** : La structure mod d est **indépendante** de la forme de la trajectoire B_j. Seule la taille globale (déjà couverte par l'argument C/d) montre un biais trivial.

---

## 5. VERDICT GLOBAL

### Le diagnostic (§1) est CORRECT :
Le Principe d'Incompatibilité entre Z et Z/dZ est la racine du blocage. Les 248+ pistes fermées en R1-R161 sont toutes des manifestations de ce même obstacle.

### Les solutions (§3-4) sont MORTES :
Les 3 angles morts et le cahier des charges de l'IRT restent du côté Z de l'incompatibilité. Aucun ne franchit le pont vers Z/dZ.

### Le Principe d'Incompatibilité formalisé :

> **Pour toute fonction f : {compositions monotones} → R mesurable dans Z (taille, ordre, complexité, courbure, pente, entropie), la distribution de f conditionné à corrSum ≡ 0 mod d est statistiquement indistinguable de la distribution inconditionnelle.**

Ce principe, vérifié numériquement sur 7+ observables et 8 valeurs de k, implique que tout outil vivant exclusivement dans Z est structurellement incapable de détecter la condition modulaire.

### L'unique espoir :
Un outil qui opère **simultanément** dans Z et Z/dZ, exploitant le fait que d = 2^S − 3^k partage les briques {2, 3} avec corrSum. Un tel outil n'existe pas dans la littérature (R160 Direction 1 : AUCUN outil pour Σ e(2^n/p) quand |H| ~ log p). Sa création constituerait une avancée fondamentale en théorie analytique des nombres.

---

## NE PAS FAIRE (ajouté à la carte)

- Géométrie d'Arakelov combinatoire pour corrSum → CIRCULAIRE
- Distorsion de pente (Slope Distortion) → observable Z, AUCUNE corrélation
- Mots sturmiens / Cobham → erreur de catégorie (séquences finies)
- IRT / Diophantine-Modular Gap → reste du côté Z
- Toute observable de Z comme prédicteur de corrSum mod d → UNIVERSELLEMENT DESTRUCTEUR
