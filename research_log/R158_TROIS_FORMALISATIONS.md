# R158 — TROIS FORMALISATIONS DU "+" : TEST DU MÉCANISME DE COUPLAGE

**Date** : 15 mars 2026
**Type** : Investigation autonome — 3 formalisations concrètes
**Front** : Le "+" (mécanisme de liaison entre monde additif et multiplicatif)
**Méthode** : Calcul numérique + diagnostic kill sur chaque formalisation

---

## 0. CONTEXTE

Suite à une suggestion externe (autre IA) que le "mécanisme de liaison" entre les mondes additif et multiplicatif n'aurait pas été assez étudié, nous testons 3 formalisations concrètes de ce "+" :

1. **Transport optimal** W₁(H, H-1) sur Z/pZ
2. **Défaut d'homomorphisme** Δ(a,b) = φ(a+b)/(φ(a)·φ(b)) où φ(a)=1-2^a
3. **k-énergie mixte E_mixed^{(3)}** avec 6-tuples (au lieu de 4-tuples)

---

## 1. FORMALISATION 1 : TRANSPORT OPTIMAL W₁(H, H-1)

### Objet
W₁ = distance de Wasserstein entre H = {2^a : a=0,...,r-1} et H-1 = {2^a-1 : a=0,...,r-1} sur (Z/pZ, distance circulaire).

### Résultat
**W₁(H, H-1) = r pour TOUS les premiers testés** (p ∈ {31, 89, 127, 257, 521, 1031, 8191}).

Le matching naturel h ↔ h-1 (avec distance |h-(h-1)| = 1 pour chaque paire) est TOUJOURS optimal. Coût total = r × 1 = r.

### Kill
**[MORT]** — objet constant (= r), aucune information arithmétique.

---

## 2. FORMALISATION 2 : DÉFAUT D'HOMOMORPHISME

### Objet
Δ(a,b) = φ(a+b) / (φ(a)·φ(b)) dans F_p*, où φ(a) = 1-2^a. Si φ était un homomorphisme (Z/rZ,+) → (F_p*,×), on aurait Δ ≡ 1.

### Résultats
- Δ = 1 dans **0% des cas** (sauf cas marginaux quand r pair)
- Valeurs distinctes de Δ : quasi-uniformes sur F_p* pour grand r
- Énergie du défaut ≈ énergie uniforme (ratio → 1 pour r → ∞)
- Aucune connexion établie avec |S_H(t)|

### Kill
**[MORT]** — objet bien défini mais non exploitable. La non-homomorphicité de φ est "maximale" (distribution uniforme des Δ), ce qui ne fournit aucune prise.

---

## 3. FORMALISATION 3 : k-ÉNERGIE MIXTE E_mixed^{(3)} (6-TUPLES)

### Objet
E_mixed^{(3)} = #{(a₁,...,a₆) ∈ {1,...,r-1}^6 : a₁+a₂+a₃ ≡ a₄+a₅+a₆ mod r ET ∏(1-2^{aᵢ}) = ∏(1-2^{aⱼ})}

### Pourquoi ça échappe à Vieta/T177
Pour k=2 (4-tuples) : 2 contraintes pour 2 fonctions symétriques → déterminé → N_cross = 0.
Pour k=3 (6-tuples) : 2 contraintes pour 3 fonctions symétriques → 1 degré de liberté → N_cross PEUT être > 0.

### Résultat numérique

| p | r | E_mixed^{(3)} | E_trivial | N_cross | N_cross/(r-1)³ |
|---|---|--------------|-----------|---------|----------------|
| 31 | 5 | 256 | 256 | **0** | 0 |
| 127 | 7 | 996 | 996 | **0** | 0 |
| 73 | 9 | 2528 | 2528 | **0** | 0 |
| 11 | 10 | 6273 | 3681 | **2592** | 3.56 |
| 89 | 11 | 5212 | 5140 | **72** | 0.07 |
| 23 | 11 | 6820 | 5140 | **1680** | 1.68 |
| 13 | 12 | 13981 | 6941 | **7040** | 5.29 |
| 43 | 14 | 15853 | 11713 | **4140** | 1.88 |
| 17 | 8 | 1885 | 1645 | **240** | 0.70 |
| 19 | 18 | 80257 | 26945 | **53312** | 10.85 |
| 29 | 28 | 515997 | 111645 | **404352** | 20.54 |

**N_cross > 0 pour 17/20 premiers testés.** C'est la **PREMIÈRE formalisation en 157 rounds** qui produit des collisions non triviales.

### MAIS : connexion au verrou BLOQUÉE

#### Test A : Distribution des modes B(s,t)

Le mode s=0 (= S_H(t)) n'est PAS anomaliquement petit :

| p | r | Rang moyen de s=0 | Typique (r/2) | Observation |
|---|---|-------------------|---------------|-------------|
| 29 | 28 | **1.0** | 14 | s=0 est le PLUS GRAND mode ! |
| 19 | 18 | **1.0** | 9 | Idem — S_H domine totalement |
| 89 | 11 | 7.6 | 5.5 | Anomaliquement petit, mais p >> r |
| 47 | 23 | 12.2 | 11.5 | Typique |

Pour p ≈ r+1 (racines primitives), |B(0,t)|² ≈ (r-1)² et |B(s≠0,t)|² ≈ 1. La décomposition ne dilue PAS S_H.

#### Test B : Borne par le moment 6

max|S_H| ≤ M₆^{1/6} = ((p-1)·E^×_3(H-1))^{1/6}

| p | r | max|S_H| | √r | M₆^{1/6} | M₆^{1/6}/√r |
|---|---|----------|-----|-----------|-------------|
| 29 | 28 | 27.0 | 5.29 | 46.8 | **8.84** |
| 89 | 11 | 10.0 | 3.32 | 14.8 | **4.46** |

Le moment 6 donne une borne **PIRE** que la triviale. Raison structurelle : M₆^{1/6} contient un facteur p^{1/6} qui explose quand p >> r (notre régime p ≈ e^r).

#### Test C : Direction de la borne

E_mixed^{(3)} ≤ E^×_3(H-1) par définition (contrainte supplémentaire réduit le comptage). Donc borner E_mixed ne borne PAS E^×_3 — c'est la **mauvaise direction**.

### Verdict Formalisation 3
**[SEMI-RÉEL]** — L'objet est non dégénéré (N_cross > 0, progrès réel sur T175/T176/T177). Mais :
- Pas de chemin vers |S_H| ≤ √r via le moment 6 (facteur p^{1/6} explose)
- Le mode s=0 de B(s,t) n'est pas anomaliquement petit (souvent le plus grand)
- E_mixed ≤ E^×_3 (mauvaise direction pour borner le moment)

---

## 4. RÉSULTAT NÉGATIF ADDITIONNEL : DOMINANCE DU MODE s=0

**Observation** : Pour les premiers où r ≈ p-1 (2 est racine primitive), le spectre de B(s,t) est CONCENTRÉ au mode s=0 :
- |B(0,t)|² ≈ (r-1)²
- |B(s,t)|² ≈ 1 pour s ≠ 0

**Explication** : Quand p = r+1 (soit (p-1)/r = 1), le caractère multiplicatif χ^{tr}(1-2^a) = χ^{(p-1)t}(1-2^a) = 1 pour tout a,t (car χ^{p-1} = 1). Donc B(s,t) = Σ_a e^{2πisa/r} · 1, qui vaut r-1 pour s=0 et 0 pour s≠0.

C'est un cas extrême, mais il montre que la décomposition bilinéaire ne peut pas aider quand la part multiplicative est "plate" — ce qui arrive exactement quand r divise (p-1) de manière "simple".

---

## 5. REGISTRE FAIL-CLOSED FINAL

| Objet | Statut | Kill |
|-------|--------|------|
| W₁(H, H-1) transport optimal | [MORT] | Constant = r, aucune info |
| Δ(a,b) défaut d'homomorphisme | [MORT] | Quasi-uniforme, non exploitable |
| E_mixed^{(3)} k-énergie 6-tuples | **[SEMI-RÉEL]** | N_cross > 0 (progrès) mais pas de chemin vers borne |
| Mode s=0 de B(s,t) | [INFORMATION NÉGATIVE] | s=0 domine quand r ≈ p-1 |
| Moment 6 comme borne | [MORT] | Facteur p^{1/6} explose en régime p >> r |
| Suspension recherche pure Bloc 3 | **MAINTENUE (8ème : R141-R157, R158)** |

**IVS** : 3.0/10 (premier objet non dégénéré depuis T166, mais sans chemin vers le verrou)

---

## 6. CE QUE CETTE INVESTIGATION APPORTE RÉELLEMENT

### Le positif
1. **Première formalisation en 157 rounds qui échappe à la dégénérescence de Vieta** (T175/T176/T177)
2. La raison est claire : pour k≥3, 2 contraintes < k fonctions symétriques élémentaires, donc les multiensembles ne sont plus déterminés
3. N_cross croît ∼ r⁴, ce qui confirme que le degré de liberté résiduel est réel

### Le négatif
1. La connexion au verrou |S_H| ≤ √r est **structurellement bloquée** par le facteur p^{1/2k} dans la borne du moment 2k
2. Le mode s=0 de B(s,t) **domine** le spectre quand r ≈ p-1, donc la décomposition ne peut pas isoler S_H comme un petit résidu
3. E_mixed ≤ E^×(mult seul) est la **mauvaise direction** pour borner S_H

### La leçon profonde
L'obstacle n'est pas l'absence de collisions non triviales — elles existent (formalisation 3 le prouve). L'obstacle est que **le moment 2k est structurellement inadapté au régime p >> r** : le facteur p^{1/2k} = e^{r/2k} ne peut jamais être compensé par un gain sur l'énergie de collision.

Cela confirme que le verrou V_SQRT_CANCEL = C_SC = BGK ε ≥ 0.215 n'est pas un problème de "trouver le bon objet de couplage" mais un problème de **méthode** : les moments ne suffisent pas, il faut un argument de nature différente (géométrie algébrique, amplification, ou résultat extérieur).

---

## 7. RECOMMANDATION STRATÉGIQUE

**La suggestion "étudier le + comme objet" a été testée exhaustivement sur 3 formalisations concrètes.**

Résultat : 2 mortes, 1 semi-réelle. Le mécanisme de couplage a effectivement été étudié — T175/T176/T177 l'étudient directement (et le tuent pour les 4-tuples). Pour les 6-tuples, le couplage est non dégénéré mais sans chemin vers la borne.

**Le diagnostic reste inchangé** : le verrou est un problème ouvert en TAN (théorie analytique des nombres) pour les sous-groupes de taille log p. Aucune approche interne (moments, énergie, décomposition bilinéaire) ne peut le résoudre sans un outil qualitativement nouveau.

**Condition de réouverture** :
- Résultat extérieur améliorant BGK pour |H| ≈ log p
- OU méthode non-moment pour borner des sommes de caractères (amplification de Vinogradov étendue ?)
- OU outil géométrique (monodromie, faisceaux — seul survivant R152)
