# SP10 Level 11 — Argument structurel : Régime B vide

**Date** : 2 mars 2026
**Objectif** : Explorer pourquoi le Régime B (p ≥ m⁴) est empiriquement vide pour les diviseurs de d(k), et chercher un argument structurel pour le prouver.

---

## 1. Contexte (résumé L10)

L'architecture de la preuve de la Condition (Q) est :

| Cas | Statut |
|-----|--------|
| k ≤ 68 | D17, **CLOS** |
| k ≥ 69, Régime A (p < m⁴) | Di Benedetto + Phase I, **CLOS** |
| k ≥ 69, Régime B (p ≥ m⁴), générique (n₃ = (p-1)/m) | N = 0, **CLOS** |
| k ≥ 69, Régime B, n₃ > 3m·ln(p) | N = 0, **CLOS** |
| k ≥ 69, Régime B, n₃ petit, 3 ∉ ⟨2⟩ | N = O(ln p/n₃), **COND.** (Konyagin) |
| k ≥ 69, Régime B, 3 ∈ ⟨2⟩ | Empiriquement vide, **HEUR.** |

Score : **4.80/5**. Le gap est le cas 3b-ii, conditionnel à l'effectivisation de Konyagin/BGK.

**Question L11** : Peut-on montrer que le Régime B est **structurellement vide** pour p | d(k), ce qui fermerait le gap sans besoin de Konyagin ?

---

## 2. Analyse numérique des ratios (Analyse 1)

**Script** : `scripts/exploration/sp10_level11_structural.py`

Pour k = 69..150, toutes les paires (k, p) avec p | d(k) et p > 3 :

| Statistique | Valeur |
|-------------|--------|
| Total paires (k,p) | 124 |
| Régime A (p < m⁴) | **124** |
| Régime B (p ≥ m⁴) | **0** |
| Ratio max log(p)/log(m) | **2.4894** |
| Ratio médian | 1.161 |
| Seuil Régime B | 4.0 |
| Marge minimale | 1.5106 |

**Top 5 cas les plus proches de Régime B :**

| k | p | m = ord_p(2) | ratio | p/m⁴ |
|---|---|-------------|-------|------|
| 90 | 127 | 7 | 2.489 | 0.053 |
| 78 | 127 | 7 | 2.489 | 0.053 |
| 71 | 127 | 7 | 2.489 | 0.053 |
| 85 | 151 | 15 | 1.852 | 0.003 |
| 119 | 151 | 15 | 1.852 | 0.003 |

**Observation clé** : Le cas le plus proche est p = 127, m = 7. Pour atteindre le Régime B, il faudrait p ≥ 7⁴ = 2401. On a p = 127, soit un facteur **19× trop petit**.

---

## 3. Contrainte structurelle (Analyse 2)

Pour tout p | d(k) avec m = ord_p(2) et S = ⌈kθ⌉ :

**Identité fondamentale** : p | (2^r − 3^k) où r = S mod m, 0 ≤ r < m.

Cette identité est vérifiée pour **100%** des 124 paires testées.

**Distribution de r/m** : uniforme dans [0, 1), comme attendu (S mod m est essentiellement aléatoire).

**Cas de n₃** :
- 3 ∈ ⟨2⟩ mod p (i.e. n₃ | m) : 11/124 cas (8.9%)
- Catégorie n₃ petit (≤ 2) : ratio max 2.489
- Catégorie n₃ moyen (3-10) : ratio max 1.852
- Catégorie n₃ grand (> 10) : ratio max 1.589

Les n₃ petits produisent les ratios les plus élevés, comme attendu (contrainte plus faible).

---

## 4. Connexion Artin (Analyse 3)

**Question** : Quelle fraction des primes p a ord_p(2) ≤ p^{1/4} (condition nécessaire pour Régime B) ?

| Statistique | Valeur |
|-------------|--------|
| Primes testés (p < 50000) | 5131 |
| ord_p(2) = p − 1 (Artin) | ~37.4% |
| ord_p(2) ≤ p^{1/4} | **0** (0.00%) |

**Résultat** : Sur les 5131 primes testés, **aucun** n'a ord_p(2) ≤ p^{1/4}. Cela confirme que les primes avec m petit relativement à p sont extrêmement rares (possiblement inexistants pour base 2).

**Remarque théorique** :
- Conjecture d'Artin (Hooley 1967, sous GRH) : 2 est racine primitive pour une proportion positive (~37.4%) des primes.
- Pour qu'un prime soit en Régime B, il faut ord_p(2) ≤ p^{1/4}, ce qui est l'extrême opposé d'Artin.
- Sous GRH, on peut probablement montrer que la densité de tels primes est 0, mais cela reste **conditionnel**.

---

## 5. Arguments élémentaires (Analyse 4)

### 5.1 Contrainte de Mersenne

Si p | d(k) et ord_p(2) = m, alors p | (2^m − 1) (facteur de nombre de Mersenne).

Les facteurs premiers de 2^m − 1 satisfont p ≡ 1 (mod m), et le plus petit possible est p = 2m + 1.

### 5.2 Nombres de Mersenne premiers

Pour les nombres de Mersenne premiers M_q = 2^q − 1 (q premier) :
- ratio = log(M_q)/log(q) ≈ q·log(2)/log(q) → ∞
- Exemples : M_17 = 131071 (ratio ≈ 4.16), M_19 = 524287 (ratio ≈ 4.47)

**M_17 et au-delà SONT en Régime B** (ratio > 4). Mais :
- Aucun nombre de Mersenne premier M_q pour q ≥ 17 ne divise d(k) pour k ∈ [69, 500]
- Densité attendue : ~0.78% des k, mais 0 observé

### 5.3 Borne p ≤ 2^m − 1

**ERREUR identifiée** : p | (2^m − 1) ne signifie PAS p ≤ 2^m − 1 ; p est un facteur premier, pas une borne.

Pour m composé, les facteurs de 2^m − 1 sont contraints par les facteurs primitifs, mais aucune borne simple ne donne ratio < 4 inconditionnellement.

---

## 6. Investigation Mersenne dans d(k) (Analyse 5)

Pour k = 69..100, on calcule gcd(d(k), 2^m − 1) pour m = 3..200 :

- Les diviseurs communs retrouvent exactement les facteurs premiers de d(k) trouvés en Analyse 1
- Aucun facteur « nouveau » n'est révélé par cette méthode
- Les valeurs de m pour lesquelles d(k) ≡ 0 (mod 2^m − 1) correspondent aux cas déjà connus

---

## 7. Distance au Régime B (Analyse 6)

Distribution du gap = 4.0 − log(p)/log(m) :

| Statistique | Valeur |
|-------------|--------|
| Gap minimum | **1.5106** (k=90, p=127, m=7) |
| Gap Q1 | 2.148 |
| Gap médiane | 2.839 |
| Gap Q3 | 3.179 |
| Gap maximum | 3.589 |

Pour le cas le plus proche (p=127, m=7) : il faudrait p ≥ 2401 pour être en Régime B. Le facteur manquant est **19×**.

---

## 8. Tentative de preuve et erreur critique

### 8.1 Tentative « Théorème SP10c »

En cours de session, une tentative a été faite de prouver Régime B vide via la borne de Weil :

**Claim (INVALIDE)** : « ρ(p) ≤ 2/√p par la borne de Weil, donc (p-1)·ρ^{52} ≤ 2^{-48} < 0.041. »

### 8.2 Erreur détectée

La borne de Weil pour les sommes exponentielles sur sous-groupes multiplicatifs donne :

    |S_t| = |∑_{j=0}^{m-1} e(t·2^j/p)| ≤ √p

Donc ρ = |S_t|/m ≤ **√p/m** (pas 2/√p).

Dans le Régime B (p ≥ m⁴) :
    √p/m ≥ m²/m = m ≥ 2

**La borne de Weil est PIRE que la borne triviale ρ ≤ 1 en Régime B.**

### 8.3 Vérification numérique

| p | m | ρ(p) réel | 2/√p | ρ > 2/√p ? |
|---|---|-----------|------|-----------|
| 31 | 5 | 0.540 | 0.359 | **OUI** |
| 43 | 14 | 0.189 | 0.305 | non |
| 73 | 9 | 0.292 | 0.234 | **OUI** |
| 89 | 11 | 0.201 | 0.212 | non |
| 127 | 7 | 0.618 | 0.177 | **OUI** |
| 151 | 15 | 0.143 | 0.163 | non |
| 937 | 117 | 0.098 | 0.065 | **OUI** |

Le claim ρ ≤ 2/√p est **faux** pour 4/7 cas testés. Le « Théorème SP10c » est **invalide**.

---

## 9. Conclusion L11

### 9.1 Ce qui est acquis

1. **Numériquement** : Régime B est vide pour k = 69..150, factor_limit = 10⁶.
2. **Ratio max** : 2.489 (marge de 1.51 au seuil 4.0).
3. **Densité Artin** : 0% des primes p < 50000 ont ord_p(2) ≤ p^{1/4}.
4. **CI Phase I** : k = 69..275, 141 PASS, 0 FAIL, 66 timeouts.

### 9.2 Ce qui reste ouvert

1. **Pas de preuve structurelle** que Régime B est vide pour tout k.
2. **Pas d'argument élémentaire** via la taille des nombres de Mersenne.
3. **La borne de Weil ne suffit pas** en Régime B.
4. **Konyagin/BGK** (c explicite) reste la piste la plus prometteuse.
5. **GRH + Artin** pourrait fermer le gap conditionnellement.

### 9.3 Score inchangé

**Score : 4.80/5** — Le gap Régime B (cas 3b-ii) reste conditionnel à Konyagin/BGK.

Les 3 pistes restantes :
- **(A)** GRH/Artin conditionnel → score 4.95/5
- **(B)** Structure de d(k) (nombres de Mersenne, facteurs primitifs) → non concluant
- **(C)** Effectivisation de Konyagin c > 0 → score 5.0/5 si c explicite

---

## 10. Anti-hallucination log L11

| # | Erreur détectée | Source | Correction |
|---|----------------|--------|------------|
| 5 | ρ ≤ 2/√p « par borne de Weil » | Session L11 | FAUX. Weil donne |S_t| ≤ √p → ρ ≤ √p/m ≥ m en Rég.B. Vérifié numériquement. |
| 6 | p ≤ 2^m − 1 comme borne | Analyse 4 | FAUX. p est facteur PREMIER de 2^m − 1, donc p ≤ 2^m − 1 est trivial mais le ratio log(p)/log(m) ≤ m·log 2/log m → ∞. |
| 7 | « ratio < 4 par borne élémentaire » | Analyse 4 | NON PROUVÉ. Aucun argument élémentaire ne contraint le ratio. |
| 8 | « Artin ferme le gap » | Analyse 3 | CONDITIONNEL à GRH. Non inconditionnel. |

(Erreurs 1-4 : voir L10 research log.)

---

## 11. Scripts créés (L11)

- `sp10_level11_structural.py` : 6 analyses + synthèse + anti-hallucination log

---

## 12. Références additionnelles (L11)

- Hooley (1967). On Artin's conjecture. J. Reine Angew. Math. 225, 209–220.
- Silverman (1988). Wieferich's criterion and the abc-conjecture. J. Number Theory 30, 226–237.
- Granville, Pomerance (2002). Two contradictory conjectures concerning Carmichael numbers. Math. Comp. 71, 883–908.
