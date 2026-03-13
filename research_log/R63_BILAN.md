# R63 — BILAN : Réduction de D∞(d_δ) vers sommes exponentielles

## Type : P (proof-oriented)
## IVS : 9/10

**Justification IVS** :
- Potentiel de réfutation : 7/10 (si |S_h| ≫ √p sur sous-groupe, la route analytique s'effondre)
- Gain de structure : 10/10 (réduction complète D∞ → Erdős-Turán → sommes S_h → objet unique)
- Proximité d'un lemme : 9/10 (un seul objet à borner : |S_h| ≤ C·√p sur arc de sous-groupe)
- Risque d'accumulation : 1/10 (round très centré, pas de dispersion)

---

## Résumé exécutif

R63 réalise la **réduction technique décisive** : le verrou d'équidistribution D∞(d_δ) → 0 est réduit, via l'inégalité d'Erdős-Turán, à borner une unique famille de sommes exponentielles S_h = Σ_{δ=0}^{M} χ_h(1 + g^{2δ}). Numériquement, |S_h|/√p ≈ 0.50, très en-dessous de la borne de Weil. D∞_ET optimal décroît comme C·ln(p)/√p → 0. Le Candidat 1 (analytique) domine écrasement le Candidat 2 (combinatoire, 84 vs 39). Le verrou pour R64 est précisément identifié : prouver |S_h| ≤ C·√p sur l'arc du sous-groupe ⟨g²⟩.

---

## Méthode

- 2 scripts, 57 tests (33 + 24), 100% PASS
- Primes testés : p = 101, 251, 503, 1009
- Erdős-Turán appliqué numériquement et optimisé en H
- Sommes exponentielles S_h calculées exactement
- Récurrence affine c_{δ+1} = g²·c_δ + (1−g²) vérifiée
- 2 candidats évalués head-to-head (10 critères)

---

## Résultats

### AXE A — Réduction de D∞

| Mesure | p=101 | p=251 | p=503 | p=1009 |
|--------|-------|-------|-------|--------|
| D∞ observé (mean) | 0.100 | 0.051 | 0.036 | 0.028 |
| D∞_ET (H optimal) | 0.407 | 0.278 | 0.210 | 0.159 |
| |S_h|/√p (mean) | ~0.50 | ~0.50 | ~0.50 | ~0.50 |
| |S_h|/(M+1) | < 0.11 | < 0.11 | < 0.11 | < 0.11 |

**Réduction** : D∞ ≤ 1/H + (1/(M+1))·Σ_{h=1}^{H} |S_h|/h (Erdős-Turán).

**Objet minimal identifié** :
> S_h = Σ_{δ=0}^{M} χ_h(1 + g^{2δ}) mod p

C'est une **somme de caractères sur un arc du sous-groupe multiplicatif** ⟨g²⟩ ⊂ (Z/pZ)*, évaluée en le décalage 1+t.

**Fait structurel** : l'arc {g^0, g^2, ..., g^{2M}} couvre EXACTEMENT le sous-groupe ⟨g²⟩ (fraction = 1.0 pour tous les p testés). Donc S_h est une somme complète sur le sous-groupe ⟨g²⟩.

### AXE B — Outils vivants vs morts

| Outil | Statut | Score |
|-------|--------|-------|
| **Erdős-Turán + sommes exponentielles** | VIVANT | 9/10 |
| **Récurrence affine c_{δ+1} = g²c_δ+(1−g²)** | VIVANT | 8/10 |
| **Sommes sur sous-groupes (Bourgain, Burgess)** | VIVANT | 7/10 |
| Pseudo-aléa naïf | MORT | 0/10 |
| Large sieve brut | MORT | 0/10 |
| Weil directe hors-cadre | MORT | 0/10 |
| L²→L∞ générique | MORT | 0/10 |
| Comptage d'incidences pur | MORT (R63) | 2/10 |

### AXE C — D∞-lite : deux candidats

**Candidat 1 — Réduction analytique via Erdős-Turán** :
- D∞ ≤ O(ln(p)/√p) → 0 sous |S_h| ≤ C·√p
- Score : **84/100**
- Ladder : **L6 (schéma de preuve)**
- Pièce manquante unique : prouver |S_h| ≤ C·√p sur sous-groupe ⟨g²⟩
- Signal fort : |S_h|/√p ≈ 0.50 (100% sous 1.0)

**Candidat 2 — Réduction combinatoire via incidences** :
- E_obs/E_unif < 3 (peu de collisions), mais passage E → D∞ pointwise = cul-de-sac
- Score : **39/100**
- Ladder : L3 (observation répétée)
- Faiblesse fatale : Parseval ramène les incidences aux... sommes exponentielles (circulaire)
- **ÉLIMINÉ**

### AXE D — Chaîne globale quantifiée

| Étape | Sous D∞ = 2·ln(p)/√p | Statut |
|-------|----------------------|--------|
| η = D∞ | 0.44 (p=1009), 0.18 (p=10007) | CALCULÉ |
| τ ≤ 1/2 + η | 0.94 (p=1009), 0.68 (p=10007) | < 1 |
| ε = 1/2 − η | 0.06 (p=1009), 0.32 (p=10007) | > 0 |
| p_seuil (η < 1/4) | **p ≥ 4538** | CALCULÉ |
| A(2) borné | < 10 pour tout p > p_seuil | SEMI-FORMEL |

---

## Théorèmes

| ID | Énoncé | Statut |
|----|--------|--------|
| T133 | D∞(d_δ) décroît : mean 0.100→0.028 pour p=101→1009, tendance O(1/√p) [OBSERVÉ] | R63 |
| T134 | Erdős-Turán réduction : D∞ ≤ 1/H + (1/M)·Σ|S_h|/h, applicable et quantitatif [PROUVÉ] | R63 |
| T135 | Objet minimal : S_h = Σ χ_h(1+g^{2δ}) somme complète sur ⟨g²⟩, |S_h|/√p ≈ 0.50 [OBSERVÉ] | R63 |
| T136 | Gain carré-racine : |S_h|/(M+1) < 0.11, bien sous la borne triviale [OBSERVÉ] | R63 |
| T137 | D∞_ET optimal = O(ln(p)/√p) → 0, sous |S_h| ≤ C·√p [SEMI-PROUVÉ] | R63 |
| T138 | Candidat 1 analytique domine Candidat 2 combinatoire : 84 vs 39 /100 [CALCULÉ] | R63 |
| T139 | Seuil pratique : p_seuil ≈ 4538 pour η < 1/4, marge confortable [CALCULÉ] | R63 |

---

## Ladder of Proof

| Objet | Niveau | Commentaire |
|-------|--------|-------------|
| Réduction Erdős-Turán | L7 lemme prouvé | Inégalité standard, application vérifiée |
| D∞ = O(ln(p)/√p) | L6 schéma de preuve | Conditionnel sur |S_h| ≤ C·√p |
| |S_h| ≤ C·√p | L3 observation répétée | 100% sous 1.0, moyenne 0.50, pas encore prouvé |
| Chaîne D∞→τ<1→α<1→K-lite | L6 schéma de preuve | Tous maillons vérifiés quantitativement |
| Récurrence affine c_δ | L7 lemme prouvé | Identité algébrique vérifiée |

---

## Pistes fermées (autopsie)

### 1. Réduction combinatoire par incidences
- **Type de mort** : absorbée (par la route analytique via Parseval)
- **Hypothèse fausse** : on peut contrôler D∞ pointwise à partir de l'énergie additive seule
- **Réalité** : l'énergie E contrôle la distribution en moyenne (L²), pas en sup (L∞). Le passage L²→L∞ nécessite exactement les sommes exponentielles du Candidat 1.
- **Ce que ça enseigne** : la route combinatoire est subordonnée à l'analytique, pas indépendante
- **Redirige vers** : Erdős-Turán + sommes S_h

### 2. Pseudo-aléatoireté naïve de d_δ
- **Type de mort** : non ciblante
- **Hypothèse fausse** : d_δ se comporte "comme aléatoire" sans structure exploitable
- **Réalité** : la structure affine c_{δ+1} = g²c_δ + (1−g²) est cruciale et exploitable
- **Redirige vers** : exploiter la récurrence, pas la contourner

### 3. Large sieve directe sur d_δ
- **Type de mort** : trop faible (déjà mort en R59, re-confirmé)
- **Réalité** : donne ≥ M+1, pire que trivial
- **Redirige vers** : Erdős-Turán (outil correct)

### 4. Weil directe sur F_p entier
- **Type de mort** : non adaptée
- **Hypothèse fausse** : la somme est sur tout F_p
- **Réalité** : la somme est sur le sous-groupe ⟨g²⟩, besoin de Burgess/Bourgain
- **Redirige vers** : estimation sur sous-groupes

---

## Survivant R64

**Réduction analytique D∞-lite** : D∞ ≤ O(ln(p)/√p) → 0, conditionnel sur |S_h| ≤ C·√p.

**Verrou restant** : Prouver que
> |S_h| = |Σ_{t ∈ ⟨g²⟩} χ_h(1 + t)| ≤ C·√p

C'est une **somme de caractères sur un sous-groupe décalé**. L'arc couvre exactement ⟨g²⟩ (sous-groupe d'ordre (p-1)/2).

**Outils candidats pour R64** :
- Complétion : Σ_{t∈⟨g²⟩} χ(1+t) = (1/2)·Σ_{t∈F_p*} (1+η(t))·χ(1+t) où η est le caractère du sous-groupe
- Weil sur la partie complète : |Σ_{F_p*} χ(1+t)| ≤ √p
- Borne résiduelle : |Σ η(t)·χ(1+t)| = somme de deux caractères composée → Jacobi
- Alternative : Bourgain-Konyagin pour sommes sur sous-groupes grands (|⟨g²⟩| = (p-1)/2 > p/3)

**Ladder** : L6 (schéma de preuve) → L7 visé en R64.

---

## Critères PASS

| Critère | Statut |
|---------|--------|
| PASS-1 : formulation canonique utile de D∞ isolée | ✅ Erdős-Turán + sommes S_h |
| PASS-2 : réduction prioritaire sélectionnée | ✅ Analytique (84/100) |
| PASS-3 : objet minimal cible identifié | ✅ S_h = Σ χ_h(1+g^{2δ}) sur ⟨g²⟩ |
| PASS-4 : tentative éliminée avec autopsie | ✅ 4 pistes fermées |
| PASS-5 : survivant unique pour R64 | ✅ D∞-lite analytique |

**Score : 5/5 PASS**

---

## Risques et limites

1. **|S_h| ≤ C·√p pas encore prouvé** : c'est le dernier verrou, mais les outils existent (complétion + Weil + Jacobi)
2. **La constante C compte** : si C trop grand, p_seuil augmente, mais le résultat reste asymptotique
3. **⟨g²⟩ = sous-groupe d'index 2** : cas favorable, car le sous-groupe est très grand ((p-1)/2)
4. **R3 seulement** : en R1/R2, l'arc pourrait ne pas couvrir tout ⟨g²⟩, ajout de difficulté

---

## CEC inchangé

---

## Verdict final : 9/10

R63 est la **réduction technique clé** du projet. Le verrou d'équidistribution est maintenant réduit à un unique objet mathématique bien identifié : une somme de caractères sur sous-groupe décalé. L'outil (Erdős-Turán) est standard, la borne souhaitée (|S_h| ≤ C·√p) est plausible numériquement (|S_h|/√p ≈ 0.50), et la pièce manquante est attaquable par complétion + Weil + Jacobi. Le survivant monte à Ladder L6. R64 devra attaquer directement la borne sur |S_h|.
