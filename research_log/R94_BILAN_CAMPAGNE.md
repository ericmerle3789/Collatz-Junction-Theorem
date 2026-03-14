# R94 — BILAN FINAL DE CAMPAGNE R89→R93

**Date**: 14 mars 2026
**Type**: X/I/P-MULTIROUND — Campagne autonome fermée
**Rounds actifs**: R89, R90, R91, R92, R93 (5/5 rounds utilisés)

---

## 1. RÉSUMÉ EXÉCUTIF GLOBAL

La campagne R89→R93 a poursuivi deux axes parallèles:
- **Axe 1 (Fermeture computationnelle du gap)**: MORT dès R89 — les deux candidats (G1, G2) sont redondants avec R34/R35/R84.
- **Axe 2 (Recherche théorique sur le verrou multilinéaire)**: A produit un SURVIVANT QUALIFIÉ — le candidat T4 "Anticorrélation des phases hybrides", partiellement prouvé avec condition ord_p(2) > √p.

**Survivant global**: T4 [PARTIELLEMENT PROUVÉ, CONDITIONNEL]

---

## 2. HISTORIQUE DE LA CAMPAGNE R89→R93

### R89 — Recalage et qualification
- Axe 1: G1 (méta-certification CRT) et G2 (compression DP) proposés
- Axe 2: T1 (Bourgain direct) et T2 (trace functions FKM) proposés
- **Verdicts Investigateur Historique**: G1 REDONDANT, T1 REDONDANT, G2 PARTIELLEMENT REDONDANT, T2 obstruction fondamentale (2^b non algébrique)
- **Découverte R89**: Reformulation sous-groupe H = ⟨2⟩ + product-to-sum → candidat T2-bis (SLS)
- **Morts**: G1, G2, T1, T2. **Survivant**: T2-bis [QUALIFIÉ AVEC RÉSERVE]

### R90 — Première poussée structurelle
- Formalisation de la chaîne de preuve en 5 étapes (orthogonalité → non-factorisation → gap simplexe/boîte → réduction mod r → relation exacte)
- **Relation exacte découverte**: N_0(p) = (C/r^k)·N_H(0) + R
- Littérature: BGK (2006) quantitativement insuffisant (ε ≈ 0.011, besoin k > 91)
- Cochrane-Hart-Pinner-Spencer (2014): Waring sur sous-groupes
- Tao (2011, 2019): confirme les barrières harmoniques
- **T2-bis bloqué** par le reste R non borné. **T3 (SWL)** proposé pour borner R via Fourier de W.

### R91 — Audit croisé et réduction du champ
- **RÉSULTAT NÉGATIF PROFOND**: |Ŵ(ℓ)| = |Ŵ(0)| exactement pour tout ℓ
  - Preuve: W supporté sur une unique classe mod r → caractères constants sur le support
  - Vérification numérique: k=21, p=5, r=4 → |Ŵ(1)/Ŵ(0)| = 1.000
- **T3 TUÉ** (spectre plat, aucune décroissance possible)
- **Diagnostic**: Le reste R dépend entièrement des sommes hybrides S_i^{(ℓ)}(t) = Σ_{b} ω_r^{ℓb}·e_p(t·α_i·2^b)
- **T4 proposé**: "Anticorrélation des phases hybrides" — borner Σ_{Z_H} χ_ℓ(∏h_i)

### R92 — Test de preuve / certification
- **Test numérique T4 PASSÉ**: k=21, p=5: W_ℓ = 0 exactement pour ℓ=1,2,3
- **Semi-formalisation RÉUSSIE**: 5 étapes toutes [PROUVÉES]
  - A: Détection par caractère additif [PROUVÉ]
  - B: t=0 → contribution nulle (orthogonalité χ_ℓ non trivial) [PROUVÉ]
  - C: Lifting χ_ℓ → F_p* via (p-1)/r extensions de Gauss [PROUVÉ]
  - D: Borne |S_i^{(ℓ)}(t)| ≤ √p (Gauss sums classiques) [PROUVÉ]
  - E: Produit → ratio = p·(√p/r)^k → 0 si r > √p [PROUVÉ]
- **Condition**: ord_p(2) > √p (vrai densité 1 conditionnelle GRH)
- **Moment L²**: Σ_t |S_i^{(ℓ)}(t)|² = rp → RMS = √r (pas √p!)
- **Structure orbitale**: S_j^{(ℓ)}(t) = S_0^{(ℓ)}(t·3^{k-1-j})
- **T5 (Equidist. orbitale)** proposé mais insuffisamment mûr → suspendu

### R93 — Tournoi final
- **Vainqueur unique**: T4 [PARTIELLEMENT PROUVÉ, CONDITIONNEL]
- T5 suspendu (heuristique)
- Tous les autres éliminés

---

## 3. RÉSULTATS AXE 1 (FERMETURE COMPUTATIONNELLE)

**Verdict**: Axe mort dès R89.
- G1 (Méta-certification CRT): [ÉLIMINÉ] — redondant avec R34 (71/71 non-bloquants), R35 (CRT product réfuté), R31 (bad primes caractérisés)
- G2 (Compression DP): [ÉLIMINÉ] — partiellement redondant avec R84, impact global 3/10

**Leçon**: L'axe computationnel n'a rien de nouveau à offrir en termes de PROGRAMME (vs k-par-k). La méthode R84 est complète mais intrinsèquement k-par-k.

---

## 4. RÉSULTATS AXE 2 (RECHERCHE THÉORIQUE)

### Cadre exact (T2-bis, absorbé)
**Relation fondamentale** (NOUVELLE dans le projet):
```
N_0(p) = (C/r^k) · N_H(0) + R

avec:
- N_H(0) = #{(h_i) ∈ H^k : Σ α_i·h_i ≡ 0 mod p}
- H = ⟨2⟩ ⊂ F_p*, r = |H| = ord_p(2)
- W̄ = C/r^k (poids moyen sur la boîte {0,...,r-1}^k)
- R = reste dû à la non-uniformité des poids W(b)
```

### Spectre plat (T3, RÉFUTÉ)
**Théorème** (PROUVÉ):
|Ŵ(ℓ)| = |Ŵ(0)| pour tout ℓ ∈ {0,...,r-1}.

Cause: W supporté sur |b| ≡ N mod r (unique classe) → caractères de Z/rZ constants sur le support.
**Conséquence**: Aucune aide ne vient de la "lissité" des poids. Le reste R dépend ENTIÈREMENT des sommes hybrides.

### Lemme conditionnel (T4, PARTIELLEMENT PROUVÉ)
**Théorème conditionnel** (SEMI-FORMALISÉ, 5 étapes PROUVÉES):

Pour p premier ≥ 5 avec **ord_p(2) > √p**, et pour tout ℓ ∈ {1,...,r-1}:

|Σ_{(h_i) ∈ Z_H(α)} χ_ℓ(∏h_i)| ≤ (p-1) · p^{(k-2)/2}

Ce qui donne un ratio par rapport à N_H(0) ≈ r^k/p de:
ratio ≤ p · (√p/r)^k → 0 quand k → ∞ (sous la condition r > √p)

**Chaîne de preuve complète**:
1. [PROUVÉ] Orthogonalité → somme = (1/p)·Σ_t ∏_i S_i^{(ℓ)}(t)
2. [PROUVÉ] t=0 contribue 0 (caractère non trivial sur H)
3. [PROUVÉ] Lifting: S_i^{(ℓ)}(t) = (r/(p-1))·Σ_n G(χ̃^n, ψ_{tα_i}) avec (p-1)/r sommes de Gauss
4. [PROUVÉ] |G(χ̃^n, ψ_a)| = √p pour χ̃^n non trivial, a ≠ 0
5. [PROUVÉ] Triangle inequality → |S_i^{(ℓ)}(t)| ≤ √p → produit ≤ p^{k/2}

### Moment L² (NOUVEAU)
**Identité exacte** (PROUVÉE):
Σ_{t=1}^{p-1} |S_i^{(ℓ)}(t)|² = rp

Donc: RMS(|S_i^{(ℓ)}|) = √(rp/(p-1)) ≈ √r

**Signification**: Le bound √p (étape D) est LÂCHE d'un facteur √(p/r).
En L², chaque facteur contribue √r, pas √p.
Le produit en L² donne r^{k/2}, pas p^{k/2}.
Le gap entre L² et L^∞ est le verrou résiduel.

### Structure orbitale (T5, HEURISTIQUE)
S_j^{(ℓ)}(t) = S_0^{(ℓ)}(t·3^{k-1-j})

Le produit ∏_i S_i^{(ℓ)}(t) évalue UNE fonction S_0^{(ℓ)} en k points
le long de l'orbite multiplicative de ⟨3⟩ dans F_p*.
Exploiter l'équidistribution de ces points pourrait lever la condition r > √p.

---

## 5. COMPARAISON FINALE DES AXES

| Critère | Axe 1 (Gap) | Axe 2 (Théorie) |
|---------|-------------|-----------------|
| Candidats qualifiés | 0/2 | 1/5 (T4) |
| Résultat formel | Aucun | Théorème conditionnel |
| Résultat négatif | Redondance confirmée | Spectre plat (T3) |
| Objet nouveau | Aucun | N_0 = (C/r^k)·N_H + R |
| Impact programme | 0/10 | 7/10 |
| Avancement preuve | — | [PARTIELLEMENT PROUVÉ] |

**Verdict**: Axe 2 >> Axe 1, sans ambiguïté.

---

## 6. SURVIVANT GLOBAL

**T4: "Anticorrélation des phases hybrides"** [QUALIFIÉ AVEC RÉSERVE]

### Fiche d'identité
- **Objet**: Σ_{(h_i)∈Z_H(α)} χ_ℓ(∏h_i) — somme de caractère multiplicatif sur zéro-ensemble additif dans H^k
- **Lemme**: |somme| < N_H(0) pour tout ℓ ≠ 0 (cancellation des phases χ_ℓ)
- **Condition**: ord_p(2) > √p
- **Statut**: [PARTIELLEMENT PROUVÉ] — conditionnel sur la taille de l'ordre
- **Réfutation**: Trouver un prime p avec ord_p(2) > √p et |somme| ≥ N_H(0) — non trouvé
- **Test numérique**: PASSÉ (k=21, p=5, cancellation exacte)

### Ce que T4 apporte au programme global
1. **Cadre exact**: N_0(p) = (C/r^k)·N_H(0) + R — relie directement compositions Collatz aux zéro-sommes dans H^k
2. **Contrôle conditionnel de R**: Pour les primes p | d(k) avec ord_p(2) > √p, le reste R est borné
3. **Quantification du gap L²/L^∞**: √r vs √p identifié comme le verrou résiduel
4. **Structure exploitable**: orbite de ⟨3⟩ → réduction à une seule fonction évaluée en k points

### Ce que T4 ne résout PAS
1. Le cas ord_p(2) ≤ √p (incluant les premiers de Mersenne)
2. Le passage N_0(p) borné → N_0(d) = 0 (CRT encore nécessaire)
3. La preuve pour TOUT k ≥ 21 (l'universalité)

---

## 7. STATUT DE PREUVE / CERTIFICATION

| Élément | Statut |
|---------|--------|
| Relation N_0(p) = (C/r^k)·N_H(0) + R | [PROUVÉ] |
| Spectre plat |Ŵ(ℓ)| = |Ŵ(0)| | [PROUVÉ] |
| Décomposition R via sommes hybrides | [PROUVÉ] |
| |S_i^{(ℓ)}(t)| ≤ √p | [PROUVÉ] |
| Σ_t |S_i^{(ℓ)}|² = rp | [PROUVÉ] |
| T4 conditionnel (r > √p) | [PARTIELLEMENT PROUVÉ] |
| T4 inconditionnel | [BLOQUÉ — gap L²/L^∞] |
| T5 (orbitale) | [HEURISTIQUE] |

---

## 8. CE QUI A ÉTÉ APPRIS

### Résultats positifs
1. La formule exacte N_0(p) = (C/r^k)·N_H(0) + R est un cadre de travail DÉFINITIF
2. Le spectre plat des poids est un résultat NÉGATIF utile (élimine toute tentative de lissage)
3. Le lifting des caractères de H vers F_p* fonctionne proprement (5 étapes formalisées)
4. Le moment L² donne RMS = √r — la borne √p est lâche d'un facteur connu
5. La structure orbitale ∏ S_i = ∏ S_0(t·3^j) est une réduction à une seule variable

### Connexions à la littérature
- Bourgain-Glibichuk-Konyagin (2006): applicable mais quantitativement insuffisant
- Bourgain multilinéaire (GAFA 2009): cadre correct mais phases exponentielles hors domaine
- Tao (2011): confirme que la réduction Collatz → sous-groupes est connue; barrières identifiées
- Konyagin-Shparlinski (1999): référence fondamentale pour sommes avec phases exponentielles
- Cochrane-Hart-Pinner-Spencer (2014): Waring sur sous-groupes

### Barrières identifiées
- Le passage L² → L^∞ pour S_i^{(ℓ)} est le verrou technique
- La condition ord_p(2) > √p est nécessaire dans la preuve actuelle
- Les outils de découplement (BDG) ne s'appliquent pas aux phases exponentielles 2^b

---

## 9. CE QUI A ÉTÉ FERMÉ UTILEMENT

| Piste | Statut | Raison |
|-------|--------|--------|
| G1 (Méta-certification CRT) | [ÉLIMINÉ] | Redondant R34/R35 |
| G2 (Compression DP) | [ÉLIMINÉ] | Impact 3/10, redondant R84 |
| T1 (Bourgain sum-product direct) | [ÉLIMINÉ] | Redondant R73 (circulaire) |
| T2 (Trace functions FKM) | [REFORMULÉ → T2-bis] | 2^b non algébrique → obstruction sheaf |
| T3 (Smooth Weight Lemma) | [RÉFUTÉ] | Spectre plat: |Ŵ(ℓ)| = |Ŵ(0)| exactement |
| T5 (Equidist. orbitale) | [SUSPENDU] | Heuristique, pas assez mûr |
| Axe 1 entier | [FERMÉ] | Aucun candidat non-redondant |

---

## 10. CE QUI EST ENTERRÉ DÉFINITIVEMENT

1. **Toute tentative de lissage par Fourier des poids W(b)**: le spectre est PLAT par structure (support sur une unique classe mod r). C'est un théorème, pas une limitation technique.

2. **L'Axe 1 (fermeture computationnelle) comme programme théorique**: les candidats sont tous redondants. La méthode R84 est k-par-k par nature.

3. **Bourgain sum-product comme outil direct pour le produit**: circulaire (R73), et quantitativement insuffisant (ε ≈ 0.011 vs besoin ε > 1/k).

---

## 11. CONDITION DE NON-BOUCLE POUR LA SUITE

Pour éviter de refaire le même travail:

1. **Ne PAS re-tenter le lissage des poids** — le spectre est PROUVÉ plat
2. **Ne PAS re-tenter BGK quantitatif pour k < 91** — la borne ε ≈ 0.011 est l'état de l'art
3. **Ne PAS relancer l'Axe 1** — entièrement redondant
4. **Concentrer les efforts sur**: lever la condition r > √p dans T4, soit par:
   - (a) Moments supérieurs de S_0^{(ℓ)} le long d'orbites de ⟨3⟩ (direction T5)
   - (b) Bornes sur le 4ème moment Σ_t |S_i|^4 exploitant la structure sous-groupe
   - (c) Résultats type Katz sur les corrélations de sommes de Gauss

---

## 12. REGISTRE FAIL-CLOSED FINAL

| Objet | Statut |
|-------|--------|
| Relation N_0(p) = (C/r^k)·N_H(0) + R | [OBJET RÉEL] |
| Spectre plat Ŵ | [OBJET RÉEL] — résultat négatif prouvé |
| T4 conditionnel | [PARTIELLEMENT PROUVÉ] |
| T4 inconditionnel | [BLOQUÉ] |
| T5 orbitale | [HEURISTIQUE] |
| Moment L² = rp | [OBJET RÉEL] — identité prouvée |
| Structure orbitale | [OBJET RÉEL] — identité prouvée |
| G1, G2 | [REDONDANT] |
| T1 | [REDONDANT] |
| T3 (SWL) | [RÉFUTÉ] |

### Évaluation IVS (Information Value Score)
- Précision des objets: 9/10 (formules exactes, pas d'approximation)
- Qualité des candidats: 7/10 (un seul survivant avec preuve conditionnelle)
- Anti-redondance: 9/10 (tous les candidats vérifiés contre la carte)
- Qualité du pipeline autonome: 8/10 (5 rounds structurés, pas de dérive)
- Honnêteté de la décision finale: 9/10 (condition clairement identifiée, pas de faux triomphe)

**Score global IVS: 8.4/10**

---

## RÉSUMÉ POUR LA FENÊTRE

**Campagne R89→R93**: 5 rounds, 8 candidats testés, 6 éliminés, 1 réfuté, 1 survivant.

**Survivant**: T4 "Anticorrélation des phases hybrides" — Σ_{Z_H} χ_ℓ(∏h_i) = o(N_H(0))
conditionnellement à ord_p(2) > √p. Preuve en 5 étapes formalisées. Test k=21 passé.

**Progrès structurel**: N_0(p) = (C/r^k)·N_H(0) + R (cadre exact).
Spectre plat (résultat négatif prouvé). RMS = √r ≠ √p (gap L²/L^∞ quantifié).

**Prochaine direction**: Lever la condition r > √p via moments supérieurs ou structure orbitale de ⟨3⟩.
