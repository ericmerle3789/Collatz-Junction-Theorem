# AUDIT V9 — MISE EN COHÉRENCE DE PORTÉE

**Date** : 2026-07-25 · **Contexte** : relecture externe déclenchée par la collaboration Macindoe.
**Méthode** : A.R.E.S. — aucune assertion sans vérification machine ou citation interne du dépôt.

---

## 1. Constat : incohérence interne du dépôt

| Document | Ce qu'il affirmait | Statut |
|---|---|---|
| `docs/PROOF_ASSEMBLY.md` §2 | Deux chemins, **prouvés k = 3..200**, chacun avec un **gap nommé** au-delà | ✅ honnête |
| `paper/preprint_en.tex` | *« complete exclusion of cycles further requires Hypothesis (H) for k ≥ 69 »* | ✅ honnête |
| `audits/AUDIT_V8_RESULTS.md` 1.3a/1.3b | distingue explicitement non-surjectivité ≠ exclusion de cycles | ✅ honnête |
| `README.md` (avant ce jour) | *« Theorem (Unconditional): for every k ≥ 3, no non-trivial positive cycle »* | ❌ **surclamait** |
| `STATUS.md` (avant ce jour) | *« PROUVÉ INCONDITIONNELLEMENT »* sans la clause de portée | ❌ **ambigu** |

**Le fond du dépôt était juste ; sa vitrine dépassait son fond.** C'est la vitrine qui a été corrigée.

## 2. Vérification indépendante effectuée

- **Définition reproduite** (canari) : `corrSum(A_min)` avec `A_min = [0..k-1]` donne bien `3^k − 2^k`, pour k = 1..11. La définition employée ici est donc celle du dépôt.
- **Claim « range < d » testé** sur l'ensemble de **toutes** les compositions, k = 3..12 : le rapport `range/d` mesuré vaut **6 à 372**, croissant — donc `range < d` est **faux** sur cet ensemble. Le claim ne peut porter que sur un sous-ensemble restreint (compositions monotones + contraintes de taille), ce que `PROOF_ASSEMBLY.md` §3 précise. **Aucune erreur mathématique n'est imputée au dépôt sur ce point** : c'est la formulation abrégée du README qui prêtait à confusion.
- Script : `experiments/test_REQ-MATH-038` (dépôt `one-obstruction-three-faces-lean`).

## 3. Corrections appliquées ce jour

1. `README.md` — titre, bandeau de portée, énoncé principal ramené à **3 ≤ k ≤ 200**, tableau de preuve refait avec le statut réel de chaque tranche (`native_decide` = compilateur, pas noyau ; k > 50000 = **OPEN**), et mention explicite : *ce dépôt ne prouve pas la conjecture*.
2. `STATUS.md` — même mise en cohérence, avec l'encadré « ce que ce théorème n'est pas ».

## 4. Corrections listées mais TOUJOURS NON FAITES (héritées de STATUS.md, mars 2026)

- [ ] **CRITIQUE** Theorem Q — condition 2 affirmée « tous » alors que 8/83 vérifient
- [ ] **MAJEUR** comptage « 73 théorèmes » → 65 réels
- [ ] **MAJEUR** bug Nat underflow dans `parseval_cost_q3` → théorème vacueux
- [ ] **MINEUR** Prop. 6.5 à marquer comme sketch ; redondance Lean

Ces points restent ouverts et doivent être traités avant toute soumission.

## 5. Ce que le dépôt apporte réellement (et c'est réel)

Le **déficit d'entropie** `log₂ d − log₂ C ≥ (S−1)·γ`, avec `γ = 1 − h(1/log₂3)`, est démontré et
partiellement formalisé. Vérifié le 2026-07-25 : **`γ · log₂3 = c_gen` exactement** (écart 0 à 50
décimales), où `c_gen` est la constante de comptage indépendamment obtenue côté Macindoe. C'est la
brique manquante de l'entrée L-A7 du carnet commun. **La valeur de ce dépôt est là — un lemme
prouvé et réutilisable — pas dans une preuve de la conjecture.**
