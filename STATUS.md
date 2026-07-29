# État du Projet — Collatz Junction Theorem

**Dernière mise à jour** : 7 mars 2026
**Auteur** : Eric Merle
**Repos** : [GitHub](https://github.com/ericmerle3789/Collatz-Junction-Theorem)

---

## Résultat principal

### Junction Theorem — PROUVÉ, mais ce qu'il prouve doit être dit exactement ✓

**Énoncé exact (inconditionnel).** Pour tout k ≥ 2, au moins l'une des deux obstructions s'applique :
- **Computationnelle** (Simons-de Weger 2005) : k ≤ 67 vérifié par DP exhaustif
- **Entropique** (Merle 2026) : k ≥ 18, C(k) < d(k)

Couverture des obstructions : [2,67] ∪ [18,∞) = [2,∞) — aucun gap logique **dans la disjonction**.

> ⚠️ **CE QUE CE THÉORÈME N'EST PAS.** « Une obstruction s'applique » n'est **pas**
> « aucun cycle n'existe ». La non-surjectivité de Ev_d dit que la carte **rate un résidu** ;
> elle ne dit pas qu'elle **rate le résidu 0**. Le préprint l'écrit lui-même : *« the complete
> exclusion of cycles further requires Hypothesis (H) for k ≥ 69 »* (Remark `junction-scope`),
> et l'audit V8 le confirme (checks 1.3a et 1.3b). **Non-existence des cycles : PROUVÉE pour
> 3 ≤ k ≤ 200 seulement** ; au-delà, deux programmes asymptotiques avec gaps nommés
> (`docs/PROOF_ASSEMBLY.md` §2). **Ce dépôt ne prouve pas la conjecture de Collatz.**

### Blocking Mechanism — PROUVÉ SOUS GRH

4-case induction sur l'automate Horner mod d.
Gap résiduel G2c = variante d'Artin pour la famille d = 2^S - 3^k.
Résolu sous GRH via Hooley (1967).

---

## Formalisation Lean 4

| Composante | Théorèmes | Sorry | Axioms | Lean version |
|---|---|---|---|---|
| `lean/verified/` (Core) | 65 | 0 | 0 | 4.15.0 |
| `lean/skeleton/` (Mathlib) | ~60 | 1 (ingénierie) | 2 (SdW, CF) | 4.29.0-rc2 |

CI configuré : `.github/workflows/lean-check.yml`

---

## Corrections requises avant publication

- [ ] **CRITIQUE** : Theorem Q — condition 2 affirmée "tous" mais seulement 8/83 vérifient → retirer ou reformuler (`paper/preprint_en.tex`)
- [ ] **MAJEUR** : Comptage "73 théorèmes" → 65 réels → corriger dans README + preprint
- [ ] **MAJEUR** : Bug Nat underflow dans `parseval_cost_q3` → théorème vacueux (`lean/verified/CollatzVerified/Basic.lean`)
- [ ] **MINEUR** : Proposition 6.5 (Conjecture M ⟹ H) → marquer honnêtement comme sketch
- [ ] **MINEUR** : Redondance Lean (zero_exclusion ×4) → nettoyer

---

## Audits de certification

| Audit | Fichier | Contenu |
|---|---|---|
| V1 | `audits/AUDIT_V1_CERTIFICATION.md` | Certification initiale |
| V2 | `audits/AUDIT_V2_CERTIFICATION.md` | Certification v2 |
| V3 | `audits/AUDIT_V3_CERTIFICATION.md` | Certification v3 |
| V4 | `audits/AUDIT_V4_MATHEMATIQUE.md` | Audit mathématique |
| V5 | `audits/AUDIT_V5_APEX1.md` | Audit APEX1 complet |
| V6 | `audits/AUDIT_V6_DEEP_DIVE.md` | Deep dive 2026 |
| V7 | `audits/AUDIT_V7_PHASE23_REVIEW.md` | Review finale Phase 23 |

---

## Projet frère

Voir `SISTER_PROJECT.md` — **collatz-nocycle-lean4** (approche complémentaire).

---

## Publication

**Plateforme cible** : arXiv.org (math.NT, math.CO)
**Journal cible** : Acta Arithmetica ou Journal of Number Theory
**État** : Prêt après corrections ci-dessus
**Preprint** : `paper/preprint_en.tex` (anglais), `paper/preprint_fr.tex` (français)
**PDF** : `paper/Merle_2026_Barrieres_Entropiques_Collatz.pdf`

---

## Lien Artin

Le Blocking Mechanism sans GRH se réduit à une variante de la conjecture d'Artin
(primitive roots) pour la famille {2^S - 3^k}. Synthèse complète dans
`research_protocol/artin_synthesis_FINAL_10f26.md`.
