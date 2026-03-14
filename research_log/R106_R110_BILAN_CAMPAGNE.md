# BILAN CAMPAGNE R106→R110

**Date** : 14 mars 2026
**Durée** : 5 rounds (R106–R110)
**Mandat** : Front resserré sur (H_k) — énergie additive k-linéaire des sous-groupes multiplicatifs de F_p*
**Protocole** : fail-closed, anti-rebranding, anti-k-par-k, anti-computationnel, binômes Investigation/Innovation

---

## SCORE IVS : 6.5 / 10

| Critère | Score | Justification |
|---------|-------|---------------|
| Théorèmes prouvés | 7/10 | T166 [PROUVÉ INCONDITIONNEL] |
| Routes nouvelles | 7/10 | Gowers U^{k-1}, BGK effectif, cohomologie — 3 routes viables |
| Avancée sur verrou | 5/10 | 2-point résolu, k-point reformulé mais OUVERT |
| Rigueur/anti-régression | 8/10 | T163 redécouverte détectée et corrigée (R109) |
| Éliminations utiles | 7/10 | 4 voies mortes confirmées (VdC, induction, Hölder prop., H-inv 3∉H) |

---

## THÉORÈMES

| ID | Énoncé | Statut | Round |
|----|--------|--------|-------|
| T166 | E_γ(H) = r^4/p + O(r^{3-η}) pour γ ∈ F_p*, H sous-groupe mult. | **PROUVÉ** | R108 |

**Preuve de T166** : Fourier → Cauchy-Schwarz → bijection t↔γt → BKT sur E(H).

---

## ROUTES IDENTIFIÉES

### 1. Gowers U^{k-1} sur Z_g [CANDIDAT PRINCIPAL — mordance 6/10]
- (H_k) pour 3∉H ⟺ uniformité de ψ = |f̂|² le long de PA dans Z_g
- Condition : ||ψ - Eψ||_{U^{k-1}} petit
- Calcul explicite pour k=3 montre faisabilité sous Katz-Sarnak
- Sous-verrou : bornes effectives sur corrélation de Gauss décalée Σ_j τ_j \overline{τ_{j+s}}
- Connexion : monodromie de Katz (Exponential Sums and Differential Equations)

### 2. BGK effectif [V_BGK_eff — mordance 5/10]
- Condition : ε(2/k) ≥ 1/(2(k-1))
- ε(δ) explicite n'existe PAS dans la littérature pour δ < 1/2
- Conjecturé : ε(δ) ≥ δ/4 suffirait pour tout k ≥ 3

### 3. Route cohomologique [mordance 4/10]
- Décomposition S_0 en sommes de Gauss complètes
- Faisceau non-standard de Katz, rang naïf g^{k-1}
- Rang effectif g^{(k-1)/2} conjectural

### 4. Interpolation A+B [mordance 3/10]
- E_k ≤ M^{2k-2s} · E_s (Fourier pour M, cohomologie pour E_s)
- Marche pour k grand, insuffisant pour k petit

---

## VOIES ÉLIMINÉES (cette campagne)

| Voie | Raison | Round |
|------|--------|-------|
| VdC sur W_ℓ | Dual à E_k par Cauchy-Schwarz, même obstruction | R106 |
| Induction E_k → E_{k-1} | Circulaire — borne sup donne trivial | R106 |
| Propagation T166 → (H_k) par Hölder | Structurellement insuffisant — perd corrélation | R108 |
| H-invariance pour 3∉H | α_j ∉ H, f̂ NON constante sur shifts — = T163 déjà connu | R109 |

---

## ÉTAT DU FRONT

```
AVANT R106                          APRÈS R110
─────────                           ──────────
T4 : r > p^{1/2+2/k}               T4 : r > p^{1/2+2/k}  (inchangé)
T164 : r > p^{2/k} sous (H_k)      T164 : r > p^{2/k} sous (H_k)  (inchangé)
(H_k) : OUVERT k≥3                 (H_k) : OUVERT k≥3  (reformulé)
                                    T166 : décorrélation 2-point PROUVÉE
                                    (H_k) = uniformité Gowers de |f̂|² sur Z_g
                                    3 routes viables identifiées
```

**Verrou résiduel exact** : V_GOWERS — prouver la petitesse de ||ψ - Eψ||_{U^{k-1}}
sur Z_g pour ψ = |f̂|² (module carré de somme exponentielle sur sous-groupe).

---

## RECOMMANDATIONS POUR R111+

1. **Priorité 1** : Attaquer V_GOWERS via les corrélations de Gauss décalées
   - Calculer Σ_j τ_j \overline{τ_{j+s}} explicitement
   - Utiliser la théorie de monodromie de Katz pour les bornes
   - Cas test : k=3 (norme U², le plus accessible)

2. **Priorité 2** : Chercher dans la littérature de Shkredov/Schoen des bornes
   directes sur T_k(A) pour A sous-groupe multiplicatif (même si c'est T_k(H)
   seulement pour 3∈H, les techniques pourraient s'adapter au cas croisé)

3. **Ne PAS faire** :
   - Ressusciter les voies mortes (VdC, induction, Hölder prop.)
   - Chercher ε(δ) explicite dans BGK (problème ouvert, hors scope)
   - Travailler sur 3∈H (route fermée R102)

---

## FICHIERS

- `R106_R110_WORKING.md` : fichier de travail complet (R106→R110)
- `R106_R110_BILAN_CAMPAGNE.md` : ce fichier
