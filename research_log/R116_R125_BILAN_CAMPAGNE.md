# BILAN CAMPAGNE R116→R125

**Date** : 14 mars 2026
**Durée** : 10 rounds (R116–R125)
**Mandat** : Le mur V_SQRT_CANCEL est-il fondamental ou local aux outils ?
**Protocole** : PROTOCOLE INTÉGRAL DE RECHERCHE appliqué strictement

---

## SCORE IVS : 6.0 / 10

| Critère | Score | Justification |
|---------|-------|---------------|
| Théorèmes prouvés | 5/10 | T170 (partiel), identités exactes |
| Routes nouvelles | 3/10 | Géo. algébrique tentée mais dimension 0 bloque |
| Avancée sur verrou | 6/10 | Réponse §9.5 : mur FONDAMENTAL (résiste à 3 familles) |
| Rigueur/protocole | 9/10 | Anti-computationnel appliqué (R121), suspension honnête (R123) |
| Éliminations utiles | 7/10 | Deligne dim 0, faisceau Z_g, L-fonction tore, computationnel |

---

## RÉSULTAT PRINCIPAL

**Réponse au §9.5 du protocole** : Le mur V_SQRT_CANCEL est **FONDAMENTAL**.

Il résiste à TROIS familles d'outils indépendantes :
1. Analyse de Fourier + BKT (R106-R114)
2. Géométrie algébrique / Deligne RH (R116-R119)
3. Positivité + T166 (R122)

**Raison profonde** : L'ensemble H+1 = {1+ζ : ζ^r = 1} est de dimension 0.
Les outils cohomologiques (Weil, Deligne, Katz) ne donnent pas d'annulation
sur des ensembles finis de points.

---

## THÉORÈME PROUVÉ

**T170** [PROUVÉ, conditionnel sur s₃|k] :
Si s₃ = ord_{Z_g}(3) ≤ k^{1/2}, alors E_k satisfait une borne améliorée :
condition r > p^{(k/s₃ - 2)/(2k - s₃ - 1)}, meilleure que T4.
- Pour k=22, s₃=2 : r > p^{0.244} (vs T4 : p^{0.591})
- Inapplicable pour k premier (s₃ = k)

---

## VOIES ÉLIMINÉES

| Voie | Raison | Round |
|------|--------|-------|
| Deligne RH sur V_s (somme directe) | Borne triviale (pas d'annulation) | R117 |
| Weil sur racines de P(y) | Dimension 0, pas de borne non-triviale | R118 |
| L-fonction sur μ_r | Dimension 0 encore | R119 |
| Computationnel sur d(k) | Nombres exponentiellement grands, §2.1 | R121 |
| Positivité + L^∞/L^2 | Seuil p^{1/2} infranchissable | R122 |

---

## DÉCISION STRATÉGIQUE

**SUSPENSION** de la piste (H_k) directe (§9.6d du protocole).

**Justification** :
- 44 rounds d'investigation (R81-R125)
- 3 familles d'outils épuisées
- Mur identifié comme problème ouvert de TAN
- Aucun progrès possible avec les méthodes connues dans le régime r ≪ √p

**Options futures** :
- A : Publier la chaîne conditionnelle (T4→T164→(H_k)→S_H(s))
- C : Katz-Sarnak effectif + crible (long terme, faisabilité 3/10)

---

## FICHIERS

- `R116_R125_WORKING.md` : fichier de travail complet
- `R116_R125_BILAN_CAMPAGNE.md` : ce fichier
