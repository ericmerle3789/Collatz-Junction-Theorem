# R153 — CAMPAGNE PISTES ORBITALES (ÉVITEMENT + PHASE)

**Date** : 15 mars 2026
**Type** : X/I/P
**Protocole** : PromptR153.md exécuté intégralement (4 agents parallèles)
**Campagne précédente** : R152 (IVS 2.5/10, SUSPENSION CONDITIONNELLE, monodromie KMS unique survivant)

---

## RÉSUMÉ EXÉCUTIF

Campagne testant deux pistes d'attaque collective du verrou (vs borne pointwise) :
- **Piste A** : Évitement orbital des s exceptionnels
- **Piste B** : Désalignement de phase orbitale

**Résultat** : Les deux pistes sont respectivement **CIRCULAIRE** (Piste A se réduit à la borne pointwise) et **REDONDANTE** (Piste B = T4+T5+HGE sous autre nom). Deux candidats concrets proposés par l'Innovateur ont des formulations spécifiques nouvelles mais ne passent pas le filtre fail-closed.

**Verdict** : SUSPENSION CONFIRMÉE. Les conditions de R152 (calcul de monodromie) restent non satisfaites.

---

# PHASE 1 — RECALAGE (Agent 1)

## Le changement de niveau d'attaque

| Avant (R1-R151) | Maintenant (R153) |
|------------------|-------------------|
| Borner \|S_H(s)\| ≤ √r pour TOUT s | Borner \|Σ_s R(s)\| sans contrôle pointwise |
| Borne individuelle → produit | Organisation collective → somme |

Ce changement est un VRAI changement de niveau. Le problème passe du pointwise au collectif.

## Analyse des manques

### Piste A — Évitement orbital

**Manque visé** : la disposition spatiale des s "mauvais" par rapport aux orbites de ⟨3⟩ dans Z/(p-1)Z.

**Sous-verrou identifié** : Pour qu'une orbite {s, 3s, ..., 3^{k-1}s} produise |R(s)| grand, CHACUN des k points doit avoir |S_H(s·3^j)| significatif. Si au moins un point de l'orbite évite les mauvais s, le produit R(s) est écrasé.

**Heuristique favorable** : Par T166 + Markov, le nombre de mauvais s (|S_H(s)|² > αr) est ≤ rp/α. La proportion de mauvais s parmi (p-1) est ≈ r/(α). Pour r ≈ log p et α modéré, la probabilité qu'une orbite de longueur k ≈ log p / log 3 soit entièrement contenue dans les mauvais s est ≈ (r/α)^k → 0 exponentiellement.

**MAIS (point critique Agent 4)** : Pour que Σ R(s) soit petit, il faut que TOUTES les orbites évitent les mauvais s. Or il faut la proportion de mauvais s < 1/k pour garantir cela, ce qui REVIENT à la borne pointwise.

### Piste B — Désalignement de phase

**Manque visé** : les arguments arg(S_H(s)) ne sont jamais contrôlés — seuls les modules le sont (T166).

**Sous-verrou identifié** : Les phases arg(R(s)) = Σ_j arg(S_H(s·3^j)) sont-elles équidistribuées?

**MAIS (point critique Agent 4)** : C'est exactement ce que T4 (R89-R93) prouve conditionnellement à ord_p(2) > √p. La "signature de phase" est T4 sous un autre nom, avec le même obstacle (régime r ≈ log p).

## Recommandation Agent 1

Piste A plus prometteuse (sous-verrou distinct) que Piste B (risque élevé de circularité). Mais Agent 1 reconnaît que la formalisation de Piste A est difficile.

---

# PHASE 2 — FABRICATION D'OBJETS (Agent 2)

## Candidat A1 : Concentration orbitale via moment 4

### Objet

Moyenne orbitale : μ(O) = (1/|O|) Σ_{t∈O} |S_H(t)|²

Pour chaque orbite O de ⟨3⟩ dans (Z/rZ)*, on mesure la masse L² portée par l'orbite.

### Lemme candidat A1

Par T166 + Parseval :
- Σ_O |O|·μ(O) = r(p-1)  (contrainte de masse totale)
- Le nombre d'orbites O avec μ(O) > αr est ≤ φ(r)/(g₃·α)

Pour toute orbite "normale" (μ(O) ≤ αr) :
|R(s)| ≤ (αr)^{k/2} pour s ∈ O

### Critère de réfutation

Calculer la variance inter-orbitale V = (1/N_orb) Σ_O (μ(O) - r)².
- Si V = o(r²) : le découpage est vide, lemme trivial → **RÉFUTÉ**
- Si V = Θ(r²) : le lemme a du mordant

### Gain opératoire explicite

Découpe Σ R(s) en orbites chargées (≤ p/β) vs normales. Les normales contribuent ≤ (p/g₃)·(αr)^{k/2}.

---

## Candidat B1 : Rapport de cohérence δ

### Objet

Rapport de cohérence : δ = |Σ_s R(s)| / Σ_s |R(s)| ∈ [0,1]

C'est le rapport entre la somme vectorielle (avec phases) et la somme des modules.

### Lemme candidat B1

Si les phases Φ(s) = Σ_j arg(S_H(s·3^j)) sont ε-indépendantes :
δ² ≤ 1/k + ε, donc |Σ R(s)| ≤ (Σ |R(s)|)/√k

### Critère de réfutation

Calculer δ(p) numériquement pour p < 10⁶.
- Si δ(p) → 0 : B1 tient
- Si δ(p) > 0.5 pour infiniment de p : **RÉFUTÉ**

### Synergie A1+B1

A1 contrôle les modules par orbite, B1 contrôle la somme pondérée par phases. Attaque combinée potentielle.

---

# PHASE 3 — AUDIT CROISÉ (Agents 3 + 4)

## Audit du Candidat A1

### Agent 3 — Non-redondance

**Énergie orbitale = T166?** Non exactement. T166 donne le moment 4 GLOBAL (Σ_s |S_H(s)|⁴). Le candidat A1 le DÉCOMPOSE PAR ORBITE de ⟨3⟩. Cette décomposition est techniquement DISTINCTE de T166 elle-même.

**Évitement orbital = T170?** Non exactement. T170 utilise la PÉRIODICITÉ de l'orbite (s₃|k). A1 utilise la DISTRIBUTION DES MODULES le long de l'orbite. Ce sont des propriétés différentes.

**Verdict Agent 3** : L'objet μ(O) est techniquement distinct des objets existants. MAIS la question "V = o(r²) ou Θ(r²)?" est un calcul non effectué. Sans ce calcul, on ne sait pas si le lemme est trivial.

### Agent 4 — Fail-closed

**Test de circularité** : L'argument "un seul s mauvais sur l'orbite contamine R(s)" est DÉVASTATEUR. Pour que Σ R(s) soit petit via l'évitement, il faut que PRESQUE TOUTES les orbites évitent les mauvais s. La proportion de mauvais s nécessaire (< 1/k) est précisément ce que la borne pointwise donnerait.

**Verdict Agent 4** : **[ÉLIMINÉ — circularité type 1]**. Le découpage en orbites chargées/normales est un objet réel (distinct de T166 seul), mais le GAIN OPÉRATOIRE est circulaire car contrôler les orbites chargées requiert la borne pointwise.

### Verdict consolidé A1

**[SEMI-RÉEL]** — L'objet μ(O) et la variance V sont des quantités bien définies et techniquement nouvelles (décomposition orbitale de T166). Mais l'exploitation pour N₀(p)=0 est circulaire.

**Motif de mort** : La contamination d'une orbite par un SEUL mauvais s écrase le gain du découpage. Le passage "peu d'orbites chargées → Σ R(s) petit" nécessite TOUTES les orbites normales, ce qui revient au pointwise.

---

## Audit du Candidat B1

### Agent 3 — Non-redondance

**Rapport δ = T4?** OUI. Le rapport de cohérence δ = |Σ R(s)|/Σ|R(s)| est EXACTEMENT ce que T4 (R89-R93) cherche à contrôler. T4 prouve conditionnellement (sous ord_p(2) > √p) que la somme s'annule par oscillation de phase. Le "désalignement de phase" EST la description de T4.

**Phase cancellation = R56?** PARTIELLEMENT. La "phase cancellation 89%" de R56 porte sur V_cross (variance inter-tranches), pas sur le produit R(s). Mais le MÉCANISME est le même : interférence destructive par rotation des phases.

**Verdict Agent 3** : **[REDONDANT]** avec T4+T5+HGE (R89-R98). L'obstacle est identique : régime r ≈ log p.

### Agent 4 — Fail-closed

**Test de redondance** : Le rapport δ est un objet mesurable bien défini, mais sa formulation comme "nouveau" candidat ignore que T4 a DÉJÀ prouvé conditionnellement que δ → 0 sous ord_p(2) > √p. La condition est non satisfaite dans notre régime. Le "test de réfutation" (calculer δ numériquement) est du computationnel exploratoire, pas un argument de preuve.

**Verdict Agent 4** : **[REDONDANT — T4/T5/HGE (R89-R98)]**

### Verdict consolidé B1

**[REDONDANT]** — Le rapport δ est T4 reformulé. L'obstacle fondamental (équidistribution des phases dans le régime r ≈ log p) est inchangé depuis R92.

**Motif de mort** : Le "désalignement de phase" est la DESCRIPTION du phénomène que T4 prouve conditionnellement. Prouver inconditionnellement l'équidistribution des phases est le verrou T5/HGE, ouvert depuis R92-R98.

---

# PHASE 4 — TOURNOI ET DÉCISION (Agent 4)

## Registre FAIL-CLOSED final

| Candidat | Verdict | Motif |
|----------|---------|-------|
| Piste A (évitement orbital) | **[ÉLIMINÉ]** | Circularité : se réduit à la borne pointwise |
| Candidat A1 (μ(O) orbitale) | **[SEMI-RÉEL]** | Objet distinct (décomp. orbitale de T166) mais exploitation circulaire |
| Piste B (signature de phase) | **[REDONDANT]** | = T4+T5+HGE (R89-R98) |
| Candidat B1 (rapport δ) | **[REDONDANT]** | = T4 reformulé, même obstacle |

## Survivants

**AUCUN.** Les deux pistes ne passent pas le filtre fail-closed.

## Confrontation avec R152

Les conditions de non-boucle de R152 restent NON SATISFAITES :
1. ❌ G_geom du faisceau {S_H(s)} non calculé
2. ❌ Lemme d'évitement quantitatif non formulé (circulaire en l'état)
3. ❌ Borne quantitative régime r ≈ log p non obtenue

---

# CHECKPOINT OBLIGATOIRE

| Question | Réponse |
|----------|---------|
| 1. Piste avec objet le plus nouveau? | **A1** (μ(O) = décomposition orbitale de T166) — objet réel mais inexploitable |
| 2. Piste changeant le plus la capacité d'attaque? | **Aucune** — A circulaire, B redondante |
| 3. Candidat réellement mordant? | **Aucun** dans l'état |
| 4. Candidat à tuer? | **B1** (redondant avec T4). A1 archivé comme objet réel [SEMI-RÉEL] |
| 5. Prochain round légitime? | **NON** sans calcul de monodromie (R152) |
| 6. Condition de non-boucle? | Inchangée depuis R152 : G_geom d'abord |

---

# INFORMATION NOUVELLE (R153)

## Résultat négatif principal

**La stratégie "attaque collective vs pointwise" se RÉDUIT au pointwise pour le produit corrélé.**

Le produit R(s) = ∏_j S_H(s·3^j) est multiplicatif : un seul facteur petit écrase le produit, un seul facteur grand le contamine. Cette multiplicativité fait que :
- L'évitement orbital nécessite que TOUTES les orbites soient normales → proportion de mauvais s < 1/k → borne pointwise
- Le désalignement de phase est exactement T4 (anticorrélation des phases le long de l'orbite)

**Leçon** : Pour le produit corrélé, il n'y a PAS d'écart entre "attaque collective" et "borne pointwise". Les deux sont équivalentes car le produit est ultrasensible à chaque facteur.

## Objet archivé

**μ(O) = moyenne orbitale L² par orbite de ⟨3⟩** : objet bien défini, techniquement distinct de T166 globale. Variance inter-orbitale V non calculée. [SEMI-RÉEL, archivé, non exploitable en l'état]

---

# NOUVELLES VOIES MORTES (R153)

| Voie | Raison | Round |
|------|--------|-------|
| Évitement orbital des s exceptionnels (piste directe) | Circulaire : se réduit à borne pointwise (un mauvais s contamine le produit) | R153 |
| Signature de phase orbitale / désalignement | = T4+T5+HGE (R89-R98), même obstacle (r ≈ log p) | R153 |
| Attaque collective vs pointwise pour le produit corrélé | Équivalentes (multiplicativité du produit) | R153 |

---

# BILAN

| Métrique | Valeur |
|----------|--------|
| Candidats proposés | 2 (A1, B1) |
| Éliminés/Redondants | 2 |
| Survivants | 0 |
| Nouvelles voies mortes | 3 |
| Résultat négatif principal | Collectif ≡ pointwise pour produit multiplicatif |
| Objet archivé | 1 (μ(O) orbitale, [SEMI-RÉEL]) |
| IVS | **2.0/10** |

---

# DÉCISION STRATÉGIQUE

**SUSPENSION CONFIRMÉE (3ème confirmation : R141, R151, R152, R153).**

La leçon de R153 renforce R152 : le produit corrélé ∏ S_H(s·3^j) est intrinsèquement ultrasensible à chaque facteur, ce qui rend toute stratégie collective équivalente au pointwise. Le seul échappatoire identifié reste l'approche par monodromie (R152) — qui attaque la FAMILLE {S_H(s)}_s comme objet cohomologique plutôt que la somme Σ R(s) terme à terme.

**Mode actif** : PUBLICATION + calcul préparatoire G_geom.
