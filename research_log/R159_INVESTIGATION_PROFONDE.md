# R159 — INVESTIGATION PROFONDE : 4 AXES SIMULTANÉS

**Date** : 15 mars 2026
**Type** : Investigation post-doctorale — 4 agents parallèles
**Fronts** : (1) Rigidité Furstenberg ×2×3, (2) Méthodes non-moment, (3) Monodromie géométrique (calcul), (4) Extension DP
**Contexte** : 158 rounds, 174 théorèmes, 198+ voies mortes. Seule direction non épuisée : monodromie géométrique (R152). Deux axes pragmatiques ajoutés.

---

## ARCHITECTURE DE L'INVESTIGATION

```
┌─────────────────────────────────────────────────┐
│              R159 — 4 AXES PARALLÈLES            │
├─────────────────────────────────────────────────┤
│                                                  │
│  Agent 1: FURSTENBERG ×2×3                       │
│  → Analogue corps fini de la rigidité ×2×3       │
│  → Connexion HGE/T4 inconditionnel               │
│  → Recherche littérature récente                  │
│                                                  │
│  Agent 2: MÉTHODES NON-MOMENT                    │
│  → Burgess, Vinogradov, Stepanov, Deligne, Katz  │
│  → Quel est le gap exact pour |H|≈log p ?        │
│  → Résultats récents 2020-2026 ?                 │
│                                                  │
│  Agent 3: MONODROMIE (CALCUL)                    │
│  → Distribution de S_H(s) numériquement          │
│  → Sato-Tate ? Semicirculaire ? Uniforme ?       │
│  → Conjecturer G_geom                            │
│                                                  │
│  Agent 4: EXTENSION DP                           │
│  → Faisabilité k=22,23,... sur M1 Pro            │
│  → Factorisation d(k), taille état               │
│  → Réduire le gap 20→? valeurs                   │
│                                                  │
├─────────────────────────────────────────────────┤
│  AUDIT CROISÉ après retour des 4 agents          │
│  Kill switches, connexion au verrou, verdict      │
└─────────────────────────────────────────────────┘
```

---

## RÉSULTATS AGENTS

### Agent 1 : Rigidité Furstenberg ×2×3 — ✅ COMPLÉTÉ → [MORT]

**Verdict : MORT — 3 obstructions indépendantes, erreur de catégorie.**

#### Obstruction 1 : Barrière de taille BGK
La rigidité de Furstenberg (×2, ×3 sur R/Z) et ses analogues finis (Bourgain-Gamburd-Sarnak) nécessitent |H| ≥ p^δ pour un δ > 0. Notre sous-groupe H = ⟨2⟩ a |H| = r ≈ log p. C'est **exponentiellement trop petit**. Aucun théorème de rigidité connu ne descend à des sous-groupes de taille logarithmique.

#### Obstruction 2 : Rang multiplicatif
La rigidité ×2×3 exploite l'action conjointe de DEUX multiplicateurs indépendants sur un groupe compact. Dans F_p*, le groupe est **cyclique** (rang 1). L'action de ×2 et ×3 sont liées : 3 = 2^{log_2(3)}, et sur F_p*, 3 ≡ 2^j mod p pour un certain j. Il n'y a pas de "rang supérieur" exploitable — les deux actions sont commensurables dans le groupe cyclique.

#### Obstruction 3 : Absence d'analogue fini
Aucun résultat dans la littérature (Bourgain, Konyagin, Shparlinski, Katz, 2000-2026) ne fournit un analogue de la rigidité de Furstenberg pour des sous-groupes multiplicatifs de F_p*. Les résultats existants (somme-produit, croissance dans SL₂) concernent des ensembles arbitraires, pas des sous-groupes cycliques.

**Conclusion** : Erreur de catégorie. La rigidité dynamique continue (Furstenberg, Rudnick-Johnson) ne se transpose pas en structure algébrique finie. Les outils (mesures invariantes, entropie, joinings) n'ont pas de traduction pour H = ⟨2⟩ ⊂ F_p*.

### Agent 2 : Méthodes non-moment — ✅ COMPLÉTÉ → [TOUTES MORTES]

**Verdict : Les 7 méthodes non-moment connues échouent TOUTES pour |H| ≈ log p, et les échecs sont CATASTROPHIQUES (pas marginaux).**

#### Hiérarchie des barrières de taille

| Seuil | Méthodes | Notre position |
|-------|----------|----------------|
| p^{1/2} | Pólya-Vinogradov, Deligne (sommes complètes) | ❌ |
| p^{1/4} | Burgess, Stepanov, Heath-Brown-Konyagin | ❌ |
| p^δ (δ > 0 fixé) | BGK (somme-produit) | ❌ |
| p^{C/log log p} | Equidistribution effective (Katz/Chebotarev) | ❌ |
| **log p** | **NOTRE RÉGIME — sous TOUS les seuils connus** | ← |

#### Résultats par méthode

1. **Burgess** (1963) : [MORT] — nécessite |H| > p^{1/4+ε}. Gap exponentiel.
2. **Vinogradov amplification** : [MORT] — bilinéaire ramène à Burgess, même barrière p^{1/4}.
3. **Stepanov** (polynôme auxiliaire) : [MORT] — même seuil p^{1/4}, mécanisme algébrique différent.
4. **Deligne/Weil II** : [MORT] — borne les sommes COMPLÈTES sur F_p (donne √p, pas √r).
5. **Katz monodromie/équidistribution** : [MARGINAL] — donne la bonne moyenne mais pas le pointwise. Famille de taille log p insuffisante pour Chebotarev effectif.
6. **BGK somme-produit** : [MORT] — nécessite |H| ≥ p^δ pour δ > 0 FIXÉ. log p = p^{o(1)} est SOUS le seuil. Gap QUALITATIF (pas quantitatif).
7. **Grand crible** : [MOYENNE SEULEMENT] — donne E[|S_H|²] ≈ r (correct !), mais pas de borne pointwise. Gap √(log p) entre moyenne et max.

#### Le point crucial : gap QUALITATIF au seuil BGK
Le seuil p^δ de BGK n'est pas une limitation technique — il reflète un obstacle fondamental du phénomène somme-produit. Quand δ → 0, le saving ε(δ) → 0 et s'annule pour les sous-groupes de taille polylogarithmique. **Aucun article 2020-2026 ne descend sous ce seuil.**

#### Le seul espoir identifié
Le grand crible montre que |S_H(t)| a la bonne taille EN MOYENNE (∼ √r). Le problème est purement POINTWISE. Si la structure spécifique de H = ⟨2⟩ (pas un sous-groupe générique) pouvait être exploitée, cela nécessiterait un argument totalement nouveau.

**Références clés** : BGK (2006), Ostafe-Shparlinski-Voloch (2022), Kowalski (2024), Alsetri (2026), Katz-NMK (lectures), Chang (2003).

### Agent 3 : Monodromie géométrique (calcul) — ✅ COMPLÉTÉ

**Verdict : Distribution GAUSSIENNE COMPLEXE confirmée. max|S_H|/√r CROÎT (∼√log(p/r)). La borne stricte |S_H| ≤ √r est FAUSSE numériquement.**

#### Résultats numériques (30 premiers, r=13..79, index=10..630)

| Observations clés | Valeur |
|-------------------|--------|
| max|S_H|/√r minimum observé | 1.27 (p=151, r=15) |
| max|S_H|/√r maximum observé | **3.60** (p=2113, r=44) |
| Kurtosis (Gaussien=2.0) | 1.2 → 2.3 (converge vers 2) |
| E[|S_H|²/r] | → 1.0 (confirmé par orthogonalité) |

#### Interprétation

1. **Distribution** : S_H(t)/√r se comporte comme une variable Gaussienne complexe pour grand index (p-1)/r. La kurtosis converge vers 2.0.

2. **max|S_H|/√r CROÎT** : la croissance est compatible avec le maximum de ~(p-1)/r variables Gaussiennes indépendantes :
   - max/√r ∼ √(2 log((p-1)/r))
   - Pour p ∼ 2^r : max/√r ∼ √(2r) → **CROISSANCE en √r**

3. **Conséquence pour le verrou** : La borne |S_H(t)| ≤ C·√r pour une CONSTANTE C est plausible, mais |S_H| ≤ √r strictement est **FAUSSE** (numériquement réfuté). La borne attendue est plutôt :
   - max_t |S_H(t)| ∼ √(r · log p) ∼ r pour p ∼ 2^r

4. **G_geom conjecturé** : Le comportement Gaussien (kurtosis → 2, pas semicirculaire) suggère un groupe de monodromie géométrique GRAND (USp(2g) ou similaire), PAS SU(2) (qui donnerait Sato-Tate semicirculaire avec kurtosis → 1.5).

#### Impact sur le projet
La borne |S_H| ≤ √r est **TROP OPTIMISTE** pour notre régime. Le comportement réel est max|S_H| ∼ √(r log p) ∼ r. Cela signifie que le verrou V_SQRT_CANCEL est encore plus dur que prévu : même une borne |S_H| ≤ r^{1-ε} pour ε > 0 serait un résultat majeur.

### Agent 4 : Extension DP — ✅ COMPLÉTÉ

**Résultat majeur : 13/20 valeurs du gap sont prouvables par DP sur M1 Pro 16GB.**

#### Référence : k=21 (prouvé R84)
- d(21) = 33,587 × 200,063 (deux premiers, le plus grand = 200K)
- Mémoire : 1.6 MB, temps < 0.01 sec

#### Tiers de faisabilité

**Tier 1 — Trivialement faisable (6 valeurs, plus faciles que k=21) :**

| k | d(k) factorisation | plus grand premier | temps DP |
|---|---|---|---|
| 25 | 11 × 13 × 191 × 251 × 36,791 | 36,791 | 0.001 s |
| 34 | 5 × 71 × 3,607 × 14,303 × 73,013 | 73,013 | 0.003 s |
| 24 | 7 × 233 × 2,113 × 77,569 | 77,569 | 0.002 s |
| 30 | 7² × 13 × 19 × 67 × 499 × 186,793 | 186,793 | 0.006 s |
| 23 | 5 × 31,727 × 272,927 | 272,927 | 0.007 s |
| 26 | 5² × 149 × 991 × 502,829 | 502,829 | 0.013 s |

**Tier 1b — Faisable avec ressources modestes (7 valeurs, mém < 4 GB) :**

| k | plus grand premier | Mémoire | temps DP |
|---|---|---|---|
| 37 | 8,674,781 | 66 MB | 0.4 s |
| 40 | 10,119,313 | 77 MB | 0.4 s |
| 29 | 44,110,909 | 337 MB | 1.3 s |
| 36 | 84,026,491 | 641 MB | 3.1 s |
| 38 | 374,524,783 | 2.8 GB | 14 s |
| 22 | 425,525,537 | 3.2 GB | 9 s |
| 27 | 513,600,499 | 3.8 GB | 14 s |

**Tier 3 — Infaisable sur 16GB (7 valeurs) :**
k = 28, 31, 32, 33, 35, 39, 41. Plus grands premiers de 2.2G à 119T.

#### Impact sur le gap
- **Gap actuel** : 20 valeurs (k=22..41)
- **Après Tier 1+1b (13 preuves)** : gap réduit à **7 valeurs** → {28, 31, 32, 33, 35, 39, 41}
- Temps total de calcul estimé : **< 1 minute**

#### Ordre d'attaque recommandé
k=25 → k=34 → k=24 → k=30 → k=23 → k=26 → k=37 → k=40 → k=29 → k=36 → k=38 → k=22 → k=27

**VERDICT : [ACTIONNABLE IMMÉDIATEMENT] — réduction du gap de 20 à 7 en < 1 min de calcul**

---

### Agent 4 bis : Extension DP — ✅ EXÉCUTÉ → [0/13 PREUVES]

**Résultat : AUCUNE preuve obtenue. Le gap reste à 20 valeurs.**

L'Agent 4 avait identifié 13 valeurs computationnellement faisables. Le DP a été exécuté sur TOUTES les factorisations. Résultat : **44 facteurs premiers testés, TOUS non-bloquants** (N₀(p) > 0 pour chacun).

| Tier | k testés | Résultat |
|------|----------|----------|
| Tier 1 (6 val) | 25, 34, 24, 30, 23, 26 | **0/6** prouvés — TOUS les facteurs sont non-bloquants |
| Tier 1b (7 val) | 37, 40, 29, 36, 38, 22, 27 | **0/7** prouvés — idem |

**Conséquence cruciale** : Le gap k=22..41 n'est PAS computationnel — il est **structurel**. La méthode "trouver un facteur premier bloquant" qui fonctionnait pour k=3..21 **échoue fondamentalement** pour k ≥ 22. Cela confirme le diagnostic du verrou Bloc 3.

### Agent 5 : Incompatibilité 2-adique/3-adique — ✅ COMPLÉTÉ → [CONCEPT CORRECT, OUTILS MORTS]

**Résultat : 8 directions explorées, 8 tuées. Le paradoxe central identifié.**

| Direction | Verdict |
|-----------|---------|
| Cadre adélique (∏ complétions) | MORT — reformulation pure |
| Rôle structurel de d(k) | MORT — ramène à Bloc 3 |
| Tension archimédien/p-adique | MORT — formule du produit = tautologie |
| Obstruction de Brauer-Manin | MORT — erreur de catégorie (ensemble fini ≠ variété) |
| Conjecture abc | MORT comme preuve — informe sur rad(d) seulement |
| Crible diophantien | MORT — congruence ≠ équation polynomiale |
| Furstenberg ×2×3 discret | MORT — pont continu→fini n'existe pas |

**Le paradoxe central** : L'incompatibilité 2/3 est un phénomène GLOBAL/ARCHIMÉDIEN. Le verrou vit aux places LOCALES p | d, où 2 et 3 sont EXACTEMENT COMPATIBLES (2^S ≡ 3^k mod p). La preuve devrait montrer que cette compatibilité locale ne se traduit pas en compatibilité pour corrSum. C'est un problème de THÉORIE ADDITIVE sur un sous-groupe MULTIPLICATIF de taille LOGARITHMIQUE.

---

## AUDIT CROISÉ

### Cohérence des résultats

| Agent | Résultat | Confirme | Contredit |
|-------|----------|----------|-----------|
| Agent 1 (Furstenberg) | 3 obstructions → MORT | R77, R152 | — |
| Agent 2 (non-moment) | 7 méthodes → TOUTES mortes | R73, R96 | — |
| Agent 3 (monodromie calcul) | max|S_H|/√r CROÎT, Gaussien | R152 (survit partiellement) | L'espoir |S_H| ≤ √r |
| Agent 4 (DP) | 0/13 preuves | Diagnostic verrou Bloc 3 | Estimation Agent 4 initial |
| Agent 5 (incompatibilité 2/3) | 8/8 tuées, paradoxe central | R77/R81/R143/phase11b/14 | — |

### Kill switches croisés

1. **Agent 3 vs le projet entier** : max|S_H|/√r ∼ √(2r) signifie que même une borne |S_H| ≤ r^{1-ε} serait un résultat majeur. La borne √r du verrou V_SQRT_CANCEL est NUMÉRIQUEMENT FAUSSE.

2. **Agent 4 vs Agent 4 initial** : L'estimation de faisabilité était correcte (calculs terminés en < 1 min). Mais la question n'était pas "peut-on calculer N₀(p)" mais "N₀(p) = 0 ?". La réponse est NON pour les 44 primes testés.

3. **Agent 2 + Agent 5** : confirmation unanime que le verrou est un problème de TAN (théorie analytique des nombres) pour |H| ≈ log p, et que AUCUN outil existant (moment, non-moment, géométrie arithmétique) ne l'adresse.

### Verdict global R159

**IVS : 4.5/10** — Round majeur en INFORMATION NÉGATIVE.

Aucun théorème nouveau, mais :
- ✅ Cartographie COMPLÈTE de l'espace des méthodes (7 non-moment + 8 géo-arith = 15 voies tuées proprement)
- ✅ Le paradoxe central clairement articulé
- ✅ La borne |S_H| ≤ √r NUMÉRIQUEMENT RÉFUTÉE (max/√r ∼ 3.6 et croissant)
- ✅ Le gap k≥22 est STRUCTUREL (pas computationnel) — confirmé par 44 primes non-bloquants
- ✅ Distribution Gaussienne complexe → G_geom vraisemblablement grand

---

## REGISTRE FAIL-CLOSED

| Objet | Statut | Kill | Round |
|-------|--------|------|-------|
| Furstenberg ×2×3 analogue fini | [MORT] | 3 obstructions indépendantes | R159 |
| Burgess/Vinogradov/Stepanov | [MORT] | Seuil p^{1/4}, gap qualitatif | R159 |
| BGK somme-produit pour log p | [MORT] | Seuil p^δ (δ>0 fixé), gap qualitatif | R159 |
| Deligne/Weil II restriction | [MORT] | Somme complète (√p ≠ √r) | R159 |
| Katz monodromie (pointwise) | [MARGINAL] | Moyenne OK, pas pointwise | R159 |
| Grand crible (pointwise) | [MOYENNE SEULE] | E[|S_H|²] correct, max non borné | R159 |
| DP extension k=22..41 | [ÉCHOUÉ] | 0/13 preuves, 44 primes non-bloquants | R159 |
| Cadre adélique | [MORT] | Reformulation tautologique | R159 |
| Brauer-Manin | [MORT] | Erreur de catégorie | R159 |
| Conjecture abc | [MORT] | Informe rad(d), pas N₀ | R159 |
| Descente/crible diophantien | [MORT] | Congruence ≠ équation | R159 |
| Incompatibilité 2/3 (8 directions) | [MORT technique] | Tous les outils sont inadaptés | R159 |
| Borne |S_H| ≤ √r | **[NUMÉRIQUEMENT RÉFUTÉE]** | max/√r = 3.6 et croissant | R159 |

### Suspension de la recherche pure Bloc 3

**MAINTENUE (9ème suspension : R141-R158, R159)**

La suspension est désormais motivée non plus par l'absence d'idées, mais par la **cartographie exhaustive** de l'espace des méthodes. Les 15 nouvelles voies explorées dans R159 confirment que le verrou V_SQRT_CANCEL est un problème ouvert de TAN nécessitant un outil qualitativement nouveau.

### Condition de réouverture
- Publication d'un résultat améliorant BGK pour |H| ≈ log p (Shkredov, Shparlinski, Murphy-Petridis)
- OU méthode non-moment adaptée aux sous-groupes logarithmiques
- OU résultat de monodromie géométrique applicable avec log p paramètres
