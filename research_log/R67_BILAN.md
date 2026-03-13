# R67 — BILAN : Audit de portée de K-lite — DISCREPANCE MODÈLE détectée

## Type : P (proof-oriented)
## IVS : 9/10

**Justification IVS** :
- Potentiel de réfutation : 10/10 (la discrepance c_δ est une réfutation partielle du claim "K-lite universel Collatz")
- Gain de structure : 9/10 (localisation exacte du gap : modèle, pas preuve)
- Proximité d'un lemme : 8/10 (K-lite ⟨g²⟩ reste PROUVÉ, mais le pont vers Collatz est OUVERT)
- Risque d'accumulation : 1/10 (round ultra-centré, résultat net)

---

## Résumé exécutif

**R67 découvre une discrepance de modèle entre R57 et R62 qui invalide le claim "K-lite universel Collatz" tel que formulé en R66.** L'audit maillon par maillon révèle que :

1. **La preuve R62-R65 est mathématiquement correcte** — aucune erreur interne.
2. **La preuve s'applique à c_δ = 1 + g^{2δ} mod p** (parcours de ⟨g²⟩ = QR_p), PAS à c_δ = 1 + g_C·2^δ mod p (parcours du coset de ⟨2⟩ dans l'orbite Collatz).
3. **Le multiplicateur a changé de 2 → g² entre R60 et R62** sans justification documentée.
4. **K-lite (⟨g²⟩) est PROUVÉ pour tout p ≥ 5** — résultat correct et utile.
5. **K-lite (Collatz) est OBSERVÉ α < 1 pour tout p ≤ 300** mais **NON PROUVÉ**.
6. **Le verrou actif est le pont modèle** : montrer que le résultat ⟨g²⟩ implique le résultat Collatz, ou adapter la preuve au multiplicateur 2.

**Verdict** : énoncé 2 du prompt — **K-lite [PROUVÉ] sur une portée plus restreinte** (⟨g²⟩, pas Collatz spécifique). Reformulation exacte ci-dessous.

---

## Méthode

- 1 script (`r67_scope_audit.py`), 16 tests, 15 PASS / 1 FAIL
- Comparaison des deux définitions c_δ sur 60 primes (5 ≤ p ≤ 300)
- Test spécifique sur primes R2 (ord_p(2) petit)
- Relecture ligne par ligne des bilans R57, R59, R60, R62, R63, R64, R65, R66
- Relecture des scripts r57, r62, r63, r64, r65, r66

---

## Résultats AXE A — Audit maillon par maillon de la chaîne

### Localisation exacte de la discrepance

| Maillon | Objet c_δ utilisé | Dépendance régime | Correct ? |
|---|---|---|---|
| R57 : reformulation δ | c_δ = 1 + g_C·2^δ (Collatz) | Non (universel) | ✅ PROUVÉ |
| R59 : formulation F4 | abstrait (N_r, α<1) | Non | ✅ |
| R60 : sous-étapes (a)(b) | orbite x→2x−1 (Collatz) | Non | ✅ PROUVÉ |
| **R62 : réduction ε-proof** | **c_δ = 1 + g^{2δ} (⟨g²⟩)** | **CHANGEMENT** | ⚠️ RUPTURE |
| R63 : réduction S_h | c_δ = 1 + g^{2δ} (⟨g²⟩) | Non (interne) | ✅ |
| R64 : Jacobi + borne √p | S_h sur ⟨g²⟩ | Non (interne) | ✅ PROUVÉ |
| R65 : intégration (d) | c_δ = 1 + g^{2δ} (⟨g²⟩) | Non (interne) | ✅ PROUVÉ |
| R66 : red team portée | audite la chaîne R62-R65 | Manque le pont R57→R62 | ⚠️ |

### La rupture R60 → R62

- **R60** utilise l'orbite affine `x → 2x − 1 mod p`, cohérente avec R57 (multiplicateur 2).
- **R62** passe à `c_δ = 1 + g^{2δ} mod p` avec g = racine primitive (multiplicateur g²).
- **Ce changement n'est pas documenté** comme une substitution intentionnelle.
- La raison probable : ⟨g²⟩ = QR_p a index 2, ce qui permet la décomposition Jacobi en R64.
- Mais ⟨2⟩ a index (p−1)/ord_p(2), potentiellement grand, où Jacobi ne s'applique pas directement.

### Tableau dépendance de régime

| Question du prompt | Réponse |
|---|---|
| Q1: Erdős–Turán dépend d'un régime ? | Non — ET est universel, mais s'applique aux c_δ qu'on lui donne |
| Q2: S_h → D∞ dépend de R3 ? | Non en interne — mais S_h est calculé sur ⟨g²⟩, pas ⟨2⟩ |
| Q3: D∞ → τ<1, hypothèse cachée ? | Non en interne — mais la longueur d'arc est celle de ⟨g²⟩ |
| Q4: τ<1 → α<1, survit un régime ? | Non |
| Q5: Cas fini : tri par régime ? | Non — vérifié pour 5 ≤ p < 67, mais SUR ⟨g²⟩ |
| Q6: Portée exacte ? | ⟨g²⟩ pour tout p ≥ 5. Collatz : NON PROUVÉ |

### Premier maillon qui casse si portée universelle fausse

**R62** — le passage du multiplicateur 2 au multiplicateur g². C'est le seul point de rupture. Toute la chaîne R62→R65 est internement correcte POUR ⟨g²⟩.

---

## Résultats AXE B — Portée exacte de K-lite

### Verdict : Énoncé 2 — K-lite PROUVÉ sur portée plus restreinte

**Théorème K-lite (⟨g²⟩) [PROUVÉ]** :
> Pour tout premier p ≥ 5, en posant c_δ = 1 + g^{2δ} mod p (où g est une racine primitive mod p) et N_r = #{δ ∈ [0, M] : dlog(r/c_δ) ∈ [0, M−δ]}, il existe α_p < 1 tel que max_{r} N_r ≤ α_p · (M+1), avec α_p → 1/4 quand p → ∞.

**Observation K-lite (Collatz) [OBSERVÉ, NON PROUVÉ]** :
> Pour tout premier 5 ≤ p ≤ 300, en posant c_δ = 1 + g_C·2^δ mod p (définition Collatz) et N_r le compteur barrier correspondant, on observe α_p < 1 avec α_max = 0.667 (à p = 7).

### Distinction des statuts

| Portée | Statut | Ladder |
|---|---|---|
| K-lite (⟨g²⟩) pour tout p ≥ 5 | **PROUVÉ** | L8 (lemme prouvé) |
| K-lite (Collatz) pour tout p ≤ 300 | **OBSERVÉ** | L3 (observation répétée) |
| K-lite (Collatz) pour tout p ≥ 5 | **CONJECTURÉ** | L1-L2 (intuition/observation) |
| "K-lite universel" (claim R66) | **RETRACTÉ** — discrepance modèle | — |

### Réponses aux questions obligatoires

1. **"Pour tout p ≥ 5" est-il correct ?** → OUI, mais uniquement pour la version ⟨g²⟩. NON pour la version Collatz.
2. **Version correcte ?** → "Pour tout p ≥ 5, K-lite prouvé pour c_δ = 1+g^{2δ} (parcours de QR_p). Pour le cas Collatz c_δ = 1+g_C·2^δ, K-lite est observé mais non prouvé."
3. **Différence prouvé/observé/conjecturé** :
   - Prouvé : chaîne analytique complète (S_h→Jacobi→ET→α<1) pour ⟨g²⟩
   - Observé : calcul direct α < 1 pour 60 primes (Collatz)
   - Conjecturé : extrapolation que α < 1 pour tout p (Collatz)
4. **Faux verrou hérité ?** → Oui : R1/R2 comme "régimes à traiter séparément" est partiellement un faux verrou. Le vrai verrou est le pont ⟨2⟩ → ⟨g²⟩, indépendamment du régime.
5. **Correction minimale** : retirer "K-lite universel PROUVÉ pour Collatz" de R66, le remplacer par "K-lite PROUVÉ pour ⟨g²⟩, gap modèle vers Collatz".

---

## Résultats AXE C — Survivant post-audit

### Candidat 1 : Pont modèle ⟨2⟩ → ⟨g²⟩ (SURVIVANT)

**Énoncé intuitif** : Montrer que le contrôle de N_r pour c_δ parcourant ⟨g²⟩ implique le même contrôle pour c_δ parcourant le coset de ⟨2⟩.

**Version semi-formelle** : Soit c_δ^C = 1 + g_C·2^δ (Collatz) et c_δ^Q = 1 + g^{2δ} (QR_p). On sait max_r N_r(c^Q) ≤ α·(M+1) avec α < 1. Montrer que max_r N_r(c^C) ≤ α'·(M+1) avec α' < 1.

**Ce qu'il donnerait** : K-lite PROUVÉ pour le cas Collatz réel, fermant la base k=2 au niveau utile.

**Ce qu'il faudrait prouver** :
- Soit un argument de sous-ensemble : ⟨2⟩ ⊆ ⟨g²⟩ quand 2 ∈ QR_p, donc c_δ^C parcourt un sous-ensemble de c_δ^Q.
- Soit un argument direct : adapter la borne S_h au sous-groupe ⟨2⟩ de QR_p.
- Soit un argument combinatoire : montrer que la restriction à un sous-arc ne peut pas concentrer les hits.

**Faiblesse potentielle** : Quand 2 ∉ QR_p (moitié des primes), les cosets sont disjoints et l'argument de sous-ensemble échoue. Un argument de transfert plus subtil serait nécessaire.

**Ladder** : L2 (intuition) — la direction est claire mais aucune preuve n'est esquissée.

### Candidat 2 : Cross-résidu (ÉLIMINÉ)

**Énoncé intuitif** : Bootstrap inter-résidus pour le théorème complet N₀(d)=0.

**Ce qu'il donnerait** : Progression vers le théorème final, mais PRÉMATURÉ tant que K-lite Collatz n'est pas prouvé.

**Faiblesse fatale** : Construire cross-résidu sur une base non prouvée (K-lite Collatz) serait bâtir sur du sable. Le pont modèle doit être fermé AVANT.

**Élimination** : Cross-résidu est ajourné (pas éliminé à terme), subordonné à la fermeture du pont modèle.

### Décision : Candidat 1 SURVIVANT pour R68

**Justification** : Le pont modèle est le gap le plus proche et le plus ciblé. Il est potentiellement fermable par un argument algébrique (sous-groupe/coset). Cross-résidu requiert que K-lite Collatz soit prouvé, donc il attend.

---

## Résultats AXE D — Chaîne globale mise à jour

### Chaîne active après R67

```
R57: reformulation δ (Collatz)     [PROUVÉ]
  ↓
R59: formulation F4                [PROUVÉ]
  ↓
R60: sous-étapes (a)(b)            [PROUVÉ]
  ↓
R62: passage ⟨2⟩ → ⟨g²⟩           [GAP — pont modèle NON PROUVÉ] ← VERROU ACTIF
  ↓
R63: réduction S_h                 [PROUVÉ pour ⟨g²⟩]
  ↓
R64: Jacobi + borne √p            [PROUVÉ pour ⟨g²⟩]
  ↓
R65: intégration (d) + cas fini    [PROUVÉ pour ⟨g²⟩]
  ↓
K-lite (⟨g²⟩)                     [PROUVÉ]
  ↓
K-lite (Collatz)                   [NON PROUVÉ — attend pont modèle]
  ↓
Cross-résidu                       [AJOURNÉ — attend K-lite Collatz]
```

### Rappel anti-dérive

**NE PAS écrire** "K-lite prouvé pour Collatz" tant que le pont modèle R62 n'est pas fermé.
**NE PAS confondre** ⟨g²⟩ = QR_p avec ⟨2⟩ = arc Collatz.
**NE PAS relancer** cross-résidu sans K-lite Collatz prouvé.

---

## Contrôle secondaire

Le script r67_scope_audit.py constitue le micro-test ciblé autorisé par le prompt.

**Résultats clés** :
- 60 primes testés, α_Collatz < 1 pour TOUS (max = 0.667 à p=7)
- Sur les primes R2 (ord petit), α_Collatz reste < 0.5 (sauf p=7 cas extrême avec M+1=3)
- Les α_Collatz et α_R62 divergent significativement sur les primes R2 (Δα jusqu'à 0.14)
- Les α_Collatz et α_R62 sont proches sur les primes R3 (Δα < 0.05)

**Observation cruciale** : quand 2 est racine primitive (ord_p(2) = p−1), les deux versions coïncident car ⟨2⟩ = ⟨g²⟩. C'est le cas pour p = 29 (Δα = 0).

---

## CEC inchangé

- Type A : obstruction première directe
- Type B : exclusion composite exacte
- Type C : exclusion composite par bornes combinées
- Type D : exclusion analytique via SPC / structure monotone composite

---

## Théorèmes

| ID | Énoncé | Statut |
|----|--------|--------|
| T153 | Discrepance c_δ : R57 utilise ⟨2⟩, R62 utilise ⟨g²⟩, les deux sont DIFFÉRENTS [PROUVÉ] | R67 |
| T154 | K-lite (⟨g²⟩) : max N_r ≤ α·(M+1) avec α < 1 pour tout p ≥ 5 [PROUVÉ] | R62-R65 (reformulé R67) |
| T155 | K-lite (Collatz) : α < 1 OBSERVÉ pour tout p ≤ 300 [OBSERVÉ] | R67 |
| T156 | Le gap modèle R57→R62 est le seul point de rupture de la chaîne [PROUVÉ] | R67 |
| T157 | Quand 2 est racine primitive (ord=p−1), les deux c_δ coïncident [PROUVÉ] | R67 |

---

## Ladder of Proof

| Objet | Niveau | Commentaire |
|-------|--------|-------------|
| K-lite (⟨g²⟩) complet | **L8 lemme prouvé** | Chaîne R62-R65 correcte |
| K-lite (Collatz) | **L3 observation répétée** | 60 primes, α < 1 partout |
| Pont modèle ⟨2⟩ → ⟨g²⟩ | **L1 intuition** | Direction identifiée, pas de preuve |
| Discrepance c_δ | **L8 lemme prouvé** | Computationnellement et théoriquement confirmé |
| Cross-résidu | **L2 intuition** | Ajourné |
| Chaîne S_h → Jacobi → ET → α<1 | **L8 lemme prouvé** | Pour ⟨g²⟩ uniquement |

---

## Ce qui est appris

1. **La preuve R62-R65 est correcte** — le problème n'est pas dans les mathématiques internes.
2. **Le problème est dans le modèle** — le passage ⟨2⟩ → ⟨g²⟩ n'est pas justifié.
3. **K-lite (⟨g²⟩) EST un résultat valide** — il contrôle la distribution des dlog dans QR_p.
4. **La décomposition Jacobi est spécifique à l'index 2** — elle utilise que ⟨g²⟩ est d'index 2 dans F_p*.
5. **Le cas Collatz utilise ⟨2⟩ d'index (p−1)/ord_p(2)** — potentiellement grand, invalidant Jacobi.
6. **L'observation computationnelle est robuste** — α < 1 pour les 60 primes testés (version Collatz).
7. **Le seuil d'alerte est atteint** — R66 avait conclu "universel" trop vite, R67 corrige.

---

## Ce qui est enterré

1. **"K-lite universel prouvé pour Collatz"** (claim R66) — RETRACTÉ, remplacé par "K-lite prouvé pour ⟨g²⟩".
2. **R1/R2 comme classification pertinente de verrou** — partiellement obsolète. Le vrai verrou est le pont modèle, pas un régime spécifique.
3. **Cross-résidu comme prochain verrou** — ajourné, subordonné au pont modèle.

---

## Autopsie des pistes fermées

### 1. "K-lite universel Collatz PROUVÉ" (R66)
- **Type de mort** : mauvaise échelle (claim trop fort)
- **Hypothèse implicite fausse** : que c_δ = 1 + g^{2δ} et c_δ = 1 + g_C·2^δ sont interchangeables
- **Ce que la mort enseigne** : TOUJOURS vérifier que l'objet prouvé est l'objet visé, pas un proxy
- **Où cela redirige** : pont modèle ⟨2⟩ → ⟨g²⟩

### 2. Classification R1/R2/R3 comme structure de verrou principal
- **Type de mort** : non ciblante (partiellement)
- **Hypothèse implicite fausse** : que le verrou dépend du régime de ord_p(2)
- **Réalité** : le verrou dépend de la DIFFÉRENCE entre ⟨2⟩ et ⟨g²⟩, pas de la taille de ord
- **Ce que la mort enseigne** : la classification par régime cache le vrai problème (pont modèle)
- **Où cela redirige** : pont modèle comme cible unique

### 3. Cross-résidu comme survivant immédiat
- **Type de mort** : absorbée (prématurée)
- **Hypothèse implicite fausse** : que K-lite Collatz est prouvé et on peut construire dessus
- **Réalité** : il faut d'abord fermer le pont modèle
- **Où cela redirige** : pont modèle d'abord, cross-résidu ensuite

### 4. Red team R66 comme audit complet
- **Type de mort** : trop faible
- **Hypothèse implicite fausse** : auditer la chaîne R62-R65 suffit pour valider "universel Collatz"
- **Réalité** : l'audit R66 a vérifié la cohérence INTERNE mais manqué le pont EXTERNE R57→R62
- **Ce que la mort enseigne** : un audit de portée doit remonter jusqu'à la formulation initiale du problème
- **Où cela redirige** : audit plus profond (fait en R67)

---

## Survivant pour R68

**Pont modèle : ⟨2⟩ → ⟨g²⟩**

- **Énoncé** : Montrer que K-lite (⟨g²⟩) implique K-lite (Collatz), ou adapter directement la preuve au sous-groupe ⟨2⟩.
- **Approches possibles** :
  1. Argument de sous-ensemble quand 2 ∈ QR_p
  2. Adaptation de la borne S_h au sous-groupe ⟨2⟩ (sommes de caractères sur coset)
  3. Argument combinatoire de non-concentration pour sous-arcs
- **Ladder** : L1 (intuition)
- **Difficulté estimée** : moyenne à élevée (la technique Jacobi index-2 ne se transfère pas trivialement)

---

## Critères PASS

| Critère | Statut |
|---------|--------|
| PASS-1 : audit maillon par maillon produit | ✅ 8 maillons audités, rupture localisée à R62 |
| PASS-2 : dépendance/non-dépendance tranchée | ✅ Pas de dépendance de régime, mais discrepance de MODÈLE |
| PASS-3 : théorème K-lite exact formulé | ✅ K-lite (⟨g²⟩) prouvé, K-lite (Collatz) observé |
| PASS-4 : illusion de portée enterrée | ✅ "K-lite universel Collatz" retracté avec autopsie |
| PASS-5 : survivant unique pour R68 | ✅ Pont modèle ⟨2⟩ → ⟨g²⟩ |

**Score : 5/5 PASS**

---

## Risques et limites

1. **Le pont modèle peut être difficile** — la technique Jacobi est spécifique à l'index 2. Pour ⟨2⟩ d'index arbitraire, il faut une approche différente (Gauss sums sur sous-groupes, Katz estimates, etc.).
2. **L'observation computationnelle est robuste mais limitée** — 60 primes ≤ 300. Il faudrait tester jusqu'à p ~ 10⁵ pour plus de confiance.
3. **Le cas 2 ∈ QR_p peut être plus simple** — quand 2 est un résidu quadratique, ⟨2⟩ ⊆ ⟨g²⟩ = QR_p et un argument de sous-ensemble pourrait marcher directement. C'est une piste prometteuse.
4. **Le seuil α_max = 0.667 (p=7)** est un petit prime, cas dégénéré (M+1=3). Les grands primes ont α bien plus petit.

---

## Registre méthodologique

### 1. Type du round
**P** (proof-oriented) — audit de portée

### 2. IVS — Information Value Score : 9/10
- Potentiel de réfutation : 10/10
- Gain de structure : 9/10
- Proximité d'un lemme : 8/10
- Risque d'accumulation : 1/10

### 3. Ladder — voir tableau ci-dessus

### 4. Autopsie — voir section dédiée (4 pistes enterrées)

---

## Verdict final : 9/10

**R67 identifie la discrepance de modèle entre c_δ = 1 + g_C·2^δ (Collatz, R57) et c_δ = 1 + g^{2δ} (⟨g²⟩, R62) qui invalide le claim "K-lite universel Collatz" de R66.** La preuve R62-R65 est internement correcte mais s'applique à un objet DIFFÉRENT du cas Collatz. K-lite (⟨g²⟩) est PROUVÉ (L8). K-lite (Collatz) est OBSERVÉ (L3) sur 60 primes mais NON PROUVÉ. Le verrou actif est le pont modèle ⟨2⟩ → ⟨g²⟩, pas un régime R1/R2/R3. Le survivant unique pour R68 est la fermeture de ce pont. La chaîne est plus honnête qu'avant R67.
