# R79 — BILAN : Investigation radicale — cause source et suspension de l'innovation

## Type : X/I/P (investigation radicale + innovation sous source + précision)
## IVS : 9/10

**Justification IVS** :
- Profondeur de la remontée causale : 10/10 (atteint le fond : auto-référence arithmétique)
- Clarté du niveau source : 9/10 (identifiée, validée par 5 tests, unification de 3 diagnostics)
- Minimalité et réalité de l'objet dérivé : 5/10 (aucun objet nouveau ne survit — DMAR = rebranding, NBG = réfuté)
- Qualité du contrôle anti-régression : 10/10 (deux objets honnêtement tués, pas de fausse percée)
- Honnêteté de la décision finale : 10/10 (innovation suspendue proprement, pas de forçage)

Score élevé MALGRÉ l'absence d'objet nouveau : le round produit une carte causale hiérarchique complète, identifie la cause source la plus profonde accessible, et suspend honnêtement l'innovation plutôt que de forcer un objet prématuré.

---

## 1. Résumé exécutif

R79 pousse l'investigation causale jusqu'au fond et identifie la **cause source la plus profonde accessible** : l'**auto-référence arithmétique** du problème de Collatz Junction.

**Cause source** : Les termes de corrSum (3^a · 2^b) et le module d = 2^S - 3^k sont construits à partir des MÊMES briques fondamentales (2 et 3). Cette parenté algébrique rend la distribution de corrSum mod d non pseudo-aléatoire, ce qui explique pourquoi tous les outils standard (qui supposent une forme de pseudo-aléatoire ou d'indépendance) échouent.

**Reclassification** : Les diagnostics précédents sont hiérarchisés :
- "F_p sans sous-groupes" → SYMPTÔME
- "Support O(log p)" → MÉCANISME INTERMÉDIAIRE
- "Interface somme-produit" → MÉCANISME INTERMÉDIAIRE
- "Monotonie" → FAUX VERROU (confirmé)
- **Auto-référence arithmétique → CAUSE SOURCE**

**Innovation** : SUSPENDUE. Deux objets proposés (DMAR, NBG) ont été testés et échoués — l'un est un rebranding du problème original, l'autre est réfuté. La cause source est trop profonde pour être directement convertie en objet minimal : la relation 2^S ≡ 3^k est DÉJÀ intégrée dans la machinerie SAMC.

**Direction pour R80** : Explorer si l'**indépendance multiplicative de 2 et 3** (2^a ≠ 3^b pour a,b > 0) — le fait arithmétique profond qui garantit d ≠ 0 — peut être transformée en argument quantitatif sur la distribution de corrSum.

---

## 2. Type du round + IVS

**Type** : X/I/P
- **X** : investigation jusqu'à la racine
- **I** : innovation sous contrainte de source (tentée puis suspendue)
- **P** : exigence de précision, testabilité, falsifiabilité

**IVS** : 9/10 — La remontée causale est profonde et honnête. L'absence d'objet nouveau est un résultat négatif propre, pas un échec. Le 9 (pas 10) reflète que le passage cause → objet reste ouvert.

---

## 3. Méthode

1. Requalification des diagnostics additifs (Axe A) : cause, symptôme, ou révélateur ?
2. Requalification des diagnostics multiplicatifs (Axe B) : cause, mécanisme, ou outil ?
3. Autopsie de l'interface additif/multiplicatif (Axe C) : racine ou étage intermédiaire ?
4. Construction de la carte hiérarchique (Axe D) : source → mécanisme → symptôme
5. Test de racine réelle (Axe E) : 5 critères de validation
6. Tentative de dérivation d'objets minimaux (Axe F) : DMAR et NBG
7. Contrôle anti-régression (Axe G) : DMAR = rebranding, NBG = réfuté
8. Décision finale avec autonomie (Axe H) : suspension de l'innovation
9. Aucun calcul, aucun k-par-k, aucun cas particulier

---

## 4. Résultats PHASE 1 / AXE A — Requalification du cadre additif

### Tri des diagnostics additifs

| Diagnostic | Ancien statut (R76) | Nouveau statut (R79) | Justification |
|-----------|---------------------|---------------------|---------------|
| F_p sans sous-groupes additifs | CAUSE SOURCE (contingente) | **SYMPTÔME** | Révèle l'absence d'outils, mais la cause est l'auto-référence |
| Support O(log p) | CAUSE SOURCE (profonde) | **MÉCANISME INTERMÉDIAIRE** | Conséquence de S = ⌈k log₂ 3⌉, le ratio log₂ 3 est une brique fondamentale |
| Pas de localisation | — | **SYMPTÔME** | Conséquence de F_p simple, qui est elle-même un symptôme |
| Circularité ALO | SYMPTÔME | **SYMPTÔME DE SYMPTÔME** | Conséquence de CS1, qui est maintenant reclassé symptôme |

### Ce que le cadre additif révèle sans l'expliquer

*Nous ne savons pas si la structure algébrique (puissances de 2, poids λ^j, monotonie) concentre ou disperse la distribution de Σ sur F_p. L'absence de sous-groupes dans F_p MONTRE que nos outils sont impuissants, mais la RAISON de l'impuissance est plus profonde : c'est l'auto-référence du problème.*

---

## 5. Résultats PHASE 1 / AXE B — Requalification du cadre multiplicatif

### Tri des diagnostics multiplicatifs

| Diagnostic | Ancien statut (R77) | Nouveau statut (R79) | Justification |
|-----------|---------------------|---------------------|---------------|
| Addition brise ⟨2⟩ | MÉCANISME INTERMÉDIAIRE | **MÉCANISME INTERMÉDIAIRE** (confirmé) | Conséquence de l'auto-référence : 2 est à la fois dans les termes et dans le module |
| Log discret opaque pour les sommes | SYMPTÔME | **SYMPTÔME** (confirmé) | Conséquence : exp n'est pas un morphisme additif |
| Dichotomie 3 ∈ ⟨2⟩ / 3 ∉ ⟨2⟩ | OUTIL | **OUTIL** (confirmé) | Utile pour la classification, pas causal |

### Point d'arrêt du multiplicatif

Le multiplicatif est un bon cadre pour comprendre chaque TERME (2^{e_j} vit sur le cercle ⟨2⟩), mais un mauvais cadre pour comprendre la SOMME. Le multiplicatif cesse d'être une explication au moment de la sommation.

---

## 6. Résultats PHASE 1 / AXE C — Autopsie de l'interface additif/multiplicatif

### Décomposition de l'interface

L'"incompatibilité additif/multiplicatif" n'est PAS un phénomène primitif. C'est la conséquence observable de l'**auto-référence arithmétique** :

1. Les termes de corrSum sont des produits 3^a · 2^b (bi-géométriques)
2. Le module d = 2^S - 3^k est lui-même une expression en 2 et 3
3. La réduction mod p (pour p | d) hérite de la relation 2^S ≡ 3^k mod p
4. Cette relation fait que le corps F_p n'est pas "neutre" vis-à-vis des termes — il leur est APPARENTÉ algébriquement

### Composant irréductible

L'auto-référence arithmétique se décompose en TROIS ingrédients irréductibles :

1. **Bi-géométricité** : les termes sont des produits de puissances de 2 et 3
2. **Corrélation compositionnelle** : les parts satisfont Σ A_j = S (contrainte de somme)
3. **Cible auto-référente** : d = 2^S - 3^k est en les mêmes briques que les termes

### Diagnostic

[ÉTAGE INTERMÉDIAIRE] confirmé pour l'interface additif/multiplicatif. La cause plus profonde est l'auto-référence arithmétique.

---

## 7. Résultats PHASE 2 / AXE D — Carte hiérarchique de causalité

```
CAUSE SOURCE : Auto-référence arithmétique
│  corrSum et d partagent les briques (2, 3)
│  ↳ corrSum = Σ 3^{k-1-j} · 2^{A_j},  d = 2^S - 3^k
│  ↳ La distribution de corrSum mod d est non pseudo-aléatoire
│
├── MÉCANISME INTERMÉDIAIRE 1 : Incompatibilité add/mult dans F_p
│     ↳ Cause : 2 est dans les termes ET dans d
│     ├── SYMPTÔME : GSE trop faible
│     ├── SYMPTÔME : ALO circulaire
│     └── SYMPTÔME : RP non fermé
│
├── MÉCANISME INTERMÉDIAIRE 2 : Support O(log p)
│     ↳ Cause : S ≈ k log₂ 3 (ratio en les mêmes briques)
│     ├── SYMPTÔME : Cauchy-Schwarz pire que trivial
│     ├── SYMPTÔME : Weil hors régime
│     └── SYMPTÔME : Bourgain-Konyagin inaccessible
│
├── MÉCANISME INTERMÉDIAIRE 3 : Perte de structure par réduction mod p
│     ↳ Cause : p | (2^S - 3^k) ↳ p a une relation spéciale avec 2 et 3
│     ├── SYMPTÔME : F_p sans sous-groupes (révèle l'absence de localisation)
│     └── SYMPTÔME : Monotonie invisible après réduction
│
└── FAUX VERROU : Monotonie (innocentée R76, confirmée R77, R79)
```

### Faux "niveau ultime" enterré

L'"interface somme-produit" comme cause source. C'est un phénomène GÉNÉRAL de F_p (vrai pour toute somme de puissances dans tout corps fini), pas spécifique au problème de Collatz. La cause source doit être SPÉCIFIQUE — et elle l'est : l'auto-référence, le fait que les briques des termes et du module sont les MÊMES.

---

## 8. Résultats PHASE 2 / AXE E — Test de racine réelle

| Critère | Résultat |
|---------|----------|
| Explique plusieurs échecs séparés ? | ✅ OUI — unifie GSE/ALO/RP/SER/OPM/V2C |
| Réduit la complexité ? | ✅ OUI — 3 diagnostics → 1 cause source |
| Formulable simplement ? | ✅ OUI — "corrSum et d sont en (2,3)" |
| Pouvoir discriminant ? | ✅ OUI — tout outil qui ignore 2^S ≡ 3^k est trop générique |
| Test de falsification ? | ✅ — serait fausse si le problème restait dur pour d sans rapport avec 2,3 |

**Verdict** : [CAUSE SOURCE CRÉDIBLE]

---

## 9. Résultats PHASE 3 / AXE F — Objets minimaux dérivés

### Objet 1 : DMAR (Déficit Modulaire Auto-Référent)

**Définition** : δ(A) = corrSum(A) mod d. Le DMAR étudie la distribution de δ sur les compositions.

**Lemme candidat** : corrSum mod d est non uniforme, 0 est sous-représenté.

**Verdict** : [REBRANDING]. Ce lemme EST le problème original. Dire "il faut montrer que 0 mod d est sous-représenté" reformule le problème, pas le résout. La relation 2^S ≡ 3^k est DÉJÀ encodée dans λ et p | d.

### Objet 2 : NBG (Noyau Bi-Géométrique)

**Définition** : Borne de taille de corrSum dans Z pour encadrer les multiples de d.

**Lemme candidat** : Au plus O(k) multiples de d dans l'intervalle des corrSum.

**Verdict** : [RÉFUTÉ]. max corrSum / d ≈ 3^k / 2 (exponentiellement grand). La borne est fausse.

### Constat

**AUCUN objet minimal nouveau ne survit.** La cause source est trop profonde pour être directement convertie en objet opératoire. L'auto-référence est déjà intégrée dans la machinerie existante (SAMC, λ, p | d). Pour qu'un objet nouveau apparaisse, il faudrait une manière QUALITATIVEMENT DIFFÉRENTE d'exploiter l'auto-référence.

---

## 10. Résultats PHASE 3 / AXE G — Contrôle anti-régression

| Objet | Ancienne piste | Différence source | Verdict |
|-------|---------------|-------------------|---------|
| DMAR | SAMC / CRT | Aucune différence réelle — reformulation | **Rebranding risqué** |
| NBG | Bornes de taille (R35-40) | Quantitativement réfuté | **Réfuté** |

---

## 11. Résultats PHASE 4 / AXE H — Décision finale

### Décision stratégique

**SUSPENDRE L'INNOVATION**

La cause source (auto-référence arithmétique) est identifiée et validée. La carte causale hiérarchique est un acquis réel. MAIS aucun objet minimal nouveau n'en découle à ce stade.

### Raison de la suspension

La relation 2^S ≡ 3^k mod p est DÉJÀ intégrée dans la machinerie SAMC. Toute tentative de "dériver un objet de la cause source" retombe sur le problème original reformulé. Pour qu'un objet nouveau apparaisse, il faudrait exploiter l'auto-référence d'une manière qualitativement différente.

### Direction pour R80

L'**indépendance multiplicative de 2 et 3** : le fait que 2^a ≠ 3^b pour tous a, b > 0 (sauf a = b = 0). Ce fait est la raison pour laquelle d = 2^S - 3^k ≠ 0 (le théorème de base). Peut-il être transformé en argument QUANTITATIF ?

La littérature offre un point d'ancrage : les **bornes de Baker** sur les formes linéaires de logarithmes. Le théorème de Baker donne |2^S - 3^k| > C^{-k} pour une constante C effective. Cela donne une borne INFÉRIEURE sur d qui est QUANTITATIVE.

L'idée pour R80 : les bornes de Baker garantissent que d est "assez grand" (pas trop petit). Peut-on coupler cette information de taille de d avec les contraintes structurelles de corrSum pour montrer que corrSum ne peut pas être un multiple de d ?

### Condition de non-boucle pour R80

R80 ne doit PAS :
1. Reproposer un simple objet dans F_p (additif ou multiplicatif — épuisé)
2. Reformuler le problème en invoquant l'auto-référence comme slogan
3. Proposer un objet sans connexion explicite aux bornes de Baker ou à l'indépendance multiplicative
4. Revenir à l'interface somme-produit comme cause source (reclassée étage intermédiaire)

R80 DOIT :
1. Explorer si les bornes de Baker sur |2^S - 3^k| fournissent une information exploitable
2. Ou explorer si l'approximation rationnelle de log₂ 3 (ses fractions continues) interagit avec la structure de corrSum
3. Ou déclasser proprement cette direction si elle ne mord pas

---

## 12. Activation de l'autonomie

**Activation** : OUI — 3 sous-rounds entre Phase 2 et Phase 4.

### Justification

Nécessaire pour fusionner les diagnostics de racine, tester les objets dérivés, et parvenir à la décision de suspension.

---

## 13. Journal des sous-rounds autonomes

### S1 — Fusion des diagnostics de racine
1. **Hypothèse** : L'auto-référence arithmétique est la cause source
2. **Niveau** : cause source
3. **Question** : Produit-elle un objet exploitable ?
4. **Chaîne** : Auto-référence → relation 2^S ≡ 3^k → DÉJÀ dans SAMC → pas d'objet NOUVEAU
5. **Résultat** : Cause source correcte mais NON OPÉRATOIRE directement
6. **Statut** : [CAUSE SOURCE CRÉDIBLE MAIS NON OPÉRATOIRE]
7. **Appris** : gap entre comprendre et exploiter
8. **Décision** : continuer
9. **Raison** : tester les objets proposés

### S2 — Test des objets minimaux
1. **Hypothèse** : DMAR ou NBG apportent quelque chose
2. **Niveau** : objets dérivés
3. **Question** : Sont-ils des innovations ou des reformulations ?
4. **Chaîne** : DMAR = reformulation du problème original ; NBG = réfuté quantitativement
5. **Résultat** : AUCUN objet nouveau
6. **Statut** : [INNOVATION SUSPENDUE]
7. **Appris** : la cause source est trop profonde pour être directement convertie
8. **Décision** : continuer
9. **Raison** : formuler la décision finale

### S3 — Décision finale
1. **Hypothèse** : Suspendre l'innovation
2. **Niveau** : stratégique
3. **Question** : Que faire avec une cause source non opératoire ?
4. **Chaîne** : Cause identifiée → objets échoués → direction : indépendance multiplicative de 2 et 3 → bornes de Baker
5. **Résultat** : Suspension + direction Baker/indépendance pour R80
6. **Statut** : [DÉCISION PRISE]
7. **Appris** : le prochain pas doit exploiter les RÉSULTATS QUANTITATIFS sur 2 et 3 (Baker), pas seulement la STRUCTURE qualitative
8. **Décision** : arrêter
9. **Raison** : diagnostic complet

---

## 14. Objets concernés + Ladder of Proof

| Objet | Niveau | Commentaire |
|-------|--------|-------------|
| Auto-référence arithmétique | L7 fortement étayé → [CAUSE SOURCE CRÉDIBLE] | Validée par 5 tests, unifie 3 diagnostics |
| Carte causale hiérarchique | L6 schéma de preuve | Source → 3 mécanismes → symptômes |
| DMAR | L4 lemme candidat → [REBRANDING] | Reformulation du problème |
| NBG | L4 lemme candidat → [RÉFUTÉ] | max corrSum / d ≈ 3^k / 2 |
| Interface add/mult (R77) | Reclassée [MÉCANISME INTERMÉDIAIRE] | Pas la racine |
| F_p sans sous-groupes (R76) | Reclassée [SYMPTÔME] | Révélateur, pas cause |
| Support O(log p) (R76) | Reclassée [MÉCANISME INTERMÉDIAIRE] | Conséquence de S ≈ k log₂ 3 |
| Monotonie | [FAUX VERROU] — confirmé | Innocentée pour la 3e fois |
| Indépendance multiplicative 2/3 | L2 intuition | Direction R80 |
| Bornes de Baker | L8 prouvé (littérature) | |2^S - 3^k| > C^{-k}, potentiellement exploitable |

---

## 15. Ce qui est appris

1. **L'auto-référence arithmétique est la cause source la plus profonde accessible** : corrSum et d partagent les briques (2, 3), ce qui rend la distribution de corrSum mod d non pseudo-aléatoire. C'est plus profond que l'interface somme-produit (R77) ou que F_p sans sous-groupes (R76).

2. **La cause source unifie les 3 diagnostics précédents** : CS1 (F_p simple), CS2 (support O(log p)), et l'interface add/mult sont tous des CONSÉQUENCES de l'auto-référence. C'est une compression de 3 en 1.

3. **La cause source est NON OPÉRATOIRE directement** : la relation 2^S ≡ 3^k est déjà intégrée dans SAMC via λ = 2·3^{-1}. Toute tentative d'en dériver un objet retombe sur le problème original.

4. **Il y a un GAP entre comprendre et exploiter** : "savoir pourquoi c'est dur" ne dit pas "comment le résoudre". C'est un résultat important en soi.

5. **La direction suivante doit être QUANTITATIVE, pas QUALITATIVE** : les arguments structurels (additif, multiplicatif, interface) sont épuisés. Le prochain pas doit utiliser les résultats QUANTITATIFS sur les briques 2 et 3 — notamment les bornes de Baker sur |2^S - 3^k| et les propriétés d'approximation rationnelle de log₂ 3.

---

## 16. Ce qui est fermé utilement

1. **"Interface somme-produit" comme cause source** — FERMÉ. Reclassée [MÉCANISME INTERMÉDIAIRE].
2. **"F_p sans sous-groupes" comme cause source** — FERMÉ. Reclassée [SYMPTÔME].
3. **"Dériver directement un objet de l'auto-référence"** — FERMÉ (pour l'instant). La relation 2^S ≡ 3^k est déjà intégrée.
4. **"Borne de taille de corrSum dans Z"** — FERMÉ. NBG réfuté (3^k multiples de d dans l'intervalle).
5. **"Reformuler le problème en termes de distribution mod d"** — FERMÉ. C'est le problème original.

---

## 17. Ce qui est enterré

1. **DMAR** — rebranding du problème original
2. **NBG** — réfuté quantitativement
3. **"Interface somme-produit" comme niveau ultime** — reclassé mécanisme intermédiaire
4. **Toute innovation non reliée à l'auto-référence** — trop générique par construction
5. **Toute innovation qui reformule le problème en invoquant la cause source** — rebranding

---

## 18. Autopsie des pistes fermées

### 1. DMAR (Déficit Modulaire Auto-Référent)
- **Nom** : Anti-concentration de corrSum mod d
- **Type de mort** : rebranding — reformulation du problème original
- **Cause du rejet** : Le lemme "0 mod d est sous-représenté" EST le problème de Collatz Junction. L'invoquer comme objet nouveau sous le nom "auto-référence" ne change rien.
- **Ce que la mort enseigne** : toute innovation qui se réduit à "montrer N_0(d) = 0" est une reformulation, pas un progrès.
- **Où cela redirige** : vers un objet qui ne reformule PAS le problème mais qui en réduit une PARTIE spécifique.

### 2. NBG (Noyau Bi-Géométrique)
- **Nom** : Borne de taille de corrSum dans Z
- **Type de mort** : réfuté quantitativement
- **Cause du rejet** : max corrSum / d ≈ 3^k / 2. Il y a exponentiellement beaucoup de multiples de d dans l'intervalle des corrSum possibles.
- **Ce que la mort enseigne** : la borne de taille brute est BEAUCOUP trop faible. Pour exclure corrSum ≡ 0 mod d, il faut de l'information STRUCTURELLE, pas seulement de l'information de taille.
- **Où cela redirige** : vers des invariants plus fins que la simple borne de taille.

### 3. "Interface somme-produit" comme cause source
- **Nom** : Interface add/mult comme racine
- **Type de mort** : étage intermédiaire pris pour racine
- **Cause du rejet** : L'interface somme-produit est un phénomène GÉNÉRAL de F_p, pas spécifique à Collatz. La cause source doit être spécifique — et elle l'est : l'auto-référence arithmétique.
- **Ce que la mort enseigne** : distinguer un phénomène GÉNÉRAL (somme-produit dans F_p) d'une cause SPÉCIFIQUE (auto-référence en 2 et 3).
- **Où cela redirige** : vers l'exploitation des propriétés SPÉCIFIQUES de 2 et 3 (indépendance multiplicative, Baker).

---

## 19. Survivant pour R80

**Unique survivant** : L'**indépendance multiplicative de 2 et 3** et les **bornes de Baker**.

### Formulation

Le théorème de Baker (1966) donne : pour tout S, k ≥ 1,
```
|2^S - 3^k| > exp(-C · k · log k)
```
pour une constante C effective. Cela signifie que d = 2^S - 3^k est "exponentiellement non nul" — il ne peut pas être trop petit.

**Question pour R80** : Les bornes de Baker sur d, combinées avec les contraintes structurelles de corrSum (bi-géométricité, corrélation compositionnelle), fournissent-elles une borne utile sur N_0(d) ?

**Pourquoi c'est potentiellement différent** : Les bornes de Baker exploitent les propriétés TRANSCENDANTALES de log 2 et log 3 (leur indépendance sur Q). Aucun round précédent n'a utilisé d'argument de transcendance ou de théorie des formes linéaires de logarithmes. C'est un cadre QUALITATIVEMENT NOUVEAU.

### Trois sous-directions

1. **Baker direct** : utiliser la borne inférieure sur d pour contraindre corrSum. Si d est "assez grand", le nombre de multiples de d dans l'intervalle est "assez petit". MAIS : NBG a montré que ce nombre est ~3^k/2, donc Baker direct est probablement trop faible.

2. **Fractions continues de log₂ 3** : l'approximation rationnelle de log₂ 3 contrôle les valeurs S/k pour lesquelles d = 2^S - 3^k est petit. Les convergents p_n/q_n de log₂ 3 donnent les "meilleures" paires (S,k). Peut-on montrer que pour ces paires, la structure de corrSum est plus contrainte ?

3. **p-adique** : les valuations p-adiques de d (pour p ∤ 6) contrôlent quels premiers divisent d. L'ordre de 2 modulo ces premiers est lié à la structure de ⟨2⟩. Les bornes de Baker dans le cadre p-adique pourraient être exploitables.

### Condition de non-boucle

R80 doit soit montrer que Baker/fractions continues apportent une information exploitable, soit les déclasser proprement.

---

## 20. Risques / limites

1. **Les bornes de Baker pourraient être trop faibles** : la borne |2^S - 3^k| > exp(-Ck log k) donne d >> 1 (d n'est pas trop petit), mais le nombre de multiples de d dans l'intervalle des corrSum est ~3^k/2 >> d. Baker ne suffirait donc pas à réduire ce nombre à 0.

2. **L'indépendance multiplicative est un fait QUALITATIF** (2^a ≠ 3^b) qui pourrait ne pas se transformer en argument QUANTITATIF (combien de compositions donnent corrSum ≡ 0 mod d).

3. **Le programme accumule des rounds de diagnostic sans percée** : R73 (fermeture analytique), R74 (SAMC), R75 (SAMC sans compression), R76 (autopsie causale), R77 (multiplicatif sans compression), R79 (cause source sans objet). Six rounds de clarification. Le plateau est réel.

4. **La cause source identifiée pourrait être correcte mais INUTILE** : "le problème est dur parce que corrSum et d partagent 2 et 3" est un diagnostic vrai mais qui pourrait ne pas mener à un objet. La distinction "comprendre ≠ résoudre" est réelle.

5. **Le recours à Baker/transcendance serait un changement radical de domaine** : le programme est jusqu'ici resté dans la théorie additive/multiplicative des nombres et la combinatoire. Passer à la théorie des formes linéaires de logarithmes serait un saut considérable.

---

## 21. Verdict final avec score /10

**Score : 9/10**

R79 accomplit pleinement sa mission d'investigation radicale :

1. Carte hiérarchique complète source → mécanisme → symptôme (✅ PASS-1)
2. Filtre anti-étage : interface somme-produit reclassée mécanisme, F_p reclassée symptôme (✅ PASS-2)
3. Deux objets proposés, pas plus (✅ PASS-3)
4. DMAR et NBG testés : rebranding et réfuté respectivement (✅ PASS-4)
5. Décision honnête : innovation SUSPENDUE, pas de fausse percée (✅ PASS-5)
6. Direction unique pour R80 : Baker/indépendance multiplicative (✅ PASS-6)

**Score PASS : 6/6**

| Critère | Statut |
|---------|--------|
| PASS-1 : Carte hiérarchique complète | ✅ Source → 3 mécanismes → symptômes |
| PASS-2 : Filtre anti-étage intermédiaire | ✅ Interface add/mult reclassée, F_p reclassée |
| PASS-3 : Au plus 2 objets minimaux | ✅ DMAR et NBG (enterrés) |
| PASS-4 : Lemme + réfutation par objet | ✅ DMAR = rebranding, NBG = réfuté |
| PASS-5 : Décision stratégique honnête | ✅ Suspension de l'innovation |
| PASS-6 : Survivant unique pour R80 | ✅ Baker/indépendance multiplicative |

Point manquant pour 10 : aucun objet nouveau ne survit. Le 9 reflète la qualité du diagnostic (cause source identifiée, hiérarchie clarifiée, innovation honnêtement suspendue) malgré l'absence de percée.

---

## 22. Registre FAIL-CLOSED

| Objet | Statut |
|-------|--------|
| Auto-référence arithmétique | [CAUSE SOURCE CRÉDIBLE] — corrSum et d partagent (2,3) |
| Carte causale hiérarchique | [FORTEMENT ÉTAYÉ] — source → 3 mécanismes → symptômes |
| DMAR (Déficit Modulaire Auto-Référent) | [RÉFUTÉ — rebranding] — reformulation du problème original |
| NBG (Noyau Bi-Géométrique) | [RÉFUTÉ] — max corrSum / d ≈ 3^k / 2 |
| Interface add/mult (R77) | [MÉCANISME INTERMÉDIAIRE] — reclassée depuis R77 |
| F_p sans sous-groupes (R76) | [SYMPTÔME] — reclassée depuis R76 |
| Support O(log p) (R76) | [MÉCANISME INTERMÉDIAIRE] — reclassée depuis R76 |
| Monotonie | [FAUX VERROU — CONFIRMÉ] — 3e confirmation |
| Indépendance multiplicative 2/3 | [HEURISTIQUE] — direction R80, non testée |
| Bornes de Baker | [PROUVÉ] (littérature) — potentiellement exploitable |
| Fractions continues de log₂ 3 | [HEURISTIQUE] — sous-direction R80 |
| SER (R77) | [SEMI-FORMALISÉ] — retenu comme reformulation, pas programme |
| SAMC (R74) | [PROUVÉ] — reformulation correcte, cause source intégrée |
| Hypothèse H | [CONJECTURAL] — inchangé |
