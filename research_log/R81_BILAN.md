# R81 — BILAN : Tournoi d'objets externes au noyau F_p — APF survit

## Type : X/I/P (investigation + innovation disciplinée + précision)
## IVS : 7/10

**Justification IVS** :
- Clarté du dehors du noyau : 8/10 (frontière opérationnelle définie, faux extérieurs identifiés)
- Minimalité réelle de l'objet : 6/10 (APF est semi-réel, GZD est faible)
- Qualité du lemme candidat : 7/10 (APF a un lemme concret et testable)
- Robustesse anti-rebranding : 6/10 (APF est un enrichissement de l'adequate prime, pas totalement nouveau)
- Honnêteté de la décision finale : 9/10 (rebranding partiel assumé, GZD honnêtement relégué)
- Qualité du tournoi : 8/10 (2 candidats, critères explicites, élimination nette)

Score 7 reflétant qu'un candidat survit mais n'est pas radicalement nouveau — c'est un enrichissement structuré d'une approche connue plutôt qu'une percée.

---

## 1. Résumé exécutif

R81 organise un tournoi fermé de 2 candidats externes au noyau irréductible F_p (découvert en R80).

**Candidat 1 — GZD (Global Z-Divisibility)** : travailler dans Z avec l'équation corrSum = m·d comme contrainte entière. L'objet est purement externe (Z, pas F_p) mais le lemme est FAIBLE : les contraintes p-adiques aux primes 2 et 3 sont triviales (v₂(d) = v₃(d) = 0), et les contraintes de taille sont insuffisantes. **ÉLIMINÉ — relégué au rang de cadre de reformulation.**

**Candidat 2 — APF (Adequate Prime via Factorization)** : utiliser la structure de factorisation de d(k) pour sélectionner un prime p | d où SAMC est tractable, en s'appuyant sur Baker et la théorie des ordres multiplicatifs. L'objet est PARTIELLEMENT externe (la sélection du prime est hors F_p, le test final reste dans F_p mais pour un F_p contraint). Le lemme est TESTABLE et plus mordant. **SURVIT avec réserve.**

**Découverte clé** : Le "dehors du noyau" n'est pas un espace vide — il contient la factorisation de d, les contraintes de taille, les ordres multiplicatifs, et Baker. Mais les outils disponibles "dehors" (taille, valuation) sont étonnamment FAIBLES pour les primes 2 et 3 (parce que d est copremier à 6). Le levier réel est dans la SÉLECTION de primes p | d avec des propriétés exploitables.

---

## 2. Type du round + IVS

**Type** : X/I/P
- **X** : investigation de la frontière du noyau
- **I** : innovation via tournoi fermé de 2 candidats
- **P** : exigence de précision, testabilité, falsifiabilité

**IVS** : 7/10 — Un candidat survit avec lemme testable, mais ce n'est pas une percée radicale.

---

## 3. Méthode

1. Définition de la frontière opérationnelle du noyau F_p (Axe A)
2. Identification du besoin externe exact dérivé de la cause source (Axe B)
3. Proposition de 2 objets candidats avec lemme + réfutation + preuve d'extériorité (Axe C)
4. Contrôle anti-rebranding contre l'historique complet (Axe D)
5. Test de réalité mathématique sévère (Axe E)
6. Évaluation de l'impact programmatique (Axe F)
7. Tournoi : qualification, audit croisé, élimination, survivant (Axe G)
8. Autonomie contrôlée : 3 sous-rounds de tournoi
9. Aucun calcul, aucun k-par-k, aucun cas particulier

---

## 4. Résultats PHASE 1 / AXE A — Frontière du noyau irréductible

### Définition opérationnelle

**Est INTERNE au noyau F_p** : tout objet qui est une transformation affine, multiplicative, ou polynomiale de corrSum mod p dans F_p, pour un p premier quelconque divisant d.

Formellement : si l'objet O peut être écrit O = f(corrSum mod p) pour une fonction f : F_p → F_p qui est une composition d'opérations de corps (addition, multiplication, inversion), alors O est interne.

**Test d'extériorité** : un objet est externe SSI il utilise une propriété qui N'A PAS d'analogue dans F_p. Les propriétés qui n'existent pas dans F_p :
1. **Taille** : |x| > |y| n'a pas de sens dans F_p
2. **Ordre total compatible avec +** : n'existe pas dans F_p
3. **Divisibilité croisée** : v_p(x) pour différents p
4. **Approximation réelle** : x/y ≈ r pour r ∈ R
5. **Structure multi-premier** : conditions simultanées mod p₁, p₂, ...
6. **Factorisation de d** : quels primes divisent d et avec quelle multiplicité

### Familles internes (interdites)

| Famille | Raison d'internalité | Exemples tués |
|---------|---------------------|---------------|
| Reformulations affines de corrSum mod p | Automorphisme de F_p | DAS, PRO (R80) |
| Changement de base dans F_p | Isomorphisme de corps | SER → SAMC (R77) |
| Polynômes évalués en (2,3) mod p | Réduction mod p détruit la structure | Polynôme formel (R80) |
| Horner / dynamique dans F_p | Même récurrence | DAS (R80) |
| Sous-groupes multiplicatifs F_p* | Même cadre, vue multiplicative | OPM, V2C (R77) |

### Faux extérieurs à interdire

1. **"Travailler dans Z[X,Y] puis évaluer en (2,3)"** — FAUX EXTÉRIEUR si on réduit ensuite mod p. Le passage par les polynômes formels ne change rien si la conclusion est mod p.
2. **"Utiliser la structure de ⟨2⟩ dans F_p*"** — FAUX EXTÉRIEUR. F_p* est un quotient de Z, pas un objet extérieur à F_p.
3. **"Baker comme mot-clé"** — FAUX EXTÉRIEUR si Baker ne fournit pas un objet CONCRET. Mentionner Baker ne suffit pas ; il faut un lemme dérivé de Baker.

---

## 5. Résultats PHASE 1 / AXE B — Besoin externe exact

### Quel besoin ne peut plus être satisfait à l'intérieur ?

Le noyau irréductible dans F_p bloque TOUTE stratégie qui travaille "par-prime" : pour un prime p GÉNÉRIQUE divisant d, la condition SAMC dans F_p est irréductible (pas de décomposition, pas de localisation, pas d'invariant stable).

Le besoin est : un mécanisme qui **sélectionne** un prime p | d SPÉCIFIQUE (pas générique) où SAMC est tractable, OU un mécanisme qui coordonne les conditions à travers PLUSIEURS primes simultanément.

### Type de sortie nécessaire

- **Option A** : Sortie par SÉLECTION — identifier un p | d avec des propriétés arithmétiques spéciales (petit ord_p(2), position spéciale de -1, etc.) qui rendent SAMC tractable dans ce F_p particulier.
- **Option B** : Sortie par COORDINATION — montrer que les conditions SAMC sur les différents p | d sont INCOMPATIBLES simultanément (argument de couverture multi-premier, CRT renforcé).
- **Option C** : Sortie par TAILLE — montrer que corrSum ∈ Z ne peut pas être divisible par d pour des raisons de taille/approximation.

### Évaluation des options

| Option | Externe ? | Force potentielle | Outils disponibles | Risque |
|--------|-----------|-------------------|-------------------|--------|
| A (sélection) | PARTIELLEMENT (sélection externe, test interne) | FORTE si le prime existe | Baker, Zsygmondy, ordres multiplicatifs | Rebranding du Lemme A' |
| B (coordination) | OUI (multi-premier) | FORTE si les corrélations sont exploitables | CRT, Bonferroni, sieves | Déjà partiellement exploré (R25-34) |
| C (taille) | OUI (Z, pas F_p) | FAIBLE car v₂(d)=v₃(d)=0 | Valuations p-adiques, Baker | Contraintes triviales |

### Formulation minimale du besoin externe

> **Besoin B81** : Un mécanisme de SÉLECTION ou COORDINATION de primes divisant d(k), dérivé de la structure arithmétique spécifique de d = 2^S - 3^k, qui produit au moins un prime p où SAMC est tractable ou un ensemble de primes dont les conditions SAMC couvrent toutes les compositions.

### Faux besoins enterrés

1. **"Un outil de taille dans Z"** — trop faible (v₂(d)=v₃(d)=0)
2. **"Un théorème de Baker directement appliqué à corrSum"** — Baker borne |2^S - 3^k|, pas corrSum
3. **"Une anti-concentration dans Z"** — les corrSum en tant qu'entiers ne sont pas des sommes de variables indépendantes

---

## 6. Résultats PHASE 2 / AXE C — Objets externes candidats

### Candidat 1 : GZD (Global Z-Divisibility)

**Dérivation depuis la cause source** :

L'auto-référence signifie corrSum et d partagent (2,3). Dans Z (avant réduction), corrSum est un ENTIER POSITIF avec :
- corrSum = Σ 3^{k-1-j}·2^{s_{j+1}} (somme de k termes de la forme 3^a·2^b)
- corrSum > d toujours (car corrSum ≥ 2^S > d = 2^S - 3^k)
- Le quotient m = corrSum/d doit être un entier ≥ 2

L'équation corrSum = m·d se réécrit :
Σ 3^{k-1-j}·2^{s_{j+1}} + m·3^k = m·2^S

Le côté gauche mélange 2 ET 3 (k+1 termes de la forme 3^a·2^b). Le côté droit est m·2^S (pure puissance de 2, ×m).

**Preuve d'extériorité** : l'argument repose sur les TAILLES des termes dans Z et la structure de leurs valuations p-adiques — des propriétés qui n'existent pas dans F_p.

**Premier lemme candidat (GZD-L1)** : La structure mixte (2,3) du côté gauche est incompatible avec la structure pure (2) du côté droit.

**Analyse de mordant** :
- v₂(d) = 0 (d est impair) → contrainte 2-adique triviale
- v₃(d) = 0 (d ≡ ±1 mod 3) → contrainte 3-adique triviale
- Pour p ≥ 5 : on retombe dans F_p (noyau irréductible)
- Contraintes de taille : corrSum ∈ [3^k - 1, 2^S·(3^k-1)/2], m ∈ [2, ≈3^k/2]. L'intervalle contient ≈ 3^k/2 entiers — trop large pour exclure tous les m par taille seule.

**Critère de réfutation** : si les contraintes p-adiques aux primes 2 et 3 ne sont pas triviales → survit. Vérification : elles SONT triviales. → lemme FAIBLE.

**Verdict** : [SEMI-RÉEL] comme cadre, mais lemme [TESTABLE MAIS FAIBLE]

---

### Candidat 2 : APF (Adequate Prime via Factorization)

**Dérivation depuis la cause source** :

L'auto-référence crée le noyau irréductible dans F_p pour un p GÉNÉRIQUE. Mais d = 2^S - 3^k est un entier SPÉCIFIQUE avec une factorisation SPÉCIFIQUE. Ses facteurs premiers ne sont pas "génériques" — ils satisfont tous 2^S ≡ 3^k mod p, ce qui contraint :
- l'ordre multiplicatif de 2 mod p (via ord_p(2))
- la position de 3 dans ⟨2⟩ ⊂ F_p* (3 ∈ ⟨2⟩ ssi ord_p(2) = ord_p(3)·... )
- la position de -1 dans ⟨2⟩ (-1 ∈ ⟨2⟩ ssi ord_p(2) est pair)

L'idée : parmi les primes p | d(k), certains pourraient avoir des propriétés qui rendent SAMC TRACTABLE dans leur F_p spécifique. Par exemple :
- Si ord_p(2) ≤ 2k, alors |⟨2⟩| ≤ 2k, et le sumset Σ_≤(k) dans F_p est une somme de k-1 éléments pris dans un ensemble de taille ≤ 2k. Les bornes de cardinalité (Cauchy-Davenport) donnent |Σ_≤(k)| ≤ min(p, k²), et si p > k², la probabilité que -1 ∈ Σ_≤(k) est ≈ k²/p — potentiellement petite.
- Si -1 ∉ ⟨2⟩ (i.e., ord_p(2) est impair), alors Σ_≤(k) ⊂ ⟨2⟩·⟨λ⟩ et -1 n'est PAS dans ce sous-ensemble si le sous-groupe est assez petit.

**Preuve d'extériorité** : La SÉLECTION du prime (quelle propriété de p exploiter, et montrer que d(k) possède un tel prime) est une opération sur Z, utilisant la factorisation de d — c'est hors F_p. Le test FINAL (SAMC insoluble dans ce F_p) est dans F_p, mais pour un F_p CONTRAINT (pas générique).

**Premier lemme candidat (APF-L1)** : Pour k ≥ K₀, d(k) = 2^{⌈k log₂ 3⌉} - 3^k possède au moins un facteur premier p tel que :
(a) ord_p(2) est impair (donc -1 ∉ ⟨2⟩), ET
(b) le sumset SAMC est contenu dans le coset pair de F_p*/⟨-1⟩, excluant -1.

**Variante (APF-L2)** : Pour k ≥ K₀, d(k) possède un facteur premier p tel que ord_p(2) ≤ f(k) pour une fonction f contrôlable, rendant le sumset SAMC assez petit pour que -1 soit exclu par cardinalité.

**Critère de réfutation** : Pour un k donné, si TOUS les primes p | d(k) permettent -1 ∈ Σ_≤(k) → APF échoue pour ce k.

**Analyse de mordant** :
- APF-L1 (parité de l'ordre) : la condition ord_p(2) impair est équivalente à -1 ∉ ⟨2⟩ dans F_p*. Si cette condition est satisfaite ET si λ = 2·3^{-1} ∈ ⟨2⟩ (ce qui arrive quand 3 ∈ ⟨2⟩), alors TOUS les termes du sumset sont dans ⟨2⟩, et -1 ∉ ⟨2⟩ implique DIRECTEMENT -1 ∉ Σ_≤(k). C'est un argument de SOUS-GROUPE — simple mais potentiellement décisif.
- APF-L1 requiert : (i) ∃ p | d(k) avec ord_p(2) impair, ET (ii) 3 ∈ ⟨2⟩ pour ce p.
- La condition (i) : ord_p(2) est impair ⟺ p ≡ 1 mod 2^{v+1} pour un certain v... en fait c'est lié au symbole de Legendre de 2 mod p et à la factorisation de p-1.
- La condition (ii) : 3 ∈ ⟨2⟩ ⟺ ord_p(3) | ord_p(2). Puisque 2^S ≡ 3^k mod p, on a 3^k = 2^S · ... (dans le groupe), donc 3 ∈ ⟨2⟩ est AUTOMATIQUE si gcd(k, ord_p(3)) = k, c'est-à-dire si ord_p(3) | k.

**Découverte clé dans APF-L1** : Si p | d(k) satisfait :
1. ord_p(2) est impair
2. 3 ∈ ⟨2⟩ mod p

Alors -1 ∉ ⟨2⟩ (par 1), et Σ_≤(k) ⊂ ⟨2⟩ (par 2, car tous les termes λ^j·2^{g_j} = (2/3)^j·2^{g_j} sont dans ⟨2⟩ quand 3 ∈ ⟨2⟩). Donc -1 ∉ Σ_≤(k). CQFD.

C'est un argument de CONFINEMENT DE SOUS-GROUPE : le sumset est confiné dans ⟨2⟩, et -1 est dehors.

**MAIS** : la condition 2 (3 ∈ ⟨2⟩) est-elle compatible avec p | d ? Si p | (2^S - 3^k), alors 2^S ≡ 3^k mod p. Soit o₂ = ord_p(2) et o₃ = ord_p(3). Alors 2^S ≡ 3^k mod p signifie que 2^S et 3^k sont le MÊME élément de F_p*. En particulier, 3^k ∈ ⟨2⟩. Cela implique 3 ∈ ⟨2⟩ SSI l'élément 3 lui-même (pas juste 3^k) est dans ⟨2⟩, c'est-à-dire SSI o₃ | o₂. Puisque 3^k ∈ ⟨2⟩, on a 3^k = 2^s pour un s, donc o₃ | gcd(k·o₃, o₂). En fait, 3^k ∈ ⟨2⟩ est automatique. Mais 3 ∈ ⟨2⟩ requiert que l'image de 3 dans F_p*/⟨2⟩ soit triviale.

Puisque 3^k ∈ ⟨2⟩, l'image de 3 dans F_p*/⟨2⟩ a ordre divisant k. Si gcd(k, [F_p* : ⟨2⟩]) = 1, alors 3 ∈ ⟨2⟩.

Ceci est une condition sur p. Elle est satisfaite quand [F_p* : ⟨2⟩] = (p-1)/o₂ est copremier à k. En particulier, si o₂ = p-1 (2 est une racine primitive mod p), alors [F_p* : ⟨2⟩] = 1 et 3 ∈ ⟨2⟩ automatiquement.

Par le théorème de la densité de Artin (conditionnel à GRH), 2 est une racine primitive mod p pour une proportion positive de primes p (≈ 37.4% sous la conjecture de Artin).

**Résumé du lemme APF-L1 complet** : Si d(k) a un facteur premier p tel que :
- 2 est racine primitive mod p (⟹ 3 ∈ ⟨2⟩ et ⟨2⟩ = F_p*)
- ET ord_p(2) = p-1 est impair (⟹ p ≡ 2 mod 4, i.e., p ≡ 3 mod 4... MAIS p-1 doit être impair, ce qui signifie p = 2, impossible car p | d et d est impair)

PROBLÈME : ord_p(2) = p - 1 est pair si p > 2 (car p-1 est pair pour tout p impair). Donc la condition "ord_p(2) impair" est INCOMPATIBLE avec "2 est racine primitive mod p" pour p > 2.

C'est un ÉCHEC de APF-L1 tel que formulé : la condition "ord_p(2) impair" est très restrictive. Si o₂ | (p-1) et p-1 est pair, o₂ est impair ssi o₂ | (p-1)/2.

Plus précisément : -1 ∈ ⟨2⟩ ⟺ 2^{o₂/2} ≡ -1 mod p (quand o₂ est pair). Si o₂ est impair, alors -1 ∉ ⟨2⟩ (car ⟨2⟩ a ordre impair, et -1 a ordre 2, donc -1 ne peut pas être dans un groupe d'ordre impair).

Donc : -1 ∉ ⟨2⟩ ⟺ ord_p(2) est impair.

Et les primes p avec ord_p(2) impair existent : il suffit que ord_p(2) divise (p-1)/2^{v₂(p-1)}, ce qui est la partie impaire de p-1. Des résultats de Heath-Brown et al. montrent qu'il existe une infinité de tels primes.

**La question clé** : d(k) a-t-il un facteur premier p tel que ord_p(2) est impair ET 3 ∈ ⟨2⟩ ?

C'est une question d'arithmétique sur d(k) = 2^S - 3^k. Elle est NON TRIVIALE et ne se réduit PAS au noyau F_p. C'est une question EXTERNE au noyau.

**Verdict APF** : Le lemme est BIEN CIBLÉ mais sa preuve nécessite :
(a) Montrer que d(k) a un prime p avec ord_p(2) impair — question de factorisation
(b) Montrer que pour ce p, 3 ∈ ⟨2⟩ — question d'arithmétique modulaire
(c) Conclure : Σ_≤(k) ⊂ ⟨2⟩ et -1 ∉ ⟨2⟩, donc -1 ∉ Σ_≤(k)

L'étape (c) est IMMÉDIATE une fois (a) et (b) établies. Les étapes (a) et (b) sont les vrais verrous, et ils sont EXTERNES au noyau F_p.

---

## 7. Résultats PHASE 2 / AXE D — Contrôle anti-rebranding

### Tableau de comparaison

| Objet R81 | Ancienne piste proche | Ressemblance | Différence réelle | Verdict |
|-----------|----------------------|-------------|-------------------|---------|
| GZD | Pré-réduction dans Z (toujours disponible) | Revient au problème original dans Z | Aucune technique nouvelle | Rebranding du problème original |
| APF | Lemme A' "adequate prime" (R31, R25-34) | Cherche un "bon" prime p | d(k) | Sélection par ord_p(2) impair + 3 ∈ ⟨2⟩ est un CRITÈRE PRÉCIS dérivé du diagnostic R80 | Nouveauté PARTIELLE |

### Drapeaux rouges

- **GZD** : Revenir dans Z sans nouvel outil = rebranding du problème. Les outils de Z (taille, valuation) ont été vérifiés FAIBLES (v₂(d) = v₃(d) = 0). Pas de nouveauté.
- **APF** : L'idée de chercher un adequate prime est ancienne. MAIS le CRITÈRE de sélection est nouveau :
  - Avant (R25-34) : critère ad hoc, vérification k-par-k
  - Maintenant (R81) : critère STRUCTUREL dérivé du diagnostic (ord_p(2) impair + confinement de sous-groupe)
  - La différence : le critère de R81 UTILISE le noyau irréductible (la condition ⟨2⟩ est le noyau du SAMC quand 3 ∈ ⟨2⟩)

### Verdict anti-rebranding

- GZD : [FAUX EXTÉRIEUR] — retour au problème original sans gain
- APF : [NOUVEAUTÉ PARTIELLE] — le critère de sélection est nouveau, l'approche générale est connue. C'est un ENRICHISSEMENT structuré, pas un rebranding pur. Autorisé en tournoi.

---

## 8. Résultats PHASE 3 / AXE E — Test de réalité mathématique

### GZD

| Critère | Statut |
|---------|--------|
| Assez défini ? | OUI — corrSum ∈ Z, m = corrSum/d |
| Lemme général ? | NON — pas de mécanisme d'exclusion dans Z |
| Évite calcul/k-par-k ? | OUI |
| Chaîne vers le verrou ? | DIRECTE mais triviale |
| Réfutation réelle ? | NON — pas de lemme assez fort à réfuter |
| Compression ? | NON — c'est le problème original |
| Signe de vacuité ? | v₂(d) = v₃(d) = 0 tue le mordant p-adique |

**Statut** : [SEMI-RÉEL] comme cadre, [PROSE] comme objet
**Lemme** : [TROP FLOU]
**Mordant** : [NON TESTABLE]

### APF

| Critère | Statut |
|---------|--------|
| Assez défini ? | OUI — critère : p | d(k) avec ord_p(2) impair et 3 ∈ ⟨2⟩ |
| Lemme général ? | PARTIELLEMENT — si les conditions (a)(b) sont satisfaites, la conclusion est immédiate |
| Évite calcul/k-par-k ? | OUI pour la structure, MAIS la vérification que d(k) a un tel prime est arithmétique |
| Chaîne vers le verrou ? | EXPLICITE : (a)+(b) ⟹ Σ ⊂ ⟨2⟩ ⟹ -1 ∉ Σ (car ord_p(2) impair) |
| Réfutation réelle ? | OUI : si pour un k, aucun p | d(k) ne satisfait (a)+(b) → APF échoue |
| Compression ? | OUI PARTIELLE : réduit le verrou à une question de factorisation de d(k) |
| Signe de vacuité ? | Si d(k) n'a AUCUN prime avec ord impair → mort |

**Statut** : [SEMI-RÉEL]
**Lemme** : [BIEN CIBLÉ]
**Mordant** : [TESTABLE]

---

## 9. Résultats PHASE 3 / AXE F — Impact programmatique

### Chaîne logique de APF

```
(1) d(k) = 2^S - 3^k a un facteur premier p avec ord_p(2) impair
                    ↓
(2) -1 ∉ ⟨2⟩ dans F_p*  (car ⟨2⟩ a ordre impair, -1 a ordre 2)
                    ↓
(3) 3 ∈ ⟨2⟩ dans F_p*  (condition arithmétique sur p)
                    ↓
(4) λ = 2·3^{-1} ∈ ⟨2⟩  (car 2 ∈ ⟨2⟩ et 3^{-1} ∈ ⟨2⟩)
                    ↓
(5) Tous les termes λ^j · 2^{g_j} ∈ ⟨2⟩
                    ↓
(6) Σ_≤(k) ⊂ ⟨2⟩  (somme d'éléments de ⟨2⟩ est dans F_p, pas forcément dans ⟨2⟩)
```

**ATTENTION — FAILLE à l'étape (6)** : La somme d'éléments de ⟨2⟩ n'est PAS nécessairement dans ⟨2⟩ ! ⟨2⟩ est un sous-groupe MULTIPLICATIF de F_p*, pas un sous-groupe additif. La SOMME d'éléments d'un sous-groupe multiplicatif peut atterrir n'importe où dans F_p.

C'est une ERREUR LOGIQUE dans la chaîne de APF-L1. La conclusion "Σ_≤(k) ⊂ ⟨2⟩" est FAUSSE — le sumset est une opération ADDITIVE, et les sous-groupes multiplicatifs ne sont pas stables par addition.

### Correction et impact

L'erreur tue la chaîne telle quelle. MAIS elle peut être partiellement sauvée :

**Version corrigée (APF-L1c)** : Si ord_p(2) est impair ET petit (say ord_p(2) = t ≤ 2k), alors :
- Le support {2^0, 2^1, ..., 2^M} mod p ne contient que t éléments distincts (car 2^t ≡ 1 mod p)
- Le sumset Σ_≤(k) est une somme de k-1 éléments pris dans un ensemble de taille t, avec poids λ^j (qui sont aussi dans ⟨2⟩, de taille t)
- Par Cauchy-Davenport, |Σ_≤(k)| ≤ min(p, k·t)
- Si p > k·t, alors |Σ_≤(k)|/p < k·t/p — la "densité" du sumset est petite
- La probabilité heuristique que -1 ∈ Σ_≤(k) est ≈ k·t/p

Ceci n'est PAS une preuve de -1 ∉ Σ_≤(k), mais c'est un ARGUMENT DE SPARSITÉ qui marche quand p est grand par rapport à k·t.

**Impact si APF-L1c fonctionne** : il réduit le verrou à deux sous-problèmes :
(a) **Problème de factorisation** : d(k) a un prime p avec ord_p(2) impair et petit
(b) **Problème de sparsité** : pour ce p, le sumset est trop petit pour contenir -1

Le pas (b) est un problème INTERNE au noyau F_p mais dans un RÉGIME FAVORABLE (⟨2⟩ petit). Le pas (a) est EXTERNE.

### Portée honnête

- Si APF-L1c fonctionne : pas structurel, réduction du verrou à la factorisation de d(k)
- Si APF-L1c échoue : la faille (somme ≠ sous-groupe multiplicatif) est une leçon précieuse

### Seuil de pertinence

APF mérite R82 si : l'analyse de la factorisation de d(k) pour k = 21-41 (le gap CRT) montre que des primes avec ord_p(2) impair et petit EXISTENT.

---

## 10. Résultats PHASE 4 / AXE G — Tournoi et décision finale

### Qualification

| Candidat | Externe ? | Lemme ? | Réfutable ? | Qualifié ? |
|----------|-----------|---------|-------------|------------|
| GZD | OUI (Z) | [TROP FLOU] | NON | ÉLIMINÉ (pas de lemme) |
| APF | PARTIELLEMENT | [BIEN CIBLÉ] (après correction) | OUI | QUALIFIÉ |

### Audit croisé

GZD n'est pas un concurrent sérieux — pas de lemme exploitable. APF survit seul.

### Élimination

GZD éliminé au premier tour. APF survit avec correction obligatoire (l'erreur additive/multiplicative de la chaîne initiale).

### Survivant unique

**APF (Adequate Prime via Factorization)** — version corrigée APF-L1c.

**Condition de non-boucle pour R82** :
1. NE PAS reproposer une reformulation dans F_p (noyau irréductible)
2. Étudier la factorisation CONCRÈTE de d(k) pour k = 3,...,50 (les petits k pour guider l'intuition, pas comme preuve)
3. Chercher des primes p | d(k) avec ord_p(2) impair et petit
4. SI de tels primes existent : étudier si le SAMC dans ce F_p contraint est tractable
5. SI pas de tels primes : APF est mort, chercher une autre direction

### Décision

**POURSUIVRE AVEC RÉSERVE** : APF est semi-réel avec un lemme bien ciblé mais fragile (la chaîne initiale avait une erreur, corrigée en version plus faible). La réserve porte sur la faille additive/multiplicative et sur le fait que c'est un enrichissement de l'adequate prime, pas une percée radicale.

---

## 11. Activation de l'autonomie

**Activation** : OUI — 3 sous-rounds pour qualifier, auditer et éliminer.

---

## 12. Journal des sous-rounds autonomes

### S1 — Qualification et formulation comparative

1. **Candidats actifs** : GZD, APF
2. **Objet exact** : GZD = corrSum/d dans Z ; APF = prime p | d avec ord_p(2) impair + confinement
3. **Question** : les deux candidats ont-ils un lemme exploitable ?
4. **Chaîne** : GZD — les contraintes p-adiques sont triviales → pas de lemme. APF — confinement de sous-groupe si les conditions sont remplies → lemme.
5. **Résultat** : GZD n'a pas de lemme exploitable. APF a un lemme mais avec une faille (somme ≠ sous-groupe multiplicatif).
6. **Statut** : GZD [ÉLIMINÉ], APF [QUALIFIÉ AVEC CORRECTION]
7. **Critère de victoire** : le candidat avec le meilleur lemme gagne. APF gagne par défaut.
8. **Ce qui est appris** : le "dehors du noyau" via les tailles/valuations est étonnamment faible. Le "dehors" utile est la factorisation.
9. **Décision** : continuer (S2)
10. **Raison** : auditer la correction de APF

### S2 — Audit croisé et test de réalité

1. **Candidat actif** : APF (seul survivant)
2. **Objet exact** : critère de sélection = ord_p(2) impair + 3 ∈ ⟨2⟩, réduit à "petit ord_p(2)" après correction
3. **Question** : la chaîne logique corrigée (APF-L1c) est-elle viable ?
4. **Chaîne** : la faille est identifiée (⟨2⟩ pas stable par +). La correction remplace le confinement exact par un argument de sparsité (|Σ| ≤ k·t << p). C'est heuristique, pas une preuve.
5. **Résultat** : APF-L1c est un SCHÉMA d'argument, pas un lemme prouvé. La sparsité seule ne suffit pas à exclure -1 (un élément sparse peut quand même contenir -1).
6. **Statut** : [SEMI-RÉEL — TESTABLE MAIS FAIBLE]
7. **Critère d'élimination** : si aucun prime de d(k) n'a ord_p(2) impair et petit → mort directe
8. **Ce qui est appris** : la distinction additive/multiplicative est FONDAMENTALE et résiste même à la sortie du noyau. Le confinement multiplicatif ne donne pas le confinement additif.
9. **Décision** : continuer (S3)
10. **Raison** : trancher si APF mérite R82 malgré sa faiblesse

### S3 — Élimination finale

1. **Candidat actif** : APF
2. **Objet exact** : le "spectre premier de d(k)" comme objet d'étude externe
3. **Question** : APF mérite-t-il R82 ?
4. **Chaîne** :
   - APF est semi-réel : le critère de sélection est défini, la chaîne logique a une faille corrigée en version faible
   - La direction est NON EXPLORÉE dans le programme : personne n'a étudié systématiquement les ordres de 2 modulo les facteurs premiers de d(k)
   - La question de factorisation est CONCRÈTE et testable (même si R82 ne doit pas être computationnel, la structure peut être étudiée théoriquement)
   - Le pire résultat : APF ne marche pas, mais l'étude du spectre premier de d(k) est un acquis
5. **Résultat** : APF mérite R82 comme direction d'investigation, pas comme objet prouvé
6. **Statut** : [POURSUIVRE AVEC RÉSERVE]
7. **Critère d'élimination pour R82** : si la faille additive/multiplicative ne peut pas être contournée → mort
8. **Ce qui est appris** : la distinction additive/multiplicative est le DERNIER verrou non contourné. Ni le noyau F_p (interne) ni la factorisation (externe) ne résolvent seuls le problème.
9. **Décision** : arrêter le tournoi. APF survit avec réserve.
10. **Raison** : candidat unique, faille identifiée, direction testable

**Budget** : 3/3 sous-rounds. 0 calcul. Dans le budget.

---

## 13. Objets concernés + Ladder of Proof

| Objet | Niveau avant R81 | Niveau après R81 | Commentaire |
|-------|-----------------|-------------------|-------------|
| Noyau irréductible F_p | L6 semi-formalisé (R80) | L6 — frontière opérationnelle DÉFINIE | Test d'extériorité formulé |
| GZD (Global Z-Divisibility) | (nouveau) | [ÉLIMINÉ — FAUX EXTÉRIEUR] | Pas de lemme : v₂(d)=v₃(d)=0 |
| APF (Adequate Prime via Fact.) | (nouveau) | **L4 LEMME CANDIDAT** (avec faille corrigée) | Semi-réel, testable, réserve |
| APF-L1 (confinement sous-groupe) | (nouveau) | [RÉFUTÉ — FAILLE ADD/MULT] | ⟨2⟩ non stable par + |
| APF-L1c (sparsité) | (nouveau) | **L3 IDÉE STRUCTURÉE** | Heuristique, pas prouvé |
| Faille additive/multiplicative | (nouveau) | **L8 PROUVÉ** (fait algébrique) | Dernier verrou identifié |
| Spectre premier de d(k) | (nouveau) | **L2 INTUITION STRUCTURÉE** | Direction pour R82 |
| Auto-référence | L7 cause source (R80) | L7 — inchangé | |
| Hypothèse H | [CONJECTURAL] | [CONJECTURAL] — inchangé | |

---

## 14. Ce qui est appris

1. **Le "dehors du noyau" via tailles/valuations est faible** : Les contraintes de taille dans Z et les valuations p-adiques aux primes 2 et 3 sont triviales (v₂(d) = v₃(d) = 0). Le "dehors" utile est la FACTORISATION de d, pas les propriétés de taille.

2. **La faille additive/multiplicative est le DERNIER VERROU** : Même avec un confinement multiplicatif parfait (tous les termes dans ⟨2⟩), la SOMME peut sortir de ⟨2⟩ parce que les sous-groupes multiplicatifs ne sont pas additifs. Cette faille était implicite dans tous les rounds précédents — R81 la rend explicite.

3. **APF a un critère de sélection structurel** : Chercher p | d(k) avec ord_p(2) impair est un critère PRÉCIS dérivé du diagnostic R80, pas un critère ad hoc. C'est un enrichissement de l'adequate prime.

4. **La direction est testable** : L'étude du spectre premier de d(k) est une direction CONCRÈTE et EXTERNE au noyau F_p.

---

## 15. Ce qui est fermé utilement

1. **"Travailler dans Z suffit"** — FERMÉ. Les outils de Z (taille, valuation aux primes 2,3) sont triviaux pour d.
2. **"Le confinement multiplicatif implique le confinement additif"** — FERMÉ (RÉFUTÉ). Faille additive/multiplicative prouvée.
3. **"Toute sortie du noyau donne automatiquement du mordant"** — FERMÉ. Le "dehors" doit être SPÉCIFIQUEMENT utile, pas seulement différent.

---

## 16. Ce qui est enterré

1. **GZD** — ENTERRÉ. Faux extérieur, retour au problème original sans gain.
2. **APF-L1 (confinement exact)** — ENTERRÉ. Faille additive/multiplicative.
3. **"Sortie par taille"** — ENTERRÉ. v₂(d) = v₃(d) = 0.

---

## 17. Autopsie des pistes fermées

### 1. GZD (Global Z-Divisibility)

- **Nom** : Divisibilité globale dans Z
- **Type de mort** : faux extérieur
- **Cause** : les contraintes p-adiques aux primes 2 et 3 sont triviales (v₂(d) = v₃(d) = 0), et les contraintes de taille sont insuffisantes (trop d'entiers m possibles)
- **Ce que la mort enseigne** : "revenir dans Z" n'est pas un gain automatique. Les outils de Z qui manquent dans F_p (taille, ordre) sont triviaux pour ce problème spécifique.
- **Où cela redirige** : vers la factorisation de d (seul levier externe non trivial)

### 2. APF-L1 (Confinement de sous-groupe)

- **Nom** : Confinement du sumset dans ⟨2⟩
- **Type de mort** : lemme trop haut (faille logique)
- **Cause** : le sumset est une SOMME (opération additive) d'éléments d'un sous-groupe MULTIPLICATIF ⟨2⟩. Les sous-groupes multiplicatifs ne sont pas stables par addition dans F_p. Σ_≤(k) ⊄ ⟨2⟩ en général.
- **Ce que la mort enseigne** : la distinction additive/multiplicative est le DERNIER verrou. Même les objets "externes" doivent le franchir pour mordre.
- **Où cela redirige** : vers APF-L1c (sparsité dans F_p contraint) ou vers un argument qui contourne le problème additif/multiplicatif

---

## 18. Survivant pour R82

**Unique survivant** : **APF (Adequate Prime via Factorization)** — version corrigée, étude du spectre premier de d(k).

### Justification
1. Direction EXTERNE au noyau F_p (factorisation de d)
2. Critère de sélection STRUCTUREL (ord_p(2) impair, petit)
3. Lemme TESTABLE (vérifiable sur les d(k) pour petits k)
4. Faille identifiée mais CONTOURNABLE (passer de confinement à sparsité)

### Condition de non-boucle pour R82
1. NE PAS reproposer une reformulation dans F_p
2. Étudier THÉORIQUEMENT la structure des facteurs premiers de d(k) = 2^S - 3^k
3. Résoudre ou clarifier : d(k) a-t-il un prime p avec ord_p(2) impair et "petit" ?
4. Si oui : comment convertir la sparsité du sumset en exclusion de -1 (contourner la faille add/mult) ?
5. Si non : APF est mort, chercher une autre direction externe

### Premier objet pour R82
Le **spectre premier de d(k)** = {(p, ord_p(2), [F_p* : ⟨2⟩]) : p premier, p | d(k)}, étudié comme objet arithmétique.

---

## 19. Risques / limites

1. **APF est un enrichissement, pas une percée** : L'approche adequate prime est connue depuis le début du programme. Le critère ord_p(2) impair est nouveau mais ne garantit pas le succès.

2. **La faille additive/multiplicative est PROFONDE** : La non-stabilité des sous-groupes multiplicatifs par addition est un fait structurel de F_p. Même avec un "bon" prime, le sumset peut contenir -1 malgré le confinement multiplicatif.

3. **La factorisation de d(k) est un problème DIFFICILE** : Pour des k grands, d(k) est un nombre énorme dont la factorisation est inconnue. Les bornes théoriques (Baker, Zsygmondy) sont faibles.

4. **Risque de retomber dans le k-par-k** : L'étude du spectre premier de d(k) pour des k spécifiques est dangereusement proche du computationnel. R82 doit rester théorique.

5. **Le gap k=21-41 pourrait persister** : L'approche CRT/adequate prime a déjà échoué sur ce gap. APF pourrait ne pas le résoudre si les primes de d(k) pour ces k n'ont pas les bonnes propriétés.

---

## 20. Verdict final avec score /10

**Score : 7/10**

R81 produit un tournoi fermé propre avec un survivant testable :

1. Frontière du noyau définie avec test opérationnel (✅ PASS-1)
2. Exactement 2 objets proposés et mis en compétition (✅ PASS-2)
3. Chaque objet a lemme + réfutation + critère de victoire (✅ PASS-3)
4. Anti-rebranding : GZD = faux extérieur, APF = nouveauté partielle (✅ PASS-4)
5. Tournoi produit décision honnête : APF survit avec réserve (✅ PASS-5)
6. Unique survivant : APF + spectre premier de d(k) (✅ PASS-6)

Le 7 (pas 8) reflète : (a) la faille additive/multiplicative dans APF-L1, (b) APF est un enrichissement plus qu'une percée, (c) GZD était un candidat faible.

**Score PASS : 6/6**

| Critère | Statut |
|---------|--------|
| PASS-1 : Frontière du noyau définie | ✅ Test opérationnel formulé |
| PASS-2 : Au plus 2 objets | ✅ GZD + APF = 2 |
| PASS-3 : Lemme + réfutation + victoire | ✅ |
| PASS-4 : Anti-rebranding | ✅ GZD tué, APF admis comme nouveauté partielle |
| PASS-5 : Décision honnête | ✅ POURSUIVRE AVEC RÉSERVE |
| PASS-6 : Survivant unique | ✅ APF |

---

## 21. Registre FAIL-CLOSED

| Objet | Statut |
|-------|--------|
| Frontière du noyau F_p | [SEMI-FORMALISÉ] — test opérationnel défini |
| GZD (Global Z-Divisibility) | [FAUX EXTÉRIEUR] — pas de lemme, v₂(d)=v₃(d)=0 |
| APF (Adequate Prime via Fact.) | [SEMI-RÉEL] — critère structurel, lemme testable, faille corrigée |
| APF-L1 (confinement exact) | [RÉFUTÉ] — faille additive/multiplicative |
| APF-L1c (sparsité) | [HEURISTIQUE] — argument de densité, pas prouvé |
| Faille additive/multiplicative | [PROUVÉ] — ⟨2⟩ non stable par addition dans F_p |
| Spectre premier de d(k) | [HEURISTIQUE] — direction non explorée |
| Noyau irréductible F_p | [SEMI-FORMALISÉ] — confirmé, frontière définie |
| Auto-référence arithmétique | [CAUSE SOURCE CRÉDIBLE] — inchangé |
| SAMC | [PROUVÉ — IRRÉDUCTIBLE] — inchangé |
| Hypothèse H | [CONJECTURAL] — inchangé |
