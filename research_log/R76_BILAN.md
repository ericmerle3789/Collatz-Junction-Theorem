# R76 — BILAN : Investigation causale profonde des blocages SAMC

## Type : X/P (investigation causale + exigence de précision)
## IVS : 9/10

**Justification IVS** :
- Profondeur de l'autopsie : 9/10 (trois autopsies causales complètes avec chaînes remontées jusqu'au mécanisme source)
- Clarté de la cause source : 9/10 (deux causes sources irréductibles identifiées et leur couplage expliqué)
- Réduction de l'espace des fausses innovations : 10/10 (monotonie innocentée, circularité ALO expliquée comme symptôme, trois faux besoins enterrés)
- Qualité du besoin conceptuel survivant : 8/10 (besoin formulé, premier objet identifié, mais non encore testé)
- Honnêteté des distinctions profond / contingent / faux verrou : 9/10 (tri rigoureux, découverte non triviale sur la contingence de CS1)

Score élevé pour un round de diagnostic : l'autopsie produit une **découverte actionnable** (la réduction mod p est le point de contingence, pas le problème lui-même).

---

## 1. Résumé exécutif

R76 autopsie causalement les trois mécanismes testés en R75 (GSE, ALO, RP) et identifie les causes sources du blocage :

**Deux causes sources irréductibles et couplées** :
1. **CS1 : F_p est un corps premier sans sous-groupes additifs non triviaux** — bloque toute stratégie de localisation du sumset. MAIS cette cause est **CONTINGENTE** au choix de réduire mod p premier. Travailler mod d (composite) ou dans Z changerait le paysage.
2. **CS2 : Le support P = {2^0,...,2^M} a O(log p) éléments** — place le problème exponentiellement en dessous du seuil p^δ requis par tous les outils harmoniques. Cette cause est **PROFONDE** et intrinsèque.

**Découverte clé** : La monotonie des compositions est un **FAUX VERROU** (explicitement innocentée). La circularité d'ALO est un **SYMPTÔME** du choix de travailler dans F_p, pas un obstacle indépendant.

**Besoin conceptuel survivant** : un **cadre de travail qui exploite la structure de corrSum AVANT la réduction complète dans F_p**, ou qui utilise la **structure multiplicative de F_p*** (le sous-groupe ⟨2⟩) plutôt que la structure additive de F_p.

**Premier objet pour R77** : la géométrie multiplicative de ⟨2⟩ dans F_p* — les distances multiplicatives, orbites sous ×λ, et structure de la map d'exponentiation discrète φ(g) = 2^g mod p.

---

## 2. Type du round + IVS

**Type** : X/P
- **X** : investigation causale profonde (autopsie des blocages)
- **P** : exigence de précision, chaînes causales complètes, testabilité des diagnostics

**IVS** : 9/10 — Round de diagnostic qui produit un résultat actionnable : le point de contingence est identifié, le faux verrou est innocenté, et le besoin conceptuel est formulé. Pas un 10 car le besoin n'est pas encore testé.

---

## 3. Méthode

1. Autopsie causale indépendante de chaque mécanisme (GSE, ALO, RP) — 5 questions obligatoires chacune
2. Fusion des trois autopsies pour localiser le mécanisme source
3. Examen de 8 dimensions (géométrie Σ_≤(k), monotonie, poids λ^j, réduction mod p, sous-groupes F_p, perte d'ordre, interaction additif/multiplicatif, échelle logarithmique)
4. Tri de chaque blocage en [PROFOND] / [CONTINGENT] / [LIÉ À LA FORMULATION] / [FAUX VERROU]
5. Extraction du besoin conceptuel par élimination
6. Aucun calcul, aucun k-par-k, aucun cas particulier

---

## 4. Résultats PHASE 1 / AXE A — Autopsie de GSE

### Chaîne causale complète

```
GSE contrôle la CARDINALITÉ de Σ_≤(k)  (information extensionnelle)
    ↓
Pour exclure -1, il faut la COMPOSITION  (information intensionnelle)
    ↓
Conversion cardinalité → composition requiert LOCALISATION
    ↓
Localisation requiert sous-structure additive dans F_p
    ↓
F_p n'a pas de sous-groupes additifs non triviaux  (corps premier)
    ↓
CONVERSION IMPOSSIBLE dans F_p
```

### Questions et réponses

1. **Type d'information contrôlé par GSE** : cardinalité (|Σ_≤(k)| ≤ C < p). Information de taille, pas de contenu.

2. **Information manquante** : localisation positionnelle — dans quelle "région" de F_p le sumset se trouve-t-il. Mais F_p n'a pas de régions.

3. **Source de la perte** : la symétrie de Cauchy-Davenport (|A+B| ≥ min(|A|+|B|-1, p)) qui ne préserve aucune information de position. Et l'impossibilité structurelle de définir des "régions" dans F_p (pas de sous-groupes additifs, pas d'intervalles compatibles avec l'addition).

4. **Axiome manquant** : un principe de localisation dans F_p — une structure W ⊊ F_p telle que Σ_≤(k) ⊂ W et -1 ∉ W. Inexistant dans F_p corps premier.

5. **Diagnostic** : [STRUCTUREL]. Conséquence de la transitivité de F_p sous translation : pour tout r, il existe une translation envoyant tout ensemble sur un ensemble contenant r.

---

## 5. Résultats PHASE 1 / AXE B — Autopsie de ALO

### Carte de circularité

```
Objectif : montrer N(-1) = 0
    ↓
Anti-concentration : montrer N(r) ≤ C/p pour tout r
    ↓
Fourier obligatoire dans F_p : N(r) = (1/p) Σ_t T(t) · ω^{-tr}
    ↓
Borner |T(t)| pour t ≠ 0
    ↓
T(t) se décompose en sommes sur ⟨2⟩ : F(c,L) = Σ e(c·2^n/p)
    ↓
|F(c,L)| avec L = O(log p) = PROBLÈME ORIGINAL (Lemme B')
    ↓
CIRCULARITÉ : l'objectif = la prémisse
```

### Point exact de rupture

La circularité naît à l'étape **"Fourier obligatoire dans F_p"**. Dans F_p, Fourier est L'UNIQUE outil pour convertir une question de valeur spécifique en question de distribution (complétude de la base de caractères). Et dans le domaine de Fourier, la complexité du problème (support doublement géométrique de taille O(log p)) traverse INTACTE.

### Propriété minimale requise pour éviter la boucle

Un mécanisme qui prouve N(-1) = 0 SANS passer par la distribution de T(t). C'est-à-dire : un argument structural direct sur l'image de σ qui exclut -1 par une propriété ALGÉBRIQUE ou COMBINATOIRE de l'image elle-même, pas de sa distribution.

### Diagnostic

Le défaut porte sur le **mauvais appariement outil/problème** : Fourier est un outil de DISTRIBUTION, mais le problème est un problème de CONTENU (quel point est dans l'image ?). Fourier transforme la question mais pas le support — d'où la circularité.

---

## 6. Résultats PHASE 1 / AXE C — Autopsie de RP

### Chaîne causale de non-fermeture

```
RP épluche le dernier terme : 2^{g_{k-1}} = (-1-s)/λ^{k-1}
    ↓
L'ensemble des sommes partielles s dépend de (g_1,...,g_{k-2}) monotone
    ↓
Cet ensemble change avec k (via M = S-k et les poids λ^j)
    ↓
Pour un invariant récursif, il faudrait P(S_j) stable en j ET en k
    ↓
P devrait caractériser la "forme" de S_j dans F_p
    ↓
F_p n'a pas de notion de "forme" pour les sous-ensembles
    ↓
INVARIANT IMPOSSIBLE dans F_p
```

### Invariant manquant

L'invariant nécessaire est un prédicat P(S_j) tel que :
- P(S_0) vrai (base)
- P(S_j) ∧ monotonie → P(S_{j+1}) (récurrence)
- P(S_{k-1}) → -1 non atteint (conclusion)

Ce prédicat devrait encoder une propriété des sous-ensembles de F_p qui se propage sous "ajout d'un terme λ^{j+1} · 2^g". Aucune propriété de ce type n'est connue dans F_p (pas de convexité, pas d'intervalles stables, pas de sous-groupes propres).

### Diagnostic

[BLOCAGE PLUS PROFOND]. RP échoue parce que le problème est **intrinsèquement non séquentialisable** dans F_p. La condition modulo p couple globalement tous les termes de la somme. C'est le même obstacle que GSE vu sous l'angle séquentiel.

---

## 7. Résultats PHASE 2 / AXE D — Mécanisme source

### Carte causale globale

```
CAUSE SOURCE 1 (CS1) : Réduction mod p premier
  └─→ F_p n'a pas de sous-groupes additifs non triviaux
       └─→ pas de localisation additive possible
            ├─→ GSE : taille sans contenu [BLOQUÉ]
            ├─→ RP : pas d'invariant stable [BLOQUÉ]
            └─→ ALO doit passer par Fourier
                 └─→ CAUSE SOURCE 2 (CS2) : Support de taille O(log p)
                      └─→ sommes exponentielles courtes hors régime
                           └─→ ALO circulaire [BLOQUÉ]
```

### Composantes

| Composant | Rôle | Justification |
|-----------|------|---------------|
| **Réduction mod p premier** | SOURCE PRINCIPALE | Détruit toute structure additive exploitable |
| **Support O(log p)** | SOURCE SECONDAIRE | Exponentiellement sous le seuil p^δ des outils harmoniques |
| Poids λ^j (géométriques) | Aggravant | Couplage multiplicatif, mais pas la cause source |
| Monotonie des g_j | **FAUX COUPABLE** | N'empêche ni ne crée le blocage |
| Interaction additif/multiplicatif | Aggravant | Domaine somme-produit, mais exige p^δ |
| Perte d'ordre après réduction | Conséquence de CS1 | Symptôme, pas cause |

### Résumé en une phrase

*Le blocage naît du couplage entre l'absence de structure additive non triviale dans F_p (pas de localisation) et la taille logarithmique du support (pas de borne harmonique), qui ensemble interdisent de convertir la sparsité de Σ_≤(k) en évitement spécifique de -1.*

### Faux coupable explicitement innocenté

**La monotonie des compositions** : La contrainte g_1 ≤ ... ≤ g_{k-1} réduit la cardinalité C mais ne crée pas l'obstacle de localisation. Le problème SANS monotonie (sumset libre dans F_p avec support de taille O(log p)) serait TOUT AUSSI DIFFICILE. Les innovations futures ne doivent PAS se concentrer sur "contourner la monotonie".

---

## 8. Résultats PHASE 3 / AXE E — Tri profond / contingent / faux verrou

| Blocage | Statut | Formulation-dépendant ? | Conséquence |
|---------|--------|------------------------|-------------|
| F_p sans sous-groupes | [PROFOND] dans F_p, [CONTINGENT] au choix de F_p | **OUI** | Changer de cadre pourrait lever ce blocage |
| Support O(log p) | [PROFOND] | NON — intrinsèque | Mais impact varie selon le cadre |
| Circularité ALO | [LIÉ À LA FORMULATION] | OUI — symptôme du choix F_p | Disparaît si on sort de F_p |
| Monotonie | [FAUX VERROU] | — | Innocentée explicitement |
| Poids λ^j | [CONTINGENT] | Partiellement | Aggravant non source |

### Découverte clé de Phase 3

R75 avait traité le blocage "F_p sans sous-groupes additifs" comme TERMINAL ("le programme a atteint la frontière des mathématiques"). L'autopsie R76 montre que ce blocage est **CONTINGENT AU CHOIX DE RÉDUIRE MOD p**. Le problème original porte sur corrSum ≡ 0 mod d où d est typiquement COMPOSITE. La réduction mod p est une DÉCISION DE MODÉLISATION, pas une contrainte du problème.

**R75 était trop terminal** : le diagnostic "frontière atteinte" était prématuré. Ce qui est atteint est la frontière des outils DANS F_p — pas la frontière du problème lui-même.

---

## 9. Résultats PHASE 4 / AXE F — Besoin conceptuel survivant

### Le besoin unique

**Un cadre de travail qui exploite la structure de corrSum AVANT ou AU-DELÀ de la réduction complète dans F_p.**

Ce cadre doit :
1. Préserver une notion de "position" ou "forme" des sous-ensembles (ce que F_p détruit) ;
2. Être assez structuré pour que l'évitement de -1 (ou de 0 mod d) soit tractable ;
3. Ne pas être k-par-k.

### Formulation minimale

> **Besoin B76** : Trouver un objet ou invariant intermédiaire entre Z et F_p qui capture assez d'information pour discriminer si -1 ∈ Σ_≤(k), sans requérir l'anti-concentration complète dans F_p.

### Trois incarnations possibles (classées)

| Rang | Forme | Description | Statut dans le programme |
|------|-------|-------------|--------------------------|
| 1 | **Géométrie multiplicative de ⟨2⟩** | Exploiter le sous-groupe ⟨2⟩ ⊂ F_p* et la map φ(g) = 2^g mod p comme structure géométrique | **NON EXPLORÉE** |
| 2 | **CRT composite renforcé** | Travailler mod d (pas mod p), exploiter les corrélations CRT entre facteurs | Partiellement explorée (R25-34), gap k=21-41 |
| 3 | **Invariants pré-réduction sur Z** | Exploiter les valuations p-adiques, la taille, l'ordre de corrSum AVANT réduction | Partiellement explorée (v_2, mod 12), trop grossier |

### Premier objet pour R77

**La map d'exponentiation discrète** φ : {0,1,...,M} → F_p* définie par φ(g) = 2^g mod p.

Question : la géométrie de l'image de φ (distances multiplicatives entre φ(g) et φ(g+1) = 2·φ(g), orbites sous multiplication par λ, structure du "chemin exponentiel" dans F_p*) porte-t-elle une information exploitable pour l'évitement de -1 dans le sumset ?

La clé : dans F_p*, la multiplication par 2 est un AUTOMORPHISME qui crée un "cercle discret" ⟨2⟩. Le sumset Σ_≤(k) est une somme pondérée d'éléments de ce cercle. La question de l'évitement de -1 est une question sur les SOMMES D'ÉLÉMENTS DU CERCLE — un objet géométrique.

### Faux besoins enterrés

1. **"Un meilleur outil d'anti-concentration dans F_p"** — ENTERRÉ. Tout outil dans F_p passe par Fourier (circularité). Le besoin n'est pas un meilleur outil DANS F_p, mais de SORTIR de F_p.

2. **"Un moyen de contourner la monotonie"** — ENTERRÉ. Faux verrou innocenté.

3. **"Des bornes de sommes exponentielles courtes plus fines"** — ENTERRÉ COMME BESOIN AUTONOME. Équivalent au problème original (circularité). Le besoin est de contourner cette nécessité.

---

## 10. Activation de l'autonomie

**Activation** : OUI — 3 sous-rounds pour fusionner les diagnostics causaux.

---

## 11. Journal des sous-rounds autonomes

### S1 — Fusion des autopsies GSE/ALO/RP

1. **Hypothèse causale active** : les trois blocages ont une cause source commune
2. **Mécanisme étudié** : convergence des trois chaînes causales
3. **Question** : les trois causes sont-elles trois faces du même problème ?
4. **Chaîne de remontée** :
   - GSE : taille sans contenu → pas de localisation → F_p sans sous-groupes
   - ALO : circularité → Fourier obligatoire dans F_p → T(t) = même objet
   - RP : pas d'invariant → sous-ensembles de F_p sans forme → F_p sans structure
   - Convergence : **absence de structure additive exploitable dans F_p**
5. **Résultat** : cause commune confirmée, MAIS avec nuance — ALO a une composante supplémentaire (taille O(log p) du support) non partagée par GSE et RP. Deux causes sources couplées, pas une seule.
6. **Statut** : [CONFIRMÉ]
7. **Ce qui est appris** : le blocage est un COUPLAGE de deux propriétés (CS1 + CS2), pas monolithique
8. **Décision** : continuer (S2)
9. **Raison** : trier la profondeur des blocages

### S2 — Tri blocage profond / contingent / faux verrou

1. **Hypothèse causale active** : certains blocages sont contingents au choix de formulation
2. **Mécanisme étudié** : dépendance des blocages au cadre de travail
3. **Question** : quel blocage survit à un changement de cadre ?
4. **Chaîne de remontée** :
   - CS1 (F_p simple) : CONTINGENT — disparaît si on ne réduit pas mod p premier
   - CS2 (support O(log p)) : PROFOND — intrinsèque, mais impact varie selon le cadre
   - Monotonie : FAUX VERROU — confirmé
5. **Résultat** : CS1 contingent, CS2 profond, monotonie faux verrou. Le choix de travailler mod p est une décision de modélisation qui AGGRAVE le blocage.
6. **Statut** : [CONFIRMÉ]
7. **Ce qui est appris** : le programme s'est enfermé dans F_p. L'autopsie montre que c'est CETTE réduction qui crée l'impasse.
8. **Décision** : continuer (S3)
9. **Raison** : extraire le besoin conceptuel survivant

### S3 — Extraction du besoin conceptuel survivant

1. **Hypothèse causale active** : le besoin est de trouver un cadre préservant plus de structure que F_p
2. **Mécanisme étudié** : les cadres alternatifs (mod d, pré-réduction Z, géométrie multiplicative)
3. **Question** : quel est le besoin formulable le plus net ?
4. **Chaîne de remontée** :
   - Problème original dans Z → réduction mod d (structure CRT) → réduction mod p (structure minimale)
   - L'étape mod p → F_p est TROP destructive
   - Besoin = travailler entre Z et F_p, ou exploiter F_p* (multiplicatif) plutôt que F_p (additif)
5. **Résultat** : besoin conceptuel = pont structurel entre Z et F_p. Premier objet = géométrie multiplicative de ⟨2⟩.
6. **Statut** : [FORMULÉ — TESTABLE]
7. **Ce qui est appris** : le programme doit pivoter du paradigme "additif dans F_p" vers un paradigme exploitant une structure plus riche
8. **Décision** : arrêter
9. **Raison** : besoin identifié, suite = round d'innovation (R77)

**Budget** : 3/3 sous-rounds. 0 calcul. Dans le budget.

---

## 12. Objets concernés + Ladder of Proof

| Objet | Niveau avant R76 | Niveau après R76 | Commentaire |
|-------|-----------------|-------------------|-------------|
| CS1 : F_p sans sous-groupes | L8 prouvé (fait algébrique) | **L8 prouvé — RECLASSÉ CONTINGENT** | Profond dans F_p, contingent au choix de cadre |
| CS2 : Support O(log p) | L8 prouvé (fait arithmétique) | **L8 prouvé — CONFIRMÉ PROFOND** | Intrinsèque au problème |
| Monotonie = blocage | L5 semi-formalisé (R75) | **[FAUX VERROU — INNOCENTÉ]** | Le problème sans monotonie est aussi difficile |
| Circularité ALO | L6 schéma de preuve | **L6 — RECLASSÉ comme SYMPTÔME de CS1** | Pas un blocage indépendant |
| Besoin B76 | (nouveau) | **L4 lemme candidat — FORMULÉ** | Cadre intermédiaire Z ↔ F_p |
| Géométrie ⟨2⟩ dans F_p* | (nouveau) | **L3 idée structurée** | Premier objet pour R77 |
| Carte causale globale | (nouveau) | **L6 schéma de preuve** | CS1 ∧ CS2 → blocage |
| Diagnostic "frontière atteinte" (R75) | L5 semi-formalisé | **[RÉVISÉ — TROP TERMINAL]** | Frontière de F_p, pas du problème |

---

## 13. Ce qui est appris

1. **Le blocage a DEUX causes sources couplées, pas une seule** : CS1 (F_p sans sous-groupes additifs) et CS2 (support de taille O(log p)). L'une bloque la localisation, l'autre bloque l'analyse harmonique. C'est leur CONJONCTION qui crée l'impasse.

2. **CS1 est CONTINGENT au choix de réduire mod p** : c'est la découverte principale de R76. Le problème original vit dans Z/dZ (qui a de la structure) ou dans Z (qui a encore plus de structure). La réduction mod p premier est une décision de modélisation qui détruit la structure additive. Ce n'est PAS une nécessité du problème.

3. **La monotonie est un FAUX VERROU** : le problème sans monotonie (sumset libre dans F_p avec support O(log p)) est tout aussi difficile. Les innovations futures ne doivent pas cibler la monotonie.

4. **La circularité d'ALO est un SYMPTÔME, pas un blocage indépendant** : elle est causée par l'obligation de passer par Fourier dans F_p (qui est une conséquence de CS1). En sortant de F_p, la circularité pourrait disparaître (les théorèmes de Littlewood-Offord sur Z ou R ne passent pas par Fourier).

5. **R75 était trop terminal** : le diagnostic "frontière des mathématiques atteinte" est révisé. Ce qui est atteint est la frontière des outils DANS F_p. Le problème lui-même a encore de l'espace d'innovation si on change de cadre.

---

## 14. Ce qui est fermé utilement

1. **"Le blocage est monolithique"** — FERMÉ. Deux causes sources distinctes et couplées.
2. **"La monotonie est un obstacle"** — FERMÉ. Faux verrou innocenté.
3. **"ALO est un blocage indépendant"** — FERMÉ. Symptôme de CS1.
4. **"Il faut un meilleur outil DANS F_p"** — FERMÉ. Le problème est de SORTIR de F_p, pas d'y trouver un meilleur outil.
5. **"Le programme est au bout"** — FERMÉ (diagnostic R75 révisé). Frontière de F_p ≠ frontière du problème.

---

## 15. Ce qui est enterré

1. **"Innovation dans F_p additif"** — ENTERRÉ. Le paradigme "additif dans F_p" est épuisé (CS1 est structurel dans ce cadre).
2. **"Contourner la monotonie"** — ENTERRÉ. Faux verrou.
3. **"Chercher de meilleures bornes de sommes exponentielles courtes"** — ENTERRÉ comme besoin autonome. Circularité.
4. **"Chercher un sous-groupe additif de F_p"** — ENTERRÉ. Impossible par définition (p premier).
5. **"Le diagnostic terminal de R75"** — ENTERRÉ. Remplacé par un diagnostic de contingence.

---

## 16. Autopsie des pistes fermées

### 1. GSE (Generalized Sumset Expansion)

- **Nom** : Expansion par cardinalité
- **Type de mort** : trop faible structurellement
- **Cause source** : les bornes de cardinalité sont symétriques (ne préservent pas l'information de position) et F_p n'a pas de sous-structures additives pour localiser le sumset
- **Ce que la mort enseigne** : dans F_p, la TAILLE d'un ensemble ne dit RIEN sur son CONTENU. La conversion taille→contenu requiert une structure de localisation absente dans F_p.
- **Où cela redirige** : vers un cadre avec localisation (Z/dZ, Z, ou F_p* multiplicatif)

### 2. ALO (Anti-concentration Littlewood-Offord)

- **Nom** : Anti-concentration par distribution
- **Type de mort** : circulaire (symptôme de CS1)
- **Cause source** : dans F_p, la seule voie vers la distribution est Fourier (complétude de la base de caractères), et Fourier préserve la complexité du support doublement géométrique
- **Ce que la mort enseigne** : Fourier est un outil de DISTRIBUTION, mais le problème est un problème de CONTENU. Le mauvais appariement outil/problème est inhérent au cadre F_p. Sur Z ou R, des outils non-Fourier existent (Littlewood-Offord combinatoire).
- **Où cela redirige** : vers l'anti-concentration HORS de F_p (sur Z ou via la structure multiplicative)

### 3. RP (Recursive Peeling)

- **Nom** : Épluchage récursif
- **Type de mort** : blocage plus profond (non-séquentialisabilité)
- **Cause source** : la condition modulo p couple globalement tous les termes ; F_p n'a pas de notion de "forme" pour les sous-ensembles, donc aucun invariant récursif ne peut caractériser l'ensemble des sommes partielles
- **Ce que la mort enseigne** : le problème est INTRINSÈQUEMENT GLOBAL dans F_p. Toute approche séquentielle est vouée à l'échec dans ce cadre.
- **Où cela redirige** : vers un argument global, ou vers un cadre où les sommes partielles ont une structure exploitable (Z, Z/dZ)

### 4. "Frontière des mathématiques" (R75)

- **Nom** : Diagnostic terminal de R75
- **Type de mort** : formulation inadéquate
- **Cause source** : R75 identifiait correctement que les outils DANS F_p sont épuisés, mais concluait à tort que le PROBLÈME est à la frontière. L'autopsie R76 montre que c'est la réduction mod p qui est le point de contingence.
- **Ce que la mort enseigne** : un diagnostic de "frontière" doit toujours préciser : frontière DE QUOI ? (Ici : de F_p additif, pas du problème.)
- **Où cela redirige** : vers un changement de cadre

---

## 17. Survivant pour R77

**Unique survivant** : Explorer la **géométrie multiplicative de ⟨2⟩ dans F_p*** comme cadre alternatif au paradigme "additif dans F_p".

### Justification
- C'est le cadre NON EXPLORÉ le plus prometteur
- Il exploite une structure qui EXISTE DÉJÀ (⟨2⟩ est un sous-groupe multiplicatif de F_p*)
- L'identité g^k = 2^{k-S} mod p (prouvée R31) relie directement la structure de ⟨2⟩ au problème
- F_p* a une structure riche (sous-groupes multiplicatifs, générateurs, ordres) contrairement à (F_p, +) qui est minimal

### Condition de non-boucle pour R77
R77 doit :
1. Formuler un objet ou invariant dans F_p* lié à ⟨2⟩
2. Tester si cet objet porte de l'information exploitable pour l'évitement de -1
3. NE PAS retomber dans l'analyse additive de F_p
4. NE PAS être k-par-k
5. Avoir un critère de réfutation clair

---

## 18. Risques / limites

1. **L'autopsie pourrait être incomplète** : les deux causes sources CS1 et CS2 sont les principales, mais il pourrait exister un troisième facteur non identifié.

2. **Le besoin conceptuel est formulé mais non testé** : la géométrie multiplicative de ⟨2⟩ pourrait s'avérer aussi stérile que l'approche additive. C'est un RISQUE, mais un risque acceptable car cette direction est non explorée.

3. **"Sortir de F_p" pourrait signifier "revenir à un problème plus dur"** : travailler dans Z/dZ ou Z pourrait restaurer de la structure MAIS aussi restaurer de la complexité. Le problème dans Z est celui de la divisibilité corrSum | 0 mod d — un problème diophantien potentiellement plus dur.

4. **La contingence de CS1 ne signifie pas que le problème est facile** : CS1 est contingent au choix de F_p, mais le problème DANS d'autres cadres a ses propres difficultés. La contingence ouvre des directions, pas des solutions.

5. **Le faux verrou "monotonie" est correctement innocenté POUR le blocage principal** : mais la monotonie pourrait redevenir pertinente dans un autre cadre (par exemple, dans Z, la monotonie des compositions crée des bornes de taille sur corrSum qui pourraient être utiles).

---

## 19. Verdict final avec score /10

**Score : 9/10**

R76 accomplit pleinement sa mission d'investigation causale :

1. Trois autopsies causales complètes avec chaînes remontées (✅ PASS-1)
2. Carte causale globale : CS1 + CS2 couplées (✅ PASS-2)
3. Monotonie innocentée comme FAUX VERROU, "frontière atteinte" R75 révisé (✅ PASS-3)
4. Besoin B76 formulé : cadre intermédiaire Z ↔ F_p, premier objet ⟨2⟩ (✅ PASS-4)
5. Unique survivant : géométrie multiplicative de ⟨2⟩ (✅ PASS-5)
6. Aucun calcul, aucun k-par-k, aucun cas (✅ PASS-6)

Point manquant pour 10 : le besoin conceptuel est bien formulé mais non encore TESTÉ. Un 10 serait pour un round qui identifie la cause ET propose un premier objet déjà partiellement validé.

**Score PASS : 6/6**

| Critère | Statut |
|---------|--------|
| PASS-1 : GSE, ALO et RP autopsiés causalement | ✅ Chaînes complètes avec 5 questions chacune |
| PASS-2 : Carte causale globale produite | ✅ CS1 + CS2, composantes source/aggravantes/faux coupable |
| PASS-3 : Au moins un faux verrou innocenté | ✅ Monotonie + diagnostic terminal R75 |
| PASS-4 : Besoin conceptuel formulé | ✅ B76 + premier objet ⟨2⟩ |
| PASS-5 : Unique survivant pour R77 | ✅ Géométrie multiplicative |
| PASS-6 : Aucune dérive | ✅ 0 calcul, 0 k-par-k, 0 terminal |

---

## 20. Registre FAIL-CLOSED

| Objet | Statut |
|-------|--------|
| CS1 : F_p sans sous-groupes additifs | [PROUVÉ] — fait algébrique ; RECLASSÉ [CONTINGENT] au choix de cadre |
| CS2 : Support O(log p) | [PROUVÉ] — fait arithmétique ; CONFIRMÉ [PROFOND] |
| Couplage CS1 ∧ CS2 → blocage | [FORTEMENT ÉTAYÉ] — les trois autopsies convergent |
| Monotonie = obstacle | [FAUX VERROU] — explicitement innocenté |
| Circularité ALO = blocage indépendant | [À REFORMULER] — c'est un symptôme de CS1 |
| Diagnostic "frontière atteinte" (R75) | [À REFORMULER] — frontière de F_p additif, pas du problème |
| GSE : conversion taille→contenu dans F_p | [RÉFUTÉ] — structurellement impossible dans F_p |
| ALO : anti-concentration non-Fourier dans F_p | [RÉFUTÉ] — Fourier est obligatoire dans F_p |
| RP : fermeture de récurrence dans F_p | [RÉFUTÉ] — pas d'invariant stable dans F_p |
| Besoin B76 : cadre intermédiaire Z ↔ F_p | [FORMULÉ — TESTABLE] |
| Géométrie multiplicative ⟨2⟩ dans F_p* | [HEURISTIQUE] — premier objet, non testé |
| Carte causale du blocage | [SEMI-FORMALISÉ] — CS1 + CS2 → 3 échecs |
| SAMC comme reformulation | [PROUVÉ] — inchangé (équivalence correcte) |
| Réduction H ⟸ A' + B' | [SEMI-FORMALISÉ] — inchangé |
| Hypothèse H | [CONJECTURAL] — inchangé |
