# R77 — BILAN : Exploration de la géométrie multiplicative de ⟨2⟩

## Type : X/I/P (investigation causale prolongée + innovation disciplinée + exigence de preuve)
## IVS : 8/10

**Justification IVS** :
- Nouveauté réelle du cadre : 7/10 (le cadre multiplicatif clarifie le problème mais ne compresse pas le verrou)
- Précision de l'objet intermédiaire : 7/10 (SER bien défini, mais reformulation plus que compression)
- Testabilité du premier lemme : 6/10 (lemmes formulés mais trop forts ou trop flous)
- Qualité du contrôle anti-rebranding : 9/10 (V2C enterré rapidement, SER diagnostiqué honnêtement)
- Honnêteté de la décision finale : 10/10 (diagnostic de l'incompatibilité additif/multiplicatif, pas de fausse percée)

Score honorable pour un round qui produit un **diagnostic raffiné** du besoin conceptuel : le noyau dur n'est pas dans l'un ou l'autre côté (additif / multiplicatif) mais à leur INTERFACE — le phénomène somme-produit en régime O(log p).

---

## 1. Résumé exécutif

R77 teste si le déplacement vers la géométrie multiplicative de ⟨2⟩ (recommandé par R76) produit un objet vivant avec un lemme testable.

**Résultat** : le déplacement **clarifie mais ne compresse pas** le verrou.

Trois objets candidats ont été proposés et testés :
- **SER** (Spectre Exponentiel Restreint) : reformulation de SAMC dans l'espace des exposants Z/SZ. Rend visible une contrainte d'espacement (Δe_j ≥ ℓ), mais la somme dans F_p brise la structure du cercle Z/SZ. Verdict : [SEMI-RÉEL], retenu comme reformulation.
- **OPM** (Obstruction par Position de -1) : exploite -1 = 2^{S/2} quand S pair. Propriété arithmétique réelle mais ne se convertit pas en exclusion de somme. Verdict : [SEMI-RÉEL], enterré comme objet autonome.
- **V2C** (Valuation 2-adique du CorrSum) : invariants 2-adiques de corrSum dans Z. Orthogonaux à d (impair). Verdict : [MAL CIBLÉ], enterré.

**Découverte structurelle clé** : Le noyau dur du problème est l'**incompatibilité entre addition et multiplication dans F_p** — le phénomène somme-produit. Ni le côté additif pur (R73-R75) ni le côté multiplicatif pur (R77) ne suffisent. Le verrou est à l'INTERFACE.

**Besoin conceptuel affiné** : un outil de type somme-produit adapté au régime O(log p), exponentiellement en dessous des seuils connus (Bourgain, Katz-Tao : p^δ).

**Décision** : POURSUIVRE AVEC RÉSERVE le SER comme cadre de reformulation. REFORMULER le besoin conceptuel de R76.

---

## 2. Type du round + IVS

**Type** : X/I/P
- **X** : investigation causale prolongée (qu'apporte le cadre multiplicatif ?)
- **I** : innovation disciplinée (3 objets candidats, pas plus)
- **P** : exigence de preuve, testabilité, falsifiabilité

**IVS** : 8/10 — Le round produit un diagnostic structurel net (noyau dur = interface additif/multiplicatif) et enterre proprement V2C et OPM. Il ne produit pas de compression du verrou, mais affine considérablement le besoin conceptuel. Un 8 plutôt que 9 car aucun lemme testable ne survit.

---

## 3. Méthode

1. Investigation de la structure propre de ⟨2⟩ ⊂ F_p* (Axe A)
2. Autopsie du couplage λ^j / ⟨2⟩ (Axe B) — cas 3 ∈ ⟨2⟩ vs 3 ∉ ⟨2⟩
3. Réévaluation de la monotonie dans le cadre multiplicatif (Axe C)
4. Génération de 3 objets candidats avec lemme + critère de réfutation (Axe D)
5. Contrôle anti-rebranding systématique (Axe E)
6. Test de réalité mathématique sévère (Axe F)
7. Évaluation de l'impact programmatique (Axe G)
8. Décision stratégique avec autonomie (Axe H, 3 sous-rounds)
9. Aucun calcul, aucun k-par-k, aucun cas particulier

---

## 4. Résultats PHASE 1 / AXE A — Structure de ⟨2⟩

### Structures multiplicatives réellement informatives

1. **Orbite cyclique** : ⟨2⟩ est isomorphe à Z/ord_p(2)Z. L'exponentiation φ(n) = 2^n mod p est un isomorphisme de groupes. Les distances entre éléments sont des RAPPORTS multiplicatifs.

2. **Ordre et relation 2^S ≡ 3^k** : ord_p(2) | S, et la relation p | (2^S - 3^k) relie intrinsèquement la structure de ⟨2⟩ au problème.

3. **Position de -1** : -1 ∈ ⟨2⟩ ⟺ ord_p(2) pair. Si oui, -1 = 2^{ord_p(2)/2}. C'est une information SPÉCIFIQUE sur la cible.

4. **Appartenance de 3 à ⟨2⟩** : Si 3 ∈ ⟨2⟩, alors λ ∈ ⟨2⟩ et TOUS les termes du sumset sont des puissances de 2. Simplifie drastiquement la structure.

### Illusions multiplicatives à enterrer

1. **"Log discret simplifie le problème"** — FAUX. Le log discret transforme les produits en sommes mais rend les SOMMES opaques. Or le problème EST un problème de somme.

2. **"Sous-groupes multiplicatifs localisent le sumset"** — FAUX PARTIEL. Le sumset est une opération ADDITIVE sur des éléments multiplicativement structurés. Le résultat n'a pas de raison d'être dans un sous-groupe multiplicatif.

### Diagnostic

Ce qui est réellement nouveau par rapport au cadre additif : la structure d'ORBITE de ⟨2⟩ (distances, espacement, position de -1) et la dichotomie 3 ∈ ⟨2⟩ / 3 ∉ ⟨2⟩. Ce qui est illusoire : croire que la structure multiplicative peut remplacer la structure additive pour le problème de somme.

---

## 5. Résultats PHASE 1 / AXE B — Couplage λ^j / ⟨2⟩

### Carte du couplage

```
λ = 2 · 3^{-1} mod p
    ├── Si 3 ∈ ⟨2⟩ : λ = 2^ℓ pour ℓ = 1 - log_2(3) mod ord_p(2)
    │     └── terme j = λ^j · 2^{g_j} = 2^{jℓ + g_j} ∈ ⟨2⟩
    │          └── sumset = somme de k-1 puissances de 2 (Waring additif dans ⟨2⟩)
    │
    └── Si 3 ∉ ⟨2⟩ : λ ∉ ⟨2⟩
          └── terme j ∈ λ^j · ⟨2⟩ (cosets distincts)
               └── sumset mélange des cosets — structure perdue
```

### Composante bloquante principale

Le blocage n'est pas dans ⟨2⟩ seul ni dans les λ^j seuls, mais dans le fait que l'**ADDITION dans F_p ne respecte pas la structure multiplicative**. La somme de deux éléments de ⟨2⟩ sort de ⟨2⟩ en général. C'est le phénomène somme-produit : les ensembles multiplicativement structurés ont des sumsets additifs GRANDS et NON STRUCTURÉS.

### Type d'objet susceptible d'absorber ce couplage

Un objet qui capture SIMULTANÉMENT la structure additive et multiplicative — un invariant somme-produit. Les résultats connus (Bourgain 2005, Katz-Tao 2001) exigent |A| ≥ p^δ, inaccessible dans notre régime.

### Faux mécanisme refusé

Traiter les λ^j comme des poids "inoffensifs" ou "organisateurs simples" : ils couplent activement les deux structures, et ce couplage EST le noyau dur.

---

## 6. Résultats PHASE 1 / AXE C — Statut de la monotonie

**Statut** : [SECONDAIRE MAIS NON TRIVIALE]

Dans le cadre multiplicatif, la monotonie g_1 ≤ ... ≤ g_{k-1} signifie que les exposants effectifs e_j = jℓ + g_j satisfont Δe_j = e_j - e_{j-1} = ℓ + (g_j - g_{j-1}) ≥ ℓ. C'est une contrainte d'**espacement minimal** sur le cercle Z/ord_p(2)Z.

Cette contrainte est :
- **non triviale** : elle restreint les configurations d'exposants (pas toutes les k-1-uplets sont admissibles)
- **non source** : elle n'affecte pas le problème fondamental (somme dans F_p ne respecte pas le cercle)
- **potentiellement utile** : si un outil somme-produit en régime court existait, la contrainte d'espacement pourrait renforcer ses bornes

**Formulation minimale** : La monotonie est une contrainte d'espacement ≥ ℓ dans l'espace des exposants. Elle est un paramètre de comptage, pas un verrou.

---

## 7. Résultats PHASE 2 / AXE D — Objets candidats

### Objet 1 : SER (Spectre Exponentiel Restreint)

**Définition** : Quand 3 ∈ ⟨2⟩ avec λ = 2^ℓ mod p, le spectre exponentiel est l'ensemble des exposants effectifs E(g) = {jℓ + g_j mod ord_p(2)}_j dans Z/SZ. La condition SAMC (-1 ∈ Σ_≤(k)) se reformule comme : existe-t-il une suite monotone (g_j) telle que Σ 2^{e_j} ≡ p-1 mod p ?

**Blocage visé** : CS1 — remplacer le cadre F_p (sans localisation) par Z/SZ (avec structure cyclique).

**Différence avec l'existant** : Travaille dans l'espace des exposants, pas des valeurs. Rend visible la contrainte d'espacement Δe_j ≥ ℓ.

**Lemme candidat** : La condition -1 ∈ Σ_≤(k) est équivalente à l'existence d'exposants e_1,...,e_{k-1} dans Z/SZ, espacés de ≥ ℓ consécutivement, tels que Σ 2^{e_j} ≡ -1 mod p.

**Critère de réfutation** : Si la map d'espacement ne contraint pas la valeur de la somme dans F_p (ce qui est le cas), le SER ne compresse pas le verrou.

---

### Objet 2 : OPM (Obstruction par Position de -1)

**Définition** : Quand ord_p(2) = S et S pair, -1 = 2^{S/2} mod p. L'OPM cherche à exploiter cette position SPÉCIFIQUE de -1 sur le cercle ⟨2⟩ pour montrer que les sommes contraintes ne peuvent pas l'atteindre.

**Blocage visé** : Évitement ciblé de -1 via sa position multiplicative.

**Différence avec l'existant** : Propriété arithmétique -1 = 2^{S/2} non exploitée auparavant.

**Lemme candidat** : Si les exposants sont contraints à un arc de Z/SZ de longueur < S/2, la somme dans F_p ne peut pas valoir 2^{S/2}.

**Critère de réfutation** : La somme dans F_p de puissances de 2 ne préserve pas la géométrie du cercle.

---

### Objet 3 : V2C (Valuation 2-adique du CorrSum)

**Définition** : Invariants v_2(corrSum) et corrSum mod 2^m dans Z, avant réduction mod d.

**Blocage visé** : CS1 — contourner F_p en travaillant dans Z.

**Lemme candidat** : corrSum mod 4 est déterminé par les deux plus petites parties.

**Critère de réfutation** : d est impair → les invariants 2-adiques sont orthogonaux à corrSum mod d.

---

## 8. Résultats PHASE 2 / AXE E — Contrôle anti-rebranding

| Objet | Ancienne piste | Ressemblance | Différence réelle | Verdict |
|-------|---------------|-------------|-------------------|---------|
| SER | SOH/Horner (R70-72) | Reformulation algébrique | SER dans Z/SZ, pas dans F_p. Expose espacement. | **Nouveauté partielle** |
| OPM | Aucune directe | — | -1 = 2^{S/2} non exploité avant | **Nouveauté réelle** (mais mordant faible) |
| V2C | Valuations v_2 (R35-40) | Même type d'information | d impair → orthogonal | **Rebranding risqué** |

**Drapeaux rouges** :
- **V2C** : drapeau rouge FORT (structurellement orthogonal)
- **SER** : drapeau orange (changement de cadre réel mais somme dans F_p brise la structure Z/SZ)

---

## 9. Résultats PHASE 3 / AXE F — Test de réalité mathématique

| Objet | Statut objet | Statut lemme | Mordant |
|-------|-------------|-------------|---------|
| SER | [SEMI-RÉEL] | [BIEN CIBLÉ mais TROP FORT] | [TESTABLE MAIS FAIBLE] |
| OPM | [SEMI-RÉEL] | [TROP FLOU] | [TESTABLE MAIS FAIBLE] |
| V2C | [SEMI-RÉEL] | [MAL CIBLÉ] | [NON TESTABLE] |

### Analyse détaillée du SER

Le SER est bien défini et produit un lemme exact (reformulation de SAMC en exposants). La contrainte d'espacement Δe_j ≥ ℓ est réelle et visible. **Mais** : la somme Σ 2^{e_j} dans F_p ne respecte pas la structure de Z/SZ. L'espacement des exposants ne contraint pas la valeur de la somme dans F_p.

Le SER souffre du MÊME obstacle que GSE : la structure des configurations (ici dans Z/SZ) ne se convertit pas en information sur la valeur de la somme (dans F_p). Le gap configuration → contenu persiste.

### Analyse détaillée de l'OPM

L'OPM exploite une propriété arithmétique réelle (-1 = 2^{S/2}), mais la notion de "moitié du cercle" ne se traduit pas en exclusion de somme dans F_p. La somme de puissances de 2 dans F_p peut donner n'importe quel résultat, indépendamment de la position des exposants sur le cercle.

### Analyse de V2C

Structurellement orthogonal à la condition mod d (d impair). **ENTERRÉ immédiatement.**

---

## 10. Résultats PHASE 3 / AXE G — Chaîne logique et impact

### Si le lemme SER était prouvé

Le lemme SER est une reformulation EXACTE de SAMC — le prouver REVIENT à prouver SAMC, qui implique H(k), qui implique l'Hypothèse H. Ce n'est pas un pas intermédiaire.

### Portée honnête

- SER : reformulation avec visibilité améliorée. **Pas local, pas décisif, mais structurel.**
- OPM : propriété arithmétique retenue. **Local.**
- V2C : mort.

### Seuil pour R78

Pour mériter R78, il faudrait que la contrainte d'espacement dans Z/SZ produise un lemme INTERMÉDIAIRE prouvable (entre le SER complet et le trivial), ou qu'un outil somme-produit en régime O(log p) soit identifié.

---

## 11. Résultats PHASE 4 / AXE H — Décision finale

### Décision stratégique

**POURSUIVRE AVEC RÉSERVE** — avec **REFORMULATION du besoin conceptuel**.

Le déplacement vers la géométrie multiplicative de ⟨2⟩ a produit une clarification structurelle importante mais pas de compression du verrou. Le SER est retenu comme cadre de reformulation (meilleure visibilité de la contrainte d'espacement) mais n'est pas un objet programmatique capable de briser le verrou.

### Découverte structurelle

Le noyau dur du problème est l'**incompatibilité entre addition et multiplication dans F_p** — le phénomène somme-produit. Ni le côté additif (R73-R75) ni le côté multiplicatif (R77) ne suffisent seuls. Le problème vit à l'INTERFACE.

### Besoin conceptuel reformulé

R76 demandait : "un cadre intermédiaire entre Z et F_p exploitant la géométrie multiplicative de ⟨2⟩".

R77 affine : **un outil ou résultat de type somme-produit adapté au régime O(log p)**, c'est-à-dire un mécanisme qui exploite SIMULTANÉMENT la structure additive et multiplicative des puissances de 2, pour des ensembles de taille exponentiellement inférieure à p^δ.

### Survivant unique pour R78

**Le problème somme-produit en régime logarithmique** : peut-on montrer que la somme de O(k) éléments de ⟨2⟩ (un sous-groupe multiplicatif) avec contrainte d'espacement a une structure additive particulière qui exclut -1 ?

### Condition de non-boucle pour R78

R78 ne doit PAS :
1. Reproposer un simple changement de cadre (additif → multiplicatif ou vice-versa)
2. Appliquer des résultats somme-produit standards (exigent p^δ, inapplicable)
3. Revenir à l'analyse harmonique pure (R73 fermé)
4. Proposer un objet sans lemme intermédiaire prouvable

R78 DOIT :
1. Identifier un résultat somme-produit exploitable en régime O(log p), ou
2. Explorer si la contrainte d'espacement ≥ ℓ, combinée à la petite taille k-1 du sumset, crée une rigidité exploitable, ou
3. Déclasser définitivement la voie F_p et proposer un retour complet à Z/dZ avec CRT renforcé

### Pistes enterrées

- **V2C** : orthogonal (d impair)
- **OPM autonome** : ne se convertit pas en exclusion
- **"Travailler dans le log discret"** : rend les sommes opaques
- **"Localiser le sumset dans un sous-groupe multiplicatif"** : la somme n'est pas multiplicative

---

## 12. Activation de l'autonomie

**Activation** : OUI — 3 sous-rounds entre Phase 2 et Phase 4.

**Justification** : nécessaire pour fusionner les diagnostics SER/OPM/V2C et parvenir à une décision stratégique honnête.

---

## 13. Journal des sous-rounds autonomes

### S1 — Tri des objets candidats
1. **Hypothèse** : SER est le meilleur candidat
2. **Objet** : SER dans Z/SZ
3. **Question** : la contrainte d'espacement est-elle réellement nouvelle par rapport à SAMC ?
4. **Démarche** : comparaison SAMC / SER
5. **Résultat** : l'espacement Δe_j ≥ ℓ est nouvelle (invisible dans SAMC), mais c'est de la visibilité, pas de la compression
6. **Statut** : [SEMI-CONFIRMÉ]
7. **Appris** : visibilité ≠ compression
8. **Décision** : continuer
9. **Raison** : tester la combinaison SER+OPM

### S2 — Test de réalité et fusion SER+OPM
1. **Hypothèse** : SER+OPM combinés pourraient être plus forts
2. **Objet** : espacement + position de -1 = 2^{S/2}
3. **Question** : l'espacement et la position de -1 créent-ils une obstruction ?
4. **Démarche** : examiner si l'addition dans F_p préserve la géométrie du cercle
5. **Résultat** : NON — l'addition dans F_p brise la structure multiplicative. C'est le phénomène somme-produit. Le noyau dur est l'INCOMPATIBILITÉ additif/multiplicatif.
6. **Statut** : [BLOCAGE IDENTIFIÉ]
7. **Appris** : le vrai verrou est à l'interface des deux structures, pas dans l'une ou l'autre
8. **Décision** : continuer
9. **Raison** : formuler la décision finale

### S3 — Décision finale
1. **Hypothèse** : le déplacement de cadre ne compresse pas le verrou
2. **Objet** : tous les candidats
3. **Question** : poursuivre, reformuler ou déclasser ?
4. **Démarche** : évaluation honnête
5. **Résultat** : V2C enterré (orthogonal), OPM enterré (autonome), SER retenu comme reformulation. Besoin reformulé : outil somme-produit en régime O(log p).
6. **Statut** : [DÉCISION PRISE — REFORMULÉE]
7. **Appris** : le besoin de R76 était trop centré sur le multiplicatif. Le vrai besoin est à l'interface.
8. **Décision** : arrêter
9. **Raison** : diagnostic complet

**Budget** : 3/3 sous-rounds, 0 calcul, dans le budget.

---

## 14. Objets concernés + Ladder of Proof

| Objet | Niveau | Commentaire |
|-------|--------|-------------|
| SER (Spectre Exponentiel Restreint) | L3 idée structurée → L4 lemme candidat | Reformulation de SAMC dans Z/SZ, visibilité de l'espacement, mais pas de compression |
| OPM (Obstruction Position -1) | L2 intuition → L3 idée structurée | Propriété arithmétique réelle (-1 = 2^{S/2}) mais sans conversion en exclusion |
| V2C (Valuation 2-adique) | L3 → [RÉFUTÉ] | Orthogonal à d (impair) |
| Incompatibilité additif/multiplicatif | L6 fortement étayé | Diagnostic structurel du noyau dur — phénomène somme-produit |
| Besoin B77 (somme-produit O(log p)) | L2 intuition | Reformulation du besoin B76, plus précis |
| Contrainte d'espacement ≥ ℓ | L5 semi-formalisé | Prouvable, mais pas encore convertie en mordant |
| Dichotomie 3 ∈ ⟨2⟩ / 3 ∉ ⟨2⟩ | L5 semi-formalisé | Structure réelle, potentiellement utile |
| CS1 : F_p sans sous-groupes | [PROUVÉ — CONFIRMÉ] | Inchangé depuis R76 |
| CS2 : Support O(log p) | [PROUVÉ — CONFIRMÉ] | Inchangé, relié aux seuils somme-produit |

---

## 15. Ce qui est appris

1. **Le noyau dur est l'incompatibilité additif/multiplicatif dans F_p** : ni le cadre additif pur (R73-R75) ni le cadre multiplicatif pur (R77) ne suffisent. Le problème vit à l'INTERFACE — exactement le domaine somme-produit.

2. **Les résultats somme-produit connus sont inaccessibles** : Bourgain (2005), Katz-Tao (2001) etc. exigent |A| ≥ p^δ. Or |⟨2⟩ ∩ support| = O(log p) est exponentiellement en dessous.

3. **La contrainte d'espacement Δe_j ≥ ℓ est une propriété structurelle réelle** : visible uniquement dans le cadre SER, invisible dans SAMC. C'est de la visibilité sans compression, mais c'est un acquis.

4. **La dichotomie 3 ∈ ⟨2⟩ / 3 ∉ ⟨2⟩ est structurante** : quand 3 ∈ ⟨2⟩, tous les termes sont dans ⟨2⟩ et le problème est un problème de Waring additif dans un sous-groupe multiplicatif. Quand 3 ∉ ⟨2⟩, les termes mélangent des cosets — le problème est structurellement plus dur.

5. **Le besoin conceptuel de R76 est AFFINÉ** : ce n'est pas "sortir de F_p additif vers F_p* multiplicatif", c'est trouver un outil qui travaille à l'interface des deux.

6. **La monotonie reste secondaire** : confirmée [SECONDAIRE MAIS NON TRIVIALE] dans le cadre multiplicatif. L'espacement ≥ ℓ est sa trace dans l'espace des exposants.

---

## 16. Ce qui est fermé utilement

1. **"La géométrie multiplicative de ⟨2⟩ suffit à compresser le verrou"** — FERMÉ. La structure multiplicative est réelle mais l'addition dans F_p la brise.
2. **"Le log discret simplifie le problème"** — FERMÉ. Rend les sommes opaques.
3. **"Les invariants 2-adiques contraignent mod d"** — FERMÉ. d est impair.
4. **"La position de -1 sur le cercle exclut la somme"** — FERMÉ (comme objet autonome). L'addition ne préserve pas la géométrie du cercle.
5. **"Il suffit de travailler d'un côté (additif OU multiplicatif)"** — FERMÉ. Le verrou est à l'interface.

---

## 17. Ce qui est enterré

1. **V2C** — structurellement orthogonal (d impair)
2. **OPM comme objet autonome** — ne se convertit pas en exclusion de somme
3. **"Log discret comme simplification"** — rend les sommes opaques
4. **"Localisation dans un sous-groupe multiplicatif"** — la somme n'est pas multiplicative
5. **"Approche purement multiplicative"** — le verrou est à l'interface, pas d'un côté

---

## 18. Autopsie des pistes fermées

### 1. V2C (Valuation 2-adique du CorrSum)
- **Nom** : Invariants 2-adiques pré-réduction
- **Type de mort** : objet sans chaîne logique (orthogonalité structurelle)
- **Cause du rejet** : d = 2^S - 3^k est toujours IMPAIR. Les invariants v_2(corrSum) et corrSum mod 2^m sont complètement orthogonaux à la condition corrSum ≡ 0 mod d. Aucune chaîne logique possible.
- **Ce que la mort enseigne** : avant de proposer un invariant "pré-réduction", vérifier qu'il n'est pas orthogonal à la condition de divisibilité visée.
- **Où cela redirige** : les invariants dans Z doivent cibler des facteurs IMPAIRS de d, pas la structure 2-adique.

### 2. OPM (Obstruction par Position de -1)
- **Nom** : Exclusion de -1 par sa position multiplicative
- **Type de mort** : dépendance cachée au cadre additif
- **Cause du rejet** : la somme dans F_p ne préserve pas la géométrie du cercle ⟨2⟩. La position de -1 = 2^{S/2} sur le cercle est une information multiplicative, mais la somme est additive — l'information ne traverse pas.
- **Ce que la mort enseigne** : toute stratégie basée UNIQUEMENT sur la structure multiplicative échoue parce que l'opération du problème (la somme) est additive. Le verrou est à l'interface.
- **Où cela redirige** : vers un outil somme-produit, pas vers un outil purement multiplicatif.

### 3. "Log discret comme simplification"
- **Nom** : Reformulation en log discret
- **Type de mort** : décor multiplicatif
- **Cause du rejet** : le log discret log_2(a+b) n'a pas de forme simple. Le passage au log discret complique l'opération principale (la somme) tout en simplifiant les opérations secondaires (les produits).
- **Ce que la mort enseigne** : une reformulation n'est utile que si elle simplifie l'opération PRINCIPALE, pas les opérations secondaires.
- **Où cela redirige** : le cadre de travail doit garder les deux opérations (somme et produit) aussi accessibles que possible — donc rester dans F_p ou dans un cadre mixte.

---

## 19. Survivant pour R78

**Unique survivant** : Le problème **somme-produit en régime logarithmique**.

### Formulation

Peut-on exploiter le fait que les termes du sumset sont des éléments d'un sous-groupe multiplicatif (⟨2⟩) pour contraindre leur somme additive, DANS LE RÉGIME |support| = O(log p) ?

### Trois directions possibles pour R78

1. **Rigidité par petitesse** : les résultats somme-produit standard exigent p^δ. Mais existe-t-il un résultat INVERSE pour les PETITS ensembles ? Un phénomène de "rigidité par petitesse" — quand un sous-groupe multiplicatif est très petit (O(log p)), ses sommes additives pourraient être PLUS contraintes, pas moins ?

2. **Retour à Z/dZ renforcé** : puisque F_p est une impasse (des deux côtés), revenir à Z/dZ avec le CRT mais en exploitant la corrélation ENTRE facteurs premiers de d. Le gap k=21-41 (R25-34) pourrait être fermé par un argument CRT somme-produit croisé.

3. **Approche algébrique directe** : la relation 2^S ≡ 3^k mod p est une relation entre deux éléments multiplicatifs. Peut-on exploiter cette relation pour contraindre corrSum ≡ 0 mod p par un argument algébrique DIRECT (sans passer par Fourier ou par la somme de puissances) ?

### Condition de non-boucle

R78 ne doit pas reproposer un simple changement de cadre, ni appliquer des résultats standard inaccessibles, ni revenir à l'analyse harmonique pure. Il doit soit identifier un résultat somme-produit en régime O(log p), soit explorer la "rigidité par petitesse", soit proposer un retour CRT avec mécanisme croisé.

---

## 20. Risques / limites

1. **Le SER est retenu comme reformulation mais pourrait être une impasse déguisée** : la visibilité de l'espacement ne garantit pas qu'un lemme intermédiaire puisse en être extrait.

2. **Le phénomène somme-produit en régime O(log p) est TERRA INCOGNITA** : aucun résultat connu ne traite ce régime. Le programme est peut-être en train de formuler un problème ouvert de théorie additive des nombres aussi difficile que le problème de Collatz lui-même.

3. **La "rigidité par petitesse" est une intuition, pas un résultat** : l'idée que les petits sous-groupes multiplicatifs ont des sommes plus contraintes n'est pas établie. Elle pourrait être fausse.

4. **Le retour à Z/dZ pourrait retrouver les mêmes blocages qu'en R25-34** : single-prime blocking pour 71 paires, gap k=21-41. Sans mécanisme nouveau, le retour serait un rebranding.

5. **Cumul de rounds sans compression** : R73 (fermeture analytique), R74 (SAMC), R75 (SAMC sans compression), R76 (autopsie causale), R77 (multiplicatif sans compression). Cinq rounds de clarification progressive mais sans percée. Le programme pourrait atteindre un plateau.

---

## 21. Verdict final avec score /10

**Score : 8/10**

R77 accomplit sa mission d'exploration disciplinée :

1. Structure multiplicative de ⟨2⟩ clarifiée (✅ PASS-1)
2. Trois objets proposés, pas plus (✅ PASS-2)
3. Chaque objet a lemme + critère de réfutation (✅ PASS-3)
4. Anti-rebranding rigoureux : V2C enterré, SER diagnostiqué honnêtement (✅ PASS-4)
5. Décision stratégique honnête : POURSUIVRE AVEC RÉSERVE + reformulation du besoin (✅ PASS-5)
6. Unique survivant : somme-produit en régime O(log p) (✅ PASS-6)

**Score PASS : 6/6**

| Critère | Statut |
|---------|--------|
| PASS-1 : Structure multiplicative de ⟨2⟩ clarifiée | ✅ Orbite, ordre, position de -1, dichotomie 3∈⟨2⟩ |
| PASS-2 : Au plus 3 objets | ✅ SER, OPM, V2C |
| PASS-3 : Lemme + critère de réfutation par objet | ✅ Chaque objet testé sévèrement |
| PASS-4 : Anti-rebranding | ✅ V2C = rebranding, SER = nouveauté partielle, OPM = nouveauté réelle |
| PASS-5 : Décision stratégique honnête | ✅ Pas de fausse percée, diagnostic du noyau dur |
| PASS-6 : Unique survivant pour R78 | ✅ Somme-produit en régime O(log p) |

Point manquant pour 9 : aucun lemme testable ne survit — tous sont soit trop forts (= problème entier) soit trop flous. Le 8 reflète un round de clarification qui affine le besoin sans compression.

---

## 22. Registre FAIL-CLOSED

| Objet | Statut |
|-------|--------|
| SER (Spectre Exponentiel Restreint) | [SEMI-FORMALISÉ] — reformulation valide dans Z/SZ, visibilité accrue, pas de compression |
| OPM (Position de -1 = 2^{S/2}) | [HEURISTIQUE] — propriété arithmétique réelle, non convertible en exclusion |
| V2C (Valuation 2-adique) | [RÉFUTÉ] — orthogonal à d (impair) |
| Contrainte d'espacement Δe_j ≥ ℓ | [SEMI-FORMALISÉ] — prouvable, pas encore mordante |
| Dichotomie 3 ∈ ⟨2⟩ / 3 ∉ ⟨2⟩ | [SEMI-FORMALISÉ] — structurante pour les cas |
| Noyau dur = incompatibilité add./mult. | [FORTEMENT ÉTAYÉ] — les deux côtés testés et échoués |
| Besoin B77 (somme-produit O(log p)) | [HEURISTIQUE] — direction identifiée, pas d'outil connu |
| "Rigidité par petitesse" des sous-groupes | [HEURISTIQUE] — intuition non étayée |
| CS1 : F_p sans sous-groupes additifs | [PROUVÉ — CONFIRMÉ] — inchangé |
| CS2 : Support O(log p) | [PROUVÉ — CONFIRMÉ] — relié aux seuils somme-produit |
| Monotonie | [FAUX VERROU — CONFIRMÉ] — secondaire, trace = espacement ≥ ℓ |
| SAMC | [PROUVÉ] — reformulation correcte, pas de compression |
| Hypothèse H | [CONJECTURAL] — inchangé |
