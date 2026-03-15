# R155 — CAMPAGNE MULTI-PISTES SOUS CONDITIONS STRICTES

**Date** : 15 mars 2026
**Type** : X/I/P
**Protocole** : PromptR155.md exécuté intégralement (4 agents parallèles, qualification → tournoi)
**Campagne précédente** : R154 (IVS 1.5/10, SUSPENSION DÉFINITIVE 5ème confirmation, morphologie≡(H_k))

---

## RÉSUMÉ EXÉCUTIF

Campagne de qualification sévère sur 4 pistes autorisées (A: objet couplé h↔h-1, B: compatibilité inter-facteurs, C: impossibilité de famille, D: monodromie binaire). Deux candidats soumis, les deux pistes sans candidat (B, D) éliminées d'office.

- **Candidat A155** (énergie croisée E^{×,+}(Γ) add-mult sur le graphe h↦h-1) : **[ÉLIMINÉ]** — trivialité algébrique : la double contrainte (h₁/h₂=h₃/h₄ ET h₁+h₄=h₂+h₃) force {h₃,h₄}={h₁,h₂}, donnant E^{×,+}(Γ)=(r-1)(2r-3) universellement, indépendamment de H
- **Candidat C155** (théorème d'impossibilité module-only) : **[EXÉCUTION COURTE AUTORISÉE AVEC RÉSERVE]** — formalise la clôture de R154, mais risque de trivialité (Parseval+Jensen en 3 lignes)
- **Piste B** : mort-née (reformulation du problème, R154+T4)
- **Piste D** : aucun candidat soumis (manque de faisceau précis)

**Verdict** : 1 piste en exécution courte conditionnelle sur 4 soumises. Suspension maintenue.

**IVS** : 2.0/10

---

## PHASE 1 — LECTURE CONTRAINTE DE LA RESEARCH MAP (Agent 1)

### Morts pertinents cités par piste

| Piste | Morts pertinents | Risque de redondance |
|-------|-----------------|---------------------|
| A (h,h-1) | R77/R81 (faille add/mult identifiée), R138 (Shkredov sum-product gap polynomial), T171/T173 (E^×(H-1)) | MOYEN — faille identifiée mais non attaquée avec objet dédié |
| B (inter-facteurs) | R153 (collectif≡pointwise), R154 (configurations≡(H_k)), T4/T5/HGE | ÉLEVÉ — toute compatibilité orbitale = (H_k) |
| C (impossibilité) | R154 (morphologie≡(H_k)), R80 (7 reformulations), R141 (identité sans outil) | FAIBLE — résultat négatif, pas d'attaque |
| D (monodromie) | R152 (survivant conditionnel), Weil/Deligne (borne √p pas √r) | MOYEN — objet non calculé |

### Diagnostic de légitimité (Agent 1)

**Piste A** : MEILLEURE LÉGITIMITÉ (1/4). Le manque réel est l'absence de lien exploitable entre structure multiplicative de H et géométrie de H-1. Le couplage (h, h-1) = (2^a, 2^a-1) encode exactement cette question. Un objet algébrique dédié n'a jamais été construit.

**Piste B** : PRÉ-DISQUALIFIÉE. Toute compatibilité inter-facteurs orbitaux se réduit à (H_k) par R154. Signal de mort immédiate : si l'objet invoque la corrélation S_H(s·3^j) pour j le long d'une orbite, c'est (H_k) par définition.

**Piste C** : LÉGITIME COMME NETTOYAGE. Ne prétend pas attaquer le verrou mais fermer une classe d'approches. Utile pour la publication.

**Piste D** : LÉGITIME MAIS SANS CANDIDAT FORMEL. Le faisceau pertinent n'est pas identifié. La restriction à un sous-ensemble fini d'un groupe n'est pas le contexte standard de la théorie de la monodromie (Katz, Laumon).

---

## PHASE 2 — QUALIFICATION (Agents 1+4)

### Shortlist

| Piste | Verdict | Raison |
|-------|---------|--------|
| A | QUALIFIÉE | Objet nouveau (graphe Γ), jamais construit dans les rounds précédents |
| B | ÉLIMINÉE | Pré-disqualifiée par R154+T4, toute compatibilité orbitale = (H_k) |
| C | QUALIFIÉE AVEC RÉSERVE | Résultat négatif légitime mais risque trivialité |
| D | SANS CANDIDAT | Manque d'objet faisceautique précis |

---

## PHASE 3 — FABRICATION DES CANDIDATS (Agent 2)

### Candidat A155 : Énergie croisée add-mult E^{×,+}(Γ)

**Objet.** Soit Γ = {(h, h-1) : h ∈ H\{1}} ⊂ F_p* × F_p*. Énergie croisée :

E^{×,+}(Γ) = #{(h₁,h₂,h₃,h₄) ∈ (H\{1})⁴ : h₁/h₂ = h₃/h₄ ET h₁+h₄ = h₂+h₃}

C'est l'énergie sum-product de H\{1} : contrainte multiplicative + contrainte additive simultanées.

**Lemme candidat.** E^{×,+}(Γ) ≤ r^{3-δ} pour un δ > 0 absolu.

**Connexion au verrou.** Via T171 : M₄(S_H) ≈ (p-1)·E^×(H-1). Si E^{×,+} contraint E^×(H-1), on obtient M₄ ≤ p·r^{3-δ'}, donc max|S_H| ≤ r^{3/4-δ''/4} qui bat √r.

**Test de réfutation.** Calculer E^{×,+}(Γ)/r³ pour p ∈ {127, 8191, 131071}. Si → constante > 0, le lemme est faux.

**Auto-évaluation Agent 2** : PRIORITAIRE — objet le plus prometteur du round.

### Candidat C155 : Théorème d'impossibilité module-only

**Énoncé candidat.** Pour toute fonctionnelle mesurable F : R₊^L → R₊ et toute orbite O(s) de ⟨3⟩ :

Σ_{s∈Rep} F(|S_H(s)|², ..., |S_H(3^{L-1}s)|²) ≥ Ω(p/r · F(r,...,r))

Toute moyenne orbitale pondérée par les modules est minorée par la contribution des s typiques. Aucune fonctionnelle des modules ne peut identifier un sous-ensemble atypique suffisant.

**Preuve esquissée.** Par Parseval, (p-1)/r orbites, Jensen sur F convexe, Markov sur M₂ pour les exceptionnels.

**Gain opératoire.** Ferme la porte aux attaques module-only. Force tout futur travail vers la structure arithmétique de H, les phases, ou les outils géométriques.

**Auto-évaluation Agent 2** : SECONDAIRE — utile pour la publication, pas une percée.

---

## PHASE 4 — AUDIT CROISÉ ET TOURNOI

### Audit A155 (Agent 3) — KILL DÉFINITIF

**Preuve de trivialité :** Fixons (h₁,h₂) = (a,b) avec a ≠ b. Les deux contraintes simultanées sont :
- MULT : h₃/h₄ = a/b
- ADD : h₃+h₄ = a+b

De MULT : h₃ = (a/b)·h₄. Substituant dans ADD : (a/b)·h₄ + h₄ = a+b, soit h₄·(a+b)/b = a+b.

- Si a+b ≠ 0 : h₄ = b et h₃ = a. L'autre solution est h₃ = b, h₄ = a.
- Si a+b = 0 (b = -a) : h₃/h₄ = -1 et h₃+h₄ = 0, donc {h₃,h₄} = {a,-a} = {a,b}.

**Résultat : {h₃,h₄} = {h₁,h₂} dans tous les cas.**

Donc :

**E^{×,+}(Γ) = (r-1)(2r-3) = O(r²)**

pour TOUT sous-groupe H de TOUTE taille dans TOUT corps. C'est une identité algébrique universelle. Aucune arithmétique de H n'intervient.

**Conséquence** : Le lemme candidat E^{×,+}(Γ) ≤ r^{3-δ} est trivialement vrai (r² ≤ r^{3-δ} pour δ < 1) mais VIDE — la borne est universelle, elle ne dit rien sur H.

**Kill switches déclenchés** :
- **KS4 (vacuité générique)** : DÉCLENCHÉ — identique pour H=⟨2⟩ et H=⟨a⟩ quelconque
- **KS5 (instanciation triviale)** : DÉCLENCHÉ — résultat = O(r²) sans structure

**Morts cités** : R80 (reformulations isomorphes — surclassé, ici ce n'est même pas une reformulation, c'est un objet vide), R138 (Shkredov sum-product — jamais atteint)

**Leçon archivée** : La double contrainte add+mult sur le MÊME 4-tuple (h₁,h₂,h₃,h₄) est structurellement dégénérée. Le couplage add/mult doit opérer sur des variables SÉPARÉES (pas les mêmes h). C'est un résultat négatif propre.

### Audit C155 (Agents 3+4)

**Trois niveaux de profondeur identifiés** :

| Niveau | Contenu | Valeur |
|--------|---------|--------|
| 1 (trivial) | Moyenne |S_H|² = r-1 par Parseval | Exercice L3, valeur zéro |
| 2 (modéré) | Fonctionnelles symétriques des modules orbitaux déterminées par tailles r_k | ≈ R154 reformulé proprement |
| 3 (non trivial) | Corrélations 2-point inter-orbites aussi insensibles à l'arithmétique de H | Vrai théorème, probabilité 20-25% |

**Risque KS4** : si l'énoncé est trivialement démontrable par Parseval + Jensen en 3 lignes (80% de probabilité selon Agent 3).

**Verdict** : C155 autorisée pour exécution courte au niveau 2.5 minimum (fonctionnelles des modules + corrélations 2-point inter-orbites). Un pur niveau 2 serait archivé comme proposition, pas comme théorème.

### Grille d'audit finale (Agent 4)

| Candidat | Statut | Agents Pour | Kill Switch déclenché |
|----------|--------|-------------|----------------------|
| A155 | **[ÉLIMINÉ]** | 0/4 | KS4 (trivialité universelle) |
| B155 | **[ÉLIMINÉ]** | 0/4 | Pré-disqualifiée R154+T4 |
| C155 | **[QUALIFIÉ AVEC RÉSERVE]** | 3/4 (conditionnel) | KS4 surveillé |
| D155 | **[SANS CANDIDAT]** | — | — |

---

## RÉSULTAT NÉGATIF PRINCIPAL

**Théorème informel T175** (dégénérescence de la double contrainte add-mult) : Pour tout sous-ensemble A d'un corps fini F_q, le nombre de 4-uplets (a₁,a₂,a₃,a₄) ∈ A⁴ satisfaisant simultanément a₁/a₂ = a₃/a₄ et a₁+a₄ = a₂+a₃ est exactement |A|(2|A|-1). En particulier, l'énergie croisée E^{×,+} ne contient aucune information arithmétique sur A.

**Preuve** : La substitution de la contrainte multiplicative dans l'additive force {a₃,a₄} = {a₁,a₂} (voir audit Agent 3, 5 lignes).

**Corollaire** : Le couplage add/mult sur H ne peut pas être réalisé via une double contrainte sur les MÊMES variables. Il faut séparer les variables additives et multiplicatives.

---

## CHECKPOINT OBLIGATOIRE

1. **Quelle piste est réellement non redondante ?** A155 était non redondante (objet jamais construit) mais trivialement dégénérée. C155 est partiellement redondante (formalise R154) mais utile pour la publication.

2. **Quel objet est le plus nouveau ?** A155 (énergie croisée E^{×,+}) était formellement le plus nouveau, mais sa trivialité annule cette nouveauté. La leçon T175 (dégénérescence double contrainte) est le vrai résultat neuf.

3. **Quelle piste change réellement la capacité d'attaque ?** Aucune directement. C155 au niveau 3 fermerait la classe module-only, orientant le futur vers les objets bilinéaires/phases — mais c'est une orientation, pas une percée.

4. **Quelle piste doit mourir ?** A155 morte (trivialité). B155 morte (pré-disqualifiée). D155 sans candidat. C155 survit conditionnellement.

5. **Une exécution courte est-elle légitime ?** Oui, pour C155, sous 4 conditions strictes :
   - Énoncé précis avant exécution
   - Critère de non-trivialité (preuve > 10 lignes au-delà de Parseval+Jensen)
   - Budget 1 round max
   - Scope : modules + corrélations 2-point inter-orbites minimum

6. **Condition de non-boucle** : C155 ne boucle pas car c'est un résultat d'impossibilité, pas une tentative de borne. Pas de risque de retomber sur "il suffit de borner E(H-1)".

---

## REGISTRE FAIL-CLOSED FINAL

| Objet | Statut |
|-------|--------|
| A155 Énergie croisée E^{×,+}(Γ) | [ÉLIMINÉ] — trivialité algébrique universelle |
| T175 Dégénérescence double contrainte add+mult | [OBJET RÉEL] — identité prouvée, 5 lignes |
| B155 Compatibilité inter-facteurs | [ÉLIMINÉ] — pré-disqualifiée R154+T4 |
| C155 Impossibilité module-only | [QUALIFIÉ AVEC RÉSERVE] — exécution courte autorisée sous conditions |
| D155 Monodromie binaire | [SANS CANDIDAT] — faisceau non identifié |
| Couplage add/mult sur mêmes variables | [MORT] — structurellement dégénéré |
| Couplage add/mult sur variables séparées | [SEMI-RÉEL] — direction future non testée |
| Suspension recherche pure Bloc 3 | **MAINTENUE (6ème : R141, R151, R152, R153, R154, R155)** |

---

## BILAN QUANTITATIF

| Métrique | Valeur |
|----------|--------|
| Pistes soumises | 4 |
| Pistes qualifiées | 2 (A, C) |
| Candidats proposés | 2 (A155, C155) |
| Candidats éliminés | 1 (A155) |
| Candidats en exécution courte | 1 (C155, conditionnel) |
| Pistes mortes ajoutées | 3 (A155 trivialité, B155 pré-disqualifiée, D155 sans candidat) |
| Informations négatives | 1 (T175 dégénérescence double contrainte add-mult) |
| Kill switches déclenchés | 2/7 sur A155 (KS4 vacuité, KS5 instanciation triviale) |
| IVS | 2.0/10 |
| Confirmations suspension | 6 (R141, R151, R152, R153, R154, R155) |

---

## RECOMMANDATION STRATÉGIQUE

**MODE INCHANGÉ : PUBLICATION + calcul préparatoire monodromie.**

Le projet reste en suspension de la recherche pure Bloc 3. R155 ajoute :
1. T175 (dégénérescence double contrainte) — archivable dans la publication
2. C155 potentiellement exécutable en R156 comme théorème de nettoyage pour la publication
3. La leçon que le couplage add/mult doit opérer sur des variables séparées — direction future non testée mais non urgente

**Condition de relance** :
- Amélioration BGK publiée (ε > 0.215 pour sous-groupes de taille log p)
- OU identification d'un faisceau non trivial pour la monodromie géométrique
- OU résultat sum-product pour |A| ≈ log p (gap majeur en TAN)
