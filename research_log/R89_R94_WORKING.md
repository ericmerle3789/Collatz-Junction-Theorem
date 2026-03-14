# CAMPAGNE R89→R94 — WORKING FILE

## R89 — RECALAGE ET QUALIFICATION DES AXES

### Date: 14 mars 2026

---

### AXE 1 — FERMETURE COMPUTATIONNELLE MÉTHODIQUE DU GAP

**État actuel**: k=21 PROUVÉ (R84). Méthode: DP hiérarchique + CRT backtracking.
**20 valeurs restantes**: k=22..41.
**Manque concret**: Extension méthodique SANS k-par-k comme philosophie.

**Investigateur Gap — Analyse**:
- La méthode R84 (DP mod facteurs de d(k) + CRT) est reproductible
- MAIS: appliquer séquentiellement à k=22,23,...,41 = k-par-k interdit
- La seule valeur de l'Axe 1 est si on peut: (a) CERTIFIER la méthode elle-même comme programme complet, ou (b) identifier une obstruction computationnelle qui INFORME la théorie
- Question: peut-on prouver que la méthode CRT-DP SUFFIT pour tout k=22..41 en PRINCIPE (complexité bornée) sans l'exécuter k par k?

**Innovateur Gap — Candidats**:
- CANDIDAT G1: "Méta-certification CRT" — Prouver que pour tout k=21..41, d(k) admet toujours un facteur premier p avec ord_p(2) > √p ET C(S-1,k-1)/p < 1. Si oui, la méthode DP+CRT est GARANTIE de terminer.
- CANDIDAT G2: "Compression d'état DP" — Borner la complexité mémoire/temps de la méthode pour les k restants. Si polynomial en k, c'est un PROGRAMME computationnel complet certifiable.

### AXE 2 — RECHERCHE THÉORIQUE GÉNÉRALE SUR LE VERROU MULTILINÉAIRE

**État actuel**: PO-R87 formulé. Verrou = produit corrélé ∏σ_i(t,v).
**Manque concret**: Borne non triviale sur le produit multilinéaire.

**Investigateur Théorie — Analyse des blocages**:
1. Gauss bounds individuels TIGHT → pas d'amélioration par facteur
2. Produit naïf (√p)^k EXPLOSE → besoin de cancellation croisée
3. FKM (Fouvry-Kowalski-Michel) = phases polynomiales, pas exponentielles (2^b)
4. BDG (Bourgain-Demeter-Guth) = découplement pour phases polynomiales, pas 2^b
5. VMVT (Vinogradov) = phases polynomiales, pas 2^b

**Cause racine du blocage**: La phase 2^b est EXPONENTIELLE en b, pas polynomiale.
Tous les outils standards de théorie analytique des nombres supposent des phases polynomiales.

**Question clé de l'Innovateur Théorie**: Existe-t-il un outil qui traite des phases EXPONENTIELLES (2^b mod p) dans un produit multilinéaire?

---

### VERDICTS INVESTIGATEUR HISTORIQUE

| Candidat | Verdict | Raison |
|----------|---------|--------|
| G1 (Méta-certification CRT) | **REDONDANT** | R34 (71/71 non-bloquants), R35 (CRT product réfuté), R31 (bad primes caractérisés) |
| G2 (Compression DP) | **PARTIELLEMENT REDONDANT** | R84 déjà conclusif: "faisable ~12/21 mais k-par-k, pas universel" |
| T1 (Bourgain sum-product direct) | **REDONDANT** | R73 (mur O(log p), 5 outils circulaires incluant Bourgain) |
| T2 (Trace functions FKM) | **NOVEL mais obstruction fondamentale** | b→2^b n'est PAS algébrique → pas de sheaf ℓ-adique direct |

### DÉCOUVERTE CRITIQUE R89 — LE CANDIDAT T2-BIS

**Reformulation sous-groupe**: σ_i(t) = Σ_{h∈H} e_p(t·α_i·h) où H = ⟨2⟩ ⊂ F_p*.

**Product-to-sum expansion** (OBJET NOUVEAU):
∏_{i=0}^{k-1} σ_i(t) = Σ_{(h_0,...,h_{k-1}) ∈ H^k} e_p(t · Σ_i α_i·h_i)

C'est une UNIQUE somme exponentielle sur H^k avec phase LINÉAIRE Σ_i α_i·h_i.

**Pourquoi ce n'est PAS R73**:
- R73 étudiait des sommes INDIVIDUELLES courtes (|H| = O(log p) termes)
- Ici on étudie une somme sur H^k (|H|^k termes) — objet COMBINATOIREMENT différent
- La somme sur t donne: Σ_t ∏σ_i(t) = p · N_0(p) — connexion directe à la cible
- L'objet est le nombre de solutions de Σ_i α_i·h_i ≡ 0 mod p avec h_i ∈ H

**Formulation précise du CANDIDAT T2-BIS** ("Subgroup Linear Sum — SLS"):
- **Objet**: N_H(α) = #{(h_0,...,h_{k-1}) ∈ H^k : Σ_i α_i·h_i ≡ 0 mod p}
- **Lemme candidat**: N_H(α) = |H|^k/p + E(α) avec |E(α)| < |H|^k/p pour k ≥ k_0
- **Si prouvé**: N_0(p) = C(S-1,k-1)/p + erreur contrôlée → N_0(d) = 0 via CRT
- **Réfutation test**: Calculer N_H(α) pour k=21, p=5,43,3221,34511 et comparer à |H|^k/p
- **Différence avec R73**: On ne borne PAS σ_i individuellement. On borne N_H directement.

**Outils disponibles pour N_H(α)**:
1. Bourgain-Glibichuk-Konyagin (2006): borne individuelle |σ_i| ≤ |H|·p^{-ε(δ)}
2. Bourgain multilinéaire (GAFA 2009): sommes sur A_1×...×A_k
3. Comptage additif: #{h_i ∈ H : Σα_i·h_i = 0} = problème de représentation dans sous-groupe

**Connexion au problème de Vinogradov sur sous-groupes**:
N_H(α) est un "problème de Waring sur H" : représenter 0 comme combinaison linéaire
à coefficients α_i d'éléments de H. Littérature: Shparlinski, Garcia, Konyagin.

### CANDIDATS SURVIVANTS R89

| Candidat | Axe | Statut | Mordant |
|----------|-----|--------|---------|
| G1 | Gap | **[ÉLIMINÉ]** | Redondant R34/R35 |
| G2 | Gap | **[ÉLIMINÉ]** | Partiellement redondant R84, impact 3/10 |
| T1 | Théorie | **[ÉLIMINÉ]** | Redondant R73 (circulaire) |
| T2 | Théorie | **[À REFORMULER]** → T2-bis | Obstruction sheaf, mais reformulé en SLS |
| **T2-bis (SLS)** | Théorie | **[QUALIFIÉ AVEC RÉSERVE]** | Objet nouveau, lemme candidat, réfutation testable |

### CHECKPOINT R89

1. **Quel axe a progressé?** Axe 2 (théorie) — candidat T2-bis qualifié
2. **Quel candidat a gagné en mordant?** T2-bis (SLS): objet précis, lemme formulé, réfutation testable
3. **Quel candidat a perdu sa non-redondance?** G1, T1 (redondants), G2 (faible impact)
4. **Quel candidat a progressé en preuve?** T2-bis: [HEURISTIQUE] — lemme formulé mais non testé
5. **Quel candidat doit être tué?** G1, G2, T1, T2 (tous sauf T2-bis)
6. **Pourquoi un round sup. justifié?** T2-bis a un lemme testable non encore testé. R90 doit pousser.

**Décision**: CONTINUER → R90 pour pousser T2-bis

---

## R90 — PREMIÈRE POUSSÉE STRUCTURELLE

### Résultats de la poussée T2-bis (SLS)

#### Chaîne de preuve formalisée (5 étapes)

| Étape | Contenu | Statut |
|-------|---------|--------|
| 1 | Orthogonalité des caractères → N_0(p) = C/p + (1/p)Σ_t Φ(t) | **[PROUVÉ]** |
| 2 | Non-factorisation sur simplexe (vs boîte) | **[PROUVÉ]** |
| 3 | Gap simplexe vs boîte — passage non borné | **[GAP]** |
| 4 | Réduction mod r → formulation boîte pondérée | **[CORRECT, BORNE MANQUANTE]** |
| 5 | Relation clé: N_0(p) = (C/r^k)·N_H(0) + R | **[CORRECT, BORNE MANQUANTE]** |

#### Relation exacte découverte
```
N_0(p) = (C/r^k) · N_H(0) + R

où:
- N_H(0) = #{(h_0,...,h_{k-1}) ∈ H^k : Σ α_i·h_i ≡ 0 mod p}
- R = reste dû à la variation des poids W(b) = C((N-|b|)/r + k-1, k-1)
- W̄ = C/r^k (poids moyen)
```

#### Verrou: Le reste R
- R provient de la non-uniformité de W(b) sur la boîte {0,...,r-1}^k
- W dépend de |b| = Σb_i seulement → analysable par Fourier sur Z/rZ
- Décomposition: R = (1/p) Σ_t Σ_{ℓ≥1} Ŵ(ℓ) · ∏_i (Σ_b ω^{ℓb} · e_p(t·α_i·2^b))
- Les sommes intérieures sont des sommes HYBRIDES (caractère additif F_p × caractère Z/rZ)
- **Régime Collatz**: N/r peut être O(1) → poids varient drastiquement → R potentiellement O(terme principal)

#### Littérature BGK — Analyse quantitative
- BGK (2006): |σ_i(t)| ≤ r·p^{-ε(δ)} avec δ = log(r)/log(p)
- Meilleur ε connu ≈ 0.011 (Di Benedetto et al., pour |H| > p^{1/4})
- Pour le produit: besoin kε > 1, soit k > 1/0.011 ≈ 91
- **k ∈ [21,41] → INSUFFISANT quantitativement**

#### Littérature Waring sur sous-groupes
- Cochrane-Hart-Pinner-Spencer (2014): représentation d'éléments par sommes dans sous-groupes
- Garcia-Voloch (1988): courbes de Fermat — pertinent pour k=2 seulement
- Tao (2011): confirme que cette réduction est connue et que les barrières sont fondamentales
- Tao (2019): modèle probabiliste pour Collatz, pas de preuve déterministe

#### Audit du candidat T2-bis (SLS)

**Forces**:
1. Objet mathématique précis et NOUVEAU dans le contexte du projet
2. Chaîne de preuve en 5 étapes, chacune avec statut clair
3. Relation exacte N_0(p) = (C/r^k)·N_H(0) + R identifiée
4. Connexion directe à la littérature existante (BGK, Cochrane, Tao)

**Faiblesses CRITIQUES**:
1. Le reste R est le VRAI verrou — pas de borne connue
2. BGK quantitativement insuffisant (ε ≈ 0.011 vs besoin ε > 1/k ≈ 0.048)
3. Régime Collatz (N/r = O(1)) = pire cas pour l'approximation uniforme
4. Tao lui-même identifie les barrières harmoniques comme fondamentales

**Statut du lemme candidat**: [HEURISTIQUE] → [BLOQUÉ]
- Le lemme "N_H(0) = r^k/p + o(r^k/p)" est VRAI (c'est le Ratio Law)
- MAIS la chaîne N_0(p) ← N_H(0) est brisée par le reste R non borné

### Investigateur Théorie — Diagnostic d'impasse R90

**Pourquoi T2-bis est bloqué?**
La cause racine n'est PAS le comptage N_H(0) (qui est probablement bien compris via BGK).
La cause racine est le PASSAGE du simplexe au sous-groupe:
- Le simplexe impose Σa_i = S → poids non uniformes W(b) sur la boîte {0,...,r-1}^k
- Ces poids varient drastiquement quand N/r = O(1)
- Le reste R capture EXACTEMENT cette non-uniformité

**Le vrai verrou reformulé**: Ce n'est PAS "borner ∏σ_i" (PO-R87).
C'est: **borner la corrélation entre les poids W(b) et le produit e_p(t·Σα_i·2^{b_i})**.

**C'est un problème de DISCREPANCE PONDÉRÉE**: la distribution des poids W(b) sur la boîte
est-elle suffisamment "lisse" par rapport à la phase exponentielle?

### Innovateur Théorie — Nouveau candidat T3

**CANDIDAT T3: "Smooth Weight Lemma" (SWL)**

Le problème se réduit à: montrer que Ŵ(ℓ) décroît assez vite en ℓ.

**Objet**: Ŵ(ℓ) = r^{-k} · Σ_{b∈{0,...,r-1}^k} W(b) · ω_r^{-ℓ·|b|}

Puisque W dépend seulement de |b|, on peut réduire:
Ŵ(ℓ) = r^{-k} · Σ_{s=0}^{k(r-1)} M(s) · W_s · ω_r^{-ℓ·s}

où M(s) = nombre de (b_0,...,b_{k-1}) ∈ {0,...,r-1}^k avec |b|=s, et W_s = C((N-s)/r+k-1,k-1).

**Lemme candidat (SWL)**: Pour ℓ ≥ 1 et k suffisamment grand:
|Ŵ(ℓ)| ≤ C·r^{-k} · (1 - c/k) pour une constante c > 0

**Si prouvé**: Le produit |Ŵ(ℓ)| · |∏ sommes hybrides| peut être < C/(p·r^k) grâce à:
- Ŵ(ℓ) petit (décroissance)
- Les sommes hybrides = sommes de Gauss modifiées, bornées par √p individuellement

**Réfutation test**: Calculer numériquement Ŵ(ℓ) pour k=21, p=5 (r=4), et vérifier la décroissance.

### CHECKPOINT R90

1. **Quel axe a progressé?** Axe 2 — chaîne formalisée, relation exacte, diagnostic d'impasse
2. **Quel candidat a gagné en mordant?** T2-bis: chaîne en 5 étapes MAIS bloqué par R
3. **Quel candidat a perdu sa non-redondance?** Aucun nouveau
4. **Quel candidat a progressé en preuve?** T2-bis: [HEURISTIQUE] → [BLOQUÉ] (honnête). T3 (SWL) émerge.
5. **Quel candidat doit être tué?** T2-bis tel quel est BLOQUÉ. T3 le remplace.
6. **Pourquoi un round sup. justifié?** T3 (SWL) a un test de réfutation concret (calcul Ŵ). R91 doit tester.

**Décision**: CONTINUER → R91 pour tester T3 (SWL) et audit croisé

---

## R91 — AUDIT CROISÉ ET RÉDUCTION DU CHAMP

### Anti-redondance T3 (SWL): NOVEL (confirmé par Investigateur Historique)
Aucune piste fermée n'étudie le spectre de Fourier de W(b). Mais c'est SANS OBJET car T3 est RÉFUTÉ (spectre plat).

### Résultat clé: Spectre de W parfaitement plat

**THÉORÈME (prouvé analytiquement et vérifié k=21, p=5)**:
Pour tout ℓ ∈ {0,...,r-1}: |Ŵ(ℓ)| = |Ŵ(0)| exactement.

**Preuve**: W(b) est supporté sur {b : |b| ≡ N mod r}. Sur cette classe,
ω_r^{-ℓ·|b|} = ω_r^{-ℓ·N} · (ω_r^r)^{ℓ·j} = ω_r^{-ℓ·N} (constant).
Donc Ŵ(ℓ) = ω_r^{-ℓ·N} · Ŵ(0). QED.

**Vérification numérique k=21, p=5, r=4**:
| s | W_s | M_21(s,4) | M·W |
|---|-----|-----------|-----|
| 1 | 1771 | 21 | 37,191 |
| 5 | 231 | 52,689 | 12,171,159 |
| 9 | 21 | 8,903,685 | 186,977,385 |
| 13 | 1 | 373,980,705 | 373,980,705 |
Total = 573,166,440 = C(33,20) ✓
|Ŵ(1)/Ŵ(0)| = |Ŵ(2)/Ŵ(0)| = |Ŵ(3)/Ŵ(0)| = 1.000 exactement ✓

### Conséquence: T3 (SWL) est MORT

Le candidat T3 reposait sur l'hypothèse que Ŵ(ℓ) décroît pour ℓ ≥ 1.
C'est FAUX: le spectre est parfaitement plat.
La cause profonde: le support de W sur une unique classe mod r rend W
"invisible" à la transformée de Fourier sur Z/rZ.

**Statut T3**: [RÉFUTÉ] — spectre plat, zéro décroissance.

### Diagnostic d'impasse R91

**Investigateur Théorie — Analyse causale**:

Le problème est maintenant PLUS CLAIR qu'avant R89:

1. La chaîne N_0(p) = (C/r^k)·N_H(0) + R est EXACTE
2. Le reste R satisfait |R| = |Ŵ(0)| · |Σ_t Σ_{ℓ≥1} ω_r^{-ℓN} · ∏_i S_i^{(ℓ)}(t)|
   où S_i^{(ℓ)}(t) = Σ_{b=0}^{r-1} ω_r^{ℓb} · e_p(t·α_i·2^b)
3. Puisque |Ŵ(ℓ)| = |Ŵ(0)|, AUCUNE aide ne vient des poids
4. Tout le travail repose sur les sommes HYBRIDES S_i^{(ℓ)}(t)

**Le verrou reformulé (version R91)**:
```
Borner Σ_{t=1}^{p-1} ∏_{i=0}^{k-1} S_i^{(ℓ)}(t)

où S_i^{(ℓ)}(t) = Σ_{b=0}^{r-1} ω_r^{ℓb} · e_p(t·α_i·2^b)
```

C'est le même produit que PO-R87 mais avec un twist SUPPLÉMENTAIRE ω_r^{ℓb}.

### Innovateur Théorie — Le twist ω_r^{ℓb} change-t-il quelque chose?

**Observation clé**: ω_r^{ℓb} = e^{2πiℓb/r}. Combiné avec e_p(t·α_i·2^b):
S_i^{(ℓ)}(t) = Σ_{b=0}^{r-1} exp(2πi(ℓb/r + t·α_i·2^b/p))

C'est une somme de Gauss GÉNÉRALISÉE avec phase additionnelle linéaire en b.

**Propriété**: {2^b : b=0,...,r-1} parcourt le sous-groupe H. Donc:
S_i^{(ℓ)}(t) = Σ_{h∈H} χ_ℓ(h) · e_p(t·α_i·h)

où χ_ℓ est le caractère multiplicatif de H défini par χ_ℓ(2^b) = ω_r^{ℓb}.

C'est une somme de caractère multiplicatif × caractère additif COMPLÈTE sur H.
Par Weil (sur le sous-groupe), si H est un sous-groupe cyclique d'ordre r:

|S_i^{(ℓ)}(t)| ≤ √p pour ℓ ≠ 0 (sous conditions)

MAIS: Weil donne √p par facteur → produit (√p)^k = p^{k/2} → MÊME MUR que MDL.

### CANDIDAT T4: "Anticorrélation des phases hybrides"

Au lieu de borner |∏ S_i^{(ℓ)}(t)| facteur par facteur,
étudier la somme SUR t: Σ_t ∏ S_i^{(ℓ)}(t).

C'est une somme de produits de sommes de Gauss généralisées.
Quand on somme sur t, des CANCELLATIONS croisées apparaissent.

**Développement**:
Σ_t ∏_i S_i^{(ℓ)}(t) = Σ_t Σ_{(h_i)∈H^k} ∏ χ_ℓ(h_i) · e_p(t·Σα_i·h_i)
= Σ_{(h_i)∈H^k} (∏ χ_ℓ(h_i)) · (Σ_t e_p(t·Σα_i·h_i))
= p · Σ_{(h_i)∈H^k, Σα_i·h_i≡0} ∏ χ_ℓ(h_i)
= p · Σ_{(h_i)∈Z_H(α)} χ_ℓ(h_0·h_1·...·h_{k-1})

où Z_H(α) = {(h_i) ∈ H^k : Σα_i·h_i ≡ 0 mod p}.

**OBJET NOUVEAU**: La somme pondérée par χ_ℓ sur l'ensemble des zéro-sommes Z_H(α).

**Lemme candidat T4**: Pour ℓ ≠ 0:
|Σ_{(h_i)∈Z_H(α)} χ_ℓ(∏h_i)| ≤ N_H(0) · δ(k)

avec δ(k) → 0 quand k → ∞ (cancellation des phases χ_ℓ sur Z_H).

**Justification heuristique**: Les h_i dans Z_H sont contraints par Σα_i·h_i = 0,
mais les PRODUITS h_0·...·h_{k-1} sont quasi-aléatoires dans H
(car la contrainte additive ne contraint pas le produit multiplicatif).
Donc χ_ℓ(∏h_i) oscille → cancellation.

**Réfutation test**: Énumérer Z_H(α) pour k=21, p=5, r=4 et calculer la somme pondérée.

### Anti-redondance T4
- Pas de piste fermée sur "sommes de caractères multiplicatifs sur zéro-ensembles additifs"
- Distinct de R73 (bornes individuelles, pas de somme sur Z_H)
- Distinct de MDL (bornes facteur par facteur)
- Distinct de T2-bis (qui ne considérait pas le twist χ_ℓ)
- **NOVEL** — objet mathématique pas encore étudié dans le projet

### CANDIDATS VIVANTS après R91

| Candidat | Statut | Mordant |
|----------|--------|---------|
| T2-bis (SLS) | [BLOQUÉ] → absorbé dans la chaîne | Chaîne correcte mais R non borné |
| T3 (SWL) | **[RÉFUTÉ]** | Spectre plat |
| **T4 (Anticorrélation hybride)** | **[QUALIFIÉ AVEC RÉSERVE]** | Objet nouveau, réfutation testable |

### CHECKPOINT R91

1. **Quel axe a progressé?** Axe 2 — T3 TUÉ (résultat négatif profond), T4 émerge
2. **Quel candidat a gagné en mordant?** T4: formulation précise, objet nouveau
3. **Quel candidat a perdu?** T3 (spectre plat = mort instantanée)
4. **Quel candidat a progressé en preuve?** T4: [HEURISTIQUE] — pas encore testé
5. **Quel candidat tuer?** T3 (déjà mort)
6. **Round sup. justifié?** OUI — T4 a un test de réfutation concret non exécuté

**Décision**: CONTINUER → R92 pour tester T4

---

## R92 — TEST DE PREUVE / TEST DE CERTIFICATION

### Test numérique T4 (k=21, p=5, r=4)

**Résultats** (script r92_test_t4.py):
- N_H(0) = 879,609,302,220
- r^k/p = 4^21/5 = 879,609,302,220.8 → Ratio Law confirmée
- **W_1 = W_2 = W_3 = 0 exactement** (cancellation parfaite)
- |W_ℓ/(p·N_H(0))| = 0 pour tout ℓ ∈ {1,2,3}

**Mécanisme**: Pour p=5, ord_5(3) = 4 = r → α_i cyclent avec période 4 → tous les σ_i(t) sont identiques. La cancellation vient de la somme sur t (4 termes de magnitude p^{k/2} dont les phases s'annulent exactement).

**Caveat**: p=5 est un cas TRÈS spécial (ord_5(2) = ord_5(3) = 4). Il faut vérifier des cas moins dégénérés.

### Semi-formalisation de T4

**THÉORÈME (PARTIELLEMENT PROUVÉ)**:
Soit p premier ≥ 5, H = ⟨2⟩ ⊂ F_p*, r = ord_p(2), α_i = 3^{k-1-i} mod p.
Pour tout ℓ ∈ {1,...,r-1}:

|Σ_{(h_i)∈Z_H(α)} χ_ℓ(∏h_i)| ≤ p·(√p/r)^k · N_H(0)/(r^k/p)

**Chaîne de preuve** (5 étapes, toutes vérifiées):

| Étape | Contenu | Statut |
|-------|---------|--------|
| A | Détection par caractère additif | [PROUVÉ] |
| B | t=0 → contribution nulle (χ_ℓ non trivial) | [PROUVÉ] |
| C | Lifting χ_ℓ → F_p* : S_i^{(ℓ)}(t) = (r/(p-1))·Σ G(χ̃^n, ψ_{tα_i}) | [PROUVÉ] |
| D | Borne Gauss: |S_i^{(ℓ)}(t)| ≤ √p | [PROUVÉ] — mais LÂCHE |
| E | Produit: |Σ_t ∏ S_i^{(ℓ)}| ≤ p^{k/2+1} → ratio = p·(√p/r)^k | [PROUVÉ] |

**Condition de mordant**: ratio → 0 ⟺ **r > √p** (i.e., ord_p(2) > √p)

### Résultats de moment (NOUVEAUX)

**L² exact**: Σ_{t≠0} |S_i^{(ℓ)}(t)|² = rp
→ RMS(|S_i|) = √(rp/(p-1)) ≈ √r (PAS √p!)
→ Le bound √p est LÂCHE d'un facteur √(p/r)

**Si on pouvait utiliser √r au lieu de √p**:
ratio = p·(√r/r)^k = p·r^{-k/2} → 0 pour tout r ≥ 2
→ T4 serait prouvé INCONDITIONNELLEMENT

**Gap**: Passer du moment L² (√r en moyenne) au sup (√p worst-case) perd tout.

### Découverte structurelle: orbite de ⟨3⟩

S_j^{(ℓ)}(t) = S_0^{(ℓ)}(t·3^{k-1-j})

Le produit ∏_i S_i^{(ℓ)}(t) = ∏_i S_0^{(ℓ)}(t·3^{k-1-i})
= S_0^{(ℓ)} évaluée en k points de l'orbite {t, t·3^{-1}, t·3^{-2}, ..., t·3^{-(k-1)}} mod p.

C'est une UNIQUE fonction évaluée le long de l'action multiplicative de ⟨3⟩ sur F_p*.

### CANDIDAT T5: "Equidistribution orbitale de ⟨3⟩"

**Idée**: Si les points {t·3^j : j=0,...,k-1} sont "bien distribués" dans F_p*,
alors le produit ∏ S_0(t·3^j) se comporte comme (RMS)^k ≈ r^{k/2}.

**Lemme candidat T5**: Sous l'hypothèse que ⟨3⟩ est "pseudo-aléatoire" dans F_p*:
|Σ_t ∏_{j=0}^{k-1} S_0^{(ℓ)}(t·3^j)| ≤ C · (rp)^{k/2} / p^{(k-2)/2}

**Justification**: Par 4ème moment / Holder:
- k facteurs, chacun de RMS √r
- Mais corrélations dues à l'orbite de 3
- La structure orbite introduit des "collisions" quand 3^a ≡ 3^b mod p (i.e., a≡b mod ord_p(3))

**Gap critique**: Besoin d'une borne sur les moments supérieurs de S_0^{(ℓ)} le long d'orbites de ⟨3⟩.
C'est un problème de "correlation of character sums along multiplicative orbits" — littérature: Katz, FKM.

### Audit T5

**Investigateur Historique**:
- PAS de piste fermée sur "corrélations le long d'orbites multiplicatives"
- Distinct de R73 (bornes individuelles, pas orbitales)
- Distinct de MDL (facteur par facteur)
- **NOVEL**

**Auditeur Fail-Closed**:
- T5 est [HEURISTIQUE]: pas de lemme prouvé, seulement la structure orbitale identifiée
- Le passage L² → L^k le long d'orbites est un problème OUVERT
- Mais la structure est CONCRÈTE et le problème est bien posé

### Bilan des candidats R92

| Candidat | Statut | Mordant | Preuve |
|----------|--------|---------|--------|
| T2-bis (SLS) | Absorbé | Chaîne exacte | [PROUVÉ] comme cadre |
| T3 (SWL) | [RÉFUTÉ] | Spectre plat | — |
| T4 (Anticorr. hybride) | **[PARTIELLEMENT PROUVÉ]** | Conditionnel r > √p | [SEMI-FORMALISÉ] |
| T5 (Equidist. orbitale) | [HEURISTIQUE] | Structure identifiée | [PAS PROUVÉ] |

### CHECKPOINT R92

1. **Quel axe a progressé?** Axe 2 — T4 PARTIELLEMENT PROUVÉ (conditionnel ord_p(2) > √p)
2. **Quel candidat a gagné?** T4: preuve correcte, 5 étapes formalisées, condition claire
3. **Quel candidat a perdu?** Aucun nouveau (T3 déjà mort)
4. **Quel candidat a progressé en preuve?** T4: [HEURISTIQUE] → [SEMI-FORMALISÉ] → [PARTIELLEMENT PROUVÉ (conditionnel)]
5. **Quel candidat tuer?** T5 est trop [HEURISTIQUE] pour survivre au tournoi
6. **Round sup. justifié?** OUI pour le tournoi final (T4 vs baseline)

**Décision**: CONTINUER → R93 tournoi final, puis R94 bilan

---

## R93 — TOURNOI FINAL DES SURVIVANTS

### Candidats en lice

| Candidat | Axe | Statut final | Score mordant |
|----------|-----|-------------|---------------|
| G1 (Méta-certification CRT) | Gap | [ÉLIMINÉ R89] — redondant | 0/10 |
| G2 (Compression DP) | Gap | [ÉLIMINÉ R89] — impact 3/10 | 1/10 |
| T1 (Bourgain direct) | Théorie | [ÉLIMINÉ R89] — redondant R73 | 0/10 |
| T2 (Trace functions) | Théorie | [REFORMULÉ → T2-bis] | — |
| T2-bis (SLS) | Théorie | [PROUVÉ comme cadre] — absorbé | 5/10 |
| T3 (SWL) | Théorie | [RÉFUTÉ R91] — spectre plat | 0/10 |
| **T4 (Anticorr. hybride)** | Théorie | **[PARTIELLEMENT PROUVÉ]** | **8/10** |
| T5 (Equidist. orbitale) | Théorie | [HEURISTIQUE] — pas de preuve | 3/10 |

### Classement final

**1er — T4 (Anticorrélation des phases hybrides)** [PARTIELLEMENT PROUVÉ]

Objet: Somme Σ_{Z_H(α)} χ_ℓ(∏h_i) — somme de caractère multiplicatif sur zéro-ensemble additif.
Lemme: |somme| ≤ p·(√p/r)^k · (r^k/p) = p^{k/2+1}/p = p^{k/2}
Condition: **ord_p(2) > √p** — vrai pour densité 1 des primes (Artin/Hooley)
Statut de preuve: 5 étapes [PROUVÉES], condition nécessaire identifiée
Test numérique: PASSÉ (k=21, p=5, cancellation exacte)
Connexion au programme: Ferme le reste R dans la décomposition N_0(p) = (C/r^k)·N_H(0) + R
Ce qui manque: (a) Cas ord_p(2) ≤ √p, (b) Vérification sur p plus grands

**2ème — T2-bis (SLS)** [PROUVÉ comme cadre]

Cadre exact absorbé dans T4. Valeur: la relation N_0(p) = (C/r^k)·N_H(0) + R est DÉFINITIVE.
Pas un candidat autonome mais un OUTIL essentiel.

**3ème — T5 (Equidist. orbitale)** [HEURISTIQUE, SUSPENDU]

Structure intéressante (∏ S_0(t·3^j) = produit le long d'orbite de ⟨3⟩) mais pas de preuve.
Pourrait lever la condition r > √p si les moments supérieurs sont bornés.
Suspendu: pas assez mûr pour le tournoi.

### Verdict Arbitre de Tournoi

**VAINQUEUR: T4** — seul candidat avec statut [PARTIELLEMENT PROUVÉ], chaîne formalisée,
test numérique passé, et condition de suffisance claire.

**Qualification globale**: T4 est [QUALIFIÉ AVEC RÉSERVE] car:
- La condition ord_p(2) > √p est nécessaire dans la preuve actuelle
- Cette condition est satisfaite pour "presque tous" les primes (densité 1 conditionnelle GRH)
- Pour les primes de d(k) spécifiquement, on peut VÉRIFIER la condition au cas par cas
- Le vrai progrès serait de lever cette condition (via T5 ou moments supérieurs)

### Progrès réel vs élégance trompeuse

**Progrès réel**:
1. Relation exacte N_0(p) = (C/r^k)·N_H(0) + R (NOUVEAU dans le projet)
2. Spectre plat des poids W (résultat NÉGATIF profond: élimine une route entière)
3. Preuve conditionnelle de T4 (5 étapes formalisées)
4. Moment L²: RMS = √r (PAS √p) — quantifie la lâcheté du bound
5. Structure orbitale: produit = S_0 évaluée le long de ⟨3⟩-orbite

**Ce qui N'EST PAS un progrès**:
- Aucun k supplémentaire du gap fermé (conforme à la consigne anti-computationnel)
- La condition r > √p n'est pas prouvée universellement
- Le passage L² → L^∞ reste le verrou technique fondamental

### CHECKPOINT R93

1. **Quel axe a progressé?** Axe 2 (théorie) — significativement. Axe 1 (gap) — mort dès R89.
2. **Quel candidat a gagné?** T4 — vainqueur unique avec preuve conditionnelle
3. **Quel candidat a perdu?** G1, G2, T1, T3 — tous éliminés
4. **Quel candidat a progressé en preuve?** T4: [HEURISTIQUE] → [PARTIELLEMENT PROUVÉ (conditionnel)]
5. **Quel candidat tuer?** T5 — suspendu (pas assez mûr)
6. **Round sup. justifié?** NON pour la recherche. OUI pour le bilan (R94).

**Décision**: PAUSE RECHERCHE → R94 bilan final de campagne
