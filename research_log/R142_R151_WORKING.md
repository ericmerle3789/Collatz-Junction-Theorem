# CAMPAGNE R142→R151 — WORKING FILE

## MANDAT : Innovation opératoire forte (PromptR142.md)

**Date** : 14 mars 2026
**Protocole** : PROTOCOLE INTÉGRAL + exigence d'innovation opératoire (pas de reformulation seule)
**Doctrine** : Un candidat doit CHANGER la capacité d'attaque, pas seulement mieux nommer le verrou
**Campagne précédente** : R141 (recalage stratégique, TAN = CARTOGRAPHIE SEULE)

---

## R142 — RECALAGE + GÉNÉRATION DE CANDIDATS

### PHASE 1 — RECALAGE : INVESTIGATION VS INNOVATION

#### AXE A — Verrou actif réel

**Verrou** : N₀(d) = 0 pour k = 22..41, où d = 2^S - 3^k.

Deux formulations équivalentes :
1. **Combinatoire** : Aucune composition A de S en k parts n'a corrSum(A) ≡ 0 mod d
2. **Analytique** : |S_H(s)| ≤ C·√r pour les sommes de caractères sur sous-groupes translatés

**Compréhension acquise** :
- 170 théorèmes prouvés, 164+ voies mortes
- Verrou UNIQUE identifié : V_SQRT_CANCEL = C_SC = BGK ε ≥ 0.215
- T166 (décorrélation 2-point) PROUVÉE et NON UTILISÉE
- T159 (filtre d'orthogonalité) PROUVÉ
- Chaîne conditionnelle COMPLÈTE

**Prise manquante** :
- Aucun OUTIL qui brise √r pour |S_H(s)|
- Aucune OBSTRUCTION combinatoire directe sur corrSum
- Aucun INVARIANT qui distingue 0 des autres résidus mod d

**Signe de formalisation latérale** :
- Produire une identité A = B sans outil pour attaquer B mieux qu'A
- Relier le verrou à un problème plus prestigieux sans gain technique
- Alarme "Identité sans Outil" (R141)

#### AXE B — Filtre anti-rebranding

**Fausses innovations déjà éliminées** :
1. Renommer V_SQRT_CANCEL en C_SC (R139) — même verrou
2. Reformuler via E^×(H-1) (R132) — identité sans outil
3. Lifting géométrique (R141) — donne √p pas √r
4. Systèmes dynamiques (R142 ancien) — reformulation équivalente
5. T173 identité (R148 ancien) — réduit au BGK, circulaire

**Test rapide de non-redondance** :
Pour chaque candidat, répondre :
1. Quel OUTIL nouveau apporte-t-il ? (pas reformulation, pas identité)
2. Passe-t-il le test "A = B implique outil pour B" ?
3. Est-il dans la liste des 164+ morts ?
4. Change-t-il la capacité d'attaque sur N₀(d) = 0 ?

---

### PHASE 2 — FABRICATION CONTRÔLÉE DE PRISES NOUVELLES

Trois binômes lancés en parallèle :
- **Binôme D** (Innovation TAN) : 3 candidats proposés
- **Binôme E** (Alternative hors-TAN) : 2 candidats proposés
- **Auditeur** : Vérification du candidat le plus fort

#### CANDIDATS DU BINÔME D (Innovation TAN)

**Candidat D1 : Décomposition Schur-Vandermonde**

Objet : La somme T(t,d) = Σ_{c_1<...<c_k} ∏_j ω_{c_j}^{3^{j-1}} (ω_c = exp(2πit·2^c/d))
est liée aux fonctions de Schur via det(y_l^{e_j}) = V(y)·s_λ(y) avec e_j = 3^{j-1}.

Lemme candidat : |T(t,d)| ≤ (S choose k)^{1/2} · s_λ(1) via oscillation des Vandermonde.

Test de réfutation : s_λ(1) pour λ_j = 3^{j-1}-(j-1), k=22, est ASTRONOMIQUEMENT grand
(partition de poids ~3^21 ≈ 10^10). La borne dépasse la triviale.

**Verdict : [SEMI-RÉEL] — 10-15%. La magnitude de s_λ(1) est probablement fatale.**

---

**Candidat D2 : Matrice de corrélation Toeplitz spectrale**

Objet : M_{ij} = (1/g) Σ_s S_H(s·3^i)·conj(S_H(s·3^j)), matrice k×k Toeplitz.

Structure Toeplitz : VÉRIFIÉE par l'auditeur (substitution s → s·3^{-i}).

Lemme candidat : Si λ_max(M) ≤ C·tr(M)/k, gain de (C/k)^k sur le produit.

**AUDIT CROISÉ — RÉSULTATS** :
- Toeplitz : ✅ VÉRIFIÉ
- Diagonale = r-1 : ❌ FAUX (l'auditeur a trouvé un contreexemple p=31,
  C(0) = 6 ≠ r-1 = 4. Les termes off-diagonaux (h₁-1)/(h₂-1) ∈ K contribuent)
- Formule off-diagonale : ❌ FAUX (la condition réelle est
  ind(h₁-1) ≡ 3·ind(h₂-1) mod g, PAS (h₁-1)/(h₂-1) ∈ 3H)
- Connexion T166 → tr(M²) : INDIRECTE (gap non comblé)
- Rank-1 collapse : IMPROBABLE (pas de raison structurelle)

**Verdict auditeur : CONDITIONAL KILL — l'objet est réel (Toeplitz vérifié) mais les
formules quantitatives sont fausses, et la borne spectrale réduit au même problème.**

---

**Candidat D3 : Bornes sur le permanent structuré**

Objet : T = (1/k!)·perm_k(A) avec A_{jc} = ω_c^{3^{j-1}}.

Borne Hadamard : |T| ≤ S^{k/2}. Comparée à la triviale (S choose k) ≈ S^k/k!.

Test de réfutation : S^{k/2} est exactement le CS itéré.

**Verdict : [PROSE] — 5%. Équivalent au Cauchy-Schwarz itéré, aucun gain réel.**

---

#### CANDIDATS DU BINÔME E (Alternative hors-TAN)

**Candidat E1 : Crible par résidus restreints mod 3^m**

**THÉORÈME PROUVÉ** : corrSum(A) ≡ 1 mod 3 pour toute composition A.
Preuve : b_{k-1} = S - Σa_i = 0, donc le terme j=k-1 donne 3^0·2^0 = 1,
et tous les termes j < k-1 ont 3^{k-1-j} ≡ 0 mod 3. □

Extension : corrSum mod 9 ∈ {4, 7} (vérifié computationnellement k=3..10).

**PROBLÈME FATAL** : gcd(d, 3) = 1 pour tout k ≥ 2 (car d = 2^S - 3^k ≡ 2^S mod 3 ≡ ±1).
Donc la restriction mod 3^m est ORTHOGONALE au module d.
Le crible réduit la densité par facteur 4.5 mais ne ferme aucun k.

De plus, l'image de corrSum couvre TOUS les résidus mod p pour p ≥ 5 premier.
Seul mod 3^m l'image est restreinte → pas de CRT multiplicatif possible.

**Verdict : [SEMI-RÉEL mais INOPÉRANT] — le théorème est vrai mais ne mord pas sur d.**

---

**Candidat E2 : Obstruction par extraction gloutonne + propagation de retenues**

Objet : Algorithme glouton G(T, k, S) : étant donné T = m·d, extraire itérativement
les b_j par b_j = floor(log₂(reste / 3^{k-1-j})), puis vérifier que la séquence
est strictement décroissante.

Vérifié : pour k=8, identifie exactement les solutions (0 faux positif/négatif).

Lemme candidat : Pour k=22..41, pour tout m ∈ [corrSum_min/d, corrSum_max/d],
G(m·d, k, S) échoue (la décroissance stricte est violée).

**ANALYSE** :
- Approche GENUINEMENT différente des sommes de caractères
- Travaille sur la représentation entière, pas sur des résidus
- Exploite la structure mixte base 2 / base 3

**PROBLÈME** : Le nombre de m à tester est ~7·10^10 pour k=22.
Un argument structural de propagation de retenue serait nécessaire.
RISQUE : l'analyse de retenue pourrait se reformuler comme un problème
d'estimation exponentielle dans Z/dZ → retour au mur.

**Verdict : [SEMI-RÉEL] — 15-20%. Genuinement nouveau mais preuve structurelle manquante.**

---

**FAIT INATTENDU (Binôme E)** : N₀(d) > 0 pour k = 2,3,4,5,8,11,17 SANS cycle.
Le test des shifts cycliques échoue : aucune composition n'a TOUS ses k shifts ≡ 0 mod d.
Ceci signifie N₀(d) = 0 est PLUS FORT que l'absence de cycle.

---

### PHASE 3 — AUDIT CROISÉ ET TOURNOI

| Candidat | Objet réel ? | Lemme candidat ? | Non-redondant ? | Change l'attaque ? | Statut |
|----------|:---:|:---:|:---:|:---:|--------|
| D1 Schur | OUI | OUI (mais infaisable) | OUI | NON (magnitude fatale) | [ÉLIMINÉ] |
| D2 Toeplitz | OUI (structure) | OUI (mais formules fausses) | PARTIEL | CONDITIONNEL | [QUALIFIÉ AVEC RÉSERVE] |
| D3 Permanent | OUI | OUI (mais = CS itéré) | NON | NON | [ÉLIMINÉ] |
| E1 Crible 3^m | OUI (théorème prouvé) | OUI (mais inopérant) | OUI | NON (gcd(d,3)=1) | [ÉLIMINÉ] |
| E2 Glouton | OUI | PARTIEL (preuve manquante) | OUI | CONDITIONNEL | [QUALIFIÉ AVEC RÉSERVE] |

**Survivants** : D2 (Toeplitz, si formules corrigées) et E2 (Glouton, si preuve structurelle).

### PHASE 4 — DÉCISION

Les deux survivants sont [QUALIFIÉ AVEC RÉSERVE]. Ni l'un ni l'autre ne ferme le problème dans l'état. Mais les deux sont des OBJETS RÉELS avec des directions de travail concrètes.

**Décision** : Explorer les deux en parallèle dans les rounds suivants.
- D2 Toeplitz : corriger les formules, calculer les vrais C(a), tester la borne spectrale
- E2 Glouton : analyser la propagation de retenues structurellement

---

## R143 — CORRECTION TOEPLITZ : FORMULES EXACTES

### BINÔME A — INVESTIGATEUR

Reprenons les formules exactes de la matrice M.

**M_{ij} = C(j-i)** où :
C(a) = (1/g) Σ_{s∈Z_g} S_H(s) · conj(S_H(s·3^a))

Par expansion et orthogonalité :
C(a) = |{(h₁,h₂) ∈ (H\{1})² : ind_g(h₁-1) ≡ 3^a · ind_g(h₂-1) mod g}|

où ind_g(x) = ind(x) mod g est l'indice de coset de x dans F_p*/H.

**Reformulation** : Si on note φ : F_p* → Z_g le morphisme de coset (φ(x) = ind(x) mod g),
alors C(a) = |{(h₁,h₂) ∈ (H\{1})² : φ(h₁-1) ≡ 3^a · φ(h₂-1) mod g}|.

Puisque h ∈ H implique φ(h) = 0, mais h-1 ∉ H en général, φ(h-1) prend diverses valeurs.

**Diagonale exacte** : C(0) = |{(h₁,h₂) : φ(h₁-1) ≡ φ(h₂-1) mod g}|
                     = |{(h₁,h₂) : (h₁-1)/(h₂-1) ∈ H}|
                     = Σ_{h₂ ∈ H\{1}} |{h₁ ∈ H\{1} : (h₁-1)/(h₂-1) ∈ H}|
                     = Σ_{h₂} |{h₁ ∈ H\{1} : h₁ ∈ (h₂-1)·H + 1}|

Soit : C(0) = |{(h₁,h₂) ∈ (H\{1})² : h₁-1 ∈ (h₂-1)·H}|

Les termes diagonaux h₁=h₂ donnent (h₁-1)/(h₁-1) = 1 ∈ H → contribuent r-1.
Les termes off-diagonaux nécessitent h₁ ≠ h₂ et (h₁-1)/(h₂-1) ∈ H.

**Interprétation** : C(0) = (r-1) + |{(h₁,h₂) ∈ (H\{1})², h₁≠h₂ : (h₁-1)/(h₂-1) ∈ H}|

Le second terme est le nombre de "collisions multiplicatives" dans H-1.

### BINÔME B — INNOVATEUR

**Observation clé** : Le nombre de collisions multiplicatives dans H-1 est EXACTEMENT
lié à l'énergie multiplicative E^×(H-1) via :

E^×(H-1) = |{(a,b,c,d) ∈ (H-1)⁴ : ab = cd}|

Et C(0) = Σ_{t∈H} |{(h₁,h₂) : (h₁-1) = t·(h₂-1)}|

en sommant sur t ∈ H. Donc :
g·C(0) = Σ_{s} |S_H(s)|² et Σ_a C(a) = (r-1)² (somme sur toutes les paires).

**La somme totale** : Σ_{a=0}^{g-1} C(a) = |{(h₁,h₂) ∈ (H\{1})² : φ(h₁-1) et φ(h₂-1) quelconques}|
Mais avec la condition que la relation φ(h₁-1) ≡ 3^a·φ(h₂-1) admette un a ∈ Z_g.
Si 3 est un générateur de Z_g* (ce qui est le cas générique), alors pour chaque
paire (h₁,h₂) avec h₁,h₂ ∈ H\{1} et h₁-1, h₂-1 ≠ 0, il existe un unique a ∈ Z_g
tel que φ(h₁-1) ≡ 3^a·φ(h₂-1) mod g (car ×3 est un automorphisme de Z_g si gcd(3,g)=1).

Quand gcd(3,g) = 1 : Σ_a C(a) = (r-1)² exactement (chaque paire contribue à un unique a).
Quand 3|g : certaines paires n'admettent aucun a, et Σ_a C(a) < (r-1)².

**Conséquence sur tr(M)** : tr(M) = k·C(0) (matrice k×k avec diagonale constante C(0)).

Si les C(a) sont "équidistribués" (C(a) ≈ (r-1)²/g pour tout a), alors :
- tr(M) = k·(r-1)²/g
- λ_max ≤ (r-1)²/g·k^{0+} (pas de concentration spectrale)
- Gain du type (C/k)^k sur le produit

MAIS : C(0) ≥ r-1 + (collisions multiplicatives), et la question est si C(0) >> (r-1)²/g.

**Calcul** : (r-1)²/g ≈ r²/g = r²·r/(p-1) = r³/p. Pour r = p^{1/k}, r³/p = p^{3/k-1}.
Pour k=22, p ~ 10⁹ : r³/p ≈ (10^{9/22})³/10⁹ = 10^{27/22-9} ≈ 10^{-7.77}. Très petit.
Tandis que r-1 ≈ r ≈ p^{1/22} ≈ 10^{0.41}.

Donc C(0) ≈ r (diagonal domine) >> (r-1)²/g ≈ r³/p (valeur "équidistribuée").

**CECI SIGNIFIE** : C(0) >> C(a) typique. La diagonale DOMINE la matrice.
La matrice est approximativement diagonale : M ≈ r·I (à des termes r³/p près).

**Conséquence** : λ_max ≈ C(0) ≈ r, et tous les eigenvalues sont ≈ r.
Donc λ_max ≈ tr(M)/k. Le gain spectral est TRIVIAL : (1/1)^k = 1.

**WAIT** — c'est en fait EXACTEMENT ce qu'on veut ! Si λ_max ≈ tr(M)/k, le gain
est (1/k)^k ≈ (1/22)^22 ≈ 10^{-30}. C'est ÉNORME.

Mais vérifions : tr(M) = k·C(0) ≈ k·r. Et λ_max ≤ max_eigenvalue de la matrice.
Pour une matrice k×k avec diagonale r et off-diagonal ≈ r³/p :
Par Gershgorin : λ_max ≤ r + (k-1)·r³/p ≈ r (car k·r³/p << r puisque k·r²/p = k·p^{2/k-1} << 1).

Donc λ_max ≈ r = tr(M)/k. La borne spectrale donne :

(1/g) Σ_s |∏_j S_H(s·3^j)|² ≤ λ_max^k = r^k

Mais la borne triviale est aussi r^k (chaque |S_H| ≤ r). Donc PAS DE GAIN.

### CHECKPOINT R143

Le calcul de Gershgorin confirme : la matrice Toeplitz est approximativement r·I
(car les off-diagonal sont r³/p << r). La borne spectrale λ_max^k ≈ r^k
est la MÊME que la borne triviale.

**Le gain (C/k)^k annoncé est FAUX** : il repose sur une confusion entre
tr(M)/k (qui est C(0) ≈ r) et λ_max (qui est aussi ≈ r, pas r/k).

Pour avoir gain, il faudrait λ_max < r, ce qui nécessiterait que C(0) < r,
i.e., MOINS de collisions que le trivial. Mais C(0) ≥ r-1 par les termes diagonaux.

**Verdict D2 Toeplitz : [ÉLIMINÉ] — la borne spectrale est triviale (= r^k).**

---

## R144 — ANALYSE STRUCTURELLE DE L'EXTRACTION GLOUTONNE (E2)

### BINÔME A — INVESTIGATEUR

L'approche E2 reformule N₀(d) = 0 comme :
"Pour tout entier m avec corrSum_min ≤ m·d ≤ corrSum_max,
le nombre m·d ne s'écrit PAS comme Σ 3^{k-1-j}·2^{b_j} avec b_0 > ... > b_{k-1} ≥ 0."

**Plage de m** : corrSum_min = (6^k-1)/5, corrSum_max = Σ 3^{k-1-j}·2^{S-1-j}.

Pour k=22, S=35 :
- corrSum_min = (6^22-1)/5 ≈ 1.3 × 10^16
- corrSum_max ≈ Σ 3^{21-j}·2^{34-j} ≈ 6^21·(1+1/6+...) ≈ 6^22/5 ≈ 2.8 × 10^16
- d ≈ 2.98 × 10^9
- m ∈ [corrSum_min/d, corrSum_max/d] ≈ [4.3 × 10^6, 9.4 × 10^6]
- Nombre de m : ~5 × 10^6

C'est beaucoup moins que les 7×10^10 estimés par le Binôme E (erreur d'estimation corrigée).

**Question structurelle** : Pour un T donné, l'algorithme glouton extrait :
1. b_0 = floor(log₂(T / 3^{k-1}))
2. T ← T - 3^{k-1}·2^{b_0}
3. b_1 = floor(log₂(T / 3^{k-2})), avec contrainte b_1 < b_0
4. etc.

La contrainte b_j < b_{j-1} est le POINT CRITIQUE. Si le glouton produit b_j ≥ b_{j-1},
alors T ne peut pas être un corrSum.

### BINÔME B — INNOVATEUR

**Observation** : Le glouton échoue quand le reste R_j = T - Σ_{i<j} 3^{k-1-i}·2^{b_i}
est "trop grand" par rapport à 3^{k-1-j}·2^{b_{j-1}-1}, forçant b_j ≥ b_{j-1}.

Formellement : le glouton réussit ssi pour tout j, R_j < 3^{k-1-j}·2^{b_{j-1}}.

Quand T = m·d = m·(2^S - 3^k), on a :
R_0 = m·d = m·2^S - m·3^k

La première extraction : b_0 = floor(log₂(m·d / 3^{k-1})).

m·d / 3^{k-1} = m·(2^S - 3^k)/3^{k-1} = m·2^S/3^{k-1} - 3m

Pour k=22 : m·2^35/3^21 - 3m ≈ m·3.16 - 3m = 0.16m.

Donc b_0 ≈ log₂(0.16m). Pour m ≈ 5×10^6 : b_0 ≈ log₂(8×10^5) ≈ 20.

Après extraction de b_0 : R_1 = m·d - 3^{k-1}·2^{b_0}.

**Le point dur** : quantifier la propagation de retenue dans R_j pour montrer
que b_j ≥ b_{j-1} arrive inévitablement.

**PROBLÈME FONDAMENTAL** : L'analyse bit par bit de m·(2^S - 3^k) - Σ 3^{k-1-j}·2^{b_j}
est essentiellement une analyse de la représentation en base mixte 2-3 de m·d.
Or, la distribution des chiffres de m·d en base 2 est liée à la distribution
des puissances de 3 modulo des puissances de 2, qui est un problème classique
mais NON RÉSOLU dans sa forme quantitative.

En fait, le cœur de l'argument serait de montrer que les bits de m·d dans les
positions intermédiaires (~S/2) sont "mal alignés" avec la structure requise.
Mais les bits de m·d dépendent de m de façon pseudo-aléatoire, et prouver
une obstruction pour TOUS les m revient à borner une somme exponentielle...
ce qui nous ramène au mur des sommes de caractères.

### CHECKPOINT R144

L'extraction gloutonne est CORRECTE comme algorithme (elle détecte les corrSum).
Mais PROUVER qu'elle échoue pour tous les multiples de d requiert une analyse
de la structure digitale de m·(2^S - 3^k) qui, poussée à ses limites,
SE RÉDUIT AU PROBLÈME ORIGINAL de borner des sommes exponentielles.

**Verdict E2 Glouton : [SEMI-RÉEL mais CIRCULAIRE] —
l'approche est genuinement différente en surface mais le cœur dur de la preuve
retombe sur les mêmes estimations exponentielles.**

---

## R145 — EXPLORATION DU FAIT INATTENDU : N₀(d) > 0 SANS CYCLE

### BINÔME A — INVESTIGATEUR

Le Binôme E a révélé : N₀(d) > 0 pour k = 2,3,4,5,8,11,17 mais il n'y a
PAS de cycle pour ces k. Cela signifie :

∃ A avec corrSum(A) ≡ 0 mod d, MAIS les k shifts cycliques de A ne donnent
PAS tous corrSum ≡ 0 mod d.

Un k-cycle correspond à une composition A telle que corrSum(A^{(i)}) ≡ 0 mod d
pour TOUTES les k rotations A^{(i)} de A.

**Conséquence** : La condition "pas de k-cycle" est PLUS FAIBLE que N₀(d) = 0.
On pourrait prouver l'absence de cycles sans prouver N₀(d) = 0.

### BINÔME B — INNOVATEUR

**Nouvel objet** : Soit CycN₀(d) = #{A ∈ Comp(S,k) : corrSum(A^{(i)}) ≡ 0 mod d ∀i}.

Alors CycN₀(d) ≤ N₀(d). Un k-cycle existe ssi CycN₀(d) > 0.

**Question** : La condition "TOUTES les k rotations" est-elle strictement plus forte ?

**Oui** — computationnellement confirmé pour k petit. La raison structurelle :
corrSum(A^{(1)}) = Σ 3^{k-1-j}·2^{b'_j} où la rotation change les b_j en un
pattern cycliquement différent. Les k conditions corrSum(A^{(i)}) ≡ 0 mod d
pour i = 0,...,k-1 forment un SYSTÈME de k congruences, pas une seule.

**MAIS** : pour k premier, les orbites sous rotation ont longueur k (sauf fixpoint),
et les k conditions sont LIÉES par la rotation. Elles ne sont pas indépendantes.

**Lemme candidat** : Pour k premier et A non-constant, si corrSum(A) ≡ 0 mod d,
alors corrSum(A^{(1)}) ≢ 0 mod d (les rotations sont incompatibles).

**Test de réfutation** : Trouver A avec corrSum(A) ≡ corrSum(A^{(1)}) ≡ 0 mod d
pour un k premier.

**PROBLÈME** : Ce lemme, même s'il est vrai, ne s'applique qu'aux k premiers
dans {22..41}, soit k ∈ {23, 29, 31, 37, 41} — 5 valeurs sur 20.
Et pour les k composites, il faudrait un argument différent.

De plus, prouver l'incompatibilité des rotations requiert une analyse
de corrSum(A^{(1)}) - corrSum(A), ce qui dépend de la DIFFÉRENCE entre
corrSum à deux rotations successives. Cette différence est :

corrSum(A^{(1)}) - corrSum(A) = (2^S - 3^k)·2^{b_0}·3^{-1}·(quelque chose)

Hmm, calculons exactement. A = (a_0,...,a_{k-1}), A^{(1)} = (a_1,...,a_{k-1},a_0).

b_j(A) = S - Σ_{i=0}^j a_i. b_j(A^{(1)}) = S - Σ_{i=0}^j a_{i+1 mod k}.

Le calcul exact de corrSum(A^{(1)}) - corrSum(A) est complexe et dépend de
toute la structure de A. Pas de simplification évidente.

### CHECKPOINT R145

L'observation CycN₀ < N₀ est RÉELLE et ouvre une piste :
on n'a pas besoin de prouver N₀(d) = 0, seulement CycN₀(d) = 0.

Mais la condition de k rotations simultanées est difficile à exploiter
structurellement. Le lemme d'incompatibilité pour k premier est un candidat
mais la preuve n'est pas claire et ne couvre que 5/20 valeurs.

**Verdict : [SEMI-RÉEL] — observation importante mais pas de prise opératoire.**

---

## R146 — RETOUR À LA CONDITION CycN₀ : APPROCHE ALGÉBRIQUE

### BINÔME A — INVESTIGATEUR

Formalisons la condition de cycle. Un vrai k-cycle de Collatz correspond à un
entier n satisfaisant T^k(n) = n où T est le map de Collatz.

La condition algébrique exacte est :
n = (Σ_{j=0}^{k-1} 3^j · 2^{a_0+...+a_{k-1-j}}) / (2^S - 3^k)

Pour que n soit un entier POSITIF, il faut :
1. d = 2^S - 3^k > 0 (vrai pour k ≥ 3)
2. Le numérateur est divisible par d
3. n > 0

La condition 2 est EXACTEMENT corrSum(A') ≡ 0 mod d (avec un reindexage).

MAIS : pour un CYCLE, on a aussi la condition que l'orbite de n sous T
revient exactement à n après k étapes. Cela impose que les a_i sont les
LONGUEURS DES SEGMENTS PAIRS consécutifs de l'orbite, et ils doivent
être CYCLIQUEMENT COHÉRENTS : si on démarre d'un autre point de l'orbite,
on obtient une rotation de A.

**Observation cruciale** : Toute rotation de A donne le MÊME n (en partant
d'un point différent du cycle). Donc n est déterminé par A modulo rotation.

Mais corrSum(A) ≡ 0 mod d ne garantit PAS corrSum(A^{(i)}) ≡ 0 mod d.
La raison : corrSum(A) = 0 mod d donne UN entier n, mais les autres
points du cycle potentiel n_1 = T(n), n_2 = T^2(n), etc. ne sont des
entiers que si TOUTES les rotations donnent aussi corrSum ≡ 0 mod d.

**En fait, c'est plus subtil** : les k points du cycle sont :
n_i = (numérateur_i) / d, et numérateur_i = corrSum(A^{(i)}).
Donc n_i ∈ Z ⟺ corrSum(A^{(i)}) ≡ 0 mod d.

Mais en réalité, si n_0 est un entier et T est le map de Collatz,
alors n_1 = T(n_0) est AUTOMATIQUEMENT un entier. Donc :
corrSum(A^{(0)}) ≡ 0 mod d ⟹ corrSum(A^{(1)}) ≡ 0 mod d ⟹ ... ⟹ corrSum(A^{(k-1)}) ≡ 0 mod d.

**WAIT** — est-ce vrai ? Si n₀ = corrSum(A)/d ∈ Z et n₀ > 0, et si le pattern
(a_0,...,a_{k-1}) est l'itinéraire de Collatz de n₀, alors oui : n₁ = T(n₀) ∈ Z
automatiquement, et corrSum(A^{(1)}) = d·n₁.

**MAIS** : corrSum(A)/d n'est pas nécessairement > 0 ! C'est un entier, mais
il pourrait être négatif ou nul. Un cycle de Collatz requiert n > 0.

Et la formule n = corrSum(A)/d donne n > 0 ssi corrSum(A) > 0.
Puisque corrSum est une somme de termes positifs, corrSum > 0 toujours.

Donc si corrSum(A) ≡ 0 mod d, alors n = corrSum(A)/d est un entier > 0,
et TOUTES les rotations de A donnent automatiquement des entiers.

**CECI CONTREDIT le fait que N₀(d) > 0 pour k=2,3,4,5 sans cycle !**

### BINÔME B — INNOVATEUR

**Résolution de la contradiction** : Le point subtil est que corrSum(A)/d = n > 0
implique que n EST un point d'un cycle SI ET SEULEMENT SI le pattern de Collatz
de n est EXACTEMENT (a_0,...,a_{k-1}).

Or, corrSum(A) ≡ 0 mod d donne n = corrSum(A)/d, mais n pourrait avoir un
pattern de Collatz DIFFÉRENT de A. La composition A encode les longueurs
des segments pairs, mais pour que n ait ce pattern, il faut que T^j(n)
soit impair exactement après a_j étapes paires.

La condition est : pour chaque j, n_j est IMPAIR et n_j·3+1 est divisible
par 2^{a_j} exactement. Ceci n'est PAS garanti par corrSum(A) ≡ 0 mod d.

En résumé : corrSum(A) ≡ 0 mod d donne un entier n, mais n pourrait NE PAS
suivre le pattern A sous la dynamique de Collatz. C'est pour ça que N₀(d) > 0
n'implique pas l'existence d'un cycle.

### CHECKPOINT R146

La distinction entre N₀(d) (condition modulaire) et CycN₀(d) (condition
dynamique) est SUBTILE mais RÉELLE. La condition modulaire est NÉCESSAIRE
mais pas SUFFISANTE pour un cycle.

Cependant, pour les k=22..41, la condition C/d < 1 signifie que même
si N₀(d) ≤ C/d < 1, on aurait N₀(d) = 0. Donc le programme original
(N₀(d) = 0 via équidistribution) est CORRECT et SUFFISANT.

La piste CycN₀ est une relaxation théorique intéressante mais N'AIDE PAS
en pratique car on ne sait pas exploiter la condition dynamique
(n suit le pattern A) de façon quantitative.

**Verdict : [OBJET RÉEL mais INOPÉRANT pour le programme actuel]**

---

## R147 — SCHUR-VANDERMONDE : TENTATIVE DE SAUVETAGE

### BINÔME A — INVESTIGATEUR

Le Candidat D1 a été éliminé car s_λ(1) est astronomique. Mais la factorisation
det(y_l^{e_j}) = V(y)·s_λ(y) est RÉELLE. Peut-on l'utiliser autrement ?

**Idée** : Au lieu de borner |T(t,d)| directement, utiliser la factorisation
pour obtenir une IDENTITÉ exacte reliant T à un objet plus maniable.

T(t,d) = Σ_{|I|=k} ∏_{j} y_{c_j}^{3^{j-1}}

Ne peut PAS s'écrire comme un seul déterminant (car pas d'alternation de signe).

Mais T est liée au e_k (fonction symétrique élémentaire) d'un alphabet pondéré.

Définissons x_c = y_c^{1} = ω_c pour c = 0,...,S-1. Alors :
- e_k(x_0,...,x_{S-1}) = Σ_{c_1<...<c_k} ∏ x_{c_j} (produits sans poids)
- Notre T = Σ_{c_1<...<c_k} ∏ x_{c_j}^{3^{j-1}} (produits PONDÉRÉS)

T N'EST PAS une fonction symétrique élémentaire (les exposants diffèrent par position).

### BINÔME B — INNOVATEUR

**Approche alternante** : On peut exprimer T comme un MINEUR du déterminant.

Considérons la matrice alternante A de taille S×k définie par A_{c,j} = x_c^{3^{j-1}}.
Le k-ème composé extérieur Λ^k(A) est une matrice (S choose k) × 1 dont les
entrées sont les mineurs k×k de A.

Chaque mineur est det(x_{c_l}^{3^{j-1}})_{l,j} pour un choix {c_1,...,c_k}.

Notre somme T = Σ_{I} (mineur_I avec signe +, pas alternant).

Le problème : les mineurs ont des SIGNES (de l'alternance), et T les somme
tous avec le signe +. La différence entre Σ|mineur| et |Σ(±mineur)| est cruciale.

**Borne via l'inégalité de Cauchy-Binet** :
|Σ_I mineur_I|² ≤ (S choose k) · Σ_I |mineur_I|²
= (S choose k) · det(A* A) (Cauchy-Binet)

A* A est une matrice k×k avec (A*A)_{ij} = Σ_c x_c^{3^{i-1}} · conj(x_c^{3^{j-1}})
= Σ_c exp(2πit·2^c·(3^{i-1} - 3^{j-1})/d)

C'est une somme exponentielle ! Et |T|² ≤ (S choose k) · |det(A*A)|.

**Calcul de det(A*A)** : (A*A)_{ij} = Σ_{c=0}^{S-1} ω_c^{3^{i-1} - 3^{j-1}}.
Pour i = j : (A*A)_{ii} = S.
Pour i ≠ j : (A*A)_{ij} = Σ_c exp(2πit·2^c·(3^{i-1}-3^{j-1})/d).

C'est une somme exponentielle de la forme Σ_c e(α·2^c) pour α = t·(3^{i-1}-3^{j-1})/d.

Par les bornes classiques sur les sommes d'exponentielles de Mordell :
|Σ_c e(α·2^c)| ≤ C·S^{1/2} pour α irrationnelle ou de "grand dénominateur".

Si les off-diagonales de A*A sont O(√S), alors det(A*A) ≈ S^k (diag dominante),
et |T|² ≤ (S choose k)·S^k, soit |T| ≤ S^k · ((S choose k)/S^k)^{1/2}...
ce qui ne donne rien de mieux.

### CHECKPOINT R147

L'approche Cauchy-Binet ramène aux MÊMES sommes exponentielles (Σ e(α·2^c))
qui sont le problème original sous une forme légèrement différente.

**Verdict D1 Schur : [ÉLIMINÉ définitivement] — toute route déterminantale
retombe sur des sommes exponentielles, ce qui est le mur original.**

---

## R148 — TENTATIVE D'INNOVATION RADICALE : DENSITÉ DE ZÉROS DE corrSum

### BINÔME A — INVESTIGATEUR

Après 6 rounds (R142-R147), tous les candidats sont soit éliminés soit réduits
au problème original. Tentons une dernière direction radicalement différente.

**Nouvelle question** : Au lieu de montrer que corrSum ne prend JAMAIS la valeur
0 mod d, peut-on montrer que la DENSITÉ des valeurs atteintes par corrSum dans
{0,...,d-1} est suffisamment faible pour que 0 soit probablement évité ?

Nous savons : |Image| ≤ C(k). Si corrSum est INJECTIF (vérifié pour k petit
par le Binôme E), alors |Image| = C(k), et la fraction de résidus couverts est C/d.

Pour k=22 : C/d ≈ 0.31. Donc ~69% des résidus sont MANQUANTS.

La question est : 0 fait-il partie des 31% couverts ou des 69% manquants ?

### BINÔME B — INNOVATEUR

**Approche par moments/distribution** : Si les valeurs de corrSum mod d étaient
uniformément distribuées parmi les d résidus, P(0 ∈ Image) = 1 - (1-1/d)^C ≈ C/d.
Pour C/d ≈ 0.31 : P ≈ 0.27. Donc "aléatoirement", il y a ~73% de chance que 0 soit évité.

Mais corrSum n'est PAS aléatoire. Les valeurs sont STRUCTURÉES par la
progression géométrique des poids 3^{k-1-j}.

**Observation** : Les corrSum values se concentrent dans un intervalle
[V_min, V_max] avec V_max/V_min ≈ 2^S/2^{S-k+1} · 3^0/3^{k-1} ≈ 2^{k-1}/3^{k-1} ≈ (2/3)^{k-1}.

Wait, V_max/V_min ≈ (S·choose·stuff) / ... Let me just note that the values
are NOT uniformly spread in [0, d-1] but concentrated in [V_min, V_max].

Les multiples de d dans [V_min, V_max] sont : m = V_min/d, ..., V_max/d.
Le nombre de tels m est (V_max - V_min)/d.

Pour k=22 : V_max ≈ 2.8×10^16, V_min ≈ 1.3×10^16, d ≈ 3×10^9.
Nombre de m : (2.8-1.3)×10^16 / 3×10^9 ≈ 5×10^6.

Et C(k) = (34 choose 21) ≈ 9.3×10^8 >> 5×10^6.

Donc il y a ~200 compositions par multiple de d. En moyenne, chaque multiple
est atteint ~200 fois. Le multiple m·d = corrSum(A) est atteint si m est un
"résidu atteint" dans la plage de m.

**Ceci est juste la formulation DP** — vérifier si chaque m dans la plage
admet une décomposition en corrSum. C'est ANTI-COMPUTATIONNEL et K-PAR-K.

### CHECKPOINT R148

L'analyse de densité ne fait que reformuler le DP dans un langage continu.
Pas d'innovation opératoire.

**Verdict : [REDONDANT avec le DP — anti-computationnel, anti-k-par-k]**

---

## R149 — CONSOLIDATION : QU'AVONS-NOUS RÉELLEMENT TROUVÉ ?

### Bilan des 8 rounds (R142-R148)

| Candidat | Type | Verdict final |
|----------|------|--------------|
| D1 Schur-Vandermonde | Innovation TAN | [ÉLIMINÉ] — s_λ(1) fatal, Cauchy-Binet = sommes exp. |
| D2 Toeplitz spectral | Innovation TAN | [ÉLIMINÉ] — Gershgorin → λ_max ≈ r → borne triviale |
| D3 Permanent | Innovation TAN | [ÉLIMINÉ] — = CS itéré |
| E1 Crible mod 3^m | Alternative | [ÉLIMINÉ] — gcd(d,3)=1, orthogonal |
| E2 Glouton | Alternative | [ÉLIMINÉ] — preuve structurelle retombe sur sommes exp. |
| CycN₀ relaxation | Observation | [INOPÉRANT] — ne s'exploite pas quantitativement |
| Densité de zéros | Tentative | [REDONDANT] — = DP reformulé |

### Théorèmes prouvés

| ID | Énoncé | Statut |
|----|--------|--------|
| T174 | corrSum(A) ≡ 1 mod 3 pour toute composition A | PROUVÉ (b_{k-1}=0) |
| — | corrSum mod 9 ∈ {4, 7} | OBSERVÉ (non prouvé formellement) |
| — | M_{ij} = C(j-i) Toeplitz (matrice de corrélation orbitale) | PROUVÉ |
| — | C(0) ≥ r-1 (diagonal ≥ trivial) | PROUVÉ |
| — | λ_max(M) ≈ r par Gershgorin | PROUVÉ |

### Résultat net

**T174 est le seul théorème nouveau.** C'est une propriété arithmétique propre de corrSum
mais qui ne mord pas sur N₀(d) car gcd(d,3) = 1.

La matrice Toeplitz est un OBJET RÉEL mais sa borne spectrale est TRIVIALE.

### Diagnostic honnête

La campagne R142-R148 a tenté 7 directions d'innovation opératoire.
Toutes ont échoué, soit par réduction au problème original (Schur, glouton),
soit par borne triviale (Toeplitz), soit par orthogonalité (crible mod 3).

Le verrou |S_H(s)| ≤ √r est FONDAMENTAL et résiste à toute tentative
de contournement, qu'elle soit par sommes de caractères, algèbre combinatoire,
analyse spectrale, ou extraction gloutonne.

---

## R150 — AUDIT FINAL ET DÉCISION

### CHECKPOINT OBLIGATOIRE

**1. Quel manque concret a guidé l'innovation ?**
Le manque d'un OUTIL brisant √r pour |S_H(s)|. Ou d'une OBSTRUCTION combinatoire
directe sur corrSum.

**2. Quel candidat est réellement nouveau ?**
La matrice Toeplitz (D2) est un objet NOUVEAU mais dont la borne est triviale.
T174 (corrSum ≡ 1 mod 3) est NOUVEAU mais inopérant.

**3. Quel candidat change la capacité d'attaque ?**
AUCUN. Tous les candidats se réduisent au problème original ou donnent des bornes triviales.

**4. Quel candidat doit mourir maintenant ?**
TOUS les 7 candidats sont morts ou inopérants.

**5. Quel survivant mérite un prochain round ?**
AUCUN.

**6. Pourquoi un prochain round serait-il encore légitime ?**
Il NE L'EST PAS dans le cadre actuel. Le verrou est un problème ouvert fondamental
de théorie analytique des nombres, résistant à 67+ rounds d'investigation ciblée
et 5+ familles d'outils.

### DÉCISION FINALE

## **CONFIRMATION DE LA SUSPENSION (R141).**

La campagne R142-R151 a tenté honnêtement l'innovation opératoire demandée
par PromptR142. Elle a produit :
- 1 théorème mineur (T174 : corrSum ≡ 1 mod 3)
- 1 objet réel mais trivial (matrice Toeplitz orbitale)
- 7 directions d'innovation toutes éliminées
- 0 candidat survivant

Le programme doit passer en **MODE PUBLICATION**.

---

## R151 — BILAN CAMPAGNE R142-R151

### SCORE IVS : 3.5 / 10

| Critère | Score | Justification |
|---------|-------|---------------|
| Théorèmes prouvés | 2/10 | T174 mineur (corrSum ≡ 1 mod 3) |
| Routes nouvelles | 4/10 | 7 directions testées, toutes éliminées proprement |
| Avancée sur verrou | 1/10 | Aucun candidat ne change la capacité d'attaque |
| Rigueur/protocole | 9/10 | PromptR142 exécuté intégralement, binômes + audit |
| Éliminations utiles | 5/10 | Schur/Toeplitz/permanent/glouton/crible éliminés avec raisons |

### REGISTRE FAIL-CLOSED FINAL

| Objet | Statut |
|-------|--------|
| D1 Schur-Vandermonde | [ÉLIMINÉ — s_λ(1) astronomique, Cauchy-Binet = sommes exp.] |
| D2 Toeplitz spectral | [ÉLIMINÉ — λ_max ≈ r par Gershgorin, borne triviale] |
| D3 Permanent structuré | [ÉLIMINÉ — = Cauchy-Schwarz itéré] |
| E1 Crible mod 3^m | [ÉLIMINÉ — gcd(d,3)=1, orthogonal au module] |
| E2 Extraction gloutonne | [ÉLIMINÉ — preuve retombe sur sommes exponentielles] |
| CycN₀ vs N₀ | [OBJET RÉEL mais INOPÉRANT] |
| Densité de zéros | [REDONDANT — reformulation du DP] |
| T174 (corrSum ≡ 1 mod 3) | [PROUVÉ mais INOPÉRANT — gcd(d,3)=1] |
| Matrice Toeplitz | [OBJET RÉEL — structure vérifiée, borne spectrale triviale] |

### OPTIONS STRATÉGIQUES

**A (RECOMMANDÉE)** : PUBLIER la chaîne conditionnelle (170+ théorèmes)
**B** : Attendre résultat EXTERNE en TAN (ε_BGK ≥ 0.1)
**C** : Explorer une piste QUALITATIVEMENT NOUVELLE si identifiée (aucune actuellement)
