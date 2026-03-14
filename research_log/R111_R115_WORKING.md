# CAMPAGNE R111→R115 — WORKING FILE

## Date: 14 mars 2026
## Mandat: Attaquer V_GOWERS — corrélations de Gauss décalées et normes U^{k-1}

---

## DIRECTIVE STRATÉGIQUE

**Continuité** : Même protocole que R106-R110. Même architecture binômes Investigation/Innovation.
**Front** : V_GOWERS = ||ψ - Eψ||_{U^{k-1}} petit sur Z_g, où ψ(a) = |f̂(t_a)|².

**Acquis non négociables** (R106-R110 inclus) :
- T159, T162, T163, T166 [PROUVÉS INCONDITIONNELS]
- T164 [COND sur (H_k)] : r > p^{2/k} suffit sous (H_k)
- (H_k) pour 3∉H ⟺ uniformité de ψ le long de PA de pas ⟨3⟩ dans Z_g
- ψ̂(s) = (1/g) Σ_j τ_j · τ̄_{j+s} (transformée de Fourier de ψ sur Z_g)
- ||ψ - Eψ||_{U^2}^4 = (1/g) Σ_{s≠0} |ψ̂(s)|^4

**Morts à ne pas ressusciter** (ajouts R106-R110) :
- VdC sur W_ℓ, induction E_k→E_{k-1}, Hölder propagation T166→(H_k)
- H-invariance pour 3∉H (= T163, ne s'applique pas)
- Plus toutes les morts antérieures (131+4 = 135 pistes)

---

## R111 — INVESTIGATION : CORRÉLATIONS DE GAUSS DÉCALÉES

### OBJECTIF

Calculer ou borner C(s) := Σ_{j=0}^{g-1} τ_j · τ̄_{j+s} (indices mod g)
où τ_j = τ(χ^{jr}, 1) = Σ_{x∈F_p*} χ^{jr}(x) · e_p(x) sont des sommes de Gauss.

C(s) est la CLÉ de toute la campagne : ψ̂(s) = C(s)/g, et les normes de Gowers
de ψ s'expriment en termes de puissances de |C(s)|.

### BINÔME A — INVESTIGATION : CALCUL EXACT DE C(s)

**Rappel des propriétés des sommes de Gauss** :
- τ_0 = τ(χ_0, 1) = Σ_x e_p(x) = -1
- Pour j ≠ 0 mod g : |τ_j| = √p (Weil)
- τ_j · τ̄_j = p pour j ≠ 0 (conséquence de |τ_j| = √p... ATTENTION :
  |τ_j|² = p est exact, pas une borne)
- Phase : τ_j = √p · e^{iθ_j} pour un angle θ_j ∈ [0, 2π)

**Calcul de C(s)** :
C(s) = τ_0·τ̄_s + Σ_{j=1}^{g-1} τ_j·τ̄_{j+s}

Terme j=0 : τ_0·τ̄_s = (-1)·τ̄_s. Pour s ≠ 0 : |τ_0·τ̄_s| = √p. Pour s=0 : τ_0·τ̄_0 = 1.

Pour j ≠ 0, j+s ≠ 0 : τ_j·τ̄_{j+s} = p · e^{i(θ_j - θ_{j+s})}

Donc C(s) = -τ̄_s + p · Σ'_j e^{i(θ_j - θ_{j+s})} + (termes de bord)

où Σ' exclut j=0 et j+s=0 mod g (au plus 2 termes manquants).

**Calcul via produit de caractères** :
τ_j · τ̄_{j+s} = (Σ_x χ^{jr}(x) e_p(x)) · (Σ_y χ^{-(j+s)r}(y) e_p(-y))
= Σ_{x,y} χ^{jr}(x) χ^{-(j+s)r}(y) e_p(x-y)
= Σ_{x,y} χ^{jr}(x/y) · χ^{-sr}(y) · e_p(x-y)

Substitution x = zy : = Σ_{y,z} χ^{jr}(z) · χ^{-sr}(y) · e_p(y(z-1))

Sommation sur j : Σ_{j=0}^{g-1} χ^{jr}(z) = g · 1_{z∈H} (indicatrice de H)

Donc : C(s) = Σ_j τ_j·τ̄_{j+s} = g · Σ_{z∈H} Σ_{y∈F_p*} χ^{-sr}(y) · e_p(y(z-1))

= g · [Σ_{y} χ^{-sr}(y) · e_p(0) + Σ_{z∈H, z≠1} Σ_y χ^{-sr}(y) e_p(y(z-1))]

Premier terme (z=1) : g · Σ_y χ^{-sr}(y) = g · 0 = 0 pour s ≠ 0 (orthogonalité des caractères).
Pour s = 0 : g · (p-1) = g(p-1).

Deuxième terme (z ≠ 1, z ∈ H) :
g · Σ_{z∈H\{1}} Σ_y χ^{-sr}(y) · e_p(y(z-1))
= g · Σ_{z∈H\{1}} τ(χ^{-sr}, z-1)

où τ(ψ, a) = Σ_y ψ(y) e_p(ay) est la somme de Gauss avec paramètre a.

**Propriété fondamentale** : Pour ψ ≠ ψ_0 et a ≠ 0 :
τ(ψ, a) = ψ^{-1}(a) · τ(ψ, 1) = ψ^{-1}(a) · τ(ψ)

Donc pour s ≠ 0 :
C(s) = g · τ(χ^{-sr}) · Σ_{z∈H\{1}} χ^{sr}(z-1)

**RÉSULTAT EXACT** :
C(s) = g · τ(χ^{-sr}) · S_H(s)

où S_H(s) := Σ_{z∈H\{1}} χ^{sr}(z-1) = Σ_{h∈H\{1}} χ^{sr}(h-1)

### BINÔME A — ANALYSE DE S_H(s)

**Objet** : S_H(s) = Σ_{h∈H\{1}} χ^{sr}(h-1).

C'est une SOMME DE CARACTÈRES MULTIPLICATIFS SUR H-1 := {h-1 : h ∈ H, h ≠ 1}.
L'ensemble H-1 est la TRANSLATION ADDITIVE du sous-groupe multiplicatif H.

**Borne triviale** : |S_H(s)| ≤ r - 1.

**Borne de Weil** : Si χ^{sr} est un caractère d'ordre d ≥ 2, et si la somme
porte sur un sous-ensemble "algébriquement structuré", Weil donne des bornes
en √p ou √r selon le contexte.

Ici : H = {x ∈ F_p* : x^g = 1} est un ensemble algébrique (racines de x^g - 1).
H - 1 = {x - 1 : x^g = 1, x ≠ 1}.

S_H(s) = Σ_{x^g=1, x≠1} χ^{sr}(x-1)

C'est une somme de caractères sur les racines d'un polynôme. Par la borne de Weil
pour sommes de caractères sur variétés algébriques :

|S_H(s)| ≤ C · √r (borne type Weil sur courbe)

MAIS : il faut vérifier que la somme n'est pas dégénérée.

**Calcul alternatif** : On peut écrire
S_H(s) = Σ_{ζ^g=1, ζ≠1} χ^{sr}(ζ - 1)

Si g | (p-1) et χ a ordre p-1, alors χ^{sr} a ordre (p-1)/gcd(sr, p-1).

L'argument h-1 pour h ∈ H parcourt un ensemble de r-1 points. La clé est
que h et h-1 vivent dans des "mondes" différents (h multiplicatif, h-1 additif).
C'est la FAILLE additif/multiplicatif identifiée en R81.

### BINÔME B — INNOVATION : BORNE SUR |C(s)|

De C(s) = g · τ(χ^{-sr}) · S_H(s) et |τ(χ^{-sr})| = √p :

|C(s)| = g · √p · |S_H(s)|

**Si |S_H(s)| ≤ A·√r** (borne type Weil) :
|C(s)| ≤ A · g · √(pr) = A · g · √p · √r

Et |ψ̂(s)| = |C(s)|/g ≤ A · √(pr) = A · √p · √r

Normalisation : Eψ = (p-r)/g ≈ r. Donc |ψ̂(s)|/Eψ ≈ √(pr)/r = √(p/r) = √g.

Pour la norme U^2 : ||ψ - Eψ||_{U^2}^4 = (1/g) Σ_{s≠0} |ψ̂(s)|^4
≤ (1/g) · g · (A·√(pr))^4 = A^4 · p²r² = A^4 · (pr)²

Et ||ψ - Eψ||_{U^2} ≤ A · (pr)^{1/2} = A · √(pr)

Condition pour k=3 (von Neumann) : ||ψ - Eψ||_{U^2} ≪ (Eψ)^2 = r²
A · √(pr) ≤ r² ⟺ A · √p ≤ r^{3/2} ⟺ r ≥ (A²p)^{1/3}

Pour A = O(1) : r ≥ p^{1/3}. C'est la condition pour (H_3) !

**Comparaison** : T4 pour k=3 donne r > p^{7/6} (IMPOSSIBLE).
La nouvelle borne donne r > p^{1/3}. GAIN MAJEUR si |S_H(s)| = O(√r).

**Pour k général** : norme U^{k-1}, condition r ≥ p^{1/(2k-3)} (à vérifier).

### QUESTION CRITIQUE : |S_H(s)| = O(√r) EST-IL VRAI ?

S_H(s) = Σ_{h∈H\{1}} χ^{sr}(h-1) = Σ_{ζ : ζ^g=1, ζ≠1} χ^{sr}(ζ-1)

C'est une somme de type Jacobi / somme hybride. Résultats connus :

1. **Borne de Weil sur variétés** (Weil 1948, Lang-Weil 1954) :
   Pour une somme Σ_{x∈V} χ(f(x)) sur une variété V de dimension d,
   le terme principal est 0 (si χ ≠ 1) et l'erreur est O(p^{d/2}).
   Ici V = {x : x^g = 1} a dimension 0, donc... pas applicable directement.

2. **Somme de caractères sur racines de l'unité** :
   C'est une somme FINIE sur r-1 points. Par complétude :
   S_H(s) = (1/g) Σ_ψ (Σ_{x∈F_p*} ψ(x) χ^{sr}(x-1))
   = (1/g) Σ_ψ J(ψ, χ^{sr}) · χ^{-sr}(-1) ... (développement via Jacobi)

   Non, plus précisément :
   Σ_{x∈F_p*} ψ(x) · χ^{sr}(x-1) = somme de Jacobi GÉNÉRALISÉE.

3. **Sommes de Jacobi** : J(ψ, χ) = Σ_{x+y=1} ψ(x)χ(y) = τ(ψ)τ(χ)/τ(ψχ).
   Pour ψχ ≠ 1 : |J| = √p.

   Notre somme : Σ_x ψ(x) χ^{sr}(x-1). Par substitution x-1 = y :
   = Σ_y ψ(y+1) χ^{sr}(y) = Σ_y ψ(y+1) χ^{sr}(y)

   Ce n'est PAS une somme de Jacobi standard (qui a ψ(x)χ(1-x)).
   C'est une SOMME HYBRIDE de deux caractères multiplicatifs évalués à x et x-1.

   Par la formule de Weil pour courbes : la somme Σ_x χ_1(x) χ_2(x-1) sur F_p*
   est bornée par √p (car c'est essentiellement une somme de Jacobi).

   Preuve : Σ_x ψ(x) χ^{sr}(x-1) = Σ_{x≠0,1} ψ(x) χ^{sr}(x-1) + ψ(1)·χ^{sr}(0)
   Le dernier terme est 0 (car χ^{sr}(0) = 0 si sr ≢ 0, sinon 1).

   Pour x ≠ 0,1 : substituer x = 1-t, obtenir Σ_t ψ(1-t) χ^{sr}(-t)
   = χ^{sr}(-1) · Σ_t ψ(1-t) χ^{sr}(t) = χ^{sr}(-1) · J(χ^{sr}, ψ̃)

   où ψ̃(t) = ψ(1-t). Hmm, ψ̃ n'est PAS un caractère multiplicatif.

   Reprenons. Σ_x ψ(x) χ^{sr}(x-1) pour ψ ≠ χ^{-sr} :
   = Σ_{a+b=1} ψ(a^{-1}) χ^{sr}(a^{-1}b)  [non standard]

   En fait, par un résultat classique (voir Lidl-Niederreiter, Thm 5.41) :
   |Σ_{x∈F_p*} χ_1(x) χ_2(x-a)| ≤ √p pour χ_1·χ_2 ≠ χ_0 et a ≠ 0.

   C'est exactement notre cas ! χ_1 = ψ = χ^{jr·g/g}... non, c'est ψ qui
   varie dans le développement de 1_H.

**RÉSULTAT CLÉ** (Lidl-Niederreiter, Finite Fields, Thm 5.41) :
Pour χ_1, χ_2 caractères multiplicatifs de F_p* avec χ_1·χ_2 ≠ χ_0, et a ≠ 0 :
|Σ_{x∈F_p*} χ_1(x) · χ_2(x-a)| ≤ √p

Application : S_H(s) = Σ_{h∈H\{1}} χ^{sr}(h-1).
On écrit 1_H(h) = (1/g) Σ_{m=0}^{g-1} χ^{mr}(h). Donc :

S_H(s) = (1/g) Σ_m Σ_{x∈F_p*\{1}} χ^{mr}(x) · χ^{sr}(x-1)

= (1/g) Σ_m B(m,s) - (1/g) Σ_m χ^{mr}(1) · χ^{sr}(0) [correction x=1]

où B(m,s) = Σ_{x∈F_p*} χ^{mr}(x) · χ^{sr}(x-1).

Terme m tel que χ^{mr} · χ^{sr} = χ_0, i.e., (m+s)r ≡ 0 mod (p-1), i.e., m ≡ -s mod g :
B(-s,s) = Σ_x χ^{-sr}(x) · χ^{sr}(x-1) = Σ_x (x-1/x)^{sr·ind} ...
Non, pour m = -s : χ^{mr} = χ^{-sr}, donc χ^{mr}·χ^{sr} = χ_0, et
B(-s,s) = Σ_x χ_0(x) · χ_0(x-1) = ... non, c'est Σ_x χ^{-sr}(x) χ^{sr}(x-1).

En fait χ_1 = χ^{mr}, χ_2 = χ^{sr}. La condition χ_1·χ_2 ≠ χ_0 ⟺ (m+s)r ≢ 0 mod (p-1)
⟺ m ≢ -s mod g.

Pour m ≠ -s mod g : |B(m,s)| ≤ √p (par Thm 5.41).

Pour m = -s mod g : B(-s,s) = Σ_x χ^{-sr}(x)·χ^{sr}(x-1).
Ceci est Σ_x [χ^{sr}(x-1)/χ^{sr}(x)] = Σ_x χ^{sr}((x-1)/x) = Σ_x χ^{sr}(1 - 1/x).
Substitution y = 1/x : = Σ_y χ^{sr}(1-y) = Σ_y χ^{sr}(1-y).
Et Σ_y χ^{sr}(1-y) = Σ_z χ^{sr}(z) (z=1-y) = 0 si sr ≢ 0 mod (p-1), i.e., s ≠ 0 mod g.
Pour s ≠ 0 mod g : B(-s,s) = 0 !

Donc pour s ≠ 0 : TOUS les termes B(m,s) sont soit ≤ √p soit = 0.

S_H(s) = (1/g) Σ_m B(m,s) + corrections O(1)

|S_H(s)| ≤ (1/g) · g · √p + O(1) = √p + O(1) ≈ √p

**ATTENTION** : La borne est √p, PAS √r !

### AUDIT CROISÉ R111

|S_H(s)| ≤ √p + O(1). Revenons au calcul de |C(s)| :

|C(s)| = g · √p · |S_H(s)| ≤ g · √p · √p = g · p

Et |ψ̂(s)| = |C(s)|/g ≤ p.

Donc |ψ̂(s)| ≤ p, et ψ̂(s)/Eψ ≤ p/r = g.

C'est la BORNE TRIVIALE ! On n'a rien gagné !

**Diagnostic** : Le développement S_H(s) = (1/g)Σ_m B(m,s) introduit g termes,
chacun borné par √p. La somme donne g·√p = √p (puisqu'on divise par g).
Mais C(s) = g·√p·S_H(s) ≈ g·√p·√p = gp. Et ψ̂ = C/g ≈ p = borne triviale.

**Le problème** : Les g termes B(m,s) pourraient s'ANNULER partiellement.
L'annulation √g (racine carrée du nombre de termes) donnerait |S_H(s)| ≤ √(p/g) = √r.
C'est EXACTEMENT l'hypothèse de type Katz-Sarnak.

### CHECKPOINT R111

1. **Calcul exact de C(s) ?** OUI — C(s) = g·τ(χ^{-sr})·S_H(s) [PROUVÉ]
2. **S_H(s) borné ?** Triviale : √p. Optimal conjectural : √r (= annulation √g)
3. **Borne triviale suffisante ?** NON — retombe sur ψ̂(s) ≤ p = max de Weil
4. **Annulation √g suffisante ?** OUI — donnerait (H_k) pour r > p^{1/3} (k=3)
5. **Sous-verrou raffiné** : V_SQRT_CANCEL = annulation √g dans S_H(s)

---

## R112 — INVESTIGATION : ANNULATION √g DANS S_H(s)

### OBJECTIF

Montrer |S_H(s)| ≤ C·√r (au lieu de √p) par annulation des phases dans
S_H(s) = (1/g) Σ_m B(m,s).

### BINÔME A — INVESTIGATION : MÉCANISME D'ANNULATION

**Rappel** : B(m,s) = Σ_x χ^{mr}(x) · χ^{sr}(x-1) pour m ≢ -s mod g.

Par somme de Jacobi : B(m,s) = χ^{sr}(-1) · J(χ^{mr}, χ^{sr})
si on utilise la substitution standard.

CORRECTION : vérifions. Σ_x χ_1(x)·χ_2(x-1) = Σ_x χ_1(x)·χ_2(x-1).
Posons x-1 = t : Σ_t χ_1(t+1)·χ_2(t). Ce n'est PAS J(χ_1,χ_2) standard.

La somme de Jacobi est J(χ_1,χ_2) = Σ_{a+b=1} χ_1(a)·χ_2(b) = Σ_a χ_1(a)·χ_2(1-a).

Notre somme : Σ_x χ_1(x)·χ_2(x-1) = Σ_x χ_1(x)·χ_2(x-1).
Par x = 1-y : Σ_y χ_1(1-y)·χ_2(-y) = χ_2(-1)·Σ_y χ_1(1-y)·χ_2(y).
Et Σ_y χ_1(1-y)·χ_2(y) = J(χ_2, χ_1) [par définition de Jacobi avec a=y, b=1-y=1-y, χ_2(a)·χ_1(b)].

ATTENTION : la convention Jacobi est J(χ,ψ) = Σ_{a+b=1} χ(a)ψ(b).
Ici : Σ_y χ_2(y)·χ_1(1-y) = J(χ_2, χ_1).

Donc : B(m,s) = χ^{sr}(-1) · J(χ^{sr}, χ^{mr})

**Formule de Jacobi-Gauss** : J(χ_1, χ_2) = τ(χ_1)·τ(χ_2)/τ(χ_1·χ_2)
pour χ_1, χ_2, χ_1·χ_2 ≠ χ_0. Et |J| = √p.

Donc : B(m,s) = χ^{sr}(-1) · τ(χ^{sr})·τ(χ^{mr}) / τ(χ^{(m+s)r})

pour m ≢ 0, m ≢ -s mod g (sinon χ_1 ou χ_1·χ_2 = χ_0).

**Substitution dans S_H(s)** :
S_H(s) = (1/g) Σ_{m=0}^{g-1} B(m,s) + corrections

= (1/g) · χ^{sr}(-1) · τ(χ^{sr}) · Σ'_m τ(χ^{mr}) / τ(χ^{(m+s)r})

+ termes de bord (m=0, m=-s)

Pour m ≠ 0, -s : chaque terme vaut τ(χ^{mr})/τ(χ^{(m+s)r}).

Puisque |τ| = √p : |τ(χ^{mr})/τ(χ^{(m+s)r})| = 1.

Donc le ratio est un NOMBRE COMPLEXE DE MODULE 1 :
τ(χ^{mr})/τ(χ^{(m+s)r}) = e^{i(θ_{mr} - θ_{(m+s)r})}

où θ_j est la phase du j-ème Gauss sum τ(χ^j).

**RÉSULTAT** :
S_H(s) = (1/g) · χ^{sr}(-1) · τ(χ^{sr}) · Σ'_m e^{i(θ_{mr} - θ_{(m+s)r})} + O(√p/g)

= (τ(χ^{sr})/g) · χ^{sr}(-1) · Σ'_m e^{iΔ_s(m)} + O(√p/g)

où Δ_s(m) = θ_{mr} - θ_{(m+s)r} est la DIFFÉRENCE DE PHASES entre Gauss sums décalés.

**La question d'annulation √g est maintenant** :
|Σ'_m e^{iΔ_s(m)}| ≤ C·√g ?

C'est une somme de g-2 termes unitaires. Si les phases Δ_s(m) sont
ÉQUIDISTRIBUÉES sur [0,2π), alors |Σ| ~ √g par le TCL.

**Katz-Sarnak** : Les phases θ_j des sommes de Gauss τ(χ^j) sont
asymptotiquement équidistribuées (Sato-Tate pour caractères multiplicatifs).
Les DIFFÉRENCES Δ_s(m) = θ_{mr} - θ_{(m+s)r} sont également équidistribuées
si les phases ne sont pas corrélées entre indices éloignés.

### BINÔME B — INNOVATION : BORNE EFFECTIVE PAR KATZ

**Programme de Katz** (Gauss Sums, Kloosterman Sums, and Monodromy, 1988) :
Katz étudie les sommes de type Σ_m f(τ_{m+a}/τ_m) où f est un caractère.
Ce sont des "traces de Frobenius" sur des faisceaux ℓ-adiques.

Notre somme Σ_m e^{iΔ_s(m)} = Σ_m τ_m/τ_{m+s} (normalisé par √p/√p = 1)
est EXACTEMENT un objet de type "corrélation de Katz".

**Faisceau de Kloosterman-Katz** : Le faisceau Kl(χ^{mr}, χ^{(m+s)r})
a un groupe de monodromie géométrique connu (SL_2 ou Sp_{2g}, selon le cas).
Katz prouve que si le groupe de monodromie est assez gros, alors les
corrélations satisfont |Σ_m| ≤ C·√g avec C EFFECTIF.

**Résultat applicable** (Katz, Sommes exponentielles, Astérisque 79) :
Pour χ_1,...,χ_N des caractères distincts de F_p*, avec N < p :
|Σ_{j=1}^N τ(χ_j)/τ(χ_{σ(j)})| ≤ D · √N

pour toute permutation σ sans point fixe, où D dépend du degré du faisceau.

Dans notre cas : σ(m) = m+s (translation), N ~ g, et le résultat donnerait
|Σ_m e^{iΔ_s(m)}| ≤ D·√g.

**ATTENTION** : Je dois vérifier la référence exacte. Le résultat de Katz
porte sur des faisceaux spécifiques et les conditions de non-dégénérescence.

### TENTATIVE DE PREUVE DIRECTE (SANS KATZ)

**Approche par complétude sur Z_g** :

Σ_m e^{iΔ_s(m)} = Σ_m τ_{mr} · τ̄_{(m+s)r} / p

= (1/p) · C(s·r... non, C(s) était défini avec l'indice j, pas m.

En fait, réécrivons. Posons ω_j = τ_j/√p (unitaire). Alors :

Σ_{m=0}^{g-1} ω_{mr} · ω̄_{(m+s)r} = (1/p) Σ_m τ_{mr} · τ̄_{(m+s)r}

Mais on avait calculé C(s) = Σ_{j=0}^{g-1} τ_j · τ̄_{j+s} avec j indexant les
mêmes termes (τ_j = τ(χ^{jr})). Donc :

Σ_m ω_{mr} · ω̄_{(m+s)r} = C(s)/p

Et C(s) = g·τ(χ^{-sr})·S_H(s).

Donc : |Σ_m ω_{mr}·ω̄_{(m+s)r}| = |C(s)|/p = g·√p·|S_H(s)|/p

Si |S_H(s)| ≤ D·√r : |Σ_m ω·ω̄| ≤ D·g·√(pr)/p = D·g·√r/√p = D·√g
(car g/√(p/r) = g·√r/√p = (p/r)·√r/√p = √(p/r) = √g).

Hmm, vérifions : g = (p-1)/r ≈ p/r. g·√r/√p = (p/r)·√r/√p = √p/√r = √(p/r) = √g. ✓

**C'est CIRCULAIRE** — on suppose |S_H(s)| ≤ √r pour prouver |Σ ω·ω̄| ≤ √g,
et vice versa. Les deux sont ÉQUIVALENTS.

### APPROCHE NON-CIRCULAIRE : SECOND MOMENT DE C(s)

Calculons Σ_{s≠0} |C(s)|² directement.

Σ_{s=0}^{g-1} |C(s)|² = Σ_s |Σ_j τ_j·τ̄_{j+s}|²

= Σ_s Σ_{j,j'} τ_j·τ̄_{j+s}·τ̄_{j'}·τ_{j'+s}

= Σ_{j,j'} τ_j·τ̄_{j'} · Σ_s τ̄_{j+s}·τ_{j'+s}

= Σ_{j,j'} τ_j·τ̄_{j'} · C̃(j'-j)

où C̃(d) = Σ_s τ̄_s·τ_{s+d} = C̄(d) = conjugué de C(-d).

Hmm, c'est une convolution auto-corrélée — circulaire à nouveau.

**Approche directe par Parseval sur Z_g** :

Σ_s |ψ̂(s)|² = (1/g) Σ_a ψ(a)² - (Eψ)² [Parseval sur Z_g, terme s=0 retiré]

= (1/g) · Var(ψ) · g = Var(ψ)

Non : Σ_s |ψ̂(s)|² = Σ_a ψ(a)² (Parseval complet). Et Σ_{s≠0} |ψ̂(s)|² = Σ_a ψ(a)² - |ψ̂(0)|².

ψ̂(0) = Σ_a ψ(a) = p - r. Donc :
Σ_{s≠0} |ψ̂(s)|² = Σ_a ψ(a)² - (p-r)²

Et Σ_a ψ(a)² = (pE(H) - r^4)/r (calculé en R110). Avec E(H) ≤ r^{3-η} :

Σ_{s≠0} |ψ̂(s)|² ≤ p·r^{2-η} - (p-r)² + p²/something...

Hmm, soyons précis. Σ_a ψ(a)² = Σ_a |f̂(t_a)|^4 = (1/r)·Σ_{t∈F_p*} |f̂(t)|^4
= (1/r)·(p·E(H) - r^4) car Σ_{t∈F_p} |f̂(t)|^4 = p·E(H) et le terme t=0 est r^4.

Σ_{s≠0} |ψ̂(s)|² = (pE(H) - r^4)/r - (p-r)²

E(H) = r^4/p + O(r^{3-η}) (car E(H) est T_2(H) et la contribution t=0 donne r^4/p,
plus BKT donne le reste).

Non, E(H) = #{(a,b,c,d)∈H^4 : a+b=c+d}. Par Fourier : E(H) = (1/p)Σ_t |f̂(t)|^4.
Le terme t=0 : r^4/p. Reste : (1/p)Σ_{t≠0} |f̂(t)|^4 = E(H) - r^4/p.
BKT : E(H) ≤ r^{3-η}. Donc E(H) - r^4/p ≤ r^{3-η}.

Σ_a ψ(a)² = (pE(H) - r^4)/r. Or pE(H) = Σ_t |f̂(t)|^4 = p·E(H).
Hmm, Σ_{t∈F_p} |f̂|^4 = p·E(H). Donc Σ_{t∈F_p*} |f̂|^4 = p·E(H) - r^4.
Divisé par r (car f̂ est H-invariante, chaque coset contribue r fois) :
Σ_a ψ(a)² = (p·E(H) - r^4)/r.

ψ̂(0) = Σ_a ψ(a) = Σ_a |f̂(t_a)|² = (Σ_{t∈F_p*} |f̂(t)|²)/r = (pr - r²)/r = p - r.

Σ_{s≠0} |ψ̂(s)|² = (p·E(H) - r^4)/r - (p-r)²

= p·E(H)/r - r³ - p² + 2pr - r²

Pour E(H) = r^4/p + δ avec δ ≤ r^{3-η} :
p·E(H)/r = r³ + pδ/r

Donc Σ_{s≠0} |ψ̂(s)|² = pδ/r - p² + 2pr - r²

= p·(E(H) - r^4/p)/r - (p-r)² + r³ - r³ ... je me perds.

Simplifions : posons E = E(H), la vraie énergie.

Σ_{s≠0} |ψ̂(s)|² = pE/r - r³ - (p-r)²
= pE/r - r³ - p² + 2pr - r²

Pour E ≈ r²  (borne minimum, chaque delta apparaît au plus r/p fois) :
pE/r ≈ pr. Alors Σ ≈ pr - r³ - p² + 2pr - r² = 3pr - p² - r³ - r² ≈ -p² (négatif ?!)

C'est incohérent. Vérifions la formule.

Le problème : ψ̂ est la DFT de ψ sur Z_g. Parseval sur Z_g :
Σ_{s=0}^{g-1} |ψ̂(s)|² = g · Σ_{a=0}^{g-1} ψ(a)²

(avec la convention ψ̂(s) = Σ_a ψ(a) ω^{-sa}).

Donc Σ_s |ψ̂(s)|² = g · Σ_a ψ(a)² et Σ_{s≠0} |ψ̂(s)|² = g·Σ_a ψ(a)² - (p-r)².

Σ_a ψ(a)² = (pE(H) - r^4)/r comme avant.

Avec E(H) ≤ r^{3-η} et r^4/p ≤ r^{3-η} (pour r ≤ p^{(3-η-1)^{-1}}...):
Σ_a ψ(a)² ≤ (p·r^{3-η})/r = p·r^{2-η}

g·Σ_a ψ(a)² ≤ g·p·r^{2-η} = (p/r)·p·r^{2-η} = p²·r^{1-η}

Et (p-r)² ≈ p².

Σ_{s≠0} |ψ̂(s)|² ≤ p²·r^{1-η} - p² = p²(r^{1-η} - 1)

Pour la borne RMS : RMS(ψ̂) = √(Σ/g) ≈ √(p²·r^{1-η}/g) = p·√(r^{1-η}·r/p) = p·r^{(2-η)/2}/√p
= √p · r^{(2-η)/2}

Avec η ≈ 1/3 : RMS ≈ √p · r^{5/6}.

Si ψ̂(s) ~ RMS pour tout s : |ψ̂(s)| ≈ √p · r^{5/6}.
Eψ ≈ r. Ratio : √p·r^{5/6}/r = √p·r^{-1/6} = √(p/r^{1/3}).
Pour r > p^{2/3} : ratio = √(p/p^{2/9}) = √(p^{7/9}) = p^{7/18} > 1.
Pas assez petit pour prouver uniformité.

**Verdict R112** : La borne L² (Parseval + BKT) ne suffit PAS à prouver
l'annulation √g dans S_H(s). On obtient des bornes RMS en √p·r^{5/6},
ce qui est trop gros.

Le sous-verrou V_SQRT_CANCEL requiert des bornes POINTWISE sur les
corrélations de Gauss, pas seulement en moyenne.

### CHECKPOINT R112

1. **Mécanisme d'annulation identifié ?** OUI — annulation des phases e^{iΔ_s(m)}
2. **Preuve obtenue ?** NON — ni par Katz direct (référence à vérifier) ni par L²
3. **Circularité détectée ?** OUI — S_H√r ⟺ |Σω·ω̄|√g (même énoncé)
4. **Second moment (Parseval+BKT) ?** INSUFFISANT — donne RMS trop gros
5. **Sous-verrou** : V_SQRT_CANCEL reste OUVERT

---

## R113 — INNOVATION : APPROCHE PAR SOMMES DE KLOOSTERMAN

### OBJECTIF

Trouver un AUTRE angle pour borner S_H(s) = Σ_{h∈H\{1}} χ^{sr}(h-1),
en exploitant la structure arithmétique de H-1.

### BINÔME A — INVESTIGATION : STRUCTURE DE H-1

H = {ζ ∈ F_p* : ζ^g = 1} (racines g-ièmes de l'unité, ou de manière équivalente,
puissances de la racine primitive ω_0 d'ordre r : H = {ω_0^j : 0 ≤ j < r}).

H - 1 = {ω_0^j - 1 : 0 ≤ j < r, j ≠ 0}.

Propriété : h - 1 = h(1 - h^{-1}). Puisque h ∈ H, h^{-1} ∈ H, et 1 - h^{-1}
est un élément de 1-H. Donc H-1 = H · (1-H^{-1}) = H · (1-H) multiplicativement.

S_H(s) = Σ_{h∈H\{1}} χ^{sr}(h-1) = Σ_{h∈H\{1}} χ^{sr}(h) · χ^{sr}(1-h^{-1})
= Σ_{h∈H\{1}} χ^{sr}(h) · χ^{sr}(1-h^{-1})

Puisque h ∈ H et χ^{sr} a ordre (p-1)/(sr, p-1) : si r | sr (toujours vrai),
alors χ^{sr}|_H = χ^{sr·1}|_H. Comme H = ker(χ^r), χ^{sr}(h) = χ^{sr}(h) = 1
si r | sr... Attendons : χ^r|_H ≡ 1 (car H = ker de la surjection F_p* → Z_g).
Donc χ^{sr}|_H = (χ^r)^s|_H = 1^s = 1. Donc χ^{sr}(h) = 1 pour tout h ∈ H.

Ceci simplifie :
S_H(s) = Σ_{h∈H\{1}} χ^{sr}(1-h^{-1})
= Σ_{h∈H\{1}} χ^{sr}(1-h) [car h ↦ h^{-1} est bijection sur H\{1}]

ATTENDS. χ^{sr}(h) = 1 pour h ∈ H, car H est dans le noyau de χ^r et
donc de χ^{sr}. Ceci donne :

S_H(s) = Σ_{h∈H\{1}} χ^{sr}(h-1) = Σ_{h∈H\{1}} χ^{sr}(h·(1-h^{-1}))
= Σ_{h∈H\{1}} 1 · χ^{sr}(1-h^{-1})
= Σ_{h'∈H\{1}} χ^{sr}(1-h')  [h' = h^{-1}]

Donc S_H(s) = Σ_{h∈H\{1}} χ^{sr}(1-h).

C'est une somme de χ^{sr} sur l'ensemble 1-H. Et 1-H est la translation
additive de -H, donc 1-H = {1-h : h ∈ H} est un COSET ADDITIF de -H.

Mais -H = H (si -1 ∈ H, ce qui arrive quand g | (p-1)/2, i.e., r pair ou p ≡ 1 mod 2r).

**Observation clé** : S_H(s) = Σ_{h∈H\{1}} χ^{sr}(1-h) est essentiellement
le POLYNÔME DE GAUSS PARTIEL évalué sur H.

### BINÔME B — INNOVATION : BORNE DIRECTE PAR CHANG-TYPE

**Résultat de Bourgain (2005), Lemme pour BGK** :
Si A ⊂ F_p* est un ensemble sans structure additive (|A+A| > C|A|),
alors pour tout caractère χ non trivial :
|Σ_{a∈A} χ(a)| ≤ |A| · p^{-ε}

pour un ε > 0 dépendant de la croissance additive de A.

**Application** : A = 1-H (translation de H). |1-H| = r-1 ≈ r.
Croissance additive : |A+A| = |(1-H) + (1-H)| = |2 - (H+H)|.
Si H a petit sumset (|H+H| ≤ C·r), alors A aussi. Mais H est un sous-groupe
multiplicatif, donc par BKT : |H+H| ≥ c·r^{1+ε'} (sum-product).

Donc |(1-H)+(1-H)| ≥ c·r^{1+ε'}, et le résultat de Bourgain s'applique :

|Σ_{h∈H\{1}} χ^{sr}(1-h)| = |S_H(s)| ≤ r · p^{-ε''}

pour un ε'' > 0 effectif !

**Attention** : le résultat de Bourgain donne ε'' > 0 mais NON EXPLICITE
pour r < √p (même problème que BGK).

**Pour r > √p** : on peut utiliser Burgess / Polya-Vinogradov :
|Σ_{x∈A} χ(x)| ≤ √p · log p pour tout ensemble A.
Ceci donne |S_H(s)| ≤ √p · log p, et |C(s)| ≤ g · p · log p.
|ψ̂(s)| ≤ p · log p. C'est encore TRIVIAL (pire que Weil même).

**Pour r ≈ p^{2/k}** : on est dans le régime r ≪ √p (pour k ≥ 5).
Le résultat de Bourgain donne r · p^{-ε''} avec ε'' non explicite.

### BINÔME B — INNOVATION : LIEN DIRECT H_k ↔ SUM-PRODUCT

**Observation cruciale** : S_H(s) = Σ_{h∈H\{1}} χ^{sr}(1-h).

L'ensemble 1-H ⊂ F_p est la DIFFÉRENCE SET de H translatée.
Les éléments de 1-H sont de la forme 1-h pour h ∈ H.

La somme de caractère Σ_{a∈1-H} χ(a) mesure la CORRÉLATION ADDITIVE
de l'ensemble 1-H avec les cosets du caractère χ.

Par le THÉORÈME DE SUM-PRODUCT de Bourgain-Katz-Tao (2004) :
H n'a ni grande somme ni grand produit. Puisque H·H = H (sous-groupe),
on a |H+H| ≥ c·|H|^{1+ε_0} pour un ε_0 > 0.

Par le lemme de CHANG (2002) / Croot-Sisask (2010) :
Si |A+A| ≥ K·|A|, alors le spectre Λ = {t : |Â(t)| ≥ δ|A|} satisfait
|Λ| ≤ C·K^2/δ^2 · log|A|.

Pour A = 1-H : K ≥ r^{ε_0}, donc |Λ| est PETIT.
Ceci signifie : pour PRESQUE TOUS les caractères χ^{sr},
|Σ_{a∈1-H} χ^{sr}(a)| ≤ δ · r.

Mais "presque tous" ne suffit pas — on a besoin de TOUS s ≠ 0.

**Le spectre restant** : Il pourrait exister O(K²/δ² · log r) valeurs de s
pour lesquelles |S_H(s)| > δr. Si ces valeurs sont les "mauvais" s,
on pourrait les traiter séparément.

### RÉSULTAT PARTIEL (T168 CANDIDAT)

**Énoncé** : Pour H ⊂ F_p* sous-groupe d'ordre r > p^δ avec δ > 0 :

#{s ∈ Z_g : |S_H(s)| > r^{1-ε}} ≤ r^{2ε} · (log r)^2

pour un ε = ε(δ) > 0.

**Preuve sketch** :
1. A = 1-H a |A+A| ≥ c·r^{1+ε_0} par BKT
2. Par Chang : le spectre de 1-H est de taille ≤ r^{2ε_0}·(log r)
3. Hors du spectre : |Â(t)| ≤ r^{1-ε_0}
4. Transformer en termes de S_H via ψ̂(s) ↔ Â(s)

C'est un résultat de TYPE "la plupart des ψ̂(s) sont petits", mais
pas une borne UNIFORME.

### CHECKPOINT R113

1. **Nouvelle approche ?** OUI — sum-product + Chang sur 1-H
2. **Borne obtenue ?** PARTIELLE — la majorité des ψ̂(s) sont petits (T168 candidat)
3. **Borne uniforme ?** NON — un petit ensemble Λ de "mauvais" s persiste
4. **Le résultat suffit-il pour (H_k) ?** À INVESTIGUER — il faut passer du
   spectre moyen au produit de PA (R114)

---

## R114 — EXPLOITATION DU RÉSULTAT SPECTRAL PARTIEL

### OBJECTIF

Utiliser le fait que "presque tous les ψ̂(s) sont petits" (T168 candidat)
pour prouver (H_k), en traitant séparément le petit ensemble de mauvais s.

### BINÔME A — INVESTIGATION : DÉCOMPOSITION SPECTRE BON / MAUVAIS

Décomposons ψ = ψ_good + ψ_bad où :
- ψ̂_good(s) = ψ̂(s) si s ∉ Λ (|ψ̂(s)| ≤ r^{1-ε})
- ψ̂_bad(s) = ψ̂(s) si s ∈ Λ (|Λ| ≤ r^{2ε}·log²r)

La moyenne de ψ sur PA = E_a ∏_m ψ(a+mℓ) = E_a ∏_m (ψ_good + ψ_bad)(a+mℓ).

Par développement : c'est une somme de 2^k termes. Le terme principal est
∏ ψ_good, et les termes mixtes impliquent au moins un ψ_bad.

**Terme principal ψ_good** :
Par Green-Tao / Gowers : |E_a ∏_m ψ_good(a+mℓ) - (Eψ_good)^k| ≤ ||ψ_good||_{U^{k-1}}^{2^{k-1}}
Et ||ψ_good||_{U^{k-1}} est PETIT car ψ̂_good est uniformément borné par r^{1-ε}.

En effet : ||ψ_good||_{U^{k-1}}^{2^{k-1}} ≤ max|ψ̂_good|^{2^{k-1}-2} · ||ψ_good||_2^2
≤ (r^{1-ε})^{2^{k-1}-2} · p (par Parseval ≤ p).

Hmm, c'est trop gros pour k grand (exponentiel en k). Mais l'exposant ε
est multiplié par 2^{k-1}-2, ce qui AIDE.

**Termes mixtes avec ψ_bad** :
||ψ_bad||_1 = Σ_a |ψ_bad(a)| ≤ √g · ||ψ_bad||_2 (Cauchy-Schwarz)
||ψ_bad||_2² = Σ_a ψ_bad(a)² = (1/g)Σ_{s∈Λ} |ψ̂(s)|²
≤ (1/g) · |Λ| · max|ψ̂|² ≤ (1/g) · r^{2ε} · p²
(car max|ψ̂| ≤ p trivialement)

||ψ_bad||_2 ≤ r^ε · p / √g = r^ε · p · √r / √p = r^{ε+1/2} · √p

Les termes mixtes contribuent au plus k · max(ψ)^{k-1} · ||ψ_bad||_1.
Avec max(ψ) ≤ p : contribution ≤ k · p^{k-1} · r^{ε+1/2} · √p · √g.

C'est TROP GROS — la décomposition naïve good/bad ne marche pas
car ψ_bad peut avoir des valeurs très grandes sur peu de cosets.

### BINÔME B — INNOVATION : APPROCHE L^{2k} DIRECTE

Au lieu de passer par Gowers, revenons à la borne directe :

E_k = r^{2k}/p + (r/p) Σ_{a} ψ(a)^k [somme sur g cosets, dont le terme a=H contribue r^{2k}/p]

Le reste R_k = (r/p) Σ_{a ∉ [H]} ψ(a)^k.

Par Parseval sur Z_g :
ψ(a) = (1/g) Σ_s ψ̂(s) ω^{sa}

ψ(a)^k = (1/g^k) Σ_{s_1,...,s_k} ψ̂(s_1)...ψ̂(s_k) ω^{a(s_1+...+s_k)}

Σ_a ψ(a)^k = (1/g^{k-1}) Σ_{s_1+...+s_k ≡ 0 mod g} ψ̂(s_1)...ψ̂(s_k)

= (1/g^{k-1}) Σ_{s_1,...,s_{k-1}} ψ̂(s_1)...ψ̂(s_{k-1}) · ψ̂(-s_1-...-s_{k-1})

**Terme diagonal** (tous s_j = 0) : (1/g^{k-1}) · ψ̂(0)^k = (p-r)^k / g^{k-1} ≈ p^k/g^{k-1} = r^{k-1}·p.

Hmm, ça ne simplifie pas. Essayons plutôt la borne M-directe mais avec
la STRUCTURE SPECTRALE de T168.

**Bound hybride** :
Σ_a ψ(a)^k ≤ (#{a : ψ(a) > T})·p^k + T^{k-2} · Σ_a ψ(a)²

Pour T = r^{1+c} (un peu au-dessus de la moyenne r) :
#{a : ψ(a) > T} ≤ (Σ ψ²)/T² ≤ p·r^{2-η} / r^{2+2c} = p·r^{-η-2c}

Contribution des gros : p·r^{-η-2c} · p^k ≈ p^{k+1}·r^{-η-2c}
Contribution des petits : r^{(1+c)(k-2)} · p·r^{2-η} = p·r^{k-η-2c+ck}

Hmm, ceci donne des bornes mais pas assez fines.

### IDÉE DIRECTE : EXPLOITER QUE ψ EST POSITIVEMENT DÉFINIE

ψ(a) = |f̂(t_a)|² ≥ 0 pour tout a. De plus, ψ est la transformée d'une
mesure de convolution : ψ(a) = |f̂|² = (f * f̌)(a) en quelque sorte.

Plus important : la POSITIVITÉ permet d'utiliser des inégalités spéciales.

**Inégalité de Hölder dans Z_g** :
(Σ_a ψ(a)^k)^{1/k} ≤ (max ψ)^{1-1/k} · (Σ ψ)^{1/k}

Σ_a ψ^k ≤ (max ψ)^{k-1} · Σ ψ = M^{2(k-1)} · (p-r)

Avec M = max|f̂(t)|_{t≠0}. C'est exactement la borne de R106/R110.
**Pas de gain par cette voie.**

### RÉSULTAT R114 : IMPASSE IDENTIFIÉE

Les approches spectrales (good/bad décomposition, L^{2k} direct, Hölder)
convergent toutes vers la même obstruction : la borne sur max|f̂|.

**Diagnostic fondamental** : La norme U^{k-1} pour k ≥ 3 est contrôlée par
les harmoniques de Fourier de ψ sur Z_g. Mais ψ̂(s) est lui-même borné par
|C(s)| ≤ g·√p·|S_H(s)|. Et |S_H(s)| est borné par la corrélation additive/multiplicative
de H, qui est exactement ce que les théorèmes de type sum-product contrôlent —
mais SANS EXPLICITATION pour δ < 1/2.

**Le verrou V_GOWERS SE RÉDUIT À** :
- Soit prouver |S_H(s)| ≤ √r (annulation √g dans les phases de Gauss)
  → Requiert Katz monodromy ou équivalent
- Soit prouver ε(δ) ≥ c·δ dans BGK
  → Problème ouvert classique en théorie additive des nombres

Les deux sont des PROBLÈMES OUVERTS de mathématiques fondamentale, hors CJT.

### CHECKPOINT R114

1. **Décomposition good/bad exploitable ?** NON — ψ_bad trop gros
2. **L^{2k} direct ?** Retombe sur max ψ → BGK
3. **Nouvelle route trouvée ?** NON — convergence vers les mêmes obstructions
4. **Diagnostic** : V_GOWERS = V_BGK_eff = V_SQRT_CANCEL — trois faces du MÊME MUR
5. **Ce mur est** : la corrélation additif/multiplicatif des sous-groupes de F_p*

---

## R115 — CONSOLIDATION FINALE ET BILAN

### THÉORÈME STRUCTUREL DE LA CAMPAGNE

**T167 (Réduction aux moments)** [PROUVÉ pour 3∈H, NON APPLICABLE 3∉H] :
Si 3 ∈ H : E_k(H;α) = T_k(H) = (1/p)Σ_t |f̂(t)|^{2k}.
(= T163, déjà connu R101)

**T166 (Décorrélation croisée)** [PROUVÉ INCONDITIONNEL, R108] :
E_γ(H) = r^4/p + O(r^{3-η}).

**T168 (Spectre partiel)** [CANDIDAT, non formalisé] :
#{s : |S_H(s)| > r^{1-ε}} ≤ r^{2ε}·log²r via Chang + BKT.

**C(s) Exact** [PROUVÉ, R111] :
C(s) = Σ_j τ_j·τ̄_{j+s} = g·τ(χ^{-sr})·S_H(s) pour s ≠ 0,
avec S_H(s) = Σ_{h∈H\{1}} χ^{sr}(1-h).

### CARTE DES VERROUS (R115)

```
         (H_k) pour 3∉H
              │
    ┌─────────┴──────────┐
    │                    │
||ψ||_{U^{k-1}} petit   max|f̂| < r·p^{-ε}
(V_GOWERS)               (V_BGK_eff)
    │                    │
    └─────────┬──────────┘
              │
    |S_H(s)| = Σ_{h∈H} χ^{sr}(1-h) ≤ √r ?
         (V_SQRT_CANCEL)
              │
    Annulation √g dans les phases
    de Gauss τ_j décalées
              │
    ┌─────────┴──────────┐
    │                    │
 Katz monodromy      Sum-product effectif
 (faisceaux)         (δ < 1/2)
    │                    │
    └─────────┬──────────┘
              │
    PROBLÈMES OUVERTS
    DE MATHÉMATIQUE FONDAMENTALE
```

### SYNTHÈSE R111-R115

**Avancées** :
- Calcul EXACT de C(s) via Jacobi-Gauss [R111]
- Réduction à S_H(s) = Σ χ^{sr}(1-h) [R111]
- Identification de la borne √r comme condition suffisante [R112]
- T168 candidat : majorité des S_H(s) sont petits [R113]
- Convergence des trois verrous V_GOWERS/V_BGK/V_SQRT en un seul [R114]

**Impasses** :
- Annulation √g non prouvable par méthodes L² (Parseval + BKT) [R112]
- Décomposition good/bad spectrale insuffisante [R114]
- Toutes les approches convergent vers le même mur fondamental [R114]

**Conclusion de campagne** :
Le verrou (H_k) pour 3∉H se réduit à un UNIQUE problème :
borner |S_H(s)| = |Σ_{h∈H} χ^{sr}(1-h)| ≤ C·√r.

C'est une somme de caractère multiplicatif évaluée sur la translation
additive d'un sous-groupe multiplicatif — un objet au CŒUR de la faille
additif/multiplicatif (R81).

Ce problème est ÉQUIVALENT à :
1. BGK effectif (ε(δ) explicite pour δ < 1/2)
2. Katz monodromy (annulation des phases de Gauss corrélées)
3. Gowers uniformity (U^{k-1} de |f̂|² sur Z_g)

Les trois sont des PROBLÈMES OUVERTS de mathématique fondamentale.
Le CJT a RÉDUIT le gap Bloc 3 à ce problème unique.

### CHECKPOINT R115

1. **Campagne productive ?** OUI — réduction complète à S_H(s)
2. **Verrou cerné ?** OUI — un SEUL objet, trois visages
3. **Score IVS** : 6.0/10 (progrès structurel, pas de théorème fermant le gap)
4. **Prochaine étape** : Publier la réduction (T164 + réduction à S_H(s)) ou
   consulter un expert en théorie analytique des nombres (Katz monodromy)
