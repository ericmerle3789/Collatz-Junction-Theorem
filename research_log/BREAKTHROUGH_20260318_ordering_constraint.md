# BREAKTHROUGH: L'ordonnancement est l'obstruction fondamentale
## 18 Mars 2026 — Cycle JEPA 12

### Le fait (vérifié k=3..7)

SANS ordonnancement : target = -3^{k-1} mod d EST atteint par
les sommes pondérées Σ 3^{k-1-π(i)} · 2^{v_i} pour une permutation π.

AVEC ordonnancement (σ₁ < σ₂ < ... < σ_{k-1}) : target JAMAIS atteint.

### Interpretation

L'ordonnancement contraint QUELLE valeur 2^v reçoit QUEL poids 3^{k-1-i}.
Les petites valeurs (v petit) reçoivent les GRANDS poids (3^{k-2}, etc.).
Les grandes valeurs (v grand) reçoivent les PETITS poids (1, 3, etc.).

Pour atteindre le target, il faudrait que certaines GRANDES valeurs
reçoivent de GRANDS poids — ce qui viole l'ordonnancement.

### Formalisation

Soit f: {v_1,...,v_{k-1}} → {0,...,k-2} une bijection (attribution des rangs).
L'ordonnancement impose f(v) = rang de v dans l'ordre croissant.

La somme ORDONNÉE : S_ord(T) = Σ 3^{k-2-rank(v)} · 2^v
La somme LIBRE : peut choisir n'importe quelle bijection f.

Claim : S_ord(T) ne peut jamais atteindre la valeur cible
car les GRANDES valeurs 2^v (qui sont exponentiellement plus grandes)
sont systématiquement multipliées par les PETITS poids 3^{k-2-rank(v)}.

L'ordonnancement crée un biais ANTI-CORRÉLATION entre poids et valeurs :
les plus grands 2^v ont les plus petits coefficients 3^j.

### Conjecture formelle

Pour tout k ≥ 3 et tout T ⊂ {1,...,S-1} de taille k-1 :
Σ_{i=1}^{k-1} 3^{k-1-i} · 2^{t_i} ≢ -3^{k-1} mod d
où t_1 < t_2 < ... < t_{k-1} sont les éléments de T ordonnés.

### Voie de preuve

L'anti-corrélation ordonnée (grands poids → petites valeurs) crée
un BIAIS SYSTÉMATIQUE dans la somme pondérée. Ce biais pourrait
être quantifié par un argument de type REARRANGEMENT INEQUALITY :

Le réarrangement de Hardy-Littlewood dit : Σ a_i · b_i est MINIMISÉ
quand a et b sont triés en ordres OPPOSÉS.

Ici : les a_i = 3^{k-1-i} (décroissants) et b_i = 2^{t_i} (croissants car t_i croissants).
Donc la somme ordonnée est PROCHE DU MINIMUM possible.
Le target (-3^{k-1} mod d) est un résidu qui nécessite une somme NON-MINIMALE.

### Prochaine étape

Quantifier le biais : montrer que la somme ordonnée est toujours dans
un intervalle [S_min, S_max] qui exclut le target mod d.
Cela revient au Range Exclusion — MAIS pour la partie variable uniquement,
pas pour corrSum entier.

La partie variable a un range plus petit que corrSum car le terme
fixe 3^{k-1} est soustrait. Le range de la partie variable est
max(var) - min(var) = corrSum_max - corrSum_min = 3^r - 1 (même que avant).
Et le target est -3^{k-1} mod d qui est un résidu SPÉCIFIQUE.

Si 3^r - 1 < d et que le target est en dehors de l'intervalle
[var_min mod d, var_max mod d]... c'est exactement Range Exclusion
appliqué à la partie variable.

MAIS on a déjà montré que Range Exclusion échoue pour les exposants
cumulatifs car le range est BIEN plus grand que d.

CEPENDANT : la partie variable ordonnée a peut-être un range
DIFFÉRENT de corrSum entier ? Non, c'est le même...

### La vraie question

Le range de la SOMME ORDONNÉE est le même que corrSum (large).
Mais la somme ordonnée est BIAISÉE vers le minimum par le réarrangement.
La distribution de la somme ordonnée mod d est NON-UNIFORME,
concentrée près du minimum. Le target est LOIN du minimum.

C'est un argument de CONCENTRATION + ANTI-CORRÉLATION.
