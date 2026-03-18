# FINDING: d est l'UNIQUE diviseur non atteint de gcd(corrSum, d)
## 18 Mars 2026, Cycle JEPA 8

### Le fait

Pour k = 3, 4, 5, 6, 9, 10, 12 :
- gcd(corrSum(σ), d) atteint TOUS les diviseurs de d SAUF d lui-même
- d est le SEUL diviseur propre manquant

Pour k = 7, 8, 11 :
- d est manquant + certains grands premiers (83, 233, 7727)
- Ces grands premiers sont exactement ceux qui bloquent par valuation

### Interpretation profonde

corrSum atteint chaque classe de résidus modulo chaque FACTEUR PROPRE de d.
Mais la combinaison CRT spécifique donnant d | corrSum est impossible.

C'est comme un PUZZLE : chaque pièce (mod p_i) peut être placée
dans n'importe quelle position, mais la configuration COMPLÈTE
qui résout le puzzle (= cycle de Collatz) n'existe pas.

### Connexion à Steiner

d = 2^S - 3^k est le dénominateur SPÉCIFIQUE de l'équation de Steiner.
Un diviseur propre d' | d ne correspond à aucune équation de cycle valide.
Le fait que gcd(corrSum, d') = d' SOIT atteignable pour d' ≠ d
mais PAS pour d' = d reflète la SPÉCIFICITÉ de l'équation de Steiner.

### Formulation conjecturale

**Conjecture (Unique Unachieved Divisor)**:
Pour tout k ≥ 3, d(k) est un diviseur non atteint de gcd(corrSum(σ), d(k))
pour tout σ ∈ Comp_cum(S, k).

Equivalence : cette conjecture = Collatz positive-cycle conjecture.

Plus forte : pour "la plupart" des k, d est le SEUL diviseur non atteint.

### Piste pour la preuve

d est "interdit" parce qu'il encode EXACTEMENT la relation 2^S = 3^k.
corrSum ne peut atteindre un multiple de d parce que ses termes
(3^{k-1-i} · 2^{σ_i}) sont "insuffisamment corrélés" à d.

La corrélation de chaque terme avec d est partielle (via p | d pour p | 3^{k-1-i}
ou p | 2^{σ_i}), mais la corrélation TOTALE ne peut atteindre d entier.

C'est peut-être formalisable via la NORME dans le corps de nombres :
N(P_σ(α)) capture la corrélation de P_σ avec TOUTES les conjuguées de α-2.
Pour k=3,4 : la norme est coprime à d (preuve complète).
Pour k ≥ 5 : la norme n'est pas coprime, mais le facteur spécifique (α-2)
ne contribue jamais.
