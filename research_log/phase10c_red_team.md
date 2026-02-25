# PHASE 10C — RED TEAM
## Attaque systématique des claims Phase 10A-B
## Date : 24 février 2026

---

## ATTAQUE 1 : "F(n) contractante" — est-ce VRAIMENT utile ?

### Le claim
F(n) = corrSum(n)/d a pente 3^k/2^S < 1 sur chaque morceau affine.
Donc au plus 1 point fixe par morceau.

### L'attaque
OUI, F est contractante sur chaque morceau. MAIS :
- Le nombre de morceaux est C(S-1, k-1) ≈ 2^{0.87k} (EXPONENTIEL)
- Chaque morceau a au plus 1 candidat → au plus 2^{0.87k} candidats
- C'est ÉNORME. La contractance seule ne tue rien.

### Verdict : CLAIM VRAI mais INUTILE seul
La contractance réduit à 1 candidat/morceau, mais il y a trop de morceaux.
Il faut une raison pour que CHAQUE candidat échoue.

---

## ATTAQUE 2 : "Baker borne n ≤ k^{O(log k)}" — vérifions la chaîne

### Le claim
Pour un k-cycle, le minimum n satisfait n ≤ k^{C·log k}.

### L'attaque
La chaîne logique est :
1. |S·log2 - k·log3| ≥ exp(-C(log k)²) [Baker-Laurent-Mignotte-Nesterenko]
2. d = 2^S - 3^k ≥ 3^k · |S·log2/k - log3| ≈ 3^k · exp(-C(log k)²)
3. n ≤ k·3^{k-1}/d ≤ k/exp(-C(log k)²) = k^{O(log k)}

PROBLÈME au point 2 : d = 2^S - 3^k. On a S = ⌈k·log₂3⌉.
Donc S·log2 - k·log3 = {k·log₂3}·log2 (partie fractionnaire).
Baker borne |S·log2 - k·log3| par le bas.
MAIS la formule d ≈ 3^k · (2^{S/k·...} - 1) n'est pas si directe.

En fait : 2^S = 3^k + d, donc log(2^S) = log(3^k + d).
Si d << 3^k : S·log2 ≈ k·log3 + d/3^k.
Donc d ≈ 3^k · (S·log2 - k·log3).
Et Baker donne S·log2 - k·log3 ≥ exp(-C(log k)²).
Donc d ≥ 3^k · exp(-C(log k)²). ✓

La borne n ≤ k·3^{k-1}/d vient du produit :
Π(1+1/(3n_j)) = 1 + d/3^k, avec n_j ≥ n.
(1+1/(3n))^k ≥ 1 + d/3^k → k/(3n) ≥ d/3^k → n ≤ k·3^{k-1}/d. ✓

### Verdict : CLAIM VRAI et SOLIDE
Baker est un théorème publié et vérifié. La chaîne est correcte.

---

## ATTAQUE 3 : "Budget exactement équilibré" — tautologie ?

### Le claim
Montée (3/2)^{0.415k} × Descente (3/4)^{0.585k} = 1 exactement.

### L'attaque
C'est une TAUTOLOGIE. Par définition, un cycle a produit = 1.
Le budget est équilibré PARCE QUE c'est un cycle.
Ça ne prouve ni n'exclut rien.

L'observation utile est que les +1 (termes 1/n_j) sont la SEULE marge.
Mais montrer que ces termes ne peuvent pas s'ajuster est le problème ouvert.

### Verdict : CLAIM VRAI mais TAUTOLOGIQUE
Aucune information nouvelle. Simple reformulation de la condition de cycle.

---

## ATTAQUE 4 : "Auto-référence exponentiellement rare" — rigueur ?

### Le claim
La densité des n qui produisent une séquence spécifique (c_1,...,c_k)
est ≈ 2^{-S}. Avec n ≤ k^{O(log k)} candidats, probabilité → 0.

### L'attaque
1. C'est un argument HEURISTIQUE, pas une preuve
2. L'hypothèse d'équidistribution n'est pas justifiée
3. Les n_c = R(c)/d sont des rationnels SPÉCIFIQUES, pas aléatoires
4. Un seul "miracle arithmétique" suffit à créer un cycle
5. L'analogue : "les nombres parfaits sont rares" mais ils EXISTENT

Plus grave : l'argument dit "c'est rare" mais pas "c'est impossible".
En maths, rare ≠ impossible. Les nombres premiers de Mersenne sont
exponentiellement rares mais il en existe infiniment (conjecture).

### Verdict : CLAIM HEURISTIQUE — NE CONSTITUE PAS UNE PREUVE
C'est une intuition correcte mais non rigoureuse.

---

## ATTAQUE 5 : La cascade corrigée — que reste-t-il ?

### Le claim (Phase 10A)
Sans hypothèse c_j croissants, la cascade donne :
- c_1 = v_2(3n+1) : déterminé par n
- n_1 = (3n+1)/2^{c_1}, puis c_2 = v_2(3n_1+1), etc.
- Minimalité n_j ≥ n borne n à chaque pas

### L'attaque
La cascade SANS c_j ordonnés est correcte dynamiquement.
MAIS elle ne bloque PAS en 3 pas comme la version erronée.

Contre-exemple : prenons c_1 = 1 (forcé), c_2 = 1, c_3 = 1, ...
Le chemin "tout-uns" donne n_j = (3^j·n + R_j)/2^j.
Dénominateur de minimalité : 2^j - 3^j < 0 pour j ≤ k.
Donc contrainte TOUJOURS VACUEUSE.

Le chemin tout-uns ne bloque jamais la minimalité.
Il échoue pour d'autres raisons (Σc_j = k ≠ S), mais la
cascade seule ne peut pas l'exclure.

La cascade n'est puissante que pour les chemins avec des
c_j grands (≥ 2), qui font descendre l'orbite.

### Verdict : CASCADE INSUFFISANTE SEULE
Elle borne n pour certains chemins mais pas tous.

---

## BILAN RED TEAM

| # | Claim | Verdict |
|---|-------|---------|
| 1 | F contractante | Vrai mais inutile seul |
| 2 | Baker n ≤ k^{O(log k)} | SOLIDE |
| 3 | Budget équilibré | Tautologie |
| 4 | Auto-référence rare | Heuristique, pas preuve |
| 5 | Cascade | Insuffisante seule |

### Conclusion RED TEAM
Aucun des 5 claims ne constitue une preuve.
Baker (claim 2) est le seul résultat dur.
Les autres sont des observations correctes mais insuffisantes.

### CE QUI MANQUE VRAIMENT
Un argument qui exploite la structure SPÉCIFIQUE de d = 2^S - 3^k.
Pas un argument générique (densité, contractance, budget).
Quelque chose qui utilise le fait que d est de la forme 2^S - 3^k
et que corrSum = Σ 3^{k-1-i} · 2^{A_i} a une structure LIÉE à d.

### DIRECTION PHASE 10D
Revenir à la question fondamentale de Tao/Lagarias :
**Pourquoi corrSum ≢ 0 (mod d) ?**
Exploiter 2^S ≡ 3^k (mod d) directement dans la somme.
