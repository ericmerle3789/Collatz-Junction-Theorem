# R175 — SYNTHÈSE : LE PHÉNOMÈNE DU PREMIER RÉSISTANT
## ET L'ANTI-CORRÉLATION DES DIVISIBILITÉS

**Date :** 15 mars 2026
**Statut :** DÉCOUVERTES STRUCTURELLES MAJEURES — pas encore une preuve

---

## 1. RÉSULTATS EMPIRIQUES (R175)

### 1.1 La non-inversibilité partielle

**Fait 1 :** gcd(g(v), d) > 1 est POSSIBLE. La conjecture "g toujours inversible mod d" est FAUSSE.

*Exemples :* S=8, x=4, d=175=5·7 : gcd(g(v), d) = 5 ou 7 pour 37.5% des vecteurs.

### 1.2 La non-annulation universelle

**Fait 2 :** gcd(g(v), d) < d pour TOUS les (S,x,v) testés (S ≤ 17). La conjecture "d ∤ g(v) toujours" reste VRAIE.

### 1.3 Le premier résistant

**Fait 3 :** Pour chaque (S,x), quand d est composite, les facteurs premiers de d se répartissent en :
- **Premiers passants** : ∃ v tel que p | g(v)
- **Premiers résistants** : ∀ v, p ∤ g(v)

Il y a TOUJOURS au moins un premier résistant (ou une puissance première résistante).

### 1.4 L'anti-corrélation des divisibilités

**Fait 4 (CRITIQUE) :** Pour les paires de premiers (p₁, p₂) divisant d, la divisibilité conjointe (p₁ | g ET p₂ | g) est souvent **MOINS fréquente** que le produit des fréquences individuelles.

| Cas | d | Paire | Attendu | Observé | Ratio |
|-----|---|-------|---------|---------|-------|
| S=8, x=4 | 175=5·7 | (5,7) | 2.0 | **0** | 0.00 |
| S=10, x=2 | 1015=5·7·29 | (5,7) | 2.5 | **0** | 0.00 |
| S=12, x=6 | 3367=7·13·37 | (7,13) | 5.8 | **0** | 0.00 |
| S=12, x=6 | 3367=7·13·37 | (7,37) | 2.9 | **0** | 0.00 |
| S=14, x=8 | 9823=11·19·47 | (11,19) | 10.6 | **0** | 0.00 |
| S=14, x=8 | 9823=11·19·47 | (11,47) | 4.2 | **0** | 0.00 |
| S=16, x=4 | 65455=5·13·19·53 | (5,19) | 21.4 | **0** | 0.00 |

**MAIS** certaines paires sont au contraire POSITIVEMENT corrélées :

| Cas | d | Paire | Attendu | Observé | Ratio |
|-----|---|-------|---------|---------|-------|
| S=11, x=5 | 1805=5·19² | (5,19) | 4.7 | 11 | 2.33 |
| S=14, x=8 | 9823=11·19·47 | (19,47) | 2.6 | 14 | 5.30 |
| S=16, x=8 | 58975=5·7·337 | (7,337) | 4.6 | 16 | 3.48 |

**Interprétation :** Les divisibilités par certains premiers sont MUTUELLEMENT EXCLUSIVES (corrélation négative totale), tandis que d'autres sont corrélées. Le réseau de corrélations est tel que la divisibilité SIMULTANÉE par TOUS les facteurs premiers est toujours impossible.

### 1.5 Le cas d premier

**Fait 5 :** Quand d est premier, 0 ∉ Image(g mod d). Pas un seul vecteur ne satisfait d | g.

C'est le cas le plus "propre" et le plus mystérieux : AUCUN facteur commun entre g(v) et d, pour AUCUN v.

**Coverage :** La fraction des résidus mod d atteints par g varie de 0.1% (S=17, x=2) à 92.3% (S=8, x=5, d=13). 0 est TOUJOURS le résidu manquant le plus "structurel".

## 2. TAXONOMIE DES MÉCANISMES DE RÉSISTANCE

### 2.1 Type A : d premier → résistance totale

Quand d est premier, la résistance est ABSOLUE : p = d et p ∤ g(v) pour tout v.

Ce cas est le plus fort et le plus fréquent (beaucoup de valeurs de d sont premières).

### 2.2 Type B : d composite, un grand premier résiste

Le plus souvent, le plus GRAND facteur premier de d est résistant. Exemple :
- S=13, x=6 : d = 7463 = 17·439. Le premier 439 résiste (17 ne résiste pas).

**Explication heuristique :** Pour un grand premier p | d, la probabilité qu'un vecteur satisfasse p | g est ≈ 1/p (si g est "pseudo-aléatoire" mod p). Avec C(S,x) vecteurs, le nombre attendu de solutions est C(S,x)/p. Pour p grand, ce nombre peut être < 1, rendant les solutions improbables.

### 2.3 Type C : d composite, corrélation négative

Quand la résistance n'est pas portée par un seul premier, c'est la CORRÉLATION NÉGATIVE entre les divisibilités qui empêche d | g. Exemple :

S=8, x=4 : d = 175 = 5·7.
- 5 | g pour 25% des vecteurs
- 7 | g pour 12.5% des vecteurs
- 5·7 = 35 | g pour **0%** des vecteurs (attendu : 3.1%)

L'ANTI-CORRÉLATION entre "5 | g" et "7 | g" est TOTALE.

### 2.4 Type D : d composite, corrélation mixte avec premier puissance résistante

S=11, x=5 : d = 1805 = 5·19².
- 5 | g pour 14% des vecteurs
- 19 | g pour 7% des vecteurs
- 5·19 | g pour 2.4% des vecteurs (> attendu : corrélation POSITIVE)
- 5·19² | g pour **0%** des vecteurs

Ici, la résistance est au niveau de la PUISSANCE 19², pas du premier 19 lui-même.

## 3. LES DEUX QUESTIONS DISTINCTES

### Question A (Le cas premier)
**Pour d = 2^S - 3^x premier, montrer que g(v) ≢ 0 mod d pour tout v.**

C'est la question la plus "propre". Elle dit : dans F_d, le polynôme F(2) = Σ 3^{x-1-j} · 2^{e_j} n'est jamais nul.

**Avantage :** Pas de complication avec les facteurs premiers.
**Obstacle :** d peut être très grand (> 10^5 pour S ≥ 17), et le nombre de vecteurs C(S,x) est encore plus grand.

### Question B (Le cas composite)
**Pour d = 2^S - 3^x composite, montrer que d ∤ g(v) pour tout v.**

**Avantage :** La résistance peut venir de mécanismes locaux (un seul premier suffit).
**Obstacle :** Le mécanisme change selon la factorisation de d.

### La question UNIVERSELLE
Prouver A OU B selon la nature de d, pour TOUT (S, x) admissible.

## 4. PISTE POUR UNE PREUVE UNIVERSELLE

### 4.1 L'obstruction archimédienne déguisée

**Observation clé :** Pour d premier, la non-annulation de g mod d n'est PAS une propriété purement modulaire. Elle survit au passage aux corps finis (g ≢ 0 dans F_d), ce qui suggère une propriété ALGÉBRIQUE de g.

La conjecture implicite : la structure anti-corrélée de g (grands 3-exposants × petits 2-exposants) induit une "torsion" dans F_d qui évite le zéro.

### 4.2 L'analogue de Weil

Dans F_p, g(v) = Σ 3^{x-1-j} · 2^{e_j} est une somme d'exponentielles. Par les bornes de Weil :

|Σ ψ(g(v))| ≤ C · √p pour un caractère additif ψ.

Si on pouvait montrer que la somme Σ_{v} exp(2πi·g(v)/p) a une borne "Weil-like", on pourrait montrer que TOUS les résidus sont atteints, SAUF un nombre borné. Et montrer que 0 fait partie de ces exceptions.

Mais la borne de Weil standard ne distingue PAS 0 des autres résidus.

### 4.3 L'argument de poids

L'idée la plus prometteuse reste l'argument de POIDS : dans g(v), le terme 3^{x-1} · 2^{e₀} a un "poids 3-adique" de x-1, tandis que le terme 2^{e_{x-1}} a un poids de 0. La somme g = Σ pondérée est dominée par le premier terme dans un sens 3-adique, et par le dernier terme dans un sens 2-adique. Cette double domination crée un "couloir" dans Z/dZ qui évite 0.

**Formalisation possible :** Montrer que l'ensemble {g(v) mod d : v ∈ V} est contenu dans un INTERVALLE d'arc de Z/dZ (au sens de la distance cyclique), et que 0 est hors de cet arc.

Ceci utiliserait l'inégalité de réarrangement de manière cruciale : g est la somme MINIMALE (parmi toutes les pairings), et cette minimisation contraint g à rester dans une "zone" de Z/dZ.

## 5. RECOMMANDATIONS

### Priorité 1 : Prouver le cas d premier
Si on peut montrer g(v) ≢ 0 mod p pour tout premier p de la forme 2^S - 3^x (avec S, x appropriés), alors :
- Pour d premier : terminé directement
- Pour d composite : il suffit de montrer qu'au moins un facteur premier de d est de cette forme (ce n'est pas garanti, mais c'est fréquent)

### Priorité 2 : L'argument de corrélation négative
Montrer THÉORIQUEMENT que la divisibilité par p₁ et p₂ (facteurs de d) est anti-corrélée quand p₁p₂ | d. Ceci pourrait utiliser le CRT combinatoire et la structure de g.

### Priorité 3 : L'argument d'arc dans Z/dZ
Montrer que Image(g mod d) est concentrée dans un arc qui évite 0.

## 6. ÉTAT DE L'EXPLORATION

| Direction | Statut | Résultat |
|-----------|--------|----------|
| gcd(g,d) = 1 ? | ❌ FAUX | gcd > 1 possible, mais gcd = d jamais |
| Premier résistant | ✅ CONFIRMÉ | Toujours au moins un p\|d avec p ∤ g(v) |
| Anti-corrélation divisibilités | ✅ CONFIRMÉ | Corrélation négative forte entre divisibilités |
| d premier → g ≢ 0 | ✅ CONFIRMÉ (S≤17) | Fait empirique robuste |
| Corrélation positive partielle | ⚠️ OBSERVÉ | Certaines paires (p₁,p₂) corrélées positivement |
| Preuve universelle | ❌ PAS ENCORE | Le GAP théorique reste ouvert |
