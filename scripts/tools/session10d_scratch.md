# SESSION 10d — NOTES D'ANALYSE (Mécanisme II CRT)
## Date : 4 mars 2026

---

## RÉSULTATS CLÉS session10d_mechanism_II_crt.py

### Classification des k par mécanisme de blocage

| k   | d         | Type     | Mécanisme              | Détail |
|-----|-----------|----------|------------------------|--------|
| 3   | 5         | Premier  | **Mec. I** (prime)     | N₀(5) = 0 |
| 4   | 47        | Premier  | **Mec. I** (prime)     | N₀(47) = 0 |
| 5   | 13        | Premier  | **Mec. I** (prime)     | N₀(13) = 0 |
| 6   | 5×59      | 2 fact.  | **Mec. II** (pairwise) | M[0,0](5,59) = 0 |
| 7   | 23×83     | 2 fact.  | **Mec. I** (un facteur)| N₀(83) = 0 |
| 8   | 7×233     | 2 fact.  | **Mec. I** (un facteur)| N₀(233) = 0 |
| 9   | 5×2617    | 2 fact.  | **Mec. II** (pairwise) | M[0,0](5,2617) = 0 |
| 10  | 13×499    | 2 fact.  | **Mec. II** (pairwise) | M[0,0](13,499) = 0 |
| 11  | 11×7727   | 2 fact.  | **Mec. I** (un facteur)| N₀(7727) = 0 |
| 12  | 5×59×1753 | 3 fact.  | **Mec. III** (triplet) | M[0,0,0] = 0 mais paires ≠ 0 |
| 13  | 502829    | Premier  | **Mec. I** (prime)     | N₀(502829) = 0 |

### Mécanisme I : Un facteur bloque seul
Pour k=7 (p=83), k=8 (p=233), k=11 (p=7727) :
- Un facteur premier grand a N₀(p) = 0
- C'est le même blocage que pour d premier
- Caractéristique : C/p < 1 pour ce facteur (plus de résidus que de compositions)

### Mécanisme II : Anti-corrélation pairwise
Pour k=6, 9, 10 :
- CHAQUE facteur a N₀(p) > 0 individuellement
- MAIS quand corrSum ≡ 0 mod p₁, TOUJOURS corrSum ≢ 0 mod p₂
- L'anti-corrélation est BIDIRECTIONNELLE (I3 : vérifiée dans les deux sens)

**Observation I5** : Les multiples de p₁ atteints, réduits mod p₂, ne contiennent JAMAIS 0.

### Mécanisme III : Anti-corrélation de rang supérieur
Pour k=12 (d = 5×59×1753) :
- Les PAIRES ne bloquent PAS :
  - M[0,0](5,59) = 300 (attendu 278.5)
  - M[0,0](5,1753) = 36 (attendu 31.8)
  - M[0,0](59,1753) = 6 (attendu 2.6)
- Le TRIPLET bloque : M[0,0,0](5,59,1753) = 0
- Cela signifie : on peut être ≡0 mod 2 facteurs à la fois, mais pas mod 3.

### Ordres multiplicatifs (I4) — Patterns observés
- Quand N₀(p) = 0 : ord_p(2) est souvent grand (≈ p-1 ou p/2)
- Quand N₀(p) > 0 : ord_p(2) plus petit
- Pour p=5 (apparaît dans k=6,9,12,17,20) : ord=4 (toujours), σ̃(u)=0
- Pour p=13 (apparaît dans k=10,15,20) : ord=12, u=5, ord(u)=4

---

## SYNTHÈSE GLOBALE SESSION 10 (a, b, c, d)

### Ce qui est PROUVÉ (numériquement, k=3..21)
1. N₀(d) = 0 pour tout k=3..21 ✓
2. Mécanisme I bloque pour d premier ET certains composites (quand un facteur est « gros »)
3. Mécanisme II (pairwise CRT) bloque pour 2 facteurs quand les deux ont N₀(p) > 0
4. Mécanisme III (triplet CRT) nécessaire pour k=12

### Ce qui est THÉORÈME (prouvé formellement)
1. f(B+1) = 2·f(B) mod p (relation de décalage)
2. Im(f) est ×2-presque-clos : violations UNIQUEMENT au plafond B_max = M
3. σ̃(u) = 0 ⟺ ord(u) | (k-1)
4. u^k = 2^{k-S} mod p (identité universelle)
5. σ(u) = (2^{k-S} - 1)/(u - 1) mod p

### Ce qui MANQUE pour la preuve universelle
1. **Mec. I** : Prouver que -1 ∉ Im(f) pour TOUT d premier (pas juste k=3,4,5,13)
   - Piste : argument de fermeture ×2 + plafond
   - Piste : backward chain depuis -1 vers σ̃(u)
   - Piste : inégalité sur la taille de l'image vs position de -1

2. **Mec. II** : Prouver l'anti-corrélation pairwise quand les deux facteurs ont N₀ > 0
   - Piste : d = 2^S - 3^k lie les ordres dans p₁ et p₂
   - Piste : les compositions ≡ 0 mod p₁ forment un sous-ensemble « structuré »
     qui évite 0 mod p₂ par construction

3. **Mec. III** : Prouver le blocage par rang r ≥ 3 quand les paires échouent
   - Cas rare (seul k=12 parmi k=3..13)
   - Potentiellement plus difficile

4. **Universalité** : Couvrir TOUT k ≥ 1 → ∞
   - k=1,2 : cas triviaux (traitement séparé)
   - k grand : argument entropique C/d → 0 AIDE mais ne suffit pas seul
   - Besoin de combiner Mec. I/II/III avec l'argument entropique

---

## PROCHAINES ÉTAPES

1. Mettre à jour MIND_MAP et BLOCKING_MECHANISM_PROOF_SKETCH
2. Régression tests (110 tests)
3. Identifier la piste la plus prometteuse pour une preuve UNIVERSELLE
4. Éventuellement : investiguer k=14..17 pour la classification Mec. I/II/III
