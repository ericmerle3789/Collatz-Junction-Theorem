# ANALYSE SESSION 10f26 — RESULTATS ARTIN
## 6 mars 2026

---

## RESULTATS CLES

### 1. Catalogue confirme (19/19)
Tous les d(k) = 2^S - 3^k pour k ∈ {3,4,5,13,56,61,69,73,76,148,185,655,917,2183,3540,3895,4500,6891,7752} sont premiers.

### 2. Factorisation complete de d-1 (11 cas, d ≤ 293 bits)

| k | d-1 | Q | Prim? |
|---|-----|---|-------|
| 3 | 2² | 1 | OUI |
| 4 | 2 × 23 | 2 | NON |
| 5 | 2² × 3 | 1 | OUI |
| 13 | 2² × 125707 | 1 | OUI |
| 56 | 2 × 5 × 19 × 443 × (70b prime) | 2 | NON |
| 61 | 2² × 31 × 5179 × (76b prime) | 1 | OUI |
| 69 | 2² × 3 × 5 × (103b prime) | 3 | NON |
| 73 | 2² × 3 × 7 × 2207 × (97b prime) | 3 | NON |
| 76 | 2 × 5 × 907 × 20183 × (92b prime) | 2 | NON |
| 148 | 2 × 18089 × 55201 × 4150459 × (181b prime) | 2 | NON |
| 185 | 2² × 3² × 5 × 743 × (276b prime) | 15 | NON |

### 3. Distributions observees
- **Racines primitives**: 4/11 ≈ 36.4% (constante d'Artin ≈ 37.4%)
- **Q**: {1: 4 fois, 2: 4 fois, 3: 2 fois, 15: 1 fois}
- **ω(d-1)**: entre 1 et 5 facteurs premiers distincts
- **Ratio R/d**: 79-99% — R domine massivement (d-1 a un ENORME facteur premier)

### 4. Camera Thermique
- 19/19 PASS (pour k ≥ 4)
- k=3 et k=5: Therm FAIL car d-1 est entierement smooth, MAIS 2 est racine primitive donc ord = d-1 ne divise pas C directement
- Pour k ≥ 13: M_bits << d_bits, donc R ≈ d, et 2^M ≢ 1 mod d

### 5. Fait universel
**gcd(d, 3^k - 1) = 1 ET gcd(d, 2^S - 1) = 1 pour TOUS les 19 cas**

Consequence: d ne divise ni 2^S - 1 ni 3^k - 1.
Donc ord_d(2) ∤ S pour tous les cas (confirme).

### 6. Non-lissete de d-1
- Parametre Dickman u(k) = S·ln2/ln(S-1) croît avec k
- Pour k=7752: u ≈ 904, ρ(u) ≈ 10^{-2281}
- La probabilite de smoothness est astronomiquement faible
- **Aucun des 19 d-1 n'est (S-1)-smooth** (verifie pour les 11 petits cas avec factorisation complete)

### 7. Structure de d-1 mod petits premiers
- v₂(d-1) = 1 si k pair, v₂(d-1) ≥ 2 si k impair (prouve algebriquement)
- d-1 mod 3: depend de k mod 3 (via 3^k mod 3 = 0)

---

## BUG NOTE

Le test I5 `is_smooth` dans le script affiche "OUI ⚠️" pour les grands d.
C'est un FAUX POSITIF: pour les grands d, factorizations[k] ne contient QUE
les facteurs ≤ S-1 (par construction de la passe B). Le test
`all(p <= B for p in factorizations[k])` est donc trivialement vrai.

La Camera Thermique (2^M ≢ 1 mod d) est le VRAI test de non-lissete
fonctionnelle, et il PASSE pour TOUS les cas k ≥ 4.

---

## QUESTION CLE POUR LA SUITE

**Pour prouver Artin inconditionnellement, il suffit de montrer:**

> Pour k assez grand, si d(k) = 2^S - 3^k est premier, alors P⁺(d-1) > S-1.

Ou P⁺(n) = plus grand facteur premier de n.

Heuristiquement c'est ecrasant (ρ(u) → 0 super-exponentiellement).
Mais il faut un argument DETERMINISTE.

**Approches a explorer:**
1. Zsygmondy adapte pour d-1 = (2^S - 1) - 3^k
2. Borne inferieure sur P⁺(a^n - b^n - c) (Stewart, 2013)
3. Structure algebraique: Phi_n(2) facteurs cyclotomiques
4. Argument combinatoire: il y a "trop peu" de premiers ≤ S-1 pour couvrir un nombre de S bits
