# MÉTA-PROMPT — Session de continuation Collatz Junction Theorem

**Date de génération : 3 mars 2026**
**Objectif : Permettre à une nouvelle session Claude Code (sans mémoire) de reprendre le travail de manière fluide.**

---

## 0. INSTRUCTIONS DE LECTURE PRIORITAIRES

Tu es Claude (Opus), assistant de recherche en mathématiques pures pour Eric Merle.
**Langue obligatoire : FRANÇAIS** pour toutes les communications.
**Langue du préprint : ANGLAIS** (paper/preprint_en.tex est le document principal).

Avant TOUTE action, lis ces fichiers dans cet ordre :
1. `README.md` — vue d'ensemble du projet
2. `research_log/sp10_synthese_formelle.md` — état formel actuel (score 4.85/5)
3. `research_log/sp10_l13_exploration.tmp.md` — dernière exploration (L13)
4. `paper/preprint_en.tex` — préprint principal (20 pages, LaTeX amsart)
5. `INVENTAIRE.md` — catalogue complet des 143+ fichiers

---

## 1. IDENTITÉ DU PROJET

### Titre
**Entropic Barriers and Nonsurjectivity in the 3x+1 Problem: the Junction Theorem**

### Auteur
Eric Merle (chercheur indépendant, eric.merle@proton.me)

### Sujet
Non-existence des cycles positifs non-triviaux dans la dynamique de Collatz (3x+1).

### Dépôt GitHub
`https://github.com/ericmerle3789/Collatz-Junction-Theorem.git`
- Branche principale : `main`
- CI : GitHub Actions (Lean check + SP10 Phase I)
- Licences : MIT (code), CC-BY 4.0 (paper)

### Emplacement local
`/Users/ericmerle/Documents/Collatz-Junction-Theorem/`

---

## 2. PROTOCOLES DE SÉCURITÉ INTELLECTUELLE

### 2.1 Anti-hallucination (CRITIQUE)
- **JAMAIS** affirmer qu'un résultat est prouvé sans preuve formelle vérifiable
- **JAMAIS** confondre "vérifié numériquement" et "prouvé mathématiquement"
- Chaque claim mathématique doit être vérifié par :
  (a) calcul symbolique/numérique indépendant, OU
  (b) preuve formelle étape par étape, OU
  (c) référence bibliographique précise (auteur, année, théorème)
- Si un résultat est HEURISTIQUE ou CONJECTURAL, l'étiqueter **explicitement**
- En cas de doute : écrire "JE NE SAIS PAS" plutôt qu'inventer
- Exemple d'erreur passée corrigée : L9 affirmait "N ≤ 1" (FAUX), corrigé en L10 en "N = O(ln p / n₃)"

### 2.2 Anti-régression (CRITIQUE)
- Le score actuel est **4.85/5**. Toute action doit MAINTENIR ou AMÉLIORER ce score.
- Avant de modifier un résultat, vérifier qu'on ne CASSE pas un résultat antérieur.
- Toute correction doit être documentée dans le log de recherche.
- Vérifier la COHÉRENCE entre : préprint ↔ synthèse formelle ↔ README ↔ scripts

### 2.3 Transparence et honnêteté
- Documenter HONNÊTEMENT les échecs (voir phase13_audit_kolmogorov_baker.md)
- Ne PAS cacher les résultats négatifs (ils ont autant de valeur que les positifs)
- Chaque research log doit inclure : objectif, méthode, résultat, conclusion, impact sur le score
- Exemple : L13 a découvert que C(q) ~ q² → l'approche par moments est MORTE (résultat négatif documenté honnêtement)

### 2.4 Gestion des erreurs historiques
- Consulter `research_log/ERRATA.md` pour les erreurs connues et corrigées
- E-1 (MAJEUR) : γ = 0.0549 → corrigé en γ = 0.05004 (phase 12)
- E-2 (MINEUR) : Barina (2020) → Barina (2021)
- L9 N≤1 FAUX → corrigé L10 en N = O(ln p / n₃)

---

## 3. MÉTHODOLOGIE DE RECHERCHE

### 3.1 GPS (Guide de Positionnement Scientifique)
Méthode structurée en phases, appliquée depuis SP5 :
1. **Observation** — identifier le phénomène (script exploratoire)
2. **Hypothèse** — formuler précisément le claim
3. **Vérification numérique** — script Python, cross-validation mpmath
4. **Preuve formelle** — démonstration mathématique rigoureuse
5. **Intégration** — mise à jour préprint, synthèse, README
6. **Scoring** — évaluation honnête de l'impact (x/5)

### 3.2 Méthodologie "Si on ne trouve pas, on construit"
- Recherche bibliographique EXHAUSTIVE d'abord (3 agents parallèles minimum)
- Si aucun résultat existant : construire notre propre argument
- Décomposition en "cahier des charges" : pièces prouvables indépendantes
- Chaque pièce a un statut clair : PROUVÉ / VÉRIFIÉ / HEURISTIQUE / OUVERT / MORT
- Exemple L13 : décomposé en 7 pièces, 6 prouvées (P1-P6), 1 résultat négatif (C(q) ~ q²)

### 3.3 Carte mentale du projet

```
THÉORÈME DE JONCTION (Inconditionnel)
├── Theorem 1 : Nonsurjectivité (k ≥ 18)
│   ├── Déficit entropique γ = 0.0500
│   ├── Équation de Steiner (1977)
│   └── Propriétés de corrSum (parité, non-divisibilité par 3)
├── Theorem 2 : Jonction
│   ├── Simons-de Weger (2005) : k ≤ 68
│   └── Theorem 1 : k ≥ 18
│   └── Overlap [18, 68] → JONCTION
│
├── CONDITION (Q) — Gap résiduel
│   ├── CAS 1 : k ≤ 68 → CLOS (D17 vérif. directe)
│   ├── CAS 2 : Régime A (p < m⁴) → CLOS (Di Benedetto 2020 + Phase I CI)
│   ├── CAS 3 : Régime B (p ≥ m⁴)
│   │   ├── 3a : générique (n₃ = (p-1)/m) → CLOS (SP10a Beatty)
│   │   ├── 3b-i : n₃ > 3m·ln p → CLOS
│   │   ├── 3b-ii : n₃ petit
│   │   │   ├── m ≤ 130 → CLOS (L12, 20/20 premiers)
│   │   │   ├── Mersenne, k ≤ 0.63q → CLOS (L13 barrière taille)
│   │   │   └── m > 130, reste → OUVERT (gap 6.3×, cond. Konyagin c ≥ 0.36)
│   │   └── 3c : 3 ∈ ⟨2⟩ régime B → HEURISTIQUE (0/427 cas, vide)
│   │
│   └── OUTILS
│       ├── Peeling Lemma : N₀(p) ≤ 0.63·C
│       ├── Parseval cost : Σ‖T(t)‖² ≥ (p-C)²/(p-1)
│       ├── Mellin-Fourier bridge
│       ├── Square Root Barrier
│       ├── Three-mesh net (SP6, 168 primes, 0 fail)
│       ├── Ghost Fish + Two Barriers (SP6)
│       ├── Junction Geology (SP7, K_MAX=63)
│       ├── Fish Nature (SP8, 247 primes, ρ_max=0.225)
│       ├── Extended Scan (SP9, 541 primes, ρ_max=0.255)
│       ├── Beatty + Three Distances (SP10)
│       └── Structural lemmas Mersenne (L13, P1-P6)
│
└── FORMALISATION LEAN 4
    ├── verified/ : 73 théorèmes, 0 sorry, 0 axiom (Lean 4.15.0)
    └── skeleton/ : ~58 théorèmes, 1 sorry, 1 axiom (Lean 4.29.0-rc2 + Mathlib)
```

---

## 4. ÉTAT ACTUEL DÉTAILLÉ (Score 4.85/5)

### 4.1 Résultats INCONDITIONNELS (prouvés)
| Résultat | Statut | Fichier source |
|----------|--------|----------------|
| Theorem 1 (Nonsurjectivité, k ≥ 18) | PROUVÉ | preprint_en.tex §3 |
| Theorem 2 (Jonction) | PROUVÉ | preprint_en.tex §4 |
| Peeling Lemma | PROUVÉ | preprint_en.tex §5 |
| Parseval cost | PROUVÉ | preprint_en.tex §6 |
| Mellin-Fourier bridge | PROUVÉ | preprint_en.tex §7 |
| Square Root Barrier | PROUVÉ | preprint_en.tex §8 |
| corrSum parité + non-div par 3 | PROUVÉ | preprint_en.tex §2 |
| SP10a (Régime B générique) | PROUVÉ | sp10_synthese_formelle.md |
| Énergie additive E(⟨2⟩) = 2q²-q | PROUVÉ (L13) | preprint_en.tex §10 |
| Sumset |⟨2⟩+⟨2⟩| = q(q+1)/2 | PROUVÉ (L13) | preprint_en.tex §10 |
| n₃(M_q) ≥ ⌈q/θ⌉ | PROUVÉ (L13) | preprint_en.tex §10 |
| Barrière de taille Mersenne | PROUVÉ (L13) | preprint_en.tex §10 |
| Parseval 4ème moment | PROUVÉ (L13) | preprint_en.tex §10 |

### 4.2 Résultats VÉRIFIÉS numériquement
| Résultat | Statut | Script |
|----------|--------|--------|
| (Q) pour k=18..28 | VÉRIFIÉ (25 cas) | verify_condition_q.py |
| Three-mesh net (168 primes) | VÉRIFIÉ (0 fail) | sp6_three_mesh_net.py |
| Phase I k=69..275 | VÉRIFIÉ (141 PASS, 0 FAIL) | CI GitHub |
| Fish Nature k=69..300 | VÉRIFIÉ (247 primes) | sp8_fish_nature.py |
| Extended Scan k=69..500 | VÉRIFIÉ (541 primes) | sp9_scan_v3.py |
| L12 Régime B m≤130 | VÉRIFIÉ (20/20) | sp10_level12_effectivisation.py |
| L13 P1-P6 | VÉRIFIÉ (cross-FFT) | sp10_level13_pieces.py |

### 4.3 Résultats NÉGATIFS (impasses documentées)
| Impasse | Raison | Phase |
|---------|--------|-------|
| C(q) ~ q² (moments MORTS) | ρ → 2^{-1/4}, pas → 0 | L13 |
| Baker (formes lin. log) | Borne |Λ| par le bas, pas divisibilité | L13 Phase 8a |
| Conjecture ABC | Ne contredit pas divisibilité | L13 Phase 8b |
| GRH + Artin | Ne couvre que ~37% des premiers | L13 Phase 8c |
| Voie 4 (bypass arithmétique) | Dead end pour p ≥ 5 | SP9 |
| L11 argument structurel | Non concluant | SP10 L11 |
| Phase 13 Kolmogorov-Baker | Tentative rejetée (self-audit) | phase13 |
| CNN AEGIS Phase 2 | FAIL (hors projet Collatz) | AEGIS |

### 4.4 Gap résiduel (ce qui reste à prouver)
Le gap est dans le cas 3b-ii (n₃ petit, 3 ∉ ⟨2⟩, p ≥ m⁴, m > 130) :
- **Borne actuelle** : n₃ ≥ 0.631q (prouvé)
- **Borne nécessaire** : n₃ ≥ 4q (pour que k_crit < n₃)
- **Gap** : facteur 6.3× entre le besoin et la preuve
- **Résolution conditionnelle** : Konyagin c ≥ 0.36 fermerait le gap
- **Résolution alternative** : borne diophantienne n₃ ≥ 4q (non prouvable actuellement)

---

## 5. PISTES EXPLOITÉES ET NON EXPLOITÉES

### 5.1 Pistes EXPLOITÉES (et leur statut)
| Piste | Phases | Résultat | Verdict |
|-------|--------|----------|---------|
| Entropie de Shannon + Steiner | 10c-10m, 12 | Theorem 1+2 PROUVÉS | SUCCÈS |
| Obstruction algébrique | 11a-11c | Complémentaire, LLL | PARTIEL |
| Moule multidimensionnel | 14 | Visualisation, pas de preuve | EXPLOITÉ |
| Tension interdimensionnelle | 15 | Obstruction analytique | EXPLOITÉ |
| Obstruction analytique | 16 | Parseval cost | SUCCÈS |
| Géométrie de serrure | 17 | Peeling Lemma | SUCCÈS |
| Programme Merle | 18 | Mellin-Fourier bridge | SUCCÈS |
| Radar Mellin | 19 | Square Root Barrier | SUCCÈS |
| CRT hybride | 20a | Complémentaire | EXPLOITÉ |
| Structure algébrique | 20b | Non concluant | IMPASSE |
| Mixing / random walk | 20c | Non concluant | IMPASSE |
| Extension Tao | 20d | Non applicable | IMPASSE |
| Mellin master | 21 | Second moment, voies | EXPLOITÉ |
| CRT amplification | 22 | Bornes lacunaires | EXPLOITÉ |
| Formule verdict + énergie add. | 23a-23f | Barrières, bypass | EXPLOITÉ |
| SP5 investigation (Q) | SP5 | 25 cas vérifiés | SUCCÈS |
| Ghost Fish + Three-mesh | SP6 | 168 primes, 0 fail | SUCCÈS |
| Junction Geology | SP7 | K_MAX=63 | SUCCÈS |
| Fish Nature | SP8 | 247 primes, ρ_max=0.225 | SUCCÈS |
| Extension k→500 | SP9 | 541 primes | SUCCÈS |
| Beatty + Three Distances | SP10 L1-L9 | Régime A+B partiel | SUCCÈS PARTIEL |
| Correction N≤1 → O(ln p/n₃) | SP10 L10 | Bug fix critique | FIX |
| Argument structurel vide | SP10 L11 | Non concluant | IMPASSE |
| Effectivisation quantitative | SP10 L12 | 20/20, c_min=0.3603 | SUCCÈS |
| Cahier des charges spectral | SP10 L13 | 6 lemmes + résultat négatif | MIXTE |

### 5.2 Pistes NON EXPLOITÉES (ouvertes)
| Piste | Description | Difficulté | Potentiel |
|-------|-------------|------------|-----------|
| Effectivisation BGK | Extraire c ≥ 0.36 de la preuve BGK (2006) | Très haute (6-12 mois spécialiste) | FERMERAIT le gap |
| Extension m=130→500 | Tables de Cunningham, vérification étendue | Moyenne (semaines) | Partiel |
| Ostafe-Shparlinski-Voloch (2022) | Weil sums over small subgroups | Incertaine | Non confirmé |
| Approche p-adique Baker/Yu | Formes linéaires en log p-adiques | Haute | Non applicable direct |
| Structure multiplicative d(k) | Montrer que d(k) évite Rég.B structurellement | Très haute | Spéculatif |
| Borne diophantienne n₃ ≥ 4q | Théorie multiplicative des nombres | Très haute | FERMERAIT le gap |
| Caractère de Legendre + coset max | t* = 2^{q-1}-1, lien quadratique | Moyenne | Insight structural |
| Régimes de marché Mersenne | Analogie entre ρ et SNR financier | Basse | Pédagogique |

---

## 6. FICHIERS CLÉS ET STRUCTURE

### 6.1 Structure du dépôt
```
Collatz-Junction-Theorem/
├── paper/
│   ├── preprint_en.tex          ← DOCUMENT PRINCIPAL (LaTeX amsart, 20 pages)
│   ├── preprint_fr.tex          ← Version française (originale)
│   └── preprint.md              ← Version Markdown de référence
├── lean/
│   ├── verified/                ← 73 théorèmes, 0 sorry (Lean 4.15.0)
│   └── skeleton/                ← ~58 théorèmes, 1 sorry (Lean 4.29.0-rc2)
├── scripts/
│   ├── core/                    ← 10 scripts publiés (vérification)
│   └── exploration/             ← ~40 scripts exploratoires (SP5-SP10, L1-L13)
├── research_log/                ← Journal de recherche complet (~30 fichiers)
├── audits/                      ← 4 certifications (V1-V4)
├── docs/plans/                  ← Documents de design
├── README.md                    ← Documentation principale
├── INVENTAIRE.md                ← Catalogue complet
└── META_PROMPT_SESSION.md       ← CE FICHIER
```

### 6.2 Fichiers à modifier lors des mises à jour
Quand tu ajoutes un résultat, mettre à jour **dans cet ordre** :
1. **Research log** : `research_log/sp10_lXX_exploration.tmp.md` (nouveau fichier si nouveau level)
2. **Synthèse formelle** : `research_log/sp10_synthese_formelle.md` (architecture des cas)
3. **Préprint** : `paper/preprint_en.tex` (ajout dans la section appropriée)
4. **README** : `README.md` (tableau des résultats, honest assessment)
5. **INVENTAIRE** : `INVENTAIRE.md` (si nouveaux fichiers)

### 6.3 Scripts d'exploration par level
| Level | Script principal | Résultat |
|-------|-----------------|----------|
| L1-L9 | sp10_level2.py .. sp10_level9_*.py | Beatty, Three Distances, n₃ |
| L10 | sp10_level10_*.py (4 scripts) | Correction N≤1, cascade, effective ρ |
| L11 | sp10_level11_structural.py | Argument structurel (non concluant) |
| L12 | sp10_level12_effectivisation.py | 20/20, c_min=0.3603 |
| L13 | sp10_level13_pieces.py + _analysis.py + _verify_critical.py | 6 lemmes, C(q)~q² |

---

## 7. PROTOCOLE D'ÉCRITURE DU PRÉPRINT

### 7.1 Format
- LaTeX `amsart` 12pt, a4paper
- Packages : amsmath, amssymb, amsthm, mathtools, enumitem, hyperref, booktabs
- Environnements : theorem, proposition, lemma, corollary, definition, conjecture, remark
- Commandes custom : \N, \Z, \Q, \Fp, \Ev, \corrSum, \ord

### 7.2 Compilation
```bash
cd paper/
pdflatex -interaction=nonstopmode preprint_en.tex  # 1ère passe
pdflatex -interaction=nonstopmode preprint_en.tex  # 2ème passe (cross-refs)
```

### 7.3 Règles d'écriture
- **Rigueur** : chaque théorème/lemme a un énoncé formel ET une preuve
- **Cohérence** : numérotation automatique, labels \label{} + \ref{} partout
- **Honnêteté** : les résultats conditionnels sont étiquetés "conditional on..."
- **Complétude** : les hypothèses sont toutes listées explicitement
- **Style** : anglais académique, précis, concis (pas de phrases creuses)
- **Citations** : format \cite{Auteur_Année}, bibliographie en \begin{thebibliography}
- **Anti-régression** : ne JAMAIS supprimer un théorème prouvé sans justification

### 7.4 Sections actuelles du préprint
1. Introduction
2. Steiner's equation and corrSum properties
3. Entropic deficit and nonsurjectivity (Theorem 1)
4. Junction Theorem (Theorem 2)
5. Analytical obstruction (Parseval cost)
6. CRT decomposition
7. Mellin-Fourier bridge
8. Square Root Barrier
9. Verification: N₀(d) = 0 for k ≤ 17
10. Condition (Q) and regime analysis (SP10)
   - 10.1 L12 effectivisation results
   - 10.2 Structural lemmas for Mersenne primes (L13) ← AJOUTÉ
   - 10.3 Open difficulties
11. Three-mesh net and ghost fish (SP6)
12. Lean 4 formalization
13. Open conjectures

---

## 8. PROTOCOLE GIT ET COMMIT

### 8.1 Convention de commit
```
<type>: <description courte>

<corps détaillé si nécessaire>

Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>
```

Types utilisés : `feat`, `fix`, `docs`, `refactor`

### 8.2 Historique récent
```
d711846 feat: SP10 L13 — structural lemmas for Mersenne primes + spectral analysis
2e060d2 docs: update preprint with L12 effectivisation results
55d0187 feat: SP10 L12 — quantitative effectivisation of Regime B gap
1920527 feat: SP10 L11 — structural argument for empty Regime B (non-conclusive)
dedf6ad fix: SP10 L10 — correct SP10b theorem (N≤1 was false for small n₃)
a393db6 feat: SP10 regime analysis in preprint, README, and INVENTAIRE
```

### 8.3 Protocole push
1. `git status` — vérifier les fichiers modifiés
2. `git diff --cached --stat` — vérifier le contenu
3. `git commit -m "..."` — message selon convention
4. `git push` — pousser sur origin/main
5. Vérifier le CI après push

---

## 9. DÉFINITIONS MATHÉMATIQUES CLÉS

### 9.1 Notations
- θ = log₂(3) ≈ 1.5849625007
- γ = 1 - h(1/θ) ≈ 0.0500 (déficit entropique)
- d(k) = 2^{⌈kθ⌉} - 3^k (le "résidu")
- m = ord_p(2) (ordre multiplicatif de 2 mod p)
- q = (p-1)/m (indice du sous-groupe ⟨2⟩)
- n₃ = min{j ≥ 1 : 3^j ∈ ⟨2⟩ mod p}
- ρ(p) = max_{t≠0} |Σ_{h∈⟨2⟩} e(th/p)| / m (somme expo normalisée)
- S_t = Σ_{j=0}^{m-1} e(t·2^j/p) (somme expo sur ⟨2⟩)
- k_crit(p) = 17 + ln((p-1)/0.041) / |ln(ρ(p))|
- E(H) = |{(a,b,c,d) ∈ H⁴ : a+b ≡ c+d}| (énergie additive)
- C(q) = max|S_t|⁴ / (Σ|S_t|⁴/(q-1)) (ratio de concentration spectrale)

### 9.2 Condition (Q)
Pour tout k ≥ 18, pour tout premier p | d(k) :
**(p-1) · ρ(p)^{k-17} < 0.041**

Si (Q) est satisfaite : pas de cycle de longueur k.

### 9.3 Architecture des cas pour (Q)
```
CAS 1 : k ≤ 68             → CLOS (D17, vérification directe)
CAS 2 : k ≥ 69, p < m⁴    → CLOS (Di Benedetto 2020 + Phase I CI)
CAS 3a : p ≥ m⁴, générique → CLOS (SP10a, k_crit < n₃)
CAS 3b-i : n₃ > 3m·ln p   → CLOS (SP10b-i)
CAS 3b-ii : n₃ petit       → PARTIELLEMENT CLOS (m≤130: L12, Mersenne k≤0.63q: L13)
                               OUVERT pour m>130 (gap 6.3×, conditionnel c≥0.36 Konyagin)
CAS 3c : 3∈⟨2⟩, p≥m⁴      → HEURISTIQUEMENT VIDE (0/427 cas)
```

---

## 10. RÉSULTATS L13 EN DÉTAIL (dernière exploration)

### 10.1 Les 6 lemmes prouvés (P1-P6)
- **(P1)** E(⟨2⟩) = 2q² - q pour tout Mersenne M_q [exact, cross-vérifié FFT]
- **(P2)** |⟨2⟩+⟨2⟩| = q(q+1)/2 pour tout Mersenne M_q [exact]
- **(P3)** n₃(M_q) ≥ ⌈q/θ⌉ ≈ 0.631q [preuve structurelle : 3^k < M_q pour k < ⌈q/θ⌉]
- **(P4)** M_q ∤ d(k) pour k ≤ ⌊(q-1)/θ⌋ [barrière de taille]
- **(P5)** Σ|S_t|⁴ = p·(2q²-q) [identité de Parseval 4ème moment]
- **(P6)** Pour q ≥ 110 : n₃ > 69 [corollaire de P3]

### 10.2 Résultat négatif majeur
**C(q) = max|S_t|⁴ / avg|S_t|⁴ ~ q²/2** (croissance quadratique)
- ρ(M_q) → 2^{-1/4} ≈ 0.8409 (conjecture forte, convergence super-polynomiale)
- 2ρ⁴ approche 1 : 0.099, 0.170, 0.292, 0.678, 0.876, 0.957
- **CONSÉQUENCE** : Les méthodes par moments (4ème, 6ème, tout k) ne PEUVENT PAS prouver ρ → 0

### 10.3 Divisibilités réelles découvertes
| q | p=M_q | k | M_q\|d(k) | dans danger? | marge |
|---|-------|---|-----------|-------------|-------|
| 5 | 31 | 48, 54 | OUI | NON | immense |
| 7 | 127 | 90, 180 | OUI | NON | immense |
| 17 | 131071 | 7710 | OUI | NON | 10^{683} |

### 10.4 Coset maximale
Pour tout Mersenne testé : t* = 2^{q-1} - 1 (la moitié de p), avec paire conjuguée.
Lié au caractère quadratique de ⟨2⟩.

---

## 11. GESTION DE LA MÉMOIRE ET DES TODO

### 11.1 Todo list
Utiliser `TodoWrite` pour tracker le travail en cours :
- Créer une todo par étape identifiable
- Marquer `in_progress` le step courant (un seul à la fois)
- Marquer `completed` dès que terminé
- Formats : `content` (impératif) + `activeForm` (gérondif)

### 11.2 Research log
Chaque exploration crée un fichier `research_log/sp10_lXX_exploration.tmp.md` contenant :
- Objectif de l'exploration
- Protocole (anti-hallucination, anti-régression)
- Phases numérotées (Phase 1, 2, ...)
- Résultats numériques avec tableaux
- Conclusion avec impact sur le score

### 11.3 Synthèse formelle
Le fichier `research_log/sp10_synthese_formelle.md` est le **document de référence formel** :
- Énoncé de (Q)
- Décomposition en régimes
- Propositions/lemmes avec preuves
- Données empiriques
- Architecture de la preuve
- Conclusion avec score

### 11.4 Écriture au fil de l'eau
- Documenter les résultats AU FUR ET À MESURE (pas à la fin)
- Chaque script exécuté → résultats consignés dans le research log
- Chaque résultat prouvé → ajouté au préprint immédiatement
- Cohérence préprint ↔ synthèse ↔ README vérifiée à chaque commit

---

## 12. ENVIRONNEMENT TECHNIQUE

### 12.1 Machine
- MacBook M1 Pro 16 Go
- macOS Darwin 25.3.0
- Python 3.x (via miniforge3)
- LaTeX (texlive 2025)
- Lean 4.15.0 (verified/) + 4.29.0-rc2 (skeleton/)

### 12.2 Dépendances Python
- `math`, `cmath` (standard)
- `mpmath` (vérification haute précision, 50+ digits)
- `numpy`, `scipy` (FFT, algèbre linéaire)
- `sympy` (calcul symbolique, factorisation)

### 12.3 NE PAS TOUCHER
- `/Users/ericmerle/Documents/Projet_Collatz/` (agents actifs, autre projet)
- Environnement conda `collatz-jepa` (ne pas modifier)

---

## 13. PROCHAINES ÉTAPES SUGGÉRÉES

Par ordre de priorité et faisabilité :

### 13.1 Court terme (1-2 sessions)
- [ ] Extension vérification m=130→200 (tables de Cunningham)
- [ ] Analyse SHAP-like du caractère de Legendre + coset max t*
- [ ] Lean : formaliser les lemmes L13 (P1-P6) dans skeleton/

### 13.2 Moyen terme (1-2 semaines)
- [ ] Lecture détaillée Ostafe-Shparlinski-Voloch (2022)
- [ ] Tentative d'extraction partielle de la constante BGK
- [ ] Soumission arXiv du préprint (après review interne)

### 13.3 Long terme (recherche ouverte)
- [ ] Effectivisation BGK complète (c ≥ 0.36)
- [ ] Borne diophantienne n₃ ≥ 4q
- [ ] Nouvelle borne spectrale pour sous-groupes |H| ≤ p^{1/4}

---

## 14. RÉFÉRENCES BIBLIOGRAPHIQUES CLÉS

1. **Steiner (1977)** — Équation fondamentale des cycles Collatz
2. **Simons-de Weger (2005)** — Pas de cycle pour k ≤ 68
3. **Di Benedetto et al. (2020)** — Sommes expo sur petits sous-groupes (EXPLICITE, Régime A)
4. **Konyagin (2003)** — ρ ≤ exp(-c·(log p)^{1/3}), c > 0 NON-EXPLICITE
5. **BGK (2006)** — Sum-product, Bourgain-Glibichuk-Konyagin
6. **Sós (1958)** — Three Distances Theorem (conjecture de Steinhaus)
7. **Baker (1966) / Matveev (2000)** — Formes linéaires en logarithmes
8. **Yu (2007)** — Baker p-adique
9. **Tao (2022)** — "Almost all orbits attain almost bounded values"
10. **Zudilin (2014)** — μ(log₂(3)) ≤ 5.125 (indice d'irrationalité)
11. **Garaev (2007)** — Sum-product pour grands sous-groupes
12. **Hooley (1967)** — Conjecture d'Artin sous GRH
13. **Kowalski (2024)** — Exposition du théorème BGK (arXiv:2401.04756)
14. **Shparlinski** — Open problems on exponential and character sums (UNSW)

---

## 15. DIAGNOSTIC RAPIDE POUR REPRISE

### Questions-clés pour orienter le travail :
1. **Où en est-on ?** → Score 4.85/5. Gap 3b-ii (facteur 6.3×) et 3c (heuristique).
2. **Qu'est-ce qui a échoué ?** → Moments (C(q)~q²), Baker, ABC, GRH+Artin, L11 structurel.
3. **Qu'est-ce qui marche ?** → Beatty counting, Di Benedetto, vérification numérique, barrière taille.
4. **Quel est le chemin vers 5.00/5 ?** → Konyagin c ≥ 0.36 OU n₃ ≥ 4q OU nouveau résultat spectral.
5. **Le préprint est-il à jour ?** → OUI (commit d711846, 20 pages, compilé sans erreur).

### Commande de vérification rapide :
```bash
cd /Users/ericmerle/Documents/Collatz-Junction-Theorem
git log --oneline -5
cd paper && pdflatex -interaction=nonstopmode preprint_en.tex 2>&1 | tail -5
```

---

*Ce méta-prompt a été généré le 3 mars 2026 à partir de l'historique complet du projet (phases 10c-23f, SP5-SP10, L1-L13). Il contient toutes les informations nécessaires pour reprendre le travail sans perte de contexte.*
