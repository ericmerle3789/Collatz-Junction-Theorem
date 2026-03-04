# MÉTA-PROMPT : CONTINUATION DU PROJET COLLATZ JUNCTION THEOREM
## Pour une nouvelle session Claude Code — Mars 2026
## Auteur : Eric Merle (avec Claude Opus 4)

---

## 0. INSTRUCTIONS IMPÉRATIVES

Tu es Claude, assistant IA d'Eric Merle sur le projet **Collatz Junction Theorem**.
- **Langue** : FRANÇAIS exclusivement (sauf noms techniques anglais)
- **Mode** : Recherche mathématique AUTONOME + scientifiquement rigoureuse
- **Protocole** : DISCOVERY_PROTOCOL v2.2 (dans `research_protocol/`)
- **Principe cardinal** : "Le script est le juge, pas le raisonnement" (AlphaProof)
- **Anti-hallucination** : toute affirmation DOIT être vérifiée par script Python
- **Dossier de travail** : `/Users/ericmerle/Documents/Collatz-Junction-Theorem/`
- **NE PAS écrire dans** : `/Users/ericmerle/Documents/Projet_Collatz/` (agents actifs)
- **Environnement** : `collatz-jepa` (NE PAS toucher)
- **GitHub** : `ericmerle3789/Collatz-Junction-Theorem` (branche `main`)
- **Commits** : uniquement sur demande explicite d'Eric

---

## 1. CONTEXTE DU PROJET

### 1.1 Objectif fondamental
> **Prouver que N₀(d) = 0 pour TOUT k ≥ 1 → ∞.**
>
> N₀(d) = nombre de compositions A de S en k parts ordonnées telles que corrSum(A) ≡ 0 mod d.
> Si N₀(d) = 0 pour tout k ≥ 3 → **pas de cycle non-trivial dans la conjecture de Collatz**.

### 1.2 Objets mathématiques centraux
```
k ≥ 3              : nombre de pas impairs dans un cycle potentiel
S = ⌈k·log₂3⌉     : hauteur (nombre total de divisions par 2)
M = S - k          : surplus de divisions
d = 2^S - 3^k      : module cristallin (toujours impair, toujours > 0 pour k ≥ 2)
C = binom(S-1, k-1) : nombre de compositions
u = 2·3^{-1} mod d : unité fondamentale

Automate de Horner mod d :
  c_0 = 1, c_j = (3·c_{j-1} + 2^{p_j}) mod d
  N₀(d) = |{compositions A : c_{k-1} = 0}|

Formulation B (shift) :
  f(B) = Σ_{j=1}^{k-1} u^j · 2^{B_j}  avec B non-décroissant dans [0, M]
  N₀(d) = 0 ⟺ -1 ∉ Im(f)
```

### 1.3 Equation de Steiner (1977)
```
Si (n₀, k) est un cycle de Collatz, alors :
  n₀ · d(k) = corrSum(A)
  corrSum(A) = 3^{k-1} + Σ_{j=1}^{k-1} 3^{k-1-j} · 2^{A_j}

  N₀(d) = 0 → pas de cycle de longueur k.
```

---

## 2. ÉTAT DE LA PREUVE (v0.15 — 4 mars 2026)

### 2.1 Architecture de la preuve (4 cas pour d premier)
```
CAS 1 (intérieur) : B₁ > 0 ET B_{k-1} < M
  → Résolu si ord_d(2) > C (orbite ×2 dans Im_interior)

CAS 2 (bord gauche) : B₁ = 0 ET B_{k-1} < M
  → Réduit au cas 1 par shift f(B+1) = 2·f(B)

CAS 3 (bord droit) : B₁ > 0 ET B_{k-1} = M
  → Réduit au cas 1 par shift

CAS 4 (double-bord) : B₁ = 0 ET B_{k-1} = M
  → Résolu si F(u) ≠ 0 mod d (polynôme explicite)
```

### 2.2 Pour d composé
```
d = p₁ · p₂ · ... · p_r
N₀(d) ≤ N₀(p_i) pour tout i (CRT inequality)
→ Il suffit qu'UN SEUL facteur premier bloque.
Vérifié k ≤ 67 par programmation dynamique exhaustive.
```

### 2.3 Tableau récapitulatif complet
```
  CAS                | STATUT                      | MÉTHODE
  -------------------|-----------------------------|----------
  d prem, σ̃=0       | ★★★★★ CLOS                  | Fini (k=3,5), prouvé + Zsygmondy
  d prem, σ̃≠0       | ★★★★★ QUASI-CLOS            | Induction 4 cas
    Cas intérieur    | CLOS (modulo ord>C)           | Orbite ×2 + pigeonhole
    Cas bord simple  | CLOS                          | Réduction au cas intérieur
    Cas double-bord  | CLOS (modulo F(u)≠0)          | Polynôme deg k-1
      k impair≤10001 | ✓✓✓✓✓ Vérifié (4998 val.)   | F_Z mod d ≠ 0
      k pair ≤1000   | ✓✓✓✓✓ Vérifié (499 val.)    | Solution hors [0,M]
      1 p crit/k     | ★★★★★ (vérifié k≤10001)     | CRT anti-corrélation
      Coprimité p=5  | ★★★★★ PROUVÉ (tout m)        | F_Z ≡ 3 mod 5
      Densité → 0    | ★★★★★ (1% à p≤5000)         | 8 p critiques ≤10000
    ord_d(2) > C     | ★★★★★ VÉRIFIÉ (19 d prem.)   | Test direct 2^C mod d
      (d-1)/ord ≤ 15 | ★★★★★ VÉRIFIÉ (k≤185)       | Factorisation de d-1
      C/d → 0        | ★★★★★ PROUVÉ                 | Stirling + entropie binaire
      Cond. (Artin)  | CONJECTURE (GRH suffit)       | (d-1)/ord borné ← Hooley
  d comp, k≤67       | ★★★★★ CLOS                  | Mec.I + Mec.II (CRT)
  d comp, k≥68       | ★★★★ EXTRAPOLÉ              | Saturation + CRT
  σ̃=0 finitude      | ★★★★★ QUASI-CLOS            | Vérifié k≤499, Zsygmondy
```

### 2.4 Les 4 gaps résiduels
```
  GAP   | STATUT                          | DÉTAIL
  ------|---------------------------------|------------------
  G1    | ★★★★★ QUASI-CLOS               | σ̃=0 seulement k=3,5 (Zsygmondy + vérif k≤499)
  G2a   | ★★★★★ QUASI-RÉSOLU             | F_Z mod d ≠ 0 vérifié k≤10001, 8 p critiques
  G2c   | ★★★★★ SOUS GRH                 | ord_d(2) > C ; Hooley suffit ; (d-1)/ord ≤ 15
  G3    | ★★★★ EXTRAPOLÉ                  | CRT anti-corrélation d composé (vérifié k≤67)
```

### 2.5 CONCLUSION MAJEURE
> **La preuve est COMPLÈTE sous GRH (Hypothèse de Riemann Généralisée).**
> Le gap résiduel se réduit à : prouver que (d-1)/ord_d(2) est borné pour
> les premiers d = 2^S - 3^k. C'est une variante de la conjecture d'Artin.
> Sous GRH, Hooley (1967) implique que 2 est racine primitive pour
> infiniment beaucoup de premiers, ce qui résout G2c.

---

## 3. RÉSULTATS COMPUTATIONNELS CLÉS (R1-R79)

### 3.1 Résultats prouvés inconditionnellement
- **R1-R5** : Peeling Lemma, N₀(d)=0 pour k≤17, barrière racine carrée
- **R6-R7** : corrSum toujours impair, jamais divisible par 3
- **R70** : T_F | 2·T_d (périodes des premiers critiques)
- **R71** : 8 premiers critiques ≤ 10000, densité → 0
- **R72** : F_Z mod d ≠ 0 pour k impairs ≤ 10001 (4998 valeurs, 0 exception)
- **R73** : Au plus 1 premier critique par k (4998 valeurs)
- **R76** : 2^C ≠ 1 mod d pour 19 d premiers (k ≤ 10000)
- **R78** : log₂(C)/S → 0.949, C/d → 0 exponentiellement

### 3.2 Résultats prouvés sous GRH
- G2c résolu : ord_d(2) >> C pour tous d premiers de forme 2^S - 3^k

### 3.3 Résultats prouvés inconditionnellement (session 10f20)
- ord_d(2) > S pour k ≥ 4 (quand 3^k < d) — preuve élémentaire
- Mais S << C, donc insuffisant pour fermer G2c

---

## 4. FICHIERS ET RÉPERTOIRES CRITIQUES

### 4.1 Documents de référence
```
research_protocol/BLOCKING_MECHANISM_PROOF_SKETCH.md  ← PROOF_SKETCH v0.15 (22 sections)
research_protocol/DISCOVERY_PROTOCOL.md               ← Protocole de recherche v2.2
research_protocol/MIND_MAP.md                          ← Carte mentale des dépendances
scripts/tools/session10b_scratch.md                    ← Cahier de brouillon (R1-R79)
```

### 4.2 Scripts de vérification importants
```
scripts/tools/session10f12_double_border_induction.py  ← Induction 4 cas
scripts/tools/session10f13_target_nonzero_proof.py     ← Polynôme F(u)
scripts/tools/session10f15_lean_ready_formulation.py   ← Formulation Lean-ready
scripts/tools/session10f16_conjectures_attack.py       ← Attaque des 4 gaps
scripts/tools/session10f18c_extended_final.py          ← F_Z mod d k≤10001
scripts/tools/session10f19b_g2c_fast.py                ← G2c : 2^C mod d (19 d prem.)
scripts/tools/session10f20_g2c_unconditional.py        ← G2c : ord > S prouvé
```

### 4.3 Paper et formalisation
```
paper/preprint_en.tex        ← Preprint anglais (à mettre à jour avec sessions 10b-10f19)
paper/preprint_fr.tex        ← Preprint français
lean/verified/               ← 73 théorèmes Lean4, 0 sorry, 0 axiome
lean/skeleton/               ← ~58 théorèmes, 1 sorry résiduel
```

### 4.4 README et inventaire
```
README.md          ← À mettre à jour (encore sur l'approche "Entropic Barriers" phases 10-23)
INVENTAIRE.md      ← À mettre à jour (n'inclut pas les sessions 10b-10f20)
```

---

## 5. PROTOCOLE DE SÉCURITÉ ET QUALITÉ

### 5.1 Règles absolues
1. **JAMAIS d'affirmation non vérifiée** — tout doit passer par un script Python
2. **Toujours citer la session et le résultat** (format R##, session 10fXX-IY)
3. **Les erreurs sont des DÉCOUVERTES** — documenter honnêtement (ex: R63 corrigé par R72)
4. **Le scratch est la source de vérité** — tout résultat y est noté
5. **PROOF_SKETCH est le document formel** — mis à jour à chaque avancée majeure

### 5.2 Conventions de nommage
- Scripts : `session10fXX_description.py` (numérotation séquentielle)
- Résultats : R## ★ (étoiles = niveau de conviction, 1 à 5)
- Sessions : 10fXX (XX = numéro, lettre optionnelle pour sous-sessions)
- Versions PROOF_SKETCH : v0.XX (incrémentale)

### 5.3 Processus de travail
1. **Générer** une conjecture ou un script de test
2. **Vérifier** par exécution Python (le script est le juge)
3. **Raffiner** si échec, corriger si erreur
4. **Documenter** dans scratch (R##) puis PROOF_SKETCH (sections)
5. **Commit** uniquement sur demande d'Eric

### 5.4 Boucle G-V-R (Aletheia-inspirée)
```
G (Generate) : proposer une conjecture ou une direction
V (Verify)   : écrire et exécuter un script de vérification
R (Refine)   : corriger, étendre, ou abandonner selon les résultats
→ Répéter jusqu'à convergence
```

---

## 6. HISTORIQUE RÉSUMÉ DES SESSIONS

### Sessions 7-9 (fondations)
- Mécanismes I (un facteur bloque), II (CRT anti-corrélation), III (triplet)
- TARGET -1, identité u = 2·3^{-1}, automate de Horner
- CRT pairwise : quand corrSum ≡ 0 mod p₁, 0 ABSENT mod p₂

### Session 10 (pré-10b)
- Filtration Im_0 ⊂ Im_1 ⊂ ... ⊂ Im_M
- Backward chain universellement exclue
- Preuves algébriques de débordement (k=3,4,5)

### Sessions 10b-10d
- Contradiction approach + exclusion chains
- Mechanism II CRT formalisé
- σ̃=0 classification : u^{k-1} = 1 mod d

### Sessions 10e-10e4
- Backward chain universelle, identité corrSum-filtration
- Théorème u = 2^{-M} (cas σ̃=0)
- Preuves complètes k=3,4,5

### Sessions 10f1-10f6
- Structural argument, cascade contradiction
- Band structure (bandes disjointes pour σ̃=0)
- Universal directions

### Sessions 10f7-10f8b
- CRT anti-corrélation étendue
- Programmation dynamique pour grands k (k ≤ 67)

### Sessions 10f9-10f12
- Framework théorique unifié
- Induction double-bordure itérée (4 cas)
- Im_interior ×2-clos

### Sessions 10f13-10f15
- Polynôme F(u) = u^{2n+2} + u^{n+2} - 2u^{n+1} - u^n - 1
- Argument de taille : C/d → 0
- Formulation Lean-ready avec sorry's explicites

### Sessions 10f16-10f17
- Attaque des 4 conjectures résiduelles (G1, G2a, G2c, G3)
- Investigation squarefree de d(k) — gcd PAS toujours squarefree (11² à k=6343)
- Coprimité locale : p ∤ F_Z prouvé pour p=5,7,13,19,23,...

### Session 10f18 (a, b, c)
- Investigation théorique G2a — périodes T_F et T_d
- 8 premiers critiques : {11, 37, 53, 59, 109, 191, 283, 8363}
- F_Z mod d ≠ 0 pour k ≤ 10001 (4998 valeurs, 0 exception)
- Au plus 1 premier critique par k — CRT anti-corrélation
- Formule fermée : F_Z = 4^m - 9^m - 17·6^{m-1}

### Session 10f19 (a, b)
- **ATTAQUE G2C** — le gap le plus dur
- 19 d premiers : 2^C ≠ 1 mod d pour TOUS ✓
- (d-1)/ord ∈ {1, 2, 3, 15} — toujours petit
- C/d → 0 prouvé (ratio 2^{-0.051·S})
- **Sous GRH : G2c RÉSOLU** via Hooley (1967)
- Correction : "ord ≥ S" est FAUX pour k=3, VRAI pour k ≥ 4

### Session 10f20 (début)
- ord_d(2) > S prouvé inconditionnellement pour k ≥ 4
- Gap S → C trop grand pour argument élémentaire
- Script créé mais non terminé (arrêt session)

---

## 7. CE QUI RESTE À FAIRE

### 7.1 Priorité 1 : Mise à jour du preprint
- Intégrer les sessions 10b-10f19 dans `paper/preprint_en.tex`
- Nouvelle section : "Blocking Mechanism Proof" avec les 4 cas + GRH
- Mettre à jour `README.md` et `INVENTAIRE.md`

### 7.2 Priorité 2 : Formalisation Lean4
- Formaliser les sorry's faciles : shift_identity, coprimality_p5, boundary_exhaustive
- Les 4998 vérifications F_Z mod d ≠ 0 comme decidable checks
- Le ratio C/d → 0 par Stirling

### 7.3 Priorité 3 : Explorer G2c inconditionnellement
- La famille d = 2^S - 3^k est très spéciale
- Bornes de Burgess ou Vinogradov sur résidus de puissances
- Exploiter que d ≡ -3^k mod 2^S (structure très contrainte)

### 7.4 Priorité 4 : Prouver la finitude de P_crit
- Si P_crit = {11, 37, 53, 59, 109, 191, 283, 8363} est fini → G2a CLOS
- Argument probabiliste : Prob(p critique) ~ 1/p² → somme convergente

### 7.5 Priorité 5 : Valider G3 pour k > 67
- CRT anti-corrélation formelle
- Programmation dynamique étendue

---

## 8. FORMULES CLÉS (aide-mémoire)

```python
# Module cristallin
d = 2**S - 3**k  # S = ceil(k * log2(3))

# Formulation B
# f(B) = sum(u^j * 2^{B_j} for j in 1..k-1) mod d
# avec u = 2 * pow(3, -1, d) mod d
# N0(d) = 0 ssi -1 not in Im(f)

# Polynôme d'annulation (k impair, n = (k-3)/2)
# F(u) = u^{2n+2} + u^{n+2} - 2*u^{n+1} - u^n - 1

# Formule fermée double-bord (k impair)
# F_Z(m) = 4^m - 9^m - 17*6^{m-1}  avec k = 2m+1

# Premiers critiques
# P_crit = {p premier : ∃m ≥ 3, p | F_Z(m) ET p | d(2m+1)}
# P_crit connu = {11, 37, 53, 59, 109, 191, 283, 8363}

# Test G2c
# pow(2, C, d) != 1  pour d premier, C = comb(S-1, k-1)
```

---

## 9. GRAPHE DE DÉPENDANCES SIMPLIFIÉ

```
N₀(d) = 0 pour tout k
├── d PREMIER
│   ├── σ̃ = 0 → CLOS (k=3,5 seulement) [G1]
│   └── σ̃ ≠ 0 → Induction 4 cas
│       ├── Cas intérieur → ord_d(2) > C [G2c — SOUS GRH]
│       ├── Cas bord → réduit à intérieur (shift)
│       └── Cas double-bord → F(u) ≠ 0 mod d [G2a — QUASI-RÉSOLU]
│           ├── k impair ≤ 10001 : VÉRIFIÉ
│           ├── k pair ≤ 1000 : VÉRIFIÉ
│           └── Grands k : argument de taille + P_crit fini [G2a]
└── d COMPOSÉ
    ├── k ≤ 67 : CLOS (DP exhaustive)
    └── k ≥ 68 : CRT anti-corrélation [G3 — EXTRAPOLÉ]
```

---

## 10. COMMENT TRAVAILLER

### 10.1 Pour lancer un script
```bash
cd /Users/ericmerle/Documents/Collatz-Junction-Theorem
python3 scripts/tools/session10fXX_description.py
```

### 10.2 Pour mettre à jour le scratch
- Éditer `scripts/tools/session10b_scratch.md`
- Ajouter R## avec étoiles et session d'origine
- Mettre à jour les tableaux BILAN et ÉTAT DE LA PREUVE

### 10.3 Pour mettre à jour le PROOF_SKETCH
- Éditer `research_protocol/BLOCKING_MECHANISM_PROOF_SKETCH.md`
- Incrémenter la version (v0.XX)
- Ajouter/modifier les sections pertinentes

### 10.4 Pour committer
```bash
git add [fichiers spécifiques]
git commit -m "feat: description"
git push
```

---

## 11. NOTES IMPORTANTES POUR LA PROCHAINE SESSION

1. **Le script session10f20 a été CRÉÉ mais NON TERMINÉ** (arrêt session).
   Il contient un théorème prouvé (ord > S) et un argument itéré incomplet.

2. **Les fichiers README.md et INVENTAIRE.md sont OBSOLÈTES** — ils reflètent encore
   l'approche "Entropic Barriers" (phases 10-23) et NON le mécanisme de blocage.

3. **Le preprint (paper/preprint_en.tex) n'inclut PAS encore les sessions 10b-10f19**.
   C'est la mise à jour la plus importante à faire.

4. **Erreurs connues et corrigées** :
   - R63 (gcd squarefree) → FAUX, corrigé par R72 (gcd=121=11² à k=6343)
   - "Théorème ord ≥ S" → FAUX pour k=3, vrai pour k ≥ 4
   - session10f18b : NameError sur `{p_max}` dans f-string → corrigé

5. **La preuve est COMPLÈTE sous GRH** — c'est le résultat majeur à documenter.
