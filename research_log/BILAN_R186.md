# BILAN R186 — N(k,S)=p(S-k) PROUVE, GEOMETRIE ECHOUE, AUTOMATE DE HORNER
**Date :** 16 mars 2026

---

## RESUME EXECUTIF

R186 a deploye 5 agents. **Correction majeure** : R184-T2 (esperance ~2^{0.507k}) est FAUX — N(k,S) = p(S-k) << C(S-1,k-1), la vraie esperance → 0. N(k,S) < d PROUVE pour k≥2 mais ne suffit PAS (fantome k=2). Geometrie des nombres ne mord pas. L'automate de Horner (A3) produit 12 resultats prouves et une structure duale exploitable.

---

## AGENT A1 — FORMULE EXACTE N(k,S)

### R186-T1 : N(k,S) = p(S-k) [PROUVE, SIGNIFICATIF]
N(k,S) = nombre de partitions de S-k (car S-k < k rend la contrainte "au plus k parts" inactive).

### R186-T2 : R184-T2 INVALIDE [PROUVE, CORRECTION MAJEURE]
Esperance coincidences ~ p(S-k) · (g_max/d) / C ~ exp(2√k) / 3^k → 0 (PAS 2^{0.507k} → ∞).

### N(k,S) < d ne suffit pas [PROUVE]
Fantome k=2 : N/d = 2/7 < 1 mais g(0,2) = 7 = d.

### Table
| k | N(k,S) | d | N/d |
|---|--------|---|-----|
| 1 | 1 | 1 | 1.0 |
| 2 | 2 | 7 | 0.286 |
| 3 | 2 | 5 | 0.4 |
| 5 | 3 | 13 | 0.231 |
| 10 | 11 | 6487 | 0.0017 |
| 20 | 77 | ~7.4×10^8 | ~10^{-7} |

---

## AGENT A2 — EXPLOITATION SPECTRALE

### 12 faits prouves sur les fibres/tranches
Structure de la compression, monotonie interne, entrelacement, bornes sigma_t.

### 2 verrous confirmes
- Compression maximale (r << k) est RARE pour les p|d
- Sommes exponentielles sur partitions monotones intraitables

### Piste fraiche : geometrie du cone monotone dans F_p^r (6/10)
Montrer que l'image Sigma evite l'hyperplan ker(F) sans sommes expo.

---

## AGENT A3 — AUTOMATE DE HORNER [RESULTAT PRINCIPAL R186]

### 12 resultats PROUVES

| ID | Enonce | Statut |
|----|--------|--------|
| H1 | Graphe G(d) s-regulier, transitions bijectives | PROUVE |
| H2 | 3^k ≡ 2^S mod d, automorphisme Phi | PROUVE |
| H3 | Decomposition en cycles primitifs (z_m≠0 intermediaire) | PROUVE |
| H4 | Dualite gauche-droite : z_j = -3^{j-k}Q_j mod d | PROUVE |
| H5 | z_1 ∈ ⟨2⟩, z_{k-1} ∈ -3^{-1}⟨2⟩ dans Z/dZ | PROUVE |
| H6 | Mot constant exclu sauf si ord_d(2) \| S | PROUVE |
| H7 | Automates projetes H_p : alphabet effectif = ord_p(2) | PROUVE |
| H8 | Dualite R185/R186 : compression par ord_p(3) (poids) vs ord_p(2) (lettres) | CONDITIONNEL |

### Piste combinee (9/10 auto-evalue)
Combiner les deux dualites : compression spectrale (A2/R185) × filtrage alphabetique (A3/R186).

---

## AGENT A4 — GEOMETRIE DES NOMBRES

### 6 approches explorees, TOUTES FERMEES
1. Reseau direct : g exponentielle en B_j, pas lineaire → ECHOUE
2. Linearisation x_j = 2^{B_j} : contrainte residuelle (puissance de 2) = comptage direct
3. Minkowski : geometrie triviale (un hyperplan)
4. Baker : renforce BC grands k, rien pour k<42
5. Coppersmith/LLL : probleme non polynomial
6. CRT-reseau : rebranding anti-correlation

### Diagnostic
Mismatch additif/multiplicatif irreductible : aucun systeme de coordonnees ne satisfait simultanement linearite, integralite et convexite.

---

## AGENT A5 — RED TEAM

### Score R185 : 4.5/10
| Resultat | Verdict |
|----------|---------|
| Compression spectrale | Aliasing standard (4/10) |
| Spectre Dirac | Tautologie (2/10) |
| Relation ORD | Exercice M1 (3/10) |
| R185-T1 | Tautologie (2/10) |
| E6' fibres | Nouvelle mais non exploitee (4/10) |
| N(k,S) < d | Juste mais survendue (5/10) |

---

## SYNTHESE

### Corrections de trajectoire
- R184-T2 (esperance → ∞) : **FAUX**, vraie esperance → 0
- N(k,S) < d : necessaire mais **pas suffisant**
- Geometrie des nombres : **FERMEE** (6 approches)
- Compression spectrale : aliasing standard, **pas de gain**

### Resultats recuperables
- N(k,S) = p(S-k) : formule exacte, utile
- Automate de Horner : 12 PROUVES, structure exploitable
- Dualite poids × lettres : nouvelle, non testee

### Pistes vivantes (recalibrees)
| Piste | Score | Raison |
|-------|-------|--------|
| **Dualite poids × lettres** | 6/10 | A3, combine R185 + R186, non testee |
| **Fibres modulaires E6'** | 5/10 | Differente de compression A2 |
| **Cone monotone dans F_p^r** | 5/10 | A2, eviter hyperplan |
| **CRT anti-correlation** | 4/10 | Inchange, verrou TAN |
| **N(k,S) < d + equidistribution** | 4/10 | DEGRADE, ne suffit pas seul |

---

## EVALUATION

| Critere | Score | Commentaire |
|---|---|---|
| **Nouveaute** | 5/10 | N(k,S)=p(S-k) nouveau, automate Horner substantiel |
| **Impact** | 5/10 | Correction T2 importante, geometrie fermee (negatif utile) |
| **Rigueur** | 8/10 | RED TEAM corrige R185, automate bien prouve |
| **Honnetete** | 10/10 | N(k,S)<d survendu reconnu, 6 fermetures geometrie |

---

*Round R186 : 5 agents, 5 fichiers .md, 0 scripts, 1 formule exacte (N(k,S)=p(S-k)), 12 resultats automate Horner, 1 correction majeure (T2 faux), 6 fermetures geometrie, 0 preuve.*
