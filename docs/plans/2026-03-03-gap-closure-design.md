# Design : Programme de Fermeture du Gap Collatz
# Date : 3 mars 2026
# Score initial : 4.85/5 — Objectif : 5.00/5

---

## Diagnostic

Le gap réside dans le Cas 3b-ii de la Condition (Q) :
- n₃ petit (2 ≤ n₃ ≤ 3m·ln(p)), 3 ∉ ⟨2⟩, p ≥ m⁴, m > 130
- Facteur manquant : 6.3× entre n₃_needed (4q) et n₃_proved (0.631q)
- Approche spectrale épuisée (ρ → 0.84 pour Mersenne, L13)
- 0/427 cas observés en Régime B (empiriquement vide)

## Programme séquentiel A → B → C

### Phase A — Fondations computationnelles

**A1** : Vérification exhaustive k = 18..25
- Calculer N₀(d(k)) par énumération de C(S,k) compositions
- Mesurer E₄(H), |G(u)|, β(p) pour calibrer Phase B
- Critère : N₀(d) = 0 pour tout k testé

**A2** : Extension Régime B m = 131..500
- Factoriser 2^m - 1 via tables/trial division
- Pour chaque premier p en Régime B : calculer ρ, k_crit, vérifier (Q)
- Critère : 100% PASS, c_min mis à jour

### Phase B — Mélange inconditionnel

**B1** : Borner E₈(H) mod p
- Généraliser Lemme 9 (solutions dans Z) à r=4
- Estimer corrections modulaires O(S^{r-1} · log S)
- Valider numériquement sur données Phase A

**B2** : Borne uniforme |μ̂_k(t)| sans EO
- Méthode Weyl ordre 2 + E₈ → mixing k ≥ 5
- OU méthode combinée énergie + paucité → |μ̂_k| ≤ S^{-k/3+o(k)}
- Critère : borne rigoureuse sans hypothèse d'équidistribution orbitale

**B3** : Attaquer PU (proportion uniformity)
- Vérification numérique : π(A,0)/k! vs 1/p pour k=5..10
- Tentative théorique : marche sur S_k via poids 3^j

### Phase C — Structure de d(k) (plan de repli)

**C1** : Analyser pourquoi d(k) n'a pas de facteurs Régime B
**C2** : Bornes sur n₃ via structure de d(k)
**C3** : Bornes spécifiques pour ⟨2⟩ (lacunarité, binary structure)

## Protocoles

- Anti-hallucination : chaque claim vérifié par calcul indépendant
- Anti-régression : score 4.85/5 ne doit jamais baisser
- Transparence : documenter honnêtement les échecs
- Fichiers temporaires : écrire au fil de l'eau dans research_log/

## Fichiers produits

- `research_log/carte_mentale_exhaustive.tmp.md` — carte complète (18 chemins)
- `scripts/exploration/phase_a1_exhaustive_k18_25.py` — vérification k=18..25
- `scripts/exploration/phase_a2_regime_b_extension.py` — extension m=131..500
