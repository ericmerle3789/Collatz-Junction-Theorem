# SESSION AUTONOME — 18 Mars 2026
## Objectif : Résolution complète de la non-trivialité de Collatz

### Contexte
- Audit critique reçu : corrSum dans lean4_proof/Basic.lean utilise exposants INDIVIDUELS
- Steiner (1977) requiert exposants CUMULATIFS (σ_i = e_1+...+e_i)
- Le skeleton Lean (JunctionTheorem.lean) est CORRECT (cumul.)
- Range Exclusion est INVALIDE (mauvaise formule)
- Junction Theorem (nonsurjectivité C(S-1,k-1) < d) reste VALIDE

### Ce qui est prouvé (solide)
1. Steiner's equation formalisée en Lean (cumul.) ✓
2. Crystal nonsurjectivity: C(S-1,k-1) < d pour k ≥ 18 ✓
3. SdW: pas de cycle k < 68 ✓
4. H → pas de cycle positif ✓

### Ce qui manque
- Hypothèse H : prouver que 0 ∈ résidus omis par Ev_d
- Équivalent : ∀ k ≥ 3, aucune séquence cumulative (0,σ_1,...,σ_{k-1})
  avec 0 < σ_1 < ... < σ_{k-1} < S ne donne corrSum ≡ 0 (mod d)

### Plan de travail
1. Vérification numérique de l'audit
2. Explorer les approches pour H
3. Configurer JEPA pour la bonne formule
4. Chercher une preuve

### Anti-hallucination
- TOUT résultat doit être vérifié numériquement
- Pas de "il est clair que" sans preuve
- Chaque claim → code de vérification
- Registre FAIL-CLOSED : si un test échoue, on s'arrête

---
## Journal de bord
