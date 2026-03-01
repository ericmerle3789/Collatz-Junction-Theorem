# Design : Phase 20 — Exploration des 4 Pistes (Hypothese H)
# Date : 27 fevrier 2026
# Approuve par : Eric Merle

---

## Contexte

### Le verrou
L'Hypothese H (Zero-Exclusion) est le dernier obstacle vers la preuve complete
de l'absence de cycles positifs non-triviaux dans la conjecture de Collatz.

**Enonce** : Pour tout k >= 1 et tout sous-ensemble A de {0,...,S-1} de taille k,
on a corrSum(A) != 0 mod d, ou d = 2^S - 3^k > 0.

### Acquis (Phases 10-19)
- 73 theoremes Lean verifies (0 sorry, 0 axiom)
- Non-surjectivite pour k >= 18 (inconditionnel) : C(S-1,k-1) < d
- Junction Theorem : [1,67] U [18,inf) = [1,inf) couvre tous les k
- Deficit entropique gamma ~= 0.0500 (universel)
- Parseval cost (Th 16.1) : contrainte energetique si N_0 >= 1
- Mellin-Fourier bridge (Th 19.1) : equivalence des 3 formulations

### Trois formulations equivalentes
1. **Additive (Fourier)** : Conjecture M — |T(t)| <= C * k^{-delta}
2. **Multiplicative (Mellin)** : Conjecture M_Mellin — |M(chi)| <= C^{1-epsilon}
3. **Combinatoire (CRT)** : Trouver un p | d avec N_0(p) = 0

---

## Approche retenue : Deep-Dive Sequentiel

Ordre : A -> B -> C -> D (du plus concret au plus abstrait)
Les decouvertes d'une piste informent les suivantes.

---

## Piste A — CRT Hybride + Computationnel

**Objectif** : Pour chaque d(k), trouver un premier p | d tel que N_0(p) = 0.

**Plan** :
1. Formaliser N_0(p) = #{A : |A|=k, Ev(A) = 0 mod p}
2. Estimer via sommes de Gauss/Kloosterman : N_0(p) = C(S-1,k-1)/p + E(p)
3. Condition de victoire : |E(p)| < C(S-1,k-1)/p => N_0(p) = 0
4. Verification numerique pour k = 8,...,17
5. Analyse : bornes de Weil-Deligne suffisantes ?

**Livrables** :
- `research_log/phase20a_piste_CRT_hybride.md`
- `scripts/phase20_crt_analysis.py`

---

## Piste B — Structure Algebrique (Bases 2 et 3)

**Objectif** : Exploiter l'incompatibilite arithmetique 2 vs 3 pour exclure 0.

**Plan** :
1. Classification Type I/II des premiers p | d
2. Rigidite du sous-groupe <2> dans (Z/pZ)* : quand 3 notin <2>
3. Quand Im(Ev) vit dans un coset strict, 0 est exclu
4. Densite des primes Type II parmi diviseurs de d
5. Connexion avec Gersonides (deja formalise)

**Livrables** :
- `research_log/phase20b_piste_structure_algebrique.md`
- `scripts/phase20_type_classification.py`

---

## Piste C — Mixing / Random Walk

**Objectif** : Modeliser Horner comme marche aleatoire, montrer biais anti-zero.

**Plan** :
1. Chaine de Markov sur Z/pZ : transitions = multiplication + ajout
2. Temps de melange : tau_mix <= O(log p * log log p)
3. Apres melange : P(r_k = 0) ~= 1/p
4. Structure de Horner => biais anti-zero (via Parseval cost)
5. Lien avec deficit entropique gamma

**Livrables** :
- `research_log/phase20c_piste_mixing_random_walk.md`
- `scripts/phase20_mixing_simulation.py`

---

## Piste D — Extension de Tao (2022)

**Objectif** : Adapter l'approche ergodique pour montrer densite(k admissibles) = 0.

**Plan** :
1. Structure de la preuve de Tao : mesure, entropie, bornes de densite
2. Point d'ancrage : deficit gamma ~= 0.0500 comme analogue
3. Adaptation : "presque tout k n'admet pas de cycle"
4. Force du resultat : densite 0 vs exclusion totale
5. Connexion Parseval cost + Mellin-Fourier bridge

**Livrables** :
- `research_log/phase20d_piste_extension_tao.md`

---

## Synthese

**Livrable final** : `research_log/phase20_synthese_4_pistes.md`

Contenu :
- Tableau comparatif (faisabilite, conditionnalite, force, chemin Lean)
- Verdict : piste(s) a avancer en Phase 21+
- Recommandation pour formalisation Lean

---

## Criteres d'evaluation par piste

| Critere | Description |
|---------|-------------|
| Faisabilite | L'approche peut-elle aboutir avec les outils actuels ? |
| Conditionnalite | Resultat inconditionnel ou dependant d'une conjecture ? |
| Force | Exclusion totale (H prouvee) ou resultat partiel ? |
| Calculabilite | Verification numerique possible ? |
| Chemin Lean | Peut-on formaliser en Lean 4 ? |
| Connexion existante | Utilise les 73 theoremes et le Parseval cost ? |
