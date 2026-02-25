# PHASE 10F — AUDIT GOUËZEL : Diagnostic et Correction
## Date : 24 février 2026

---

## LA CRITIQUE DE GOUËZEL (exacte)

> "Are the hypothesis structures faithful to the published results?
> The assumption CF doesn't seem faithful. You should point to the
> precise statement in Simons & de Weger. Your current H3 is not
> reasonable — I don't think it follows from any published result.
> Assumptions should correspond word for word to results in the
> literature, and everything should depend only on these."

## DIAGNOSTIC

### Hypothèses FIDÈLES
- H1 (Baker) : (2^s - 3^k) · k^6 ≥ 3^k — FIDÈLE à Baker/Matveev
  (peut nécessiter vérification de l'exposant exact, mais l'esprit est correct)
- H2 (Barina) : tout n < 2^71 converge — FIDÈLE à Barina 2025

### Hypothèse NON FIDÈLE
- H3 (SdW k ≤ 982) : PAS dans Simons-de Weger. SdW prouve m ≤ 68.
- H3' (CF : k > 1322 → n < 2^71) : PAS publié. Dérivation interne.

## CE QUE LA LITTÉRATURE PROUVE RÉELLEMENT

### Sur les cycles
- Steiner (1977) : pas de 1-cycle
- Simons-de Weger (2005) : pas de m-cycle pour m ≤ 68
- Hercher (2023) : pas de m-cycle pour m ≤ 91
  [arxiv: 2201.00406, J. Integer Sequences 26, Art. 23.3.5]

### ATTENTION : m vs k
- m = nombre de cycles (au sens de Hercher/SdW)
- k = nombre d'étapes impaires
- Dans notre formalisation : k = nombre d'étapes impaires
- Hercher prouve : pas de cycle avec k ≤ 91 étapes impaires

## CORRECTION PROPOSÉE

### Option 1 : Hypothèses fidèles minimales (3 hyp.)
- H1 : Baker (forme linéaire en logarithmes) — tel quel
- H2 : Barina (convergence ≤ 2^71) — tel quel
- H3 : Hercher (pas de k-cycle pour k ≤ 91) — citation directe

Problème : Baker + Hercher + Barina ne couvrent QUE k ≤ 91.
Pour k ∈ [92, 1322] : Baker donne n ≤ (k^7+k)/3 < 2^71. OK.
Pour k > 1322 : n peut dépasser 2^71. GAP NON COUVERT.

### Option 2 : SdW fidèle (leur vrai théorème)
Simons-de Weger Theorem 3 : pour tout m-cycle non trivial,
k ≥ f(m) pour une fonction explicite f.
Leur Table 5 donne les bornes.

Mais citer correctement SdW nécessite de comprendre exactement
ce que leur Theorem 3 dit (la borne dépend de convergents de log₂3).

### Option 3 : Séparer prouvé vs conditionnel
- Théorème INCONDITIONNEL : pas de k-cycle pour k ≤ 91 (Hercher)
  + Baker + Barina → pas de cycle avec k ≤ 1322
- Théorème CONDITIONNEL : sous hypothèse CF → pas de cycle pour tout k
  Mais H3 doit être clairement identifiée comme NON PUBLIÉE

## LE VRAI PROBLÈME STRUCTUREL

Le gap k > 1322 n'est couvert par AUCUN résultat publié directement.
La couverture repose sur une CHAÎNE de raisonnement :
1. Baker → borne sur d
2. CF de log₂3 → borne renforcée sur d entre convergents
3. Product Bound → borne sur n
4. Vérification que n < 2^71 dans chaque fenêtre CF

Cette chaîne est CORRECTE mathématiquement mais non formalisée.
Gouëzel dit : formalisez-la ou ne prétendez pas l'avoir.

## PLAN D'ACTION

1. Identifier le théorème de meilleure approximation exact à citer
2. L'encoder fidèlement comme hypothèse
3. DÉRIVER le gap k > 1322 comme THÉORÈME dans Lean
4. OU accepter que k > 1322 est conditionnel et le dire clairement
