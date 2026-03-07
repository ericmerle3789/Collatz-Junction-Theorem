# Plan : Close the sorry k>=307 — COMPLETED

**Status: COMPLETED (March 2026)**
- 0 sorry, 2 axioms (Simons--de Weger + CF lower bound)
- See `AsymptoticBound.lean` for the implementation

## Original plan (historical, in French)

## Stratégie en 2 sous-cas

### Cas 1 : S/k NON convergent de log₂3
- gap_non_convergent donne |Δ| ≥ log2/(2k)
- Bridge lemma : Δ ≥ ε > 0 ⟹ d = 2^S - 3^k ≥ 2^S · ε/2
- deficit_linear_growth donne log₂(C) ≤ S(1-γ) + log₂(S)
- Comparaison : γS > log₂(S) + log₂(k) + 2.53 pour k ≥ 307

### Cas 2 : S/k EST un convergent de log₂3
- Ceci signifie S/k = pₙ/qₙ (convergent impair, n=7,9,11,...)
- Donc k = m·qₙ, S = m·pₙ pour un m ≥ 1
- Factorisation : 2^(m·p) - 3^(m·q) = (2^p - 3^q) · Σ (2^p)^i · (3^q)^(m-1-i)
- Borne : d ≥ (2^p - 3^q) · (3^q)^(m-1) ≥ 3^(q(m-1))
- deficit_linear_growth : C ≤ S · 2^{S(1-γ)} = m·p · 2^{mp(1-γ)}
- Besoin : 3^{q(m-1)} > m·p · 2^{mp(1-γ)}
  ⟺ q(m-1)·log₂3 > log₂(mp) + mp(1-γ)
  ⟺ qm·log₂3 - q·log₂3 > log₂(mp) + mp - γmp
  Puisque S = mp ≈ mq·log₂3 : qm·log₂3 ≈ mp
  ⟺ mp - q·log₂3 > log₂(mp) + mp - γmp
  ⟺ γmp > q·log₂3 + log₂(mp)
  ⟺ γS > q·log₂3 + log₂S
  Pour q₇=306 : γS > 306·1.585 + log₂S = 485 + log₂S
  Pour k=612(m=2): S=970, γS=48.5 vs 485+9.92=494.92... ECHEC!

### PROBLEME : La factorisation ne suffit pas pour petit m!
Pour m=2, k=612, S=970 : d = (2^485-3^306)(2^485+3^306) ≈ 2^{960}
C(969,611) ≈ 2^{969·H(611/969)} ≈ 2^{969·0.951} ≈ 2^{921}
Margin ≈ 39 bits. OK numériquement mais la borne (3^q)^(m-1) = 3^306 ≈ 2^485 est trop faible.

Meilleure borne : d = (2^p-3^q)·Σ ≥ (2^p-3^q)·(2^p)^{m-1}/(2)
puisque 2^p > 3^q et la somme géométrique Σ ≥ (2^p)^{m-1}/2 (?)
Non, Σ = Σ_{i=0}^{m-1} (2^p)^i·(3^q)^{m-1-i}. Chaque terme ≥ (3^q)^{m-1}.
Donc Σ ≥ m·(3^q)^{m-1}.
d ≥ (2^p - 3^q)·m·(3^q)^{m-1}

Pour m=2, p=485, q=306 :
d ≥ (2^485-3^306)·2·3^306
2^485-3^306 ≈ 2^485·(1-2^{-0.0007}) ≈ 2^485·4.85e-4 ≈ 2^{474}
d ≥ 2^{474}·2·2^{485} = 2^{960}
C(969,611) ≈ 2^{921}. Margin 39 bits. ✓

Pour m général : d ≥ (2^p-3^q)·m·(3^q)^{m-1}
log₂(d) ≥ log₂(2^p-3^q) + log₂(m) + (m-1)·q·log₂3
         ≈ p-11 + log₂(m) + (m-1)·q·1.585
         = p-11 + log₂(m) + (m-1)·p (puisque q·1.585 ≈ p)
         = mp - 11 + log₂(m)
         = S - 11 + log₂(m)
C ≤ S·2^{S(1-γ)} ⟹ log₂C ≤ S(1-γ) + log₂S

Besoin : S - 11 + log₂(m) > S(1-γ) + log₂S
⟺ γS > 11 + log₂S - log₂m
⟺ γS > 11 + log₂(S/m) = 11 + log₂(p)

Pour p₇=485 : γS = 0.05·mp = 0.05·485m = 24.25m
RHS = 11 + log₂(485) = 11 + 8.92 = 19.92
Pour m=1 : 24.25 > 19.92 ✓ (mais m=1 ⟹ k=306, déjà couvert par native_decide)
Pour m=2 : 48.5 > 19.92 ✓
Pour m≥1 : 24.25m > 19.92 ✓ toujours (puisque 24.25 > 19.92)

Pour p₉=24727 : γS = 0.05·24727m = 1236.35m
RHS = 11 + log₂(24727) = 11 + 14.59 = 25.59
Pour m=1 : 1236.35 > 25.59 ✓

### CONCLUSION : La factorisation MARCHE pour tous les convergents!
d ≥ (2^p - 3^q)·m·(3^q)^{m-1}
log₂d ≥ S - C₀ + log₂m où C₀ ≈ 11 (dépend de |2^p-3^q|)
Et γS > C₀ + log₂(p) pour tout convergent pₙ/qₙ avec n ≥ 7

MAIS : il faut prouver (2^p-3^q) > 0 pour chaque convergent impair.
Ceci est EXACTEMENT ce que close_case vérifie pour k=qₙ !
On l'a déjà pour q₇=306 (dans FiniteCases).

Pour q₉=15601 : il faudrait 2^24727 > 3^15601. C'est vrai (convergent impair ⟹ p/q > ξ)
mais on peut le vérifier par native_decide : (3:ℤ)^15601 < (2:ℤ)^24727. FAISABLE.

## Plan révisé FINAL

1. Lemme bridge_exp : 1 - e^{-x} ≥ x/(1+x) pour x > 0 (Mathlib?)
2. Lemme crystallModule_lower_non_conv : pour k non-convergent, d ≥ 2^S·log2/(4k)
3. Lemme comparison_non_conv : γS > log₂S + log₂k + C ⟹ C < d
4. Lemme factorization : 2^(mp) - 3^(mq) ≥ (2^p-3^q)·m·(3^q)^{m-1}
5. Lemme comparison_conv : pour convergent p/q avec p≥485, d_factored > C

PROBLEME RESTANT : Comment prouver en Lean que S/k est ou n'est pas un convergent
de manière DECIDABLE, sans axiome sur la fraction continue de log₂3 ?

## IDÉE CLÉ : Éviter complètement le split convergent/non-convergent!

Au lieu de distinguer les cas, utiliser une borne UNIVERSELLE sur d :
- d = 2^S - 3^k est un entier positif
- 3^k = 2^S - d, donc (2^S - d)^{1/k} = 3, i.e., 3^k + d = 2^S
- En fait, on peut borner d DIRECTEMENT par les propriétés de 2^S - 3^k

Borne universelle : d ≥ 1 (trivial, mais insuffisant).

Borne via Ridout/Roth : |2^α - 3^β| ≥ exp(-C·max(α,β)^{1-δ}) pour tout δ > 0.
Non formalisé.

## NOUVELLE IDÉE : native_decide pour TOUT k ≤ N₀, algébrique pour k > N₀

Pour k très grand, même d ≥ 1 suffit si C < 1... mais C ≥ 1 toujours.

Non, C est toujours énorme. On a BESOIN d'une borne sur d.

## DÉCISION FINALE : Split en 2, avec native_decide pour les convergents proches

1. by_cases sur convergence (décidable via `convergentDenominators_12`)
2. Non-convergent : Legendre + deficit (preuve algébrique complète)
3. Convergent : factorisation + native_decide des cas de base

Le point clé : il n'y a qu'un NOMBRE FINI de convergents à vérifier
car au-delà de q₁₁=79335, la factorisation + borne de base suffit.

STOP — trop complexe. Approche plus simple :

## APPROCHE ULTIME : Tout par native_decide jusqu'à k grand + borne simple

Étendre native_decide MASSIVEMENT :
- k ∈ [307, 665] : S jusqu'à 1055 (entiers ~1000 bits) — faisable en minutes
- k ∈ [666, 15600] : S jusqu'à 24725 — LENT (entiers ~25000 bits)

Non viable pour k > ~1000.

## VRAIE APPROCHE FINALE : 3 tiers

Tier 1 : k ∈ [307, 665] par native_decide (359 cas, S ≤ 1055)
Tier 2 : k ∈ [666, ∞) non-convergent : Legendre + deficit
Tier 3 : k ∈ [666, ∞) convergent : factorisation

Pour Tier 2, il faut prouver la non-convergence.
Trick : Si k n'est pas divisible par aucun qₙ ≤ k, alors S/k n'est pas un convergent.
Car si S/k = pₙ/qₙ, alors qₙ | k.

Les qₙ dans [666, ∞) pertinents : q₈=665 (couvert par Tier 1),
q₉=15601, q₁₀=31867, q₁₁=79335.
Pour k ∈ [666, ∞) : si qₙ | k avec qₙ > 306, c'est q₈=665 ou plus.
Mais k=665 est dans Tier 1. Pour k > 665 avec 665|k : k=1330, 1995, ...
Rat.divInt S k = Rat.divInt (m·1055) (m·665) = 1055/665 = p₈/q₈
MAIS q₈=665 est un convergent PAIR, et p₈/q₈ < ξ.
Donc S = ⌈k·ξ⌉ = ⌈665m·ξ⌉ > 665m·ξ > m·p₈ = 1054m.
Mais S = ⌈665m·ξ⌉ = 1055m (car 665·ξ ≈ 1054.00006, donc 665m·ξ ≈ 1054.00006m,
et ⌈1054.00006m⌉ = 1055 pour m=1, = 1055m pour m ≥ 1? NON!)
⌈1054.00006·2⌉ = ⌈2108.00012⌉ = 2109 ≠ 1055·2 = 2110.
Donc S ≠ m·p₈ pour m > 1 en général!

OK la relation S/k ≠ pₙ/qₙ est PLUS SUBTILE que "qₙ ne divise pas k".

SIMPLIFICATION : Pour l'hypothèse de gap_non_convergent,
on a besoin que Rat.divInt S k ne soit pas un convergent.
Rat.divInt S k est la fraction RÉDUITE. Si S/k = a/b en fraction réduite,
alors pour que a/b soit un convergent, il faut a/b = pₙ/qₙ, i.e., a=pₙ et b=qₙ.
Donc b = qₙ pour un certain n. Et b | k.

Pour k > 665 : les seuls qₙ qui divisent k sont qₙ ≤ k.
Les qₙ ≤ 79335 sont : 1,1,2,5,12,41,53,306,665,15601,31867,79335.

Mais on a besoin que la fraction RÉDUITE de S/k ne soit PAS un convergent.
Ceci peut être vérifié computationnellement pour chaque k.

APPROCHE PRAGMATIQUE : Je vais écrire le code maintenant.
