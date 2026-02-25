# PHASE 10D — RÉFLEXION PROFONDE
## La structure de corrSum mod d
## Date : 24 février 2026

---

## LA QUESTION

corrSum = Σ_{i=0}^{k-1} 3^{k-1-i} · 2^{A_i}

avec A_0 = 0, A_i = c_1 + ... + c_i, A_k = S, chaque c_j ≥ 1.

d = 2^S - 3^k. On veut : corrSum ≢ 0 (mod d), i.e., d ∤ corrSum.

---

## OBSERVATION 1 : Réduction mod d

Dans Z/dZ : 2^S ≡ 3^k.

Posons u = 2 · 3^{-1} mod d. Alors u^S = 2^S · 3^{-S} ≡ 3^k · 3^{-S} = 3^{k-S} = 3^{-B}
où B = S - k.

Donc u est une racine de u^S = 3^{-B} dans Z/dZ.

corrSum = Σ_{i=0}^{k-1} 3^{k-1-i} · 2^{A_i}
        = 3^{k-1} · Σ_{i=0}^{k-1} (2/3)^{A_i} · 3^{A_i - i}

Non, simplifions autrement. Factorisons 3^{k-1} :

corrSum = Σ_{i=0}^{k-1} 3^{k-1-i} · 2^{A_i}

Le terme i a 3^{k-1-i} et 2^{A_i}. Notons que A_i = i + b_i
où b_i = A_i - i = (c_1-1) + (c_2-1) + ... + (c_i-1) ≥ 0.

Donc 2^{A_i} = 2^i · 2^{b_i}.

corrSum = Σ_{i=0}^{k-1} 3^{k-1-i} · 2^i · 2^{b_i}
        = 3^{k-1} · Σ_{i=0}^{k-1} (2/3)^i · 2^{b_i}

Mod d, posons u = 2 · 3^{-1} :

corrSum ≡ 3^{k-1} · Σ_{i=0}^{k-1} u^i · 2^{b_i}  (mod d)

Notons f(b) = Σ_{i=0}^{k-1} u^i · 2^{b_i}.

corrSum ≡ 0 (mod d) ⟺ f(b) ≡ 0 (mod d)
(car gcd(3, d) = 1, donc 3^{k-1} est inversible mod d)

---

## OBSERVATION 2 : La somme f(b) est un polynôme évalué

f(b) = Σ_{i=0}^{k-1} u^i · 2^{b_i}

Les b_i satisfont 0 = b_0 ≤ b_1 ≤ ... ≤ b_{k-1} ≤ B.
(monotonie des b-vecteurs dans la paramétrisation de Steiner)

Chaque terme est u^i · 2^{b_i}. Le "poids" dépend de la position i
(via u^i) et de l'excès cumulé b_i (via 2^{b_i}).

Pour un cycle : f(b) ≡ 0 (mod d).

MAIS la cible correcte de Steiner est n = corrSum/d,
donc en fait corrSum = n·d, i.e., f(b) = n·d/3^{k-1}.

Non, soyons précis : corrSum ≡ 0 (mod d) ⟺ f(b) ≡ 0 (mod d).

---

## OBSERVATION 3 : Que vaut f(b) pour des cas simples ?

### Cas b = (0,0,...,0) : tous les c_j = 1, donc S = k.
IMPOSSIBLE car S ≈ 1.585k > k. Ne satisfait pas Σc_j = S.

### Cas b = (0,0,...,0,B) : c_k = B+1, tous les autres c_j = 1.
f = Σ_{i=0}^{k-2} u^i · 1 + u^{k-1} · 2^B
  = (u^{k-1} - 1)/(u - 1) + u^{k-1} · 2^B

### Cas uniforme : b_i = ⌊iB/(k-1)⌋ (approximation)
Distribution "plate" de l'excès. C'est le cas le plus "générique".

---

## OBSERVATION 4 : L'IDENTITÉ CRUCIALE

f(b) = Σ_{i=0}^{k-1} u^i · 2^{b_i}

Or u = 2·3^{-1} mod d, donc u^i = 2^i · 3^{-i}.

f(b) = Σ 2^i · 3^{-i} · 2^{b_i} = Σ 2^{i+b_i} · 3^{-i}
     = Σ 2^{A_i} · 3^{-i}

Donc f(b) ≡ 0 (mod d) ⟺ Σ 2^{A_i} · 3^{-i} ≡ 0 (mod d)
⟺ Σ 2^{A_i} · 3^{k-1-i} ≡ 0 (mod d) [multipliant par 3^{k-1}]
⟺ corrSum ≡ 0 (mod d). Circulaire, mais attendons...

La forme Σ 2^{A_i} · 3^{-i} mod d est intéressante car
dans Z/dZ, les puissances de 2 et 3 sont LIÉES par 2^S = 3^k.

---

## OBSERVATION 5 : Le groupe engendré par 2 mod d

Soit G = <2> le sous-groupe multiplicatif engendré par 2 dans (Z/dZ)*.

L'ordre de 2 mod d divise S (car 2^S = 3^k ≡ 3^k mod d).
Mais 2^S ≡ 3^k ≠ 1 en général, donc ord(2) ne divise pas S
sauf si 3^k ≡ 1 (mod d).

3^k mod d = 3^k mod (2^S - 3^k). Or 2^S ≡ 3^k mod d,
donc 3^k ≡ 2^S mod d. Et 3^{2k} ≡ 2^{2S} mod d.

L'ordre de 3 mod d : 3^k ≡ 2^S, 3^{2k} ≡ 2^{2S}, etc.
En général, ord(3) | lcm avec une relation à S et k.

POINT CLÉ : 2 et 3 ne sont pas indépendants mod d.
La relation 2^S = 3^k + d contraint TOUT.

---

## OBSERVATION 6 : Reformulation comme somme géométrique tordue

corrSum = Σ_{i=0}^{k-1} 3^{k-1-i} · 2^{A_i}

Dans Z/dZ, remplaçons 3^k par 2^S :
3^{k-1} = 3^k / 3 = 2^S / 3 (mod d)

Donc le terme i=0 : 3^{k-1} · 2^0 = 2^S/3 (mod d)
Le terme i=1 : 3^{k-2} · 2^{A_1} = 2^S/(3^2) · 2^{A_1} = 2^{S+A_1}/9
...
Le terme i : 3^{k-1-i} · 2^{A_i} = 2^S · 3^{-1-i} · 2^{A_i} = 2^{S+A_i} · 3^{-(i+1)}

Donc : corrSum ≡ Σ_{i=0}^{k-1} 2^{S+A_i} · 3^{-(i+1)} (mod d)

Factorisons 2^S : corrSum ≡ 2^S · Σ 2^{A_i} · 3^{-(i+1)} (mod d)
                          ≡ 3^k · Σ 2^{A_i} · 3^{-(i+1)} (mod d)
                          ≡ Σ 2^{A_i} · 3^{k-i-1} (mod d)

C'est à nouveau corrSum. Circulaire.

---

## OBSERVATION 7 : La VRAIE piste — récurrence sur les termes

Écrivons corrSum différemment. Posons T_j le j-ème terme :
T_j = 3^{k-1-j} · 2^{A_j}

Alors T_{j+1}/T_j = (3^{k-2-j}/3^{k-1-j}) · (2^{A_{j+1}}/2^{A_j})
                   = (1/3) · 2^{c_{j+1}}
                   = 2^{c_{j+1}} / 3

Donc T_{j+1} = T_j · 2^{c_{j+1}} / 3.

C'est EXACTEMENT le ratio de Collatz ! Le ratio T_{j+1}/T_j = 2^{c_j}/3
est l'INVERSE du ratio n_{j+1}/n_j ≈ 3/2^{c_j}.

Les termes de corrSum évoluent à l'INVERSE de l'orbite.
Quand l'orbite monte (petit c_j), le terme descend.
Quand l'orbite descend (grand c_j), le terme monte.

C'est une DUALITÉ entre l'orbite et la somme.

---

## OBSERVATION 8 : La formule fermée de corrSum

corrSum = Σ_{j=0}^{k-1} T_j avec T_0 = 3^{k-1}, T_{j+1} = T_j · 2^{c_{j+1}}/3.

Donc T_j = 3^{k-1} · Π_{m=1}^{j} (2^{c_m}/3) = 3^{k-1} · 2^{A_j} / 3^j = 3^{k-1-j} · 2^{A_j}.
Cohérent. ✓

Le rapport T_{k-1}/T_0 = 2^{A_{k-1}} / 3^{k-1} = 2^{S-c_k} / 3^{k-1}.

Pour un cycle : 3^k/2^S < 1, donc 2^S > 3^k, donc T_{k-1}/T_0 > 2^{S-S}/3^{k-1}...
Ça dépend de c_k.

---

## OBSERVATION 9 : LE MOMENT EUREKA ?

Posons corrSum mod d.

corrSum = Σ_{j=0}^{k-1} 3^{k-1-j} · 2^{A_j}

Notons que A_{k-1} = S - c_k. Donc le dernier terme est
T_{k-1} = 3^0 · 2^{S-c_k} = 2^{S-c_k}.

Et mod d : 2^S ≡ 3^k, donc 2^{S-c_k} = 2^S · 2^{-c_k} ≡ 3^k · 2^{-c_k}.

Le premier terme : T_0 = 3^{k-1}.

corrSum mod d = 3^{k-1} + 3^{k-2}·2^{c_1} + ... + 3^k·2^{-c_k} (mod d)

En factorisant par 3^{k-1} :
corrSum/3^{k-1} ≡ 1 + (2/3)^{c_1}·2^{b_1-b_0}·...

Non, revenons au basique. La question VRAIE est :

Σ_{j=0}^{k-1} 3^{k-1-j} · 2^{A_j} ≡ 0 (mod 2^S - 3^k) ?

Écrivons cette somme comme un POLYNÔME en 2 et 3.
C'est une combinaison linéaire de monômes 3^a · 2^b.

La relation d ≡ 0 (mod d) dit 2^S ≡ 3^k.
Donc dans Z/dZ, toute puissance 2^{S+r} ≡ 3^k · 2^r.

Cela permet de RÉDUIRE tout 2^m avec m ≥ S en utilisant 2^S → 3^k.

Mais les A_j < S (sauf A_k = S), donc 2^{A_j} est déjà réduit.

SAUF si on additionne : la SOMME peut dépasser d. Et c'est le cas.
corrSum >> d en général (corrSum ≈ n·d avec n >> 1).

---

## OBSERVATION 10 : L'approche de Steiner inversée

Steiner (1977) pose le problème comme :
"Étant donné k et la séquence c, trouver n = R(c)/d."

Mais inversons : "Étant donné n, la séquence c est DÉTERMINÉE."

Pour n fixé impair, la dynamique donne :
c_1 = v_2(3n+1), n_1 = (3n+1)/2^{c_1}
c_2 = v_2(3n_1+1), n_2 = (3n_1+1)/2^{c_2}
...

Après k pas : n_k = (3^k·n + corrSum) / 2^S.
Cycle ⟺ n_k = n ⟺ n·(2^S - 3^k) = corrSum.

Mais corrSum DÉPEND de n (via les c_j qui dépendent de n).

C'est un problème de POINT FIXE :
n → c(n) → corrSum(c(n)) → corrSum(c(n))/d = n ?

---

## OBSERVATION 11 : La structure 2-adique — LE VRAI LEVIER

Pour n impair, c_1 = v_2(3n+1).
3n+1 en binaire : si n = ...b_m...b_1b_0 en binaire (b_0 = 1 car impair),
alors 3n+1 = 2n + n + 1.

L'addition 2n + (n+1) propage des retenues.
c_1 = nombre de 0 terminaux de 3n+1 = longueur de la chaîne
de propagation de retenue.

Si n ≡ 1 (mod 4) : n = ...01, 3n+1 = ...00 + ...10 = ...100, c_1 ≥ 2.
Si n ≡ 3 (mod 4) : n = ...11, 3n+1 = ...10 + ...00 = ...10, c_1 = 1.

Plus précisément : c_1 dépend de n mod 2^m pour un m croissant.

C'est la CLÉ : la séquence c dépend de n 2-ADIQUEMENT.
Et la condition n = corrSum/d est une condition RATIONNELLE.

La tension entre la structure 2-adique (locale) et la
condition rationnelle (globale) est peut-être LE levier.

---

## OBSERVATION 12 : L'argument de Wirsching (2-adic)

Wirsching (1998) a montré que la fonction de Collatz est
analytique dans les entiers 2-adiques Z_2.

L'application T : Z_2 → Z_2 est continue et analytique par morceaux.
Un cycle dans N est aussi un cycle dans Z_2.

MAIS Z_2 est compact, donc T a des points fixes (Brouwer).
Les cycles dans Z_2 EXISTENT (en nombre infini, même).
Le problème est de montrer qu'aucun n'est un entier POSITIF.

C'est la DUALITÉ : abondance 2-adique vs rareté rationnelle.

---

## SYNTHÈSE INTERMÉDIAIRE — Où en est-on ?

Après 12 observations, les pistes se clarifient :

1. **L'approche purement algébrique mod d** (obs 1-6, 9) tourne en rond.
   La relation 2^S ≡ 3^k est utile mais ne donne pas de contradiction directe.

2. **La dualité orbite/somme** (obs 7-8) est élégante mais descriptive.

3. **L'auto-référence** (obs 10) est le cœur du problème.

4. **La tension 2-adique/rationnel** (obs 11-12) est la piste la plus PROFONDE.

La question devient :
**Un point fixe 2-adique de T^k peut-il être rationnel positif ?**

Si on montrait que tout point fixe 2-adique de T^k est soit
négatif, soit irrationnel, soit 1, ce serait LA preuve.

C'est l'approche de Lagarias-Kontorovich (2-adic analysis).
Où en est la littérature ? Que sait-on exactement ?
