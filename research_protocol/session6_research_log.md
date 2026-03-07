# SESSION 6 — RESEARCH LOG
## Attaque de l'Énoncé C (le cœur de la preuve)
### Date : 3 mars 2026

---

## OBJECTIF DE LA SESSION

Prouver l'Énoncé C : Pour tout k ≥ 3 et tout état serré s = 3+2^p,
le backward restreint aux positions > p ne peut pas atteindre s.
Autrement dit : max_bwd(s) = p (et non p+1 ou plus).

---

## RÉSULTATS

### 1. Bug corrigé dans Investigation 6

L'Investigation 6 originale oubliait le terme q₂ dans le préfixe.

- **Préfixe BUGGÉ** : 5·3^{k-2} (manque le terme j=2)
- **Préfixe CORRECT** : (9 + 5·2^p)·3^{k-3} = 19·3^{k-3} pour p=1

Conséquence : les "faux positifs" (target trouvé pour k=5, k=10) sont
des artefacts du bug. Le target CORRIGÉ est TOUJOURS ABSENT pour k=5..12.

### 2. L'argument mod 3 est INSUFFISANT

**Tentative** : prefix ≡ 0 mod 3, suffix ≡ 2^{q_{k-1}} mod 3 ∈ {1,2}.
Donc corrSum ≢ 0 mod 3. Et si d | corrSum exigeait 3 | corrSum, on aurait une contradiction.

**Problème** : gcd(d, 3) = 1 (car d = 2^S - 3^k et 3 ∤ 2^S).
Donc d | corrSum N'EXIGE PAS 3 | corrSum. L'argument est invalide.

Vérification : pour k=5, target mod d = 11, et 11 mod 3 = 2 (pas 0).
L'obstruction mod 3 ne fonctionne que pour certains k (ex: k=8 où target mod 3 = 0).

### 3. L'automate non ordonné atteint le target

L'automate backward SANS contrainte d'ordre strict (positions quelconques ≥ p+2)
ATTEINT toujours s=5, en utilisant des positions RÉPÉTÉES (ex: [3,3,5]).

Pour k=5..13 : l'automate non ordonné couvre TOUT Z/dZ (100%).

### 4. L'automate ORDONNÉ n'atteint PAS le target

L'automate backward AVEC positions strictement décroissantes
(q_{k-1} > q_{k-2} > ... > q_2, toutes ≥ p+2)
N'ATTEINT JAMAIS s=5. Vérifié pour k=5..13.

**Perte de couverture** typique :
- k=5 : 13 → 7 résidus (53.8%)
- k=7 : 1909 → 126 (6.6%)
- k=10 : 6487 → 1181 (18.2%)
- k=12 : 517135 → 19324 (3.7%)

### 5. Zone d'exclusion croissante

La distance minimale entre les résidus ordonnés et le target :
- k=5 : rayon = 1
- k=6 : rayon = 6
- k=7 : rayon = 15
- k=8 : rayon = 5
- k=9 : rayon = 64
- k=10 : rayon = 32

Le target n'est pas seulement absent : il est entouré d'un "bassin d'exclusion"
qui tend à croître avec k (non monotone à cause de d variable).

### 6. Vérification exhaustive étendue

Pour TOUT p (pas seulement p=1) et k=3..12 :
Aucune composition (0, p, p+1, q₃, ..., q_{k-1}) ne donne corrSum ≡ 0 mod d.
Vérifié sur des centaines de milliers de compositions.

---

## NATURE DE L'OBSTRUCTION

L'obstruction est la **COMBINAISON** de trois facteurs :

1. **Contrainte d'ordre strict** : réduit C(n, k-2) vs n^{k-2}
2. **Structure multiplicative** : poids 3^{k-1-j}·2^{q_j} avec hiérarchie
3. **Identité 3^k = 2^S - d** : lie le modulus aux poids

Aucun de ces facteurs seul ne suffit :
- L'ordre seul laisse beaucoup de résidus atteignables
- La structure multiplicative seule (automate non ordonné) couvre tout
- L'identité modulaire seule ne bloque rien

C'est leur **interaction** qui crée un "trou" systématique dans
les résidus atteignables, incluant toujours le target.

---

## CONSÉQUENCE STRATÉGIQUE

**L'Énoncé C est ÉQUIVALENT à N₀(d)=0 restreint aux compositions
commençant par position p.** Ce n'est PAS un lemme indépendant
plus facile que le théorème principal.

Cela signifie que la décomposition en Énoncés A/B/C ne "réduit" pas
réellement la difficulté : elle la redistribue. L'Énoncé B est facile
(pigeonhole), mais l'Énoncé C concentre TOUTE la difficulté de N₀(d)=0.

---

## PROCHAINES PISTES

### Piste 1 : Approche spectrale (Front E du protocole)
- Matrice de transfert T de l'automate Horner
- Restriction aux positions ordonnées = matrice triangulaire ?
- Spectre de T^{k-1} → formule pour N₀(d)
- Gap spectral → décroissance exponentielle

### Piste 2 : Argument de taille + combinatoire
- C(S-p-2, k-3) / d < 1 pour k ≥ 6 (couverture incomplète)
- Montrer que le target est STRUCTURELLEMENT dans les "trous"
- Utiliser la structure de Horner (récurrence multiplicative)

### Piste 3 : Abandon de l'Énoncé C comme lemme isolé
- Utiliser le Double Peeling comme CADRE CONCEPTUEL
- Prouver N₀(d)=0 directement (sans décomposer en A/B/C)
- L'Invariant Fort comme CONSÉQUENCE (pas prérequis) de N₀(d)=0

### Piste 4 : Retour au Peeling Lemma itéré
- Peeling sur PLUSIEURS variables simultanément
- Borne N₀(d) ≤ (k-1)/(S-1) · C = C/d · (k-1)/(1-ε) → 0 pour k grand
- Prouver que la borne est < 1 pour k ≥ k₀ (borne effective)

---

## SCRIPTS CRÉÉS

1. `enonce_c_investigation.py` — 8 investigations initiales (BUG dans Inv.6)
2. `enonce_c_deep_analysis.py` — correction du bug, analyse suffixe, tentative mod 3
3. `obstruction_search.py` — 7 approches pour trouver l'obstruction réelle
4. `ordered_backward_automaton.py` — automate ordonné, analyse CLEF de la session

---

## CONCLUSION

La session 6 n'a pas trouvé de preuve de l'Énoncé C, mais a
**identifié la nature exacte de l'obstruction** :
ce n'est pas une congruence simple mais l'interaction de l'ordre strict
avec la structure multiplicative dans Z/dZ.

Cela réoriente la stratégie vers des méthodes capables de capturer
cette interaction : spectrales, combinatoires, ou retour au peeling itéré.
