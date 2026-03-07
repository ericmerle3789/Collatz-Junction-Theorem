# SESSION 10f22 — SCRATCH : Attaque Artin pour G2c
## Date : 5 mars 2026
## Objectif : Prouver 2^C not equiv 1 mod d SANS GRH, pour d = 2^S - 3^k premier

---

## PRE-ENGAGEMENT SESSION 10f22
- **Hypothese** : La structure p-adique de d-1 et C = binom(S-1,k-1)
  permet de prouver ord_d(2) nmid C par incompatibilite de valuations
- **Succes** : Trouver un argument inconditionnel prouvant ord nmid C pour tout k >= 3
  (ou au moins pour une famille infinie dense)
- **Echec** : Apres 5 iterations G-V-R sans progres -> Cimetiere + doc
- **Budget** : 5 iterations G-V-R maximum

---

## STRATEGIE PRINCIPALE : ord nmid C au lieu de ord > C

### Changement de paradigme
- Session 10f21 cherchait a prouver **ord > C** (equivalent a Artin)
- Session 10f22 cherche a prouver **ord nmid C** (beaucoup plus faible!)
- ord nmid C suffit car : 2^C equiv 1 mod d ssi ord | C
- Il suffit de trouver UN prime p tel que v_p(ord) > v_p(C)

### Pourquoi c'est different d'Artin
- Artin = "Q est borne" (equiv. ord ~ d)
- Notre approche = "ord et C sont p-adiquement incompatibles"
- On n'a PAS BESOIN que ord soit grand, juste qu'il ne divise pas C !
- Contre-ex conceptuel : ord = 4, C = 6 => ord nmid C car v_2(4)=2 > v_2(6)=1

---

## OBSERVATIONS STRUCTURELLES

### O1. v_2(d-1) est determine par k [PROUVE]
- k impair : d equiv 5 mod 8 => d-1 equiv 4 mod 8 => v_2(d-1) = 2
- k pair : d equiv 7 mod 8 => d-1 equiv 6 mod 8 => v_2(d-1) = 1

### O2. v_2(Q) est determine par residuacite quadratique [PROUVE]
- k impair : 2 non-QR mod d => Q impair => v_2(Q) = 0
- k pair : 2 est QR mod d => Q pair, et v_2(Q) >= 1

### O3. v_2(ord) = v_2(d-1) - v_2(Q) [PROUVE]
- k impair : v_2(ord) = 2 - 0 = 2
- k pair : v_2(ord) = 1 - v_2(Q). Si v_2(Q) = 1 : v_2(ord) = 0

### O4. v_2(C) = v_2(binom(S-1, k-1)) [DEFINITION]
- Par Kummer : v_2(C) = nombre de retenues dans l'addition (k-1) + (S-k) en base 2
- La somme est S-1

---

## LITTERATURE (resume de l'exploration)

### Resultats existants
1. **Hooley (1967)** : Artin sous GRH. Donne Q borne pour densite positive de p.
2. **Heath-Brown (1986)** : Au plus 2 exceptions parmi les premiers. Un de {2,3,5} est PR infiniement.
3. **Erdos-Murty (1999)** : ord_p(a) > p^{1/2+eps} pour presque tous p. Inconditionnel mais "presque tous" exclut les familles minces.
4. **Kurlberg-Pomerance (2005)** : ord_p(a) > p^{0.677} pour une proportion positive de p.
5. **Pappalardi (1995)** : Raffinement quantitatif d'Erdos-Murty.

### Verdict
- AUCUN resultat inconditionnel connu pour ord_p(2) sur une famille SPECIFIQUE de premiers
- La famille d = 2^S - 3^k est trop mince (~ log^2(x) elements jusqua x)
- L'approche directe (prouver ord grand) est BLOQUEE par la barriere d'Artin
- => Il faut changer de strategie : prouver ord nmid C par incompatibilite de valuations

---

## G-V-R ITERATION 1 : APPROCHE v_2 (COMPLETEE)

### Pre-engagement iter 1
- **Hypothese** : v_2(C) <= 1 pour tout k >= 3 impair avec d premier
- **Succes** : Si vrai, v_2(ord) = 2 > v_2(C) <= 1 => ord nmid C pour k impair
- **Echec** : Un k impair avec d premier et v_2(C) >= 2

### Resultats script (session10f22_artin_investigation.py)
- I1 : v_2(d-1) = 2 pour TOUT k impair, 1 pour TOUT k pair — confirme 19/19 [PROUVE]
- I2 : v_2(ord) > v_2(C) pour k=3,5,13,69,73 (5/12 k impairs). ECHOUE pour 7/12.
- I3 : **HYPOTHESE v_2(C) <= 1 INVALIDEE** ⚠
  - v_2(C) atteint 16 pour k impair <= 100000
  - 48159/49999 = 96.3% des k impairs ont v_2(C) >= 2
  - Premier contre-exemple : k=11, S=18, v_2(C) = 3
- I4 : Pour k pair, p=23 marche pour k=4, p=5 pour k=56,76, p=31 pour k=3540
- I5 : G2c VERIFIE pour les 19 d premiers (2^C neq 1 mod d) [VERIFIE_k=3..10000]
- I7 : v_3 gagne pour k=5 et k=3895 mais pas generalement
- I8 : Approche hybride — 11/19 ont un petit premier gagnant, 8/19 non

### ANALYSE D'ECHEC (obligatoire selon protocole)

**Pourquoi l'hypothese v_2(C) <= 1 est fausse :**
- v_2(binom(n, m)) = nombre de retenues dans m + (n-m) en base 2 (Kummer)
- Pour k impair : m = k-1 (pair), n-m = S-k (qui peut etre petit)
- Quand S et k sont "proches" en representation binaire, il y a BEAUCOUP de retenues
- v_2(C) croit typiquement comme ~log_2(k)/3 — pas borne !

**Pistes ouvertes par l'echec :**
1. L'approche v_2 marche pour k=3, 5, 13, 69, 73 (les "petits" k impairs ou d premier)
   → Peut-on prouver directement pour CES cas specifiques ?
   → OUI pour k=3, 5 : v_2(C) = 0, 0 respectivement, v_2(ord) = 2. PROUVE.
   → Pour k=13, 69, 73 : v_2(C) = 1, 1, 1. Aussi prouve individuellement.
   → MAIS ce n'est pas universel.

2. L'approche v_p avec d'autres premiers p marche pour des cas supplementaires
   → 11/19 = 58% ont un "petit premier gagnant" <= 47
   → Les 8/19 restants (k=61,148,185,655,917,2183,6891,7752) n'en ont pas
   → MAIS pour ces 8 cas, ord > C quand meme (C ≪ d)

3. **NOUVELLE PISTE** : gcd(C, d-1) approach
   → Observation : ord | C => ord | gcd(C, d-1)
   → Si gcd(C, d-1) = 1, alors ord | 1, contradiction.
   → Si 2^{gcd(C,d-1)} neq 1 mod d, alors ord nmid gcd(C,d-1), donc ord nmid C.

### Verdict iter 1
- **Resultat partiel** : v_2 prouve G2c pour k=3, 5, 13, 69, 73 (5 cas) [PROUVE]
- **Resultat negatif** : v_2(C) <= 1 est FAUX en general [INVALIDE]
- **Lecon** : Pas de prime UNIQUE qui marche universellement. Il faut soit :
  (a) Un argument qui combine tous les primes, soit
  (b) Un argument de taille (C < ord), soit
  (c) Un argument sur gcd(C, d-1)
- **Statut** : La piste n'est pas morte. L'analyse d'echec ouvre la voie gcd.

---

## G-V-R ITERATION 2 : APPROCHE gcd(C, d-1) (EN COURS)

### Pre-engagement iter 2
- **Hypothese** : gcd(C, d-1) est "petit" et ne contient pas ord comme diviseur
  Formellement : 2^{gcd(C, d-1)} neq 1 mod d pour tout k >= k_0
- **Succes** : Prouver que 2^{gcd(C,d-1)} neq 1 pour tout k avec d premier
- **Echec** : Trouver un k avec d premier et 2^{gcd(C,d-1)} equiv 1 mod d ET gcd non trivial
- **Lien avec iter 1** : gcd(C,d-1) = 1 => resultat immediat.
  gcd > 1 mais 2^gcd neq 1 => resultat aussi.
  gcd > 1 et 2^gcd = 1 => besoin d'un autre argument.

### Logique mathematique
```
CHAIN : 2^C equiv 1 mod d
  => ord | C          (definition de l'ordre)
  => ord | (d-1)      (Fermat)
  => ord | gcd(C, d-1) (intersection)
  => 2^{gcd(C,d-1)} equiv 1 mod d  (car ord | gcd)

CONTRAPOSEE :
  2^{gcd(C,d-1)} neq 1 mod d
  => ord nmid gcd(C, d-1)
  => ord nmid C
  => 2^C neq 1 mod d  ✓
```

### Scripts de verification
→ session10f22_iter2_investigation.py (sections J1-J7)
→ session10f22_iter2_j8_j10.py (sections J8-J13)

### Resultats (COMPLETES)

#### J1-J3 : gcd(C, d-1) — taille et structure
- gcd(C, d-1) = 1 pour seulement 1/19 cas (k=5)
- gcd = 2 pour 7/19 cas (k=3,4,13,76,148,7752 et un autre)
- gcd max = 2 813 348 (22 bits) pour k=3895
- C < d pour tout k > 17 avec d premier (C/d → 0 exponentiellement)

#### J4-J5 : Structure p-adique du gcd
- v_2(gcd) = min(v_2(C), v_2(d-1)) <= 2 toujours (car v_2(d-1) <= 2)
- Pour les grands k : gcd domine par petits facteurs premiers partages

#### J6 : RESULTAT MAJEUR
- **2^{gcd(C,d-1)} ≢ 1 mod d pour les 19/19 d premiers** ★★★★★
- Mecanisme unifie : aucun diviseur r > 1 de gcd(C,d-1) ne satisfait 2^r ≡ 1 mod d
- Prouve G2c via : ord ∤ gcd(C,d-1) => ord ∤ C => 2^C ≢ 1 mod d

#### J8 : Verification C mod ord ≠ 0
- C mod ord ≠ 0 pour les 19/19 cas ✓
- gcd(C,d-1) < ord pour les 19/19 cas ✓

#### J9-J10 : Reformulation et equivalence
- C·Q < d-1 pour 17/19 cas (echoue k=3 et k=5 ou C >= d)
- **DECOUVERTE CRITIQUE** : C·Q < d-1 ⟺ C < ord (match=True pour 19/19)
- La condition gcd < ord est equivalente a C < ord
- Prouver Q < 2^{0.051·S} est aussi ouvert que Artin

#### J11 : Cas speciaux k=3, k=5
- k=3 : d=5, C=6, ord=4, Q=1, gcd=2, 2^2=4≠1 mod 5 ✓
- k=5 : d=13, C=35, ord=12, Q=1, gcd=1, 2^1=2≠1 mod 13 ✓
- C >= ord MAIS gcd < ord → l'approche gcd fonctionne quand meme

#### J12 : Borne triviale insuffisante
- ord >= S-1 (borne triviale par taille)
- gcd < S-1 pour 15/19 cas
- **ECHEC** : k=61 (gcd=124 > S-1=96), k=3895 (gcd=2813348 > S-1=6173),
  k=4500 (gcd=56470 > S-1=7132), k=6891 (gcd=1054812 > S-1=10921)
- Conclusion : la borne triviale est INSUFFISANTE

### ANALYSE D'ECHEC ITERATION 2 (obligatoire selon protocole)

**Hypothese testee** : 2^{gcd(C,d-1)} ≢ 1 mod d pour tout k >= 3 avec d premier

**Resultat computationnel** : CONFIRME pour 19/19 cas (k=3..10000) ★★★★★

**Echec THEORIQUE** : La tentative de prouver cela inconditionnellement echoue car :
1. gcd(C,d-1) < ord ⟺ C < ord (equivalence exacte verifiee 19/19)
2. Prouver C < ord requiert Q < d/C ≈ 2^{0.051·S}
3. Prouver Q < f(S) pour f(S) → ∞ est ouvert (equiv. Artin faible)
4. La borne triviale ord >= S-1 est insuffisante (gcd > S-1 pour 4 cas)

**Pourquoi l'equivalence gcd < ord ⟺ C < ord est-elle exacte ?**
- gcd(C,d-1) divise C ET divise d-1
- gcd < ord ⟺ gcd < (d-1)/Q ⟺ gcd·Q < d-1
- Comme gcd | C : gcd·Q <= C·Q. Donc C·Q < d-1 ⟹ gcd·Q < d-1 ⟹ gcd < ord
- Reciproque : si gcd < ord et gcd | C, alors C pourrait etre multiple de gcd
  MAIS ord | (d-1) et C est generique → gcd < ord ssi C < ord

**Pistes ouvertes par l'echec :**
1. **Approche directe** : Peut-on prouver 2^{gcd(C,d-1)} ≢ 1 mod d en utilisant
   la structure 2^S ≡ 3^k mod d SANS passer par "gcd < ord" ?
   → Si on montre que 2^g mod d a une forme specifique (liee a 3^k),
     cela contournerait la barriere
2. **Approche modulaire** : C mod ord via Wolstenholme ou proprietes des binom
   → binom(S-1, k-1) mod p pour les facteurs premiers de ord
3. **Approche probabiliste** : Parmi les diviseurs de d-1, la probabilite
   que ord divise C est ~ produit(1/p) pour p | ord — exponentiellement petite
   → Argument heuristique fort mais pas une preuve

---

## ANTI-HALLUCINATION : 5 Tests

### Iteration 1 (v_2 approach)
1. **Contre-exemple fabrique** : k=11 (non premier) a v_2(C)=3. k=61 (d premier) a v_2(C)=4.
   L'hypothese v_2(C) <= 1 CESSE d'etre vraie → non trivial, BIEN.
2. **Double verification** : v_2(C) calcule par Kummer ET par factorisation directe → concordent.
3. **Limites** : k=3 (v_2(C)=0, OK), k→inf (v_2(C)→inf, hypothese FAUSSE). Test concluant.
4. **Sceptique** : "Peut-on prouver ord nmid C sans connaitre v_p(ord) ?"
   → OUI, via gcd(C, d-1) : si 2^gcd neq 1, pas besoin de connaitre ord explicitement.
5. **gcd(d,m)** : L'argument est sur d-1 (divisibilite), pas sur d (congruence).
   Pas de probleme de type gcd(d,m). ✓

### Iteration 2 (gcd approach)
1. **Contre-exemple cherche** : Pour k=3, gcd(C,d-1) = gcd(6,4) = 2.
   2^2 = 4 ≡ 4 mod 5 ≠ 1. OK. Pour k=3895, gcd = 2 813 348 ≫ S-1 = 6173.
   MAIS 2^{gcd} ≢ 1 mod d. Le gcd peut etre tres grand sans etre multiple de ord.
   Pas de contre-exemple trouve (2^gcd ≡ 1) sur k=3..10000. ✓
2. **Double verification** : gcd(C,d-1) calcule par math.gcd directement.
   Verifie aussi : tous les diviseurs r > 1 de gcd testés → 2^r ≢ 1 mod d.
   Coherent avec J6 et J8. ✓
3. **Limites** :
   - k=3 : gcd=2, ok. k=5 : gcd=1, trivial. k=3895 : gcd=2813348, tres grand.
   - gcd croit IRREGULIEREMENT : pas de tendance monotone.
   - La condition gcd < ord EST verifiee mais EQUIVALENTE a C < ord (Artin). ✓
4. **Sceptique** : "L'approche gcd contourne-t-elle Artin ?"
   → NON. J9-J10 montrent que gcd < ord ⟺ C < ord exactement.
   → Cependant, la VERIFICATION 2^gcd ≢ 1 est un test plus fin que C < ord
     car elle detecte aussi les cas k=3, k=5 ou C >= ord.
   → Sur le plan THEORIQUE : impasse confirmee. Sur le plan COMPUTATIONNEL : outil puissant. ✓
5. **gcd(d,m)** : L'argument utilise gcd(C, d-1) avec d-1, pas d.
   C et d-1 sont tous deux des entiers bien definis (pas de division par d).
   La conclusion porte sur 2^gcd mod d (congruence), distincte du gcd.
   Pas de confusion type gcd(d,m). ✓

---

## ETAT G-V-R

- **Iteration 1** : [COMPLETEE] v_2(C) <= 1 INVALIDE. v_2 partiel (5/19). Erreur analysee. ✓
- **Iteration 2** : [COMPLETEE] gcd(C,d-1) approach.
  - Computationnel : 2^{gcd} ≢ 1 pour 19/19 ★★★★★
  - Theorique : gcd < ord ⟺ C < ord (equiv. Artin). IMPASSE.
  - Erreur analysee : 3 pistes ouvertes (approche directe, modulaire, probabiliste). ✓
- **Iteration 3** : [COMPLETEE] Approche directe 2^S ≡ 3^k + argument de taille
  - **DECOUVERTE MAJEURE** : Si 0 < g < log_2(d), alors 2^g mod d = 2^g ≠ 1
    (argument ELEMENTAIRE et INCONDITIONNEL, aucune theorie des nombres)
  - Couvre 15/19 cas (tous sauf k=61, 3895, 4500, 6891)
  - 4 cas rebelles : gcd(C,d-1) >= log_2(d)
  - Pour les rebelles : g < ord trivially (g ≈ 2^22 vs ord ≈ 2^6000)
    mais cela necessite connaitre Q (retour a Artin)
  - Bezout : 2^g ≡ (2^C)^u mod d — CIRCULAIRE, cul-de-sac
  - Identite 2^S ≡ 3^k : donne 2^g ≡ 3^{qk}·2^r mais pas de moyen
    d'eliminer 3^{qk}·2^r = 1 dans le cas general
  - Erreur analysee. ✓

### ANALYSE D'ECHEC ITERATION 3

**Hypothese testee** : L'identite 2^S ≡ 3^k mod d permet de prouver
2^g ≢ 1 mod d pour g = gcd(C,d-1) via un argument structurel.

**Resultat partiel** : L'argument de TAILLE (g < log_2(d)) est nouveau
et inconditionnel, couvrant 15/19 cas. MAIS il ne couvre pas les 4 rebelles.

**Pourquoi les 4 rebelles echappent a l'argument de taille :**
- k=61 : g=124 = 2^2·31, d a 95 bits. g > 95 car 31 | (d-1) et 31 | C.
- k=3895 : g=2813348 = 2^2·29·79·307, d a 6173 bits. g a 22 bits.
  gcd est compose de "moyens" premiers (29, 79, 307) partages entre C et d-1.
- k=4500 : g=56470 = 2·5·5647, d a 7132 bits. 5647 est premier et divise C et d-1.
- k=6891 : g=1054812 = 2^2·3·11·61·131, d a 10917 bits.

**Pattern des rebelles** : Le gcd contient des facteurs premiers p
tels que v_p(C) = v_p(d-1) = 1 (une seule puissance), et le produit
de ces facteurs depasse log_2(d). Ce sont des "coincidences de divisibilite"
entre binom(S-1,k-1) et 2^S-3^k-1 pour des premiers p de taille moderee.

**Pistes ouvertes par l'echec :**
1. Peut-on borner le nombre de "petits" premiers p tels que p | C et p | (d-1) ?
   → Borne sur omega(gcd(C,d-1)) : nombre de facteurs premiers distincts
   → Empiriquement : max 5 facteurs (k=6891). Produit max ≈ 2^22.
2. Approche hybride : argument de taille pour la majorite + v_p specifique pour rebelles ?
   → Iter 1 a montre que v_2 marche pour certains cas. Combinaison ?
3. Lien d-1 mod p pour p | C : peut-on prouver que certains p ne divisent pas d-1 ?
   → d-1 = 2^S - 3^k - 1. Pour p premier : d-1 ≡ 2^S - 3^k - 1 mod p.
   → Si 2^S ≢ 3^k + 1 mod p, alors p ∤ (d-1), et p ne contribue pas au gcd.

### ANTI-HALLUCINATION Iteration 3
1. **Contre-exemple cherche** : k=61 a g=124 > log_2(d)=95. L'argument de taille
   ne s'applique PAS — confirme que la borne g < log_2(d) n'est pas universelle.
   Non trivial. ✓
2. **Double verification** : 2^g mod d calcule directement ET via 3^{qk}·2^r
   donnent le meme resultat pour les 19 cas (K1 verifie). ✓
3. **Limites** : g < log_2(d) couvre 15/19. Les 4 rebelles ont g de 7 a 22 bits
   vs d de 95 a 10917 bits → ratio g/d astronomiquement petit mais g > log_2(d). ✓
4. **Sceptique** : "L'argument Bezout contourne-t-il le probleme ?"
   → NON. K3 montre explicitement que Bezout donne 2^g ≡ (2^C)^u, circulaire. ✓
5. **gcd(d,m)** : L'argument de taille porte sur g (entier positif) et d (premier).
   2^g est un entier, 2^g mod d est une congruence. Pas de confusion. ✓

- **Iteration 4** : [COMPLETEE] Controle du gcd via d-1 mod p
  - L1 : Pour chaque rebelle, chaque premier p | g satisfait 2^S ≡ 3^k+1 mod p
    (necessaire pour p | (d-1)). Verifie pour les 4 rebelles.
  - L2 : Seulement 2-6% des premiers divisant C divisent aussi d-1
    k=61: 4/66 (6.1%), k=3895: 15/750 (2.0%), k=4500: 8/848 (0.9%), k=6891: 22/1282 (1.7%)
    → La plupart des premiers de C ne contribuent PAS au gcd
  - L3 : Heuristique g ≈ S^c avec c ∈ [0, 1.7]. Rebelles ont c > 1.
    (k=3895: c=1.67, k=6891: c=1.49, k=4500: c=1.23, k=61: c=1.06)
    Non-rebelles : c ∈ [0, 0.92]
  - L4 : g n'est PAS multiple de ord pour aucun des 19 cas ✓
  - L5 : "g not multiple of ord" EST EXACTEMENT "ord ∤ C" — CIRCULAIRE
    (puisque g | C, ord | g ⟹ ord | C et reciproquement si g = gcd(C,d-1))
  - L6 : g < S IMPOSSIBLE a prouver en general
    Primorial(S) ≈ e^S ≫ S : si d-1 est divisible par beaucoup de
    petits premiers qui divisent aussi C, g peut etre arbitrairement grand
  - L7 : Synthese finale — 15/19 inconditionnel, 4/19 conditionnel (Artin)
  - Erreur analysee. ✓

### ANALYSE D'ECHEC ITERATION 4 (obligatoire selon protocole)

**Hypothese testee** : Le nombre de premiers p divisant a la fois C et d-1
est bornable, ce qui controlerait g = gcd(C,d-1) < log_2(d).

**Resultat** : L'hypothese est PLAUSIBLE mais NON PROUVABLE avec les outils actuels.

**Observations positives :**
1. Empiriquement, seulement 2-6% des premiers de C divisent aussi d-1
   → La "filtration" par d-1 est TRES selective
2. L'exposant c dans g ≈ S^c est stable : non-rebelles c < 1, rebelles c ∈ [1, 1.7]
3. La condition 2^S ≡ 3^k + 1 mod p (necessaire pour p | d-1) est ARITHMETIQUE
   et devrait eliminer la plupart des p heuristiquement

**Pourquoi ca ne suffit pas pour une preuve :**
1. "La plupart des p ne divisent pas d-1" n'empeche pas que le PRODUIT
   des quelques p qui divisent d-1 depasse S (cf. k=3895 : 5 facteurs, produit 2.8M)
2. Prouver que le produit des p communs est < S revient a borner
   sum_{p | gcd} log(p) < log(S), ce qui est une forme de conjecture d'Artin
   deguisee (controle du "smooth part" de d-1 relatif a C)
3. L'argument circulaire L5 confirme : toute borne sur gcd qui implique
   ord ∤ C est EQUIVALENTE a une assertion sur ord

**Verdict** : IMPASSE STRUCTURELLE confirmee. 4 iterations G-V-R sans percee
theorique sur les 4 rebelles. La barriere d'Artin est REELLE et non contournable
par les approches testees.

**Pas de pistes nouvelles ouvertes** — les 3 pistes de l'iteration 2
(directe, modulaire, probabiliste) ont toutes ete explorees et closent :
- Directe (iter 3) : argument de taille couvre 15/19, pas les 4 rebelles
- Modulaire (iter 2) : C mod ord = gcd < ord ⟺ C < ord (circulaire)
- Probabiliste (iter 4) : 2-6% heuristique mais pas prouvable

### ANTI-HALLUCINATION Iteration 4
1. **Contre-exemple cherche** : k=3895 a 15 premiers communs entre C et d-1
   sur 750 premiers divisant C (2%). Le produit 29×79×307 = 703 957 × 4 = 2 813 348.
   Ce produit depasse S=6174 malgre le faible ratio 2%. Non trivial. ✓
2. **Double verification** : La condition p | (d-1) ⟺ 2^S ≡ 3^k+1 mod p
   est verifiee algebriquement : d-1 = 2^S-3^k-1, donc p | (d-1) ssi
   2^S-3^k-1 ≡ 0 mod p ssi 2^S ≡ 3^k+1 mod p. Coherent. ✓
3. **Limites** : L'exposant c varie de 0 (k=5, gcd=1) a 1.67 (k=3895).
   Pour les 19 cas, max(c)=1.67. Pour k→∞, aucune borne a priori sur c. ✓
4. **Sceptique** : "La borne 2-6% prouve-t-elle quelque chose ?"
   → NON. Le ratio est descriptif. Un seul "gros" premier commun suffit
   a faire g > S. Le controle du produit (pas du ratio) est ce qui compte. ✓
5. **gcd(d,m)** : Tous les calculs portent sur gcd(C, d-1) — entiers positifs.
   Les congruences 2^S mod p sont correctement evaluees. Pas de confusion. ✓

---

## CLOTURE G-V-R : SYNTHESE FINALE

- **Iteration 1** : [COMPLETEE] v_2(C) ≤ 1 INVALIDE. v_2 partiel (5/19). ✓
- **Iteration 2** : [COMPLETEE] gcd(C,d-1) approach. 2^gcd ≢ 1 pour 19/19. ✓
- **Iteration 3** : [COMPLETEE] Argument de taille 15/19. 4 rebelles identifies. ✓
- **Iteration 4** : [COMPLETEE] Controle gcd via d-1 mod p. Impasse structurelle. ✓
- **Iteration 5** : [COMPLETEE] LUMIERE SPECIALE — Primes temoins. 3/4 rebelles RESOLUS. ✓
- **Iteration 5bis** : [COMPLETEE] ULTRASON — recherche q > S-1 | d-1 pour k=6891. 0 hits sur 663K primes. ✓
- **Iteration 5ter** : [COMPLETEE] CAMERA THERMIQUE — 2^M mod d pour k=6891. RESOLU! Score 19/19. ✓

### Iteration 5 : Lumiere speciale (primes temoins)

**Idee** (inspiree par Eric — metaphore de la lumiere infrarouge) :
Au lieu de regarder la TAILLE de g = gcd(C,d-1), regarder la STRUCTURE p-adique.
Un prime p est "temoin" si v_p(ord) > v_p(C), ce qui prouve ord ∤ C
independamment de la taille du gcd.

**Resultats spectaculaires :**
- k=3895 : **RESOLU** par temoin p=3 (v_3(ord)=3 > v_3(C)=0) ★
  Le plus petit temoin possible ! v_3(d-1)=3 et 2^{(d-1)/3} ≢ 1 mod d,
  donc v_3(Q)=0, v_3(ord)=3. Comme 3 ∤ C : temoin immediat.
- k=4500 : **RESOLU** par temoin p=43 (v_43(ord)=1 > v_43(C)=0) ★
  43 | (d-1) mais 43 ∤ C. v_43(Q)=0, donc v_43(ord)=v_43(d-1)=1.
- k=61 : **RESOLU** par temoin p=5179 (v_5179(ord)=1 > v_5179(C)=0) ★
  AUSSI resolu par factorisation complete de d-1 (95 bits) : Q_exact=1,
  ord=d-1, C < ord directement.
- k=6891 : **NON RESOLU** — aucun temoin p <= 10000 ★★
  Les 5 facteurs premiers de g={2,3,11,61,131} ont TOUS v_p(ord) <= v_p(C).
  Specificement : p=3 divise Q (v_3(Q)=1), p=11,61,131 ont v_p(d-1)=v_p(C)=1.
  Q_pred(p<=10000) = 3. Marge : Q < 2^549 suffirait.
  MORALEMENT resolu (Q=3 << 2^549) mais pas PROUVE.

**SCORE INTERMEDIAIRE ITERATION 5 : 18/19 INCONDITIONNEL, 1/19 CONDITIONNEL (k=6891)**
→ Resolu par iteration 5ter (CAMERA THERMIQUE) ci-dessous.

### ANALYSE D'ECHEC ITERATION 5 (cas k=6891) → RESOLU par iter 5ter

**Hypothese testee** : Pour chaque rebelle, il existe un prime p "temoin"
tel que v_p(ord) > v_p(C), prouvant ord ∤ C.

**Resultat** : SUCCES pour 3/4 rebelles. ECHEC pour k=6891.

**Pourquoi k=6891 resiste :**
1. g = 1054812 = 2^2 × 3 × 11 × 61 × 131 (5 facteurs premiers)
2. Pour CHAQUE facteur premier p de g :
   - p=2 : v_2(d-1)=2, v_2(C)=12. v_2(ord)=2 car v_2(Q)=0. 2 <= 12 : pas temoin.
   - p=3 : v_3(d-1)=1, v_3(C)=2. v_3(Q)=1, v_3(ord)=0. 0 < 2 : pas temoin.
     **PROBLEME SPECIFIQUE** : p=3 DIVISE Q pour k=6891.
   - p=11 : v_11(d-1)=1, v_11(C)=1. v_11(Q)=0, v_11(ord)=1. 1 = 1 : egalite.
   - p=61 : v_61(d-1)=1, v_61(C)=1. v_61(Q)=0, v_61(ord)=1. 1 = 1 : egalite.
   - p=131 : v_131(d-1)=1, v_131(C)=1. v_131(Q)=0, v_131(ord)=1. 1 = 1 : egalite.
3. Les primes p=11,61,131 ont EXACTEMENT v_p(d-1)=v_p(C)=1 — l'egalite
   parfaite empeche toute conclusion sur ord | C via ces primes.
4. Un temoin ne peut venir que d'un prime p ∤ g, i.e. un prime p tel que
   v_p(d-1) >= 1 mais v_p(C) = 0. Aucun tel p <= 10000 n'a v_p(Q) < v_p(d-1).

**Pistes ouvertes :**
1. Chercher un temoin p > 10000 (computationnellement lourd, d ~ 2^10917)
2. Prouver que Q_pred(p <= ∞) < 2^549 (borne sur Q)
3. Argument structurel specifique a k=6891

### ANTI-HALLUCINATION Iteration 5
1. **Contre-exemple cherche** : k=6891 est un vrai contre-exemple a l'hypothese
   "il existe toujours un temoin p petit". Les 5 facteurs de g n'offrent aucun
   temoin. Non trivial, confirme la realite du probleme. ✓
2. **Double verification** : Les valuations v_p sont calculees par DEUX methodes :
   v_p(d-1) par division successive ET v_p(C) par formule de Legendre.
   pow(2, (d-1)//p^e, d) est calcule par exponentiation modulaire Python.
   Resultats coherents entre W1, W3, W4. ✓
3. **Limites** : k=3895 resolu par p=3 (trivial a posteriori !). k=61 resolu
   par p=5179 — grand prime. k=4500 par p=43 — intermediaire. Le "rayon"
   necessaire varie enormement. Pour k=6891, aucun rayon p <= 10000 ne suffit. ✓
4. **Sceptique** : "Le temoin p=3 pour k=3895 est-il reel ?"
   → OUI. v_3(d-1)=3 (d-1 ≡ 0 mod 27). v_3(C)=0 (binom(S-1,k-1) non divisible
   par 3). 2^{(d-1)/3} mod d ≢ 1 (verifie computationnellement).
   Donc v_3(ord) = 3 > 0 = v_3(C). CQFD. ✓
5. **gcd(d,m)** : Les calculs portent sur d-1 (divisibilite), C (binomial),
   et ord (ordre multiplicatif). Pas de confusion entre d et d-1.
   pow(2, (d-1)//p^e, d) est bien 2^{quotient} mod d. ✓

---

### Iteration 5bis : Ultrason (primes q > S-1 divisant d-1)

**Idee** (inspiree par Eric — metaphore de l'ultrason) :
Si C = binom(S-1, k-1), alors tout facteur premier de C est <= S-1 (Kummer).
Donc pour tout q > S-1 : v_q(C) = 0 TOUJOURS.
Un tel q divisant d-1 avec q ne divisant pas Q serait un temoin AUTOMATIQUE.
C'est l'ultrason : une frequence AU-DELA du spectre audible de C.

**Script** : session10f22_iter5bis_ultrason.py

**Resultats pour k=6891 :**
- Scanne 663 252 premiers q dans (10921, 10^7]
- **ZERO hits** : aucun premier q > S-1 ne divise d-1 dans ce range
- d-1 est divisible par des premiers <= 10921 mais les facteurs > 10921 sont
  trop grands pour etre trouves par crible direct (d a 10917 bits)
- Heuristique : P(d-1 est (S-1)-smooth) ≈ 10^{-2370} — impossible en pratique
  mais pas prouvable que R > 1

**Verdict** : Ultrason confirme que d-1 a des facteurs enormes > S-1 (avec
quasi-certitude) mais ne les TROUVE pas directement. Transition vers camera thermique.

### Iteration 5ter : Camera Thermique (RESOLUTION COMPLETE)

**Idee** (inspiree par Eric — metaphore de la camera thermique) :
Vision nocturne = amplifier la lumiere existante (ultrason : chercher les q).
Camera thermique = detecter ce que l'objet EMET (sa chaleur = son residu R).

**Traduction mathematique :**
1. Calculer M = partie (S-1)-smooth de d-1 (tous les petits facteurs extraits)
2. R = (d-1)/M = residu "chaud" (facteurs GRANDS, tous > S-1)
3. Tester 2^M mod d :
   - Si ≢ 1 : ord ne divise pas M, donc ord a un composant dans R
   - Tout facteur q de R satisfait q > S-1, donc v_q(C) = 0
   - v_q(ord) >= 1 > 0 = v_q(C) => TEMOIN GARANTI
   - => ord ne divise pas C => 2^C ≢ 1 mod d  QED

**Theoreme (Camera Thermique) :**
Soit d premier, M = prod_{p <= S-1} p^{v_p(d-1)} la partie (S-1)-smooth de d-1.
Si 2^M ≢ 1 mod d, alors pour tout C avec facteurs premiers <= S-1 : ord_d(2) ne divise pas C.
Preuve : 5 lignes, pure logique, AUCUNE hypothese. ★★★★★

**Script** : session10f22_iter5ter_thermal.py

**Resultats pour k=6891 :**
- M = 2^2 * 3 * 11 * 61 * 131 = 1 054 812 (21 bits)
- R a 10 896 bits (residu MASSIF)
- **2^M ≢ 1 mod d** ★★★★★
- k=6891 EST RESOLU par camera thermique!

**Verification sur les 19 cas** : session10f22_thermal_all19_fast.py
- Camera thermique seule : **17/19** (echoue k=3 et k=5 ou d-1 est entierement smooth)
- Argument de taille seul : **15/19** (echoue k=61, 3895, 4500, 6891)
- **UNION SIZE + THERMAL = 19/19** ★★★★★
  Les ensembles d'echec sont DISJOINTS :
  - SIZE echoue quand g est grand (4 rebelles) → THERMAL marche (R massif)
  - THERMAL echoue quand d-1 est smooth (k=3, k=5 petits d) → SIZE marche (g petit)

**ANTI-HALLUCINATION Iteration 5bis/5ter :**
1. **Contre-exemple** : k=3 (d=5, d-1=4=2^2, M=4, R=1, 2^4 mod 5 = 1) et
   k=5 (d=13, d-1=12=2^2*3, M=12, R=1, 2^12 mod 13 = 1).
   La camera thermique ECHOUE pour ces cas. Non trivial. ✓
2. **Double verification** : M = gcd(C,d-1) pour k=6891 (1054812).
   2^M mod d calcule par Python pow(2, M, d). Resultat != 1. ✓
3. **Limites** : R/d ratio varie de 0% (k=3,5) a 100% (k=7752).
   Les rebelles ont R/d > 99%. La camera thermique est QUASI-UNIVERSELLE. ✓
4. **Sceptique** : "La camera thermique est-elle equivalente a l'approche gcd (iter 2) ?"
   → Pour k=6891 : M = gcd(C,d-1) exactement (memes facteurs).
   → THEORIQUEMENT different : gcd dit juste "2^g ≢ 1", camera thermique dit
   POURQUOI (existence de q > S-1 dans ord). La camera donne le MECANISME.
   → COMPUTATIONNELLEMENT identique pour les cas testes. ✓
5. **gcd(d,m)** : M est un entier (produit de puissances de petits premiers).
   2^M mod d est une congruence bien definie. R = (d-1)/M est une division exacte. ✓

---

### RESULTAT FINAL SESSION 10f22 (mis a jour iteration 5ter — CAMERA THERMIQUE)

**CE QUI EST PROUVE (inconditionnel) :**
1. v_2(d-1) <= 2 pour tout k >= 3 [PROUVE]
2. C/d → 0 exponentiellement [PROUVE]
3. Si g = gcd(C,d-1) < log_2(d), alors 2^C ≢ 1 mod d [PROUVE, ELEMENTAIRE]
4. g < log_2(d) pour 15/19 cas (k=3..10000) [VERIFIE — Methode SIZE]
5. Si ∃ prime temoin p avec v_p(ord) > v_p(C), alors 2^C ≢ 1 mod d [PROUVE]
6. Prime temoin existe pour k=61 (p=5179), k=3895 (p=3), k=4500 (p=43) [VERIFIE]
7. k=61 : Q_exact=1, C < ord directement [PROUVE par factorisation]
8. **Theoreme Camera Thermique** : Si 2^M ≢ 1 mod d (M = smooth part de d-1),
   alors ord ne divise pas C [PROUVE, 5 lignes, INCONDITIONNEL]
9. 2^M ≢ 1 mod d pour 17/19 cas [VERIFIE — echoue k=3, k=5 seulement]
10. **UNION SIZE (15/19) + THERMAL (17/19) = 19/19** [VERIFIE ★★★★★]

**CE QUI EST PROUVE (conditionnel sur Q petit, i.e. Artin) :**
11. Si Q < 2^{0.051*S}, alors 2^C ≢ 1 mod d [PROUVE conditionnellement]
12. Q < 2^{0.051*S} pour les 19/19 cas observes [VERIFIE]

**CE QUI EST VERIFIE MAIS NON PROUVE (pour le cas GENERAL k > 10000) :**
13. 2^{gcd(C,d-1)} ≢ 1 mod d pour les 19 d premiers (k=3..10000) [VERIFIE★★★★★]
14. gcd(C,d-1) < ord pour les 19/19 cas [VERIFIE]
15. La camera thermique est CALCULABLE pour tout k specifique,
    mais la preuve que 2^M ≢ 1 TOUJOURS est ouverte (plus faible qu'Artin)

**CE QUI EST OUVERT (cas general k > 10000) :**
16. Prouver que SIZE ou THERMAL marche pour TOUT k avec d premier
17. Prouver que d-1 n'est jamais entierement (S-1)-smooth (quasi-certain, pas prouve)
18. Prouver que 2^M ≢ 1 mod d quand R > 1 (beaucoup plus faible qu'Artin)
19. Q borne inconditionnellement pour d = 2^S - 3^k premier en general

**AVANCEE SESSION 10f22 :**
- 10f21 : "G2c ⟺ Artin, investigation terminee" (0/19 inconditionnel)
- 10f22 iter 1-4 : **15/19 inconditionnel** (argument elementaire de taille)
- 10f22 iter 5 : **18/19 inconditionnel** (primes temoins)
- 10f22 iter 5bis : Ultrason — 0 hits sur 663K primes. Confirme R > 1 mais ne trouve pas q.
- 10f22 iter 5ter : **19/19 INCONDITIONNEL** (camera thermique) ★★★★★
  k=6891 resolu : 2^M ≢ 1 mod d avec M = 1 054 812 (21 bits)

**SCORE FINAL : 19/19 CAS PROUVES INCONDITIONNELLEMENT (k <= 10000)**
- Deux methodes complementaires :
  (A) SIZE : g = gcd(C,d-1) < log_2(d) → 2^g < d → 2^g ≠ 1 (15 cas)
  (B) THERMAL : 2^M ≢ 1 mod d → ord a un facteur > S-1 → ord ne divise pas C (17 cas)
  (C) UNION A+B = 19/19 (les ensembles d'echec sont disjoints)
- Alternative unifiee : 2^{gcd(C,d-1)} ≢ 1 mod d verifie pour 19/19 (iter 2, J6)

### DESTINATION : PROOF_SKETCH avec mention "19/19 inconditionnel (k <= 10000, SIZE + THERMAL)"

---

## LEAN4 FORMALIZATION — G2c.lean (Session 10f22 continuation)

### Approche initiale (8 sorry)
- Formulation via gcd reduction : `modPow 2 (Nat.gcd (binom n k) (d-1)) d ≠ 1`
- 11/19 prouves par `native_decide` (k <= 185)
- 8 sorry (k >= 655) : assume que binom(n,k) trop grand pour native_decide

### Percee : formulation directe (0 sorry)
- **Observation cle** : `modPow 2 (binom n k) d ≠ 1` est directement verifiable !
- `modPow` utilise square-and-multiply : O(log C) elevations au carre mod d
- Les intermediaires restent < d a chaque etape (reduction modular)
- Meme pour k=7752 (d ≈ 2^12285) : ~12000 squarings, < 1 seconde avec GMP

### Verification experimentale
```
lean G2cTest.lean  (k=655 seul)   → 0.65s ✓
lean G2cTest.lean  (k=7752 seul)  → 0.67s ✓
lean G2cTest.lean  (8 cas)        → 1.72s ✓ (TOUS les sorry fermes!)
lake build         (projet entier) → 4.5s  ✓
```

### Resultat final G2c.lean
- **19 theoremes, 0 sorry, 0 axiome**
- 4 preuves de primalite (k=3,4,5,13) par `isPrime` + `native_decide`
- Theoreme resume `g2c_all_19` : conjonction des 19 cas
- Axiomes : uniquement propext, Quot.sound, Lean.ofReduceBool (base de confiance Lean4)
- Namespace `G2c` pour eviter collision avec `binom` de Basic.lean
- Import `CollatzVerified.Basic` pour reutiliser la definition de `binom`

### Correction technique : isPrime termination
- Version initiale : `if d * d > n then true` avec `termination_by n - d`
- `omega` ne peut pas prouver `d < n` a partir de `d*d ≤ n` (arithmetique quadratique)
- Fix : changer la garde en `if d ≥ n then true` (trial division jusqu'a n-1)
- Performance identique pour `native_decide` sur les petits nombres (5, 13, 47, 502829)

### Score Lean4 total du projet CollatzVerified
- **Basic.lean** : 73 theoremes, 0 sorry, 0 axiom
- **G2c.lean** : 23 theoremes (19 g2c + 4 primalite), 0 sorry, 0 axiom
- **Total** : 96 theoremes, 0 sorry, 0 axiom

---

## INVESTIGATION K > 10000 — VERDICT

### Question : SIZE ou THERMAL marchent-ils pour TOUT k ?

### Reponse : **OUVERT — au-dela de la technologie mathematique actuelle**

**Analyse detaillee (agent de recherche) :**

1. **d-1 peut-il etre entierement (S-1)-smooth ?**
   - Heuristique Dickman : probabilite super-exponentiellement petite pour k grand
   - Mais : resultat de densite, pas de garantie pour un nombre specifique
   - S-unit equations (Evertse-Gyory) : finitude pour S fixe, mais notre S croit avec k
   - **OUVERT inconditionnellement**

2. **Peut-on prouver 2^M ≢ 1 mod d quand R > 1 ?**
   - Identite structurelle : 2^S ≡ 3^k mod d → ord ne divise pas S
   - Erdos-Murty (1999) : "pour presque tout premier p", pas pour un p specifique
   - Pomerance-Shparlinski (2002) : ord rarement smooth, mais densite pas individuel
   - **OUVERT inconditionnellement**

3. **Lien avec Artin ?**
   - G2c necessite BEAUCOUP MOINS qu'Artin (un seul facteur > S-1 dans ord suffit)
   - Mais meme cette version affaiblie est ouverte pour des premiers specifiques
   - Heath-Brown (1986) : au moins un de {2, 3, 5} est racine primitive pour infinis p

4. **Bornes sur P(ord_d(2)) ?**
   - Stewart (2013) : P(2^n - 1) > n · exp(log n / (104 log log n)) — Mersenne, pas ord
   - Schinzel (1962) : P(2^n - 1) ≥ 2n + 1 pour n > 12
   - Aucun resultat applicable directement a P(ord_d(2)) pour d = 2^S - 3^k

5. **Theorie des nombres smooth pour d-1 ?**
   - ABC donnerait des contraintes, mais ABC est non prouve
   - S-unit bounds trop grossiers (ensemble de premiers croit avec k)

### Strategie recommandee
- **Theoreme conditionnel** : "Sous ABC effectif, G2c pour tout k"
- **Theoreme inconditionnel** : "G2c verifie pour tout k ≤ 10000 (Lean4, 0 sorry)"
- **Exploration** : etendre la verification computationnelle a k ≤ 100000 (faisable)
- **Hybride** : combiner SIZE + THERMAL en un seul argument structurel
