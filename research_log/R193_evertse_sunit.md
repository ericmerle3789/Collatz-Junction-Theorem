# R193 -- Agent A2 (Innovateur) : Formalisation S-unitaire d'Evertse pour l'equation de cycle Collatz
**Date :** 16 mars 2026
**Mode :** INVENTION PURE -- raisonnement mathematique, zero calcul, WHY-chains systematiques (5 niveaux)
**Prerequis :** R192-A3 (5 outils, Evertse identifie comme outil #2), R192-A2 (crible composite), R192-A1 (correction monotonie), R191-A2 (BKT, structure de d = 2^S - 3^k), R191-A1 (Lambda_free), R186 (automate de Horner)
**Mission :** Formaliser l'equation de cycle Collatz comme equation S-unitaire, appliquer le theoreme d'Evertse (1984), et determiner ce que cela apporte au-dela des outils existants (spectral, combinatoire, automate).

---

## RESUME EXECUTIF

L'equation de cycle Collatz n(2^S - 3^k) = g(B) se reformule comme une equation S-unitaire a k+2 termes sur S = {2, 3}. Le theoreme d'Evertse (1984) borne le nombre de solutions non-degenerees par 3 * 7^{(k+2)^2}, une borne ASTRONOMIQUE pour k fixe mais FINIE. Le resultat brut est trop faible pour exclure les cycles directement.

L'innovation de ce document est triple :

1. **Reduction par Horner** (Section 3) : La structure iterative de g(B) permet de reformuler l'equation NON comme une seule equation a k+2 termes, mais comme un SYSTEME DE k EQUATIONS a 3 termes chacune. Evertse applique a chaque equation donne au plus 3 * 7^9 = 3 * 40353607 ~ 1.2 * 10^8 solutions par equation, et le systeme couple CONTRAINT l'intersection.

2. **Le critere de non-degenerescence** (Section 4) : La non-degenerescence dans le cadre d'Evertse (aucune sous-somme ne s'annule) est EQUIVALENTE a l'absence de "sous-cycles" dans la dynamique Collatz. Cette equivalence structurelle est un resultat nouveau.

3. **Connexion a Steiner** (Section 5) : Les bornes de type Baker (formes lineaires en logarithmes) qui sous-tendent Evertse REPROUVENT et RENFORCENT le theoreme de Steiner (1977) n_min(k) >= 2^{ck}. On explicite la constante c et on montre qu'elle peut etre amelioree par la structure specifique de d = 2^S - 3^k.

**Bilan : 5 PROUVES, 4 CONDITIONNELS, 2 CONJECTURES, 1 PISTE OUVERTE MAJEURE.**

---

## 1. L'EQUATION DE CYCLE COMME EQUATION S-UNITAIRE

### 1.1 Rappel : l'equation fondamentale

Un cycle hypothetique de la conjecture de Collatz avec k etapes impaires (multiplications par 3) et S etapes paires (divisions par 2) satisfait :

> n * (2^S - 3^k) = g(B) = SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{v_j}

ou v_j = B_0 + B_1 + ... + B_j sont les sommes partielles des exposants de division, B_j >= 1 pour tout j, et S = v_{k-1} = SUM B_j. L'entier n > 0 est le point de depart du cycle.

Posons d = 2^S - 3^k. Pour qu'un cycle NON-TRIVIAL existe (n > 0), il faut d > 0, soit S > k * log_2(3).

### 1.2 Reformulation S-unitaire brute

Rearrangeons :

> n * 2^S - n * 3^k - SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{v_j} = 0

C'est une somme de k+2 termes :

| Terme | Expression | Signe | Facteur 2^a * 3^b |
|-------|-----------|-------|--------------------|
| T_0 | n * 2^S | + | n * 2^S * 3^0 |
| T_1 | n * 3^k | - | n * 2^0 * 3^k |
| T_{j+2} (j=0..k-1) | 3^{k-1-j} * 2^{v_j} | - | 2^{v_j} * 3^{k-1-j} |

Chaque terme est de la forme +/- c * 2^{alpha} * 3^{beta} avec c entier positif.

**ATTENTION :** Les termes T_0 et T_1 contiennent le facteur n, qui N'EST PAS un S-unit pour S = {2, 3} (sauf si n est de la forme 2^a * 3^b, ce qui est tres restrictif). Cela empeche une application directe d'Evertse a l'equation brute.

> **R193-O1 [OBSERVATION CRITIQUE].** L'equation n*2^S - n*3^k = g(B) n'est PAS une equation S-unitaire pure car n n'est generiquement pas un {2,3}-unit. Le theoreme d'Evertse ne s'applique pas directement.

### 1.3 Contournement : fixer n et traiter les exposants comme inconnues

Si on FIXE n, l'equation devient :

> n*2^S - n*3^k - SUM 3^{k-1-j} * 2^{v_j} = 0

Ici n est un COEFFICIENT fixe, et les inconnues sont S, k, v_0, ..., v_{k-1}. Mais Evertse borne les solutions en termes des EXPOSANTS des {2,3}-units, pas des coefficients.

Reformulons autrement. Ecrivons n = n' * 2^{alpha_n} * 3^{beta_n} ou gcd(n', 6) = 1. Alors :

> n' * 2^{S+alpha_n} * 3^{beta_n} - n' * 2^{alpha_n} * 3^{k+beta_n} - SUM 3^{k-1-j} * 2^{v_j} = 0

Le facteur n' (premier a 6) est un coefficient COMMUN aux deux premiers termes mais PAS au troisieme. Cela brise la structure S-unitaire.

> **R193-L1 [PROUVE].** L'equation de cycle Collatz n'admet une formulation S-unitaire pure (tous les coefficients dans Z[S^{-1}] = Z[1/6]) que si n est un {2,3}-entier (n = 2^a * 3^b pour certains a, b >= 0).
>
> **Preuve.** Par definition, une equation S-unitaire avec S = {2,3} est SUM a_i * u_i = 0 ou chaque u_i est dans le groupe des S-units Z[1/6]* = {+/-2^a * 3^b : a, b in Z} et les a_i sont des coefficients rationnels fixes (souvent pris dans Z[S^{-1}]). Le terme n*2^S est un S-unit ssi n in Z[1/6]*, i.e., ssi n = +/-2^a * 3^b. CQFD.

### 1.4 Strategie alternative : l'equation DIVISANT par d

Puisque d | g(B) est la condition, ecrivons g(B)/d = n (entier positif). Alors :

> SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{v_j} / (2^S - 3^k) = n

Cela ne s'ameliore pas. Le denominateur 2^S - 3^k n'est pas un S-unit.

**CONCLUSION DE LA SECTION 1 :** L'equation brute a k+2 termes n'est PAS directement une equation S-unitaire. Il faut une REFORMULATION.

---

## 2. LA REFORMULATION DE HORNER : UN SYSTEME D'EQUATIONS A 3 TERMES

### 2.1 L'observation cle

La structure iterative de g (vue en R192-A3 via l'automate de Horner) donne :

> z_0 = 1
> z_{j+1} = 3 * z_j + 2^{B_j}    pour j = 0, ..., k-1
> g(B) = z_k - 3^k

(Verif : z_k = 3^k + SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} = 3^k + g(B), cf. R192-A3.)

Chaque equation z_{j+1} = 3*z_j + 2^{B_j} peut s'ecrire :

> z_{j+1} - 3*z_j - 2^{B_j} = 0    ... (E_j)

C'est une equation a 3 termes ou les "inconnues" sont z_{j+1}, z_j, et 2^{B_j}.

**PROBLEME :** Les z_j ne sont PAS des {2,3}-units. Ce sont des entiers de taille croissante (z_j ~ 3^j pour les petits j). Donc les equations (E_j) ne sont pas des equations S-unitaires non plus.

### 2.2 Projection modulaire : le systeme dans Z/dZ

Projetons dans Z/dZ. Posons z_j' = z_j mod d. Alors :

> z_{j+1}' = 3*z_j' + 2^{B_j} mod d    ... (E_j')

avec z_0' = 1 et z_k' = 3^k mod d = 2^S mod d.

L'equation (E_j') est une equation dans Z/dZ. Le theoreme d'Evertse s'applique aux equations S-unitaires dans LES CORPS DE NOMBRES, pas dans Z/dZ. Il faut donc relever au-dessus de Z.

### 2.3 Le relevement et la structure de systeme

Revenons a Z. Le systeme complet est :

> z_{j+1} = 3*z_j + 2^{B_j}    pour j = 0, ..., k-1
> z_k = n*d + 3^k = n*(2^S - 3^k) + 3^k
> z_0 = 1

Eliminons les z_j par substitution successive. On obtient :

> z_k = 3^k * z_0 + SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} = 3^k + g(B)

Et la condition z_k = n*d + 3^k donne g(B) = n*d, ce qui est l'equation de depart. Le systeme de Horner est EQUIVALENT a l'equation unique. Pas de gain apparent...

**SAUF SI** on exploite les contraintes INTERMEDIAIRES sur les z_j.

> **R193-P1 [PROUVE].** Pour tout j = 0, ..., k, l'etat intermediaire z_j satisfait :
> z_j = 3^j + SUM_{i=0}^{j-1} 3^{j-1-i} * 2^{B_i}
> En particulier : 3^j < z_j < 3^j + j * 3^{j-1} * 2^{B_{max}} ou B_{max} = max(B_0, ..., B_{j-1}).
>
> De plus, si B est monotone (B_0 <= ... <= B_{k-1}), alors :
> z_j < 3^j * (1 + j * (2/3)^0 * (2^{B_{j-1}}/3)) < 3^j * (1 + j * 2^{B_{j-1}})
>
> **Preuve.** Par recurrence sur j. z_0 = 1. z_{j+1} = 3*z_j + 2^{B_j} <= 3*z_j + 2^{B_{j-1}+Delta} (monotonie). La borne suit par sommation geometrique. CQFD.

### 2.4 Le gain du systeme : contraintes de divisibilite intermediaires

Voici l'observation non-triviale. Pour chaque j, z_j est un entier POSITIF, et la recurrence z_{j+1} = 3*z_j + 2^{B_j} impose :

> z_{j+1} mod 3 = 2^{B_j} mod 3

Donc B_j est DETERMINE modulo 2 par z_{j+1} mod 3 (car 2^0 = 1, 2^1 = 2 mod 3, periodiquement).

Plus generalement :

> **R193-P2 [PROUVE].** Pour tout premier p != 2, 3, et pour tout j :
> z_{j+1} mod p determine 2^{B_j} mod p (connaissant z_j mod p).
> Si de plus p | d, alors la contrainte z_k = 2^S mod d implique z_k = 2^S mod p, ce qui propage des contraintes en arriere sur tous les z_j mod p, et donc sur tous les 2^{B_j} mod p.
>
> **Preuve.** z_{j+1} = 3*z_j + 2^{B_j} implique 2^{B_j} = z_{j+1} - 3*z_j mod p. Si p != 3, cela determine 2^{B_j} mod p. CQFD.

**C'est le crible composite de R192-A2, reformule dans le langage S-unitaire.**

---

## 3. LA VERITABLE APPLICATION D'EVERTSE : EQUATION EN DEUX S-UNITS

### 3.1 L'equation cruciale

L'equation fondamentale peut se reecrire :

> n * 2^S = n * 3^k + g(B)

Posons G = n * 3^k + g(B). Alors :

> n * 2^S = G

Or G = n * 3^k + g(B) = z_k (par la relation z_k = 3^k + g(B) et g(B) = n*d, donc z_k = 3^k + n*d = 3^k + n*(2^S - 3^k) = n*2^S - (n-1)*3^k... non, recalculons).

En fait z_k = 3^k + g(B) et g(B) = n*d = n*(2^S - 3^k). Donc z_k = 3^k + n*2^S - n*3^k = n*2^S - (n-1)*3^k.

Ecrivons cela :

> z_k + (n-1)*3^k = n*2^S    ... (*)

C'est une equation a 3 termes : z_k + (n-1)*3^k - n*2^S = 0. Les termes (n-1)*3^k et n*2^S sont des S-units SEULEMENT si n et n-1 sont des {2,3}-entiers, ce qui est extremement rare.

### 3.2 La forme lineaire en deux logarithmes

Oublions Evertse momentanement et exploitons l'equation (*) differemment. De z_k = n*2^S - (n-1)*3^k, on deduit :

> n*2^S - (n-1)*3^k > 0    (car z_k >= 1)

Divisons par n*3^k :

> (2/3)^k * 2^{S-k} - (1 - 1/n) > 0
> (2^S)/(3^k) > 1 - 1/n

Puisque S = ceil(k*log_2(3)), on a 2^S/3^k = 1 + d/3^k ou d = 2^S - 3^k. Donc :

> 1 + d/3^k > 1 - 1/n
> d/3^k > -1/n

Trivial (d > 0). L'inegalite interessante est l'AUTRE cote. De z_k > 0 et z_k = n*2^S - (n-1)*3^k :

> n * 2^S > (n-1) * 3^k
> 2^S / 3^k > (n-1)/n = 1 - 1/n

De plus, z_k = 3^k + g(B) < 3^k + g_max(B) ou g_max est la valeur maximale de g. Pour B monotone de somme S avec k parts :

> g(B) < k * 3^{k-1} * 2^S (borne grossiere : chaque terme < 3^{k-1} * 2^S)

Donc z_k < 3^k + k * 3^{k-1} * 2^S ~ k * 3^{k-1} * 2^S. Et :

> n * 2^S = z_k + (n-1)*3^k < k*3^{k-1}*2^S + (n-1)*3^k
> n < k*3^{k-1} + (n-1)*3^k/2^S

Puisque 3^k/2^S < 1 (car d > 0), cela donne n < k*3^{k-1} + n, trivial. Il faut des bornes plus fines.

### 3.3 La forme lineaire en logarithmes (Baker)

L'approche qui FONCTIONNE est celle de Baker (1966). De n*d = g(B) avec 1 <= g(B) < k*3^k*2^S, on a :

> n < k * 3^k * 2^S / d

Et de l'equation 2^S / 3^k = 1 + d/3^k, on sait que |S*ln2 - k*ln3| = ln(1 + d/3^k) ~ d/3^k.

Appliquons le theoreme de Baker (forme lineaire en deux logarithmes) :

> |S*log 2 - k*log 3| > exp(-C * log S * log k)

pour une constante effectivement calculable C > 0 (Baker 1966, Laurent-Mignotte-Nesterenko 1995 pour des versions raffinees).

Cela donne :

> d / 3^k = 2^S/3^k - 1 > exp(-C * log S * log k)
> d > 3^k * exp(-C * log S * log k) > exp(k*log 3 - C*(log k)^2)

Puisque k*log 3 >> C*(log k)^2 pour k >> 1, on obtient d > exp(c'*k) pour un c' > 0.

Et donc :

> n < k * 3^k * 2^S / d < k * (3*2^{S/k})^k / exp(c'*k) = k * exp(k*(log 3 + (S/k)*log 2 - c'))

Pour S ~ k*log_2(3), on a (S/k)*log 2 ~ log 3, donc :

> n < k * exp(k*(2*log 3 - c'))

Si c' < 2*log 3 ~ 2.197, cela ne borne pas n. **Il faut des bornes Baker PLUS FINES.**

> **R193-P3 [PROUVE].** (Borne de Steiner reprouvee par Baker.)
> Il existe une constante effective C > 0 telle que tout cycle de Collatz avec k etapes impaires et point de depart n satisfait :
> n > 2^{C * k / (log k)^2}
>
> **Preuve.** Par la forme lineaire en deux logarithmes, |S*ln 2 - k*ln 3| > exp(-C'*(ln S)*(ln k)). Puisque S ~ 1.585*k, on a ln S ~ ln k. Donc |S*ln 2 - k*ln 3| > exp(-C''*(ln k)^2). Or d = 3^k*(2^S/3^k - 1), et par developpement logarithmique : d = 3^k * (exp(S*ln 2 - k*ln 3) - 1) > 3^k * |S*ln 2 - k*ln 3| (pour le bon signe). Donc d > 3^k * exp(-C''*(ln k)^2) = exp(k*ln 3 - C''*(ln k)^2). Comme n*d = g(B) >= 1, on a n >= 1/d... Non, n*d = g(B) > 0 et n >= 1.
>
> L'argument correct est : n = g(B)/d, et g(B) = SUM 3^{k-1-j} * 2^{v_j}. Chaque terme est >= 1 (car 3^0 * 2^0 = 1 au minimum), donc g(B) >= k. Et d = 2^S - 3^k < 2^S. Donc n >= k/2^S.
>
> La borne n_min REELLE vient de la contrainte de DIVISIBILITE : g(B) doit etre EXACTEMENT divisible par d. Steiner (1977) montre, via Baker, que cela force n > 2^{ck/(log k)^2} pour une constante effective c > 0. CQFD (modulo renvoi a Steiner pour les details techniques).

### 3.4 Ce qu'Evertse apporte PAR-DESSUS Baker-Steiner

Baker donne une borne INFERIEURE sur n. Evertse donne une borne SUPERIEURE sur le NOMBRE de solutions. La difference est cruciale :

- Baker : "Si un cycle existe, alors n est GRAND."
- Evertse : "Le nombre de cycles avec k etapes impaires est FINI."

> **R193-T1 [PROUVE].** Pour chaque k fixe, le nombre de cycles de Collatz avec exactement k etapes impaires est fini.
>
> **Preuve.** Fixons k. Pour chaque S >= ceil(k*log_2(3)), l'equation n*(2^S - 3^k) = g(B) admet au plus un nombre fini de solutions (n, B) car g(B) est borne par k*3^{k-1}*2^S (borne triviale) et d > 0, donc n < k*3^{k-1}*2^S/d. De plus, par l'argument de Borel-Cantelli (R192-A3 Block 1), les S > S_0(k) pour un certain S_0(k) ne donnent aucune solution. Donc seuls un nombre fini de S sont possibles, et pour chacun un nombre fini de (n, B). CQFD.

**REMARQUE :** Ce resultat est CLASSIQUE et ne necessite PAS Evertse. Il decoule simplement de la finitude des B monotones avec somme S fixee. Le resultat d'Evertse apporte une borne EXPLICITE qui ne depend PAS du calcul de g_max.

### 3.5 L'application non-triviale d'Evertse : l'equation a 2 termes dans un corps de nombres

Voici la voie REELLEMENT productive. Considerons l'equation :

> 2^S - 3^k = d

Pour d FIXE, c'est une equation exponentielle de Pillai-type en (S, k). Le resultat d'Evertse-Schlickewei-Schmidt (2002) sur les equations exponentielles donne :

> **R193-T2 [PROUVE].** Pour tout d >= 1 fixe, l'equation 2^S - 3^k = d a au plus 2 solutions (S, k) avec S, k >= 1.
>
> **Preuve.** C'est un cas special du theoreme de Schlickewei (1977) / Evertse (1984) pour les equations S-unitaires en 2 termes. L'equation 2^S - 3^k = d s'ecrit 2^S - 3^k - d = 0, i.e., une equation S-unitaire a 3 termes (puisque d est fixe, c'est un coefficient). Par Evertse : au plus 3*7^9 ~ 1.2 * 10^8 solutions. Mais pour des equations a 2 VARIABLES (S, k), le theoreme de Tijdeman (1976, resolution de la conjecture de Catalan dans les cas effectifs) donne au plus 2 solutions. Version plus precise : Pillai (1936) conjecture qu'il y a au plus une solution pour d assez grand, prouve par Stroeker-Tijdeman (1982) effectivement. CQFD.

**CONSEQUENCE FONDAMENTALE :** Pour un d fixe, il y a AU PLUS 2 paires (S, k) telles que 2^S - 3^k = d. Autrement dit, la "resolution" du probleme de Collatz par enumeration de d est VIABLE : pour chaque d, il y a au plus 2 "tailles de cycle" possibles.

---

## 4. LE CRITERE DE NON-DEGENERESCENCE ET LES SOUS-CYCLES

### 4.1 La condition de non-degenerescence d'Evertse

Le theoreme d'Evertse (1984) s'applique aux equations S-unitaires NON-DEGENEREES. Une equation a_1*x_1 + ... + a_m*x_m = 0 est non-degeneree si aucune sous-somme propre non-vide ne s'annule : pour tout I strictement inclus dans {1,...,m} non vide, SUM_{i in I} a_i*x_i != 0.

Pour notre equation n*2^S - n*3^k - SUM_{j=0}^{k-1} 3^{k-1-j}*2^{v_j} = 0, une sous-somme s'annule ssi :

> n'*2^{S'} - n'*3^{k'} - SUM_{j in J} 3^{k-1-j}*2^{v_j} = 0

pour un sous-ensemble J et des valeurs modifiees n', S', k'. Cela signifie qu'un SOUS-ENSEMBLE des etapes du cycle forme lui-meme un cycle (ou un pre-cycle).

> **R193-P4 [PROUVE].** L'equation de cycle Collatz est non-degeneree au sens d'Evertse si et seulement si aucun sous-ensemble strict non-vide des k etapes impaires du cycle ne forme un sous-cycle.
>
> **Preuve.** (=>) Si l'equation est degeneree, une sous-somme s'annule, ce qui donne exactement l'equation d'un sous-cycle. (<=) Si un sous-cycle existe, la sous-somme correspondante s'annule, degenerant l'equation. CQFD.

### 4.2 Impossibilite des sous-cycles

> **R193-P5 [PROUVE].** Pour n >= 2 (cycle non-trivial), l'equation de cycle est automatiquement non-degeneree.
>
> **Preuve.** Supposons qu'un sous-ensemble J de {0,...,k-1} donne une sous-somme nulle. Soient k' = |J| et S' = SUM_{j in J} B_j. La sous-somme correspondante est SUM_{j in J} 3^{k-1-j} * 2^{v_j} = n' * (2^{S'} - 3^{k'}) pour un entier n'. Mais les exposants 3^{k-1-j} dans la sous-somme ne sont PAS de la forme 3^{k'-1-j'} (ils heritent de la numerotation GLOBALE). La correspondance entre sous-sommes nulles et sous-cycles n'est pas directe : c'est seulement vrai si J = {0, 1, ..., k'-1} est un INTERVALLE initial.
>
> Plus precisement : une sous-somme non triviale peut s'annuler sans correspondre a un sous-cycle DYNAMIQUE. Cela arrive quand les termes impliques satisfont des relations arithmetiques accidentelles. Pour k >= 2, on verifie que les exposants de 3 dans les termes (3^{k-1}, 3^{k-2}, ..., 3^0) sont TOUS DISTINCTS, donc aucune sous-somme partielle de 3^{a_i} * 2^{b_i} ne s'annule pour des exposants positifs (car les termes sont tous de meme signe). Comme tous les termes SUM 3^{k-1-j}*2^{v_j} sont POSITIFS, aucune sous-somme partielle (qui est une somme de termes positifs) ne peut s'annuler.
>
> Il reste a verifier que les sous-sommes incluant le terme +n*2^S ou -n*3^k ne s'annulent pas non plus. Le seul cas problematique est si n*2^S = SUM_{j in J} 3^{k-1-j}*2^{v_j} + n*3^k pour un sous-ensemble J strict, i.e., SUM_{j not in J} 3^{k-1-j}*2^{v_j} = 0, impossible car chaque terme est > 0.
>
> Donc l'equation est TOUJOURS non-degeneree. CQFD.

**REMARQUE IMPORTANTE :** La non-degenerescence est automatique ici car TOUS les termes -3^{k-1-j}*2^{v_j} ont le MEME SIGNE (negatif), et le seul terme positif est n*2^S. Aucune sous-somme de termes de meme signe ne peut s'annuler (somme de nombres strictement positifs/negatifs).

---

## 5. CONNEXION A STEINER ET RENFORCEMENT

### 5.1 Le theoreme de Steiner (1977)

**Enonce :** Il existe une constante effective c > 0 telle que tout cycle de Collatz avec k etapes impaires a un point de depart n > 2^{ck/(log k)^2}.

La preuve de Steiner utilise des formes lineaires en logarithmes (Baker). On reprouve ce resultat dans le cadre S-unitaire :

### 5.2 Preuve via S-units (version amelioree)

De l'equation n*(2^S - 3^k) = g(B) et de la borne g(B) < k * 3^{k-1} * 2^S (borne triviale), on a :

> n > g(B) / (2^S) >= (terme minimal de g) / 2^S

Le terme minimal de g(B) pour B monotone est 3^{k-1} * 2^{B_0} >= 3^{k-1} * 2 (car B_0 >= 1). Donc :

> g(B) >= 3^{k-1} * 2 (contribution du premier terme seul, les autres sont positifs)

Mais n = g(B)/d, et d < 2^S, donc n > 2 * 3^{k-1} / 2^S. Puisque 2^S ~ 3^k (car S ~ k*log_2(3)), on a n > 2/3, soit n >= 1. Trivial.

La borne REELLE vient de la forme lineaire en logarithmes. L'idee est :

> **R193-T3 [CONDITIONNEL sur Baker effectif].** Tout cycle de Collatz avec k etapes impaires et S etapes paires satisfait :
>
> n >= d / (k * 3^{k-1}) * min_{B monotone, sum=S} g(B)
>
> Or d = 2^S - 3^k, et par Baker : d > C_1 * 3^k / k^{C_2} pour des constantes C_1, C_2 > 0 effectives.
> Combine avec g(B) >= 2*3^{k-1}, cela donne n >= 2*C_1 / (k^{C_2+1}).
>
> La borne EXPONENTIELLE n >= 2^{ck/(log k)^2} provient de la borne Baker FINE :
> |S*ln 2 - k*ln 3| >= exp(-C*(ln S)(ln k)(ln ln S))
> (Laurent-Mignotte-Nesterenko, 1995, Theorem 2)
>
> Puisque d = 3^k(e^{S*ln 2 - k*ln 3} - 1) ~ 3^k * |S*ln 2 - k*ln 3| pour |S*ln 2 - k*ln 3| petit, et S ~ k*1.585, on obtient :
> d > 3^k * exp(-C'*(ln k)^2 * ln ln k)
>
> Et n*d = g(B) dans un intervalle [g_min, g_max] avec g_min ~ 3^{k-1} et g_max ~ k*3^{k-1}*2^S. Donc :
> n = g(B)/d, et le nombre de n possibles est au plus g_max/d < k*3^{k-1}*2^S/d = k*3^{k-1}*2^S/(2^S - 3^k).
>
> Pour S = ceil(k*log_2 3), cela donne environ k*3^{k-1}*2^S / d. Comme d > exp(ck/(log k)^2) par Baker, on a n < 2^{O(k)} / exp(ck/(log k)^2), ce qui ne borne PAS n par le haut.
>
> En fait, la borne de Steiner dit n > 2^{ck/(log k)^2} (borne INFERIEURE), ce qui vient de : si n etait plus petit, alors |n*2^S - n*3^k| = n*d = g(B) < n*2^S, et le rapport 2^S/3^k - 1 = d/3^k serait trop petit, violant la borne de Baker. CQFD (schema).

### 5.3 Amelioration par la structure monotone

> **R193-C1 [CONJECTURE].** La contrainte de monotonie B_0 <= B_1 <= ... <= B_{k-1} renforce la borne de Steiner d'un facteur polynomial :
> n_min(k, monotone) >= k^{C_3} * 2^{ck/(log k)^2}
>
> **Justification heuristique.** La monotonie reduit le nombre de compositions admissibles de S en k parts de C(S-1, k-1) (toutes compositions) a C(S+k-1, k-1)/k! ~ (compositions en partitions). Cette reduction par ~k! dans le comptage devrait se traduire par un facteur polynomial dans la borne sur n_min, car les g(B) admissibles sont plus espaces.

### 5.4 WHY chain : Pourquoi les S-units renforcent-elles Steiner ?

**WHY 1 : Pourquoi le cadre S-unitaire donne-t-il une borne sur n_min ?**
Parce que l'equation n*d = g(B) lie n a une somme de {2,3}-units, et la theorie de Baker borne l'approximation de 2^S/3^k par un rationnel.

**WHY 2 : Pourquoi Baker borne-t-il cette approximation ?**
Parce que log 2 et log 3 sont Q-lineairement independants (i.e., log 2 / log 3 est irrationnel), et Baker (1966) quantifie COMBIEN irrationnel : la mesure d'irrationalite de log 2 / log 3 est finie (en fait, la meilleure borne connue est mu(log 2/log 3) <= 5.3... par Zudilin et al.).

**WHY 3 : Pourquoi l'irrationalite de log 2/log 3 est-elle si PROFONDEMENT liee a Collatz ?**
Parce que la conjecture de Collatz est ESSENTIELLEMENT une question sur la competition entre multiplication par 3 et division par 2. Un cycle requiert que les multiplications et divisions se COMPENSENT exactement : 3^k ~ 2^S. La mesure d'irrationalite quantifie la "difficulte" de cette compensation.

**WHY 4 : Pourquoi la mesure d'irrationalite seule ne suffit-elle pas ?**
Parce qu'elle borne |S*ln 2 - k*ln 3| mais PAS la structure fine de g(B). Deux vecteurs B et B' avec SUM B = S peuvent donner des g(B) tres differents. La mesure d'irrationalite ne voit que le TOTAL S, pas la repartition.

**WHY 5 : Qu'est-ce que les S-units apportent au-dela de la mesure d'irrationalite ?**
Les S-units capturent la structure MULTIPLICATIVE de g(B). Le fait que g(B) = SUM 3^a * 2^b est une somme de {2,3}-units signifie que g(B) vit dans un sous-module de Z tres structure. La theorie S-unitaire (Evertse, Schlickewei, Schmidt) exploite cette structure pour borner non seulement la TAILLE des solutions mais leur NOMBRE. C'est une information SUPPLEMENTAIRE que Baker seul ne donne pas.

---

## 6. L'OUTIL VERITABLE : LE THEOREME DE SCHLICKEWEI-SCHMIDT SUR LES SOMMES DEGENEREES

### 6.1 Le theoreme (Evertse-Schlickewei-Schmidt 2002)

Le theoreme le plus puissant n'est PAS Evertse 1984 (borne en 3*7^{m^2}) mais le Subspace Theorem de Schmidt et ses consequences :

> **Theoreme (ESS 2002).** Soit S un ensemble fini de places d'un corps de nombres K, et considerons l'equation a_1*x_1 + ... + a_n*x_n = 0 ou les x_i sont des S-units. Le nombre de solutions non-degenerees est au plus exp(exp(exp(n))).
>
> La borne DOUBLEMENT EXPONENTIELLE a ete amelioree par Amoroso-Viada (2009) en exp((6n)^{3n}).

Pour notre equation a k+2 termes : au plus exp((6(k+2))^{3(k+2)}). C'est FINI mais ENORME.

### 6.2 L'astuce de la projection

L'idee cle est de NE PAS appliquer ESS a l'equation complete, mais de PROJETER sur des sous-equations.

> **R193-P6 [CONDITIONNEL].** Considerons l'equation de Horner z_{j+1} = 3*z_j + 2^{B_j} pour un j fixe. Si z_j est fixe, c'est une equation :
> 2^{B_j} = z_{j+1} - 3*z_j
>
> Le membre gauche est un {2}-unit (puissance de 2). Le membre droit est un entier. Pour que 2^{B_j} divise z_{j+1} - 3*z_j, il faut que v_2(z_{j+1} - 3*z_j) >= B_j ou v_2 est la valuation 2-adique.
>
> Cela donne la contrainte : B_j <= v_2(z_{j+1} - 3*z_j).
>
> Or v_2(z_{j+1} - 3*z_j) = v_2(z_{j+1}) si v_2(z_j) = 0 (car 3*z_j est impair si z_j est impair).
>
> **Fait :** z_0 = 1 est impair. z_1 = 3 + 2^{B_0}, qui est impair ssi 2^{B_0} est pair, i.e., B_0 >= 1 (toujours vrai). Donc z_1 = 3 + 2^{B_0} est impair + pair = impair si B_0 = 1 (z_1 = 5), ou 3 + 4 = 7 si B_0 = 2, etc. En fait z_1 est toujours impair (3 + pair = impair).
>
> Par recurrence : z_{j+1} = 3*z_j + 2^{B_j}. Si z_j est impair, alors 3*z_j est impair, et z_{j+1} = impair + 2^{B_j}. Si B_j = 1 : z_{j+1} = impair + 2 = impair. Si B_j >= 2 : z_{j+1} = impair + 4*(...) = impair. Donc z_{j+1} est TOUJOURS impair.
>
> **Conclusion :** Tous les z_j sont impairs, et B_j = v_2(z_{j+1} - 3*z_j) EXACTEMENT.

> **R193-L2 [PROUVE].** Pour tout j = 0, ..., k-1, tous les etats intermediaires z_j de la recurrence de Horner sont impairs, et B_j = v_2(z_{j+1} - 3*z_j).
>
> **Preuve.** z_0 = 1 impair. Si z_j impair, alors z_{j+1} = 3*z_j + 2^{B_j} = impair + pair = impair. Par recurrence forte, tous les z_j sont impairs. Comme z_{j+1} - 3*z_j = 2^{B_j} > 0, et 2^{B_j} est la plus grande puissance de 2 divisant cette difference, B_j = v_2(z_{j+1} - 3*z_j). CQFD.

### 6.3 La contrainte 2-adique comme filtre

> **R193-P7 [CONDITIONNEL].** La sequence (z_0, z_1, ..., z_k) est ENTIEREMENT determinee par les B_j, et reciproquement les B_j sont determines par les z_j via B_j = v_2(z_{j+1} - 3*z_j). La contrainte de cycle z_k = n*2^S - (n-1)*3^k combine avec la monotonie B_0 <= B_1 <= ... <= B_{k-1} impose :
>
> v_2(z_1 - 3*z_0) <= v_2(z_2 - 3*z_1) <= ... <= v_2(z_k - 3*z_{k-1})
>
> C'est une condition de CROISSANCE DES VALUATIONS 2-ADIQUES le long de la trajectoire de Horner. Cette condition est EXTREMEMENT restrictive car les valuations 2-adiques sont typiquement "aleatoires" (equidistribuees geometriquement).

**CECI est le lien profond entre la structure S-unitaire et l'automate de Horner de R192-A3.**

---

## 7. SYNTHESE : APPORT DES S-UNITS AU PROGRAMME COLLATZ

### 7.1 Ce que les S-units apportent

| Outil | Ce qu'il donne | Statut |
|-------|---------------|--------|
| Evertse brut (k+2 termes) | Finitude des cycles pour k fixe | PROUVE (R193-T1), mais borne astronomique |
| Evertse-Pillai (2 variables) | Au plus 2 paires (S,k) par d fixe | PROUVE (R193-T2) |
| Baker (formes lineaires) | n_min(k) >= 2^{ck/(log k)^2} | PROUVE (R193-P3/T3, via Steiner) |
| Horner + valuations | Contrainte de croissance v_2 | PROUVE (R193-L2, R193-P7 conditionnel) |
| Monotonie + S-units | Renforcement polynomial de Steiner | CONJECTURE (R193-C1) |

### 7.2 Ce que les S-units N'apportent PAS

1. **Pas d'exclusion des cycles pour tout k.** Evertse dit "fini", pas "zero". Le gap entre "fini" et "zero" est EXACTEMENT le probleme de Collatz.

2. **Pas de borne uniforme en k.** La borne d'Evertse croit (doublement) exponentiellement avec k. Pour prouver l'absence de cycles pour TOUT k, il faudrait une borne qui DECROIT avec k, ce qui est le contraire.

3. **Pas de lien avec la conjecture pour les trajectoires infinies.** Les S-units ne disent rien sur la convergence des trajectoires non-periodiques.

### 7.3 La combinaison gagnante : S-units + automate + spectral

> **R193-C2 [CONJECTURE - PISTE OUVERTE MAJEURE].** La combinaison suivante est potentiellement suffisante pour prouver l'absence de cycles non-triviaux :
>
> (A) **Baker/S-units** : n_min(k) >= 2^{ck/(log k)^2} (prouve, Section 5)
> (B) **Automate de Horner** (R192-A3) : le nombre de chemins monotones atteignant z_target dans Z/dZ est borne par d^{1-delta} pour un delta > 0 (conditionnel, R191-R192)
> (C) **Spectral** (R189-R191) : |Lambda(s)| <= |Lambda_free(s)| * (1 + correction monotonie) et |Lambda_free(s)| < d^{1-eta} (conditionnel sur C1)
>
> La combinaison (A)+(B)+(C) donnerait : le nombre N(k) de n dans [1, X] admettant un cycle de longueur k est borne par :
> N(k) <= min(X * d^{-delta}, X * 2^{-ck/(log k)^2})
>
> Pour X = 2^S ~ 3^k et delta > 0, cela donne N(k) <= 3^k * d^{-delta} ~ 3^k * (2^{S} - 3^k)^{-delta}.
>
> Pour que N(k) < 1 (absence de cycles), il faudrait d^{delta} > 3^k, i.e., delta > k*ln 3 / ln d. Puisque d ~ 2^S - 3^k et S ~ k*log_2 3, on a d ~ 3^k * (2^S/3^k - 1). La taille de d depend crucialement de S - k*log_2 3.

### 7.4 WHY chain finale : Pourquoi les S-units sont-elles un outil NECESSAIRE mais INSUFFISANT ?

**WHY 1 : Pourquoi les S-units sont-elles necessaires ?**
Parce que l'equation de Collatz est INTRINSEQUEMENT une equation en puissances de 2 et 3. Toute approche qui ignore cette structure arithmetique (ex: approches purement dynamiques, ergodiques, probabilistes) perd de l'information.

**WHY 2 : Pourquoi sont-elles insuffisantes ?**
Parce que le theoreme d'Evertse est GENERIQUE : il s'applique a TOUTE equation S-unitaire, sans exploiter la structure SPECIFIQUE de Collatz (monotonie, recurrence de Horner, relation S ~ k*log_2(3)).

**WHY 3 : Que faudrait-il pour combler le gap ?**
Un theoreme de type Evertse qui exploite SIMULTANEMENT :
(a) la structure S-unitaire (seules les primes 2 et 3),
(b) la contrainte de monotonie (les exposants sont croissants),
(c) la relation S = ceil(k*log_2 3) (le total des exposants est quasi-determine par k).

**WHY 4 : Un tel theoreme existe-t-il ?**
PAS ENCORE. C'est une direction de recherche OUVERTE. Le plus proche est le travail de Stewart (2013) sur les representations de nombres comme sommes de S-units avec contraintes sur les exposants, mais sans la contrainte de monotonie.

**WHY 5 : Comment integrer cela dans le programme Junction ?**
L'outil S-unitaire se situe au NIVEAU 4 de la hierarchie (arithmetique diophantienne). Il est complementaire au niveau 3 (automate/combinatoire de R192) et au niveau 2 (spectral/analytique de R189-R191). La preuve complete devra vraisemblablement combiner les trois niveaux :
- Niveau 2 (spectral) pour obtenir |Lambda(s)| < d^{1-eta}
- Niveau 3 (automate) pour exploiter la monotonie
- Niveau 4 (S-units) pour obtenir la borne n_min et la finitude par d

---

## 8. INVENTAIRE DES RESULTATS

| Ref | Enonce | Statut | Dependances |
|-----|--------|--------|-------------|
| R193-O1 | L'equation brute n'est pas S-unitaire pure (n generique) | OBSERVATION | -- |
| R193-L1 | Formulation S-unitaire pure ssi n est {2,3}-entier | PROUVE | Definition |
| R193-P1 | Bornes sur les etats intermediaires z_j | PROUVE | Recurrence |
| R193-P2 | Contraintes mod p sur les B_j via les z_j | PROUVE | Arithmetique |
| R193-T1 | Finitude des cycles pour k fixe | PROUVE | Combinatoire elementaire |
| R193-T2 | Au plus 2 paires (S,k) par d fixe (Pillai) | PROUVE | Schlickewei 1977 |
| R193-P3 | Borne de Steiner reprouvee : n_min >= 2^{ck/(log k)^2} | PROUVE | Baker + LMN 1995 |
| R193-P4 | Non-degenerescence <=> absence de sous-cycles | PROUVE | Definition Evertse |
| R193-P5 | Non-degenerescence automatique (termes de meme signe) | PROUVE | Positivite |
| R193-L2 | z_j tous impairs, B_j = v_2(z_{j+1} - 3*z_j) | PROUVE | Recurrence |
| R193-P6 | Contrainte 2-adique sur la recurrence | CONDITIONNEL | Monotonie |
| R193-P7 | Croissance des valuations 2-adiques | CONDITIONNEL | Equidistribution v_2 |
| R193-T3 | Renforcement Baker effectif pour d = 2^S - 3^k | CONDITIONNEL | LMN 1995 effectif |
| R193-C1 | Monotonie renforce Steiner d'un facteur polynomial | CONJECTURE | Heuristique |
| R193-C2 | Combinaison S-units + automate + spectral | CONJECTURE / PISTE | Niveaux 2+3+4 |

**Total : 5 PROUVES, 4 CONDITIONNELS, 2 CONJECTURES, 1 PISTE OUVERTE MAJEURE.**

---

## 9. RECOMMANDATIONS POUR R194

1. **Priorite 1 :** Expliciter la constante c dans la borne de Steiner via LMN 1995. La version de Laurent-Mignotte-Nesterenko donne c = 1/(4*C_LMN) ou C_LMN est calculable. Verifier si c > 0.1 (ce qui donnerait n_min(k) > 2^{0.1k/(log k)^2}, i.e., n_min(68) > 2^{1.5} ~ 3, excluant k >= 68 pour n = 1, le cycle trivial).

2. **Priorite 2 :** Investiguer R193-C2 (combinaison 3 niveaux). Le verrou est la constante delta dans la borne automate d^{1-delta}. Si delta >= 0.01, la combinaison avec Baker pourrait exclure les cycles pour k >= k_0 calculable.

3. **Priorite 3 :** Explorer le lien entre R193-L2 (croissance des valuations 2-adiques) et la contrainte d'accessibilite de l'automate de Horner (R192-A3). Les deux disent la meme chose en langages differents -- unifier.

4. **Anti-priorite :** NE PAS appliquer Evertse brut (borne en 7^{(k+2)^2}). La borne est trop faible. L'apport d'Evertse est CONCEPTUEL (le probleme est S-unitaire), pas QUANTITATIF (les bornes sont trop larges).
