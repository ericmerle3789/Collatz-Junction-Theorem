# R183 — INVESTIGATION RACINAIRE : La Tension HLP et la Loi de Modestie
## Pourquoi le minimum de g(v) ne peut-il (structurellement) atteindre la resonance ?

**Date :** 16 mars 2026
**Methode :** Raisonnement pur, chaine des POURQUOI (>=8 niveaux)
**Prerequis :** R182 (retournement HLP), R174 (poids desequilibre), R172 (analyse archimedienne), phase15 (tension 2/3)

---

## 1. LE RETOURNEMENT HLP — RAPPEL ET CADRAGE

Par l'inegalite de rearrangement de Hardy-Littlewood-Polya :

- Poids 3^{k-1-j} : DECROISSANTS en j (j=0 porte le plus gros poids)
- Valeurs 2^{B_j} avec B_0 <= ... <= B_{k-1} : CROISSANTES en j

**Donc la monotonie MINIMISE g(v).** [PROUVE — HLP, elementaire]

Le vecteur monotone est l'arrangement le plus "modeste" : il assigne les gros poids aux petites valeurs et les petits poids aux grandes valeurs. Parmi toutes les permutations des memes valeurs {2^{B_j}}, c'est celui qui produit le plus petit g.

**Question fondamentale :** Cette modestie empeche-t-elle structurellement g de tomber sur un multiple de d = 2^S - 3^k ?

---

## 2. CHAINE DES POURQUOI — 10 NIVEAUX

### WHY-1 : Pourquoi la minimisation de g par HLP est-elle un probleme ?

Minimiser g le rapproche de sa borne inferieure g_min = 3^x - 2^x (positions empaquetees a gauche). Plus g est petit, plus il est "proche de 0" en un sens absolu. Or un cycle exige g ≡ 0 mod d, et d est positif. Donc un g petit pourrait sembler favorable aux cycles.

**MAIS** — "proche de 0 en valeur absolue" et "egale a 0 modulo d" sont deux notions INCOMMENSURABLES. Un g tres petit peut etre tres loin de 0 mod d (exemple : g = 1 n'est jamais ≡ 0 mod d pour d >= 2). Et un g grand peut etre ≡ 0 mod d.

**Statut : PROUVE** (la distinction valeur absolue / arithmetique modulaire est triviale).

### WHY-2 : Pourquoi la minimisation ne suffit-elle pas a CREER un cycle ?

Parce que g doit etre EXACTEMENT 0 mod d, pas juste "petit". La modestie produit un g petit mais g petit ≠ g ≡ 0 mod d. Il faut une coincidence ARITHMETIQUE precise.

Le nombre de multiples de d dans [g_min, g_max] est ~ (2^{S-x} - 1)(3^x - 2^x)/d, qui est EXPONENTIELLEMENT grand (R172 §2.3). Donc l'intervalle des g possibles contient ENORMEMENT de multiples de d. Ce n'est pas la taille de g qui est le probleme.

**Statut : PROUVE** (R172, combinatoire elementaire).

### WHY-3 : Alors pourquoi g ne peut-il pas etre exactement 0 mod d ?

C'est LA question entiere de Collatz pour les k-cycles. Ce qui empeche g d'atteindre un multiple de d n'est pas sa TAILLE mais sa STRUCTURE. L'ensemble des valeurs atteignables par g(v) est un sous-ensemble RIGIDE de [g_min, g_max], et ce sous-ensemble pourrait eviter tous les multiples de d.

La rigidite provient de l'anti-correlation : les positions des 2^{B_j} ne sont pas libres, elles sont ORDONNEES, et les coefficients 3^{k-1-j} dependent de cette position de facon fixe et decroissante.

**Statut : DEDUIT** (reformulation structurelle du probleme).

### WHY-4 : Qu'est-ce qui SPECIFIQUEMENT dans l'anti-correlation empeche g ≡ 0 mod d ?

Voici le point delicat. L'anti-correlation impose que g est une somme de produits OPPOSES : grand × petit + petit × grand. Cette structure cree un RESSERREMENT de l'ensemble des valeurs atteignables.

**Argument precis :** Si les coefficients c_j = 3^{k-1-j} et les valeurs x_j = 2^{B_j} etaient independants, l'ensemble des g atteignables serait dense dans [g_min, g_max]. Mais l'anti-correlation COUPLE c_j et x_j : quand x_j est grand (j grand), c_j est petit, et reciproquement. Cela signifie que les termes c_j · x_j sont tous du MEME ORDRE DE GRANDEUR :

Pour le vecteur regulier (B_j = j + B_0) : c_j · x_j = 3^{k-1-j} · 2^{j+B_0} = 2^{B_0} · (3/2)^{k-1-j} · 2^{k-1}

Tous les termes vivent dans une bande de largeur ~ (3/2)^k. Cette EQUIDISTRIBUTION FORCEE des termes est une propriete de l'anti-correlation.

**Statut : DEDUIT** (observation structurelle, pas encore un theoreme).

### WHY-5 : Pourquoi l'equidistribution forcee des termes empeche-t-elle la divisibilite ?

Parce que g = somme de k termes de meme ordre de grandeur est beaucoup plus CONTRAINT qu'une somme de k termes d'ordres differents. Les sommes de termes "equilibres" occupent un sous-espace MINCE de l'espace des valeurs possibles.

**Analogie geometrique :** Imaginez k vecteurs dans R^1 de normes comparables. Leur somme vit dans un intervalle de largeur ~ k × (norme typique). Mais si les vecteurs avaient des normes tres differentes (un dominant les autres), la somme pourrait prendre presque n'importe quelle valeur dans un intervalle ~ (norme du dominant). L'anti-correlation empeche un terme de dominer : c'est la DEMOCRATIE FORCEE de l'escalier.

Le probleme modulaire : g ≡ 0 mod d exige que la somme de ces k termes equilibres tombe sur un point precis du reseau dZ. L'equidistribution forcee fait que les pas de g (quand on change un B_j) sont eux aussi de taille comparable — on ne peut pas faire de "grands sauts" vers un multiple de d.

**Statut : CONJECTURE** (l'argument de sous-espace mince n'est pas formalise).

### WHY-6 : Pourquoi ne peut-on pas faire de grands sauts ?

Quand on modifie un seul B_j (disons B_j → B_j + 1), g change de delta_j = 3^{k-1-j} · 2^{B_j}. Ce delta est le terme j lui-meme. Par l'anti-correlation, tous les deltas sont de meme ordre.

Cela signifie que les PAS ELEMENTAIRES de la marche dans l'espace des g sont tous de taille comparable. La marche ne peut pas enjamber rapidement d'un residue a un autre mod d — elle progresse a vitesse UNIFORME dans Z/dZ.

**MAIS** — et c'est crucial — la question est de savoir si cette marche uniforme COUVRE tout Z/dZ ou si elle reste confinee. C'est un probleme de COUVERTURE D'UN RESEAU PAR UNE MARCHE CONTRAINTE.

**Statut : CONJECTURE** (la formulation comme marche contrainte est correcte, la non-couverture est non prouvee).

### WHY-7 : Pourquoi la marche contrainte pourrait-elle ne pas couvrir Z/dZ ?

Deux obstructions possibles :

**(A) Obstruction COMBINATOIRE :** Le nombre de valeurs atteignables est C(S, k) ~ 2^{k·log(S/k)} (R172). Pour k >= 18, C(S, k) < d (Junction Theorem, Bloc 1). Donc l'image de g mod d ne peut pas etre surjective — elle omet au moins un residu. Mais cela ne dit pas LEQUEL est omis.

**(B) Obstruction STRUCTURELLE (la vraie question) :** Meme si C(S,k) etait > d, y aurait-il une raison pour que 0 mod d soit specifiquement exclu ?

L'obstruction B est le coeur du probleme. Elle demande : y a-t-il un INVARIANT de g(v) qui exclut 0 mod d ?

Le candidat le plus fort pour cet invariant est le suivant : g(v) est TOUJOURS une somme de puissances de 2 ponderee par des puissances de 3 DECROISSANTES, appliquees a des puissances de 2 CROISSANTES. Cette structure cree un BIAIS SYSTEMATIQUE dans la distribution de g mod d.

**Statut : CONJECTURE** (l'existence d'un biais systematique est observee numeriquement mais non prouvee).

### WHY-8 : D'ou viendrait le biais systematique ?

Le biais viendrait de la relation 3^k ≡ 2^S mod d (definition meme de d). Cette relation force :

g(v) = Σ 3^{k-1-j} · 2^{B_j} ≡ Σ 2^{S·(k-1-j)/k} · 2^{B_j} mod d (en remplacant 3 par 2^{S/k} "approximativement")

Mais 3 ≡ 2^{S/k} mod d n'est PAS exact — c'est le coeur du probleme. L'ecart entre 3 et 2^{S/k} dans Z/dZ est precisement ce qui cree le biais.

**Fait cle :** Dans Z/dZ, 3^k = 2^S. Donc 3 est une racine k-ieme de 2^S mod d. Si k ne divise pas ord_{d}(2), cette racine k-ieme n'est PAS une puissance entiere de 2. C'est la RAISON PROFONDE du biais : 3 et 2 sont INCOMMENSURABLES dans Z/dZ pour la plupart des d.

L'incommensurabilite de 2 et 3 dans Z/dZ est l'ECHO MODULAIRE de l'irrationalite de log_2(3) dans R.

**Statut : DEDUIT** (la relation 3^k = 2^S mod d est triviale ; l'incommensurabilite modulaire est un fait).

### WHY-9 : Pourquoi l'incommensurabilite modulaire 2/3 empeche-t-elle g ≡ 0 ?

Parce que g(v) = Σ 3^{k-1-j} · 2^{B_j} melange les deux mondes de facon IRREDUCTIBLE. Chaque terme est un HYBRIDE 2-3. L'annulation g ≡ 0 mod d exigerait que les contributions "monde 3" (les coefficients) et "monde 2" (les exposants) se compensent PARFAITEMENT.

C'est un probleme de COMPENSATION DIOPHANTIENNE : trouver des entiers B_0 < ... < B_{k-1} avec Σ B_j = S - k tels que Σ 3^{k-1-j} · 2^{B_j} ≡ 0 mod (2^S - 3^k).

L'incommensurabilite dit que les "vitesses" de 2 et 3 dans Z/dZ sont differentes, et que cette difference empeche une annulation systematique. C'est analogue au fait que e^{i·alpha·n} + e^{i·beta·n} ne s'annule pas si alpha/beta est irrationnel (mais ceci est un argument de mesure, pas un argument exact).

**Statut : CONJECTURE** (l'analogie avec les phases incommensurables est suggestive mais non rigoureuse).

### WHY-10 : Pourquoi l'argument exact (pas de mesure) echoue-t-il ?

Parce que le probleme est FINI pour chaque k. On n'a pas le luxe d'un argument asymptotique (sauf dans le Bloc 1). Pour un k donne, il y a un nombre fini de vecteurs et un module d fini. L'incommensurabilite est un phenomene ASYMPTOTIQUE qui ne donne pas d'outil FINI.

**C'est la racine premiere :** Le probleme de Collatz vit a l'INTERFACE entre le fini et l'infini. Les arguments asymptotiques (densite de Tao, Junction Theorem) fonctionnent pour k "assez grand". Les arguments finis (verification par ordinateur) fonctionnent pour k "assez petit". Mais la zone intermediaire (k entre 3 et ~42) echappe aux deux.

Et pour cette zone intermediaire, la tension HLP (monotonie minimise g) est un obstacle supplementaire : elle dit que parmi tous les arrangements possibles, le vecteur monotone — le seul pertinent pour Collatz — est celui qui produit le g le PLUS PETIT, donc potentiellement le plus dangereux pour les cycles. Mais "petit" n'implique pas "multiple de d".

**Statut : DEDUIT** (diagnostic du verrou structurel).

---

## 3. LA RACINE PREMIERE

Apres 10 niveaux de POURQUOI, la racine premiere est :

> **L'impossibilite des k-cycles n'est pas une consequence de la taille de g (trop petit ou trop grand), mais de l'INCOMMENSURABILITE ARITHMETIQUE entre les bases 2 et 3 a l'interieur de Z/dZ, combinee avec la contrainte de monotonie qui FORCE l'anti-correlation et restreint g a un sous-ensemble RIGIDE de l'espace des valeurs.**

Plus precisement, trois forces s'exercent simultanement :

1. **Force HLP (modestie)** : La monotonie minimise g parmi les permutations. g est aussi petit que possible. [PROUVE]

2. **Force de comptage (rarete)** : Le nombre de vecteurs monotones C(S,k) est exponentiellement plus petit que d pour k >= 18. L'image de g mod d est non-surjective. [PROUVE — Junction Theorem]

3. **Force d'incommensurabilite (biais)** : Les termes 3^a · 2^b dans g sont des hybrides 2-3 dont l'annulation mod d = 2^S - 3^k exigerait une compensation parfaite entre les mondes 2 et 3. L'irrationalite de log_2(3) empeche cette compensation de se produire generiquement. [CONJECTURE]

La force (1) est prouvee mais de MAUVAIS SIGNE (aide les cycles potentiels).
La force (2) est prouvee mais NON LOCALISEE (n'exclut pas 0 specifiquement).
La force (3) est le coeur du probleme — non prouvee.

**La tension fondamentale de R182 se resout ainsi :** La modestie de l'escalier monotone rapproche g de 0 en valeur absolue, mais l'incommensurabilite 2/3 dans Z/dZ eloigne g de 0 en valeur modulaire. Ces deux forces sont ORTHOGONALES : l'une agit dans R (taille), l'autre dans Z/dZ (arithmetique). Le fait qu'elles agissent dans des espaces differents explique pourquoi la tension existe sans contradiction.

**Statut : DEDUIT** (synthese des analyses precedentes).

---

## 4. LA LOI DE MODESTIE — ALLEGORIE APPROFONDIE

L'escalier monotone est modeste : il distribue les gros fardeaux (3^{k-1}) sur les petites marches (2^{B_0}) et les petits fardeaux (3^0) sur les grandes marches (2^{B_{k-1}}). Cette modestie minimise l'energie totale g.

Mais la resonance (g ≡ 0 mod d) n'est pas une question d'energie minimale — c'est une question de FREQUENCE. Pour que la somme resonne avec le module d, il faudrait que les termes soient accordes sur une harmonique precise de d. Or l'accord exige une relation RATIONNELLE entre les bases 2 et 3, qui n'existe pas (log_2(3) irrationnel).

**La loi sous-jacente :** La modestie n'est pas un hasard — c'est une LOI THERMODYNAMIQUE de l'escalier monotone. Par analogie :

- L'escalier monotone est l'etat de PLUS BASSE ENERGIE (HLP).
- La resonance avec d est l'equivalent d'une TRANSITION DE PHASE (passage par 0 mod d).
- L'energie de la transition (gap entre g_min mod d et 0) est POSITIVE.

La conjecture profonde est : **le gap energetique entre l'etat fondamental (g_min) et la resonance (0 mod d) est strictement positif pour tout k >= 2.**

Ce gap est mesurable : c'est min_v |g(v) mod d| / d, ou le minimum porte sur tous les vecteurs monotones v. Le "mur de verre" (R182, A2) est l'observation numerique que ce gap est toujours > 0.

**La loi, si elle existe, serait :** *Dans toute somme anti-correlee de puissances de bases multiplicativement independantes, la valeur minimale sous contrainte de monotonie ne peut pas etre un multiple du denominateur naturel de la somme.*

**Statut : CONJECTURE** (non formalisee, pas meme un enonce precis).

---

## 5. LA DISTRIBUTION DE g(v) MOD d

### 5.1 Que dit HLP sur la distribution ?

HLP dit que le vecteur monotone donne g_min (parmi les permutations). Le vecteur ANTI-monotone (B_0 >= ... >= B_{k-1}, qui n'est PAS un vecteur de Collatz valide) donnerait g_max.

**Question 3 du prompt :** La distribution entre g_min et g_max est-elle uniforme ?

NON. La distribution des g(v) sur l'ensemble des vecteurs monotones n'est pas uniforme dans [g_min, g_max]. Elle est CONCENTREE autour de la valeur typique, qui correspond au vecteur "regulier" B_j ~ j · S/k. Par un argument de type loi des grands nombres :

- La valeur typique est g_typ ~ k · 3^{k/2} · 2^{S/2} (terme central de la somme).
- La variance est dominee par les termes extremes.

Modulo d, la distribution des g(v) sur les C(S,k) vecteurs est quasi-uniforme sur un SOUS-ENSEMBLE de Z/dZ (par les arguments de sommes exponentielles, R181). Mais "quasi-uniforme sur un sous-ensemble" signifie que la densite est ~ C(S,k) / |image|, pas ~ C(S,k) / d.

**Statut : DEDUIT** (arguments heuristiques, pas de preuve).

### 5.2 La distance g_min — plus proche multiple de d

**Question 4 du prompt :** La distance entre g_min et le multiple de d le plus proche croit-elle avec k ?

g_min = 3^k - 2^k (pour k = x, S minimal). Le plus proche multiple de d en dessous de g_min est floor(g_min / d) · d. La distance est :

delta_min(k) = g_min mod d = (3^k - 2^k) mod (2^S - 3^k)

Or 3^k ≡ 2^S mod d, donc g_min = 3^k - 2^k ≡ 2^S - 2^k = 2^k(2^{S-k} - 1) mod d.

Puisque gcd(2, d) = 1, delta_min(k) ≡ 2^k · (2^{S-k} - 1) mod d.

Pour S = ceil(k · log_2(3)), S - k ~ k · (log_2(3) - 1) ~ 0.585k. Donc 2^{S-k} ~ 2^{0.585k} ~ 1.5^k.

Ainsi delta_min(k) ~ 2^k · 1.5^k = 3^k mod d. Mais 3^k ≡ 2^S mod d ≡ 0 mod... non, 3^k = 2^S - d.

Reformulons : g_min mod d = (3^k - 2^k) mod d. Or 3^k = d + 2^S, donc 3^k mod d = 2^S mod d = 3^k mod d... c'est circulaire.

Directement : g_min = 3^k - 2^k. Et d = 2^S - 3^k. Donc g_min + d = 2^S - 2^k = 2^k(2^{S-k} - 1). Et g_min = -(d - (2^S - 2^k - 3^k + 2^k))... simplifions.

g_min / d = (3^k - 2^k) / (2^S - 3^k).

Pour S = ceil(k · alpha), alpha = log_2(3) : 2^S ~ 3^k (un peu plus grand), donc d << 3^k, et g_min / d ~ (3^k - 2^k) / d >> 1. Il y a BEAUCOUP de multiples de d en dessous de g_min. La fractional part {g_min / d} est essentiellement aleatoire (equidistribution des frac(k · alpha) par Weyl).

**Conclusion :** La distance delta_min(k) / d = frac(g_min / d) ne CROIT PAS systematiquement avec k — elle oscille de facon quasi-aleatoire dans [0, 1). C'est un phenomene d'equidistribution, pas de croissance monotone.

**Statut : DEDUIT** (par equidistribution de Weyl et proprietes de frac(k · alpha)).

---

## 6. PISTES EMERGENTES

### Piste 1 : L'argument de rigidite du sous-espace (6/10)

L'ensemble des g(v) atteignables forme un SOUS-ENSEMBLE RIGIDE de [g_min, g_max]. Ce sous-ensemble a une structure qui pourrait etre etudiee comme un SUMSET : c'est l'image d'une application lineaire (les coefficients 3^{k-1-j}) evaluee sur les sommets d'un simplexe discret (les vecteurs monotones).

La theorie des sumsets (Freiman, Ruzsa, Green-Tao) etudie exactement ce type d'objet. Si le sumset a une "structure additive" particuliere (progression arithmetique, union de progressions), sa distribution mod d pourrait etre contrainte.

**Direction :** Etudier la dimension de Freiman de l'ensemble {g(v) : v monotone} et ses proprietes mod d.

### Piste 2 : L'orthogonalite taille/arithmetique (5/10)

La tension HLP agit dans R (taille de g), tandis que la condition de cycle agit dans Z/dZ (arithmetique de g). Ces deux contraintes sont ORTHOGONALES. Un argument qui les couple — par exemple via les hauteurs de Weil — pourrait transformer la tension en obstruction.

**Direction :** Formuler g(v) comme un point sur une variete arithmetique et utiliser la theorie des hauteurs pour montrer que le "point de cycle" (g ≡ 0 mod d) a une hauteur incompatible avec la contrainte de monotonie.

### Piste 3 : L'equidistribution NON-uniforme de g mod d (5/10)

Si la distribution de g(v) mod d n'est PAS uniforme mais a un TROU autour de 0, c'est exactement ce qu'il faut. Le biais pourrait venir de l'anti-correlation : les termes equilibres de g creent une structure de Fourier dans Z/dZ qui interfere destructivement a la frequence 0.

**Direction :** Calculer la transformee de Fourier de la distribution de g(v) mod d et montrer que le coefficient de Fourier a la frequence correspondant a 0 mod d est anormalement petit.

### Piste 4 : Le "gap de resonance" comme invariant (4/10)

Definir gap(k) = min_v (g(v) mod d) / d. Si gap(k) > 0 pour tout k >= 2, les cycles sont exclus. Le defi est de montrer gap(k) > 0 UNIFORMEMENT.

L'analogie thermodynamique suggerait que ce gap est l'energie d'activation d'une transition de phase impossible. Mais formaliser cela necessite un cadre mathematique precis (theorie ergodique sur le simplexe ?).

---

## 7. THEOREME CANDIDAT

**THEOREME CANDIDAT R183 (Exclusion par Incommensurabilite Anti-Correlee).**

*Soit k >= 2, S = ceil(k · log_2(3)), d = 2^S - 3^k. Soit G_k = {g(v) mod d : v vecteur monotone dans le simplexe S(S, k)}. Alors 0 ∉ G_k.*

*Mecanisme conjecture :*
1. L'ensemble G_k est un sumset anti-correle de taille C(S,k).
2. Pour k >= 18, |G_k| < d (Junction Theorem), donc G_k est non-surjectif.
3. L'incommensurabilite de 2 et 3 dans Z/dZ cree un biais dans G_k qui exclut 0.
4. Pour k < 18, la verification est finie (et realisee par ordinateur).

**Statut : CONJECTURE** (aucune des etapes 1-3 n'est prouvee en tant qu'implication pour 0 ∉ G_k).

---

## 8. SYNTHESE — REPONSE A L'ALLEGORIE

**Q : La modestie de l'escalier empeche-t-elle structurellement la resonance ?**

R : La modestie SEULE n'empeche pas la resonance. Elle minimise g en valeur absolue (force archimedienne), mais la resonance est une condition modulaire (force arithmetique). Les deux forces sont orthogonales.

**Q : Et si la modestie n'etait pas un hasard mais une LOI ?**

R : La modestie EST une loi — c'est le theoreme de HLP. Mais cette loi agit dans le mauvais espace (R au lieu de Z/dZ). Pour qu'elle devienne une obstruction aux cycles, il faudrait un PONT entre l'espace archimedien (ou la modestie agit) et l'espace modulaire (ou la resonance vit). Ce pont serait un invariant qui traduit la minimalite archimedienne en exclusion modulaire.

**Q : Ce pont existe-t-il ?**

R : C'est la question ouverte centrale. Les candidats sont :
- Les hauteurs de Weil (theorie des nombres)
- La theorie des sumsets (combinatoire additive)
- La transformee de Fourier sur Z/dZ (analyse harmonique)

Aucun de ces outils n'a ete applique avec succes a ce probleme precis. Le verrou est que le support (C(S,k) vecteurs monotones) est trop petit pour les outils analytiques (qui demandent un support ~ d^delta) et trop grand pour les outils combinatoires finis (qui demandent une enumeration).

---

## 9. BILAN

| Element | Statut | Commentaire |
|---------|--------|-------------|
| Monotonie minimise g (HLP) | PROUVE | Elementaire, valable pour tout k |
| Minimisation agit dans R, pas dans Z/dZ | PROUVE | Orthogonalite triviale |
| g_min mod d ne croit pas avec k | DEDUIT | Equidistribution de Weyl |
| Biais de g(v) mod d excluant 0 | CONJECTURE | Observe numeriquement (mur de verre) |
| Incommensurabilite 2/3 comme source du biais | CONJECTURE | Coherent mais non formalise |
| Gap de resonance > 0 pour tout k >= 2 | CONJECTURE | Equivalent a la conjecture de Collatz pour k-cycles |
| Pont archimedien-modulaire via hauteurs/sumsets | QUESTION OUVERTE | Aucun outil existant ne s'applique directement |

### Chaine des POURQUOI — Resume

| Niveau | Reponse condensee | Statut |
|--------|-------------------|--------|
| WHY-1 | Minimiser g le rapproche de 0 en valeur absolue | PROUVE |
| WHY-2 | Mais g ≡ 0 mod d ≠ g petit : il faut une coincidence arithmetique | PROUVE |
| WHY-3 | L'ensemble des g atteignables est rigide (anti-correlation) | DEDUIT |
| WHY-4 | L'anti-correlation equilibre les termes (democratie forcee) | DEDUIT |
| WHY-5 | Les termes equilibres restreignent g a un sous-espace mince | CONJECTURE |
| WHY-6 | Les pas elementaires sont uniformes : marche a vitesse constante dans Z/dZ | CONJECTURE |
| WHY-7 | La marche contrainte n'a pas assez de pas (C(S,k) < d pour k >= 18) OU un biais structurel exclut 0 | PROUVE (comptage) + CONJECTURE (biais) |
| WHY-8 | Le biais vient de l'incommensurabilite de 2 et 3 dans Z/dZ | DEDUIT |
| WHY-9 | L'incommensurabilite empeche la compensation parfaite des hybrides 2-3 | CONJECTURE |
| WHY-10 | L'argument exact echoue car le probleme est FINI pour chaque k : a l'interface fini/infini | DEDUIT |

### Racine premiere

**L'obstruction aux k-cycles n'est pas la modestie de l'escalier (force archimedienne, mauvais signe) mais l'incommensurabilite arithmetique de 2 et 3 dans Z/dZ (force modulaire, bon signe). La tension HLP est un LEURRE : elle agit dans le mauvais espace. Le vrai combat se joue dans Z/dZ, ou les bases 2 et 3 sont "presque alignees" (3^k = 2^S mod d) mais jamais assez pour qu'une somme anti-correlee s'annule.**

---

*R183 : 10 niveaux de POURQUOI, racine premiere identifiee (incommensurabilite modulaire, pas modestie archimedienne), 4 pistes emergentes, 1 theoreme candidat (conjecture). La tension HLP est diagnostiquee comme un leurre — orthogonale au vrai probleme.*
