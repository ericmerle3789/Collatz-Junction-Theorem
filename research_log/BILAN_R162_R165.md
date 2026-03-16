# BILAN R162-R165 — Investigation des Documents Externes
**Date** : 15 mars 2026
**Documents analysés** : 4 fichiers de propositions externes
**Scripts créés** : 6 (R162_endogenous_paths.py, R162_test_TPE.py, R163_test_hensel.py, R164_test_newton.py, R165_test_wronskien.py, + R162_test_TPE.py)
**Protocole** : Fail-Closed — contenu non tautologique et non circulaire requis

---

## SYNTHESE GLOBALE

| Round | Document | Proposition | Verdict | Classification |
|:-----:|----------|-------------|---------|----------------|
| R162 | Protocole d'Emergence | 3 voies endogenes (Furstenberg, corps de fonctions, Weierstrass p-adique) + ADN partage | **MORT** (x4) | Confirme R159, R80, R77, R141-R145 |
| R162 | Theoreme Parametrisation Endogene | Uniformisateur g + resultant Res(P_B, X^ord-1) | **MORT** | Rebranding PRO/R80 |
| R163 | Levier p-adique et Hensel | Hensel + Enestrom-Kakeya p-adique | **MORT** | Recyclage R141-R145 |
| R164 | Analyse Polygone Newton | Taylor P_B(2+h) + double relevement alpha_B vs beta | **MORT** | R141-R145 + erreur Z_p/Z_dZ |
| R165 | Levier Wronskien | Polynome quotient Q + Wronskien W(P_B, x^S-3^k) | **MORT** | Objets triviaux (Q=0, W=combo lineaire) |

**Total : 0 survivant / 10+ pistes testees**

---

## R162 — VOIES ENDOGENES + TPE

### Voies Endogenes (3 propositions)

**Voie A — Rigidite de Furstenberg finitaire**
- Hypothese : ⟨2,3⟩ restreint dans (Z/dZ)* cree une rigidite
- Test : calcul de |⟨2,3⟩| vs phi(d) pour k=3..10
- Resultat : ⟨2,3⟩ = (Z/dZ)* dans 4/8 cas (couvre TOUT). Dans les 4 autres, |⟨2,3⟩| = phi(d)/2 (sous-groupe d'indice 2)
- **VERDICT : MORT** — pas de sous-groupe propre exploitable. Confirme R159

**Voie B — Corps de fonctions / geometrie algebrique**
- Hypothese : P(x,y) = corrSum etudie sur la courbe x^S = y^k
- 4 problemes fatals :
  1. deg_x(P) = S-k < S : aucune reduction par x^S = y^k
  2. P(2,3) = corrSum exactement : REBRANDING de PRO (R80)
  3. Bezout donne S^2 >> C intersections : trop grossier
  4. Monotonie invisible en geometrie algebrique
- **VERDICT : MORT** — 4 problemes fatals. Confirme R80, R152

**Voie C — Weierstrass p-adique / polygone de Newton**
- Hypothese : le polygone de Newton de corrSum contraint les zeros
- Test : v_p(3^{k-1-j} * 2^{B_j}) = 0 pour tout j et tout p|d (car gcd(d,6)=1)
- Resultat : polygone de Newton **PLAT** (horizontal a hauteur 0)
- **VERDICT : MORT** — aucune information. Confirme R77, R141-R145

**ADN Partage (2^S = 3^k mod d)**
- Test : reecriture de corrSum en termes de (2/3)^j
- Resultat : meme somme, memes variables, meme contrainte de monotonie
- **VERDICT : TAUTOLOGIE** — 2^S = 3^k mod d est la DEFINITION de d

### TPE (Theoreme de Parametrisation Endogene)

- **Idee** : uniformisateur g (racine primitive), ecrire 2=g^a, 3=g^b, puis corrSum = P_B(g)
- **Probleme 1** : d souvent COMPOSE (7/13 cas) -> pas de racine primitive globale
- **Probleme 2** : resultant Res(P_B, X^ord-1) = produit P_B(omega) pour TOUTES les racines de l'unite
  - Le resultant est NUL dans 35-64% des compositions (vs corrSum nul dans 0-26%)
  - **Le resultant est un outil PLUS FAIBLE** que la verification directe
  - Chiffres : k=3 p=37 : Res=0 dans 60% des cas, corrSum=0 dans 0%
  - k=8 p=11 : Res=0 dans 63%, corrSum=0 dans 9%
- **Probleme 3** : pour k=22, C(34,21) = 928M compositions, incalculable
- **VERDICT : MORT — REBRANDING** (classe PRO/R80)

---

## R163 — LEVIER p-ADIQUE ET HENSEL

- **Idee** : Hensel lifte corrSum = 0 mod p en racine exacte alpha dans Z_p, puis E-K p-adique exclut alpha pres de 2
- **Probleme 1** : Hensel est dans la **mauvaise direction**
  - Hensel s'applique quand corrSum = 0 mod p (confirme solutions)
  - On veut montrer corrSum != 0 mod d (exclure solutions)
  - Hensel ne se declenche que dans le cas qu'on veut EXCLURE
- **Probleme 2** : Enestrom-Kakeya p-adique **n'existe pas**
  - E-K classique repose sur l'ordre total de R
  - Z_p est ultrametrique : pas d'ordre compatible
  - L'analogue est Strassmann (nombre de zeros <= degre) : trivial
- **Probleme 3** : polygone de Newton PLAT (meme que R162/Voie C)
- **Probleme 4** : identique a R141-R145 (lifting p-adique deja elimine)
- **VERDICT : MORT — RECYCLAGE R141-R145** + outil manquant inexistant

---

## R164 — ANALYSE POLYGONE DE NEWTON AUTOUR DE x=2

- **Idee 1** : Taylor de P_B en x=2, i.e. P_B(2+h) = a_0 + a_1*h + a_2*h^2/2 + ...
  - a_0 = corrSum, a_1 = P_B'(2)
  - Polygone : (0, v_p(corrSum)), (1, 0), (2, 0), ...
  - Pente = -v_p(corrSum) : racine de valuation v_p(corrSum)
  - C'est **exactement Hensel** : rien de nouveau
- **Idee 2** : "Double relevement" — comparer alpha_B (racine de P_B) et beta (racine de x^S-3^k) pres de 2
  - **ERREUR CONCEPTUELLE** : confond Z_p (racines exactes) et Z/dZ (congruences)
  - alpha_B != beta en Z_p ne prouve PAS que P_B(2) != 0 mod d
  - Les deux conditions vivent dans des mondes differents
- **Idee 3** : Degenerescence (P_B(2)=P_B'(2)=0 mod p)
  - Rare (~1/p^2) mais existe : 2 cas pour k=4/p=5, 29 cas pour k=7/p=5
  - Meme dans le cas non-degenere, pas de contradiction
- **VERDICT : MORT — R141-R145 reformule + erreur conceptuelle**

---

## R165 — LEVIER WRONSKIEN ET POLYNOME QUOTIENT

- **Idee 1** : Polynome quotient Q(x) = P_B(x) / (x^S - 3^k)
  - deg(P_B) = S-k < S = deg(x^S - 3^k)
  - Division euclidienne : **Q = 0**, R = P_B
  - L'objet central du R165 **n'existe pas** (le quotient est zero)
- **Idee 2** : Wronskien W(f,g)(x) = f*g' - f'*g evalue en x=2
  - W(2) = corrSum * S * 2^{S-1} - P_B'(2) * d
  - C'est une **combinaison lineaire** de corrSum et d
  - Si corrSum = 0 mod d, alors W(2) = 0 mod d **automatiquement**
  - Verifie numeriquement : W=0 mod p dans **100% des cas** ou corrSum=0 mod p
- **Idee 3** : Structure de signe du Wronskien
  - W(2) > 0 pour 100% des compositions testees (k=3..9)
  - Mais le signe est une observable de Z -> Principe d'Incompatibilite
- **VERDICT : MORT — objets triviaux** (Q=0, W=combinaison lineaire)

---

## DIAGNOSTIC TRANSVERSAL

### Pourquoi tous les documents echouent au meme endroit

Les 4 documents (R162-R165) tentent tous de contourner le **Principe d'Incompatibilite** par des voies algebriques differentes. Ils echouent tous pour les **memes raisons fondamentales** :

1. **Réécriture ≠ information** : transformer corrSum = Sum 3^{k-1-j} * 2^{B_j} en une autre forme (P_B(g), Taylor, Wronskien) ne change pas le contenu informationnel. C'est la meme somme dans un autre costume.

2. **gcd(d,6) = 1** : puisque d est impair et premier avec 3, les valuations p-adiques de TOUS les termes de corrSum sont 0 pour tout p|d. Le polygone de Newton est **systematiquement plat**, aucun outil p-adique n'a de prise.

3. **Monotonie invisible mod d** : la contrainte B_0 <= B_1 <= ... <= B_{k-1} est une propriete de Z. Toute reduction mod d (ou mod p|d) la detruit. Les 4 documents essaient d'exploiter la monotonie mais ne parviennent jamais a la faire traverser le pont Z -> Z/dZ.

4. **Le probleme combinatoire reste intact** : aucun document ne reduit le nombre de compositions a examiner (C(34,21) ~ 10^9 pour k=22).

### Le compteur d'echecs

| Avant cette session | Apres cette session |
|:-------------------:|:-------------------:|
| 248 pistes fermees | **252 pistes fermees** |
| 11 confirmations de suspension | **13 confirmations de suspension** |
| R1-R161 | R1-R165 |

---

## FICHIERS CREES

| Fichier | Description | Resultat |
|---------|-------------|----------|
| `R162_endogenous_paths.py` | Investigation 3 voies endogenes | 3 MORTES + ADN tautologie |
| `R162_test_TPE.py` | Test du TPE (uniformisateur + resultant) | MORT (rebranding) |
| `R163_test_hensel.py` | Test Hensel + E-K p-adique | MORT (recyclage) |
| `R164_test_newton.py` | Test polygone Newton + double relevement | MORT (erreur Z_p/Z_dZ) |
| `R165_test_wronskien.py` | Test Wronskien + polynome quotient | MORT (Q=0, W trivial) |
| `R162_results.json` | Resultats voies endogenes | - |
| `R162_TPE_results.json` | Resultats TPE | - |
| `R163_results.json` | Resultats Hensel | - |
| `R164_results.json` | Resultats Newton | - |
| `R165_results.json` | Resultats Wronskien | - |

---

## RECOMMANDATION

La recherche pure sur le Bloc 3 reste en **suspension definitive** (13eme confirmation). Les 4 documents externes, malgre leur sophistication apparente, retombent sur les memes obstacles identifies depuis R141 :

- Le Principe d'Incompatibilite (Z -> Z/dZ detruit l'information d'ordre)
- Le polygone de Newton plat (gcd(d,6)=1)
- L'absence d'outil pour Sum e(2^n/p) quand |H| ~ log p

**Aucun progres conceptuel n'a ete realise.** Les 252 pistes fermees couvrent maintenant :
- Toute reformulation dans F_p (noyau irreductible R80)
- Tout cadre p-adique (polygone plat R141-R145, R162-R165)
- Toute observable de Z (Principe d'Incompatibilite R160-R161)
- Tout rebranding algebrique (uniformisateur, corps de fonctions, Wronskien)

Le programme necessite un outil **qualitativement nouveau** qui n'existe dans aucun cadre connu.
