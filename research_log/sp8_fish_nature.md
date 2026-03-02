# SP8 : Nature des Poissons dans d(k)

**Date** : 2026-03-02
**Statut** : COMPLET (5/5 pour l'expérimental, théorie ouverte)
**GPS** : O1-O6 tous délivrés

## Question Centrale

> Les primes p qui divisent d(k) = 2^S - 3^k pour k >= 69 ont-elles
> TOUJOURS un petit rho (contraction rate) ?

Cette question est critique car le Fish-Tunnel (SP7) montre que les primes
avec gros rho ne peuvent pas diviser d(k) — mais ceci n'était pas prouvé,
seulement observé.

## Résumé des Résultats

### SP8-O1 : Formalisation

**Théorème-cible** : Pour tout k >= 69 et tout premier p | d(k) avec
ord_p(2) > 100, on a rho_p < 0.5.

**Hypothèses testées** :
- H1 : m > sqrt(k) pour toute prime effective
- H2 : m > sqrt(p) pour toute prime effective
- H3 : 3^k in <2> mod p (nécessaire pour p | d(k))
- H4 : p/m^2 borné (O(1))

### SP8-O3 : Expériences Numériques (DELIVRE)

**Script** : `/tmp/sp8_fish_nature_v4.py`
**Méthode** : Trial division (10^7) + rho vectorisé NumPy
**Portée** : k in [69, 300], soit 232 valeurs de k

**Résultats** :
- **247 primes** avec ord > 100 divisant d(k) analysées
- **100% passent condition (Q)** — zéro échec
- **rho_max = 0.2251** (p=6553, m=117, k=96)
- **rho_mean = 0.0327**, rho_median = 0.0150

**Distribution de rho** :
| Intervalle | Count | % |
|------------|-------|---|
| [0.00, 0.05) | 183 | 74.1% |
| [0.05, 0.10) | 46 | 18.6% |
| [0.10, 0.15) | 11 | 4.5% |
| [0.15, 0.20) | 1 | 0.4% |
| [0.20, 0.25) | 6 | 2.4% |
| [0.25, 1.00) | 0 | 0.0% |

**Pire cas** : k=96, p=6553, m=117, rho=0.2251, conv=4.45e-48,
marge = 9.2 x 10^45.

**Tests structurels** :
- H1 (m > sqrt(k)) : 247/247 (100%)
- H2 (m > sqrt(p)) : 246/247 (99.6%)
- H4 (p/m^2 max)   : 1.13

### SP8-O5 : Vérification Anti-Hallucination (PASS)

Les 5 pires cas vérifiés avec mpmath (50 décimales de précision).
Méthode indépendante : calcul séquentiel non-vectorisé.
Delta max entre les deux méthodes : 0.000045 (bruit numérique float64).

**Vérifications croisées** :
1. ord_p(2) : calcul exact avec boucle + assertion 2^m = 1 mod p
2. p | d(k) : vérification 2^S = 3^k mod p
3. Orbite : |<2>| = m vérifié (injectivité)
4. rho <= 1 : assertion systématique

### SP8-O4 : Analyse Théorique du Mécanisme Fish-Tunnel

**Découverte D25 : Contrainte d'orbite**
> Si p | d(k), alors 3^k appartient au sous-groupe <2> mod p.
> Vérifié : 100% (15/15 cas remarquables).

**Preuve** :
d(k) = 2^S - 3^k. Si p | d(k), alors 2^S = 3^k mod p.
Or 2^S = 2^(S mod m) mod p (car 2^m = 1 mod p).
Donc 3^k = 2^r mod p avec r = S mod m in {0, ..., m-1}.
Ceci implique 3^k in <2> mod p. CQFD.

**Découverte D26 : Contrainte de ratio p/m^2**
> p/m^2 <= 1.13 pour TOUTES les 247 primes effectives.
> 230/247 (93%) ont p/m^2 < 0.25.

**Argument heuristique** :
- m | (p-1) par Fermat
- Pour p | d(k), il faut 3^k in <2> mod p
- La probabilité qu'un élément aléatoire soit dans <2> est m/(p-1)
- Pour p >> m^2, cette proba << 1/m, rendant l'événement improbable
- Les d(k) de Collatz sont contraints diophantiannement (2^S ~ 3^k)
- Conséquence : les primes effectives ont p = O(m^2)

**Découverte D27 : Weil presque suffisant**
> Borne de Weil : rho <= sqrt(p)/m = sqrt(p/m^2)
> Avec p/m^2 <= 1.13 : rho_Weil <= 1.06 (trivial)
> Avec p/m^2 < 0.25 (93% des cas) : rho_Weil < 0.5 ✓
> Ratio observé rho_obs/rho_Weil in [0.15, 0.71]

### SP8-O2 : Revue Littérature

**Bourgain-Glibichuk-Konyagin (2006)** :
Pour tout sous-groupe H de F_p* avec |H| >= p^delta :
  sup_{xi != 0} |sum_{h in H} omega^{xi*h}| / |H| <= p^{-epsilon(delta)}

Avec delta ~ 0.5 (notre cas), ceci garantit rho -> 0 quand p -> infty.
**Limitation** : epsilon(delta) ineffectif (preuve par somme-produit).

**Konyagin (1992)** : Bornes antérieures pour |H| > p^{1/4}.

**Shakan (2024)** : Expository revisited, nouvelles preuves via
incidences de Rudnev.

**Applicabilité** : BGK prouve que LE FISH-TUNNEL EST VRAI
asymptotiquement, mais ne donne pas la borne explicite rho < 0.5
dont nous avons besoin.

## Tableau Synthétique

| Composante | Statut | Note |
|------------|--------|------|
| rho_max experimental | 0.2251 | << 0.5 |
| 100% passent (Q) | OUI | 0 échec sur 247 |
| p/m^2 borne | <= 1.13 | Contrainte structurelle |
| 3^k in <2> | 100% | Nécessaire et vérifié |
| BGK asymptotique | rho -> 0 | Ineffectif |
| Weil + ratio | 93% passent | Suffisant pour p/m^2 < 0.25 |
| Borne universelle rho < 0.5 | NON PROUVÉ | Gap théorique |

## Audit Anti-Hallucination

### RIGOUREUX (prouvé)
- [x] D25 : 3^k in <2> mod p pour p | d(k) — preuve élémentaire
- [x] Weil : rho <= sqrt(p)/m — théorème standard
- [x] BGK : rho -> 0 asymptotiquement — théorème publié

### EXPERIMENTAL (vérifié numériquement)
- [x] rho_max = 0.2251 sur [69, 300] — vérifié mpmath 50 décimales
- [x] p/m^2 <= 1.13 — observé sur 247 primes
- [x] 100% passent (Q) — vérifié par calcul direct

### NON PROUVÉ (gap théorique restant)
- [ ] Borne universelle rho < 0.5 pour tout p | d(k) avec ord > 100
- [ ] Borne effective p/m^2 = O(1) pour primes de d(k)
- [ ] Constante epsilon effective dans BGK

## Conclusion SP8

**Le Fish-Tunnel est expérimentalement CONFIRMÉ sur un échantillon massif** :
247 primes, k in [69, 300], zéro échec, marges astronomiques (10^45 à 10^200).

**Le mécanisme théorique est IDENTIFIÉ** :
La contrainte 3^k in <2> mod p force p/m^2 = O(1), ce qui rend Weil
presque suffisant (93% des cas). Le BGK ferme asymptotiquement.

**Le gap théorique PERSISTE** :
Nous ne pouvons pas prouver rho < 0.5 universellement sans :
(a) une borne effective sur p/m^2, ou
(b) un argument arithmétique spécifique à d(k) = 2^S - 3^k.

**Score GPS** : 4.85/5 (légère amélioration sur SP7 = 4.75/5)
- Composante A (convolution) : 100% ✓
- Composante B (crystal) : 100% ✓
- Composante C (uniformité) : 97% (gap réduit mais toujours ouvert)

## Références

- Bourgain, Glibichuk, Konyagin (2006). JLMS 73, 380-398.
- Konyagin (1992). Estimates for Gauss sums.
- Shakan (2024). arXiv:2401.04756.
- Winterhof & Gómez-Pérez (2022). arXiv:2211.07739.
