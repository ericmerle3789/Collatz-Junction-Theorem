TYPE: P
OBJET CIBLÉ: LSD (h=2) + Horner Telescoping / WEL
QUESTION CENTRALE: Parmi les deux routes survivantes vers μ→1 (LSD par distances de Hamming, Horner par non-résonance des tranches), laquelle produit la prochaine vraie marche démontrable ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: faire monter au moins une des deux routes d’un cran vers un lemme, et autopsier proprement toute route qui se révèle trop fragile.

# BRIEF CLAUDE CODE — ROUND 47 (R47)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R46.

### Contexte acquis
- R46 a transformé le programme μ→1 en deux routes survivantes complémentaires :
  1. **LSD** : approche par collisions et distances de Hamming
  2. **Horner Telescoping** : approche spectrale / inductive par tranches B₀=b₀
- T50 [PROUVÉ] :
  μ − 1 = (p−1)/C + p·E_excess/C²
- T52 [PROUVÉ] :
  pour h=1, collision ssi ord_p(2) divise |Δ|
- Weyl k≥4, MSL-lite et Erdős-Turán ont été fermés avec autopsie.
- Le verrou actuel est :
  **faire monter soit LSD soit Horner d’un cran vers une preuve partielle réelle de WEL ou de μ→1.**

## Objectif de R47
R47 doit répondre à cette question centrale :

> La prochaine vraie marche démontrable vers μ→1 passe-t-elle par LSD (en montant de h=1 à h=2), ou par Horner (en transformant la non-résonance des tranches en lemme intermédiaire) ?

R47 doit exploiter 4 agents en 2 binômes parallèles.
Pas de dispersion.
Pas de benchmark de confort.

---

# ORGANISATION OBLIGATOIRE — 2 BINÔMES

## BINÔME A — ROUTE LSD

### Agent A1 — Investigateur LSD
#### Mission
Analyser la structure exacte ou semi-exacte des collisions à distance de Hamming h=2.

#### Questions obligatoires
1. Quelle est la forme algébrique exacte de
   P_B(g) − P_B'(g) quand h(B,B') = 2 ?
2. Peut-on réduire la condition de collision à une forme bilinéaire / binomiale contrôlable ?
3. Quels sous-cas de h=2 sont plus accessibles :
   - coordonnées adjacentes,
   - coordonnées éloignées,
   - mêmes ordres de grandeur de Δ,
   - autres ?
4. Une borne de type Weil ou une structure de type “deux termes dominants” est-elle crédible ?
5. Quel est le plus petit sous-lemme exact ou semi-exact atteignable pour h=2 ?

#### Livrables
- forme canonique du cas h=2 ;
- classification des sous-cas ;
- verdict honnête : exact prouvable / semi-formel / trop dur.

### Agent A2 — Innovateur LSD
#### Mission
Si h=2 complet est trop dur, proposer un noyau prouvable plus faible mais utile.

#### Candidats autorisés
1. Lemme h=2 restreint :
   un sous-cas naturel de h=2 où la collision est caractérisable proprement.
2. Lemme near-pairs :
   l’excès de collisions vient d’un sous-ensemble très structuré de paires proches, contrôlable combinatoirement.

#### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait sur μ−1 ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle.

#### Règle
À la fin, garder un seul survivant LSD.

---

## BINÔME B — ROUTE HORNER

### Agent B1 — Investigateur Horner
#### Mission
Formaliser la décomposition par tranches B₀=b₀ et isoler le point dur exact de la non-résonance.

#### Questions obligatoires
1. Quelle est la forme canonique de S(r) après conditionnement sur B₀ = b₀ ?
2. Que faudrait-il montrer exactement pour que les tranches ne s’ajoutent pas constructivement ?
3. Cette non-résonance peut-elle être reformulée :
   - en quasi-orthogonalité,
   - en contrôle de corrélation entre tranches,
   - en phase variable,
   - autre ?
4. La base k=2 peut-elle être rendue totalement propre ?
5. Quelle version affaiblie de l’induction serait déjà utile ?

#### Livrables
- formule canonique par tranches ;
- point dur localisé ;
- verdict honnête sur la faisabilité immédiate.

### Agent B2 — Innovateur Horner
#### Mission
Proposer un lemme intermédiaire plus faible que la non-résonance complète, mais suffisant pour faire monter WEL.

#### Candidats autorisés
1. WEL-lite :
   une version qualitative faible de μ→1 pour un régime naturel (p fixé, k grand).
2. Lemme de décorrélation des tranches :
   les corrélations inter-tranches sont globalement petites en moyenne, sans contrôle uniforme total.

#### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait immédiatement ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle.

#### Règle
À la fin, garder un seul survivant Horner.

---

# ARBITRAGE FINAL OBLIGATOIRE
Après les 4 agents, produire une synthèse qui répond explicitement :

1. La route **LSD** a-t-elle franchi une marche réelle ?
2. La route **Horner** a-t-elle franchi une marche réelle ?
3. Laquelle des deux est désormais la **route prioritaire pour R48** ?
4. L’autre route doit-elle être :
   - poursuivie en secondaire,
   - gelée,
   - ou enterrée (avec autopsie) ?

---

# REGISTRE MÉTHODOLOGIQUE OBLIGATOIRE

## 1. Type du round
Rappeler explicitement : P

## 2. IVS — Information Value Score
Note sur 10 avec justification courte :
- potentiel de réfutation
- gain de structure
- proximité d’un lemme
- risque d’accumulation

## 3. Ladder of Proof
Pour chaque objet touché :
- intuition
- observation
- observation répétée
- calcul exact
- semi-formalisation
- schéma de preuve
- lemme candidat
- lemme prouvé
- résultat publiable

## 4. AUTOPSIE DES PISTES FERMÉES (OBLIGATOIRE)
Pour toute piste éliminée, fournir :

- Nom
- Type de mort :
  - contredite
  - mauvaise échelle
  - trop faible
  - non ciblante
  - redondante
  - absorbée
- Hypothèse implicite fausse
- Ce que la mort enseigne
- Où cela redirige

---

# CONTRAINTES MÉTHODOLOGIQUES
Tu dois distinguer explicitement :
- prouvé
- semi-prouvé
- calculé exact
- semi-formalisé
- heuristique
- conjectural
- réfuté

Tu ne dois pas :
- lancer une campagne computationnelle large ;
- garder artificiellement les deux routes si l’une n’avance pas réellement ;
- présenter un sous-cas sympathique comme percée générale.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : un noyau LSD h=2 ou near-pairs utile est formulé.
PASS-2 : un lemme intermédiaire Horner utile est formulé.
PASS-3 : au moins une des deux routes franchit une marche claire dans la Ladder of Proof.
PASS-4 : l’arbitrage LSD vs Horner est beaucoup plus net.
PASS-5 : toute piste affaiblie ou fermée reçoit une autopsie complète.

# ÉCHEC UTILE
Même en cas d’échec, R47 est utile si :
- l’une des deux routes est clairement montrée trop fragile ;
- le bon sous-problème démontrable est mieux isolé ;
- une hiérarchie nette entre route principale et route secondaire émerge.

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats Binôme LSD
5. Résultats Binôme Horner
6. Arbitrage final LSD vs Horner
7. CEC inchangé
8. Objets concernés + Ladder of Proof
9. Ce qui est appris
10. Ce qui est enterré
11. Autopsie des pistes fermées
12. Route prioritaire pour R48
13. Risques / limites
14. Verdict final avec score /10

# CONSIGNE FINALE
R47 doit utiliser les 4 agents pour départager intelligemment les deux routes survivantes.
Le but n’est pas de faire “plus de recherche”.
Le but est de savoir quelle route porte la prochaine vraie marche de preuve.
Chercher le meilleur levier, pas multiplier les paris.
Et pense à mettre le bilan de la mission dans le rapport sur mon disque local, version détaillée.