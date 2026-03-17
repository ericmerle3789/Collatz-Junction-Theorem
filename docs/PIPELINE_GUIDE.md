# Guide du Pipeline Syracuse-JEPA v3.2

**Version :** 3.2 | **Date :** Mars 2026 | **Auteur :** Eric Merle
**Objectif :** Preuve computationnelle que N0(d(k)) = 0 pour tout k >= 3 (pas de cycle non-trivial de Collatz)

---

## Table des matieres

1. [Vue d'ensemble](#vue-densemble)
2. [Concepts mathematiques cles](#concepts-mathematiques-cles)
3. [Guide des modules](#guide-des-modules)
4. [Architecture de la preuve](#architecture-de-la-preuve)
5. [Comment executer](#comment-executer)
6. [Glossaire](#glossaire)

---

## Vue d'ensemble

### Objectif du pipeline

Le pipeline Syracuse-JEPA v3.2 est une **machine de decouverte et de preuve** automatisee pour le Collatz Junction Theorem. Son but : demontrer que pour tout entier k >= 3, aucune composition monotone de S(k) en k parties ne produit un corrSum divisible par d(k), ce qui implique l'inexistence de cycles non-triviaux dans la suite de Collatz.

### Architecture globale (14 stages)

Le pipeline enchaine 14 etapes, de l'exploration brute a la verification formelle en Lean 4 :

```
Explorer -> Analyst -> Pattern Miner -> Strategist
                                            |
                                            v
Spectral -> FCQ -> MapXref -> Creative -> Hybrid Prover
                                            |
                                            v
Prover -> Discovery -> Genius -> Red Team -> Formalizer -> Verifier
```

### Diagramme de flux detaille

```
STAGE  1   EXPLORE ............... Enumeration exhaustive de corrSum pour k=k_min..k_max
STAGE  2   ANALYST ............... Analyse structurelle profonde par premier
STAGE  3   PATTERN MINER ......... Extraction de tendances, invariants, conjectures
STAGE  4   STRATEGIST ............ Classement de strategies de preuve
STAGE  5   SPECTRAL ENGINE ....... Programmation dynamique mod p, preuve par CRT
STAGE  5b  FCQ ENGINE ............ Operateur de transfert Fourier, rayon spectral rho_p
STAGE  5c  MAP CROSS-REFERENCE ... Re-assessment des 195 rounds de recherche
STAGE  5d  CREATIVE ENGINE ....... Le Cerveau Creatif -- detection de resonances
STAGE  5e  HYBRID PROVER ......... Combinaison de toutes les methodes (k=3..200)
STAGE  6   PROVER (Steiner) ...... Extension n_min + verification Barina
STAGE  7   DISCOVERY ............. Jardinier (causes racines) + Innovateur (nouvelles quantites)
STAGE  8   GENIUS ................ Proof gaps, cas difficiles, oracle, contradictions
STAGE  9   RED TEAM .............. Audit adversarial, cross-validation, falsification
STAGE 10   FORMALIZE + VERIFY .... Generation Lean 4 + verification par le kernel
```

---

## Concepts mathematiques cles

### corrSum, d(k), S(k)

La colonne vertebrale du Junction Theorem repose sur trois quantites :

**S(k)** -- L'exposant optimal de 2 :
```
S(k) = ceil(k * log2(3))
```
C'est le plus petit entier tel que 2^S > 3^k.

**d(k)** -- Le denominateur :
```
d(k) = 2^S(k) - 3^k
```
C'est toujours un entier positif, impair, et premier avec 3 pour k >= 2.

**corrSum(A, k)** -- La somme correlative :
```
corrSum(A, k) = SUM_{i=0}^{k-1} 3^{k-1-i} * 2^{a_i}
```
ou A = (a_0 <= a_1 <= ... <= a_{k-1}) est une composition monotone de S en k parties.

**Junction Theorem :** Si un cycle de longueur k existe dans Collatz, alors il existe une composition monotone A telle que corrSum(A, k) = 0 mod d(k). La contraposee est : si N0(d(k)) = #{A monotone : corrSum(A,k) = 0 mod d(k)} = 0, alors aucun k-cycle n'existe.

### FCQ (Fourier-based Counting with Quotients)

Methode spectrale pour prouver N0(p) = 0 pour un premier p | d(k).

**Rayon spectral libre :**
```
rho_p = max_{a != 0} |SUM_{j=0}^{q-1} omega^{a * 2^j mod p}| / q
```
ou q = ord_p(2) et omega = e^{2*pi*i/p}.

**Borne FCQ :**
```
R(p, k) = q * rho_p^{k-1}
```
Si R(p, k) < 1 pour un p | d(k), alors N0(p) = 0, donc N0(d) = 0 par CRT.

**Resultats cles :**
- rho_5 = 1/4 exactement (2 est racine primitive mod 5)
- R(p, 18) < 1 pour tout p >= 5
- Quand 2 est racine primitive mod p : rho_p = 1/(p-1)

### Rayon spectral rho_p

Pour tout premier p >= 5, on a rho_p < 1. C'est un fait calculatoire verifie jusqu'a p = 2000 et demontre theoriquement : les q valeurs distinctes {2^j mod p} ne peuvent produire une somme de racines de l'unite de module q.

### Borne de Steiner n_min

Si un k-cycle existe avec plus petit element n_min, alors :
```
n_min <= (3^k - 1) * 2^{S-k-1} / d(k)
```
Si cette borne tombe sous 2^71 (limite de verification de Barina 2025), le cycle est exclu par contradiction.

---

## Guide des modules

### 1. `run_pipeline_v3.py` -- Orchestrateur principal

**Role :** Point d'entree du pipeline. Enchaine les 14 stages et produit un rapport JSON complet.

**Fonction principale :**
```python
def run_pipeline_v3(
    k_min: int = 3,
    k_max: int = 40,
    lean_dir: str = 'lean4_proof',
    max_retries: int = 3,
    timeout: int = 600,
    analysis_only: bool = False,
    full_scan: bool = False
) -> dict
```

| Parametre | Description |
|-----------|-------------|
| `k_min`, `k_max` | Plage de k a explorer (defaut 3..40) |
| `lean_dir` | Repertoire du projet Lean 4 |
| `max_retries` | Tentatives de verification Lean |
| `timeout` | Timeout Lean en secondes |
| `analysis_only` | Stages 1-9 seulement, pas de Lean |
| `full_scan` | Etend les scans spectraux jusqu'a k=200 |

**Sorties :**
- `analysis_result_v3.json` : resultats intermediaires (insights, strategies, spectral, etc.)
- `pipeline_result_v3.json` : resultat final incluant le build Lean

**Dependances :** Tous les modules du pipeline.

---

### 2. `analyst.py` -- Primitives de theorie des nombres

**Role :** Analyse structurelle profonde. Etudie POURQUOI l'evitement fonctionne : factorisation premiere de d(k), ordres multiplicatifs, sous-groupes, donnees spectrales.

**Fonctions principales :**

```python
def factorize(n: int, limit: int = 10**7) -> List[Tuple[int, int]]
```
Factorisation premiere par division. Retourne `[(p, e), ...]`.

```python
def multiplicative_order(a: int, n: int) -> int
```
Calcule ord_n(a) via factorisation de phi(n). Complexite O(sqrt(n) * log n).

```python
def is_in_subgroup(target: int, generator: int, p: int) -> bool
```
Teste si `target` appartient au sous-groupe engendre par `generator` dans (Z/pZ)*.

```python
def euler_phi(n: int) -> int
```
Indicatrice d'Euler.

```python
def analyze_prime(p: int, e: int, k: int, S: int,
                  compositions: list = None) -> PrimeAnalysis
```
Analyse detaillee d'un premier p | d(k) : ord_p(2), ord_p(3), 3 dans <2>?, adequation, borne rho, distribution corrSum mod p.

```python
def analyze_k(k: int, max_compositions: int = 100_000) -> AnalysisResult
```
Analyse structurelle complete pour un k : factorisation, per-prime analysis, produit rho, gap analysis, budget operatoriel, estimations LDS et FCQ.

```python
def analyze_range(k_min: int = 3, k_max: int = 40,
                  max_compositions: int = 500_000
                  ) -> Tuple[List[AnalysisResult], List[CrossKInsight]]
```
Analyse croisee sur une plage de k. Detecte 8 types de patterns : croissance du gap, decroissance du produit rho, prevalence des premiers adequats, structure 3 dans <2>, croissance des ordres, convergence FCQ, ratio de budget, structure du fantome k=4.

```python
def format_insights(insights: List[CrossKInsight]) -> str
```
Mise en forme des insights pour affichage.

**Dataclasses cles :**
- `PrimeAnalysis` : analyse d'un premier (p, e, ord, adequation, rho, avoidance_ratio...)
- `AnalysisResult` : analyse complete d'un k (S, d, factorisation, prime_analyses, product_rho_bound, gap, budget, LDS, FCQ...)
- `CrossKInsight` : insight decouverte inter-k (categorie, description, confiance, lien vers piste)

---

### 3. `spectral.py` -- Analyse spectrale par programmation dynamique

**Role :** Calcul exact de N0(p) = #{compositions monotones avec corrSum = 0 mod p} via DP. Ne necessite PAS l'enumeration de toutes les compositions.

**Insight cle :** Pour l'evitement, N0(d)=0 decoule du CRT si N0(p)=0 pour UN SEUL premier p|d. Le module teste les premiers par taille croissante (plus petit = DP plus rapide).

**Fonctions principales :**

```python
def count_compositions_with_residue(
    k: int, S: int, p: int, target_r: int = 0
) -> Tuple[int, int]
```
Compte les compositions monotones avec corrSum = target_r mod p. Retourne (n_matching, n_total). Complexite : O(k * p * S^2). DP avec memoization sur l'etat (position j, residu courant mod p, valeur min, somme restante).

```python
def check_avoidance_prime(k: int, p: int) -> PrimeAvoidanceResult
```
Verifie si N0(p) = 0 pour un premier p specifique.

```python
def prove_avoidance(k: int, max_prime: int = 500) -> Optional[AvoidanceProof]
```
Tente de prouver N0(d(k)) = 0 en trouvant un premier temoin p | d avec N0(p) = 0.

```python
def extended_avoidance_scan(k_min: int = 3, k_max: int = 200,
                             max_prime: int = 500) -> List[dict]
```
Scan complet des k. Pour chaque k, cherche un premier p | d(k) avec p <= max_prime tel que N0(p) = 0.

```python
def generate_lean_theorems_extended(proofs: List[dict],
                                     k_max_native: int = 40) -> str
```
Genere des theoremes Lean pour les preuves d'evitement au-dela de native_decide.

**Dataclasses :**
- `PrimeAvoidanceResult` : resultat N0(p) pour un premier (p, k, S, n_zero, n_total, avoids, fraction)
- `AvoidanceProof` : preuve N0(d) = 0 via CRT (k, d, method, witness_prime, details)

---

### 4. `fcq_transfer.py` -- Operateur de transfert FCQ

**Role :** Implementation R196-R197. Calcule le rayon spectral exact rho_p pour chaque premier, avec et sans contrainte de monotonie. Produit des certificats d'evitement.

**Fonctions principales :**

```python
def compute_rho_free(p: int, q: int) -> Tuple[float, int]
```
Calcule rho_p libre (sans monotonie) = max_{a != 0} |SUM_{j=0}^{q-1} omega^{a*2^j mod p}| / q. Retourne (rho, argmax_a). Pour p ou 2 est racine primitive (q = p-1) : SUM_{t dans (Z/pZ)*} omega^{at} = -1, donc rho_p = 1/(p-1).

```python
def compute_rho_monotone(k: int, S: int, p: int) -> Tuple[float, int, int]
```
Calcule le rho effectif AVEC contrainte de monotonie via DP + DFT sur la distribution des residus. Retourne (effective_rho, N0, N_total). Couteux car necessite p appels DP.

```python
def analyze_fcq_prime(k: int, p: int) -> FCQPrimeResult
```
Analyse FCQ complete pour une paire (k, p) : rho libre et monotone, R libre et monotone, N0 exact.

```python
def analyze_fcq_k(k: int, max_prime: int = 500) -> FCQGlobalResult
```
Analyse FCQ pour tous les premiers de d(k). Identifie le meilleur premier et le premier "tueur".

```python
def verify_rho5() -> bool
```
Verification que rho_5 = 1/4 exactement (R197).

```python
def run_fcq_study(k_max: int = 80, max_prime: int = 200) -> List[FCQGlobalResult]
```
Etude FCQ complete pour k=3..k_max. Statistiques par premier, comparaison monotone vs libre, analyse des racines primitives.

```python
def compute_rho_table(max_prime: int = 500) -> Dict[int, Tuple[float, int]]
```
Table de rho_p pour tous les premiers jusqu'a max_prime. Verifie les predictions theoriques (p=3: rho=1/2, p=5: rho=1/4, p=7: rho=1/3).

```python
def fcq_avoidance_certificate(k: int, max_prime: int = 500) -> Optional[dict]
```
Produit un certificat d'evitement FCQ pour un k donne. Deux types : exact_dp (N0=0 par DP) ou fcq_bound (R < 1).

**Dataclasses :**
- `FCQPrimeResult` : resultat pour un (k, p) (q, rho_free, R_free, rho_monotone, R_monotone, N0_actual, proves_avoidance, is_primitive_root)
- `FCQGlobalResult` : resultat pour un k (best_prime, best_R, killing_prime, proves_avoidance)

---

### 5. `creative_engine.py` -- Le Cerveau Creatif (CCE)

**Role :** Decouverte de nouvelles quantites et relations mathematiques par combinaison exhaustive de proprietes. Inspire de FunSearch (DeepMind), AlphaProof, et de la philosophie Investigateur racinaire + Innovateur deductif.

**Architecture en 4 organes :**

1. **Le Terreau (Seed Bank)** -- Atomes mathematiques extraits du pipeline : proprietes, bornes, identites, structures.
2. **Le Capteur (Resonance Detector)** -- Detecte les tensions/resonances entre graines. Quand deux proprietes interagissent de maniere non-triviale, c'est une "idee captee du futur".
3. **L'Innovateur (Constructor)** -- Construit de nouveaux objets mathematiques a partir des resonances. Chaque construction est motivee par un gap identifie.
4. **Le Juge (Verifier + Red Team)** -- Teste rigoureusement chaque innovation. Distingue reformulation (zero contenu) de veritable progres (nouveau contenu quantitatif).

**Fonctions principales :**

```python
def plant_seeds(k_max: int = 40) -> List[Seed]
```
Extrait les atomes mathematiques du pipeline (rho, ordres, gaps, entropie, etc.).

```python
def detect_resonances(seeds: List[Seed], k_max: int = 25) -> List[Resonance]
```
Detecte les interactions non-triviales entre paires de graines.

```python
def construct_innovations(seeds: List[Seed], resonances: List[Resonance],
                          k_max: int = 25) -> List[Innovation]
```
Construit de nouveaux objets mathematiques a partir des resonances detectees.

```python
def judge_innovations(innovations: List[Innovation],
                      k_max: int = 25) -> List[Innovation]
```
Teste chaque innovation : distingue reformulation (zero contenu) de vrai progres.

```python
def run_creative_engine(k_max: int = 25) -> CreativeResult
```
Enchaine les 4 organes. Retourne un `CreativeResult` avec `seeds_planted`, `resonances_detected`, `innovations_born`, `innovations_surviving`.

**Dataclasses :**
- `Seed` : atome mathematique (name, category, values, universality, relevance_to_gap)
- `Resonance` : tension entre deux graines (seed_a, seed_b, type, strength, gap_it_addresses)
- `Innovation` : nouvel objet construit (name, definition, formula, verified_range, proof_impact)
- `CreativeResult` : bilan du cycle creatif

---

### 6. `hybrid_prover.py` -- Hybrid Prover

**Role :** Combine TOUTES les methodes disponibles pour prouver N0(d(k)) = 0 pour chaque k=3..200, dans l'ordre du cout croissant.

**Arsenal de methodes :**

| Methode | Description | Cout |
|---------|-------------|------|
| A. FCQ Primitive Root | rho = 1/(p-1), instantane | Tres faible |
| B. Spectral DP | N0(p) direct, rapide pour petit p | Faible |
| C. FCQ General | rho_p < 1 pour p a grand ordre | Moyen |
| D. Steiner + Barina | n_min < 2^71 | Faible |

**Fonctions principales :**

```python
def try_fcq_primitive(k: int, max_prime: int = 50000) -> Optional[ProofCertificate]
```
Tente FCQ avec les premiers ou 2 est racine primitive.

```python
def try_spectral_dp(k: int, max_prime: int = 500) -> Optional[ProofCertificate]
```
Tente le calcul DP direct de N0(p) pour les petits premiers. Verifie la complexite avant de lancer (k * p * S^2 < 10^8).

```python
def try_fcq_general(k: int, max_prime: int = 50000) -> Optional[ProofCertificate]
```
Tente FCQ avec n'importe quel premier (pas seulement racines primitives). Cache les rho pour eviter les recalculs.

```python
def try_steiner(k: int) -> Optional[ProofCertificate]
```
Argument de Steiner : si un cycle existe, n_min <= borne. Si borne.bit_length() <= 71, Barina l'exclut.

```python
def prove_all(k_min: int = 3, k_max: int = 200) -> List[ProofCertificate]
```
Tente de prouver N0(d(k)) = 0 pour tous les k, methodes par ordre de cout. Produit un certificat NONE pour les cas non resolus.

```python
def run_hybrid_prover(k_min: int = 3, k_max: int = 200) -> dict
```
Execution complete avec statistiques par methode et liste des cas ouverts.

**Dataclass :**
- `ProofCertificate` : certificat de preuve (k, proved, method, witness_prime, witness_ord, is_primitive_root, rho, R_bound, n0_exact, n_total, computation_time, details)

---

### 7. `teleological_study.py` -- Etude teleologique

**Role :** Travaille a rebours depuis la structure de la preuve. Decouverte CCE Cycle 1 : les paires (k, p) evitantes ont systematiquement q/k >> 1, tandis que les non-evitantes ont q/k ~ 1.

**Fonctions principales :**

```python
def scan_avoidance_pairs(k_max: int = 50,
                          max_prime: int = 200) -> List[AvoidancePair]
```
Scanne toutes les paires (k, p) et calcule N0(p) exact, ord_p(2), q/k, borne FCQ.

```python
def analyze_threshold(pairs: List[AvoidancePair]) -> ThresholdAnalysis
```
Analyse du seuil q/k qui separe les paires evitantes des non-evitantes. Determine si la separation est nette (clean) ou s'il y a chevauchement.

```python
def study_near_misses(pairs: List[AvoidancePair]) -> List[dict]
```
Etudie les paires proches du seuil (mecanisme de l'evitement). Les 20 "quasi-evitements" les plus proches.

```python
def study_primitive_root_effect(pairs: List[AvoidancePair]) -> dict
```
Correlation entre racines primitives et evitement. Compare taux d'evitement primitives vs non-primitives.

```python
def run_teleological_study(k_max: int = 40,
                            max_prime: int = 100) -> dict
```
Etude complete en 5 phases : scan, threshold, near-misses, primitive roots, distribution q/k.

**Dataclasses :**
- `AvoidancePair` : paire (k, p) avec donnees d'evitement (q, q_over_k, n0, avoids, rho_free, R_bound, fcq_proves)
- `ThresholdAnalysis` : analyse du seuil (min_avoiding_qk, max_non_avoiding_qk, separation_gap, has_clean_separation, threshold, confidence, exceptions)

---

### 8. `artin_study.py` -- Etude des racines primitives d'Artin

**Role :** Question centrale : pour tout k >= 3, est-ce que d(k) a au moins un facteur premier p avec 2 racine primitive mod p ? Si oui, FCQ + CRT conclut.

**Connexion a Artin :** La conjecture d'Artin (1927) predit que 2 est racine primitive pour une infinite de premiers. Hooley (1967) l'a prouvee sous GRH. Heath-Brown (1986) a prouve inconditionnellement qu'au moins un de {2, 3, 5} est racine primitive pour une infinite de premiers.

**Fonctions principales :**

```python
def analyze_artin_profile(k: int, max_prime: int = 50000) -> ArtinProfile
```
Profil Artin pour d(k) : nombre de facteurs racines primitives, plus petite/grande, densite, FCQ suffisant ?

```python
def scan_artin_profiles(k_max: int = 80,
                         max_prime: int = 10000) -> List[ArtinProfile]
```
Scan de tous les k. Identifie les k sans racine primitive.

```python
def analyze_primitive_density_trend(profiles: List[ArtinProfile]) -> dict
```
Compare la densite observee avec la constante d'Artin (environ 0.3740).

```python
def find_minimal_k_for_fcq(profiles: List[ArtinProfile]) -> dict
```
Pour chaque k, quel est le plus petit premier qui fait marcher FCQ ? Regression log(p) vs k.

```python
def run_artin_study(k_max: int = 60, max_prime: int = 10000) -> dict
```
Etude complete en 3 phases.

**Dataclass :**
- `ArtinProfile` : profil d'un k (n_prime_factors, n_primitive_root, smallest_primitive, primitive_density, best_rho, best_R, fcq_sufficient)

---

### 9. `effective_budget.py` -- Budget Spectral Effectif (ESB)

**Role :** Innovation CCE Cycle 2. Le gap 1.35x dans le framework operatoriel est un artefact de l'hypothese de contraction lineaire : budget = k * taux. En realite, la dimension effective des compositions monotones est dim_eff = log2(C_mono) ~ C_HR * sqrt(S), bien inferieure a k-1. Le ratio de compression dim_eff/dim_total tend vers 0.

**Fonctions principales :**

```python
def partitions_at_most_k(n: int, k: int) -> int
```
Compte les partitions de n en au plus k parties (DP).

```python
def compute_esb(k: int, p: int) -> ESBResult
```
Calcule le budget spectral effectif pour (k, p). Trois modeles compares :
- **Modele A** (standard) : R = q * rho^{k-1}
- **Modele B** (effectif) : R = q * rho^{dim_eff} (optimiste)
- **Modele C** (geometrique) : R = q * rho^{sqrt(dim_eff * (k-1))} (intermediaire)

```python
def scan_esb(k_max: int = 50, max_prime: int = 200) -> dict
```
Scan comparatif FCQ standard vs ESB. Compte les cas supplementaires prouves par ESB.

**Dataclass :**
- `ESBResult` : budget pour (k, p) (dim_eff, dim_total, compression, contraction, esb, fcq_bound, esb_positive, fcq_proves)

---

### 10. `universal_study.py` -- Etude de preuve universelle

**Role :** Explore les 3 voies vers l'universalite (preuve pour TOUT k sans cas par cas).

**Les 3 voies :**
- **PATH A** -- Theorie algebrique des nombres (Zsygmondy/cyclotomique) : d(k) = a^k - b^k a un diviseur premier primitif pour k impair
- **PATH B** -- Theorie analytique des nombres (Conjecture M) : borner |T(t)| <= C * k^{-delta}
- **PATH C** -- Transcendance + Baker : exploiter le produit multiplicatif PROD(3 + 1/n_i) = 2^S

**Fonctions principales :**

```python
def analyze_zsygmondy(k_max: int = 200) -> List[dict]
```
Analyse Zsygmondy de d(k) = 2^S - 3^k. Pour k impair et > 6 : Zsygmondy garantit un diviseur premier primitif p = 1 mod k. 7/12 cas residuels sont impairs.

```python
def explore_cyclotomic_structure(k_max: int = 50) -> dict
```
Decomposition cyclotomique pour k impair : d(k) = Phi_k(a,b) * (produit sur d|k, d<k). Les diviseurs primitifs sont dans Phi_k(a,b).

```python
def run_universal_study(k_max: int = 200) -> dict
```
Etude complete avec synthese et recommandation (PATH A pour k impairs + Steiner extension pour k pairs).

---

### 11. `rho_universal.py` -- Verification universelle rho < 1

**Role :** Verifie que rho_p < 1 pour TOUS les premiers p >= 5. Calcule k_min(p) = seuil a partir duquel FCQ prouve l'evitement.

**Fonctions principales :**

```python
def compute_rho(p: int) -> Tuple[float, int]
```
Calcul exact de rho_p et ord_p(2) pour un premier p. Itere sur tous les a de 1 a p-1.

```python
def compute_rho_fast(p: int, sample_limit: int = 500) -> Tuple[float, int]
```
Version rapide avec echantillonnage pour grands premiers (p > 500) : premiers 200, derniers 200, et valeurs espacees.

```python
def compute_k_min(q: int, rho: float) -> int
```
Calcule k_min = ceil(1 + log(q)/log(1/rho)).

```python
def verify_rho_universal(p_max: int = 2000, fast: bool = False) -> List[PrimeRhoData]
```
Verifie rho < 1 pour tous les premiers 5 <= p <= p_max. Produit statistiques k_min.

```python
def analyze_kmin_growth(results: List[PrimeRhoData]) -> dict
```
Regression lineaire k_min vs log(p). Predit k_min pour 10^6, 10^9, 10^12, 10^18.

```python
def test_residual_cases(results: List[PrimeRhoData]) -> dict
```
Teste si k_min(p) <= k pour les 9 cas residuels parmi les premiers connus.

```python
def run_rho_universal(p_max: int = 2000, fast: bool = False) -> dict
```
Verification complete en 3 phases.

**Dependance :** `sympy.primerange` pour l'enumeration des premiers.

**Dataclass :**
- `PrimeRhoData` : donnees rho pour un premier (p, q, rho, k_min, is_prim_root)

---

### 12. `proof_structure.py` -- Structure complete de la preuve

**Role :** Assemblage des 3 ingredients de la preuve et verification cas par cas pour k=3..200.

**Les 3 ingredients :**

1. **Contraction spectrale universelle** : rho_p < 1 pour tout p >= 5
2. **Denominateur positif** : d(k) >= 5, impair, premier avec 3 pour k >= 3
3. **Seuil FCQ** : k_min(p) petit (<= 7 pour p <= 2000)

**Fonctions principales :**

```python
def verify_ingredient_1(p_max: int = 500) -> dict
```
Verifie rho_p < 1 pour tous les premiers jusqu'a p_max. Retourne all_pass, max_kmin, data.

```python
def verify_ingredient_2(k_max: int = 200) -> dict
```
Verifie d(k) > 0, impair, premier avec 3 pour tout k. Retourne plage min/max facteurs.

```python
def prove_case(k: int, max_prime: int = 50000) -> CaseCertificate
```
Preuve pour un k individuel : d'abord FCQ (petits premiers, calcul rho, borne R), puis Steiner+Barina.

```python
def run_full_proof(k_max: int = 200) -> ProofStatus
```
Preuve complete pour k=3..k_max. Retourne le statut global.

**Dataclasses :**
- `ProofStatus` : statut global (k_max_tested, n_proved, n_total, n_open, open_cases, methods, rho_universal_verified_up_to, rho_all_pass, kmin_max_observed, kmin_regression_coeff, residual_details)
- `CaseCertificate` : certificat pour un k (method, witness_prime, witness_ord, rho, kmin, details)

---

### 13. `discovery.py` -- Jardinier + Innovateur

**Role :** Deux philosophies complementaires de decouverte mathematique.

**JARDINIER** (Root-Cause Investigator) : creuse la chaine des "pourquoi" sur 4 niveaux :
```
Niveau 0 : Le phenomene (N0(d(k))=0)
Niveau 1 : Decomposition CRT
Niveau 2 : Analyse par premier (zero-sets per prime)
Niveau 3 : Intersection des zero-sets (vide?)
Niveau 4 : Cause structurelle profonde (lattice monotone + incommensurabilite 2^a/3^b)
```

**INNOVATEUR** (Deductive Innovator) : cree de nouvelles quantites mathematiques.

**Fonctions principales :**

```python
def investigate_avoidance_root(k: int) -> RootCause
```
Investigation de la cause racine de N0(d(k))=0. Produit une chaine de causalites.

```python
def discover_gap_spectrum(k_max: int = 30) -> Innovation
```
**Nouvelle quantite** : G(k) = {min(r, d-r)/d : r = corrSum(A,k) mod d(k), A monotone}. Mesure la FORCE de l'evitement, pas seulement son existence.

```python
def discover_prime_avoidance_fingerprint(k_max: int = 25) -> Innovation
```
**Nouvelle quantite** : F(k) = (N0(p_1)/N, N0(p_2)/N, ...) pour p_i | d(k). Revele quels premiers portent l'evitement et lesquels sont neutres.

```python
def discover_monotonicity_cost(k_max: int = 20) -> Innovation
```
**Nouvelle quantite** : M(k) = N0(d,mono) / (N(mono)/d). Si M(k) = 0 : la monotonie suffit a empecher corrSum = 0 mod d.

```python
def run_discovery(k_max: int = 25) -> Tuple[List[RootCause], List[Innovation]]
```
Execution complete. Investigue k in {3, 4, 7, 10, 13, 20, 22, 25} puis decouvre 3 quantites.

**Dataclasses :**
- `RootCause` : explication causale (phenomenon, depth, chain, deepest_cause, is_structural, universality, formalizability)
- `Innovation` : nouvel objet (name, definition, motivation, computed_values, pattern, conjecture, novelty)

---

### 14. `genius.py` -- Detecteur de lacunes de preuve

**Role :** 4 moteurs qui vont la ou un LLM ne peut pas aller, car ils necessitent du calcul exhaustif sur des millions de points de donnees.

**Moteur 1 : PROOF GAP DETECTOR**

```python
def detect_proof_gaps(k_max: int = 40) -> List[ProofGap]
```
Pour chaque strategie de preuve, identifie le lemme manquant EXACT avec son enonce mathematique precis, le type (bound, uniformity, structure, combinatorial), la difficulte, et l'evidence disponible. Detecte 5 types de gaps : uniformite LDS+FCQ, borne operatorielle, intersection CRT, extension Steiner, structure des sous-groupes.

**Moteur 2 : HARD CASE ANALYZER**

```python
def analyze_hard_cases(k_max: int = 25) -> List[HardCase]
```
Trouve les k ou l'evitement tient de justesse. Score de difficulte 0-10 base sur : taille du gap normalise, nombre de quasi-collisions, nombre de petits premiers.

**Moteur 3 : ASYMPTOTIC ORACLE**

```python
def build_asymptotic_oracle(k_max: int = 25) -> List[AsymptoticPrediction]
```
4 predictions asymptotiques avec regression lineaire et R^2 :
1. Deficit entropique gamma(k) = log2(d) - log2(C)
2. Ratio de couverture C(k)/d(k)
3. Croissance du min gap
4. Nombre de facteurs premiers de d(k)

**Moteur 4 : CONTRADICTION AMPLIFIER**

```python
def amplify_contradictions(k_max: int = 25) -> List[Contradiction]
```
Suppose qu'un k-cycle EXISTE et derive des consequences : borne n_min (Steiner), enumeration des compositions candidates, contraintes modulaires, deficit entropique.

```python
def run_genius(k_max: int = 25) -> dict
```
Execution des 4 moteurs avec synthese.

**Dataclasses :**
- `ProofGap` : lacune de preuve (strategy, gap_statement, gap_type, difficulty, connects_to)
- `HardCase` : cas difficile (k, difficulty_score, smallest_nonzero_gap, critical_prime, vulnerability)
- `AsymptoticPrediction` : prediction (quantity, model, prediction_k100, prediction_k1000, confidence, warning)
- `Contradiction` : contradiction derivee (assumption, consequence, absurdity_level, is_proved_impossible)

---

### 15. `redteam.py` -- Audit adversarial Red Team

**Role :** Chaque affirmation doit survivre a un test adversarial. Le module cross-valide par methodes independantes, falsifie activement, detecte le rebranding, et teste les cas limites.

**Suites d'audit :**

| Suite | Fonction | Verifie |
|-------|----------|---------|
| Identites de base | `audit_basic_identities()` | S(k) = ceil(k*log2(3)), d(k) > 0, formule corrSum, fantomes k=2 et k=4 |
| Cross-check evitement | `audit_avoidance_cross_check()` | N0 par 2 methodes independantes pour k=3..25 |
| Factorisation | `audit_factorization()` | PROD(p^e) == d(k) pour k=3..50 |
| Ordres multiplicatifs | `audit_multiplicative_orders()` | ord correct (2^ord = 1 mod p) et minimal pour k=3..30 |
| Bornes de Steiner | `audit_steiner_bounds()` | Borne n_min vs max reel de corrSum/d pour k=3..25 |
| Coherence Lean | `audit_lean_consistency()` | checkAvoidance k = true dans Lean correspond a N0=0 en Python |

```python
def run_full_audit() -> List[AuditResult]
```
Execution de toutes les suites. Retourne la liste des resultats avec statut et severite.

**Niveaux de statut :**
- `PASS` : verification reussie
- `FAIL` : verification echouee
- `WARNING` : situation ambigue

**Niveaux de severite :**
- `CRITICAL` : compromet l'integrite du pipeline
- `HIGH` : resultat possiblement incorrect
- `MEDIUM` : irregularite a investiguer
- `LOW` : verification de routine

**Dataclass :**
- `AuditResult` : resultat d'audit (check_name, status, details, severity)

---

### 16. `map_reeval.py` -- Re-assessment de la carte de recherche

**Role :** Cross-reference les 195 rounds de recherche (RESEARCH_MAP.md) avec les calculs exacts du pipeline. Re-evalue les pistes fermees et decouvre des invariants structurels.

**Fonctions principales :**

```python
def compute_full_residue_data(k: int, p: int) -> dict
```
Distribution complete des residus mod p pour un k donne (p appels DP).

```python
def reeval_ratio_law(k_max: int = 80) -> PisteReeval
```
Re-assessment R29 : la loi des ratios N0*p/C -> 1 est FAUSSE (max rho = 3.37).

```python
def reeval_crt_anticorrelation(k_max: int = 40) -> PisteReeval
```
Re-assessment R84-R86 : le produit CRT >> 1/d (ratio jusqu'a 10^36). L'independence echoue.

```python
def reeval_order_diversity(k_max: int = 80) -> PisteReeval
```
Re-assessment R31 : l'ordre eleve aide mais ne suffit pas seul.

```python
def discover_new_invariants(k_max: int = 50) -> List[StructuralInvariant]
```
Decouverte de 4 invariants structurels :
1. 3 n'est PAS dans <2> mod p pour TOUT p | d(k) -- UNIVERSEL
2. ord_p(2) >= 3 pour tout p | d(k) -- UNIVERSEL
3. Deficit entropique ~ lineaire en k
4. N0(p) > 0 pour les petits premiers (evitement = collectif, pas per-prime)

```python
def run_map_reeval(k_max: int = 50) -> dict
```
Re-assessment complete avec synthese.

**Dataclasses :**
- `PisteReeval` : re-assessment (piste_id, name, original_status, new_status, reason, evidence, confidence)
- `StructuralInvariant` : invariant (name, statement, verified_range, counterexample, connects_to, proof_potential)

---

### 17. `generator.py` -- Generation de donnees

**Role :** Generation des compositions monotones et de leurs corrSum pour l'entrainement JEPA et la verification. Ce module fournit les fonctions de base utilisees par tout le pipeline.

**Fonctions principales :**

```python
def compute_S(k: int) -> int
```
S(k) = ceil(k * log2(3)). Utilise `math.ceil` et `math.log2`.

```python
def compute_d(k: int) -> int
```
d(k) = 2^S - 3^k. Utilise le bit-shift `1 << S` pour precision arbitraire.

```python
def corrsum(A: List[int], k: int) -> int
```
corrSum(A, k) = SUM 3^{k-1-i} * 2^{a_i}. Precision arbitraire Python.

```python
def corrsum_terms(A: List[int], k: int) -> List[int]
```
Retourne les termes individuels 3^{k-1-i} * 2^{a_i}.

```python
def corrsum_mod(A: List[int], k: int, m: int) -> int
```
corrSum mod m, calcul efficace par `pow(base, exp, mod)`.

```python
def enumerate_monotone_compositions(k: int, S: int
                                     ) -> Generator[Tuple[int, ...], None, None]
```
Enumere TOUTES les compositions monotones (recursion avec backtracking). **ATTENTION :** exponentiel en k, utiliser seulement pour k <= ~25.

```python
def count_compositions(k: int, S: int) -> int
```
Compte les compositions monotones par DP en O(S * k). Equivalent au nombre de partitions de S en exactement k parties non-negatives.

```python
def sample_monotone_composition(k: int, S: int,
                                 rng: np.random.Generator) -> Tuple[int, ...]
```
Echantillonne une composition aleatoire (methode stars-and-bars + tri). Biais vers les partitions avec plus d'ordonnements distincts (acceptable pour JEPA).

```python
def generate_dataset_exact(k: int) -> dict
```
Dataset exact pour un k : toutes les compositions, corrSums, residus mod d, ratios.

```python
def generate_dataset_sampled(k: int, n_samples: int, seed: int = 42) -> dict
```
Dataset echantillonne pour les grands k.

```python
def generate_multi_view_features(A: Tuple[int, ...], k: int, S: int, d: int) -> dict
```
3 vues pour JEPA :
- **Vue 1 (structurelle)** : composition normalisee, gaps inter-elements
- **Vue 2 (arithmetique)** : log-termes, ratio fractionnaire, residus mod petits premiers
- **Vue 3 (spectrale)** : FFT magnitude et phase de la sequence

```python
def prepare_jepa_batch(dataset: dict, pad_k: int = 50) -> dict
```
Prepare un batch padde pour l'entrainement JEPA (numpy arrays).

---

## Architecture de la preuve

### Les 3 ingredients

```
INGREDIENT 1 -- Contraction spectrale universelle
  Pour tout premier p >= 5 : rho_p < 1
  Preuve : les q valeurs distinctes {2^j mod p} ne peuvent aligner
  q racines de l'unite. Par theorie des sommes de caracteres :
  |S(a)| <= sqrt(p) pour tout a.
  Donc rho_p = max |S(a)|/q <= sqrt(p)/q.
  Quand q > sqrt(p) (~98% des premiers) : rho_p < 1 avec borne explicite.

INGREDIENT 2 -- Denominateur positif
  d(k) = 2^{ceil(k*log2(3))} - 3^k >= 5, impair, premier avec 3, pour k >= 3.
  (Stroeker-Tijdeman 1983, verification elementaire pour petits k)
  Consequence : d(k) a toujours au moins un facteur premier p >= 5.

INGREDIENT 3 -- Seuil FCQ petit
  k_min(p) = ceil(1 + log(q)/log(1/rho_p))
  Observe : k_min(p) <= 7 pour p <= 2000.
  Theorique : k_min(p) = O(log p) avec coefficient ~0.1.
  Avec |S(a)| <= sqrt(p) : k_min(p) <= 1 + 1/(1 - log(sqrt(p))/log(q)).
  Pour q > p^{0.51} : k_min < 52.
```

### Assemblage de la preuve

- **Cas A (k >= K0, grand k)** : tout premier p | d(k) satisfait p <= d(k) <= 2^{1.585k+1}. Par k_min(p) = O(log p) = O(k), et specifiquement k_min <= 0.11*k. Comme k >= K0 >> k_min(p), FCQ prouve N0(p) = 0.

- **Cas B (3 <= k < K0, fini)** : preuve cas par cas par les methodes du hybrid prover.

### Bilan k=3..200

| Methode | Nombre de k prouves |
|---------|:-------------------:|
| FCQ Primitive Root | ~111 |
| FCQ General | ~58 |
| Spectral DP | variable |
| Steiner + Barina | ~16 |
| **Total prouve** | **189/198** |
| **Cas residuels** | **9** |

*(Le total exclut k=4 qui est un fantome connu.)*

### Les 9 cas residuels et strategies

```
k dans {135, 143, 148, 158, 166, 176, 185, 192, 193}
```

Ces k ont d(k) dont les plus petits facteurs premiers sont tres grands (> 10^7). Les d(k) correspondants font 200-304 bits. Strategies pour les resoudre :

1. **Factorisation profonde** : ECM/Pollard pour trouver des facteurs de taille intermediaire dans d(k)
2. **Extension Steiner** : si la verification Collatz est poussee au-dela de 2^71 (ex: 2^80 couvrirait k jusqu'a ~160)
3. **Zsygmondy** (pour les k impairs parmi les residuels : 135, 143, 165, 171, 185, 193) : garantit un diviseur premier primitif p = 1 mod k, avec ord_p(2) | k(k-1)/2 et probablement grand
4. **FCQ avec grands premiers** : si un facteur est trouve avec rho < 1 et k_min <= k

---

## Comment executer

### Prerequis

- **Python** >= 3.10
- **Conda** : environnement `collatz-jepa`
- **Dependances** : `numpy`, `sympy` (pour `primerange` dans `rho_universal.py`)
- **Lean 4** (optionnel, pour la verification formelle au stage 10)

### Installation

```bash
conda activate collatz-jepa
cd /Users/ericmerle/Documents/Collatz-Junction-Theorem
```

### Commandes pour lancer le pipeline

**Execution standard (k=3..40, analyse + verification Lean) :**
```bash
python -m syracuse_jepa.pipeline.run_pipeline_v3
```

**Analyse seule (pas de Lean) :**
```bash
python -m syracuse_jepa.pipeline.run_pipeline_v3 --analysis-only
```

**Scan complet k=3..200 :**
```bash
python -m syracuse_jepa.pipeline.run_pipeline_v3 --full-scan --k-max 200 --analysis-only
```

**Plage personnalisee :**
```bash
python -m syracuse_jepa.pipeline.run_pipeline_v3 --k-min 3 --k-max 80 --analysis-only
```

### Options de ligne de commande

| Option | Defaut | Description |
|--------|--------|-------------|
| `--k-min` | 3 | Premiere valeur de k |
| `--k-max` | 40 | Derniere valeur de k |
| `--lean-dir` | `lean4_proof` | Repertoire du projet Lean |
| `--timeout` | 600 | Timeout Lean (secondes) |
| `--analysis-only` | false | Stages 1-9 seulement |
| `--full-scan` | false | Scan spectral/prover jusqu'a k=200 |

### Executer des modules individuellement

```bash
# Spectral engine (k=3..100)
python -m syracuse_jepa.pipeline.spectral

# FCQ transfer operator (k=3..80)
python -m syracuse_jepa.pipeline.fcq_transfer

# Hybrid prover (k=3..150, argument optionnel)
python -m syracuse_jepa.pipeline.hybrid_prover 150

# Artin study (k=3..60, argument optionnel)
python -m syracuse_jepa.pipeline.artin_study 60

# Teleological study (k=3..30, argument optionnel)
python -m syracuse_jepa.pipeline.teleological_study 30

# Universal rho verification (p <= 2000, argument optionnel)
python -m syracuse_jepa.pipeline.rho_universal 2000
# Ajouter --fast pour echantillonnage des grands premiers

# Complete proof structure (k=3..200)
python -m syracuse_jepa.pipeline.proof_structure 200

# Red Team audit
python -m syracuse_jepa.pipeline.redteam

# Research map re-assessment
python -m syracuse_jepa.pipeline.map_reeval

# Creative engine
python -m syracuse_jepa.pipeline.creative_engine

# Discovery engine
python -m syracuse_jepa.pipeline.discovery

# Genius engine
python -m syracuse_jepa.pipeline.genius

# Data generator validation
python -m syracuse_jepa.data.generator
```

### Fichiers de sortie

| Fichier | Contenu |
|---------|---------|
| `analysis_result_v3.json` | Resultats complets de l'analyse (insights, strategies, spectral) |
| `pipeline_result_v3.json` | Resultat final incluant le build Lean |
| `spectral_results.json` | Resultats du scan spectral CRT |
| `hybrid_results.json` | Certificats du hybrid prover |
| `artin_results.json` | Profils Artin des d(k) |
| `teleological_results.json` | Analyse du seuil q/k |
| `creative_results.json` | Innovations du cerveau creatif |
| `rho_universal_results.json` | Verification rho < 1 pour tous les premiers |
| `proof_status.json` | Statut complet de la preuve |

---

## Glossaire

| Terme | Definition |
|-------|------------|
| **corrSum** | Somme correlative SUM 3^{k-1-i} * 2^{a_i} pour une composition monotone A |
| **d(k)** | Denominateur 2^S - 3^k, ou S = ceil(k*log2(3)) |
| **S(k)** | Plus petit entier tel que 2^S > 3^k |
| **N0(m)** | Nombre de compositions monotones avec corrSum = 0 mod m |
| **Composition monotone** | Tuple (a_0 <= a_1 <= ... <= a_{k-1}), SUM a_i = S |
| **CRT** | Theoreme des restes chinois : N0(d) = 0 si N0(p) = 0 pour un p divisant d |
| **FCQ** | Fourier-based Counting with Quotients -- methode spectrale |
| **rho_p** | Rayon spectral FCQ : max_{a != 0} \|SUM omega^{a*2^j mod p}\| / ord_p(2) |
| **R(p, k)** | Borne FCQ = ord_p(2) * rho_p^{k-1}. Si R < 1, evitement prouve |
| **k_min(p)** | Seuil minimal de k pour que R(p,k) < 1 |
| **ord_p(a)** | Ordre multiplicatif de a modulo p |
| **Racine primitive** | a est racine primitive mod p si ord_p(a) = p-1 |
| **Conjecture d'Artin** | 2 est racine primitive mod p pour une infinite de premiers |
| **Constante d'Artin** | Environ 0.3740 -- densite prevue des premiers ou 2 est racine primitive |
| **Steiner n_min** | Borne superieure sur le plus petit element d'un hypothetique cycle |
| **Barina** | Verification de convergence Collatz jusqu'a 2^71 (2025) |
| **Fantome** | Composition avec corrSum = 0 mod d (k=2 et k=4 en ont) |
| **Premier adequat** | p tel que ord_p(2) impair et -1 n'est pas dans <2> mod p |
| **Gap 1.35x** | Ecart entre le budget spectral disponible et le budget requis (R189) |
| **ESB** | Effective Spectral Budget -- budget ajuste pour la dimension effective |
| **Zsygmondy** | Theoreme : a^n - b^n a un diviseur premier primitif pour n > 6 |
| **CCE** | Collatz Creative Engine -- Le Cerveau Creatif |
| **LDS** | Levier Diophantien Structurel -- k0(p) >= c*q sans GRH (R196-R197) |
| **Conjecture M** | \|T(t)\| <= C*k^{-delta} pour t != 0 -- le verrou principal |
| **Red Team** | Audit adversarial systematique de toutes les affirmations |
| **JEPA** | Joint Embedding Predictive Architecture (LeCun) -- architecture ML du projet |
| **Phi_k(a,b)** | k-ieme polynome cyclotomique applique a (a, b) |
