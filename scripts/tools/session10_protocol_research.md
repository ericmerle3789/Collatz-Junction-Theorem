# SESSION 10 — RECHERCHE MÉTHODOLOGIQUE
## Enrichissement du DISCOVERY_PROTOCOL v2.1 → v2.2
### Date : 4 mars 2026

---

## SOURCES ÉTUDIÉES

### 1. DeepMind Aletheia (février 2026)
- **Papier** : "Towards Autonomous Mathematics Research" (arXiv:2602.10177)
- **Architecture** : Generator → Verifier → Reviser (boucle itérative)
- **Principes clés** :
  - Le Generateur propose des pistes (créatif, potentiellement faux)
  - Le Vérificateur en langage naturel filtre les erreurs
  - Le Réviseur améliore basé sur le feedback du vérificateur
  - Boucle continue jusqu'à validation OU limite d'itérations atteinte
  - **Tool use intensif** : pas juste du raisonnement, aussi des calculs
  - Score de 95.1% sur IMO-Proof Bench Advanced
  - Premier papier de recherche (Feng26) généré ENTIÈREMENT par IA

**Ce qu'on peut adapter :**
- Formaliser notre boucle Conjecture → Vérification numérique → Révision
- Ajouter un "budget d'itérations" explicite (pas de boucle infinie)
- Le Vérificateur doit être INDÉPENDANT du Générateur (scripts séparés)

### 2. AlphaProof (Nature, 2025)
- **Architecture** : RL + Lean4 formel
- **Principes clés** :
  - Travaille dans un langage FORMEL (Lean) → vérification automatique
  - Test-Time RL : génère des millions de variantes au moment de l'inférence
  - "Le modèle n'est PAS le juge — le noyau formel est le juge"
  - Les hallucinations sont ACCEPTÉES tant que le vérificateur les tue
  - 300 milliards de tokens d'entraînement, 300K preuves formelles
  - A résolu 3/5 problèmes non-géométriques de l'IMO 2024

**Ce qu'on peut adapter :**
- Le principe "le script est le juge, pas le raisonnement"
- Séparer la GÉNÉRATION d'hypothèses de leur VÉRIFICATION
- Tolérer les "hallucinations créatives" SI le test numérique les filtre
- Test-Time RL → pour nous : tester des VARIANTES du problème

### 3. FunSearch (Nature, 2024)
- **Architecture** : LLM + Evaluateur automatique + base évolutive
- **Principes clés** :
  - Le LLM génère des PROGRAMMES (pas juste des réponses)
  - L'Évaluateur exécute et SCORE les programmes
  - Les meilleurs sont gardés dans une base
  - Sélection évolutive : on montre les meilleurs au LLM pour en générer de meilleurs
  - "Exploiter la créativité des LLMs en ne gardant que leurs meilleures idées"
  - A découvert de nouveaux cap sets (problem combinatoire ouvert)

**Ce qu'on peut adapter :**
- Garder un "pool des meilleures approches" (notre MIND_MAP en est une forme)
- L'évaluateur automatique = nos scripts de régression
- Idée d'ÉVOLUTION des approches : chaque session améliore la précédente

### 4. AlphaGeometry 2 (février 2025)
- **Architecture** : Moteur symbolique DDAR + LLM pour constructions auxiliaires
- **Principes clés** :
  - Tente d'abord une preuve SYMBOLIQUE pure
  - Si échec : le LLM propose des constructions auxiliaires
  - Puis re-tente la preuve symbolique
  - Boucle itérative avec tree search
  - 84% des problèmes IMO géométrie 2000-2024

**Ce qu'on peut adapter :**
- Notre équivalent du DDAR = vérification par force brute (scripts)
- Quand le brute force échoue → proposer des "constructions auxiliaires" (lemmes intermédiaires)
- Tree search = explorer systématiquement les branches de notre MIND_MAP

### 5. Tao + AlphaEvolve (novembre 2025)
- **Architecture** : Optimisation par évolution de CODE
- **Principes clés** :
  - Convertir le problème en FONCTION DE SCORE
  - Évoluer du code qui optimise ce score
  - "Les inputs extrémaux ont souvent une structure décrivable par du code court"
  - **Vérification conservatrice** : scoring avec marge d'erreur
  - Les "exploits" (gaming du score) sont un vrai problème → détection humaine
  - Résultats négatifs aussi importants : documenter ce qui ne marche PAS
  - Arithmétique exacte ou par intervalles, PAS flottante
  - Performance varie par domaine : excellent en algèbre finie, faible en théorie des nombres

**Ce qu'on peut adapter :**
- Score function pour notre problème = N₀(d) (il EST notre fonction de score !)
- Scoring conservateur : ne pas se contenter de k=3..15, pousser plus loin
- Résultats négatifs = notre Cimetière des approches
- Arithmétique exacte (on le fait déjà avec Python integers)

### 6. Safe + Lean4 (2025)
- **Architecture** : Chain-of-thought → Lean4 → vérification étape par étape
- **Principes clés** :
  - Chaque étape du raisonnement traduite en Lean4
  - Si la preuve Lean échoue → l'étape est fausse
  - "Audit trail formel" pour chaque conclusion
  - 210K+ théorèmes dans mathlib4

**Ce qu'on peut adapter :**
- Notre objectif Lean4 déjà mentionné (81 théorèmes existants)
- Chaque nouveau lemme devrait avoir un CRITÈRE DE VÉRIFICATION computationnel
- Traçabilité : chaque résultat lié à son script de vérification

### 7. Anti-hallucination (littérature 2025-2026)
- **Principes clés** :
  - OpenAI prouve mathématiquement que les hallucinations sont INÉVITABLES
  - "Il est significativement plus facile de VÉRIFIER une réponse que de la GÉNÉRER"
  - Chain-of-Verification : décomposer, vérifier chaque maillon
  - Structured self-consistency : proof validity +8.3%, symbolic accuracy +9.6%
  - 6 catégories de mitigation : Training, Architecture, Input, Post-generation, Interpretability, Agent-based

**Ce qu'on peut adapter :**
- Chain-of-Verification = notre protocole de 5 tests anti-hallucination
- Ajouter : structured self-consistency (vérifier la même chose de 3 façons)
- Post-generation quality control = régression tests après chaque résultat

---

## SYNTHÈSE : PRINCIPES À INTÉGRER AU PROTOCOLE v2.2

### A. BOUCLE G-V-R (Generate-Verify-Revise) — d'Aletheia
**Principe** : Toute investigation suit le cycle :
1. **GENERATE** : Formuler une conjecture ou approche (créatif, OK si faux)
2. **VERIFY** : Tester numériquement avec un script INDÉPENDANT
3. **REVISE** : Si vérifié → promouvoir. Si réfuté → réviser ou abandonner.
4. **ITERATE** : Jusqu'à preuve complète ou budget d'itérations épuisé.

**Budget** : Maximum 5 itérations par branche. Si pas de progrès → Cimetière.

### B. SÉPARATION GÉNÉRATEUR/JUGE — d'AlphaProof
**Principe** : "Le script est le juge, pas le raisonnement."
- Le raisonnement (théorie) est un GÉNÉRATEUR d'hypothèses
- Le script (calcul) est le JUGE qui valide ou invalide
- Les hallucinations théoriques sont ACCEPTÉES tant que le juge les filtre

### C. POOL ÉVOLUTIF — de FunSearch
**Principe** : Maintenir un pool des meilleures approches qui ÉVOLUE.
- Notre MIND_MAP est ce pool
- Chaque session sélectionne les meilleures branches et les améliore
- Les branches mortes vont au Cimetière (sélection naturelle)

### D. SCORING CONSERVATEUR — de Tao/AlphaEvolve
**Principe** : Ne pas se contenter de résultats numériques limités.
- Toujours tester au-delà de la plage connue (k=3..15 → k=3..25+)
- Arithmétique exacte (jamais de flottants pour les congruences)
- Détecter les "exploits" : un résultat qui marche pour de mauvaises raisons
- Documenter les résultats négatifs aussi soigneusement que les positifs

### E. CONSTRUCTIONS AUXILIAIRES — d'AlphaGeometry
**Principe** : Quand l'approche directe échoue, introduire des objets auxiliaires.
- Lemmes intermédiaires (comme notre TARGET -1 reformulation)
- Substitutions (comme B_j = A_j - j)
- Synthétiques calibrés (retirer une hypothèse pour voir ce qui change)

### F. CHAIN-OF-VERIFICATION — de la littérature anti-hallucination
**Principe** : Vérifier CHAQUE MAILLON de la chaîne logique.
- Pas seulement le résultat final, mais chaque étape intermédiaire
- Chaque lemme a son propre test numérique
- Self-consistency : vérifier le même résultat par 3 méthodes différentes

### G. PREUVE UNIVERSELLE (k ≥ 1 → ∞) — rappel d'Eric
**Principe** : La preuve doit être UNIVERSELLE.
- Pas d'argument limité à une plage de k
- Pas d'argument qui nécessite de vérifier cas par cas
- L'argument doit couvrir k=1, k=2 (cas triviaux), k=3..17 (testés), k→∞
- Pour k=1 et k=2 : corrSum n'est pas défini de la même façon → traitement séparé
- Pour k ≥ 3 : la preuve par Mécanismes I/II/III doit être UNIFORME

---

## MODIFICATIONS CONCRÈTES POUR v2.2

### FOND (contenu mathématique) :
1. Ajouter la boucle G-V-R comme MÉTA-PROCESSUS de chaque investigation
2. Ajouter le scoring conservateur (tester au-delà de k=15)
3. Expliciter la séparation générateur/juge
4. Ajouter le principe de constructions auxiliaires
5. Renforcer la chain-of-verification (3 méthodes par résultat)
6. Rappeler l'objectif k ≥ 1 → ∞ dans chaque phase

### FORME (structure du document) :
1. Ajouter une section "PROCESSUS G-V-R" en début de Phase 3
2. Ajouter un diagramme de la boucle itérative
3. Ajouter des métriques de progrès (inspirées AlphaProof)
4. Enrichir le Cimetière avec la notion d'évolution (FunSearch)
5. Ajouter une section "UNIVERSALITÉ" rappelant l'objectif final
