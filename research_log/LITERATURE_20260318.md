# LITTÉRATURE IA AUTO-AMÉLIORATION (18 Mars 2026)

## Sources clés pour upgrade JEPA

### 1. FunSearch (DeepMind 2024) — Nature
LLM gelé + évaluateur déterministe + boucle évolutive.
Island model pour diversité. Code open-source.
→ **Implémenté partiellement** : hypothesis_evolution.py

### 2. AlphaProof (DeepMind 2024-2025) — Nature
RL + auto-formalisation Lean + MCTS sur tactiques.
Test-time RL : s'améliore pendant l'inférence.
→ **À implémenter** : MCTS sur tactiques Lean

### 3. AlphaEvolve (DeepMind 2025)
Dual-model (Flash + Pro), diff-based prompting, multi-objectif.
→ **À implémenter** : architecture dual-model

### 4. DeepSeek-Prover-V2 (2025)
Décomposition en sous-objectifs + GRPO + Lean.
7B open-source. 82.4% miniF2F.
→ **À implémenter** : décomposition sous-objectifs du Lemme Manquant

### 5. Reflexion (Shinn 2023) + LATS (Zhou 2023)
Auto-critique verbale + mémoire épisodique + MCTS.
→ **Implémenté** : self_reflection.py, failure_memory.json

### 6. Aletheia (DeepMind Feb 2026)
Triade Generator-Verifier-Reviser sur problèmes ouverts.
212/700 problèmes d'Erdős résolus. Article autonome publié.
→ **À implémenter** : triade pour le Lemme Manquant

### 7. MAP-Elites / Quality-Diversity
Archive avec niches comportementales. Bonus de nouveauté.
→ **À implémenter** : archive de stratégies de preuve

## Priorité d'implémentation
1. Triade Generator-Verifier-Reviser (Aletheia)
2. Décomposition sous-objectifs (DeepSeek)
3. MAP-Elites archive (Quality-Diversity)
4. MCTS sur espaces de preuve (AlphaProof)
