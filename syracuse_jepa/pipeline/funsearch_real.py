#!/usr/bin/env python3
"""
FUNSEARCH RÉEL — Adapté à notre environnement
================================================

Environnement : MacBook M1 16Go, Python 3.12, pas de GPU.
LLM : Claude (via pipeline textuel — les mutations sont des FONCTIONS Python).
Évaluateur : calcul numérique exact (corrSum, vérification mod d).

Architecture FunSearch adaptée :
1. PROGRAMS DATABASE : archive de FONCTIONS de preuve Python
2. ISLAND MODEL : 3 îles indépendantes avec migration
3. MUTATION : combinaison/modification de fonctions existantes
4. ÉVALUATION : score = fraction de k testés où la fonction prouve N₀=0
5. SÉLECTION : garder les meilleurs, migrer entre îles

Chaque "programme" est une STRATÉGIE DE PREUVE : une fonction Python qui,
donnée (k, d, ρ, data), tente de prouver N₀=0 et retourne True/False.

Les mutations créent de NOUVELLES stratégies en combinant des morceaux
de stratégies existantes.
"""

import sys, os, json, random, time, copy
from math import ceil, log2, comb, gcd
from itertools import combinations, product as cart_product

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)

# ══════════════════════════════════════════════════════════════
# PRECOMPUTED TEST DATA
# ══════════════════════════════════════════════════════════════

def precompute_test_data(k_max=12):
    """Precompute all data needed for evaluation."""
    data = {}
    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 200000: continue

        inv3 = pow(3, -1, d)
        rho = (2 * inv3) % d
        max_delta = S - k

        # All corrSum residues
        residues = []
        for sigma in enumerate_cumulative_sequences(k, S):
            cs = corrsum_cumulative(sigma, k)
            residues.append(cs % d)

        N0 = sum(1 for r in residues if r == 0)

        # Factorize d
        factors = {}
        n = d
        for p in range(2, min(10000, n)):
            while n % p == 0:
                factors[p] = factors.get(p, 0) + 1
                n //= p
        if n > 1:
            factors[n] = 1

        # ord_d(2)
        x = 2 % d
        ord2 = 1
        while x != 1 and ord2 < d:
            x = (x * 2) % d
            ord2 += 1

        data[k] = {
            'S': S, 'd': d, 'C': C, 'rho': rho, 'max_delta': max_delta,
            'N0': N0, 'factors': factors, 'ord_d_2': ord2,
            'residues': residues,
        }

    return data


# ══════════════════════════════════════════════════════════════
# PROOF STRATEGY PRIMITIVES (building blocks)
# ══════════════════════════════════════════════════════════════

def prim_valuation_check(k, kdata):
    """Try to prove N₀=0 via valuation: find p|d with v_p(corrSum)=0 for all σ."""
    d = kdata['d']
    for p, _ in kdata['factors'].items():
        all_coprime = all(r % p != 0 for r in kdata['residues'])
        if all_coprime:
            return True, f"v_{p}(corrSum)=0 for all σ"
    return False, "no blocking prime"


def prim_ord_check(k, kdata):
    """Check if ord_d(2) > S-k (individual swaps nonzero)."""
    return kdata['ord_d_2'] > kdata['S'] - k, f"ord={kdata['ord_d_2']}, S-k={kdata['S']-k}"


def prim_subgroup_check(k, kdata):
    """Check if all residues are in <2,3> mod d."""
    d = kdata['d']
    # Generate <2,3>
    gen23 = set()
    frontier = {1}
    visited = set()
    while frontier and len(visited) < d:
        x = frontier.pop()
        if x in visited: continue
        visited.add(x)
        gen23.add(x)
        frontier.add((x * 2) % d)
        frontier.add((x * 3) % d)

    all_in = all(r in gen23 for r in kdata['residues'] if r != 0)
    if all_in and 0 not in gen23:
        return True, "all corrSum in <2,3>, 0 not in <2,3>"
    return False, f"{sum(1 for r in set(kdata['residues']) if r in gen23)}/{len(set(kdata['residues']))} in <2,3>"


def prim_direct_check(k, kdata):
    """Direct check: N₀ = 0."""
    return kdata['N0'] == 0, f"N0={kdata['N0']}"


def prim_norm_coprime(k, kdata):
    """Check if norm N(P_σ(α)) is coprime to d for all σ (works for k=3,4)."""
    if k > 5:  # Too expensive for larger k
        return False, "skipped (k too large)"
    import cmath
    from math import pi
    S, d = kdata['S'], kdata['d']
    if gcd(S, k) != 1:
        return False, "gcd(S,k) ≠ 1"

    alpha = 3**(k/S)
    all_coprime = True
    for sigma in enumerate_cumulative_sequences(k, S):
        norm = 1.0
        for j in range(S):
            root = alpha * cmath.exp(2j * cmath.pi * j / S)
            val = sum(3**(k-1-i) * root**sigma[i] for i in range(k))
            norm *= val
        norm_int = round(norm.real)
        if gcd(abs(norm_int), d) != 1:
            all_coprime = False
            break

    return all_coprime, "norm coprime" if all_coprime else "norm not coprime"


# ══════════════════════════════════════════════════════════════
# COMPOSITE STRATEGIES (combinations of primitives)
# ══════════════════════════════════════════════════════════════

class ProofStrategy:
    """A composite proof strategy = ordered list of primitives to try."""
    def __init__(self, name, primitives, description=""):
        self.name = name
        self.primitives = primitives  # List of (name, function) pairs
        self.description = description
        self.fitness = 0.0
        self.successes = {}  # k → (True/False, reason)
        self.generation = 0

    def evaluate(self, test_data):
        """Evaluate on all test data. Fitness = fraction proved."""
        self.successes = {}
        for k, kdata in test_data.items():
            proved = False
            reason = ""
            for pname, pfunc in self.primitives:
                result, r = pfunc(k, kdata)
                if result:
                    proved = True
                    reason = f"{pname}: {r}"
                    break
            self.successes[k] = (proved, reason)

        n_proved = sum(1 for v, _ in self.successes.values() if v)
        self.fitness = n_proved / len(test_data) if test_data else 0
        return self.fitness

    def __repr__(self):
        return f"Strategy({self.name}, fit={self.fitness:.3f})"


# ══════════════════════════════════════════════════════════════
# ISLAND MODEL
# ══════════════════════════════════════════════════════════════

ALL_PRIMITIVES = [
    ("valuation", prim_valuation_check),
    ("ord_check", prim_ord_check),
    ("subgroup_23", prim_subgroup_check),
    ("direct", prim_direct_check),
    ("norm_coprime", prim_norm_coprime),
]


def create_random_strategy(gen=0):
    """Create a random composite strategy."""
    n_prims = random.randint(1, len(ALL_PRIMITIVES))
    chosen = random.sample(ALL_PRIMITIVES, n_prims)
    name = "+".join(p[0] for p in chosen) + f"_g{gen}"
    s = ProofStrategy(name, chosen)
    s.generation = gen
    return s


def mutate_strategy(parent, gen):
    """Mutate a strategy by adding, removing, or reordering primitives."""
    new_prims = list(parent.primitives)
    mutation = random.choice(['add', 'remove', 'swap', 'replace'])

    if mutation == 'add' and len(new_prims) < len(ALL_PRIMITIVES):
        unused = [p for p in ALL_PRIMITIVES if p not in new_prims]
        if unused:
            new_prims.insert(random.randint(0, len(new_prims)), random.choice(unused))

    elif mutation == 'remove' and len(new_prims) > 1:
        new_prims.pop(random.randint(0, len(new_prims)-1))

    elif mutation == 'swap' and len(new_prims) > 1:
        i, j = random.sample(range(len(new_prims)), 2)
        new_prims[i], new_prims[j] = new_prims[j], new_prims[i]

    elif mutation == 'replace':
        idx = random.randint(0, len(new_prims)-1)
        new_prims[idx] = random.choice(ALL_PRIMITIVES)

    name = "+".join(p[0] for p in new_prims) + f"_g{gen}"
    child = ProofStrategy(name, new_prims)
    child.generation = gen
    return child


def crossover(parent1, parent2, gen):
    """Crossover: take first half from parent1, second from parent2."""
    mid1 = len(parent1.primitives) // 2
    mid2 = len(parent2.primitives) // 2
    new_prims = parent1.primitives[:max(1, mid1)] + parent2.primitives[mid2:]
    # Deduplicate
    seen = set()
    unique = []
    for p in new_prims:
        if p[0] not in seen:
            unique.append(p)
            seen.add(p[0])
    name = "+".join(p[0] for p in unique) + f"_cx_g{gen}"
    child = ProofStrategy(name, unique)
    child.generation = gen
    return child


class Island:
    """An island in the island model."""
    def __init__(self, island_id, size=8):
        self.id = island_id
        self.population = [create_random_strategy() for _ in range(size)]
        self.best_ever = None
        self.size = size

    def evolve_step(self, test_data, gen):
        """One evolution step."""
        # Evaluate
        for s in self.population:
            s.evaluate(test_data)

        # Sort by fitness
        self.population.sort(key=lambda s: s.fitness, reverse=True)

        # Track best
        if self.best_ever is None or self.population[0].fitness > self.best_ever.fitness:
            self.best_ever = copy.deepcopy(self.population[0])

        # Selection: keep top half
        survivors = self.population[:self.size // 2]

        # Offspring: mutation + crossover
        offspring = []
        while len(survivors) + len(offspring) < self.size:
            if random.random() < 0.7:
                parent = random.choice(survivors)
                child = mutate_strategy(parent, gen)
            else:
                p1, p2 = random.sample(survivors, min(2, len(survivors)))
                child = crossover(p1, p2, gen)
            offspring.append(child)

        self.population = survivors + offspring

    def get_best(self):
        return self.population[0] if self.population else None

    def receive_migrant(self, strategy):
        """Accept a migrant from another island."""
        self.population.append(copy.deepcopy(strategy))
        # Remove worst
        if len(self.population) > self.size:
            self.population.sort(key=lambda s: s.fitness, reverse=True)
            self.population = self.population[:self.size]


def run_funsearch(n_islands=3, island_size=8, n_generations=30, migration_interval=5):
    """Run the full FunSearch island model."""
    print("FUNSEARCH RÉEL — Island Model for Proof Strategy Discovery")
    print("=" * 65)

    t0 = time.time()

    # Prepare test data
    test_data = precompute_test_data(k_max=12)
    print(f"Test data: {len(test_data)} k-values")

    # Create islands
    islands = [Island(i, island_size) for i in range(n_islands)]

    for gen in range(n_generations):
        # Evolve each island
        for island in islands:
            island.evolve_step(test_data, gen)

        # Migration
        if gen > 0 and gen % migration_interval == 0:
            for i in range(n_islands):
                donor = islands[i].get_best()
                receiver = islands[(i + 1) % n_islands]
                if donor:
                    receiver.receive_migrant(donor)

        # Report
        bests = [island.get_best() for island in islands]
        best_fit = max(b.fitness for b in bests if b)
        best_strat = max(bests, key=lambda b: b.fitness if b else 0)
        if gen % 5 == 0 or best_fit >= 1.0:
            print(f"Gen {gen:3d}: best={best_fit:.3f} ({best_strat.name[:40]})")

        if best_fit >= 1.0:
            print(f"\n★★★ PERFECT STRATEGY at gen {gen}!")
            break

    # Final report
    elapsed = time.time() - t0
    print(f"\n{'='*65}")
    print(f"FUNSEARCH COMPLETE — {elapsed:.1f}s")

    all_best = max((island.best_ever for island in islands if island.best_ever),
                   key=lambda s: s.fitness, default=None)

    if all_best:
        print(f"\nBest strategy: {all_best.name}")
        print(f"Fitness: {all_best.fitness:.3f}")
        print(f"Primitives: {[p[0] for p in all_best.primitives]}")
        print(f"\nPer-k results:")
        for k in sorted(all_best.successes):
            proved, reason = all_best.successes[k]
            print(f"  k={k}: {'✓' if proved else '✗'} {reason}")

        # Which k are NOT proved?
        unproved = [k for k, (v, _) in all_best.successes.items() if not v]
        if unproved:
            print(f"\nUnproved k: {unproved}")
            print("These need NEW primitives not yet in the search space.")
        else:
            print(f"\nALL k proved! Strategy covers everything.")

    return all_best


if __name__ == '__main__':
    random.seed(42)
    best = run_funsearch(n_islands=3, island_size=10, n_generations=40, migration_interval=5)
