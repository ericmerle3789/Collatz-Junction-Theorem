#!/usr/bin/env python3
"""
CREATIVE TACTIC GENERATOR — Invents new algebraic operations
================================================================

Le problème des moteurs précédents : ils combinent des PRIMITIVES FIXES.
Un vrai créatif INVENTE de nouvelles opérations.

Architecture inspirée de :
- FunSearch : l'espace de recherche est le PROGRAMME lui-même
- AlphaEvolve : mutations de FONCTIONS, pas de paramètres
- MAP-Elites : diversité comportementale

MÉTHODE : Représenter chaque tactic comme un ARBRE D'OPÉRATIONS
sur les objets mathématiques du graphe. Muter l'arbre pour créer
de nouvelles tactics. Évaluer sur les k de test.

OPÉRATIONS ATOMIQUES sur Z/dZ :
- add(a, b) : a + b mod d
- mul(a, b) : a · b mod d
- pow(a, n) : a^n mod d
- inv(a) : a^{-1} mod d
- gcd(a, d) : pgcd
- ord(a) : ordre multiplicatif
- eval_poly(P, x) : évaluation polynomiale

OPÉRATIONS SUR LES SÉQUENCES :
- sort(δ) : trier
- reverse(δ) : inverser
- shift(δ, n) : décaler
- diff(δ) : différences successives
- cumsum(δ) : sommes cumulées

OPÉRATIONS SUR LES POLYNÔMES :
- factor(P, root) : diviser par (X - root)
- deriv(P) : dérivée
- resultant(P, Q) : résultant
- compose(P, Q) : P(Q(X))
- gcd_poly(P, Q) : pgcd polynomial

L'arbre de tactic est une EXPRESSION composée de ces opérations.
La MUTATION change un sous-arbre. Le CROSSOVER échange des sous-arbres.
"""

import sys, os, random, json, time, copy
from math import ceil, log2, gcd
from typing import Any, List, Optional, Tuple
from dataclasses import dataclass, field
from enum import Enum, auto

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.engine.symbolic_objects import ModularInt, Polynomial, ProofGraph
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


# ══════════════════════════════════════════════════════════════
# EXPRESSION TREES
# ══════════════════════════════════════════════════════════════

class OpType(Enum):
    # Constants
    CONST_RHO = auto()      # ρ = 2/3 mod d
    CONST_D = auto()        # d
    CONST_ONE = auto()      # 1
    CONST_TWO = auto()      # 2
    CONST_THREE = auto()    # 3
    CONST_K = auto()        # k
    CONST_S = auto()        # S
    CONST_CORRSUM = auto()  # corrSum mod d (sequence-dependent)

    # Unary ops on Z/dZ
    INV = auto()            # a^{-1}
    NEG = auto()            # -a
    SQ = auto()             # a²
    ORD = auto()            # multiplicative order

    # Binary ops on Z/dZ
    ADD = auto()            # a + b
    MUL = auto()            # a · b
    POW = auto()            # a^b
    GCD_D = auto()          # gcd(a, d)
    SUB = auto()            # a - b

    # Predicates (return True/False)
    IS_ZERO = auto()        # a = 0?
    IS_UNIT = auto()        # gcd(a,d) = 1?
    GT = auto()             # a > b?
    DIVIDES = auto()        # a | b?


@dataclass
class ExprNode:
    """A node in an expression tree."""
    op: OpType
    children: List['ExprNode'] = field(default_factory=list)
    value: Any = None  # For constants

    def depth(self) -> int:
        if not self.children:
            return 0
        return 1 + max(c.depth() for c in self.children)

    def size(self) -> int:
        return 1 + sum(c.size() for c in self.children)

    def evaluate(self, env: dict) -> Any:
        """Evaluate the expression in the given environment."""
        try:
            if self.op == OpType.CONST_RHO:
                return env['rho']
            elif self.op == OpType.CONST_D:
                return env['d']
            elif self.op == OpType.CONST_ONE:
                return ModularInt(1, env['d'])
            elif self.op == OpType.CONST_TWO:
                return ModularInt(2, env['d'])
            elif self.op == OpType.CONST_THREE:
                return ModularInt(3, env['d'])
            elif self.op == OpType.CONST_K:
                return env['k']
            elif self.op == OpType.CONST_S:
                return env['S']
            elif self.op == OpType.CONST_CORRSUM:
                return env.get('corrsum_mod', ModularInt(0, env['d']))

            elif self.op == OpType.INV:
                val = self.children[0].evaluate(env)
                if isinstance(val, ModularInt) and val.is_unit():
                    return val.inverse()
                return None

            elif self.op == OpType.NEG:
                val = self.children[0].evaluate(env)
                if isinstance(val, ModularInt):
                    return ModularInt(-val.value, val.modulus)
                return None

            elif self.op == OpType.SQ:
                val = self.children[0].evaluate(env)
                if isinstance(val, ModularInt):
                    return val * val
                return None

            elif self.op == OpType.ADD:
                a = self.children[0].evaluate(env)
                b = self.children[1].evaluate(env)
                if isinstance(a, ModularInt) and isinstance(b, ModularInt):
                    return a + b
                return None

            elif self.op == OpType.MUL:
                a = self.children[0].evaluate(env)
                b = self.children[1].evaluate(env)
                if isinstance(a, ModularInt) and isinstance(b, ModularInt):
                    return a * b
                return None

            elif self.op == OpType.SUB:
                a = self.children[0].evaluate(env)
                b = self.children[1].evaluate(env)
                if isinstance(a, ModularInt) and isinstance(b, ModularInt):
                    return a - b
                return None

            elif self.op == OpType.POW:
                a = self.children[0].evaluate(env)
                b = self.children[1].evaluate(env)
                if isinstance(a, ModularInt) and isinstance(b, (int, ModularInt)):
                    exp = b.value if isinstance(b, ModularInt) else b
                    if exp < 0 or exp > 10000:
                        return None
                    return a ** exp
                return None

            elif self.op == OpType.IS_ZERO:
                val = self.children[0].evaluate(env)
                if isinstance(val, ModularInt):
                    return val.is_zero()
                return None

            elif self.op == OpType.IS_UNIT:
                val = self.children[0].evaluate(env)
                if isinstance(val, ModularInt):
                    return val.is_unit()
                return None

            elif self.op == OpType.GCD_D:
                val = self.children[0].evaluate(env)
                if isinstance(val, ModularInt):
                    return gcd(val.value, val.modulus)
                return None

            elif self.op == OpType.ORD:
                val = self.children[0].evaluate(env)
                if isinstance(val, ModularInt) and val.is_unit():
                    d = val.modulus
                    if d > 100000:
                        return None
                    return val.order()
                return None

        except Exception:
            return None
        return None

    def __repr__(self):
        if not self.children:
            return self.op.name
        args = ", ".join(repr(c) for c in self.children)
        return f"{self.op.name}({args})"


# ══════════════════════════════════════════════════════════════
# EXPRESSION TREE GENERATION & MUTATION
# ══════════════════════════════════════════════════════════════

LEAF_OPS = [OpType.CONST_RHO, OpType.CONST_ONE, OpType.CONST_TWO, OpType.CONST_THREE,
            OpType.CONST_K, OpType.CONST_S, OpType.CONST_CORRSUM]
UNARY_OPS = [OpType.INV, OpType.NEG, OpType.SQ]
BINARY_OPS = [OpType.ADD, OpType.MUL, OpType.SUB, OpType.POW]
PRED_OPS = [OpType.IS_ZERO, OpType.IS_UNIT]


def random_expr(max_depth=3) -> ExprNode:
    """Generate a random expression tree."""
    if max_depth <= 0 or random.random() < 0.4:
        return ExprNode(random.choice(LEAF_OPS))

    if random.random() < 0.4:
        child = random_expr(max_depth - 1)
        return ExprNode(random.choice(UNARY_OPS), [child])
    else:
        left = random_expr(max_depth - 1)
        right = random_expr(max_depth - 1)
        return ExprNode(random.choice(BINARY_OPS), [left, right])


def random_predicate(max_depth=3) -> ExprNode:
    """Generate a random predicate (returns bool)."""
    inner = random_expr(max_depth)
    return ExprNode(random.choice(PRED_OPS), [inner])


def mutate_expr(expr: ExprNode, max_depth=4) -> ExprNode:
    """Mutate an expression tree."""
    expr = copy.deepcopy(expr)

    # Pick a random node to mutate
    nodes = collect_nodes(expr)
    if not nodes:
        return random_expr(max_depth)

    target = random.choice(nodes)

    mutation = random.choice(['replace_subtree', 'change_op', 'wrap', 'unwrap'])

    if mutation == 'replace_subtree':
        new_sub = random_expr(max(1, max_depth - target.depth()))
        target.op = new_sub.op
        target.children = new_sub.children

    elif mutation == 'change_op':
        if not target.children:
            target.op = random.choice(LEAF_OPS)
        elif len(target.children) == 1:
            target.op = random.choice(UNARY_OPS)
        elif len(target.children) == 2:
            target.op = random.choice(BINARY_OPS)

    elif mutation == 'wrap':
        if target.depth() < max_depth:
            inner = copy.deepcopy(target)
            if random.random() < 0.5:
                target.op = random.choice(UNARY_OPS)
                target.children = [inner]
            else:
                other = random_expr(1)
                target.op = random.choice(BINARY_OPS)
                target.children = [inner, other]

    elif mutation == 'unwrap':
        if target.children:
            child = random.choice(target.children)
            target.op = child.op
            target.children = child.children

    return expr


def collect_nodes(expr: ExprNode) -> List[ExprNode]:
    """Collect all nodes in the tree."""
    result = [expr]
    for child in expr.children:
        result.extend(collect_nodes(child))
    return result


def crossover_expr(a: ExprNode, b: ExprNode) -> ExprNode:
    """Crossover: replace a random subtree of a with one from b."""
    a = copy.deepcopy(a)
    b = copy.deepcopy(b)

    a_nodes = collect_nodes(a)
    b_nodes = collect_nodes(b)

    target = random.choice(a_nodes)
    source = random.choice(b_nodes)

    target.op = source.op
    target.children = source.children

    return a


# ══════════════════════════════════════════════════════════════
# CREATIVE TACTIC = Expression that computes something about ρ
# and checks if it's zero/nonzero/unit/etc.
# ══════════════════════════════════════════════════════════════

@dataclass
class CreativeTactic:
    """A tactic is an expression tree that, when evaluated, produces
    a value in Z/dZ. If this value has a specific property (e.g., nonzero),
    it constitutes a proof step."""
    name: str
    expr: ExprNode
    assertion: str  # "nonzero", "unit", "zero"
    fitness: float = 0.0
    generation: int = 0
    behavioral_descriptor: Tuple = ()  # For MAP-Elites

    def test(self, k, d, rho_val) -> Optional[bool]:
        """Test the tactic on a specific k."""
        env = {
            'k': k,
            'S': compute_S(k),
            'd': d,
            'rho': ModularInt(rho_val, d),
        }
        result = self.expr.evaluate(env)
        if result is None:
            return None

        if self.assertion == "nonzero":
            if isinstance(result, ModularInt):
                return not result.is_zero()
            elif isinstance(result, bool):
                return result
            elif isinstance(result, int):
                return result != 0
        elif self.assertion == "unit":
            if isinstance(result, ModularInt):
                return result.is_unit()
        elif self.assertion == "zero":
            if isinstance(result, ModularInt):
                return result.is_zero()

        return None


# ══════════════════════════════════════════════════════════════
# MAP-ELITES ARCHIVE
# ══════════════════════════════════════════════════════════════

class MAPElitesArchive:
    """Archive of diverse tactics indexed by behavioral descriptors."""
    def __init__(self):
        self.archive = {}  # descriptor -> best tactic

    def add(self, tactic: CreativeTactic):
        desc = tactic.behavioral_descriptor
        if desc not in self.archive or tactic.fitness > self.archive[desc].fitness:
            self.archive[desc] = tactic

    def sample(self) -> Optional[CreativeTactic]:
        if not self.archive:
            return None
        return random.choice(list(self.archive.values()))

    def best(self) -> Optional[CreativeTactic]:
        if not self.archive:
            return None
        return max(self.archive.values(), key=lambda t: t.fitness)

    def size(self):
        return len(self.archive)

    def diversity(self):
        return len(set(self.archive.keys()))


# ══════════════════════════════════════════════════════════════
# EVALUATION
# ══════════════════════════════════════════════════════════════

def evaluate_tactic(tactic: CreativeTactic, test_ks: List[int]) -> float:
    """
    Evaluate a tactic PROPERLY: it must prove N₀=0 for each k.

    A tactic is USEFUL only if it distinguishes between:
    - ordered δ (should give corrSum ≢ 0 mod d)
    - unordered δ hitting target (should give corrSum ≡ 0 mod d)

    The expression is evaluated on the CORRECTION polynomial's value,
    not just on ρ. It must be nonzero for ALL ordered δ but allow
    zero for some unordered δ.

    STRICT evaluation: the expression must compute something that is
    nonzero for ALL cumulative sequences σ (i.e., for all valid δ),
    AND this nonzero-ness must IMPLY corrSum ≢ 0 mod d.
    """
    n_pass = 0
    n_fail = 0
    n_error = 0

    for k in test_ks:
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 50000: continue

        rho_val = (2 * pow(3, -1, d)) % d

        # Test: evaluate the expression for EACH cumulative sequence
        # The expression should be nonzero for ALL sequences
        all_nonzero = True
        n_tested = 0
        for sigma in enumerate_cumulative_sequences(k, S):
            cs = corrsum_cumulative(sigma, k)
            cs_mod = cs % d

            # Build environment with SEQUENCE-SPECIFIC data
            env = {
                'k': k, 'S': S, 'd': d,
                'rho': ModularInt(rho_val, d),
                'corrsum_mod': ModularInt(cs_mod, d),
                'sigma': sigma,
            }
            result = tactic.expr.evaluate(env)

            if result is None:
                n_error += 1
                break

            if tactic.assertion == "nonzero":
                if isinstance(result, ModularInt) and result.is_zero():
                    all_nonzero = False
                    break
                elif isinstance(result, bool) and not result:
                    all_nonzero = False
                    break
            n_tested += 1

        if all_nonzero and n_tested > 0 and n_error == 0:
            # Check: does "expression always nonzero" IMPLY corrSum ≢ 0?
            # For now: if the expression USES corrsum_mod and is always nonzero,
            # it's meaningful. If it doesn't use corrsum_mod, it's trivial.
            uses_corrsum = 'corrsum_mod' in repr(tactic.expr).lower()
            if uses_corrsum:
                n_pass += 1
            else:
                # Trivial — doesn't use the actual corrSum data
                n_pass += 0  # No credit for trivial tactics
        else:
            n_fail += 1

    total = n_pass + n_fail
    fitness = n_pass / total if total > 0 else 0
    fitness *= (1 - 0.3 * n_error / max(1, total + n_error))

    tactic.fitness = fitness
    tactic.behavioral_descriptor = (
        n_pass, n_fail,
        min(5, tactic.expr.depth()),
        min(10, tactic.expr.size()),
    )
    return fitness


# ══════════════════════════════════════════════════════════════
# MAIN EVOLUTION LOOP
# ══════════════════════════════════════════════════════════════

def run_creative_evolution(n_generations=50, pop_size=30, test_ks=None):
    """Run the creative tactic evolution with MAP-Elites."""
    if test_ks is None:
        test_ks = list(range(3, 21))

    print("CREATIVE TACTIC GENERATOR — MAP-Elites Evolution")
    print("=" * 65)
    print(f"Test k-values: {test_ks}")
    print(f"Population: {pop_size}, Generations: {n_generations}")

    t0 = time.time()
    archive = MAPElitesArchive()

    # Seed with known good tactics
    known_seeds = [
        # ρ - 1 = -1/3 (unit → correction always has this factor)
        ExprNode(OpType.SUB, [ExprNode(OpType.CONST_RHO), ExprNode(OpType.CONST_ONE)]),
        # ρ² - 1 (relevant for k=4 proof)
        ExprNode(OpType.SUB, [ExprNode(OpType.SQ, [ExprNode(OpType.CONST_RHO)]),
                               ExprNode(OpType.CONST_ONE)]),
        # 2·ρ - 1 (= 2·(2/3) - 1 = 1/3)
        ExprNode(OpType.SUB, [ExprNode(OpType.MUL, [ExprNode(OpType.CONST_TWO),
                                                      ExprNode(OpType.CONST_RHO)]),
                               ExprNode(OpType.CONST_ONE)]),
        # 3·ρ - 2 (should be 0! since 3ρ = 2)
        ExprNode(OpType.SUB, [ExprNode(OpType.MUL, [ExprNode(OpType.CONST_THREE),
                                                      ExprNode(OpType.CONST_RHO)]),
                               ExprNode(OpType.CONST_TWO)]),
    ]

    # Initialize with seeds + random
    population = []
    for expr in known_seeds:
        for assertion in ["nonzero", "unit"]:
            t = CreativeTactic(f"seed_{assertion}", expr, assertion)
            evaluate_tactic(t, test_ks)
            population.append(t)
            archive.add(t)

    while len(population) < pop_size:
        expr = random_expr(random.randint(2, 4))
        assertion = random.choice(["nonzero", "unit"])
        t = CreativeTactic(f"rand_{len(population)}", expr, assertion)
        evaluate_tactic(t, test_ks)
        population.append(t)
        archive.add(t)

    best_ever_fitness = 0

    for gen in range(n_generations):
        # Evaluate
        population.sort(key=lambda t: t.fitness, reverse=True)
        best = population[0]

        if best.fitness > best_ever_fitness:
            best_ever_fitness = best.fitness

        if gen % 10 == 0 or best.fitness >= 1.0:
            print(f"Gen {gen:3d}: best={best.fitness:.3f} ({best.expr}), "
                  f"archive={archive.size()}, diversity={archive.diversity()}")

        if best.fitness >= 1.0:
            print(f"\n★★★ PERFECT TACTIC at gen {gen}!")
            print(f"    expr: {best.expr}")
            print(f"    assertion: {best.assertion}")
            break

        # Selection: keep top half + MAP-Elites samples
        survivors = population[:pop_size // 3]
        # Add samples from archive for diversity
        for _ in range(pop_size // 6):
            sample = archive.sample()
            if sample:
                survivors.append(sample)

        # Offspring
        offspring = []
        while len(survivors) + len(offspring) < pop_size:
            if random.random() < 0.6:
                # Mutation
                parent = random.choice(survivors)
                child_expr = mutate_expr(parent.expr)
                assertion = parent.assertion if random.random() < 0.7 else random.choice(["nonzero", "unit"])
                child = CreativeTactic(f"mut_g{gen}", child_expr, assertion, generation=gen)
            elif random.random() < 0.8:
                # Crossover
                p1 = random.choice(survivors)
                p2 = random.choice(survivors)
                child_expr = crossover_expr(p1.expr, p2.expr)
                assertion = random.choice([p1.assertion, p2.assertion])
                child = CreativeTactic(f"cx_g{gen}", child_expr, assertion, generation=gen)
            else:
                # Random new
                child_expr = random_expr(random.randint(2, 5))
                assertion = random.choice(["nonzero", "unit"])
                child = CreativeTactic(f"new_g{gen}", child_expr, assertion, generation=gen)

            evaluate_tactic(child, test_ks)
            offspring.append(child)
            archive.add(child)

        population = survivors + offspring

    # Final report
    elapsed = time.time() - t0
    best = archive.best()
    print(f"\n{'='*65}")
    print(f"EVOLUTION COMPLETE — {elapsed:.1f}s")
    print(f"Archive: {archive.size()} tactics, {archive.diversity()} niches")
    if best:
        print(f"Best: fitness={best.fitness:.3f}")
        print(f"  expr: {best.expr}")
        print(f"  assertion: {best.assertion}")
        print(f"  descriptor: {best.behavioral_descriptor}")

        # Show per-k results
        for k in test_ks:
            d = compute_d(k)
            if d <= 0: continue
            rho_val = (2 * pow(3, -1, d)) % d
            result = best.test(k, d, rho_val)
            print(f"  k={k:3d}: {result}")

    # Save archive
    out = os.path.join(os.path.dirname(__file__), '..', 'logs', 'creative_archive.json')
    os.makedirs(os.path.dirname(out), exist_ok=True)
    archive_data = {
        'n_tactics': archive.size(),
        'n_niches': archive.diversity(),
        'best_fitness': best.fitness if best else 0,
        'best_expr': repr(best.expr) if best else None,
        'elapsed': elapsed,
    }
    with open(out, 'w') as f:
        json.dump(archive_data, f, indent=2)

    return archive


if __name__ == '__main__':
    random.seed(42)
    archive = run_creative_evolution(n_generations=60, pop_size=40, test_ks=list(range(3, 25)))
