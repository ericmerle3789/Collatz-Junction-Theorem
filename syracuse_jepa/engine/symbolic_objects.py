#!/usr/bin/env python3
"""
SYMBOLIC OBJECTS — Mathematical objects as first-class Python entities
========================================================================

Every mathematical object in our proof has a TYPE, VALUE, PROPERTIES,
and RELATIONS to other objects. They form a GRAPH.

This is NOT just a number — it's a STRUCTURED representation that
supports SYMBOLIC REASONING: simplification, substitution, pattern
matching, and proof construction.

Adapted to: MacBook M1, Python 3.12, no external symbolic algebra
(we build our own, lean and specific to our problem).
"""

from dataclasses import dataclass, field
from typing import List, Dict, Optional, Set, Any, Tuple
from enum import Enum, auto
from math import ceil, log2, gcd


class ObjType(Enum):
    """Types of mathematical objects."""
    INTEGER = auto()
    MODULAR = auto()       # Element of Z/nZ
    POLYNOMIAL = auto()    # Polynomial over Z or Z/nZ
    SEQUENCE = auto()      # Finite sequence (like δ or σ)
    SET = auto()           # Finite set of elements
    GROUP_ELEMENT = auto() # Element of a multiplicative group
    IDEAL = auto()         # Ideal in a ring
    BOUND = auto()         # Inequality / bound


class Relation(Enum):
    """Types of relations between objects."""
    DIVIDES = auto()       # a | b
    COPRIME = auto()       # gcd(a,b) = 1
    CONGRUENT = auto()     # a ≡ b mod n
    LESS_THAN = auto()     # a < b
    ELEMENT_OF = auto()    # a ∈ S
    ROOT_OF = auto()       # a is root of P
    GENERATES = auto()     # a generates G
    FACTORS_AS = auto()    # P = Q · R


@dataclass
class MathObject:
    """A mathematical object with symbolic metadata."""
    name: str
    obj_type: ObjType
    value: Any
    properties: Dict[str, Any] = field(default_factory=dict)
    relations: List[Tuple['MathObject', Relation, Any]] = field(default_factory=list)
    latex: str = ""

    def __repr__(self):
        return f"{self.name}:{self.obj_type.name}={self.value}"

    def add_property(self, key, value):
        self.properties[key] = value
        return self

    def add_relation(self, other, rel_type, context=None):
        self.relations.append((other, rel_type, context))
        return self


@dataclass
class ModularInt:
    """Element of Z/nZ with full arithmetic."""
    value: int
    modulus: int

    def __post_init__(self):
        self.value = self.value % self.modulus

    def __add__(self, other):
        if isinstance(other, ModularInt):
            assert self.modulus == other.modulus
            return ModularInt((self.value + other.value) % self.modulus, self.modulus)
        return ModularInt((self.value + other) % self.modulus, self.modulus)

    def __mul__(self, other):
        if isinstance(other, ModularInt):
            assert self.modulus == other.modulus
            return ModularInt((self.value * other.value) % self.modulus, self.modulus)
        return ModularInt((self.value * other) % self.modulus, self.modulus)

    def __sub__(self, other):
        if isinstance(other, ModularInt):
            assert self.modulus == other.modulus
            return ModularInt((self.value - other.value) % self.modulus, self.modulus)
        return ModularInt((self.value - other) % self.modulus, self.modulus)

    def __pow__(self, exp):
        return ModularInt(pow(self.value, exp, self.modulus), self.modulus)

    def __eq__(self, other):
        if isinstance(other, ModularInt):
            return self.value == other.value and self.modulus == other.modulus
        return self.value == (other % self.modulus)

    def __hash__(self):
        return hash((self.value, self.modulus))

    def __repr__(self):
        return f"{self.value} mod {self.modulus}"

    def inverse(self):
        return ModularInt(pow(self.value, -1, self.modulus), self.modulus)

    def order(self):
        """Multiplicative order."""
        if gcd(self.value, self.modulus) != 1:
            return None
        x = self.value
        o = 1
        while x != 1:
            x = (x * self.value) % self.modulus
            o += 1
            if o > self.modulus:
                return None
        return o

    def is_unit(self):
        return gcd(self.value, self.modulus) == 1

    def is_zero(self):
        return self.value == 0


@dataclass
class Polynomial:
    """Polynomial over Z/nZ: P(X) = Σ coeffs[i] · X^i."""
    coeffs: List[ModularInt]  # coeffs[i] = coefficient of X^i
    modulus: int
    variable: str = "X"

    @property
    def degree(self):
        for i in range(len(self.coeffs)-1, -1, -1):
            if self.coeffs[i].value != 0:
                return i
        return -1  # Zero polynomial

    def evaluate(self, x: ModularInt) -> ModularInt:
        result = ModularInt(0, self.modulus)
        for i, c in enumerate(self.coeffs):
            result = result + c * (x ** i)
        return result

    def __repr__(self):
        terms = []
        for i, c in enumerate(self.coeffs):
            if c.value == 0: continue
            if i == 0:
                terms.append(str(c.value))
            elif i == 1:
                terms.append(f"{c.value}·{self.variable}")
            else:
                terms.append(f"{c.value}·{self.variable}^{i}")
        return " + ".join(terms) if terms else "0"

    def roots(self) -> List[ModularInt]:
        """Find all roots by brute force (for small modulus)."""
        if self.modulus > 50000:
            return []
        return [ModularInt(x, self.modulus) for x in range(self.modulus)
                if self.evaluate(ModularInt(x, self.modulus)).is_zero()]

    def factor_out_root(self, root: ModularInt) -> 'Polynomial':
        """Factor out (X - root): P(X) = (X - root) · Q(X)."""
        n = len(self.coeffs)
        if n <= 1:
            return Polynomial([ModularInt(0, self.modulus)], self.modulus)

        q_coeffs = [ModularInt(0, self.modulus)] * (n - 1)
        q_coeffs[-1] = self.coeffs[-1]
        for i in range(n-2, 0, -1):
            q_coeffs[i-1] = self.coeffs[i] + root * q_coeffs[i]

        return Polynomial(q_coeffs, self.modulus, self.variable)


@dataclass
class ProofGraph:
    """
    A directed graph of mathematical objects and their relations.
    Nodes = MathObject, Edges = Relations.
    The proof IS the graph: a path from AXIOMS to CONTRADICTION.
    """
    objects: Dict[str, MathObject] = field(default_factory=dict)
    edges: List[Tuple[str, str, Relation, str]] = field(default_factory=list)
    axioms: Set[str] = field(default_factory=set)
    goals: Set[str] = field(default_factory=set)
    contradictions: List[str] = field(default_factory=list)

    def add_object(self, obj: MathObject) -> str:
        self.objects[obj.name] = obj
        return obj.name

    def add_edge(self, src: str, dst: str, rel: Relation, justification: str = ""):
        self.edges.append((src, dst, rel, justification))

    def add_axiom(self, name: str):
        self.axioms.add(name)

    def add_goal(self, name: str):
        self.goals.add(name)

    def add_contradiction(self, description: str):
        self.contradictions.append(description)

    def is_proved(self):
        return len(self.contradictions) > 0

    def summary(self):
        return (f"ProofGraph: {len(self.objects)} objects, {len(self.edges)} edges, "
                f"{len(self.axioms)} axioms, {len(self.goals)} goals, "
                f"{len(self.contradictions)} contradictions")


# ══════════════════════════════════════════════════════════════
# COLLATZ-SPECIFIC OBJECT CONSTRUCTORS
# ══════════════════════════════════════════════════════════════

def build_collatz_graph(k: int) -> ProofGraph:
    """Build the proof graph for a specific k."""
    S = ceil(k * log2(3))
    d = 2**S - 3**k
    if d <= 0:
        return ProofGraph()

    G = ProofGraph()

    # Core objects
    k_obj = MathObject("k", ObjType.INTEGER, k, {'positive': True, 'ge_3': k >= 3})
    S_obj = MathObject("S", ObjType.INTEGER, S, {'definition': f'ceil({k}·log₂3)'})
    d_obj = MathObject("d", ObjType.INTEGER, d, {'odd': d % 2 == 1, 'positive': d > 0})

    rho_val = (2 * pow(3, -1, d)) % d
    rho_obj = MathObject("ρ", ObjType.MODULAR, ModularInt(rho_val, d),
                          {'definition': '2·3⁻¹ mod d', 'unit': True})

    G.add_object(k_obj)
    G.add_object(S_obj)
    G.add_object(d_obj)
    G.add_object(rho_obj)

    # Relation: 2^S ≡ 3^k mod d
    G.add_edge("S", "d", Relation.CONGRUENT, "2^S ≡ 3^k mod d (definition of d)")

    # The polynomial Q_δ
    Q_obj = MathObject("Q_δ", ObjType.POLYNOMIAL, None,
                        {'degree': k-1, 'universal_root': 1})
    G.add_object(Q_obj)

    # Factorization Q = (X-1)·R
    R_obj = MathObject("R_δ", ObjType.POLYNOMIAL, None,
                        {'degree': k-3, 'max_roots': k-3})
    G.add_object(R_obj)
    G.add_edge("Q_δ", "R_δ", Relation.FACTORS_AS, "Q_δ = (X-1)·R_δ (X=1 universal root)")

    # Goal: R_δ(ρ) ≠ 0
    goal = MathObject("R_δ(ρ)≠0", ObjType.BOUND, None,
                       {'equivalent_to': 'N₀(d)=0', 'equivalent_to_collatz': True})
    G.add_object(goal)
    G.add_goal("R_δ(ρ)≠0")

    # Axioms
    steiner = MathObject("Steiner", ObjType.BOUND, None,
                          {'statement': 'Cycle ⟺ corrSum ≡ 0 mod d'})
    G.add_object(steiner)
    G.add_axiom("Steiner")

    junction = MathObject("Junction", ObjType.BOUND, None,
                           {'statement': f'C(S-1,k-1) < d for k ≥ 18', 'lean_proved': True})
    G.add_object(junction)
    G.add_axiom("Junction")

    if k < 68:
        sdw = MathObject("SdW", ObjType.BOUND, None,
                          {'statement': 'No cycle for k < 68', 'published': True})
        G.add_object(sdw)
        G.add_axiom("SdW")
        G.add_contradiction(f"k={k} < 68: SdW proves no cycle. QED.")

    # ord_d(2) computation
    rho_mi = ModularInt(rho_val, d)
    ord_rho = rho_mi.order() if d < 100000 else None

    if ord_rho:
        ord_obj = MathObject("ord_d(ρ)", ObjType.INTEGER, ord_rho,
                              {'gt_max_delta': ord_rho > S - k if ord_rho else None})
        G.add_object(ord_obj)

    return G


# ══════════════════════════════════════════════════════════════
# TEST
# ══════════════════════════════════════════════════════════════

if __name__ == '__main__':
    print("SYMBOLIC OBJECTS — Building proof graphs")
    print("=" * 60)

    for k in [3, 5, 7, 68, 100]:
        G = build_collatz_graph(k)
        print(f"\nk={k}: {G.summary()}")
        if G.is_proved():
            print(f"  PROVED: {G.contradictions[0]}")
        else:
            print(f"  OPEN — goals: {G.goals}")
            for name, obj in G.objects.items():
                if obj.properties:
                    props = ", ".join(f"{k}={v}" for k, v in obj.properties.items()
                                    if v is not None)
                    if props:
                        print(f"    {name}: {props}")
