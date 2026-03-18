#!/usr/bin/env python3
"""
SELF-REFLECTION ENGINE + FAILURE MEMORY
==========================================

After each proof attempt: analyze WHY it failed.
Store failures persistently. Before trying: check memory.

Inspired by Reflexion (Shinn et al. 2023) and LATS (Zhou et al. 2023).
"""

import os, json, time
from datetime import datetime

PROJECT = '/Users/ericmerle/Documents/Collatz-Junction-Theorem'
MEMORY_FILE = os.path.join(PROJECT, 'syracuse_jepa', 'logs', 'failure_memory.json')


def load_memory():
    if os.path.exists(MEMORY_FILE):
        with open(MEMORY_FILE) as f:
            return json.load(f)
    return {'dead_ends': [], 'partial_successes': [], 'open_questions': []}


def save_memory(memory):
    os.makedirs(os.path.dirname(MEMORY_FILE), exist_ok=True)
    with open(MEMORY_FILE, 'w') as f:
        json.dump(memory, f, indent=2)


def record_dead_end(approach, reason, constraint, tried_variants=None):
    """Record a dead-end approach so we don't try it again."""
    memory = load_memory()
    entry = {
        'approach': approach,
        'reason': reason,
        'constraint': constraint,
        'tried_variants': tried_variants or [],
        'timestamp': datetime.now().isoformat(),
    }
    # Check if already recorded
    for de in memory['dead_ends']:
        if de['approach'] == approach:
            de['reason'] = reason  # Update
            save_memory(memory)
            return
    memory['dead_ends'].append(entry)
    save_memory(memory)


def record_partial_success(approach, what_works, what_fails, k_range):
    """Record a partially successful approach."""
    memory = load_memory()
    memory['partial_successes'].append({
        'approach': approach,
        'what_works': what_works,
        'what_fails': what_fails,
        'k_range': k_range,
        'timestamp': datetime.now().isoformat(),
    })
    save_memory(memory)


def record_open_question(question, context, priority='HIGH'):
    """Record an open question for future investigation."""
    memory = load_memory()
    memory['open_questions'].append({
        'question': question,
        'context': context,
        'priority': priority,
        'timestamp': datetime.now().isoformat(),
    })
    save_memory(memory)


def check_if_tried(approach):
    """Check if an approach was already tried."""
    memory = load_memory()
    for de in memory['dead_ends']:
        if approach.lower() in de['approach'].lower():
            return True, de
    return False, None


def reflect_on_session():
    """Analyze the current session's findings and update memory."""
    print("SELF-REFLECTION: Updating failure memory")
    print("=" * 60)

    # Record all dead ends from this session
    dead_ends = [
        ("Range Exclusion with individual exponents",
         "Uses wrong corrSum formula (individual vs cumulative)",
         "Steiner's equation requires cumulative exponents",
         ["original Range Exclusion", "Baker-LMN closing"]),

        ("FCQ prime-by-prime for cumulative",
         "N0(p) > 0 for most primes p|d with cumulative formula",
         "CRT interference needed, not single-prime blocking",
         ["spectral radius", "primitive roots", "Artin study"]),

        ("Exponential sums L-infinity",
         "max|G(a)| >> 1, need max|G| < (d-C)/(d-1) ≈ 1",
         "Image is too sparse for exp sum equidistribution",
         ["L-infinity", "Cauchy-Schwarz"]),

        ("Exponential sums L2 (Parseval)",
         "Collision count too high due to sparse image",
         "(d-C)^2 << (d-1)*Delta for sparse distributions",
         ["Parseval bound", "collision count"]),

        ("Inertia of d in number field",
         "d always splits (2 is always a root of X^S-3^k mod d)",
         "By construction: 2^S ≡ 3^k mod d, so 2 is a root",
         ["prime ideal", "splitting behavior"]),

        ("Number field norm for all k",
         "N(P_σ(α)) can be divisible by d for k ≥ 5",
         "Other conjugates absorb the d factor, not the real one",
         ["norm approach", "coprimality"]),

        ("Subgroup <2,3> containment for all k",
         "corrSum mod d not always in <2,3> for k ≥ 4",
         "Works for k=3,5 but not universal",
         ["subgroup", "units group"]),

        ("corrSum coprime to d",
         "gcd(corrSum, d) > 1 for some sequences (k ≥ 6)",
         "Proper divisors of d are achieved as gcd values",
         ["coprimality", "gcd"]),
    ]

    for approach, reason, constraint, variants in dead_ends:
        record_dead_end(approach, reason, constraint, variants)
        print(f"  ✗ {approach}: {reason[:60]}")

    # Record partial successes
    partial = [
        ("Number field norm",
         "Proves k=3,4 completely (N coprime to d for prime d)",
         "N not coprime for k ≥ 5",
         "k=3,4"),

        ("Valuation blocking",
         "Some primes p|d have v_p(corrSum)=0 for all σ",
         "Not all k have a blocking prime",
         "k=3,4,5,7,8,11"),

        ("<2,3> subgroup containment",
         "corrSum in <2,3> ⊂ (Z/dZ)* for k=3,5",
         "Not universal",
         "k=3,5"),

        ("Ordering obstruction",
         "ALL free solutions have crossings; sorting correction ≠ 0",
         "Verified computationally, not yet proved for all k",
         "k=3..8"),

        ("ord_d(2) > S-k",
         "Every individual swap correction is nonzero",
         "Total correction nonvanishing unproved",
         "k=3..20"),
    ]

    for approach, works, fails, k_range in partial:
        record_partial_success(approach, works, fails, k_range)
        print(f"  ◐ {approach}: works for {k_range}")

    # Record open questions
    questions = [
        ("Why is ρ=2/3 never a root of the correction polynomial Q_δ?",
         "Vandermonde analysis shows ρ avoids all root sets",
         "CRITICAL"),

        ("Can Baker's theorem prove ord_d(2) > S-k for all k?",
         "Baker gives ord ≥ exp(c·√(log d)), need > S-k ≈ 0.585k",
         "HIGH"),

        ("Is d always the UNIQUE unachieved divisor of gcd(corrSum,d)?",
         "Verified for k=3..12, fails for k=7,8,11 (extra unachieved)",
         "MEDIUM"),

        ("Can the Catalan-Mihailescu connection be exploited?",
         "d = 2^S - 3^k is Catalan-type; near-miss residuals ±1",
         "HIGH"),
    ]

    for q, ctx, priority in questions:
        record_open_question(q, ctx, priority)
        print(f"  ? [{priority}] {q[:60]}")

    save_memory(load_memory())
    print(f"\nMemory saved to {MEMORY_FILE}")


def suggest_next_approach():
    """Based on memory, suggest the next approach to try."""
    memory = load_memory()

    print("\n" + "=" * 60)
    print("NEXT APPROACH SUGGESTIONS")
    print("=" * 60)

    # Find approaches NOT in dead ends
    tried = set(de['approach'].lower() for de in memory['dead_ends'])

    suggestions = [
        "Prove ρ never root of Q_δ using algebraic geometry",
        "Use Skolem-Mahler-Lech theorem on linear recurrences",
        "Apply Weil bound to character sums with rank-dependent weights",
        "Exploit Baker-Wüstholz for linear forms in 3 logarithms",
        "Use p-adic analysis (Hensel lifting) on corrSum",
        "Apply Roth/Schmidt subspace theorem to Diophantine approximation",
        "Use model theory (o-minimality) for definable sets",
        "Information-theoretic argument via Kolmogorov complexity",
    ]

    for s in suggestions:
        was_tried, info = check_if_tried(s)
        if not was_tried:
            print(f"  → {s}")
        else:
            print(f"  ✗ (tried) {s}: {info['reason'][:50]}")


if __name__ == '__main__':
    reflect_on_session()
    suggest_next_approach()
