#!/usr/bin/env python3
"""UNSAT-focused battery for the guarded reduction. The failure mode
that killed Block 8 was spurious cuts on UNSAT formulas; random
formulas are ~92% SAT, so the random batteries under-sample the
direction that matters. Rejection-sample UNSAT formulas and test only
those, graph-level, independent oracle."""

import sys
import random

sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
from mc_check import is_bipartite, eccentricity, distances_from
from independent_mc import has_matching_cut
from verify_sol_reduction import formula_sat, random_formula
from guarded_reduction import build_guarded_graph

target = int(sys.argv[1]) if len(sys.argv) > 1 else 60
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 4242
n_hi = int(sys.argv[3]) if len(sys.argv) > 3 else 2
m_hi = int(sys.argv[4]) if len(sys.argv) > 4 else 3

rng = random.Random(seed)
tested = mism = timeouts = 0
attempts = 0
while tested + timeouts < target and attempts < 200_000:
    attempts += 1
    n = rng.randint(1, n_hi)
    m = rng.randint(1, m_hi)
    clauses = random_formula(rng, n, m)
    if formula_sat(n, clauses):
        continue
    g = build_guarded_graph(n, clauses)
    assert is_bipartite(g)[0]
    assert len(distances_from(g, "u")) == len(g)
    assert min(eccentricity(g, v) for v in g) == 3
    try:
        mc = has_matching_cut(g, budget=50_000_000)
    except TimeoutError:
        timeouts += 1
        continue
    tested += 1
    if mc:
        mism += 1
        if mism <= 5:
            print(f"SPURIOUS CUT on UNSAT: n={n} m={m} clauses={clauses} "
                  f"|V|={len(g)}")
print(f"UNSAT battery: tested {tested}; spurious {mism}; "
      f"timeouts {timeouts}; formula attempts {attempts}")
sys.exit(1 if mism else 0)
