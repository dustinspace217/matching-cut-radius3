#!/usr/bin/env python3
"""Does the Lemma-9B abstraction flaw propagate into the GUARDED
reduction? Compare, per formula: the ISLAND-as-coded answer on the base
set instance vs the CORRECT graph-level case-A1 answer on the guarded
graph vs SAT."""
import sys, random
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
sys.path.insert(0, "/tmp/claude/pvnp")
from verify_sol_reduction import formula_sat
from sol_set_reduction import build_set_instance
from guarded_reduction import build_guarded_graph
from decomp import layers
from fast_a1 import caseA1_fast
from island_sat import island_yes

rng = random.Random(808)
bad = 0
for _ in range(1500):
    n = rng.randint(1, 5); m = rng.randint(1, 6)
    cl = [[(rng.randrange(n), rng.random() < 0.5) for _ in range(3)]
          for _ in range(m)]
    isl = island_yes(*build_set_instance(n, cl)) is not None
    g = build_guarded_graph(n, cl)
    L1, L2, L3 = layers(g)
    a1 = caseA1_fast(g, L1, L2, L3) is not None
    sat = formula_sat(n, cl)
    if not (isl == a1 == sat):
        bad += 1
        if bad <= 5:
            print(f"DIVERGE island={isl} graphA1={a1} sat={sat} n={n} cl={cl}")
print(f"checked 1500; divergences {bad}")
