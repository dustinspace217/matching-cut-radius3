#!/usr/bin/env python3
"""Exhaustive n=1 TWO-clause guarded battery with the independent oracle
(the published exhaustive companion only did single clauses, which are
all satisfiable). 64 formulas, 18 of them UNSAT."""
import sys, itertools, time
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
from verify_sol_reduction import formula_sat
from guarded_reduction import build_guarded_graph
from independent_mc import has_matching_cut
from mc_check import is_bipartite, eccentricity

t0 = time.time(); tested = mism = nun = 0
for s1 in itertools.product((True, False), repeat=3):
    for s2 in itertools.product((True, False), repeat=3):
        cl = [[(0, x) for x in s1], [(0, x) for x in s2]]
        g = build_guarded_graph(1, cl)
        assert is_bipartite(g)[0]
        assert min(eccentricity(g, v) for v in g) == 3
        sat = formula_sat(1, cl)
        mc = has_matching_cut(g, budget=1_000_000_000)
        tested += 1; nun += (not sat)
        if sat != mc:
            mism += 1
            print(f"MISMATCH sat={sat} mc={mc} cl={cl}")
print(f"exhaustive n=1 2-clause: tested {tested} (UNSAT={nun}); "
      f"mismatches {mism}; {time.time()-t0:.0f}s")
