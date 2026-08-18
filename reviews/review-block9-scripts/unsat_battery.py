#!/usr/bin/env python3
"""UNSAT-focused graph-level battery for the guarded reduction.

The published batteries are heavily SAT-skewed (guarded_exhaustive.py is
100% SAT). Block 8's refutation lived entirely on the sat=False/mc=True
side, so that is the side worth hammering.
"""
import sys, time, itertools, random
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
from mc_check import is_bipartite, eccentricity, distances_from
from independent_mc import has_matching_cut
from verify_sol_reduction import formula_sat
from guarded_reduction import build_guarded_graph

CASES = []

# 1. all 2-clause formulas over n=1 (64 ordered pairs) -- includes UNSAT
for s1 in itertools.product((True, False), repeat=3):
    for s2 in itertools.product((True, False), repeat=3):
        cl = [[(0, x) for x in s1], [(0, x) for x in s2]]
        CASES.append((1, cl))

# 2. degenerate: unused variable + UNSAT core (n=2, only var 0 used)
CASES.append((2, [[(0, True), (0, True), (0, False)],
                  [(0, True), (0, False), (0, False)]]))
# 3. unused variable + SAT core
CASES.append((2, [[(0, True), (0, True), (0, True)],
                  [(0, True), (0, True), (0, False)]]))
# 4. mixed-variable UNSAT over n=2
CASES.append((2, [[(0, True), (0, True), (0, False)],
                  [(0, True), (0, False), (0, False)],
                  [(1, True), (1, True), (1, False)]]))

t0 = time.time()
tested = mism = 0
nsat = nunsat = 0
for n, clauses in CASES:
    g = build_guarded_graph(n, clauses)
    assert is_bipartite(g)[0]
    assert len(distances_from(g, "u")) == len(g)
    r = min(eccentricity(g, v) for v in g)
    assert r == 3, f"radius {r}"
    sat = formula_sat(n, clauses)
    mc = has_matching_cut(g, budget=200_000_000)
    tested += 1
    nsat += sat
    nunsat += (not sat)
    if sat != mc:
        mism += 1
        print(f"MISMATCH sat={sat} mc={mc} n={n} |V|={len(g)} cl={clauses}")
print(f"tested {tested} (SAT={nsat} UNSAT={nunsat}); mismatches {mism}; "
      f"{time.time()-t0:.1f}s")
