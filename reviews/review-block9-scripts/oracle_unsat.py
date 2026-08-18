#!/usr/bin/env python3
"""Strongest independent evidence on the failure direction: run the
INDEPENDENT oracle (independent_mc.has_matching_cut, no decomposition,
no theory) on the guarded graph for EVERY UNSAT n=1 two-clause formula,
plus some UNSAT n=2 ones."""
import sys, time, itertools
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
from verify_sol_reduction import formula_sat
from guarded_reduction import build_guarded_graph
from independent_mc import has_matching_cut
from mc_check import is_bipartite, eccentricity

cases = []
for s1 in itertools.product((True, False), repeat=3):
    for s2 in itertools.product((True, False), repeat=3):
        cl = [[(0, x) for x in s1], [(0, x) for x in s2]]
        if not formula_sat(1, cl):
            cases.append((1, cl))
# UNSAT with an unused variable (n=2, only var 0 occurs)
cases.append((2, [[(0, True), (0, True), (0, False)],
                  [(0, True), (0, False), (0, False)]]))
bad = to = 0
for n, cl in cases:
    g = build_guarded_graph(n, cl)
    assert is_bipartite(g)[0]
    assert min(eccentricity(v_, g) if False else eccentricity(g, v_)
               for v_ in g) == 3
    t0 = time.time()
    try:
        mc = has_matching_cut(g, budget=2_000_000_000)
    except TimeoutError:
        mc = "TIMEOUT"; to += 1
    print(f"n={n} |V|={len(g)} sat=False oracle_mc={mc} "
          f"({time.time()-t0:.1f}s) cl={cl}", flush=True)
    if mc is True:
        bad += 1
print(f"UNSAT instances with a spurious matching cut: {bad}; timeouts {to}")
