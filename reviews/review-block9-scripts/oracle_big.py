#!/usr/bin/env python3
"""Extend the published guarded battery (n<=2, m<=2) to n<=3, m<=3 with
the INDEPENDENT oracle, unrestricted variable choice (unused variables
possible), reporting SAT/UNSAT composition and timeouts."""
import sys, random, time
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
from verify_sol_reduction import formula_sat
from guarded_reduction import build_guarded_graph
from independent_mc import has_matching_cut
from mc_check import is_bipartite, eccentricity

rng = random.Random(20260816)
tested = mism = to = nun = 0
t0 = time.time()
for it in range(300):
    n = rng.randint(1, 3); m = rng.randint(1, 3)
    cl = [[(rng.randrange(n), rng.random() < 0.5) for _ in range(3)]
          for _ in range(m)]
    g = build_guarded_graph(n, cl)
    assert is_bipartite(g)[0]
    assert min(eccentricity(g, v) for v in g) == 3
    sat = formula_sat(n, cl)
    try:
        mc = has_matching_cut(g, budget=300_000_000)
    except TimeoutError:
        to += 1
        print(f"TIMEOUT n={n} m={m} sat={sat} |V|={len(g)}", flush=True)
        continue
    tested += 1; nun += (not sat)
    if sat != mc:
        mism += 1
        print(f"MISMATCH sat={sat} mc={mc} n={n} m={m} cl={cl}", flush=True)
    if it % 25 == 0:
        print(f"  ..{it} done {time.time()-t0:.0f}s", flush=True)
print(f"tested {tested} (UNSAT={nun}); mismatches {mism}; timeouts {to}; "
      f"{time.time()-t0:.0f}s")
