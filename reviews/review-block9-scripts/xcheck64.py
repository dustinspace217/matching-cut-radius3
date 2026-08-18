#!/usr/bin/env python3
"""Cross-check the case DECOMPOSITION against the independent oracle on
all 64 n=1 two-clause guarded graphs (|V|=56). If they agree everywhere,
the decomposition-based scaling to n<=6/m<=10 is trustworthy."""
import sys, itertools, time
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
sys.path.insert(0, "/tmp/claude/pvnp")
from verify_sol_reduction import formula_sat
from guarded_reduction import build_guarded_graph
from independent_mc import has_matching_cut
from decomp import layers, caseA0, caseB
from fast_a1 import caseA1_fast

t0 = time.time(); bad = 0
for s1 in itertools.product((True, False), repeat=3):
    for s2 in itertools.product((True, False), repeat=3):
        cl = [[(0, x) for x in s1], [(0, x) for x in s2]]
        g = build_guarded_graph(1, cl)
        L1, L2, L3 = layers(g)
        dec = (caseA1_fast(g, L1, L2, L3) is not None or bool(caseA0(g, L3))
               or bool(caseB(g, L1)))
        orc = has_matching_cut(g, budget=1_000_000_000)
        if dec != orc:
            bad += 1
            print("DECOMP/ORACLE DISAGREE", cl, dec, orc)
print(f"decomposition vs independent oracle on 64 guarded graphs: "
      f"{bad} disagreements; {time.time()-t0:.0f}s")
