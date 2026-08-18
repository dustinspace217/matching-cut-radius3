#!/usr/bin/env python3
"""FAST CONTROL: the case-B detector must reproduce the Block-8 leak on
the UNGUARDED graph for small formulas (n=1, m=1..2). If it does, then
'0 case-B survivors' on the guarded graph is meaningful."""
import sys, itertools
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
sys.path.insert(0, "/tmp/claude/pvnp")
from verify_sol_reduction import build_graph, formula_sat
from guarded_reduction import build_guarded_graph
from mc_check import eccentricity, distances_from
from decomp import layers, caseA0, caseB
from fast_a1 import caseA1_fast

def report(builder, label, n, cl):
    g = builder(n, cl)
    if len(distances_from(g, "u")) != len(g):
        return None
    L1, L2, L3 = layers(g)
    a1 = caseA1_fast(g, L1, L2, L3) is not None
    a0 = bool(caseA0(g, L3))
    try:
        b = caseB(g, L1, budget=20_000_000)
    except TimeoutError:
        b = "TIMEOUT"
    sat = formula_sat(n, cl)
    mc = a1 or a0 or (bool(b) if b != "TIMEOUT" else False)
    print(f"{label:10s} n={n} sat={sat} A1={a1} A0={a0} "
          f"B={[x[0] for x in b][:5] if b != 'TIMEOUT' else 'TIMEOUT'} "
          f"-> mc={mc}{'   <-- SPURIOUS' if mc and not sat else ''}")
    return mc, sat

# n=1 UNSAT formulas (2 clauses)
cases = []
for s1 in itertools.product((True, False), repeat=3):
    for s2 in itertools.product((True, False), repeat=3):
        cl = [[(0, x) for x in s1], [(0, x) for x in s2]]
        if not formula_sat(1, cl):
            cases.append((1, cl))
print(f"{len(cases)} UNSAT n=1 2-clause formulas")
for n, cl in cases[:4]:
    print("clauses:", cl)
    report(build_graph, "UNGUARDED", n, cl)
    report(build_guarded_graph, "GUARDED", n, cl)
