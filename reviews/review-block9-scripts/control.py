#!/usr/bin/env python3
"""CONTROL: the case-B detector must FIND the Block-8 leaks in the
UNGUARDED graph. If it reports 'no case B' there too, then '0 case-B
survivors' in the guarded graph proves nothing about the guards."""
import sys, random
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
sys.path.insert(0, "/tmp/claude/pvnp")
from verify_sol_reduction import build_graph, formula_sat, random_formula
from guarded_reduction import build_guarded_graph
from mc_check import eccentricity, distances_from
from decomp import layers, caseA0, caseB
from fast_a1 import caseA1_fast

rng = random.Random(2026)
leaks = found = 0
for _ in range(400):
    n = rng.randint(1, 3); m = rng.randint(1, 3)
    cl = random_formula(rng, n, m)
    g = build_graph(n, cl)
    if len(distances_from(g, "u")) != len(g):
        continue
    if min(eccentricity(g, v) for v in g) != 3:
        continue
    sat = formula_sat(n, cl)
    L1, L2, L3 = layers(g)
    a1 = caseA1_fast(g, L1, L2, L3) is not None
    a0 = bool(caseA0(g, L3))
    b = caseB(g, L1)
    mc = a1 or a0 or bool(b)
    if sat != mc:
        leaks += 1
        if bool(b):
            found += 1
        if leaks <= 3:
            print(f"UNGUARDED leak sat={sat} mc={mc} A1={a1} A0={a0} "
                  f"B={[x[0] for x in b][:4]} n={n} cl={cl}")
print(f"UNGUARDED: leaks reproduced={leaks} (of which case-B={found})")
print("expected from Block 8: 50 spurious cuts on this exact battery")

# and the guarded version of the SAME formulas
rng = random.Random(2026)
gl = 0
for _ in range(400):
    n = rng.randint(1, 3); m = rng.randint(1, 3)
    cl = random_formula(rng, n, m)
    g = build_guarded_graph(n, cl)
    sat = formula_sat(n, cl)
    L1, L2, L3 = layers(g)
    a1 = caseA1_fast(g, L1, L2, L3) is not None
    a0 = bool(caseA0(g, L3))
    b = caseB(g, L1)
    mc = a1 or a0 or bool(b)
    if sat != mc:
        gl += 1
        print(f"GUARDED leak sat={sat} mc={mc} A1={a1} A0={a0} "
              f"B={[x[0] for x in b][:4]} n={n} cl={cl}")
print(f"GUARDED on the same 400-formula battery: leaks={gl}")
