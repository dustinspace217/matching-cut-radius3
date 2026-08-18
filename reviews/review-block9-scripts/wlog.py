#!/usr/bin/env python3
"""Direct check of the WLOG and the case decomposition: enumerate ALL
valid colourings of a small guarded graph and classify by
(colour of u, #blue L1). Also verify the colour-swap involution maps the
valid-colouring set onto itself."""
import sys
from collections import Counter
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
sys.path.insert(0, "/tmp/claude/pvnp")
from attack import all_valid_colourings, layers
from guarded_reduction import build_guarded_graph
from verify_sol_reduction import formula_sat

cl = [[(0, True), (0, True), (0, True)]]      # SAT, n=1, m=1
g = build_guarded_graph(1, cl)
L1, L2, L3, L4 = layers(g)
print("|V|", len(g), "sat", formula_sat(1, cl), "L4", L4)
cols = all_valid_colourings(g, limit=200000)
print("total valid colourings:", len(cols))
cnt = Counter((c["u"], sum(1 for w in L1 if c[w] == "B")) for c in cols)
for k in sorted(cnt):
    print(f"  u={k[0]} blueL1={k[1]}: {cnt[k]}")
S = set(frozenset(v for v in g if c[v] == "B") for c in cols)
swapped = set(frozenset(v for v in g if v not in b) for b in S)
print("colour-swap closed:", S == swapped)
# every u-blue colouring's swap is u-red and already in the set
ub = [c for c in cols if c["u"] == "B"]
print("u-blue colourings:", len(ub),
      "all swaps present:",
      all(frozenset(v for v in g if c[v] == "R") in S for c in ub))
