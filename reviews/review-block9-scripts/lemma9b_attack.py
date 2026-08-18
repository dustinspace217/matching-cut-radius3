#!/usr/bin/env python3
"""ATTACK on Lemma 9B AS STATED IN THE NOTE.

Note 9B: "case-A1 colourings exist iff the derived ISLAND instance
(X = selectable L2, Z = L3, groups = shared-witness classes) is YES",
with ISLAND as defined in 9.2 / set_problem.py -- where UNSELECTABLE L2
vertices are simply not listed (set_problem.py docstring, lines 19-22).

But in the graph, beta counts ALL L2 neighbours of z (selectable or not)
and gamma must hold at unselectable L2 vertices too. So the abstraction
drops constraints. Candidate counterexample below.
"""
import sys
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
sys.path.insert(0, "/tmp/claude/pvnp")
from mc_check import make_graph, is_bipartite, eccentricity, distances_from
from set_problem import solve_bruteforce
from verify_reformulation import layers, caseA_exists_via_colourings, \
    caseA1_via_sets, caseA0_via_sets
from decomp import island_instance

E = [("u", "w1"), ("u", "w2"), ("u", "w3"), ("u", "w4"),
     ("w1", "v"),
     ("w2", "y1"), ("w3", "y1"),
     ("w3", "y2"), ("w4", "y2"),
     ("z", "v"), ("z", "y1"), ("z", "y2")]
g = make_graph(E)
print("bipartite:", is_bipartite(g)[0])
eccs = {x: eccentricity(g, x) for x in g}
print("radius:", min(eccs.values()), "diameter:", max(eccs.values()),
      "ecc(u):", eccs["u"], "|V|:", len(g))
L1, L2, L3 = layers(g, "u")
print("L1:", sorted(L1), "L2:", sorted(L2), "L3:", sorted(L3))
sel = [x for x in L2 if len(g[x] & L1) == 1]
print("selectable L2:", sorted(sel))

a1_truth, a0_truth = caseA_exists_via_colourings(g, "u", L1, L2)
a1_sets = caseA1_via_sets(g, "u", L1, L2, L3)
print("GROUND TRUTH case-A1 exists (all colourings):", a1_truth)
print("verify_reformulation's set criterion (gamma/beta over ALL L2):",
      a1_sets)

groups, zadj, S = island_instance(g, L1, L2, L3)
print("derived ISLAND instance per the note: groups=", groups,
      " zadj=", zadj)
B = solve_bruteforce(groups, zadj)
print("ISLAND (set_problem.solve_bruteforce) says:",
      "YES" if B is not None else "NO", B)
print()
if (B is not None) != a1_truth:
    print("*** LEMMA 9B AS STATED IS REFUTED: ISLAND="
          f"{'YES' if B is not None else 'NO'} but case-A1={a1_truth} ***")
else:
    print("no divergence on this instance")
