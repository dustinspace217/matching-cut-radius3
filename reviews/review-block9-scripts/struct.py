#!/usr/bin/env python3
"""Structural audit of the guarded graph: radius, diameter, layer sizes,
L3 degrees (case-A0 claim), selectability, and whether the ISLAND
instance derived from the guarded graph equals the base one."""
import sys, random
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
sys.path.insert(0, "/tmp/claude/pvnp")
from mc_check import eccentricity, distances_from
from guarded_reduction import build_guarded_graph
from sol_set_reduction import build_set_instance
from decomp import layers, island_instance
from verify_sol_reduction import random_formula


def audit(n, clauses):
    g = build_guarded_graph(n, clauses)
    eccs = {v: eccentricity(g, v) for v in g}
    rad = min(eccs.values()); diam = max(eccs.values())
    L1, L2, L3 = layers(g)
    minl3 = min(len(g[z]) for z in L3)
    centers = [v for v in g if eccs[v] == rad]
    # derived ISLAND from the guarded graph vs the base set instance
    groups_g, zadj_g, S = island_instance(g, L1, L2, L3)
    groups_b, zadj_b = build_set_instance(n, clauses)
    same_groups = (sorted(tuple(sorted(t)) for t in groups_g) ==
                   sorted(tuple(sorted(t)) for t in groups_b))
    # compare z rows restricted to nonempty
    zg = sorted(tuple(sorted(v)) for v in zadj_g.values() if v)
    zb = sorted(tuple(sorted(v)) for v in zadj_b.values() if v)
    empty_z = [z for z, v in zadj_g.items() if not v]
    return dict(n=n, m=len(clauses), V=len(g), rad=rad, diam=diam,
                centers=len(centers), L1=len(L1), L2=len(L2), L3=len(L3),
                minL3deg=minl3, sel=len(S), same_groups=same_groups,
                same_z=(zg == zb), empty_z=len(empty_z))


rng = random.Random(3)
rows = []
for n in (1, 2, 3):
    for m in (1, 2, 3):
        cl = random_formula(rng, n, m)
        rows.append(audit(n, cl))
# degenerate: unused variable
rows.append(audit(2, [[(0, True), (0, True), (0, False)]]))
for r in rows:
    print(r)
