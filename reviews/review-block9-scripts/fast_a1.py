#!/usr/bin/env python3
"""Exact case-A1 decision straight from the GRAPH (not from the ISLAND
abstraction), CNF + DPLL. Written from the colouring definition:

  blue = B2 u B3 with B2 subset of selectable L2 (exactly one L1 nbr),
  B3 = N(B2) cap L3, and validity means
    (alpha) witness map injective on B2
    (beta)  every z in B3 has <=1 neighbour in L2 outside B2
    (gamma) every v in L2 \\ B2 has <=1 neighbour in B3
  -- with gamma and beta quantified over ALL L2 vertices, selectable or
  not. Unselectable vertices are hard-coded outside B2.
"""
import sys
from itertools import combinations
sys.path.insert(0, "/tmp/claude/pvnp")
from island_sat import dpll


def caseA1_fast(g, L1, L2, L3):
    sel = [v for v in L2 if len(g[v] & L1) == 1]
    selset = set(sel)
    var = {}
    for v in sel:
        var[("b", v)] = len(var) + 1
    for z in L3:
        var[("t", z)] = len(var) + 1
    cls = []
    for z in L3:
        tz = var[("t", z)]
        nbL2 = sorted(g[z] & L2, key=repr)
        nbSel = [v for v in nbL2 if v in selset]
        for v in nbSel:
            cls.append((-var[("b", v)], tz))
        cls.append(tuple([-tz] + [var[("b", v)] for v in nbSel]))
        # beta over ALL L2 neighbours; unselectable ones contribute
        # a constant-false b-literal (i.e. they are simply omitted)
        for a, b in combinations(nbL2, 2):
            lits = [-tz]
            for x in (a, b):
                if x in selset:
                    lits.append(var[("b", x)])
            cls.append(tuple(lits))
    # alpha
    bywit = {}
    for v in sel:
        bywit.setdefault(next(iter(g[v] & L1)), []).append(v)
    for w, vs in bywit.items():
        for a, b in combinations(vs, 2):
            cls.append((-var[("b", a)], -var[("b", b)]))
    # gamma over ALL L2
    for v in L2:
        zs = sorted(g[v] & L3, key=repr)
        for z1, z2 in combinations(zs, 2):
            lits = [-var[("t", z1)], -var[("t", z2)]]
            if v in selset:
                lits.append(var[("b", v)])
            cls.append(tuple(lits))
    if not sel:
        return None
    cls.append(tuple(var[("b", v)] for v in sel))
    r = dpll(len(var), cls)
    if r is None:
        return None
    return frozenset(v for v in sel if r.get(var[("b", v)]))
