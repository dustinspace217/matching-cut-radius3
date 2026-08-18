#!/usr/bin/env python3
"""SENSITIVITY / mutation test: break the guard battery deliberately and
confirm the harness detects it. If a mutant still passes, the batteries
are too weak to be evidence for the original."""
import sys, random
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
sys.path.insert(0, "/tmp/claude/pvnp")
from mc_check import make_graph, eccentricity, distances_from
from verify_sol_reduction import formula_sat
from decomp import layers, caseA0, caseB
from fast_a1 import caseA1_fast


def build(n, clauses, drop_T2=False, guards_for=None, no_killer=False):
    E = []
    u = "u"
    base_w = []

    def l1(name):
        E.append((u, name))
    for i in range(n):
        qi = f"q{i}"; l1(qi); base_w.append(qi)
        E += [(qi, f"t{i}"), (qi, f"f{i}"), (f"t{i}", f"g{i}"),
              (f"f{i}", f"g{i}"), ("a", f"g{i}")]
    l1("w_a"); base_w.append("w_a"); E.append(("w_a", "a"))
    for ci, cl in enumerate(clauses):
        occ = []
        for j, (vi, sign) in enumerate(cl):
            p = f"p_{ci}_{j}"; wp = f"w_{p}"; l1(wp); base_w.append(wp)
            E.append((wp, p))
            base = f"t{vi}" if sign else f"f{vi}"
            for k in (0, 1):
                E += [(base, f"c_{ci}_{j}_{k}"), (p, f"c_{ci}_{j}_{k}")]
            occ.append(p)
        for p in occ:
            E.append((f"z{ci}", p))
    zk = "Zk"
    ts = ("T1",) if drop_T2 else ("T1", "T2")
    for t in ts:
        for s in ("a", "b"):
            w = f"w{t}{s}"; l1(w); E.append((w, t))
        if not no_killer:
            E.append((t, zk))
    for W in base_w:
        if guards_for is not None and not guards_for(W):
            continue
        gw = f"G_{W}"; wpr = f"wp_{W}"; l1(wpr)
        E += [(W, gw), (wpr, gw)]
        if not no_killer:
            E.append((gw, zk))
    return make_graph(E)

