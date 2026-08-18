#!/usr/bin/env python3
"""Fast sensitivity/mutation test: does the harness DETECT a broken guard
battery? Small formulas only, case-B search short-circuits on first hit."""
import sys, random
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
sys.path.insert(0, "/tmp/claude/pvnp")
from mc_check import eccentricity, distances_from
from verify_sol_reduction import formula_sat
from decomp import layers, caseA0
from fast_a1 import caseA1_fast
from gbuild import build


def caseB_any(g, L1, budget=5_000_000):
    """Same as decomp.caseB but stops at the first surviving b."""
    verts = sorted(g, key=repr)
    for b in sorted(L1, key=repr):
        col = {"u": "R", b: "B"}
        for w in L1:
            if w != b:
                col[w] = "R"
        free = [v for v in verts if v not in col]
        calls = [0]

        def okv(v):
            return sum(1 for w in g[v]
                       if w in col and col[w] != col[v]) <= 1

        def rec(i):
            calls[0] += 1
            if calls[0] > budget:
                raise TimeoutError()
            if i == len(free):
                return True
            v = free[i]
            for c in ("R", "B"):
                col[v] = c
                if okv(v) and all(okv(w) for w in g[v] if w in col):
                    if rec(i + 1):
                        return True
                del col[v]
            return False
        try:
            if rec(0):
                return b
        except TimeoutError:
            return "TIMEOUT"
    return None


def battery(builder, label, rounds=40, seed=5):
    rng = random.Random(seed)
    mism = bs = skipped = 0
    for _ in range(rounds):
        n = rng.randint(1, 2); m = 1
        cl = [[(rng.randrange(n), rng.random() < 0.5) for _ in range(3)]
              for _ in range(m)]
        # force some UNSAT instances by using 2 clauses over 1 var
        if rng.random() < 0.5:
            n = 1
            cl = [[(0, True), (0, True), (0, False)],
                  [(0, True), (0, False), (0, False)]]
        g = builder(n, cl)
        if len(distances_from(g, "u")) != len(g):
            skipped += 1; continue
        if min(eccentricity(g, v) for v in g) != 3:
            skipped += 1; continue
        L1, L2, L3 = layers(g)
        a1 = caseA1_fast(g, L1, L2, L3) is not None
        a0 = bool(caseA0(g, L3))
        b = caseB_any(g, L1)
        if b:
            bs += 1
        if formula_sat(n, cl) != (a1 or a0 or bool(b)):
            mism += 1
    print(f"{label:36s} mismatches={mism:3d} caseB-alive={bs:3d} "
          f"skipped={skipped}", flush=True)


battery(lambda n, c: build(n, c), "ORIGINAL guarded")
battery(lambda n, c: build(n, c, guards_for=lambda W: W.startswith("q")),
        "MUTANT: guards only for q_i")
battery(lambda n, c: build(n, c, guards_for=lambda W: False),
        "MUTANT: no guards at all")
battery(lambda n, c: build(n, c, no_killer=True),
        "MUTANT: killer Zk disconnected")
battery(lambda n, c: build(n, c, drop_T2=True), "MUTANT: one ballast only")
