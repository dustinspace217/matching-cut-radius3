#!/usr/bin/env python3
"""Adversarial audit G: enumerate EVERY valid colouring of real guarded
graphs and classify it against section 4's case split.

Section 4 claims: after normalising u to red, every valid colouring is
case A1 (all L1 red, blue cap L2 nonempty). Any A0 or B colouring found
refutes Claim 4.2 or Claim 4.4 directly, with a witness.
"""
import sys, time, itertools
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
from guarded_reduction import build_guarded_graph
from mc_check import distances_from
from verify_sol_reduction import formula_sat


def all_valid_colourings(g, cap=200000):
    """All valid colourings with u pinned RED (the swap halves the space).
    Backtracking with the <=1-cross prune; yields dicts."""
    verts = [v for v in sorted(g, key=repr) if v != "u"]
    # order by BFS from u for strong early pruning
    d = distances_from(g, "u")
    verts.sort(key=lambda v: (d[v], repr(v)))
    col = {"u": "R"}
    out = []

    def cross(v):
        return sum(1 for w in g[v] if w in col and col[w] != col[v])

    def rec(i):
        if len(out) >= cap:
            return
        if i == len(verts):
            if any(c == "B" for c in col.values()):
                out.append(dict(col))
            return
        v = verts[i]
        for c in ("R", "B"):
            col[v] = c
            if cross(v) <= 1 and all(cross(w) <= 1 for w in g[v] if w in col):
                rec(i + 1)
            del col[v]

    rec(0)
    return out


def classify(g, col):
    d = distances_from(g, "u")
    L1 = [v for v in g if d[v] == 1]
    L2 = [v for v in g if d[v] == 2]
    blueL1 = [v for v in L1 if col[v] == "B"]
    if blueL1:
        return f"B(b={blueL1})"
    return "A1" if any(col[v] == "B" for v in L2) else "A0"


def main():
    cases = [(1, [[(0, True), (0, True), (0, True)]]),          # SAT
             (1, [[(0, True), (0, True), (0, False)]]),          # SAT (x=1)
             (1, [[(0, True), (0, True), (0, False)],
                  [(0, False), (0, False), (0, True)]]),         # UNSAT
             (1, [[(0, True), (0, False), (0, False)],
                  [(0, True), (0, True), (0, False)]]),          # UNSAT
             (2, [[(0, True), (1, True), (1, False)]]),          # SAT
             (2, [[(0, True), (0, True), (1, False)],
                  [(0, False), (0, False), (1, True)]]),
             ]
    bad = 0
    for n, cls in cases:
        g = build_guarded_graph(n, cls)
        t0 = time.time()
        cols = all_valid_colourings(g)
        kinds = {}
        for c in cols:
            k = classify(g, c)
            kinds[k] = kinds.get(k, 0) + 1
        sat = formula_sat(n, cls)
        off = {k: v for k, v in kinds.items() if k not in ("A1",)}
        if off:
            bad += 1
        print(f"n={n} m={len(cls)} |V|={len(g)} sat={sat} "
              f"u-red valid colourings={len(cols)} kinds={kinds} "
              f"({time.time()-t0:.0f}s)"
              + ("   *** NON-A1 COLOURING FOUND ***" if off else ""))
        if off:
            for c in cols:
                if classify(g, c) != "A1":
                    print("   witness:", {k: v for k, v in c.items()
                                          if v == "B"})
                    break
    print("non-A1 instances:", bad)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
