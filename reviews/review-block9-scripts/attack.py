#!/usr/bin/env python3
"""Adversarial probe of the guarded reduction.

Enumerates ALL valid matching-cut colourings of the guarded graph (own
backtracking enumerator, no 24-vertex cap) and classifies each by
(colour of u, number of blue L1 vertices) so we can see whether case B
is really dead and whether case-A solutions really track SAT.
"""
import sys
from collections import Counter
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
from mc_check import make_graph, is_bipartite, eccentricity, distances_from
from verify_sol_reduction import formula_sat
from guarded_reduction import build_guarded_graph


def layers(g, u="u"):
    d = distances_from(g, u)
    return ({v for v in g if d[v] == 1},
            {v for v in g if d[v] == 2},
            {v for v in g if d[v] == 3},
            {v for v in g if d[v] > 3})


def all_valid_colourings(g, limit=None):
    """Backtracking enumerator: yields every valid red/blue colouring
    (both colours used, every vertex <=1 cross neighbour)."""
    verts = sorted(g, key=repr)
    n = len(verts)
    col = {}

    def feasible(v, c):
        cnt = 0
        for w in g[v]:
            if w in col and col[w] != c:
                cnt += 1
                if cnt > 1:
                    return False
        for w in g[v]:
            if w in col and col[w] != c:
                cw = sum(1 for x in g[w] if x in col and col[x] != col[w])
                if cw > 1:
                    return False
        return True

    out = []

    def rec(i):
        if limit is not None and len(out) >= limit:
            return
        if i == n:
            if len(set(col.values())) == 2:
                out.append(dict(col))
            return
        v = verts[i]
        for c in ("R", "B"):
            col[v] = c
            if feasible(v, c):
                rec(i + 1)
            del col[v]
    rec(0)
    return out


def classify(n, clauses, limit=None, verbose=True):
    g = build_guarded_graph(n, clauses)
    assert is_bipartite(g)[0]
    L1, L2, L3, L4 = layers(g)
    assert not L4, f"L4 nonempty: {L4}"
    r = min(eccentricity(g, v) for v in g)
    sat = formula_sat(n, clauses)
    cols = all_valid_colourings(g, limit=limit)
    cnt = Counter()
    samples = {}
    for c in cols:
        key = (c["u"], sum(1 for w in L1 if c[w] == "B"))
        cnt[key] += 1
        samples.setdefault(key, c)
    if verbose:
        print(f"n={n} clauses={clauses} sat={sat} |V|={len(g)} radius={r} "
              f"validcolourings={len(cols)}")
        for k in sorted(cnt):
            print(f"   u={k[0]} blueL1={k[1]}: {cnt[k]}")
    return g, (L1, L2, L3), sat, cols, cnt, samples


if __name__ == "__main__":
    # a known UNSAT formula over 1 variable, 2 clauses
    f_unsat = [[(0, True), (0, True), (0, False)],
               [(0, True), (0, False), (0, False)]]
    print("formula_sat:", formula_sat(1, f_unsat))
    classify(1, f_unsat)
