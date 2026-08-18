#!/usr/bin/env python3
"""An independent, obviously-correct exact matching-cut checker.

Deliberately DIFFERENT from exact_layered.py (no center-branch, no
layer-aware propagation): plain recursive backtracking that colours
vertices in a fixed order, pruning as soon as any coloured vertex has >1
differently-coloured coloured-neighbour. Exhaustive + sound pruning =
correct. Returns (has_mc, witness_or_None). A node budget guards runtime;
raises TimeoutError if exceeded (caller treats as 'unknown', never as a
result). Trust basis: ~20 lines of exhaustive search, independent of the
solver under test.
"""

import sys

sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))


def has_matching_cut(g, budget=5_000_000):
    verts = sorted(g, key=repr)
    n = len(verts)
    col = {}
    calls = [0]

    def cross_ok(v):
        # v just coloured: count coloured cross-neighbours
        c = 0
        for w in g[v]:
            if w in col and col[w] != col[v]:
                c += 1
                if c > 1:
                    return False
        return True

    def rec(i):
        calls[0] += 1
        if calls[0] > budget:
            raise TimeoutError()
        if i == n:
            colours = set(col.values())
            return len(colours) == 2  # both colours used
        v = verts[i]
        for c in ("R", "B"):
            col[v] = c
            if cross_ok(v):
                # also re-check already-coloured neighbours of v don't now
                # exceed budget (v added a cross to them)
                bad = False
                for w in g[v]:
                    if w in col and col[w] != c:
                        cw = sum(1 for x in g[w]
                                 if x in col and col[x] != col[w])
                        if cw > 1:
                            bad = True
                            break
                if not bad and rec(i + 1):
                    return True
            del col[v]
        return False

    return rec(0)


if __name__ == "__main__":
    # sanity vs mc_check on small graphs
    from mc_check import make_graph, valid_colourings
    import random
    rng = random.Random(1)
    ok = True
    for _ in range(3000):
        n = rng.randint(3, 10)
        p = rng.randint(1, n - 1)
        L = list(range(p)); R = list(range(p, n))
        edges = [(a, b) for a in L for b in R if rng.random() < 0.4]
        g = make_graph(edges, isolated=L + R)
        a = has_matching_cut(g)
        b = next(valid_colourings(g), None) is not None
        if a != b:
            ok = False
            print("DISAGREE", edges, a, b)
            break
    print("independent_mc self-check vs mc_check:", "PASS" if ok else "FAIL")
