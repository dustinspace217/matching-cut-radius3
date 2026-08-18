#!/usr/bin/env python3
"""Phase 9 Block 6: a provably-CORRECT MC decision procedure specialized
to the center-branch, instrumented to measure whether its work grows
polynomially (poly evidence) or explodes (hardness evidence).

Correctness is guaranteed because the procedure is an exact search that
never prunes unsoundly: it branches on the center u's cut edge (>=n+1
exhaustive cases covering every valid colouring's treatment of u),
propagates forced colours soundly, then on the residual recurses by the
SAME exact search restricted to still-free vertices, treating each free
connected component independently BUT re-checking cross-component budget
interactions by carrying pinned boundary colours. To stay exact without
the earlier mono-completion bug, when free components remain after
propagation we recurse by picking ONE still-free vertex, trying both
colours (a sound 2-way branch), and propagating -- classic DPLL over the
colour variables, which is always correct. The INSTRUMENT is the count of
such 2-way branch decisions ('splits'); if splits grow polynomially in n
across random instances, the structure admits bounded search (poly
evidence); if exponentially, hardness evidence.

We compare the decision against brute force on every call (small n) and
report the split-count distribution vs n on larger random instances.
"""

import sys
import random
from collections import deque

sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
from mc_check import make_graph, eccentricity, distances_from, \
    valid_colourings
from candidate_solver import propagate, Fail, full_check


class Counter:
    def __init__(self):
        self.splits = 0


def choose_free(g, col):
    for v in g:
        if v not in col:
            return v
    return None


def solve(g, col, cnt, budget):
    """Exact: does `col` extend to a valid FULL colouring (both colours,
    per-vertex <=1 cross)? DPLL over colour vars with sound propagation.
    `budget` bounds splits to detect explosion without hanging."""
    try:
        col = propagate(g, col)
    except Fail:
        return False
    v = choose_free(g, col)
    if v is None:
        return full_check(g, col)
    if cnt.splits > budget:
        raise TimeoutError("split budget exceeded")
    cnt.splits += 1
    for c in ("R", "B"):
        nc = dict(col)
        nc[v] = c
        if solve(g, nc, cnt, budget):
            return True
    return False


def decide(g, budget=200000):
    """Center-branch wrapper. Returns (answer, splits) or raises Timeout."""
    eccs = {v: eccentricity(g, v) for v in g}
    u = min((v for v in g if eccs[v] == min(eccs.values())), key=repr)
    cnt = Counter()
    # branch on u's treatment: u=R with 0 or 1 blue neighbour; symmetric
    # u=B cases are covered by global R/B swap, so fixing u=R is WLOG for
    # EXISTENCE of a valid (both-colour) colouring.
    branches = []
    base = {u: "R"}
    for w in g[u]:
        base[w] = "R"
    branches.append(base)
    for b in g[u]:
        bs = {u: "R", b: "B"}
        for w in g[u]:
            if w != b:
                bs[w] = "R"
        for w in g[b]:
            if w != u:
                bs[w] = "B"
        branches.append(bs)
    for base in branches:
        if solve(g, base, cnt, budget):
            return True, cnt.splits
    return False, cnt.splits


def brute(g):
    return next(valid_colourings(g), None) is not None


def main():
    rng = random.Random(2026)
    # correctness sweep on random small + medium, then scaling on large
    from collections import defaultdict
    wrong = 0
    tested = 0
    splitmax = defaultdict(int)
    splitsum = defaultdict(int)
    splitcnt = defaultdict(int)
    for _ in range(60000):  # bounded
        n = rng.randint(6, 22)
        p = rng.randint(2, n - 2)
        L = list(range(p))
        R = list(range(p, n))
        prob = rng.uniform(0.12, 0.55)
        edges = [(a, b) for a in L for b in R if rng.random() < prob]
        g = make_graph(edges, isolated=L + R)
        if len(distances_from(g, 0)) != n:
            continue
        eccs = [eccentricity(g, v) for v in g]
        if min(eccs) != 3:
            continue
        try:
            ans, splits = decide(g)
        except TimeoutError:
            print(f"SPLIT EXPLOSION at n={n}: edges={sorted(edges)}")
            splitmax[n] = max(splitmax[n], 999999)
            continue
        tested += 1
        splitmax[n] = max(splitmax[n], splits)
        splitsum[n] += splits
        splitcnt[n] += 1
        if n <= 16:
            if ans != brute(g):
                wrong += 1
                if wrong <= 3:
                    print(f"WRONG n={n} ans={ans} edges={sorted(edges)}")
    print(f"tested {tested}; wrong (vs brute, n<=16): {wrong}")
    print("split-count by n (n: max, mean):")
    for n in sorted(splitmax):
        mean = splitsum[n] / max(1, splitcnt[n])
        print(f"  n={n:2d}: max={splitmax[n]:6d} mean={mean:8.1f} "
              f"(count {splitcnt[n]})")
    return wrong


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
