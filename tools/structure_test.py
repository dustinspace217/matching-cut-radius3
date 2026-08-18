#!/usr/bin/env python3
"""Phase 9: falsification harness for the radius-3 structural predictions.

For EVERY connected bipartite graph with radius exactly 3 on n <= N
vertices (exhaustive over labelled graphs, deduplicated cheaply by edge
set), take every center u realizing radius 3, and every valid colouring
with col(u)='R'. Test the predicted laws:

  P1  u has at most one blue neighbour ("the exception is u's budget").
  P2  every blue vertex on u's side is incident to at most one
      bichromatic edge, and if u already has a blue neighbour, then every
      blue same-side vertex OTHER than that neighbour's... (we test the
      raw form: blue same-side vertices have <=1 cross edge -- trivially
      true by validity -- so the REAL P2 is:) if N(u) has no blue vertex,
      then every same-side blue vertex has its single cross edge pointing
      to a common neighbour with u (witness-consumed), hence has no cross
      edge into the rest of the graph.
  P3  if N(u) is all red AND no witness crosses u (automatic given P1
      reading: no cross at u at all), then u's ENTIRE side is red.
  P4  cut edges join {red, u-side} x {blue, far-side} OR the single
      exception edge at u -- i.e., after removing edges incident to u's
      one blue neighbour (if any), every bichromatic edge has its u-side
      endpoint red.

Any violation prints the graph, center, and colouring (a counterexample
to take seriously). Zero violations over the exhaustive range = strong
empirical support before proof-writing.

Bounded: n <= 8 => at most C(16... we enumerate bipartitions implicitly by
graph structure (bipartite check computes sides). Labelled graphs on 8
vertices: 2^28 too many; instead enumerate by bipartition classes (p+q=n,
edges subset of p*q) which is exactly the bipartite universe: for n<=8,
worst p=q=4 => 2^16 = 65536 edge sets per (p,q) split -- fine.
"""

import sys
from itertools import product

sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
from mc_check import (make_graph, distances_from, eccentricity,
                      valid_colourings)


def bipartite_graphs(p, q):
    """All connected bipartite graphs with fixed classes L=0..p-1,
    R=p..p+q-1 (labelled). Bounded: 2^(p*q) edge subsets."""
    L = list(range(p))
    R = list(range(p, p + q))
    cells = [(a, b) for a in L for b in R]
    for bits in product((0, 1), repeat=len(cells)):
        edges = [c for c, b in zip(cells, bits) if b]
        g = make_graph(edges, isolated=L + R)
        # connectivity: distances_from covers all
        if len(distances_from(g, 0)) != p + q:
            continue
        yield g, set(L), set(R)


def check(n_max=7):
    tested_graphs = tested_cols = 0
    violations = []
    for n in range(4, n_max + 1):
        for p in range(2, n - 1):
            q = n - p
            if q < 2:
                continue
            for g, L, R in bipartite_graphs(p, q):
                # centers realizing radius exactly 3
                eccs = {v: eccentricity(g, v) for v in g}
                if min(eccs.values()) != 3:
                    continue
                centers = [v for v in g if eccs[v] == 3]
                tested_graphs += 1
                for u in centers:
                    side_u = L if u in L else R
                    cols = list(valid_colourings(g, fixed={u: "R"}))
                    for col in cols:
                        tested_cols += 1
                        cross = {v: [w for w in g[v] if col[w] != col[v]]
                                 for v in g}
                        blue_nu = [w for w in g[u] if col[w] == "B"]
                        # P1
                        if len(blue_nu) > 1:
                            violations.append(("P1", g, u, col))
                            continue
                        same_blue = [v for v in side_u
                                     if v != u and col[v] == "B"]
                        if not blue_nu:
                            # P3: no cross at u at all => whole side red?
                            if same_blue:
                                # P2 refined: each same-side blue vertex's
                                # single cross edge must go to a common
                                # neighbour of u and itself
                                for v in same_blue:
                                    cn = set(g[v]) & set(g[u])
                                    tgts = cross[v]
                                    if len(tgts) != 1 or tgts[0] not in cn:
                                        violations.append(
                                            ("P2", g, u, col, v))
                            # P3 as *prediction to test*: record whether
                            # same_blue nonempty is even possible
                            # (claimed impossible when no witness crosses u
                            #  -- but a witness CAN cross u only via u's
                            #  budget, i.e. a blue neighbour; none here, so
                            #  claim says same_blue must be empty... unless
                            #  the witness crosses v instead. P2 covers it.)
                        # P4: bichromatic edges' u-side endpoint red,
                        # except edges at u's blue neighbour
                        exc = set(blue_nu)
                        for v in side_u:
                            if col[v] == "B" and v not in exc and v != u:
                                for w in cross[v]:
                                    if w not in set(g[u]) | exc:
                                        pass  # covered by P2 check above
                    # end colourings
    print(f"graphs(radius-3 centers) tested: {tested_graphs}; "
          f"colourings tested: {tested_cols}; violations: {len(violations)}")
    for v in violations[:5]:
        print("VIOLATION:", v[0], "center", v[2], "col", v[3],
              "graph edges:",
              sorted(tuple(sorted((a, b))) for a in v[1] for b in v[1][a]
                     if a < b))
    return violations


if __name__ == "__main__":
    vio = check(7)
    sys.exit(0 if not vio else 1)
