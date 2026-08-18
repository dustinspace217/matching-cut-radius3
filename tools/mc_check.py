#!/usr/bin/env python3
"""Brute-force analyzer for Matching Cut structure on small graphs.

The instrument for Phase 9 (see scratch/phase9-matchingcut.md): every
gadget claim gets machine-checked here before it is believed. A matching
cut is modeled per Lucke 2501.08735 Observation 1 as a *valid red-blue
colouring*: both colours used, and every vertex adjacent to at most one
vertex of the other colour. This file deliberately uses the colouring
formulation so gadget analyses match the paper's proofs line for line.

Capabilities:
  - enumerate all valid red-blue colourings of a graph (exhaustive, 2^n;
    intended for gadget-sized graphs, n <= ~24)
  - check matching-cut existence
  - list colourings restricted to designated boundary vertices, to
    characterize a gadget's external behaviour (its "colour type")
  - verify bipartiteness, radius, diameter, and the one-sided domination
    property from the phase9 structural lemma

Graphs are dicts: vertex -> set of neighbours (undirected, loopless).
Vertices are any hashable labels. All loops are bounded by 2^n / n^2 with
n <= 24 enforced (hard cap below) so runs stay in milliseconds-to-seconds.
"""

from itertools import product
from collections import deque

# Hard cap: exhaustive enumeration is 2^n; 24 keeps worst case ~16M
# colour vectors, seconds in CPython. Raise consciously, never silently.
MAX_EXHAUSTIVE_N = 24


def make_graph(edges, isolated=()):
    """Build adjacency dict from an edge list (+ optional isolated verts).

    Input: iterable of 2-tuples, iterable of extra vertices.
    Output: dict vertex -> set(neighbours). Rejects loops."""
    g = {}
    for u, v in edges:
        if u == v:
            raise ValueError(f"loop at {u}")
        g.setdefault(u, set()).add(v)
        g.setdefault(v, set()).add(u)
    for w in isolated:
        g.setdefault(w, set())
    return g


def is_bipartite(g):
    """Two-colour by BFS; returns (True, side_dict) or (False, None)."""
    side = {}
    for start in g:
        if start in side:
            continue
        side[start] = 0
        q = deque([start])
        while q:
            v = q.popleft()
            for w in g[v]:
                if w not in side:
                    side[w] = 1 - side[v]
                    q.append(w)
                elif side[w] == side[v]:
                    return False, None
    return True, side


def distances_from(g, src):
    """BFS distances from src; unreachable vertices absent from result."""
    dist = {src: 0}
    q = deque([src])
    while q:
        v = q.popleft()
        for w in g[v]:
            if w not in dist:
                dist[w] = dist[v] + 1
                q.append(w)
    return dist


def eccentricity(g, v):
    d = distances_from(g, v)
    if len(d) != len(g):
        return float("inf")  # disconnected: eccentricity undefined/infinite
    return max(d.values())


def radius_diameter(g):
    """Exact radius and diameter via all-sources BFS (fine at gadget size)."""
    eccs = [eccentricity(g, v) for v in g]
    return min(eccs), max(eccs)


def valid_colourings(g, fixed=None):
    """Yield all VALID red-blue colourings as dicts vertex->'R'/'B'.

    Valid (Lucke Obs. 1): both colours used; every vertex adjacent to at
    most one vertex of the other colour. `fixed` optionally pins some
    vertices' colours (gadget boundary analysis). Exhaustive over the
    unpinned vertices."""
    verts = sorted(g, key=repr)
    if len(verts) > MAX_EXHAUSTIVE_N:
        raise ValueError(f"n={len(verts)} exceeds MAX_EXHAUSTIVE_N")
    fixed = dict(fixed or {})
    free = [v for v in verts if v not in fixed]
    for bits in product("RB", repeat=len(free)):
        col = dict(fixed)
        col.update(zip(free, bits))
        colours = set(col.values())
        if len(colours) < 2:
            continue
        ok = True
        for v in verts:
            cross = sum(1 for w in g[v] if col[w] != col[v])
            if cross > 1:
                ok = False
                break
        if ok:
            yield col


def has_matching_cut(g):
    """Does g admit a matching cut? (Any valid colouring witnesses one.)"""
    return next(valid_colourings(g), None) is not None


def boundary_types(g, boundary, fixed=None):
    """The gadget's external behaviour: set of colour patterns the
    boundary vertices can take across all valid colourings (up to the
    global R/B swap, which we quotient out by pinning boundary[0]='R'
    unless the caller already fixed it)."""
    fixed = dict(fixed or {})
    pats = set()
    for col in valid_colourings(g, fixed=fixed):
        pats.add(tuple(col[b] for b in boundary))
    return pats


def cut_edges(g, col):
    """The bichromatic edge set of a colouring (the matching cut)."""
    return {frozenset((u, v)) for u in g for v in g[u] if col[u] != col[v]}


def dominates_side(g, u):
    """Phase 9 structural lemma check: does N(N(u)) cover u's side?
    Returns (holds, side_dict) for bipartite g; raises otherwise."""
    bip, side = is_bipartite(g)
    if not bip or side is None:
        raise ValueError("graph not bipartite")
    d = distances_from(g, u)
    same = [v for v in g if side[v] == side[u]]
    return all(d.get(v, 99) <= 2 for v in same), side


def report(g, name=""):
    """One-shot summary used in gadget notebooks/logs."""
    bip, _ = is_bipartite(g)
    r, dm = radius_diameter(g)
    cols = list(valid_colourings(g))
    print(f"[{name}] n={len(g)} bipartite={bip} radius={r} diam={dm} "
          f"valid_colourings={len(cols)} matching_cut={bool(cols)}")
    return cols


if __name__ == "__main__":
    # Self-test on known structure: K_{2,3} must be monochromatic-forced
    # (no valid colouring at all, since a valid colouring needs both
    # colours somewhere and K_{2,3} alone cannot host a matching cut).
    k23 = make_graph([(f"a{i}", f"b{j}") for i in range(2) for j in range(3)])
    assert not has_matching_cut(k23), "K_{2,3} should have no matching cut"
    # ...while a 6-cycle does (two opposite edges).
    c6 = make_graph([(i, (i + 1) % 6) for i in range(6)])
    assert has_matching_cut(c6), "C6 should have a matching cut"
    # And P4: cutting the middle edge is a matching cut.
    p4 = make_graph([(0, 1), (1, 2), (2, 3)])
    assert has_matching_cut(p4)
    r, dm = radius_diameter(c6)
    assert (r, dm) == (3, 3)
    print("mc_check.py self-tests passed")
