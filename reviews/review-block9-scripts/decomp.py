#!/usr/bin/env python3
"""Case-decomposed exact analysis of the guarded graph.

MC exists  <=>  (WLOG u red)  A1 or A0 or B, where
  A1: u red, all L1 red, blue cap L2 nonempty  -- decided via ISLAND
  A0: u red, all L1 red, blue subset of L3     -- decided by min L3 degree
  B : u red, exactly one L1 vertex blue        -- decided by pinned search
(>=2 blue L1 with u red is impossible: u would have >=2 cross edges.)

Each branch is decided exactly; B is searched per candidate b with the
rest of L1 pinned red, which collapses the tree.
"""
import sys
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
from mc_check import distances_from
from set_problem import solve_bruteforce


def layers(g, u="u"):
    d = distances_from(g, u)
    assert len(d) == len(g), "disconnected"
    assert max(d.values()) == 3, f"ecc(u)={max(d.values())}"
    return ({v for v in g if d[v] == 1},
            {v for v in g if d[v] == 2},
            {v for v in g if d[v] == 3})


def island_instance(g, L1, L2, L3):
    """Derived ISLAND instance: X = selectable L2 (exactly one L1 nbr),
    groups = classes sharing that witness, Z = L3."""
    S = [v for v in L2 if len(g[v] & L1) == 1]
    bywit = {}
    for v in S:
        w = next(iter(g[v] & L1))
        bywit.setdefault(w, []).append(v)
    groups = [tuple(sorted(vs, key=repr)) for vs in bywit.values()]
    Sset = set(S)
    zadj = {}
    for z in L3:
        nb = tuple(sorted((g[z] & Sset), key=repr))
        zadj[z] = nb
    return groups, zadj, Sset


def caseA1(g, L1, L2, L3):
    """Exact: enumerate B2 subsets of selectable L2 honouring alpha,
    then check beta over N(B2) and gamma over ALL of L2 minus B2 (not
    just the selectable ones -- the graph demands it)."""
    from itertools import combinations
    S = sorted((v for v in L2 if len(g[v] & L1) == 1), key=repr)
    wit = {v: next(iter(g[v] & L1)) for v in S}
    for r in range(1, len(S) + 1):
        for B2t in combinations(S, r):
            B2 = set(B2t)
            ws = [wit[v] for v in B2]
            if len(set(ws)) != len(ws):
                continue
            B3 = set()
            for v in B2:
                B3 |= (g[v] & L3)
            if any(len(g[z] - B2) > 1 for z in B3):
                continue
            if any(len(g[v] & B3) > 1 for v in L2 - B2):
                continue
            return B2, B3
    return None


def caseA0(g, L3):
    return [z for z in L3 if len(g[z]) <= 1]


def caseB(g, L1, budget=50_000_000):
    """For each candidate unique blue L1 vertex b, pin u=R, b=B, rest of
    L1 = R, and search exhaustively for a valid completion."""
    hits = []
    verts = sorted(g, key=repr)
    for b in sorted(L1, key=repr):
        pin = {"u": "R", b: "B"}
        for w in L1:
            if w != b:
                pin[w] = "R"
        col = dict(pin)
        free = [v for v in verts if v not in pin]
        calls = [0]

        def okv(v):
            c = 0
            for w in g[v]:
                if w in col and col[w] != col[v]:
                    c += 1
            return c <= 1

        # pinned vertices must already be consistent
        bad = any(not okv(v) for v in pin if all(
            w in col for w in g[v]))

        def rec(i):
            calls[0] += 1
            if calls[0] > budget:
                raise TimeoutError()
            if i == len(free):
                return len(set(col.values())) == 2
            v = free[i]
            for c in ("R", "B"):
                col[v] = c
                if okv(v) and all(okv(w) for w in g[v] if w in col):
                    if rec(i + 1):
                        return True
                del col[v]
            return False

        if rec(0):
            hits.append((b, dict(col)))
    return hits


def analyse(g, verbose=True):
    L1, L2, L3 = layers(g)
    a1 = caseA1(g, L1, L2, L3)
    a0 = caseA0(g, L3)
    b = caseB(g, L1)
    if verbose:
        print(f"  |V|={len(g)} |L1|={len(L1)} |L2|={len(L2)} |L3|={len(L3)} "
              f"minL3deg={min(len(g[z]) for z in L3)}")
        print(f"  A1={'YES' if a1 else 'no'}  A0={'YES' if a0 else 'no'} "
              f"({a0[:3]})  B={'YES' if b else 'no'} ({[x[0] for x in b]})")
    return a1, a0, b
