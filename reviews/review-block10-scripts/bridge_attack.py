#!/usr/bin/env python3
"""Adversarial audit E: Lemma D + Lemma A jointly, computed FROM THE GRAPH.

Nothing here reuses tools/sol_set_reduction.py or tools/set_problem.py --
the ISLAND instance is derived from build_guarded_graph's output by the
document's own recipe, and solved by a fresh brute force written here.

Three things compared per formula:
  (1) F satisfiable (brute force over assignments)
  (2) Lemma B' condition on the REAL guarded graph (all-L2 form, subsets
      of S enumerated directly)
  (3) ISLAND on the derived instance I(F) read off the graph

(1)==(2) is the composite claim of sections 5-6; (2)==(3) is Lemma D.
"""
import sys, random, itertools, time
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
from guarded_reduction import build_guarded_graph
from mc_check import distances_from
from verify_sol_reduction import formula_sat


def Bprime_on_graph(g):
    """Document's Lemma B' condition, enumerated over subsets of S."""
    d = distances_from(g, "u")
    L1 = {v for v in g if d[v] == 1}
    L2 = {v for v in g if d[v] == 2}
    L3 = {v for v in g if d[v] == 3}
    S = sorted((v for v in L2 if len(set(g[v]) & L1) == 1), key=repr)
    wit = {v: next(iter(set(g[v]) & L1)) for v in S}
    k = len(S)
    for mask in range(1, 1 << k):
        B2 = {S[i] for i in range(k) if mask >> i & 1}
        ws = [wit[v] for v in B2]
        if len(set(ws)) != len(ws):
            continue
        NB3 = set()
        for v in B2:
            NB3 |= set(g[v]) & L3
        if any(len(set(g[z]) - B2) > 1 for z in NB3):
            continue
        if any(len(set(g[v]) & NB3) > 1 for v in L2 - B2):
            continue
        return B2
    return None


def island_from_graph(g):
    """Derive I(F) from the graph exactly as Lemma D prescribes."""
    d = distances_from(g, "u")
    L1 = {v for v in g if d[v] == 1}
    L2 = {v for v in g if d[v] == 2}
    L3 = {v for v in g if d[v] == 3}
    S = sorted((v for v in L2 if len(set(g[v]) & L1) == 1), key=repr)
    wit = {v: next(iter(set(g[v]) & L1)) for v in S}
    groups = {}
    for v in S:
        groups.setdefault(wit[v], set()).add(v)
    Z = sorted((z for z in L3 if set(g[z]) & set(S)), key=repr)
    zadj = {z: set(g[z]) for z in Z}
    return S, list(groups.values()), zadj


def island_solve(X, groups, zadj):
    """Fresh brute force for ISLAND (alpha/beta/gamma), independent of
    tools/set_problem.py."""
    X = sorted(X, key=repr)
    k = len(X)
    xz = {x: [z for z, nb in zadj.items() if x in nb] for x in X}
    for mask in range(1, 1 << k):
        B = {X[i] for i in range(k) if mask >> i & 1}
        if any(len(grp & B) > 1 for grp in groups):
            continue
        touched = set()
        for x in B:
            touched.update(xz[x])
        if any(len(zadj[z] - B) > 1 for z in touched):
            continue
        if any(sum(1 for z in xz[x] if z in touched) > 1
               for x in X if x not in B):
            continue
        return B
    return None


def main():
    rng = random.Random(112358)
    shapes = []
    # exhaustive n=1 m=1,2 ; n=2 m=1
    for s in itertools.product((True, False), repeat=3):
        shapes.append((1, [list(zip((0, 0, 0), s))]))
    for s1 in itertools.product((True, False), repeat=3):
        for s2 in itertools.product((True, False), repeat=3):
            shapes.append((1, [list(zip((0, 0, 0), s1)),
                               list(zip((0, 0, 0), s2))]))
    for vis in itertools.product(range(2), repeat=3):
        for s in itertools.product((True, False), repeat=3):
            shapes.append((2, [list(zip(vis, s))]))
    # degenerate: unused variables, all-same-variable clauses
    shapes += [(3, [[(0, True), (0, True), (0, False)]]),
               (4, [[(1, False), (1, False), (1, False)]]),
               (2, [[(0, True), (0, True), (0, True)],
                    [(0, True), (0, False), (0, False)]]),
               (1, [[(0, True), (0, True), (0, False)],
                    [(0, False), (0, False), (0, True)],
                    [(0, True), (0, True), (0, True)]])]
    # random, bounded so |S| = 1+2n+3m <= 18
    while len(shapes) < 400:
        n = rng.randint(1, 4)
        m = rng.randint(1, 3)
        if 1 + 2 * n + 3 * m > 18:
            continue
        shapes.append((n, [[(rng.randrange(n), rng.random() < .5)
                            for _ in range(3)] for _ in range(m)]))

    t0 = time.time()
    bad12 = bad23 = 0
    unsat = 0
    for n, cls in shapes:
        g = build_guarded_graph(n, cls)
        sat = formula_sat(n, cls)
        if not sat:
            unsat += 1
        b = Bprime_on_graph(g) is not None
        X, groups, zadj = island_from_graph(g)
        isl = island_solve(X, groups, zadj) is not None
        if sat != b:
            bad12 += 1
            print(f"*** sections5-6 MISMATCH sat={sat} B'={b} n={n} cls={cls}")
        if b != isl:
            bad23 += 1
            print(f"*** Lemma D MISMATCH B'={b} ISLAND={isl} n={n} cls={cls}")
    print(f"instances={len(shapes)} ({unsat} UNSAT)  "
          f"SAT-vs-B' mismatches={bad12}  B'-vs-ISLAND mismatches={bad23}  "
          f"({time.time()-t0:.0f}s)")
    return 1 if (bad12 or bad23) else 0


if __name__ == "__main__":
    sys.exit(main())
