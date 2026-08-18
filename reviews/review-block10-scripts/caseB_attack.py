#!/usr/bin/env python3
"""Adversarial audit C: try to CONSTRUCT a valid case-B colouring of a
real guarded graph, and check the prior review's 9-vertex graph against
Lemma B' as written in the new document.

Case B search: u red, one chosen L1 vertex b blue, every other L1 vertex
red; exhaustive backtracking over L2 u L3 for a valid completion. Any
completion found REFUTES Claim 4.4. Run for EVERY choice of b on several
instances, including UNSAT formulas.

Also re-derives, per instance and per b, the document's forced chain
(guards red by Claim 4.3, Zk blue, >=2 crosses at Zk) so a mismatch
between "the prose says contradiction at Zk" and "the search says no
completion" would be visible.
"""
import sys, random, itertools
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
from guarded_reduction import build_guarded_graph
from mc_check import make_graph, distances_from, eccentricity
from verify_sol_reduction import formula_sat


def complete(g, pinned):
    """Exhaustive backtracking: is there a valid colouring extending
    `pinned` (both colours already present among pins)? Returns a
    colouring or None. Prunes on the <=1-cross invariant."""
    col = dict(pinned)
    free = [v for v in sorted(g, key=repr) if v not in col]
    # order free vertices by adjacency to already-pinned ones (better pruning)
    free.sort(key=lambda v: -len(set(g[v]) & set(col)))

    def cross(v):
        return sum(1 for w in g[v] if w in col and col[w] != col[v])

    def ok_local(v):
        if cross(v) > 1:
            return False
        for w in g[v]:
            if w in col and cross(w) > 1:
                return False
        return True

    for v in list(col):
        if cross(v) > 1:
            return None

    def rec(i):
        if i == len(free):
            return dict(col)
        v = free[i]
        for c in ("R", "B"):
            col[v] = c
            if ok_local(v):
                r = rec(i + 1)
                if r is not None:
                    return r
            del col[v]
        return None

    return rec(0)


def caseB_scan(n, clauses, verbose=False):
    g = build_guarded_graph(n, clauses)
    d = distances_from(g, "u")
    L1 = {v for v in g if d[v] == 1}
    survivors = []
    for b in sorted(L1, key=repr):
        pinned = {"u": "R"}
        for w in L1:
            pinned[w] = "B" if w == b else "R"
        r = complete(g, pinned)
        if r is not None:
            survivors.append((b, r))
    return g, sorted(L1, key=repr), survivors


def forced_chain_check(n, clauses):
    """Independent re-derivation of the prose's forced chain, per b."""
    g = build_guarded_graph(n, clauses)
    d = distances_from(g, "u")
    L1 = {v for v in g if d[v] == 1}
    L2 = {v for v in g if d[v] == 2}
    bad = []
    for b in sorted(L1, key=repr):
        # Claim 4.3: every L2 vertex with two L1 nbrs, neither of them b, is red
        red_L2 = {v for v in L2
                  if len(set(g[v]) & L1) == 2 and b not in g[v]}
        # b's other neighbours forced blue
        forced_blue = set(g[b]) - {"u"}
        # each forced-blue L2 vertex v: its red L1 witnesses count
        for v in forced_blue:
            redwit = [w for w in set(g[v]) & L1 if w != b]
            if len(redwit) != 1:
                bad.append(f"{b}: forced-blue {v} has {len(redwit)} red witnesses")
                continue
            # budget consumed -> all L3 nbrs of v blue
            l3 = set(g[v]) - L1
            for z in l3:
                # z blue; count its red nbrs (in red_L2)
                reds = [x for x in g[z] if x in red_L2]
                if len(reds) < 2:
                    bad.append(f"{b}: blue {z} has only {len(reds)} pinned-red "
                               f"nbrs -> prose chain incomplete")
    return bad


def nine_vertex():
    E = [("u","w1"),("u","w2"),("u","w3"),("u","w4"),
         ("w1","v"),("w2","y1"),("w3","y1"),("w3","y2"),("w4","y2"),
         ("z","v"),("z","y1"),("z","y2")]
    g = make_graph(E)
    sys.path.insert(0, "/tmp/claude/pvnp2")
    from lemmaB_attack import layers, truth_A1, sets_Bprime
    print("9-vertex graph: ecc(u) =", eccentricity(g, "u"),
          " radius =", min(eccentricity(g, x) for x in g))
    L1, L2, L3 = layers(g, "u")
    print("  L1", sorted(L1), "L2", sorted(L2), "L3", sorted(L3))
    t = truth_A1(g, "u", L1, L2)
    s = sets_Bprime(g, "u", L1, L2, L3)
    print("  ground-truth case-A1 exists:", t is not None)
    print("  document Lemma B' says:", s is not None, s)
    print("  --> B' AGREES (not a counterexample to the corrected lemma)"
          if (t is not None) == (s is not None) else
          "  *** B' REFUTED ON THE PRIOR REVIEW'S GRAPH ***")


def main():
    nine_vertex()
    print()
    rng = random.Random(31337)
    shapes = []
    # every n=1 single-clause sign pattern (all SAT), plus n=1 two-clause
    for signs in itertools.product((True, False), repeat=3):
        shapes.append((1, [list(zip((0,0,0), signs))]))
    for s1 in itertools.product((True, False), repeat=3):
        for s2 in itertools.product((True, False), repeat=3):
            shapes.append((1, [list(zip((0,0,0), s1)), list(zip((0,0,0), s2))]))
    # n=2 assorted incl. UNSAT-hunting
    for _ in range(60):
        n = rng.randint(1, 2)
        m = rng.randint(1, 3)
        shapes.append((n, [[(rng.randrange(n), rng.random() < .5)
                            for _ in range(3)] for _ in range(m)]))
    tot = surv = unsat = 0
    chain_bad = []
    for n, cls in shapes:
        sat = formula_sat(n, cls)
        if not sat:
            unsat += 1
        g, L1, s = caseB_scan(n, cls)
        tot += 1
        if s:
            surv += 1
            print(f"*** CASE-B SURVIVOR n={n} cls={cls} b={s[0][0]}")
        chain_bad += forced_chain_check(n, cls)
    print(f"case-B exhaustive completion search: {tot} instances "
          f"({unsat} UNSAT), all L1 choices of b each; survivors={surv}")
    print(f"prose forced-chain re-derivation defects: {len(chain_bad)}")
    for x in chain_bad[:10]:
        print("   ", x)
    return 1 if (surv or chain_bad) else 0


if __name__ == "__main__":
    sys.exit(main())
