#!/usr/bin/env python3
"""Adversarial audit C2: re-derive Claim 4.4's forced chain EXACTLY as the
document argues it, per instance and per choice of b, and confirm the
contradiction lands where the prose says it lands (>=2 crosses at Zk).

Document's chain (all three branches):
  b blue, u red -> every other neighbour of b is blue.
  The double-witnessed neighbour of b (a guard G_W, or a ballast T)
  becomes blue; its OTHER witness is red and consumes its budget;
  therefore its remaining neighbour Zk is blue.
  Every other double-witnessed L2 vertex has both witnesses != b, so is
  RED by Claim 4.3.  Zk blue then has >=2 red neighbours.
"""
import sys, random, itertools
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
from guarded_reduction import build_guarded_graph
from mc_check import distances_from
from verify_sol_reduction import formula_sat

bad = []

def check(n, clauses):
    ctx = f"n={n} cls={clauses}"
    g = build_guarded_graph(n, clauses)
    d = distances_from(g, "u")
    L1 = {v for v in g if d[v] == 1}
    L2 = {v for v in g if d[v] == 2}
    L3 = {v for v in g if d[v] == 3}
    dbl = {v for v in L2 if len(set(g[v]) & L1) == 2}   # guards + ballast
    for b in sorted(L1, key=repr):
        forced_blue = set(g[b]) - {"u"}
        # the prose's chain runs through the double-witnessed forced-blue
        # vertices; there must be at least one, else the branch is unargued
        pivots = forced_blue & dbl
        if not pivots:
            bad.append(f"{ctx}: b={b} has NO double-witnessed forced-blue "
                       f"neighbour -- prose branch has no pivot")
            continue
        for v in pivots:
            other = [w for w in set(g[v]) & L1 if w != b]
            if len(other) != 1:
                bad.append(f"{ctx}: b={b} pivot {v} has {len(other)} other "
                           f"witnesses (prose assumes exactly 1)")
                continue
            rest = set(g[v]) - L1
            if rest != {"Zk"}:
                bad.append(f"{ctx}: b={b} pivot {v} non-L1 nbrs {sorted(rest)}"
                           f" != {{Zk}}")
                continue
            # Zk forced blue; count vertices RED by Claim 4.3 among N(Zk)
            reds = [x for x in g["Zk"]
                    if x in dbl and b not in g[x]]
            if len(reds) < 2:
                bad.append(f"{ctx}: b={b} pivot {v}: Zk has only {len(reds)} "
                           f"Claim-4.3-red neighbours -- no contradiction")
            # and confirm Zk itself is in L3 with all nbrs in L2
            if not set(g["Zk"]) <= L2:
                bad.append(f"{ctx}: Zk has non-L2 neighbour")


def main():
    rng = random.Random(600613)
    shapes = []
    for signs in itertools.product((True, False), repeat=3):
        shapes.append((1, [list(zip((0, 0, 0), signs))]))
    for vis in itertools.product(range(2), repeat=3):
        for signs in itertools.product((True, False), repeat=3):
            shapes.append((2, [list(zip(vis, signs))]))
    shapes.append((4, [[(0, True), (0, True), (0, True)]]))   # unused vars
    for _ in range(300):
        n = rng.randint(1, 6)
        m = rng.randint(1, 6)
        shapes.append((n, [[(rng.randrange(n), rng.random() < .5)
                            for _ in range(3)] for _ in range(m)]))
    for n, cls in shapes:
        check(n, cls)
    print(f"chain re-derivation over {len(shapes)} instances x all b: "
          f"defects={len(bad)}")
    for x in bad[:15]:
        print("   ", x)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
