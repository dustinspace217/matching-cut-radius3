#!/usr/bin/env python3
"""Adversarial audit D: fresh end-to-end battery.

Builds the real guarded graph, decides matching-cut existence with the
THEORY-FREE independent oracle, and compares with brute-force SAT of the
source formula. Fresh seed (never used in this project: 8675309).
Deliberately over-weights UNSAT instances -- the direction that killed
the Block-8 construction.
"""
import sys, random, itertools, time
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
from guarded_reduction import build_guarded_graph
from independent_mc import has_matching_cut
from mc_check import is_bipartite, distances_from, eccentricity
from verify_sol_reduction import formula_sat


def run(shapes, budget, label):
    t0 = time.time()
    tested = mism = to = unsat = 0
    for n, cls in shapes:
        g = build_guarded_graph(n, cls)
        assert is_bipartite(g)[0]
        assert len(distances_from(g, "u")) == len(g)
        assert min(eccentricity(g, v) for v in g) == 3
        sat = formula_sat(n, cls)
        if not sat:
            unsat += 1
        try:
            mc = has_matching_cut(g, budget=budget)
        except TimeoutError:
            to += 1
            continue
        tested += 1
        if sat != mc:
            mism += 1
            print(f"*** MISMATCH sat={sat} mc={mc} n={n} cls={cls} "
                  f"|V|={len(g)}")
    print(f"[{label}] tested={tested} UNSAT-in-set={unsat} mismatches={mism} "
          f"timeouts={to}  ({time.time()-t0:.0f}s)")
    return mism


def unsat_n1_m2():
    """All 18 UNSAT n=1 two-clause formulas (forces-1 x forces-0, both
    orders)."""
    force1 = [s for s in itertools.product((True, False), repeat=3)
              if sum(s) == 2]
    force0 = [s for s in itertools.product((True, False), repeat=3)
              if sum(s) == 1]
    out = []
    for a in force1:
        for b in force0:
            out.append((1, [list(zip((0, 0, 0), a)), list(zip((0, 0, 0), b))]))
            out.append((1, [list(zip((0, 0, 0), b)), list(zip((0, 0, 0), a))]))
    return out


def main():
    rng = random.Random(8675309)
    # 1) fresh random battery, n<=2 m<=2 (oracle-feasible)
    rand = []
    while len(rand) < 120:
        n = rng.randint(1, 2)
        m = rng.randint(1, 2)
        cls = [[(rng.randrange(n), rng.random() < .5) for _ in range(3)]
               for _ in range(m)]
        rand.append((n, cls))
    bad = run(rand, 40_000_000, "fresh random n<=2 m<=2")

    # 2) every UNSAT n=1 two-clause instance (36 incl. both orders)
    bad += run(unsat_n1_m2(), 60_000_000, "ALL UNSAT n=1 m=2")

    # 3) UNSAT-focused n=2 m=2 sample (|V|=62) -- beyond prior oracle coverage
    uns = []
    tries = 0
    while len(uns) < 25 and tries < 20000:
        tries += 1
        cls = [[(rng.randrange(2), rng.random() < .5) for _ in range(3)]
               for _ in range(2)]
        if not formula_sat(2, cls):
            uns.append((2, cls))
    bad += run(uns, 200_000_000, "UNSAT-focused n=2 m=2 (|V|=62)")
    print("TOTAL MISMATCHES:", bad)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
