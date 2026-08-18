#!/usr/bin/env python3
"""Audit E2: UNSAT-heavy version of the bridge attack, fresh seed.
Only formulas that are UNSAT (the direction a broken reduction leaks in)
plus degenerate shapes the project's own generator cannot produce
(unused variables, all-same-variable clauses, contradictory pairs).
"""
import sys, random, time
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
sys.path.insert(0, "/tmp/claude/pvnp2")
from guarded_reduction import build_guarded_graph
from verify_sol_reduction import formula_sat
from bridge_attack import Bprime_on_graph, island_from_graph, island_solve


def main(target=300, seed=2718281):
    rng = random.Random(seed)
    got = 0
    tries = 0
    bad12 = bad23 = 0
    t0 = time.time()
    while got < target and tries < 400000:
        tries += 1
        n = rng.randint(1, 4)
        m = rng.randint(2, 4)
        if 1 + 2 * n + 3 * m > 19:
            continue
        cls = [[(rng.randrange(n), rng.random() < .5) for _ in range(3)]
               for _ in range(m)]
        if formula_sat(n, cls):
            continue
        got += 1
        g = build_guarded_graph(n, cls)
        b = Bprime_on_graph(g) is not None
        X, groups, zadj = island_from_graph(g)
        isl = island_solve(X, groups, zadj) is not None
        if b:
            bad12 += 1
            print(f"*** SPURIOUS case-A1 on UNSAT n={n} cls={cls}")
        if b != isl:
            bad23 += 1
            print(f"*** Lemma D MISMATCH n={n} cls={cls}")
    print(f"UNSAT-only instances={got} (from {tries} draws)  "
          f"spurious case-A1={bad12}  LemmaD mismatches={bad23}  "
          f"({time.time()-t0:.0f}s)")
    return 1 if (bad12 or bad23) else 0


if __name__ == "__main__":
    sys.exit(main(*[int(x) for x in sys.argv[1:]]))
