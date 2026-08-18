#!/usr/bin/env python3
"""Adversarial audit F: theory-free oracle pushed past prior coverage.

Prior best theory-free slice (earlier review): all 64 n=1 two-clause
guarded graphs, |V|=56. Here: n=1 THREE-clause guarded graphs, |V|=75,
UNSAT-first (the direction that killed Block 8), then SAT ones.
Prints one line per instance so partial progress is usable.
"""
import sys, time, itertools
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
from guarded_reduction import build_guarded_graph
from independent_mc import has_matching_cut
from mc_check import is_bipartite, distances_from, eccentricity
from verify_sol_reduction import formula_sat

SIGNS = list(itertools.product((True, False), repeat=3))


def main(budget=2_000_000_000):
    formulas = []
    for a in SIGNS:
        for b in SIGNS:
            for c in SIGNS:
                cls = [list(zip((0, 0, 0), s)) for s in (a, b, c)]
                formulas.append(cls)
    unsat = [f for f in formulas if not formula_sat(1, f)]
    sat = [f for f in formulas if formula_sat(1, f)]
    print(f"n=1 m=3: {len(formulas)} formulas, {len(unsat)} UNSAT", flush=True)
    order = unsat + sat[:40]
    done = mism = to = 0
    t0 = time.time()
    for cls in order:
        g = build_guarded_graph(1, cls)
        assert is_bipartite(g)[0]
        assert len(distances_from(g, "u")) == len(g)
        assert min(eccentricity(g, v) for v in g) == 3
        s = formula_sat(1, cls)
        t1 = time.time()
        try:
            mc = has_matching_cut(g, budget=budget)
        except TimeoutError:
            to += 1
            print(f"TIMEOUT |V|={len(g)} sat={s}", flush=True)
            continue
        done += 1
        tag = "OK " if s == mc else "*** MISMATCH ***"
        if s != mc:
            mism += 1
        print(f"{tag} |V|={len(g)} sat={s} mc={mc} "
              f"{time.time()-t1:.1f}s  (done={done} mism={mism} to={to} "
              f"total={time.time()-t0:.0f}s)", flush=True)
    print(f"FINAL done={done} mismatches={mism} timeouts={to}", flush=True)
    return 1 if mism else 0


if __name__ == "__main__":
    sys.exit(main())
