#!/usr/bin/env python3
import sys, time, itertools, random
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
sys.path.insert(0, "/tmp/claude/pvnp")
from mc_check import is_bipartite, eccentricity, distances_from
from independent_mc import has_matching_cut
from verify_sol_reduction import formula_sat, random_formula
from guarded_reduction import build_guarded_graph
from decomp import analyse

def run(n, clauses, cross_check=False, verbose=True):
    g = build_guarded_graph(n, clauses)
    assert is_bipartite(g)[0]
    r = min(eccentricity(g, v) for v in g)
    sat = formula_sat(n, clauses)
    if verbose:
        print(f"n={n} m={len(clauses)} sat={sat} radius={r} cl={clauses}")
    a1, a0, b = analyse(g, verbose=verbose)
    mc_decomp = bool(a1) or bool(a0) or bool(b)
    ver = None
    if cross_check:
        try:
            ver = has_matching_cut(g, budget=60_000_000)
        except TimeoutError:
            ver = "TIMEOUT"
    return sat, mc_decomp, bool(a1), bool(a0), bool(b), ver

if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "validate"
    if mode == "validate":
        # small instances where the independent oracle still terminates
        bad = 0
        for n in (1,):
            for vis in itertools.product(range(n), repeat=3):
                for signs in itertools.product((True, False), repeat=3):
                    cl = [list(zip(vis, signs))]
                    sat, md, a1, a0, b, ver = run(n, cl, cross_check=True,
                                                  verbose=False)
                    tag = ""
                    if ver != "TIMEOUT" and ver != md:
                        tag = "  <-- DECOMP DISAGREES WITH ORACLE"
                        bad += 1
                    print(f"n={n} cl={cl} sat={sat} decomp={md} "
                          f"(A1={a1},A0={a0},B={b}) oracle={ver}{tag}")
        print("decomp-vs-oracle disagreements:", bad)
    elif mode == "battery":
        rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 7)
        t0 = time.time(); tested = mism = nun = 0
        rows = []
        for _ in range(int(sys.argv[3]) if len(sys.argv) > 3 else 60):
            n = rng.randint(1, 3); m = rng.randint(1, 3)
            cl = random_formula(rng, n, m)
            sat, md, a1, a0, b, _ = run(n, cl, verbose=False)
            tested += 1; nun += (not sat)
            if sat != md:
                mism += 1
                print(f"MISMATCH sat={sat} decomp={md} A1={a1} A0={a0} "
                      f"B={b} n={n} cl={cl}")
            if b:
                print(f"CASE-B SURVIVOR n={n} cl={cl}")
        print(f"tested {tested} (UNSAT={nun}); mismatches {mism}; "
              f"{time.time()-t0:.1f}s")
