#!/usr/bin/env python3
"""Scaled adversarial test of the GUARDED reduction via exact case
decomposition. Validates fast A1 against decomp's brute force first."""
import sys, random, time
from itertools import product
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
sys.path.insert(0, "/tmp/claude/pvnp")
from verify_sol_reduction import formula_sat
from guarded_reduction import build_guarded_graph
from decomp import layers, caseA1, caseA0, caseB
from fast_a1 import caseA1_fast


def rand_free(rng, n, m):
    return [[(rng.randrange(n), rng.random() < 0.5) for _ in range(3)]
            for _ in range(m)]


mode = sys.argv[1] if len(sys.argv) > 1 else "validate"

if mode == "validate":
    rng = random.Random(99)
    bad = 0
    for _ in range(120):
        n = rng.randint(1, 2); m = rng.randint(1, 2)
        cl = rand_free(rng, n, m)
        g = build_guarded_graph(n, cl)
        L1, L2, L3 = layers(g)
        slow = caseA1(g, L1, L2, L3) is not None
        fast = caseA1_fast(g, L1, L2, L3) is not None
        if slow != fast:
            bad += 1
            print("A1 DISAGREE", n, cl, slow, fast)
    print("fast-A1 vs brute-force-A1 disagreements:", bad)

elif mode == "battery":
    seed = int(sys.argv[2]); rounds = int(sys.argv[3])
    nmax = int(sys.argv[4]); mmax = int(sys.argv[5])
    rng = random.Random(seed)
    t0 = time.time(); tested = mism = nun = 0
    bsurv = 0
    for _ in range(rounds):
        n = rng.randint(1, nmax); m = rng.randint(1, mmax)
        cl = rand_free(rng, n, m)
        g = build_guarded_graph(n, cl)
        L1, L2, L3 = layers(g)
        a1 = caseA1_fast(g, L1, L2, L3) is not None
        a0 = bool(caseA0(g, L3))
        b = caseB(g, L1)
        mc = a1 or a0 or bool(b)
        sat = formula_sat(n, cl)
        tested += 1; nun += (not sat)
        if b:
            bsurv += 1
            print(f"CASE-B SURVIVOR n={n} cl={cl} b={[x[0] for x in b]}")
        if a0:
            print(f"CASE-A0 ALIVE n={n} cl={cl}")
        if sat != mc:
            mism += 1
            print(f"MISMATCH sat={sat} mc={mc} A1={a1} A0={a0} "
                  f"B={bool(b)} n={n} m={m} |V|={len(g)} cl={cl}")
    print(f"tested {tested} (UNSAT={nun}); mismatches {mism}; "
          f"caseB survivors {bsurv}; {time.time()-t0:.1f}s")
