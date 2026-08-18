#!/usr/bin/env python3
"""Scale Lemma 9A far past the published battery (n<=3, m<=3), and hit
the degenerate shapes the published generator can never produce:
variables occurring in no clause, m=0, single-variable formulas,
clauses with repeated literals of both signs."""
import sys, random, time
from itertools import product
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
sys.path.insert(0, "/tmp/claude/pvnp")
from verify_sol_reduction import formula_sat
from sol_set_reduction import build_set_instance
from island_sat import island_yes


def check(n, clauses):
    return formula_sat(n, clauses), island_yes(*build_set_instance(n, clauses)) is not None


def rand_formula_free(rng, n, m):
    """Unlike tools/verify_sol_reduction.random_formula, this does NOT
    sample distinct variables per clause, so variables can go unused and
    clauses can repeat a variable in all three positions."""
    return [[(rng.randrange(n), rng.random() < 0.5) for _ in range(3)]
            for _ in range(m)]


t0 = time.time()
mism = 0
tested = 0
nun = 0

# 0. m = 0 (no clauses) for n = 0..4
for n in range(0, 5):
    s, y = check(n, [])
    tested += 1
    if s != y:
        mism += 1; print(f"MISMATCH m=0 n={n} sat={s} island={y}")

# 1. exhaustive 2-clause formulas over n=1 and n=2 (all repeats/signs)
for n in (1, 2):
    for v1 in product(range(n), repeat=3):
        for s1 in product((True, False), repeat=3):
            for v2 in product(range(n), repeat=3):
                for s2 in product((True, False), repeat=3):
                    cls = [list(zip(v1, s1)), list(zip(v2, s2))]
                    s, y = check(n, cls)
                    tested += 1; nun += (not s)
                    if s != y:
                        mism += 1
                        if mism <= 5:
                            print(f"MISMATCH exh2 n={n} sat={s} island={y} "
                                  f"cls={cls}")
print(f"  after exhaustive-2clause: tested={tested} unsat={nun} mism={mism} "
      f"{time.time()-t0:.1f}s")

# 2. exhaustive 3-clause formulas over n=1 (all sign patterns)
for s1 in product((True, False), repeat=3):
    for s2 in product((True, False), repeat=3):
        for s3 in product((True, False), repeat=3):
            cls = [[(0, x) for x in s1], [(0, x) for x in s2],
                   [(0, x) for x in s3]]
            s, y = check(1, cls)
            tested += 1; nun += (not s)
            if s != y:
                mism += 1; print(f"MISMATCH exh3 sat={s} island={y} {cls}")

# 3. large random, unrestricted variable choice (unused vars possible)
rng = random.Random(4242)
for _ in range(4000):
    n = rng.randint(1, 6)
    m = rng.randint(1, 8)
    cls = rand_formula_free(rng, n, m)
    s, y = check(n, cls)
    tested += 1; nun += (not s)
    if s != y:
        mism += 1
        if mism <= 10:
            print(f"MISMATCH rand n={n} m={m} sat={s} island={y} cls={cls}")

print(f"TOTAL tested={tested} UNSAT={nun} mismatches={mism} "
      f"{time.time()-t0:.1f}s")
sys.exit(1 if mism else 0)
