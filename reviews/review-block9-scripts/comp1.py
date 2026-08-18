#!/usr/bin/env python3
"""Composition of the two guarded batteries: how many UNSAT instances?"""
import sys, random
from itertools import product
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
from verify_sol_reduction import formula_sat, random_formula

# guarded_exhaustive.py battery
sat_c = unsat_c = 0
for n in (1, 2):
    for vis in product(range(n), repeat=3):
        for signs in product((True, False), repeat=3):
            clauses = [list(zip(vis, signs))]
            if formula_sat(n, clauses): sat_c += 1
            else: unsat_c += 1
print(f"guarded_exhaustive battery: SAT={sat_c} UNSAT={unsat_c}")

# guarded_reduction.main default battery: n in [1,2], m in [1,2], 200 rounds seed 2026
rng = random.Random(2026)
sat_c = unsat_c = 0
sizes = []
for _ in range(200):
    n = rng.randint(1, 2)
    m = rng.randint(1, 2)
    clauses = random_formula(rng, n, m)
    if formula_sat(n, clauses): sat_c += 1
    else: unsat_c += 1
print(f"guarded_reduction default battery: SAT={sat_c} UNSAT={unsat_c}")
