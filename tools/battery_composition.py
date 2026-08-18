#!/usr/bin/env python3
"""Sanity check: how many SAT vs UNSAT formulas did the set-level
equivalence battery (sol_set_reduction.py) actually contain? A battery
that was accidentally all-SAT (or all-UNSAT) would make '0 mismatches'
vacuous in one direction."""

import sys
import random
from itertools import product

sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
from verify_sol_reduction import formula_sat, random_formula

sat_n = unsat_n = 0
for n in (1, 2, 3):
    for vis in product(range(n), repeat=3):
        for signs in product((True, False), repeat=3):
            cl = [list(zip(vis, signs))]
            if formula_sat(n, cl):
                sat_n += 1
            else:
                unsat_n += 1
for vis1 in product(range(2), repeat=3):
    for s1 in product((True, False), repeat=3):
        for vis2 in product(range(2), repeat=3):
            for s2 in product((True, False), repeat=3):
                cls = [list(zip(vis1, s1)), list(zip(vis2, s2))]
                if formula_sat(2, cls):
                    sat_n += 1
                else:
                    unsat_n += 1
rng = random.Random(2026)
for _ in range(400):
    n = rng.randint(1, 3)
    m = rng.randint(1, 3)
    cls = random_formula(rng, n, m)
    if formula_sat(n, cls):
        sat_n += 1
    else:
        unsat_n += 1
print(f"battery composition: SAT={sat_n} UNSAT={unsat_n}")
