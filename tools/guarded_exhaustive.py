#!/usr/bin/env python3
"""Exhaustive companion to guarded_reduction.py: every single-clause
formula over n <= 2 variables (all variable tuples incl. repeats, all
sign patterns), graph-level, independent oracle. Complements the random
battery with systematic coverage of the degenerate shapes (repeated
literals, all-same-variable clauses) where constructions usually break."""

import sys
from itertools import product

sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
from mc_check import is_bipartite, eccentricity, distances_from
from independent_mc import has_matching_cut
from verify_sol_reduction import formula_sat
from guarded_reduction import build_guarded_graph

tested = mism = 0
for n in (1, 2):
    for vis in product(range(n), repeat=3):
        for signs in product((True, False), repeat=3):
            clauses = [list(zip(vis, signs))]
            g = build_guarded_graph(n, clauses)
            assert is_bipartite(g)[0]
            assert len(distances_from(g, "u")) == len(g)
            assert min(eccentricity(g, v) for v in g) == 3
            sat = formula_sat(n, clauses)
            mc = has_matching_cut(g, budget=50_000_000)
            tested += 1
            if sat != mc:
                mism += 1
                print(f"MISMATCH sat={sat} mc={mc} n={n} cl={clauses}")
print(f"exhaustive single-clause: tested {tested}; mismatches {mism}")
sys.exit(1 if mism else 0)
