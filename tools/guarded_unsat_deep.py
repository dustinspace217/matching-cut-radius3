#!/usr/bin/env python3
"""Deep UNSAT coverage for the guarded reduction, closing the timeout
gap from guarded_unsat_battery.py. For each rejection-sampled UNSAT
formula, decide matching-cut existence TWICE:
  1. exact_layered.decide — the fast center-branch DPLL (validated
     0 errors / ~59k instances across Blocks 6-8), generous split budget;
  2. independent_mc — the slow plain backtracker, generous node budget.
Record agreement. A 'no-cut' verdict counts as fully verified only when
BOTH solvers complete and agree; DPLL-only verdicts are reported
separately (evidence, one instrument). Any disagreement or any spurious
cut is a failure loudly reported."""

import sys
import random

sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
from mc_check import is_bipartite, distances_from
from independent_mc import has_matching_cut
from verify_sol_reduction import formula_sat, random_formula
from guarded_reduction import build_guarded_graph
from exact_layered import decide

target = int(sys.argv[1]) if len(sys.argv) > 1 else 60
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 555
n_hi = int(sys.argv[3]) if len(sys.argv) > 3 else 3
m_hi = int(sys.argv[4]) if len(sys.argv) > 4 else 3

rng = random.Random(seed)
both_ok = dpll_only = spurious = disagree = neither = 0
attempts = 0
while (both_ok + dpll_only + neither) < target and attempts < 500_000:
    attempts += 1
    n = rng.randint(1, n_hi)
    m = rng.randint(1, m_hi)
    clauses = random_formula(rng, n, m)
    if formula_sat(n, clauses):
        continue
    g = build_guarded_graph(n, clauses)
    assert is_bipartite(g)[0]
    assert len(distances_from(g, "u")) == len(g)
    try:
        mc_dpll, _ = decide(g, budget=2_000_000)
    except TimeoutError:
        mc_dpll = None
    try:
        mc_ind = has_matching_cut(g, budget=200_000_000)
    except TimeoutError:
        mc_ind = None
    if mc_dpll is True or mc_ind is True:
        spurious += 1
        print(f"SPURIOUS CUT on UNSAT: n={n} m={m} clauses={clauses} "
              f"dpll={mc_dpll} ind={mc_ind}")
    elif mc_dpll is False and mc_ind is False:
        both_ok += 1
    elif mc_dpll is False and mc_ind is None:
        dpll_only += 1
    elif mc_dpll is None and mc_ind is False:
        dpll_only += 1  # one complete instrument said no-cut
    else:
        neither += 1
    if mc_dpll is not None and mc_ind is not None and mc_dpll != mc_ind:
        disagree += 1
        print(f"INSTRUMENT DISAGREEMENT: n={n} clauses={clauses} "
              f"dpll={mc_dpll} ind={mc_ind}")
print(f"deep UNSAT: both-verified {both_ok}; single-instrument "
      f"{dpll_only}; neither {neither}; spurious {spurious}; "
      f"disagreements {disagree}; attempts {attempts}")
sys.exit(1 if (spurious or disagree) else 0)
