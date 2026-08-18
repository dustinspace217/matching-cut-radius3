#!/usr/bin/env python3
"""Block 9: test Sol's reduction AT THE SET LEVEL.

Block 8 refuted the GRAPH-level claim (spurious matching cuts — all of
them, per the defect taxonomy, colourings where an L1 vertex turns blue,
i.e. case B). The SET problem is case A only, so those leaks cannot exist
here by definition. This tests the surviving sub-claim:

  CANDIDATE LEMMA: signed NOT-1-IN-3-SAT formula F is satisfiable
  IFF the derived witness-group island instance is YES.

Construction (Sol's, at set level):
  X: anchor a (private); t_i, f_i per variable (SHARED group {t_i,f_i});
     occurrence proxy p_{C,j} per clause position (private).
  Z: gate g_i ~ (a, t_i, f_i);
     copies c_{C,j,0}, c_{C,j,1} each ~ (base literal of position, p_{C,j});
     clause z_C ~ (p_{C,0}, p_{C,1}, p_{C,2}).

Intended semantics: any nonempty B pulls in a (via a gate); a + gates
force exactly one of t_i/f_i per variable (assignment); double copies
force proxy <-> base; z_C allows selected-proxy counts {0,2,3} = clause
is NOT-1-IN-3 satisfied. Reverse: every solution reads off a satisfying
assignment.

Test: same 400-formula battery as the graph-level refuter (same seed,
same generator) PLUS exhaustive single/double-clause formulas, comparing
brute-force SAT against brute-force set-problem decision. Any mismatch
in either direction falsifies the lemma at the set level too.
"""

import sys
from itertools import product

sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
from set_problem import solve_bruteforce
from verify_sol_reduction import formula_sat, random_formula
import random


def build_set_instance(n, clauses):
    """Formula -> (groups, zadj) in set_problem format."""
    groups = [("a",)]
    zadj = {}
    for i in range(n):
        groups.append((f"t{i}", f"f{i}"))          # shared witness q_i
        zadj[f"g{i}"] = ("a", f"t{i}", f"f{i}")     # variable gate
    for ci, cl in enumerate(clauses):
        occ = []
        for j, (vi, sign) in enumerate(cl):
            p = f"p_{ci}_{j}"
            groups.append((p,))                     # private witness
            base = f"t{vi}" if sign else f"f{vi}"
            for k in (0, 1):                        # equality copies
                zadj[f"c_{ci}_{j}_{k}"] = (base, p)
            occ.append(p)
        zadj[f"z{ci}"] = tuple(occ)                 # clause vertex
    return groups, zadj


def check(n, clauses):
    sat = formula_sat(n, clauses)
    groups, zadj = build_set_instance(n, clauses)
    B = solve_bruteforce(groups, zadj)
    return sat, (B is not None), B


def main():
    mism = 0
    tested = 0

    # exhaustive: every single clause over n<=3 variables (all sign
    # patterns, all variable tuples incl. repeats)
    for n in (1, 2, 3):
        for vis in product(range(n), repeat=3):
            for signs in product((True, False), repeat=3):
                cl = [list(zip(vis, signs))]
                sat, yes, B = check(n, cl)
                tested += 1
                if sat != yes:
                    mism += 1
                    if mism <= 5:
                        print(f"MISMATCH(exh1) sat={sat} set={yes} "
                              f"n={n} cl={cl} B={B}")
    # exhaustive-ish: pairs of clauses over 2 variables
    for vis1 in product(range(2), repeat=3):
        for s1 in product((True, False), repeat=3):
            for vis2 in product(range(2), repeat=3):
                for s2 in product((True, False), repeat=3):
                    cls = [list(zip(vis1, s1)), list(zip(vis2, s2))]
                    sat, yes, B = check(2, cls)
                    tested += 1
                    if sat != yes:
                        mism += 1
                        if mism <= 5:
                            print(f"MISMATCH(exh2) sat={sat} set={yes} "
                                  f"cls={cls} B={B}")

    # the same random battery the graph-level refuter used
    rng = random.Random(2026)
    for _ in range(400):
        n = rng.randint(1, 3)
        m = rng.randint(1, 3)
        clauses = random_formula(rng, n, m)
        sat, yes, B = check(n, clauses)
        tested += 1
        if sat != yes:
            mism += 1
            if mism <= 5:
                print(f"MISMATCH(rand) sat={sat} set={yes} "
                      f"n={n} cls={clauses} B={B}")

    print(f"tested {tested}; mismatches {mism}")
    return 1 if mism else 0


if __name__ == "__main__":
    sys.exit(main())
