#!/usr/bin/env python3
"""Block 9 step 1: full taxonomy of the spurious cuts in Sol's reduction.

Reruns the same 400-formula battery as verify_sol_reduction.py (same seed,
same generator, so the same 50 mismatches reappear), and for every
mismatch extracts an ACTUAL witness colouring from an exhaustive search,
then classifies the defect: which vertex classes sit on the minority side.

Why: the hand-checked counterexample (center u defects with its degree-2
witness leaves) is ONE defect shape; a repair designed against one shape
can miss others. Repair design needs the complete list.

Output: one line per mismatch with (n, m, minority-side vertex classes),
plus an aggregated shape census at the end. Written for one-shot run;
results land in scratch/ via shell redirect.
"""

import sys
import random
from collections import Counter

sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
from mc_check import make_graph, is_bipartite, eccentricity, distances_from
from verify_sol_reduction import build_graph, formula_sat, random_formula


def mc_witness(g):
    """Exhaustive backtracking, same pruning as independent_mc, but
    returns a witness colouring dict (or None). Kept separate from the
    validated oracle so that instrument stays untouched."""
    verts = sorted(g, key=repr)
    n = len(verts)
    col = {}

    def rec(i):
        if i == n:
            return len(set(col.values())) == 2
        v = verts[i]
        for c in ("R", "B"):
            col[v] = c
            ok = sum(1 for w in g[v] if w in col and col[w] != c) <= 1
            if ok:
                bad = False
                for w in g[v]:
                    if w in col and col[w] != c:
                        cw = sum(1 for x in g[w]
                                 if x in col and col[x] != col[w])
                        if cw > 1:
                            bad = True
                            break
                if not bad and rec(i + 1):
                    return True
            del col[v]
        return False

    return dict(col) if rec(0) else None


def classify(name):
    """Map a vertex name to its construction role."""
    if name == "u":
        return "u"
    if name == "a":
        return "a"
    if name.startswith("w_"):
        return "wit"       # private witness (degree 2)
    if name.startswith("q"):
        return "q"         # shared variable witness
    if name.startswith(("t", "f")):
        return "lit"       # literal vertex t_i / f_i
    if name.startswith("g"):
        return "gate"      # variable gate g_i
    if name.startswith("p_"):
        return "occ"       # occurrence vertex
    if name.startswith("c_"):
        return "copy"      # equality-copy vertex
    if name.startswith("z"):
        return "clause"    # clause vertex z_C
    return "?"


def main():
    rng = random.Random(2026)  # same seed as the verifier
    shapes = Counter()
    mismatches = 0
    for _ in range(400):
        n = rng.randint(1, 3)
        m = rng.randint(1, 3)
        clauses = random_formula(rng, n, m)
        g = build_graph(n, clauses)
        if not is_bipartite(g)[0]:
            continue
        if len(distances_from(g, "u")) != len(g):
            continue
        if min(eccentricity(g, v) for v in g) != 3:
            continue
        if formula_sat(n, clauses):
            continue  # only the sat=False & mc=True direction failed
        w = mc_witness(g)
        if w is None:
            continue  # correct on this one
        mismatches += 1
        # minority side = the side NOT containing the majority
        sides = Counter(w.values())
        minority_colour = min(sides, key=lambda c: sides[c])
        minority = sorted(v for v, c in w.items() if c == minority_colour)
        roles = tuple(sorted(Counter(classify(v) for v in minority).items()))
        shapes[(n, roles)] += 1
        if mismatches <= 12:
            print(f"n={n} m={m} minority({len(minority)}): {minority}")
    print(f"\ntotal spurious-cut instances: {mismatches}")
    print("\nshape census ((n, minority-role-multiset) -> count):")
    for k, v in shapes.most_common():
        print(f"  {k}: {v}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
