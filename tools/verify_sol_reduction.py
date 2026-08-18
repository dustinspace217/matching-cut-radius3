#!/usr/bin/env python3
"""DECISIVE TEST of Sol's NP-hardness reduction for MC bipartite radius-3.

Sol claims: MC on bipartite radius-3 is NP-complete, via a reduction from
SIGNED-NOT-1-IN-3-SAT (relation R(x,y,z) = "x+y+z != 1", over literals).
We build Sol's actual GRAPH and test, end to end against brute force:
  G has a matching cut  IFF  the source formula is satisfiable.
No reliance on the case-A reformulation -- we brute-force the real graph's
matching-cut existence and compare to a brute-force SAT check of the
formula. Any spurious matching cut (graph YES, formula NO) or missed one
(graph NO, formula YES) FALSIFIES the reduction.

Sol's construction (verbatim from the reply):
  L2: anchor a; t_i,f_i per variable; occurrence vertex p_{C,j} per
      clause position.
  L1 (witnesses): t_i,f_i share witness q_i; a and every occurrence get
      private witnesses. Plus the center u adjacent to all L1.
  L3: variable gate g_i ~ {a, t_i, f_i}; per occurrence p of literal l
      two copies c0,c1 each ~ {b(l), p} where b(x_i)=t_i, b(~x_i)=f_i;
      clause vertex z_C ~ {the three occurrence vertices of C}.

We add the center u ~ all L1 to realize the 4-layer graph. Then verify
bipartite + radius exactly 3, and brute-force matching-cut existence.
Compare against brute-force satisfiability over all 2^n assignments.
Enumerate many small random formulas.
"""

import sys
import random
from itertools import product

sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
from mc_check import (make_graph, is_bipartite, eccentricity,
                      distances_from)
from independent_mc import has_matching_cut


def build_graph(n, clauses):
    """clauses: list of 3 (var_index, sign) with sign True=positive.
    Returns edge list of Sol's graph with center u."""
    E = []
    u = "u"
    L1 = []  # witnesses

    def wit(name):
        q = f"w_{name}"
        L1.append(q)
        E.append((u, q))
        E.append((q, name))
        return q

    # variables
    for i in range(n):
        ti, fi = f"t{i}", f"f{i}"
        qi = f"q{i}"          # shared witness
        L1.append(qi)
        E.append((u, qi))
        E.append((qi, ti))
        E.append((qi, fi))
        # variable gate g_i ~ {a, t_i, f_i}
        E.append((ti, f"g{i}"))
        E.append((fi, f"g{i}"))
        E.append(("a", f"g{i}"))
    wit("a")  # anchor private witness
    # occurrences
    for ci, cl in enumerate(clauses):
        occ_vertices = []
        for j, (vi, sign) in enumerate(cl):
            p = f"p_{ci}_{j}"
            wit(p)  # private witness for occurrence
            base = f"t{vi}" if sign else f"f{vi}"
            # two copies c0,c1 each ~ {base, p}
            for k in (0, 1):
                c = f"c_{ci}_{j}_{k}"
                E.append((base, c))
                E.append((p, c))
            occ_vertices.append(p)
        # clause vertex z_C ~ the three occurrence vertices
        for p in occ_vertices:
            E.append((f"z{ci}", p))
    return make_graph(E)


def formula_sat(n, clauses):
    """SIGNED-NOT-1-IN-3: each clause R(l1,l2,l3): NOT exactly one true."""
    for assign in product((0, 1), repeat=n):
        ok = True
        for cl in clauses:
            t = sum(1 for (vi, sign) in cl
                    if (assign[vi] == 1) == sign)
            if t == 1:
                ok = False
                break
        if ok:
            return True
    return False


def has_mc(g):
    return has_matching_cut(g)


def random_formula(rng, n, m):
    clauses = []
    for _ in range(m):
        cl = []
        vs = rng.sample(range(n), min(3, n))
        while len(vs) < 3:
            vs.append(rng.randrange(n))
        for vi in vs[:3]:
            cl.append((vi, rng.random() < 0.5))
        clauses.append(cl)
    return clauses


def main():
    rng = random.Random(2026)
    tested = 0
    mism = 0
    radius_bad = 0
    for _ in range(400):
        n = rng.randint(1, 3)
        m = rng.randint(1, 3)
        clauses = random_formula(rng, n, m)
        g = build_graph(n, clauses)
        bip = is_bipartite(g)[0]
        if not bip:
            print("NOT BIPARTITE", n, clauses)
            return 1
        if len(distances_from(g, "u")) != len(g):
            continue
        r = min(eccentricity(g, v) for v in g)
        if r != 3:
            radius_bad += 1
            continue  # only test instances that are genuinely radius-3
        tested += 1
        sat = formula_sat(n, clauses)
        mc = has_mc(g)
        if sat != mc:
            mism += 1
            if mism <= 5:
                print(f"MISMATCH sat={sat} mc={mc} n={n} clauses={clauses}")
    print(f"tested {tested}; mismatches {mism}; "
          f"radius!=3 skipped {radius_bad}")
    return 1 if mism else 0


if __name__ == "__main__":
    sys.exit(main())
