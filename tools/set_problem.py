#!/usr/bin/env python3
"""The witness-group island problem (Block 7's case-A reformulation,
stated as a standalone combinatorial problem).

INSTANCE: bipartite graph between X (the L2 side) and Z (the L3 side),
plus a partition of X into witness groups (a group = the X-vertices that
share one L1 witness in the graph picture; singleton group = private
witness).

QUESTION: is there a nonempty B ⊆ X with
  (alpha) at most one member of each witness group in B;
  (beta)  every z in N(B) has at most 1 neighbour outside B;
  (gamma) every x in X\\B has at most 1 neighbour in N(B)?

Equivalently (verified equivalence, verify_reformulation.py 27462/0):
G bipartite radius-3, center u, has a valid matching-cut colouring with
u red, N(u) all red, and blue∩L2 nonempty  IFF  the derived instance
(X=L2, Z=L3, groups = shared-L1-witness classes restricted to S) is YES.
NOTE the derivation detail: only X-vertices with EXACTLY ONE L1 neighbour
are selectable (others can never be blue in case A); we model that here
by simply not listing unselectable vertices in any group — callers build
instances where every listed X-vertex is selectable.

This module gives a brute-force decision procedure for small instances.
Instance format: groups = list of tuples of X-names (the partition),
zadj = dict z-name -> tuple of X-names.
"""

import sys
from itertools import combinations


def solve_bruteforce(groups, zadj):
    """Return a solving B (frozenset) or None. Enumerates all subsets
    respecting alpha, smallest first; checks beta+gamma. Exponential —
    intended for |X| <= ~18 verification use only."""
    X = [x for grp in groups for x in grp]
    # neighbour map X -> touched z's
    xz = {x: [] for x in X}
    for z, nbrs in zadj.items():
        for x in nbrs:
            xz[x].append(z)
    n = len(X)
    # enumerate subsets by size (finds a smallest witness, nice for study)
    for r in range(1, n + 1):
        for Bt in combinations(X, r):
            B = set(Bt)
            # alpha: at most one per group
            if any(sum(1 for x in grp if x in B) > 1 for grp in groups):
                continue
            # touched z's
            touched = set()
            for x in B:
                touched.update(xz[x])
            # beta
            if any(sum(1 for x in zadj[z] if x not in B) > 1
                   for z in touched):
                continue
            # gamma
            ok = True
            for x in X:
                if x in B:
                    continue
                if sum(1 for z in xz[x] if z in touched) > 1:
                    ok = False
                    break
            if ok:
                return frozenset(B)
    return None


if __name__ == "__main__":
    # tiny smoke tests with known answers
    # 1) single private vertex, no z: B={x} works trivially
    assert solve_bruteforce([("x",)], {}) == frozenset({"x"})
    # 2) two vertices sharing a witness, one z adjacent to both:
    #    B={x1}: z touched, x2 outside -> beta ok (1 outside);
    #    gamma at x2: 1 touched neighbour -> ok
    assert solve_bruteforce([("x1", "x2")], {"z": ("x1", "x2")}) is not None
    # 3) forced-violation: x1 alone, z with 3 nbrs all private:
    #    B={x1}: z touched, 2 outside -> beta fails; B={x1,x2}: 1 outside ok
    r = solve_bruteforce([("x1",), ("x2",), ("x3",)],
                         {"z": ("x1", "x2", "x3")})
    assert r is not None and len(r) >= 2
    print("set_problem smoke tests PASS")
    sys.exit(0)
