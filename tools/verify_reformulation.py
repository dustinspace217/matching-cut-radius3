#!/usr/bin/env python3
"""Verify the Case-A reformulation lemma exhaustively.

LEMMA (candidate): let G be connected bipartite radius-3 with center u,
layers L0..L3. There is a valid colouring with u red and N(u) all red and
blue ∩ L2 nonempty IFF there exists nonempty B2 ⊆ S := {v ∈ L2 :
|N(v)∩L1| = 1} such that, with B3 := N(B2)∩L3:
  (α) the witness map v ↦ (unique L1-neighbour of v) is injective on B2;
  (β) every z ∈ B3 has |N(z) ∖ B2| ≤ 1  (N(z) ⊆ L2);
  (γ) every v ∈ L2 ∖ B2 has |N(v) ∩ B3| ≤ 1.
(The corresponding colouring: blue = B2 ∪ B3, red = rest.)

Also verify the A0 side: a valid colouring with u red, N(u) red, and
blue ∩ L2 EMPTY exists iff some nonempty set of degree-<=1 L3 vertices
with pairwise distinct neighbours exists (equivalently: some L3 vertex has
degree <= 1).

Check both directions on every connected bipartite radius-3 graph n<=8
(and centers): enumerate all valid colourings of the graph, restrict to
case A (u red, N(u) red); compare against enumeration of all B2 ⊆ S
satisfying (α)(β)(γ) plus the A0 criterion. Report mismatches.
"""

import sys
from itertools import product, combinations, chain

sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
from mc_check import (make_graph, eccentricity, distances_from,
                      valid_colourings)
from structure_test import bipartite_graphs


def layers(g, u):
    d = distances_from(g, u)
    L1 = {v for v in g if d[v] == 1}
    L2 = {v for v in g if d[v] == 2}
    L3 = {v for v in g if d[v] == 3}
    return L1, L2, L3


def caseA_exists_via_colourings(g, u, L1, L2):
    """Ground truth: any valid colouring with u=R, N(u) all R?
    Split by whether blue∩L2 is empty. Returns (a1_exists, a0_exists)."""
    a1 = a0 = False
    for col in valid_colourings(g, fixed={u: "R"}):
        if any(col[w] == "B" for w in L1):
            continue
        if any(col[v] == "B" for v in L2):
            a1 = True
        else:
            a0 = True
        if a1 and a0:
            break
    return a1, a0


def caseA1_via_sets(g, u, L1, L2, L3):
    S = [v for v in L2 if len(set(g[v]) & L1) == 1]
    for r in range(1, len(S) + 1):
        for B2t in combinations(S, r):
            B2 = set(B2t)
            wits = [next(iter(set(g[v]) & L1)) for v in B2]
            if len(set(wits)) != len(wits):
                continue
            B3 = set()
            for v in B2:
                B3 |= set(g[v]) & L3
            ok = True
            for z in B3:
                if len(set(g[z]) - B2) > 1:
                    ok = False
                    break
            if ok:
                for v in L2 - B2:
                    if len(set(g[v]) & B3) > 1:
                        ok = False
                        break
            if ok:
                return True
    return False


def caseA0_via_sets(g, L3):
    return any(len(g[z]) <= 1 for z in L3)


def main(n_max=8):
    graphs = 0
    mism = 0
    for n in range(4, n_max + 1):
        for p in range(2, n - 1):
            q = n - p
            if q < 2:
                continue
            for g, L, R in bipartite_graphs(p, q):
                eccs = {v: eccentricity(g, v) for v in g}
                if min(eccs.values()) != 3:
                    continue
                graphs += 1
                for u in (v for v in g if eccs[v] == 3):
                    L1, L2, L3 = layers(g, u)
                    a1_truth, a0_truth = caseA_exists_via_colourings(
                        g, u, L1, L2)
                    a1_sets = caseA1_via_sets(g, u, L1, L2, L3)
                    a0_sets = caseA0_via_sets(g, L3)
                    if a1_truth != a1_sets or a0_truth != a0_sets:
                        mism += 1
                        if mism <= 5:
                            print(f"MISMATCH n={n} center={u} "
                                  f"A1 truth={a1_truth} sets={a1_sets} "
                                  f"A0 truth={a0_truth} sets={a0_sets}")
                            print("  edges:",
                                  sorted(tuple(sorted((a, b)))
                                         for a in g for b in g[a] if a < b))
    print(f"graphs={graphs} mismatches={mism}")
    return mism


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
