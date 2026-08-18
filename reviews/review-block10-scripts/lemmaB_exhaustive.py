#!/usr/bin/env python3
"""Adversarial audit B2: EXHAUSTIVE sweep of Lemma B' in the document's
GENERAL form -- any connected bipartite graph and any center u with
ecc(u)=3, NOT restricted to radius exactly 3 (which is all that
tools/verify_reformulation.py covers). n <= 8.
"""
import sys
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
sys.path.insert(0, "/tmp/claude/pvnp2")
from mc_check import eccentricity
from structure_test import bipartite_graphs
from lemmaB_attack import layers, truth_A1, sets_Bprime


def main(n_max=8):
    graphs = pairs = mism = 0
    nonradius3 = 0
    for n in range(4, n_max + 1):
        for p in range(2, n - 1):
            q = n - p
            if q < 2:
                continue
            for g, L, R in bipartite_graphs(p, q):
                eccs = {v: eccentricity(g, v) for v in g}
                if not any(e == 3 for e in eccs.values()):
                    continue
                graphs += 1
                if min(eccs.values()) != 3:
                    nonradius3 += 1
                for u in (v for v in g if eccs[v] == 3):
                    L1, L2, L3 = layers(g, u)
                    t = truth_A1(g, u, L1, L2) is not None
                    s = sets_Bprime(g, u, L1, L2, L3) is not None
                    pairs += 1
                    if t != s:
                        mism += 1
                        if mism <= 5:
                            print("MISMATCH center", u, "truth", t, "sets", s,
                                  sorted(tuple(sorted((a, b))) for a in g
                                         for b in g[a] if a < b))
    print(f"graphs={graphs} (of which radius!=3: {nonradius3}) "
          f"(graph,center) pairs={pairs} mismatches={mism}")
    return 1 if mism else 0


if __name__ == "__main__":
    sys.exit(main(*[int(x) for x in sys.argv[1:]]))
