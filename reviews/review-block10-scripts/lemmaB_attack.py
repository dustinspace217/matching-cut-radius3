#!/usr/bin/env python3
"""Adversarial audit B: attack Lemma B' AS WRITTEN IN THE DOCUMENT.

Document statement (mc-radius3-theorem.md section 5), transcribed here
independently of tools/verify_reformulation.py:

  For a connected bipartite G with a vertex u of eccentricity 3 and BFS
  layers L0..L3, let S := {v in L2 : |N(v) cap L1| = 1}, w(v) := that
  unique L1 neighbour.

  G has a valid colouring with u red, N(u) all red, and blue cap L2
  nonempty  IFF  there is a nonempty B2 subset of S with
    (alpha) w injective on B2
    (beta') every z in N(B2) cap L3 has |N(z) \\ B2| <= 1, N(z) the FULL
            L2-neighbourhood
    (gamma') every v in L2 \\ B2 -- selectable or not -- has
             |N(v) cap N(B2) cap L3| <= 1

NOTE: the document does NOT require radius exactly 3, only ecc(u) = 3.
We test that general form (strictly harder than the radius-3 form the
project's own script tests).
"""
import sys, random
from itertools import combinations, product
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
from mc_check import make_graph, is_bipartite, distances_from, eccentricity


def layers(g, u):
    d = distances_from(g, u)
    return ({v for v in g if d.get(v) == 1},
            {v for v in g if d.get(v) == 2},
            {v for v in g if d.get(v) == 3})


def truth_A1(g, u, L1, L2):
    """Ground truth by exhaustive colouring: does a valid colouring exist
    with u red, all of L1 red, blue cap L2 nonempty? Returns witness."""
    free = sorted((set(g) - {u} - L1), key=repr)
    fixed = {u: "R"}
    for w in L1:
        fixed[w] = "R"
    for bits in product("RB", repeat=len(free)):
        col = dict(fixed)
        col.update(zip(free, bits))
        if not any(col[v] == "B" for v in L2):
            continue
        if len(set(col.values())) < 2:
            continue
        ok = True
        for v in g:
            if sum(1 for x in g[v] if col[x] != col[v]) > 1:
                ok = False
                break
        if ok:
            return col
    return None


def sets_Bprime(g, u, L1, L2, L3):
    """The document's condition, verbatim."""
    S = [v for v in L2 if len(set(g[v]) & L1) == 1]
    for r in range(1, len(S) + 1):
        for B2t in combinations(S, r):
            B2 = set(B2t)
            wits = [next(iter(set(g[v]) & L1)) for v in B2]
            if len(set(wits)) != len(wits):       # (alpha)
                continue
            NB3 = set()
            for v in B2:
                NB3 |= set(g[v]) & L3
            if any(len(set(g[z]) - B2) > 1 for z in NB3):   # (beta')
                continue
            if any(len(set(g[v]) & NB3) > 1 for v in L2 - B2):  # (gamma')
                continue
            return B2
    return None


def check(g, u, verbose=False):
    if len(distances_from(g, u)) != len(g):
        return None
    if eccentricity(g, u) != 3:
        return None
    if not is_bipartite(g)[0]:
        return None
    L1, L2, L3 = layers(g, u)
    t = truth_A1(g, u, L1, L2)
    s = sets_Bprime(g, u, L1, L2, L3)
    return (t is not None, s is not None, t, s)


def rand_bip(rng, p, q, prob):
    Lv = [f"L{i}" for i in range(p)]
    Rv = [f"R{j}" for j in range(q)]
    E = [(a, b) for a in Lv for b in Rv if rng.random() < prob]
    return make_graph(E, isolated=Lv + Rv)


def main(trials=40000, seed=48271):
    rng = random.Random(seed)
    tested = 0
    bad = []
    for _ in range(trials):
        p = rng.randint(2, 6)
        q = rng.randint(2, 6)
        if p + q > 12:
            continue
        g = rand_bip(rng, p, q, rng.choice([0.25, 0.35, 0.45, 0.55]))
        for u in list(g):
            r = check(g, u)
            if r is None:
                continue
            tested += 1
            if r[0] != r[1]:
                bad.append((sorted(tuple(sorted((a, b))) for a in g
                                   for b in g[a] if repr(a) < repr(b)),
                            u, r[0], r[1]))
                if len(bad) > 5:
                    break
        if len(bad) > 5:
            break
    print(f"Lemma B' (document form, ecc(u)=3, any radius): "
          f"tested {tested} (graph,center) pairs; mismatches {len(bad)}")
    for b in bad[:5]:
        print("  MISMATCH center=", b[1], "truth=", b[2], "sets=", b[3])
        print("   edges:", b[0])
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(*[int(x) for x in sys.argv[1:]]))
