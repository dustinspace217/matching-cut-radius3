#!/usr/bin/env python3
"""Adversarial audit A: check EVERY prose claim of mc-radius3-theorem.md
sections 2-3 against build_guarded_graph, on many formula shapes.

Layers are recomputed by BFS from u (never trusted from names), so a
name/layer drift in the builder would show up.
"""
import sys, random, itertools
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
from guarded_reduction import build_guarded_graph
from mc_check import make_graph, is_bipartite, distances_from, eccentricity

FAIL = []

def note(cond, msg, ctx):
    if not cond:
        FAIL.append(f"{msg} | {ctx}")

def audit(n, clauses):
    ctx = f"n={n} clauses={clauses}"
    g = build_guarded_graph(n, clauses)
    d = distances_from(g, "u")
    note(len(d) == len(g), "DISCONNECTED", ctx)
    if len(d) != len(g):
        return g
    L = {k: {v for v in g if d[v] == k} for k in range(0, 5)}
    L1, L2, L3 = L[1], L[2], L[3]
    note(not L[4], "layer 4 nonempty", ctx)

    # --- 3.1 bipartite with the CLAIMED parts A={u}|L2, B=L1|L3
    A = {"u"} | L2
    B = L1 | L3
    note(A | B == set(g), "parts do not cover V", ctx)
    for v in g:
        for w in g[v]:
            note((v in A) != (w in A), f"edge inside a part {v}-{w}", ctx)
    note(is_bipartite(g)[0], "not bipartite", ctx)

    # --- 3.2 / 3.3 radius & eccentricity
    eccs = {v: eccentricity(g, v) for v in g}
    note(eccs["u"] == 3, f"ecc(u)={eccs['u']}", ctx)
    note(min(eccs.values()) == 3, f"radius={min(eccs.values())}", ctx)
    note(all(e >= 3 for e in eccs.values()), "some ecc<3", ctx)
    diam = max(eccs.values())
    note(diam >= 4, f"DIAMETER {diam} <= 3 -- lands in known-poly cell!", ctx)

    # --- §2 layer membership by name
    for v in g:
        if v == "u":
            continue
        nm = v
        is_l1 = (nm.startswith("q") or nm == "w_a" or nm.startswith("w_p_")
                 or nm.startswith("wp_") or nm in ("wT1a","wT1b","wT2a","wT2b"))
        is_l3 = (nm.startswith("g") or nm.startswith("c_")
                 or nm.startswith("z") or nm == "Zk")
        exp = 1 if is_l1 else (3 if is_l3 else 2)
        note(d[v] == exp, f"vertex {v} in layer {d[v]}, expected {exp}", ctx)

    # --- §2 "u ~ every L1 vertex and nothing else"
    note(g["u"] == L1, "N(u) != L1", ctx)

    # --- §2 L1 adjacency, exactly as written in the prose
    def nb(v):
        return set(g[v])
    for i in range(n):
        note(nb(f"q{i}") == {"u", f"t{i}", f"f{i}", f"G_q{i}"},
             f"N(q{i}) = {sorted(nb(f'q{i}'))}", ctx)
    note(nb("w_a") == {"u", "a", "G_w_a"}, f"N(w_a)={sorted(nb('w_a'))}", ctx)
    for ci, cl in enumerate(clauses):
        for j in range(3):
            p = f"p_{ci}_{j}"
            w = f"w_{p}"
            note(nb(w) == {"u", p, f"G_{w}"}, f"N({w})={sorted(nb(w))}", ctx)

    # --- §2 witness counts in L2 ("a,t,f,p have EXACTLY ONE L1-neighbour")
    S = {v for v in L2 if len(nb(v) & L1) == 1}
    expected_S = {"a"} | {f"t{i}" for i in range(n)} | {f"f{i}" for i in range(n)} \
                 | {f"p_{ci}_{j}" for ci in range(len(clauses)) for j in range(3)}
    note(S == expected_S, f"S mismatch: extra={sorted(S-expected_S)} "
                          f"missing={sorted(expected_S-S)}", ctx)
    for v in L2 - S:
        note(len(nb(v) & L1) == 2, f"{v} has {len(nb(v)&L1)} witnesses", ctx)

    # --- §2 L3 degrees
    for z in L3:
        note(len(g[z]) >= 2, f"L3 vertex {z} has degree {len(g[z])}", ctx)
    for i in range(n):
        note(len(g[f"g{i}"]) == 3 and nb(f"g{i}") == {"a", f"t{i}", f"f{i}"},
             f"g{i} nbrs {sorted(nb(f'g{i}'))}", ctx)
    for ci in range(len(clauses)):
        for j in range(3):
            for k in (0, 1):
                c = f"c_{ci}_{j}_{k}"
                note(len(g[c]) == 2, f"copy {c} degree {len(g[c])}", ctx)
        note(len(g[f"z{ci}"]) == 3, f"z{ci} degree {len(g[f'z{ci}'])}", ctx)
    BW = [f"q{i}" for i in range(n)] + ["w_a"] + \
         [f"w_p_{ci}_{j}" for ci in range(len(clauses)) for j in range(3)]
    note(nb("Zk") == {"T1", "T2"} | {f"G_{W}" for W in BW},
         f"N(Zk) mismatch: {sorted(nb('Zk'))}", ctx)
    note(len(g["Zk"]) == 2 + len(BW), "Zk degree formula", ctx)
    note(len(BW) == n + 1 + 3*len(clauses), "|BW| formula", ctx)

    # --- 3.3(ii): every L1 vertex has at most 3 L2-neighbours; |L2|>=4
    for v in L1:
        note(len(nb(v) & L2) <= 3, f"L1 vertex {v} has {len(nb(v)&L2)} "
                                   f"L2-neighbours", ctx)
    note(len(L2) >= 4, f"|L2|={len(L2)}", ctx)
    # --- 3.3(iii): every L2 vertex has at most 2 L1-neighbours; |L1|>=5
    for v in L2:
        note(len(nb(v) & L1) <= 2, f"L2 vertex {v} has {len(nb(v)&L1)} "
                                   f"L1-neighbours", ctx)
    note(len(L1) >= 5, f"|L1|={len(L1)}", ctx)
    # --- every L2 vertex has an L1 neighbour; every L3 vertex an L2 neighbour
    for v in L2:
        note(nb(v) & L1, f"L2 vertex {v} has no witness", ctx)
    for z in L3:
        note(nb(z) <= L2, f"L3 vertex {z} has a non-L2 neighbour", ctx)

    # --- Lemma D structural claims
    B2cands = S
    # (D1) Zk's L2-neighbours are all unselectable
    note(not (nb("Zk") & S), "Zk has a selectable L2-neighbour", ctx)
    # (D2) every base L3 vertex has ALL L2-neighbours selectable
    base_L3 = L3 - {"Zk"}
    for z in base_L3:
        note(nb(z) <= S, f"base L3 {z} has unselectable nbr "
                         f"{sorted(nb(z)-S)}", ctx)
    # (D3) groups induced by the witness map
    wmap = {v: next(iter(nb(v) & L1)) for v in S}
    grp = {}
    for v, w in wmap.items():
        grp.setdefault(w, set()).add(v)
    exp_groups = [{f"t{i}", f"f{i}"} for i in range(n)] + [{"a"}] + \
                 [{f"p_{ci}_{j}"} for ci in range(len(clauses)) for j in range(3)]
    note(sorted(map(sorted, grp.values())) == sorted(map(sorted, exp_groups)),
         f"groups mismatch {sorted(map(sorted,grp.values()))}", ctx)
    # (D4) for v in L2\S, N(v) cap L3 == {Zk}
    for v in L2 - S:
        note(nb(v) & L3 == {"Zk"}, f"{v} L3-nbrs {sorted(nb(v)&L3)}", ctx)
    # (D5) for v in S, N(v) cap L3 subset base
    for v in S:
        note(nb(v) & L3 <= base_L3, f"{v} touches Zk", ctx)
    return g


def main():
    rng = random.Random(917253)
    shapes = []
    # exhaustive tiny: n=1, m=1 all sign patterns
    for signs in itertools.product((True, False), repeat=3):
        shapes.append((1, [list(zip((0,0,0), signs))]))
    # n=2, m=1 all var tuples & signs
    for vis in itertools.product(range(2), repeat=3):
        for signs in itertools.product((True, False), repeat=3):
            shapes.append((2, [list(zip(vis, signs))]))
    # unused variables: n=3, clause only on var 0
    shapes.append((3, [[(0, True), (0, True), (0, False)]]))
    shapes.append((5, [[(0, True), (0, True), (0, True)]]))
    # repeated literals across clauses
    shapes.append((2, [[(0,True),(0,True),(0,True)],
                       [(0,True),(0,True),(0,True)],
                       [(1,False),(1,False),(1,False)]]))
    # random
    for _ in range(400):
        n = rng.randint(1, 5)
        m = rng.randint(1, 5)
        cls = []
        for _ in range(m):
            cls.append([(rng.randrange(n), rng.random() < .5) for _ in range(3)])
        shapes.append((n, cls))
    for n, cls in shapes:
        audit(n, cls)
    print(f"audited {len(shapes)} instances; failures={len(FAIL)}")
    for f in FAIL[:25]:
        print("  FAIL:", f)
    return 1 if FAIL else 0


if __name__ == "__main__":
    sys.exit(main())
