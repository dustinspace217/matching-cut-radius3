#!/usr/bin/env python3
"""Control: my attack scripts must DETECT a deliberately broken variant.
A battery that cannot fail proves nothing.

Mutants:
  M1  no guards at all (Sol's unguarded construction + ballast/killer)
  M2  killer Zk disconnected from the guards
  M3  only one ballast vertex
Each is run through (a) the case-B exhaustive completion search and
(b) the theory-free oracle vs SAT, on the same instances.
"""
import sys, itertools
sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
sys.path.insert(0, "/tmp/claude/pvnp2")
from mc_check import make_graph, distances_from
from independent_mc import has_matching_cut
from verify_sol_reduction import formula_sat
from caseB_attack import complete


def build(n, clauses, mutant=None):
    E = []
    u = "u"
    bw = []

    def l1(x):
        E.append((u, x))

    for i in range(n):
        qi = f"q{i}"
        l1(qi); bw.append(qi)
        E += [(qi, f"t{i}"), (qi, f"f{i}"), (f"t{i}", f"g{i}"),
              (f"f{i}", f"g{i}"), ("a", f"g{i}")]
    l1("w_a"); bw.append("w_a")
    E.append(("w_a", "a"))
    for ci, cl in enumerate(clauses):
        occ = []
        for j, (vi, sign) in enumerate(cl):
            p = f"p_{ci}_{j}"
            wp = f"w_{p}"
            l1(wp); bw.append(wp)
            E.append((wp, p))
            base = f"t{vi}" if sign else f"f{vi}"
            for k in (0, 1):
                E += [(base, f"c_{ci}_{j}_{k}"), (p, f"c_{ci}_{j}_{k}")]
            occ.append(p)
        for p in occ:
            E.append((f"z{ci}", p))
    zk = "Zk"
    ballast = ("T1",) if mutant == "M3" else ("T1", "T2")
    for t in ballast:
        for s in ("a", "b"):
            w = f"w{t}{s}"
            l1(w); E.append((w, t))
        E.append((t, zk))
    if mutant != "M1":
        for W in bw:
            gw = f"G_{W}"
            wpr = f"wp_{W}"
            l1(wpr)
            E += [(W, gw), (wpr, gw)]
            if mutant != "M2":
                E.append((gw, zk))
    return make_graph(E)


def scan(n, cls, mutant):
    g = build(n, cls, mutant)
    d = distances_from(g, "u")
    L1 = {v for v in g if d[v] == 1}
    surv = 0
    for b in sorted(L1, key=repr):
        pin = {"u": "R"}
        for w in L1:
            pin[w] = "B" if w == b else "R"
        if complete(g, pin) is not None:
            surv += 1
    sat = formula_sat(n, cls)
    try:
        mc = has_matching_cut(g, budget=100_000_000)
    except TimeoutError:
        mc = None
    return surv, sat, mc


def main():
    # UNSAT n=1 two-clause instances -- where a broken guard leaks
    tests = [(1, [[(0, True), (0, True), (0, False)],
                  [(0, False), (0, False), (0, True)]]),
             (1, [[(0, True), (0, False), (0, False)],
                  [(0, True), (0, True), (0, False)]]),
             (1, [[(0, False), (0, True), (0, True)],
                  [(0, True), (0, False), (0, False)]])]
    for mutant in (None, "M1", "M2", "M3"):
        tot_s = mm = 0
        for n, cls in tests:
            s, sat, mc = scan(n, cls, mutant)
            tot_s += s
            if mc is not None and sat != mc:
                mm += 1
        print(f"{mutant or 'INTACT':7s}  case-B survivors={tot_s:3d}  "
              f"oracle-vs-SAT mismatches={mm}/{len(tests)}")


if __name__ == "__main__":
    main()
