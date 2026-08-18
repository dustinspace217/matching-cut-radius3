#!/usr/bin/env python3
"""Block 9: the guarded reduction — Sol's construction + a case-B killer.

Block 8's refutation + tonight's defect taxonomy showed ALL leaks in
Sol's graph-level reduction are case-B colourings (exactly one L1 vertex
blue, everything cascading from there). The set-level core (case A) is
verified sound (sol_set_reduction.py: 4,784 formulas, 0 mismatches).

THE GUARD BATTERY (the new part), designed to make case B impossible:
  - Ballast: T1, T2 in L2, each with TWO private L1 witnesses. A vertex
    with two L1 witnesses can only be blue if one of its witnesses is
    the (unique) blue L1 vertex; T1/T2's witnesses guard each other via
    the shared killer below.
  - Killer: Z* in L3, adjacent to T1, T2, and every guard vertex.
  - Guard: for EVERY L1 witness W of the base construction (shared q_i,
    anchor witness w_a, proxy witnesses w_p), add G_W in L2 with edges
    {W, w'_W, Z*} where w'_W is a fresh private L1 witness.

Why case B dies (paper argument, machine-tested here): let b in L1 be
the unique blue L1 vertex (u red WLOG). b's budget is consumed by the
u-edge, so ALL of b's other neighbours are forced blue.
  - b = W (any base witness) or b = w'_W: forces G_W blue; G_W's budget
    goes to its other (red) witness, so G_W's L3-neighbours are forced
    blue: Z* turns blue. Z* then crosses T1 and T2 (red, since neither
    of their witnesses is b) — 2 cross edges, invalid.
  - b = a T-witness: forces that T blue, whose budget goes to its other
    witness, forcing Z* blue, which crosses the other T + all guards —
    invalid.
Case A0 dies: every L3 vertex has degree >= 2 (gates 3, copies 2,
clause vertices 3, Z* >= 4).
Case A is untouched: guards, T's (two L1 witnesses each) are never blue
in case A, so Z* is never touched; the set-problem semantics on the base
construction are exactly as verified.

THE TEST (decisive, same shape that refuted Block 8): build the real
graph, check bipartite + radius exactly 3, brute-force matching-cut
existence with the INDEPENDENT oracle, compare with brute-force SAT.
"""

import sys
import random

sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
from mc_check import make_graph, is_bipartite, eccentricity, distances_from
from independent_mc import has_matching_cut
from verify_sol_reduction import formula_sat, random_formula


def build_guarded_graph(n, clauses):
    """Formula -> guarded graph edge list. Layers: u / L1 witnesses /
    L2 = X-vertices + guards + ballast / L3 = Z-vertices + killer."""
    E = []
    u = "u"
    base_witnesses = []   # every L1 witness of the base construction

    def l1(name):
        E.append((u, name))

    # --- base construction (Sol's, unchanged) ---
    for i in range(n):
        qi = f"q{i}"
        l1(qi)
        base_witnesses.append(qi)
        E.append((qi, f"t{i}"))
        E.append((qi, f"f{i}"))
        E.append((f"t{i}", f"g{i}"))
        E.append((f"f{i}", f"g{i}"))
        E.append(("a", f"g{i}"))
    wa = "w_a"
    l1(wa)
    base_witnesses.append(wa)
    E.append((wa, "a"))
    for ci, cl in enumerate(clauses):
        occ = []
        for j, (vi, sign) in enumerate(cl):
            p = f"p_{ci}_{j}"
            wp = f"w_{p}"
            l1(wp)
            base_witnesses.append(wp)
            E.append((wp, p))
            base = f"t{vi}" if sign else f"f{vi}"
            for k in (0, 1):
                c = f"c_{ci}_{j}_{k}"
                E.append((base, c))
                E.append((p, c))
            occ.append(p)
        for p in occ:
            E.append((f"z{ci}", p))

    # --- guard battery (new) ---
    zk = "Zk"  # the killer, in L3
    # ballast T1, T2, two private witnesses each
    for t in ("T1", "T2"):
        for s in ("a", "b"):
            w = f"w{t}{s}"
            l1(w)
            E.append((w, t))
        E.append((t, zk))
    # one guard per base witness
    for W in base_witnesses:
        gw = f"G_{W}"
        wprime = f"wp_{W}"
        l1(wprime)
        E.append((W, gw))
        E.append((wprime, gw))
        E.append((gw, zk))
    return make_graph(E)


def main(n_lo=1, n_hi=2, m_lo=1, m_hi=2, rounds=200, seed=2026,
         budget=20_000_000):
    rng = random.Random(seed)
    tested = mism = timeouts = 0
    for _ in range(rounds):
        n = rng.randint(n_lo, n_hi)
        m = rng.randint(m_lo, m_hi)
        clauses = random_formula(rng, n, m)
        g = build_guarded_graph(n, clauses)
        ok, _ = is_bipartite(g)
        if not ok:
            print("NOT BIPARTITE", n, clauses)
            return 1
        if len(distances_from(g, "u")) != len(g):
            print("DISCONNECTED", n, clauses)
            return 1
        r = min(eccentricity(g, v) for v in g)
        if r != 3:
            print(f"RADIUS {r} != 3", n, clauses)
            return 1
        sat = formula_sat(n, clauses)
        try:
            mc = has_matching_cut(g, budget=budget)
        except TimeoutError:
            timeouts += 1
            continue
        tested += 1
        if sat != mc:
            mism += 1
            if mism <= 5:
                print(f"MISMATCH sat={sat} mc={mc} n={n} m={m} "
                      f"clauses={clauses} |V|={len(g)}")
    print(f"tested {tested}; mismatches {mism}; timeouts {timeouts}")
    return 1 if mism else 0


if __name__ == "__main__":
    args = [int(x) for x in sys.argv[1:]]
    sys.exit(main(*args))
