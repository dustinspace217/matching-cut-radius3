#!/usr/bin/env python3
"""Fast ISLAND decision via a direct CNF encoding + a small DPLL.

Encoding (straight from the definition in set_problem.py, no theory baked
in): b_x = "x in B" for x in X; t_z = "z in N(B)" for z in Z.
  t_z <-> OR_{x in N(z)} b_x
  alpha: at most one b_x per group
  beta:  for each z and each pair x,y in N(z): (~t_z | b_x | b_y)
  gamma: for each x and each pair z1,z2 in N(x): (b_x | ~t_z1 | ~t_z2)
  nonempty: OR_x b_x
"""
from itertools import combinations


def encode(groups, zadj):
    X = [x for grp in groups for x in grp]
    Z = list(zadj)
    var = {}
    for x in X:
        var[("b", x)] = len(var) + 1
    for z in Z:
        var[("t", z)] = len(var) + 1
    cls = []
    xz = {x: [] for x in X}
    for z in Z:
        nb = [x for x in zadj[z] if x in xz]
        for x in nb:
            xz[x].append(z)
        tz = var[("t", z)]
        # b_x -> t_z
        for x in nb:
            cls.append((-var[("b", x)], tz))
        # t_z -> OR b_x
        cls.append(tuple([-tz] + [var[("b", x)] for x in nb]))
        # beta
        for x, y in combinations(nb, 2):
            cls.append((-tz, var[("b", x)], var[("b", y)]))
    # alpha
    for grp in groups:
        for x, y in combinations(grp, 2):
            cls.append((-var[("b", x)], -var[("b", y)]))
    # gamma
    for x in X:
        for z1, z2 in combinations(xz[x], 2):
            cls.append((var[("b", x)], -var[("t", z1)], -var[("t", z2)]))
    # nonempty
    cls.append(tuple(var[("b", x)] for x in X))
    return len(var), cls, var


def dpll(nvars, clauses):
    """Plain DPLL with unit propagation. Returns assignment dict or None."""
    clauses = [list(c) for c in clauses]
    occ = {}
    for i, c in enumerate(clauses):
        for l in c:
            occ.setdefault(l, []).append(i)
    assign = {}

    def sat_lit(l):
        v = abs(l)
        if v not in assign:
            return None
        return assign[v] == (l > 0)

    def solve(depth=0):
        # unit propagation
        trail = []
        while True:
            changed = False
            for c in clauses:
                unassigned = []
                satisfied = False
                for l in c:
                    s = sat_lit(l)
                    if s is True:
                        satisfied = True
                        break
                    if s is None:
                        unassigned.append(l)
                if satisfied:
                    continue
                if not unassigned:
                    for v in trail:
                        del assign[v]
                    return None
                if len(unassigned) == 1:
                    l = unassigned[0]
                    assign[abs(l)] = (l > 0)
                    trail.append(abs(l))
                    changed = True
            if not changed:
                break
        unass = [v for v in range(1, nvars + 1) if v not in assign]
        if not unass:
            return dict(assign)
        v = unass[0]
        for val in (True, False):
            assign[v] = val
            r = solve(depth + 1)
            if r is not None:
                return r
            del assign[v]
        for v2 in trail:
            del assign[v2]
        return None

    return solve()


def island_yes(groups, zadj):
    nv, cls, var = encode(groups, zadj)
    r = dpll(nv, cls)
    if r is None:
        return None
    B = frozenset(x for (k, x) in var if k == "b" and r.get(var[("b", x)]))
    return B


if __name__ == "__main__":
    # validate against the brute force on random small instances
    import sys, random
    sys.path.insert(0, "/home/dustin/Claude/p-vs-np/tools")
    from set_problem import solve_bruteforce
    rng = random.Random(11)
    bad = 0
    for it in range(4000):
        ng = rng.randint(1, 4)
        groups = []
        names = 0
        for _ in range(ng):
            k = rng.randint(1, 2)
            grp = tuple(f"x{names+i}" for i in range(k))
            names += k
            groups.append(grp)
        X = [x for g in groups for x in g]
        zadj = {}
        for zi in range(rng.randint(0, 4)):
            k = rng.randint(1, min(3, len(X)))
            zadj[f"z{zi}"] = tuple(rng.sample(X, k))
        a = solve_bruteforce(groups, zadj) is not None
        b = island_yes(groups, zadj) is not None
        if a != b:
            bad += 1
            print("DISAGREE", groups, zadj, a, b)
            if bad > 3:
                break
    print("island_sat vs brute force disagreements:", bad)
