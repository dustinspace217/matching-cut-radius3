#!/usr/bin/env python3
"""Verify the Schaefer classification of Sol's source relation.

R = "not exactly one true of three" = {000,011,101,110,111}.
Source problem: satisfiability of conjunctions of R applied to LITERALS
(variables or negations). By Schaefer's dichotomy this is NP-complete iff
the literal-closed language Γ = {R composed with every negation pattern}
escapes all six tractable classes: 0-valid, 1-valid, Horn (AND-closed),
dual-Horn (OR-closed), affine (XOR-closed: a⊕b⊕c closure), bijunctive
(majority-closed). Check all 8 negation variants of R against all six
closure properties by brute force. NP-complete iff for EACH class, SOME
variant violates it.
"""

from itertools import product

R = {(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0), (1, 1, 1)}


def variant(R, flips):
    return {tuple(t[i] ^ flips[i] for i in range(3)) for t in R}


def closed_under(rel, op3=None, op2=None):
    ts = list(rel)
    if op2:
        for a in ts:
            for b in ts:
                if tuple(op2(a[i], b[i]) for i in range(3)) not in rel:
                    return False
        return True
    for a in ts:
        for b in ts:
            for c in ts:
                if tuple(op3(a[i], b[i], c[i]) for i in range(3)) not in rel:
                    return False
    return True


def main():
    variants = [variant(R, f) for f in product((0, 1), repeat=3)]
    classes = {
        "0-valid": lambda rel: (0, 0, 0) in rel,
        "1-valid": lambda rel: (1, 1, 1) in rel,
        "Horn(AND)": lambda rel: closed_under(rel, op2=lambda x, y: x & y),
        "dualHorn(OR)": lambda rel: closed_under(rel, op2=lambda x, y: x | y),
        "affine(XOR3)": lambda rel: closed_under(
            rel, op3=lambda x, y, z: x ^ y ^ z),
        "bijunctive(MAJ)": lambda rel: closed_under(
            rel, op3=lambda x, y, z: (x & y) | (x & z) | (y & z)),
    }
    all_escape = True
    for name, test in classes.items():
        holds_for_all = all(test(v) for v in variants)
        print(f"{name}: holds for ALL variants = {holds_for_all}")
        if holds_for_all:
            all_escape = False
    print("=> literal-closed language escapes every Schaefer class:",
          all_escape)
    print("=> source problem (R over literals) NP-complete per Schaefer:",
          all_escape)


if __name__ == "__main__":
    main()
