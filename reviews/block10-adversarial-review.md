# Fresh adversarial review — mc-radius3-theorem.md (rewritten proof)
(block10-reviewer, delivered 2026-08-18 ~00:51 PDT; attack scripts
preserved in scratch/review-block10-scripts/)

VERDICT SUMMARY:
- Machine level: SURVIVES, with new coverage (independent structural
  audit 475 instances; Lemma B' independently transcribed from the
  document and checked exhaustively in MORE generality than ever
  tested — 276,260 (graph,center) pairs over ALL connected bipartite
  graphs to n=8 with any ecc-3 center, 0 mismatches; graph-derived
  ISLAND bridge with a fresh brute force, 700 instances, 0; exhaustive
  case-B completion search over every b, 132 instances, 0 survivors;
  complete valid-colouring enumeration of six real guarded graphs
  (every colouring found is case A1; UNSAT instances have zero);
  fresh-seed e2e battery 163 instances 0 mismatches 0 timeouts;
  theory-free oracle slice at |V|=75 beyond prior reach; mutation
  controls catch broken variants).
- Proof level: COULD NOT BREAK IT. Every step re-derived by hand and
  machine-checked. The five Block-9 repairs land. The FIRST review's
  objection to the ballast branch was itself incorrect (nothing forces
  guards blue; Claim 4.3 pins them red; the rewrite's branch 3 is the
  correct argument).
- New check the document never made: DIAMETER >= 4 asserted on every
  instance (diameter <= 3 would be a known-poly cell and self-refute).
- Zero REFUTED findings. Residual (all fixed in the document after
  this review): F8 citation scope narrower than lemma (the 27,462/0
  check covers radius-3 graphs only; lemma stated for any ecc-3
  center — reviewer's own 276,260-pair check covers the general form);
  F9 unbacked degenerate-case escape hatch (restrict the source
  problem to n>=1, m>=1 instead); F10 three unfinished sentences
  (|V| formula — true count 6n+19m+12 — plus two abandoned clauses,
  and an editorial bracket in branch 3); F11 three unstated one-line
  layering facts used by Lemma B'; F12 standing theory-free-oracle
  scaling limit (~207s at |V|=75), accurately stated in §9.
- Reviewer's stated ceiling: second same-family model reviewer, not an
  expert human referee, not a proof assistant. Pending at delivery:
  deep_oracle.py |V|=75 UNSAT sweep (1/270 complete, correct so far).

Full report text (verbatim) follows.

---

I formed my own view from the document and `guarded_reduction.py`
before opening the earlier review. My scripts are in
`/tmp/claude/pvnp2/` [preserved: scratch/review-block10-scripts/].
**No REFUTED findings.** Two SUSPICIOUS items are
substantive-but-harmless (a citation-scope over-claim and an
unexhibited degenerate instance); three are editorial. Everything
load-bearing HOLDS.

Note first: I ran a check the document does not make, because it could
have killed the theorem outright — **diameter**. Bipartite + diameter
≤ 3 is a known-polynomial cell, so a construction that accidentally
had diameter 3 would be self-refuting. `struct_audit.py` asserts
diameter ≥ 4 on every instance; all pass.

## 1. HOLDS — prose (§2, §3) against `build_guarded_graph`
475 instances (exhaustive n=1 m=1 and n=2 m=1 sign/variable patterns;
unused variables; all-same-variable clauses; 400 random up to n=5,
m=5). Layers recomputed by BFS from u, never trusted from names.
`audited 475 instances; failures=0`. Verified exactly as written:
N(q_i) = {u, t_i, f_i, G_{q_i}}; N(w_a) = {u, a, G_{w_a}};
N(w_p) = {u, p, G_{w_p}}; a/t/f/p have exactly one L1-neighbour and
guards/ballast exactly two; S is exactly {a} ∪ {t_i,f_i} ∪ {proxies};
L3 degrees g_i=3, c=2, z_C=3, Zk=2+|BW|, all ≥ 2; N(Zk) = {T1,T2} ∪
{G_W}; every L1 vertex has ≤ 3 L2-neighbours and |L2| ≥ 4; every L2
vertex has ≤ 2 L1-neighbours and |L1| ≥ 5; the claimed bipartition has
no edge inside a part; ecc(u)=3, every eccentricity ≥ 3, radius
exactly 3. §3.1–3.3 are now genuine general arguments; 3.3(ii)/(iii)
correctly reduce "ecc ≤ 2" to "adjacent to every opposite-part vertex"
via bipartite parity. Closes the earlier review's finding 8.

## 2. HOLDS — Lemma B'
Re-derived both directions by hand; statement transcribed FROM THE
DOCUMENT, independently of verify_reformulation.py. Random: 21,354
(graph, center) pairs, 0 mismatches. Exhaustive, beyond anything the
project has run: all connected bipartite graphs to n=8 and every
center with ecc(u)=3 — NOT restricted to radius 3:
`graphs=69816 (of which radius!=3: 42354) (graph,center)
pairs=276260 mismatches=0`. The earlier review's 9-vertex
counterexample, run against B' as written: ground truth case-A1 =
False, document's B' = False — correctly rejected (β' fails counting
the unselectable y1, y2). The repair is real, not cosmetic.

## 3. HOLDS — Lemma D
All three structural claims checked per instance (Zk has no selectable
L2-neighbour; every base L3 vertex has an all-selectable
L2-neighbourhood; induced groups exactly {t_i,f_i} ∪ {a} ∪ {p}; every
L2∖S vertex has N(v) ∩ L3 = {Zk}; no S vertex touches Zk): 0 failures.
bridge_attack/bridge_unsat derive the ISLAND instance FROM THE GRAPH
by the document's recipe and solve with a fresh brute force (no
set_problem.py): 400 mixed (51 UNSAT) + 300 UNSAT-only, fresh seeds:
`SAT-vs-B' mismatches=0, B'-vs-ISLAND mismatches=0`. Shapes include
unused variables, all-same-variable clauses, repeated literals.

## 4. HOLDS — Claim 4.4 (case B); the earlier review was wrong here
caseB_attack.py: 132 instances (31 UNSAT), EVERY choice of b ∈ L1,
exhaustive completion with u red, b blue, rest of L1 red:
`survivors=0`. chain_check.py re-derives the prose chain per instance
per b on 373 instances: every b has a double-witnessed forced-blue
pivot with exactly one other witness whose only non-L1 neighbour is
Zk, and Zk always has ≥ 2 Claim-4.3-red neighbours. `defects=0`.
Branch list exhaustive against the builder's L1 inventory. Flagged
explicitly: the earlier review's objection to the ballast branch is
itself incorrect — nothing forces a guard blue; Claim 4.3 pins guards
RED, and Zk's budget is what breaks. The rewrite's branch 3 is the
correct argument; the earlier review's proposed alternative would have
been a wrong repair.

## 5. HOLDS — Claim 4.2 and the §4 split
All L3 degrees ≥ 2 on all 475 instances. Stronger: enumerate_all.py
enumerates EVERY valid u-red colouring of six real guarded graphs
(|V| = 37, 43, 56, 62): every colouring found is A1; zero A0, zero
case-B; the two UNSAT instances have ZERO valid colourings. The A0
argument is sound by hand (blue ⊆ L3 is independent; L3–L3 edges
impossible in the layering).

## 6. HOLDS — §1 source hardness
schaefer_check.py reproduced AND hand-checked: R is 0-valid and
1-valid but the (1,1,0)-variant excludes 000 and the (1,0,0)-variant
excludes 111; R not Horn (011∧101=001∉R); R dual-Horn but the
(1,0,0)-variant is not (100∨001=101∉variant); not affine (|R|=5); not
bijunctive (maj(000,011,101)=001∉R). Schaefer applies; the signs are
what break dual-Horn.

## 7. HOLDS — end-to-end, fresh seed 8675309
e2e.py: 163 instances, 0 mismatches, 0 timeouts, 54 UNSAT — 120 fresh
random n≤2/m≤2, all 18 UNSAT n=1 m=2 formulas, 25 UNSAT-focused n=2
m=2 at |V|=62. Theory-free oracle vs brute-force SAT (oracle
self-check re-run: PASS). Beyond prior theory-free coverage:
deep_oracle.py runs n=1 m=3 guarded graphs at |V|=75 (prior best
complete slice |V|=56); first instance, UNSAT:
`OK |V|=75 sat=False mc=False 206.7s`; sweep pending. Mutation
control: INTACT survivors=0 mismatches=0/3; M1 (no guards)
survivors=24 mismatches=3/3; M2 (killer detached) survivors=48
mismatches=3/3; M3 (one ballast) survivors=0 (T2 redundant given ≥2
guards — design observation, not defect; branch 3 cites T2 plus a
guard, valid).

## 8. SUSPICIOUS — §5's citation scoped narrower than the lemma
verify_reformulation.py tests only radius-exactly-3 graphs
(min-ecc != 3 skipped), whereas Lemma B' is stated for ANY connected
bipartite G with an ecc-3 vertex. Same defect shape that refuted the
previous write-up, milder form. Harmless HERE only because the
general form was verified in this review (276,260 pairs incl. 42,354
non-radius-3 graphs, 0 mismatches). Fix the sentence.

## 9. SUSPICIOUS — §1's degenerate-case escape hatch unbacked
"maps to a fixed YES/NO instance": no fixed instance exhibited; the NO
half asserts an un-named cut-free radius-3 bipartite graph. Cleaner
repair: source problem restricted to n ≥ 1, m ≥ 1 is still NP-hard.

## 10. SUSPICIOUS — three unfinished sentences
§2 |V| formula wrong and abandoned mid-expression — true count
|V| = 6n + 19m + 12 (verified 37, 43, 56, 62, 75). §4 branch 1
abandoned first clause. §3.3(ii) redundant trailing clause. Plus the
bracketed editorial note in branch 3 (history, not proof).

## 11. SUSPICIOUS — three facts used in Lemma B' never justified
(a) for z ∈ L3, N(z) ⊆ L2 (needs ecc(u)=3 for no L4 + bipartiteness
for no L3–L3); (b) no L2–L2 edges; (c) an L1 vertex's non-u
neighbours all lie in L2. Each a one-liner; the ⇐ direction leans on
all three.

## 12. Standing limit (not new)
Theory-free oracle ~207 s at |V|=75; coverage above rests on
instruments sharing the theory under test. enumerate_all (complete
through |V|=62) and the |V|=75 slice extend the frontier, not the
ceiling.

# Verdict
Machine level: survives, with new coverage. Proof level: I could not
break it — a real change from the previous review. Every step of the
chain (WLOG, 4.1, 4.2, 4.3, 4.4's branches, B' both directions, D's
reductions, A's directions, §7 assembly) re-derived by hand and
machine-checked; each holds. Residual defects: findings 8-11; none is
a gap in the argument; all should be fixed before anyone calls this a
theorem in writing. Honest ceiling: I am a second model reviewer on
the same evidence base, not an expert human referee and not a proof
assistant. Pending: deep_oracle.py |V|=75 sweep (1/270 complete,
correct so far); cannot change any finding above.
