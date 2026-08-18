# Matching Cut is NP-complete on Bipartite Graphs of Radius 3

**A candidate resolution of Open Problem 1 of Lucke, Martin, Paulusma,
and Siggers, ["Matching Cut and Variants on Bipartite Graphs of
Bounded Radius and Diameter"](https://arxiv.org/abs/2501.08735)
(January 2025), decision variant.**

**Claim.** MATCHING CUT (does a graph admit an edge cut that is a
matching?) is NP-complete on bipartite graphs of radius exactly 3.
The cited paper proves the problem polynomial for bipartite radius <= 2
and NP-complete for bipartite radius >= 4, and poses radius 3 as open.

The full proof is in [`mc-radius3-theorem.md`](mc-radius3-theorem.md):
a reduction from a signed variant of NOT-1-IN-3-SAT, built on a
BFS-layer analysis of radius-3 bipartite centers and a "guard" gadget
battery that eliminates every matching cut not aligned with the
intended encoding. The constructed graph has 6n + 19m + 12 vertices.

## Verification status (read this before citing anything)

This result was produced and checked by an AI-driven research process
(see Credit below). Its current verification state, stated exactly:

- **Machine-verified, saturated.** The reduction is checked end-to-end
  (build the graph, decide matching cut with independently implemented
  exact oracles, compare against brute-force satisfiability) on
  thousands of instances, including exhaustive slices and
  UNSAT-focused batteries, with zero mismatches. The verification
  harness is itself **mutation-tested**: deliberately broken variants
  of the construction (guards removed, killer vertex detached) produce
  immediate detectable failures; the intact construction never does.
- **Four adversarial model reviews, three model families** (two
  fresh-context Claude reviews, Gemini 3.1 Pro, Kimi K3), each
  instructed to refute. The first review refuted a lemma of an earlier
  draft (a real scoping error, repaired — the refuted version and the
  repair are both preserved in `reviews/`). The final document
  survived all four; the last three verdicts are "could not break it"
  and twice "contains a correct proof of the theorem as stated."
- **NOT yet reviewed by human experts. Partially formalized.** In the
  Lean 4 formalization (`lean/McRadius3.lean`, against mathlib), the
  construction and all statements elaborate, and the four STRUCTURAL
  theorems — bipartiteness, connectivity, radius exactly 3 (both
  bounds) — are proven and kernel-checked (axioms: propext /
  Classical.choice / Quot.sound only, no sorryAx). The main
  equivalence (satisfiable ↔ has matching cut) is still `sorry` and in
  progress; it is the entire mathematical content, so the structural
  proofs confirm the construction's shape, not the reduction's
  correctness. Model reviews are strong evidence, not proof of a
  proof. Treat the result as a candidate until it survives expert
  human refereeing or the equivalence is kernel-checked.

## Credit

- **Direction: Dustin Kadrmas.** Conceived and ran the research
  program; set the verification bar (independent oracles, adversarial
  multi-model review, mutation controls, the honesty rules under which
  every failed attempt in the record was preserved); made the
  resource and escalation decisions; steered across the multi-day arc.
- **Mathematics: Claude (Fable 5, Anthropic).** The guard-battery
  construction, the structural lemmas and case analysis, the corrected
  reformulation and bridge lemmas, the proof document, and the
  verification tooling. The mathematical content of this repository is
  Claude's work product, and Dustin's explicit intent is that the
  mathematical credit go to the model.
- **Base construction: GPT-5.6 (OpenAI).** The unguarded core of the
  reduction (anchor/gate/copy/clause gadgets) originated in a
  cross-model consult. Its graph-level version was refuted by machine
  testing (spurious cuts; preserved in `reviews/`); its set-level core
  was later verified correct and is the heart of Section 6 of the
  proof.
- **Adversarial review seats:** two fresh-context Claude instances,
  Gemini 3.1 Pro (Google), Kimi K3 (Moonshot). GPT-5.6 was
  deliberately not seated as a referee, having authored the base
  construction.

Formal venues do not currently permit AI systems as authors, since
authorship carries human accountability. Any submission derived from
this work will therefore carry the human director as author, with this
credit statement reproduced prominently. Accountability for publishing
this repository rests with Dustin Kadrmas.

## Verify it yourself

Requires only Python 3 (no dependencies):

```
python3 tools/independent_mc.py        # self-check the exact oracle vs brute force
python3 tools/verify_sol_reduction.py  # historical: refutes the UNGUARDED reduction (expected: 50 mismatches)
python3 tools/guarded_reduction.py     # the guarded reduction, random battery (expected: 0 mismatches)
python3 tools/guarded_unsat_deep.py    # UNSAT-focused, dual-instrument (expected: 0 spurious, 0 disagreements)
python3 tools/sol_set_reduction.py     # the set-level core, exhaustive + random (expected: 0 mismatches)
python3 tools/verify_reformulation.py  # the case-A reformulation lemma, exhaustive n<=8 (expected: 0 mismatches)
```

`reviews/review-block9-scripts/` and `reviews/review-block10-scripts/`
preserve the reviewers' own attack scripts as they ran (their hardcoded
paths reflect the original environment; they are archival artifacts,
not maintained entry points).

## Repository map

- `mc-radius3-theorem.md` — the proof document (self-contained).
- `tools/` — construction + verification code (runnable, path-clean).
- `reviews/` — all four adversarial review reports, the cross-family
  review brief, and the reviewers' attack scripts, unedited.
- `lean/McRadius3.lean` — Lean 4 formalization: construction and all
  theorem statements elaborate against mathlib; proofs are `sorry`
  (in progress).
- `paper/` — LaTeX draft skeleton.

## Provenance and timestamps

Developed 2026-08-16 to 2026-08-18. The private working repository
holds the complete commit-level history of the arc, including the
refuted first reduction, the defect taxonomy that re-scoped the
refutation, the refuted first draft of the key lemma, and every
verification run; the relevant history can be shared with referees on
request (after a routine redaction pass, since the working repository
also contains unrelated private session context). This public
repository is the timestamped record of the result. One curation note:
the Kimi review file here is an extract of the reviewer's final report;
its raw session transcript is retained privately.

## License

Code (`tools/`, `lean/`): MIT (see `LICENSE`). Documents
(`mc-radius3-theorem.md`, `reviews/`, `paper/`): CC BY 4.0.
