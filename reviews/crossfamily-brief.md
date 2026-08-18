# Cross-family adversarial review brief

You are reviewing a candidate NP-completeness proof as a hostile
referee. Your job is to refute it, not to admire it. You are the first
NON-Claude-family reviewer; two Claude-family reviews already ran (the
first refuted an earlier draft's key lemma; the second could not break
this rewrite). Do not trust their conclusions; re-derive everything
yourself from the document alone.

TARGET DOCUMENT: scratch/mc-radius3-theorem.md
(claim: MATCHING CUT is NP-complete on bipartite graphs of radius
exactly 3 — the open case of arXiv:2501.08735, Open Problem 1).

Construction source of truth if the prose is ambiguous:
tools/guarded_reduction.py (function build_guarded_graph).

Focus your effort where a paper referee would:
1. The case analysis in section 4 (Claims 4.1-4.4): is the branch list
   really exhaustive? Does any branch have an escape the forced-chain
   argument misses? Is the WLOG sound?
2. Lemma B' in section 5, both directions: any colouring the set
   abstraction misses, or set solution that fails to colour?
3. Lemma D (the bridge): do the three structural facts really hold for
   every formula shape (repeated literals, variables absent from all
   clauses, single-variable formulas)?
4. Lemma A in section 6: any ISLAND solution of the constructed
   instance that does not read off a satisfying assignment? Check the
   degenerate seeds.
5. Section 3: are bipartiteness and radius-exactly-3 actually proven
   for all n >= 1, m >= 1, or only asserted?
6. Anything the document assumes silently.

Deliver: a numbered list of findings, each labeled REFUTED (with a
concrete counterexample — an explicit small formula or graph and the
violating colouring/set), SUSPICIOUS (a stated gap you could not
convert to a counterexample), or HOLDS (with what you attacked). End
with a verdict: does the document contain a correct proof of the
theorem as stated? Be terse. Genuine holes are the only currency here;
politeness is worthless.
