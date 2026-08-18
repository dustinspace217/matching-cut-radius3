--- 9 assistant text blocks; LAST one below ---
All attacks are complete; two supplementary runs are still going (details at the end). Here is the report.

---

# Adversarial review — Block 9 (Lemma 9A, Lemma 9B, guarded reduction)

My scripts are in `/tmp/claude/pvnp/`; every command below is reproducible from there. I reproduced all four published checks first as a baseline: `sol_set_reduction.py` → `tested 4784; mismatches 0`; `guarded_exhaustive.py` → `tested 72; mismatches 0`; `verify_reformulation.py` → `graphs=27462 mismatches=0`; `guarded_reduction.py` (default battery, which the note left "running") → `tested 200; mismatches 0; timeouts 0`.

## 1. Lemma 9B as stated in the note — REFUTED

The note says: *"case-A1 colourings … exist iff the derived ISLAND instance (X = selectable L2, Z = L3, groups = shared-witness classes) is YES."* With ISLAND as defined in §9.2 and implemented in `set_problem.py`, this is false. `set_problem.py` lines 19-22 state that unselectable L2 vertices are modeled "by simply not listing [them] in any group" — but in the graph, β counts **all** L2 neighbours of z, and γ must hold **at** unselectable L2 vertices. The abstraction drops both constraints.

Counterexample, 9 vertices, bipartite, radius 3 (`/tmp/claude/pvnp/lemma9b_attack.py`):

```
u–w1, u–w2, u–w3, u–w4;  w1–v;  w2–y1, w3–y1;  w3–y2, w4–y2;  z–v, z–y1, z–y2
```

`v` is the only selectable L2 vertex; `y1` and `y2` each have two L1 neighbours. Output:

```
GROUND TRUTH case-A1 exists (all colourings): False
verify_reformulation's set criterion (beta/gamma over ALL L2): False
derived ISLAND per the note: groups=[('v',)]  zadj={'z': ('v',)}
ISLAND (set_problem.solve_bruteforce) says: YES frozenset({'v'})
*** LEMMA 9B AS STATED IS REFUTED: ISLAND=YES but case-A1=False ***
```

B={v} passes ISLAND-β (zero *listed* vertices outside B), but in the graph z has two red L2 neighbours, y1 and y2, so z carries two cross edges.

Aggravating detail: the "machine 27,462/0 = verify_reformulation.py" citation attached to 9B points at a **different statement**. `verify_reformulation.py:71-77` ranges β and γ over all of `L2`, not over X. That version is correct and reproduces green. **Lemma 9B in the form the note writes it has never been machine-checked.**

Blast radius — it does not reach the guarded reduction. `struct.py` shows the ISLAND instance derived from the guarded graph is identical to `build_set_instance`'s (`same_groups=True, same_z=True`) plus one empty row for Zk, because every unselectable L2 vertex there (guards, ballast) has exactly one L3 neighbour and every base z has an all-selectable L2 neighbourhood. `propagate.py`: 1500 formulas at n≤5, m≤6, with `island(base) == graph-A1(guarded) == SAT`, zero divergences. The note's Corollary (case-A1 is NP-complete) is also rescuable, since Sol's unguarded graph has no unselectable L2 vertices at all — but its proof as written rests on the false lemma.

## 2. Lemma 9A — HOLDS

Attacked with a CNF+DPLL ISLAND solver I validated against `set_problem.solve_bruteforce` on 4000 random instances (`island_sat.py`, 0 disagreements), then run far past the published battery (`big9a.py`):

- m = 0 (no clauses) for n = 0..4
- exhaustive 2-clause formulas over n=1 and n=2, all variable tuples with repeats, all sign patterns — 4165 instances, 342 UNSAT
- exhaustive 3-clause formulas over n=1
- 4000 random formulas at n≤6, m≤8 with **unrestricted** variable choice, so variables occurring in no clause and all-same-variable clauses actually appear. The published `random_formula` samples distinct variables per clause and can never generate either shape.

`TOTAL tested=8677 UNSAT=1979 mismatches=0`.

I also walked the ⇒ sketch by hand against the degenerate solutions you named. Proxies selected without their base: both copies of that proxy become touched, so the outside base has two touched neighbours and γ fails. Bases selected without `a`: the gate has {a, partner} outside and the partner is α-blocked, so β fails. Empty-interaction seeds: B nonempty forces a ∈ B in all three cases, and B={a} alone dies at β on any gate. Repeated literals are per-position, so no copy or proxy is ever shared. No slack found in β or γ.

## 3. Guarded reduction, case-B analysis — HOLDS as mathematics; one branch is argued wrongly in the docstring

The five L1 families are `q_i`, `w_a`, `w_p`, the ballast witnesses `wT*`, and the guard privates `wp_W`. Four die exactly as the docstring claims: the guard is forced blue, its other L1 witness consumes its budget, Zk is forced blue, and both T1 and T2 are red (neither of their witnesses is b), giving Zk two cross edges.

**The ballast branch names the wrong contradiction site.** Docstring: *"b = a T-witness: forces that T blue … forcing Z\* blue, which crosses the other T + all guards — invalid."* At that point Z\* has exactly **one** red neighbour (the other T); the guards are **forced blue**, not crossing. The real contradiction is at each guard, which then has two red L1 witnesses. The branch still dies, and it silently needs at least one guard to exist (true — there is always at least one base witness).

Also unstated: why at most one L1 vertex can be blue when u is red. It follows from u's own budget, but the docstring simply asserts "the unique blue L1 vertex".

Machine evidence via a case-decomposed exact analyzer (`decomp.py`, `scale_guard.py`) that searches case B per candidate b with the rest of L1 pinned red — complete for case B: 3400 formulas (400 at n≤4/m≤5, 3000 at n≤6/m≤10), 1404 UNSAT, **0 mismatches, 0 case-B survivors, 0 case-A0 alive**.

Control that this detector is not vacuous (`control_fast.py`) — on the **unguarded** graph it reproduces the Block-8 spurious cuts on the same formulas:

```
UNGUARDED n=1 sat=False A1=False A0=False B=['q0','w_a','w_p_0_2','w_p_1_0'] -> mc=True  <-- SPURIOUS
GUARDED   n=1 sat=False A1=False A0=False B=[] -> mc=False
```

Mutation test showing the harness detects a broken battery (`sens_fast.py`):

```
ORIGINAL guarded                mismatches=  0 caseB-alive=  0
MUTANT: guards only for q_i     mismatches= 18 caseB-alive= 40
MUTANT: no guards at all        mismatches= 18 caseB-alive= 40
MUTANT: killer Zk disconnected  mismatches= 18 caseB-alive= 40
MUTANT: one ballast only        mismatches=  0 caseB-alive=  0
```

The last row is a design observation, not a defect: T2 is redundant whenever there are at least two guards.

## 4. Guards blocking a legitimate case-A solution — HOLDS

Guards and ballast are double-witnessed, hence unselectable, so X is unchanged; Zk's row in the derived instance is empty; guards and ballast have exactly one L3 neighbour each, so γ is vacuous at them; and no base z gains a neighbour. Machine: `struct.py` (identical derived instances across n,m ∈ {1,2,3}²), `propagate.py` (1500 formulas, 0 divergences), plus every SAT instance in every battery returned mc=True.

## 5. Case A0 impossible — HOLDS

`minL3deg=2` in every structural audit (gates 3, copies 2, clause vertices 3, Zk = 2 + #base-witnesses ≥ 3), and `caseA0` never fired across 3400+ instances including the degenerate `m=1, n=2` gate-only-variable shape. The necessity direction is sound too: a blue set inside L3 is independent, since L3–L3 edges are impossible in a bipartite layering, so each blue z would need degree ≤ 1.

## 6. WLOG "u red" — HOLDS

Both checkers define a matching cut as "both colours used, every vertex has at most one cross neighbour", which is invariant under R↔B swap, so the swap is a bijection on valid colourings and no u-blue colouring escapes the case analysis. Machine-confirmed on a 37-vertex guarded graph (`wlog.py`): 4 valid colourings total, `colour-swap closed: True`, `u-blue colourings: 2, all swaps present: True`, and both u-red colourings are case A with `blueL1=0`.

## 7. Source problem NP-hardness — HOLDS

`schaefer_check.py` reproduced: 0-valid, 1-valid, Horn, dual-Horn, affine, and bijunctive all fail for the literal-closed language. Worth spelling out in a write-up: R itself *is* closed under OR (dual-Horn); it is the signed variants that break it, so the hardness depends on negations being available.

## 8. Bipartiteness and radius 3 are asserted per instance, never proved — SUSPICIOUS

`guarded_reduction.py:119-129` checks bipartite, connected, and radius per instance and aborts otherwise. There is no written argument that this holds for all (n,m), which a reduction needs, since an instance falling outside radius 3 would land in a different and already-resolved cell. Empirically it is radius 3, **diameter 5-6**, with exactly one center (u), across every shape I audited. Diameter above 3 is fine here — the open cell is radius-3 with diameter unconstrained.

## 9. Evidence scaling limit — SUSPICIOUS

The independent oracle is the only theory-free instrument and it does not scale: `oracle_big.py` (n≤3, m≤3, 300M-node budget) hit `TIMEOUT n=3 m=3 sat=False |V|=87` and needed 423s for its first 25 instances. Theory-free coverage therefore tops out at:

- the published default battery at n≤2/m≤2 — 200 tested, 0 mismatches, 0 timeouts, 178 SAT / 22 UNSAT
- `exh64.py` — **all 64** n=1 two-clause guarded graphs at |V|=56, 18 of them UNSAT, 0 mismatches, 20s
- `oracle_unsat.py` — all 18 UNSAT n=1 two-clause instances plus an UNSAT n=2 with an unused variable, 0 spurious cuts
- `attack.py` — complete enumeration of **every** valid colouring of a 56-vertex UNSAT guarded graph, finding zero

Everything beyond that (the 3400-instance sweep) rests on the case decomposition, which is itself part of the theory under test. I cross-validated it against the oracle on all 64 |V|=56 guarded graphs (`xcheck64.py`, 0 disagreements) and against `caseA1`'s brute force (`0 disagreements` on 120 graphs), but that is validation-by-agreement, not independence.

## 10. `guarded_exhaustive.py` is vacuous on the direction that killed Block 8 — SUSPICIOUS (methodological)

All 72 of its formulas are satisfiable, because every single signed NOT-1-IN-3 clause is satisfiable, so a single-clause battery cannot contain an UNSAT case. Its docstring claims it covers "the degenerate shapes … where constructions usually break", but Block 8's 50 defects were all `sat=False & mc=True`, and this battery contains zero `sat=False` instances. Measured directly (`comp1.py`): `guarded_exhaustive battery: SAT=72 UNSAT=0`. Replacement written and run: `/tmp/claude/pvnp/exh64.py`.

---

## Overall verdict

**Machine level: survives.** I attacked it with a complete case decomposition, a mutation-tested harness, an UNSAT-focused battery the note never ran, exhaustive colouring enumeration of a full 56-vertex UNSAT instance, and 3400 formulas out to n=6/m=10. Zero counterexamples, zero case-B survivors, and the harness demonstrably catches three deliberately broken variants of the guard battery.

**Proof level: does not survive as written.** Lemma 9B is false in the generality the note states, and the 27,462/0 verification cited for it checks a different statement, so the chain 9A → 9B → corollary → guarded reduction has a broken link. The defect is scoping rather than substance: replacing "ISLAND with X = selectable L2" by the β/γ-over-all-L2 formulation that `verify_reformulation.py` actually checks repairs it, and the guarded construction satisfies the extra hypotheses (verified, not assumed). On top of that: the mis-stated ballast branch, the unstated uniqueness argument for the blue L1 vertex, and no proof that the construction is bipartite and radius-3 for all (n,m).

So the answer is neither "both" nor "neither" — machine yes, written proof no. Nothing I found suggests the claim is wrong; what I found is that the artifact does not yet contain a proof of it. Before this is called a result, the note needs 9B restated and reproved, the ballast branch rewritten, and the structural properties proved rather than asserted — and the verification contract's remaining items (independent adversarial review of the *rewritten* proof, same-day literature re-check) are still outstanding. I would not move confidence past "promising and unrefuted" on the strength of this review.

## Still running (both supplementary; neither can change a finding)

- `oracle_big.py` — independent oracle at n≤3/m≤3. Already produced its useful result, the `|V|=87` timeout that establishes finding 9. Its coverage role was taken over by `exh64.py` and `xcheck64.py`, which completed green.
- `control.py` — the slow full version of the leak-reproduction control. Superseded by `control_fast.py`, which completed and is quoted in finding 3.
