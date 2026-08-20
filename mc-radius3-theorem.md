# Matching Cut on bipartite graphs of radius 3: NP-completeness

**Status: CANDIDATE THEOREM — four adversarial model reviews across
three model families, zero unrepaired mathematical findings.
Review 1 (Claude; scratch/block9-adversarial-review.md) refuted the
FIRST write-up's Lemma B scoping while finding zero counterexamples to
the construction; this document is the rewrite repairing all five of
its findings. Review 2 (Claude, fresh context;
scratch/block10-adversarial-review.md), on THIS document: "Machine
level: survives, with new coverage. Proof level: I could not break
it" — its four residual editorial/scoping findings incorporated.
Review 3 (Gemini 3.1 Pro; scratch/crossfamily-gemini-reply.md):
six findings, all HOLDS — "The document contains a correct proof of
the theorem as stated." Review 4 (Kimi K3;
scratch/crossfamily-kimi-reply.md): same verdict; one prose finding
(an unstated BFS premise in Lemma B'(⇒)), repaired in Observation 5.0.
Sol (GPT-5.6) was deliberately NOT seated as referee: he authored the
base construction (§2's unguarded core), a conflict for this joint.
NOT yet a theorem for citation: no human expert review, no proof
assistant. Those are the named next escalations, and they are the
real referees — four model reviews are strong evidence, not proof
of a proof.**

Grades per project convention: statements below are [synthesis] unless
marked. Machine evidence is catalogued in §8.

## 0. Problem and result

MATCHING CUT: given graph G, is there a partition of V(G) into two
nonempty classes such that the edges joining the classes form a
matching? Equivalently: a red/blue coloring using both colors in
which every vertex has at most one neighbor of the opposite color
("budget ≤ 1 cross edge per vertex"). We use the coloring form
throughout; the two forms are trivially equivalent (the cut edges at a
vertex are exactly its cross edges).

Known (Lucke, Martin, Paulusma, Siggers, arXiv:2501.08735, Table 1)
[verified, primary]: on bipartite graphs, MATCHING CUT is polynomial
for radius ≤ 2 and diameter ≤ 3, NP-complete for radius ≥ 4 and
diameter ≥ 4; radius 3 is posed as Open Problem 1. Fresh literature
check 2026-08-16: still open (the Feb-2025 Minimum-Matching-Cut paper
2502.18942 does not touch the decision cell).

**Theorem.** MATCHING CUT is NP-complete on bipartite graphs of radius
exactly 3.

Membership in NP is trivial (the coloring is a certificate). Hardness
is by reduction from SIGNED NOT-1-IN-3-SAT (§1), via the construction
G(F) of §2. The proof has four independent parts:
- §3: G(F) is bipartite, connected, radius exactly 3, size O(n+m);
- §4: structure of valid colorings — WLOG u red; case split A1/A0/B;
  A0 and B are impossible for G(F);
- §5: case A1 exists iff the derived set problem has a solution
  (Lemma B', the corrected reformulation) and the derived set problem
  of G(F) coincides with ISLAND(I(F)) (Lemma D);
- §6: ISLAND(I(F)) is solvable iff F is satisfiable (Lemma A).

## 1. Source problem

SIGNED NOT-1-IN-3-SAT: variables x_1..x_n; each clause is an ordered
triple of literals (l_1,l_2,l_3) (repeats allowed, both within and
across clauses); the clause is satisfied iff the number of TRUE
literals among its three positions is ≠ 1 (i.e. ∈ {0,2,3}).
We take the problem RESTRICTED to instances with n ≥ 1 and m ≥ 1;
this restriction is still NP-complete: the general problem reduces to
it by mapping any instance with m = 0 or n = 0 — such instances are
always satisfiable (the empty conjunction; resp. no variables to
constrain) — to the fixed satisfiable restricted instance consisting
of the single clause (x_1, x_1, x_1) (true count 0 or 3, never 1).
The graph reduction below is defined exactly on the restricted
instances, so no fixed NO-instance is ever needed.

NP-completeness [verified mechanically, tools/schaefer_check.py]: the
constraint language {all sign-patterns of R(a,b,c): a+b+c ≠ 1} escapes
all six Schaefer tractable classes (0-valid, 1-valid, Horn, dual-Horn,
affine, bijunctive), so CSP over it is NP-complete by Schaefer's
dichotomy [textbook]. Note the signs are essential: R itself is
dual-Horn (closed under OR); the signed variants break it.

## 2. The construction G(F)

Vertex set, in four layers (the names L0..L3 will be justified in §3):

- L0: the center u.
- L1 ("witnesses"), all adjacent to u and to nothing else except as
  listed:
  - q_i for each variable i (the SHARED witness of the variable pair);
  - w_a (witness of the anchor);
  - w_p for each occurrence position p = (C,j), C a clause, j ∈ {1,2,3}
    (witness of the proxy p);
  - w'_W for each W ∈ BW := {q_1..q_n, w_a, all w_p} (the guard's
    second witness);
  - wT1a, wT1b, wT2a, wT2b (ballast witnesses).
- L2:
  - the anchor a; literal vertices t_i, f_i; proxy vertices p = p_{C,j};
  - guard G_W for each W ∈ BW; ballast T1, T2.
- L3:
  - gates g_i; copies c_{C,j,0}, c_{C,j,1}; clause vertices z_C;
  - the killer Zk.

Edges:
- u ~ every L1 vertex (and nothing else).
- L1–L2: q_i ~ t_i, f_i, G_{q_i};  w_a ~ a, G_{w_a};  w_p ~ p, G_{w_p};
  w'_W ~ G_W;  wT1a, wT1b ~ T1;  wT2a, wT2b ~ T2.
- L2–L3: g_i ~ a, t_i, f_i;  c_{C,j,k} ~ base(l_{C,j}) and p_{C,j}
  for k ∈ {0,1}, where base(x_i) = t_i and base(¬x_i) = f_i;
  z_C ~ p_{C,1}, p_{C,2}, p_{C,3};  Zk ~ T1, T2, and every G_W.

There are no other edges. Builder: tools/guarded_reduction.py
(build_guarded_graph). |V| = 6n + 19m + 12: each variable contributes
{q_i, w'_{q_i}, G_{q_i}, t_i, f_i, g_i} (6); each clause contributes
three positions × {w_p, w'_{w_p}, G_{w_p}, p, c_0, c_1} plus z_C (19);
the constants are u, w_a, w'_{w_a}, G_{w_a}, a, the four ballast
witnesses, T1, T2, Zk (12). (Machine-confirmed: 37, 43, 56, 62, 75 for
(n,m) = (1,1), (2,1), (1,2), (2,2), (1,3).) Construction is linear
time.

Witness counts in L2 (used constantly below): a, t_i, f_i, p have
EXACTLY ONE L1-neighbor each (w_a; q_i; q_i; w_p). G_W has exactly two
(W, w'_W). T1, T2 have exactly two (their two ballast witnesses).

L3 degrees (used in §4, case A0): g_i has 3; c has 2; z_C has 3;
Zk has 2 + |BW| ≥ 2 + (n + 1 + 3m) ≥ 5. All ≥ 2.

## 3. Structural properties

**Claim 3.1 (bipartite).** Parts: A := {u} ∪ L2 and B := L1 ∪ L3.
Every edge listed in §2 joins A to B: u–L1 edges join A to B; L1–L2
edges join B to A; L2–L3 edges join A to B. There are no u–L2, u–L3,
L1–L1, L1–L3, L2–L2, or L3–L3 edges in the edge list. ∎

**Claim 3.2 (connected, ecc(u) = 3).** Every L1 vertex is adjacent
to u (distance 1). Every L2 vertex has an L1-neighbor (witness counts
above), so is at distance 2 (it is not adjacent to u: u's neighbors
are exactly L1). Every L3 vertex has an L2-neighbor (g_i ~ a; c ~ p;
z_C ~ p_{C,1}; Zk ~ T1) and no shorter connection (its neighbors are
all in L2 by §2, and it is not adjacent to u), so it is at distance 3.
L3 is nonempty (Zk). Hence G connected with ecc(u) = 3, and the labels
L0..L3 are exactly the BFS layers from u. ∎

**Claim 3.3 (no vertex has eccentricity ≤ 2; hence radius exactly 3).**
Distances between same-part vertices are even, cross-part odd
(Claim 3.1).
(i) v ∈ L3: u is in the other part, v is not adjacent to u (u's
neighbors are exactly L1), so dist(v,u) ≥ 3.
(ii) v ∈ L1: ecc ≤ 2 would force every A-vertex to be adjacent to v
(odd distance ≤ 2 means distance 1). But no L1 vertex is adjacent to
all of L2: every L1 vertex has at most 3 L2-neighbors (inspect §2:
q_i has 3; w_a, w_p have 2; w'_W has 1; ballast witnesses have 1),
while |L2| ≥ 4 (a, T1, T2, G_{w_a} always exist). So some L2 vertex is
at distance ≥ 3 from v.
(iii) v ∈ L2: ecc ≤ 2 would force v adjacent to every B-vertex, in
particular to every L1 vertex. But every L2 vertex has at most 2
L1-neighbors (witness counts above), while |L1| ≥ 5 (w_a and the four
ballast witnesses always exist). So some L1 vertex is at distance ≥ 3
from v.
(iv) u: ecc(u) = 3 by Claim 3.2.
Hence every vertex has eccentricity ≥ 3, and radius(G) = 3 exactly. ∎

## 4. Valid colorings: WLOG and case analysis

Fix any valid coloring χ (both colors used, every vertex ≤ 1 cross).

**WLOG u is red.** The color swap R↔B is an involution on valid
colorings (the definition is color-symmetric), so a valid coloring
exists iff one with χ(u) = R exists. We assume χ(u) = R from here on.

**Claim 4.1 (at most one blue L1 vertex).** u's cross edges are
exactly its edges to blue L1 vertices; budget ≤ 1. ∎

So exactly one of:
- **Case A** (all of L1 red), split into A1 (blue ∩ L2 ≠ ∅) and
  A0 (blue ∩ L2 = ∅);
- **Case B** (exactly one L1 vertex b is blue).

**Claim 4.2 (case A0 is impossible in G(F)).** In case A0, blue
⊆ L3 (u, L1, L2 are all red), and blue ≠ ∅ (both colors used). A blue
z ∈ L3 has all its neighbors in L2 (§2), all red, so it carries
deg(z) cross edges, forcing deg(z) ≤ 1. But every L3 vertex of G(F)
has degree ≥ 2 (§2). Contradiction. ∎

**Claim 4.3 (two red witnesses freeze a vertex).** If v ∈ L2 has two
L1-neighbors and both are red, then v is red: blue v would cross both
witnesses (2 > 1). ∎

**Claim 4.4 (case B is impossible in G(F)).** Let b be the unique blue
L1 vertex. b's cross edge to u (red) consumes b's budget, so EVERY
other neighbor of b is blue. By Claim 4.3, every L2 vertex whose two
witnesses both differ from b is red; in particular, in every branch
below, all guards G_W with b ∉ {W, w'_W} are red, and T1 (resp. T2) is
red unless b is one of its two ballast witnesses. We branch on b; the
list is exhaustive by the L1 inventory in §2.

1. b = W ∈ BW (a base witness q_i, w_a, or w_p). G_W ~ b, so G_W is
   blue. G_W's witnesses are W = b (blue) and w'_W (red): the cross to
   w'_W consumes G_W's budget, so G_W's remaining neighbor Zk is
   blue. Zk's neighbors are T1, T2, and every guard: T1, T2 are red
   (their witnesses are ballast witnesses ≠ b), and every OTHER guard
   G_{W'} (W' ≠ W) is red by Claim 4.3 (its witnesses W', w'_{W'} are
   both ≠ b). T1 and T2 alone already give Zk two cross edges.
   Contradiction.
2. b = w'_W (a guard's second witness). G_W ~ b is blue; its other
   witness W is red (W ∈ BW, and b = w'_W ≠ W); the cross to W
   consumes G_W's budget; Zk is blue; T1, T2 red as in branch 1;
   ≥ 2 crosses at Zk. Contradiction.
3. b ∈ {wT1a, wT1b} (T2 symmetric). T1 ~ b is blue. T1's other
   ballast witness is red; that cross consumes T1's budget; T1's
   remaining neighbor Zk is blue. Zk's neighbors T2 (red: its
   witnesses ≠ b) and every guard G_W (red by Claim 4.3: no guard has
   a ballast witness) give ≥ 2 crosses at Zk — already T2 plus any one
   guard, and at least one guard exists (G_{w_a}). Contradiction.

All branches are contradictory, so case B admits no valid coloring. ∎

Consequently: **G(F) has a matching cut iff it has a case-A1
coloring.**

## 5. Case A1 ⟺ the set problem

**Definitions.** For a connected bipartite graph G with a vertex u of
eccentricity 3 and BFS layers L0..L3 from u, let
S := {v ∈ L2 : |N(v) ∩ L1| = 1} (the "selectable" vertices) and let
w : S → L1 map v to its unique L1-neighbor.

**Observation 5.0 (layering).** Under these hypotheses, every edge of
G joins consecutive layers: same-layer edges are impossible (the BFS
layers of a bipartite graph alternate parts, so a same-layer edge
would lie inside one part); L0–L2 and L1–L3 edges are impossible for
the same reason; an L0–L3 edge would put an L3 vertex at distance 1;
and there is no L4 since ecc(u) = 3. Consequently: for z ∈ L3,
N(z) ⊆ L2; for W ∈ L1, N(W) ⊆ {u} ∪ L2; there are no L2–L2 edges; and
for v ∈ L2, N(v) ⊆ L1 ∪ L3. Moreover every v ∈ L2 has AT LEAST ONE
L1-neighbor (a BFS-layer-2 vertex has a neighbor at distance 1 from
u by definition), so "budget forces exactly one L1-neighbor" in
Lemma B'(⇒) is well-grounded: the budget gives ≤ 1 and the layering
gives ≥ 1. These facts are used throughout §5.

**Lemma B' (corrected reformulation).** [Machine verification, two
checks with jointly matching scope: tools/verify_reformulation.py —
27,462 radius-exactly-3 graphs, 0 mismatches — and the second review's
lemmaB_exhaustive.py (scratch/review-block10-scripts/), which sweeps
ALL connected bipartite graphs to n = 8 and EVERY center of
eccentricity 3, radius-3 or not: 69,816 graphs, 276,260
(graph, center) pairs, 0 mismatches. The lemma is stated for the
general ecc-3 hypothesis, which the second check covers; the proof of
the Theorem only ever applies it to G(F), where u realizes the radius
3.] G has a valid coloring
with u red, N(u) all red, and blue ∩ L2 ≠ ∅ **iff** there is a
nonempty B2 ⊆ S with:
  (α) w is injective on B2;
  (β') every z ∈ N(B2) ∩ L3 has |N(z) ∖ B2| ≤ 1, where N(z) is z's
       FULL L2-neighborhood — selectable or not;
  (γ') every v ∈ L2 ∖ B2 — selectable or not — has
       |N(v) ∩ N(B2) ∩ L3| ≤ 1.

[The Block-9 note stated this lemma with β, γ ranging over selectable
vertices only; the first adversarial review refuted that version with
a 9-vertex counterexample and observed that the machine check had
always verified THIS all-of-L2 version. This is the repair.]

Proof. (⇒) Let χ be such a coloring; put B2 := blue ∩ L2 ≠ ∅.
- Every v ∈ B2 has all its L1-neighbors red (hypothesis), each
  contributing a cross at v; budget forces exactly one L1-neighbor,
  so B2 ⊆ S, and v's budget is then exhausted, so every L3-neighbor
  of v is blue. Hence every z ∈ N(B2) ∩ L3 is blue.
- (α) A witness W ∈ L1 is red; each blue L2-neighbor of W is a cross
  at W; budget ≤ 1. Two B2-members sharing W would give 2.
- (β') A blue z ∈ L3 has crosses exactly at its red L2-neighbors
  (N(z) ⊆ L2); these include ALL of N(z) ∖ B2 (any L2 vertex outside
  B2 is red, whether selectable or not); budget ≤ 1.
- (γ') A red v ∈ L2 ∖ B2 has a cross at each blue L3-neighbor; the
  vertices of N(v) ∩ N(B2) ∩ L3 are all blue (first bullet);
  budget ≤ 1.
(⇐) Given such a B2, color blue exactly B2 ∪ (N(B2) ∩ L3), red
everything else. Check every vertex's budget:
- u: all neighbors (L1) red; 0 crosses.
- W ∈ L1: red; crosses = blue L2-neighbors = |N(W) ∩ B2| ≤ 1 by (α)
  (each B2-member has W as its unique witness, so two would share W).
- v ∈ B2: blue; crosses = red neighbors = the unique witness (red)
  plus red L3-neighbors; but N(v) ∩ L3 ⊆ N(B2) ∩ L3 is entirely
  blue; total 1.
- z ∈ N(B2) ∩ L3: blue; crosses = red L2-neighbors = |N(z) ∖ B2| ≤ 1
  by (β').
- v ∈ L2 ∖ B2: red; its neighbors are in L1 (red) and L3; blue
  L3-neighbors are exactly N(v) ∩ N(B2) ∩ L3 (nothing else in L3 is
  blue); ≤ 1 by (γ').
- z ∈ L3 ∖ N(B2): red; its neighbors are in L2; blue ones would be
  in B2 ∩ N(z) = ∅ (z ∉ N(B2)); 0 crosses.
Both colors are used (u red, B2 ≠ ∅ blue). ∎

**The ISLAND problem.** Instance: bipartite graph (X, Z), partition of
X into groups. Question: is there a nonempty B ⊆ X, at most one member
per group, with (β) every z ∈ N(B) having ≤ 1 neighbor outside B and
(γ) every x ∈ X ∖ B having ≤ 1 neighbor in N(B)? (Here neighborhoods
are in the (X,Z) graph; X plays the role of the selectable vertices.)

**Lemma D (bridge; G(F)-specific).** Apply Lemma B' to G(F). Then
S = {a} ∪ {t_i, f_i} ∪ {proxies p} exactly (each has one witness, §2;
guards and ballast have two), the group partition of S induced by w is
{{t_i, f_i}} ∪ {{a}} ∪ {{p}} (q_i serves t_i and f_i; w_a serves a;
w_p serves p; note G_{q_i} is ALSO a neighbor of q_i but is not in S,
so it joins no group), and conditions (β'), (γ') on G(F) reduce to
ISLAND's (β), (γ) on the instance I(F) := (X = S, Z-side = the base
L3 vertices {g_i, c, z_C}, groups as above):
- (β' = β): the L3 vertices reachable from B2 ⊆ S are base vertices
  only (Zk's L2-neighbors are guards and ballast, none in S), and
  every base L3 vertex has ALL its L2-neighbors in S (g_i ~ a,t_i,f_i;
  c ~ base, proxy; z_C ~ proxies — §2), so "N(z) ∖ B2 over all L2" =
  "N(z) ∖ B over X".
- (γ' = γ): for v ∈ S ∖ B2 the two conditions are verbatim identical
  (v's L3-neighborhood consists of base vertices). For v ∈ L2 ∖ S
  (guards, ballast): N(v) ∩ L3 = {Zk}, and Zk ∉ N(B2) as above, so
  (γ') holds vacuously at v.
Hence: G(F) has a case-A1 coloring iff ISLAND(I(F)) is YES. ∎

## 6. ISLAND(I(F)) ⟺ F satisfiable

**Lemma A [first review: HOLDS; machine 8,677 instances incl. 1,979
UNSAT, plus shapes outside the original generator].** For the instance
I(F) (equivalently built directly by tools/sol_set_reduction.py:
X = {a} ∪ {t_i,f_i} ∪ {p_{C,j}}; groups {t_i,f_i} shared, others
singleton; Z: g_i ~ (a,t_i,f_i); c_{C,j,k} ~ (base(l_{C,j}), p_{C,j}),
k ∈ {0,1}; z_C ~ (p_{C,1},p_{C,2},p_{C,3})):
ISLAND(I(F)) is YES iff F is satisfiable.

Proof. (⇐) Given a satisfying assignment σ, take
B := {a} ∪ {t_i : σ(x_i)=1} ∪ {f_i : σ(x_i)=0}
      ∪ {p_{C,j} : σ(l_{C,j})=1}.
(α): one literal per variable group; singletons. Touched z's: every
g_i (a ∈ B) has exactly one of t_i,f_i outside (1); a copy c_{C,j,k}
is touched iff base or proxy ∈ B, and by construction of B, proxy ∈ B
iff σ(l)=1 iff base ∈ B, so touched copies have 0 outside; z_C is
touched iff its clause has t_C ≥ 1 true positions, and then has
3 − t_C ≤ 1 outside since t_C ∈ {0,2,3} (σ satisfies C). (γ): an
unselected literal vertex sees only its gate among touched z's (its
occurrence copies are untouched: base ∉ B and proxy ∉ B); an
unselected proxy sees at most z_C (its copies are untouched); a is
in B. So B is a solution.
(⇒) Let B be any solution.
1. Selected proxy ⇒ its base selected: p ∈ B touches both copies
   c_{p,0}, c_{p,1}; if base(p) ∉ B then base(p) is an X-vertex
   outside B with TWO touched neighbors — (γ) violated.
2. Selected base ⇒ a selected: t_i ∈ B touches g_i; f_i ∉ B by (α);
   if a ∉ B then g_i has two neighbors outside B — (β) violated.
   (Symmetrically for f_i ∈ B.)
3. B ≠ ∅ ⇒ a ∈ B: any member is a, a base (→2), or a proxy (→1→2).
4. a ∈ B ⇒ full assignment: every g_i is touched, so ≤ 1 of {t_i,f_i}
   is outside B (β), i.e. ≥ 1 selected; (α) gives ≤ 1; define
   σ(x_i) := 1 iff t_i ∈ B.
5. Selected base ⇒ its proxies selected: base ∈ B touches both copies
   of each of its occurrences; an unselected proxy of such an
   occurrence would have two touched neighbors — (γ). With step 1:
   p_{C,j} ∈ B ⟺ base(l_{C,j}) ∈ B ⟺ σ(l_{C,j}) = 1.
6. Clause satisfaction: the touched z_C has ≤ 1 of its three proxies
   outside B (β), so t_C ≥ 2; an untouched z_C has t_C = 0. Either
   way t_C ≠ 1: σ satisfies every clause.
Repeated literals are unproblematic: proxies and copies are
per-position objects. ∎

## 7. Assembling the theorem

For n ≥ 1, m ≥ 1: G(F) is constructible in polynomial time (§2),
bipartite (3.1), connected of radius exactly 3 (3.2, 3.3). It has a
matching cut iff a case-A1 coloring exists (§4: WLOG u red; A0 dies
by 4.2, B by 4.4) iff ISLAND(I(F)) is YES (§5: B' + D) iff F is
satisfiable (§6). Source problem NP-complete (§1). Membership in NP
trivial. Hence MATCHING CUT on bipartite graphs of radius exactly 3
is NP-complete. This resolves half of Open Problem 1 of
arXiv:2501.08735 (the DISCONNECTED PERFECT MATCHING radius-3 case
remains open; the paper's radius-≥4 DPM hardness and this
construction's compatibility with DPM have not been examined).

## 8. Machine evidence (all code in tools/, logs in scratch/)

- Independent oracle (independent_mc.py, plain exhaustive backtracking,
  validated 3,000/0 against a second brute-forcer): random batteries
  60+120+81 (19 timeouts recorded as unknowns), 0 mismatches; the
  first review added: all 64 n=1 two-clause guarded graphs (18 UNSAT):
  0 mismatches; complete enumeration of every valid coloring of a
  56-vertex UNSAT instance: none exist.
- UNSAT-focused: 32 + 52 (dual-instrument agreement, exact_layered ∧
  independent_mc) + reviewer's 1,404 (case-decomposed) — 0 spurious
  cuts anywhere, 0 instrument disagreements.
- Set level: 4,784 formulas (374 UNSAT) exhaustive+random, 0
  mismatches; review extended to 8,677 (1,979 UNSAT) incl. unused
  variables and all-same-variable clauses: 0.
- Mutation tests (review): guards removed / killer disconnected →
  18 mismatches + 40 case-B survivors on the same battery; intact
  construction → 0. The batteries demonstrably detect broken variants.
- Reformulation (Lemma B', all-L2 form): 27,462 graphs / 0 mismatches.
- Case-B impossibility + A0 impossibility: 3,400 formulas via complete
  case decomposition: 0 case-B survivors, 0 A0.
- Structural claims 3.1-3.3: asserted programmatically on every
  instance of every battery (bipartite, connected, radius exactly 3);
  0 violations.
- Second review (scratch/review-block10-scripts/), all fresh code:
  independent structural audit incl. DIAMETER ≥ 4 (excluding the
  known-poly diameter-≤3 cell), 475 instances, 0 failures; Lemma B'
  transcribed from this document and checked on 276,260
  (graph, center) pairs over ALL connected bipartite graphs to n=8
  with any ecc-3 center, 0 mismatches; the Block-9 counterexample
  correctly rejected by B'; graph-derived bridge with a fresh ISLAND
  brute force, 700 instances (351 UNSAT), 0; exhaustive case-B
  completion over EVERY b on 132 instances, 0 survivors; complete
  valid-coloring enumeration of six guarded graphs to |V|=62 (all
  colorings are A1; UNSAT instances have none); fresh-seed e2e 163
  instances, 0 mismatches, 0 timeouts; theory-free slice at |V|=75;
  mutation controls (guards removed / killer detached) each caught.

## 9. Honest limits

- The theory-free oracle scales only to |V| ≈ 87; wider sweeps rest on
  the case-decomposed analyzer, cross-validated against the oracle
  (0/64 disagreements) but not independent of the theory.
- This document has passed no expert human review. Both adversarial
  reviews were Claude-family models: review 1 refuted the previous
  write-up's Lemma B scoping (repaired, §5); review 2 could not break
  the rewritten proof at either level but states its own ceiling
  plainly ("a second model reviewer working the same evidence base,
  not an expert human referee and not a proof assistant"). A
  cross-family model review is the next cheap escalation; expert human
  review and Lean formalization are the real referees.
- The two reviews disagreed once — review 1 called the ballast-branch
  argument wrong, review 2 judged review 1's objection itself
  incorrect and this document's branch 3 correct. The disagreement is
  settled by the written argument (Claim 4.3 pins guards red; machine:
  0 case-B survivors over every b, 132 instances) — but it is a live
  reminder that model reviews are fallible in both directions.
- Formalization (Lean) would be the referee that cannot be flattered;
  not attempted for this artifact yet.
