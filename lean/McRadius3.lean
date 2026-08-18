/-
McRadius3: Phase 10 formalization.

Formalization target (plan.md Phase 10): the combinatorial core of
scratch/mc-radius3-theorem.md —
  T1  the guarded construction G(F) as a SimpleGraph;
  T2  structural lemmas (bipartite, connected, radius exactly 3);
  T3  the equivalence: G(F) has a matching cut ↔ F is satisfiable.

Status: T2 and T3 are proved. The file contains no `sorry`, and
`#print axioms` on every theorem shows only propext / Classical.choice /
Quot.sound. Machine-checked: G(F) is bipartite, connected, of radius
exactly 3, and has a matching cut iff F is satisfiable — §3 through §6
of the note.

NOT established here, and both needed before the NP-completeness claim
follows: that SIGNED NOT-1-IN-3-SAT is NP-complete (Schaefer, §1 of the
note), and that the reduction is polynomial-time (visibly size-linear,
but this file contains no complexity-theoretic content whatsoever).
What is verified is the combinatorial core — the part where a
construction of this kind fails if it is wrong.

One scope note on the route taken. §5 of the note factors the argument
through Lemma B' (stated for ALL connected bipartite graphs with an
eccentricity-3 centre) and Lemma D (the ISLAND bridge). This file does
not formalize either; it argues directly on G(F). So the THEOREM is
corroborated, but B' in its general form is not — an error there that
happens not to affect G(F) would survive this check.
-/

/-
Design notes (mirroring tools/guarded_reduction.py §2 of the paper):
- Colours are `Bool`; a matching-cut colouring is: both colours used,
  and every vertex has at most one differently-coloured neighbour —
  stated as a uniqueness condition so no Fintype/cardinality machinery
  is needed.
- The vertex type `GVert n m` enumerates the construction's four
  layers verbatim. `BW n m` (base witnesses) is the disjoint sum
  q_i ⊕ w_a ⊕ w_{(C,j)} indexing the guard battery.
- Adjacency is given as a one-directional edge enumeration `edgeTo`
  (exactly the edge list of §2); `SimpleGraph.fromRel` symmetrizes and
  removes any loops.
-/
import Mathlib

set_option autoImplicit false

namespace McRadius3

/-! ## Matching cuts, in colouring form -/

variable {V : Type*}

/-- A matching-cut colouring: both colours are used, and every vertex
has AT MOST ONE neighbour of the opposite colour (stated as: any two
cross-coloured neighbours coincide). This is the standard "edge cut
that is a matching" definition in colouring form. -/
def IsMCColouring (G : SimpleGraph V) (c : V → Bool) : Prop :=
  (∃ v, c v = true) ∧ (∃ v, c v = false) ∧
    ∀ v w₁ w₂, G.Adj v w₁ → G.Adj v w₂ →
      c w₁ ≠ c v → c w₂ ≠ c v → w₁ = w₂

/-- A graph has a matching cut iff some matching-cut colouring exists. -/
def HasMatchingCut (G : SimpleGraph V) : Prop :=
  ∃ c, IsMCColouring G c

/-! ## Signed NOT-1-IN-3-SAT -/

/-- A literal: a variable index and a sign (`true` = positive). -/
abbrev Literal (n : ℕ) := Fin n × Bool

/-- A formula: `m` ordered clauses, each a triple of literals. -/
abbrev Formula (n m : ℕ) := Fin m → Literal n × Literal n × Literal n

/-- A literal is true under `σ` iff the variable's value equals the sign. -/
def evalLit {n : ℕ} (σ : Fin n → Bool) (l : Literal n) : Bool :=
  σ l.1 == l.2

/-- Number of true positions of a clause (multiplicity counted). -/
def trueCount {n : ℕ} (σ : Fin n → Bool)
    (Cl : Literal n × Literal n × Literal n) : ℕ :=
  (cond (evalLit σ Cl.1) 1 0) + (cond (evalLit σ Cl.2.1) 1 0) +
    (cond (evalLit σ Cl.2.2) 1 0)

/-- `σ` satisfies `F` iff no clause has exactly one true position. -/
def Satisfies {n m : ℕ} (σ : Fin n → Bool) (F : Formula n m) : Prop :=
  ∀ C : Fin m, trueCount σ (F C) ≠ 1

/-! ## The guarded construction -/

/-- Base witnesses `BW`: the shared variable witnesses q_i, the anchor
witness w_a, and one proxy witness per clause position. Each indexes
one guard in the battery. -/
abbrev BW (n m : ℕ) := Sum (Fin n) (Sum Unit (Fin m × Fin 3))

/-- Vertices of the guarded graph, by layer (§2 of the paper).
L0: `u`. L1: `q`, `wa`, `wp`, `wprime`, `wT`. L2: `a`, `t`, `f`, `p`,
`guard`, `ballast`. L3: `gate`, `copy`, `clause`, `killer`. -/
inductive GVert (n m : ℕ) : Type
  | u : GVert n m
  | q (i : Fin n) : GVert n m
  | wa : GVert n m
  | wp (C : Fin m) (j : Fin 3) : GVert n m
  | wprime (W : BW n m) : GVert n m
  | wT (which : Bool) (slot : Bool) : GVert n m
  | a : GVert n m
  | t (i : Fin n) : GVert n m
  | f (i : Fin n) : GVert n m
  | p (C : Fin m) (j : Fin 3) : GVert n m
  | guard (W : BW n m) : GVert n m
  | ballast (which : Bool) : GVert n m
  | gate (i : Fin n) : GVert n m
  | copy (C : Fin m) (j : Fin 3) (k : Bool) : GVert n m
  | clause (C : Fin m) : GVert n m
  | killer : GVert n m
  deriving DecidableEq

namespace GVert

variable {n m : ℕ}

/-- The j-th literal of clause C. -/
def litAt (F : Formula n m) (C : Fin m) (j : Fin 3) : Literal n :=
  if j = 0 then (F C).1 else if j = 1 then (F C).2.1 else (F C).2.2

/-- The base literal vertex of clause position (C, j):
`t i` for a positive literal on variable i, `f i` for a negative. -/
def base (F : Formula n m) (C : Fin m) (j : Fin 3) : GVert n m :=
  let l := litAt F C j
  if l.2 then t l.1 else f l.1

/-- One-directional edge enumeration — the §2 edge list verbatim.
`fromRel` below symmetrizes. -/
def edgeTo (F : Formula n m) : GVert n m → GVert n m → Prop
  -- u ~ every L1 vertex
  | u, q _ => True
  | u, wa => True
  | u, wp _ _ => True
  | u, wprime _ => True
  | u, wT _ _ => True
  -- L1–L2
  | q i, t i' => i = i'
  | q i, f i' => i = i'
  | q i, guard W => W = Sum.inl i
  | wa, a => True
  | wa, guard W => W = Sum.inr (Sum.inl ())
  | wp C j, p C' j' => C = C' ∧ j = j'
  | wp C j, guard W => W = Sum.inr (Sum.inr (C, j))
  | wprime W, guard W' => W = W'
  | wT which _slot, ballast which' => which = which'
  -- L2–L3
  | a, gate _ => True
  | t i, gate i' => i = i'
  | f i, gate i' => i = i'
  | v, copy C j _ => v = base F C j ∨ v = p C j
  | p C _j, clause C' => C = C'
  | ballast _, killer => True
  | guard _, killer => True
  | _, _ => False

end GVert

/-- The guarded graph G(F). -/
def guardedGraph {n m : ℕ} (F : Formula n m) : SimpleGraph (GVert n m) :=
  SimpleGraph.fromRel (GVert.edgeTo F)

/-! ## The bipartition (used to state T2 without extra API) -/

/-- `true` for the side {u} ∪ L2, `false` for L1 ∪ L3. -/
def side {n m : ℕ} : GVert n m → Bool
  | GVert.u => true
  | GVert.a => true
  | GVert.t _ => true
  | GVert.f _ => true
  | GVert.p _ _ => true
  | GVert.guard _ => true
  | GVert.ballast _ => true
  | _ => false

/-! ## T2 — helpers

The T2 proofs are elementary case analysis on the edge enumeration, but
two facts are worth isolating because they are the only steps that are
not pure constructor bookkeeping:

* `side_base` — the `copy` row of `edgeTo` names its left endpoint by a
  *value* (`base F C j`) rather than by a constructor pattern, so it is
  the one row where the formula `F` is involved. `base` is always a `t`
  or an `f` vertex, hence always on the `true` side.
* `adj_of_edgeTo` — `fromRel` symmetrizes and drops loops, so one
  direction of the edge list plus distinctness of the endpoints is
  already an edge of `guardedGraph`. Stated once so the fifteen
  adjacency facts below are one-liners.
-/

/-- `base F C j` is `t i` or `f i` (`i` = the literal's variable), so it
lies on the `true` side of the bipartition whatever `F` says. -/
theorem side_base {n m : ℕ} (F : Formula n m) (C : Fin m) (j : Fin 3) :
    side (GVert.base F C j) = true := by
  -- `base` is an `if` on the literal's sign; both branches are `true`-side,
  -- so case on the sign rather than reasoning about which branch is taken.
  cases h : (GVert.litAt F C j).2 <;> simp [GVert.base, h, side]

/-- Every in-neighbour of a `copy` vertex is on the `true` side: the
`copy` row of `edgeTo` admits only `base F C j` and `p C j`. This is the
only case of `guardedGraph_bipartite` that the constructor patterns do
not settle outright. -/
theorem side_of_edgeTo_copy {n m : ℕ} {F : Formula n m} {v : GVert n m}
    {C : Fin m} {j : Fin 3} {k : Bool}
    (h : GVert.edgeTo F v (GVert.copy C j k)) : side v = true := by
  -- `edgeTo F v (copy ..)` only reduces once `v` is a constructor, so case
  -- on `v` to read the `copy` row off the definition; every branch gives
  -- the same disjunction.
  have key : v = GVert.base F C j ∨ v = GVert.p C j := by
    cases v <;> exact h
  rcases key with rfl | rfl
  · exact side_base F C j
  · rfl

/-- The one-directional form of `guardedGraph_bipartite`: every row of
the edge list joins the two sides. -/
theorem edgeTo_side {n m : ℕ} (F : Formula n m) (v w : GVert n m)
    (h : GVert.edgeTo F v w) : side v ≠ side w := by
  cases w
  -- The `copy` column is the only one whose left endpoint is not a
  -- constructor pattern; `side_of_edgeTo_copy` supplies its side.
  case copy C j k =>
    rw [side_of_edgeTo_copy h]
    simp [side]
  -- Every other column: both endpoints are constructors, so `edgeTo`
  -- either reduces to `False` (no such row) or the two sides differ by
  -- computation.
  all_goals (cases v <;> simp_all [side, GVert.edgeTo])

/-- `fromRel` symmetrizes the edge list, so a single direction suffices. -/
theorem adj_of_edgeTo {n m : ℕ} {F : Formula n m} {v w : GVert n m}
    (hne : v ≠ w) (h : GVert.edgeTo F v w) : (guardedGraph F).Adj v w :=
  ⟨hne, Or.inl h⟩

/-! ### The edges used to reach every vertex from the centre

Not the whole edge list — one edge per vertex family, chosen so that
every vertex has a named route back to `u`. (The rows that give a second
route, e.g. `q i ~ guard (inl i)` or `t i ~ gate i`, are not needed here
and are left unstated.) Together these give the explicit walks of
`exists_short_walk_from_u`, which is what both `guardedGraph_connected`
and `guardedGraph_ecc_u_le` consume. -/

section Adjacency

variable {n m : ℕ} (F : Formula n m)

theorem adj_u_q (i : Fin n) : (guardedGraph F).Adj GVert.u (GVert.q i) :=
  adj_of_edgeTo (by simp) trivial

theorem adj_u_wa : (guardedGraph F).Adj GVert.u GVert.wa :=
  adj_of_edgeTo (by simp) trivial

theorem adj_u_wp (C : Fin m) (j : Fin 3) :
    (guardedGraph F).Adj GVert.u (GVert.wp C j) :=
  adj_of_edgeTo (by simp) trivial

theorem adj_u_wprime (W : BW n m) :
    (guardedGraph F).Adj GVert.u (GVert.wprime W) :=
  adj_of_edgeTo (by simp) trivial

theorem adj_u_wT (b s : Bool) :
    (guardedGraph F).Adj GVert.u (GVert.wT b s) :=
  adj_of_edgeTo (by simp) trivial

theorem adj_q_t (i : Fin n) :
    (guardedGraph F).Adj (GVert.q i) (GVert.t i) :=
  adj_of_edgeTo (by simp) rfl

theorem adj_q_f (i : Fin n) :
    (guardedGraph F).Adj (GVert.q i) (GVert.f i) :=
  adj_of_edgeTo (by simp) rfl

theorem adj_wa_a : (guardedGraph F).Adj GVert.wa GVert.a :=
  adj_of_edgeTo (by simp) trivial

theorem adj_wp_p (C : Fin m) (j : Fin 3) :
    (guardedGraph F).Adj (GVert.wp C j) (GVert.p C j) :=
  adj_of_edgeTo (by simp) ⟨rfl, rfl⟩

theorem adj_wprime_guard (W : BW n m) :
    (guardedGraph F).Adj (GVert.wprime W) (GVert.guard W) :=
  adj_of_edgeTo (by simp) rfl

theorem adj_wT_ballast (b s : Bool) :
    (guardedGraph F).Adj (GVert.wT b s) (GVert.ballast b) :=
  adj_of_edgeTo (by simp) rfl

theorem adj_a_gate (i : Fin n) :
    (guardedGraph F).Adj GVert.a (GVert.gate i) :=
  adj_of_edgeTo (by simp) trivial

/-- The right disjunct of the `copy` row: `p C j` is a copy's neighbour
regardless of the literal at `(C, j)`. -/
theorem adj_p_copy (C : Fin m) (j : Fin 3) (k : Bool) :
    (guardedGraph F).Adj (GVert.p C j) (GVert.copy C j k) :=
  adj_of_edgeTo (by simp) (Or.inr rfl)

theorem adj_p_clause (C : Fin m) (j : Fin 3) :
    (guardedGraph F).Adj (GVert.p C j) (GVert.clause C) :=
  adj_of_edgeTo (by simp) rfl

theorem adj_ballast_killer (b : Bool) :
    (guardedGraph F).Adj (GVert.ballast b) GVert.killer :=
  adj_of_edgeTo (by simp) trivial

end Adjacency

/-- Every vertex is joined to the centre `u` by an explicit walk of
length at most 3 — one walk per constructor, following the layer the
vertex lives in (L1 in one step, L2 in two, L3 in three). This single
construction serves both T2 statements below: connectivity needs only
the walk, the eccentricity bound needs only its length. -/
theorem exists_short_walk_from_u {n m : ℕ} (F : Formula n m) (v : GVert n m) :
    ∃ p : (guardedGraph F).Walk GVert.u v, p.length ≤ 3 := by
  cases v with
  | u => exact ⟨.nil, by simp⟩
  -- L1: adjacent to `u` outright.
  | q i => exact ⟨.cons (adj_u_q F i) .nil, by simp⟩
  | wa => exact ⟨.cons (adj_u_wa F) .nil, by simp⟩
  | wp C j => exact ⟨.cons (adj_u_wp F C j) .nil, by simp⟩
  | wprime W => exact ⟨.cons (adj_u_wprime F W) .nil, by simp⟩
  | wT b s => exact ⟨.cons (adj_u_wT F b s) .nil, by simp⟩
  -- L2: via the L1 witness that guards it.
  | a => exact ⟨.cons (adj_u_wa F) (.cons (adj_wa_a F) .nil), by simp⟩
  | t i => exact ⟨.cons (adj_u_q F i) (.cons (adj_q_t F i) .nil), by simp⟩
  | f i => exact ⟨.cons (adj_u_q F i) (.cons (adj_q_f F i) .nil), by simp⟩
  | p C j => exact ⟨.cons (adj_u_wp F C j) (.cons (adj_wp_p F C j) .nil), by simp⟩
  | guard W =>
      exact ⟨.cons (adj_u_wprime F W) (.cons (adj_wprime_guard F W) .nil), by simp⟩
  | ballast b =>
      -- Either slot of the `wT` pair works; take `true`.
      exact ⟨.cons (adj_u_wT F b true) (.cons (adj_wT_ballast F b true) .nil), by simp⟩
  -- L3: via the L2 vertex it hangs off.
  | gate i =>
      exact ⟨.cons (adj_u_wa F) (.cons (adj_wa_a F) (.cons (adj_a_gate F i) .nil)),
        by simp⟩
  | copy C j k =>
      exact ⟨.cons (adj_u_wp F C j) (.cons (adj_wp_p F C j) (.cons (adj_p_copy F C j k) .nil)),
        by simp⟩
  | clause C =>
      -- A clause vertex sees all three of its proxies; position 0 will do.
      exact ⟨.cons (adj_u_wp F C 0) (.cons (adj_wp_p F C 0) (.cons (adj_p_clause F C 0) .nil)),
        by simp⟩
  | killer =>
      exact ⟨.cons (adj_u_wT F true true)
        (.cons (adj_wT_ballast F true true) (.cons (adj_ballast_killer F true) .nil)), by simp⟩

/-! ## T2 — structural statements -/

theorem guardedGraph_bipartite {n m : ℕ} (F : Formula n m) :
    ∀ v w, (guardedGraph F).Adj v w → side v ≠ side w := by
  intro v w hvw
  -- `fromRel` symmetrized the edge list, so the edge is one direction or
  -- the other of `edgeTo`; `edgeTo_side` handles a single direction.
  have h : GVert.edgeTo F v w ∨ GVert.edgeTo F w v := hvw.2
  rcases h with h | h
  · exact edgeTo_side F v w h
  · exact (edgeTo_side F w v h).symm

theorem guardedGraph_connected {n m : ℕ} (F : Formula n m) :
    (guardedGraph F).Connected := by
  -- Connectivity from a hub: `u` reaches everything, so any two vertices
  -- are joined through `u`.
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨GVert.u, fun v => ?_⟩
  obtain ⟨p, -⟩ := exists_short_walk_from_u F v
  exact ⟨p⟩

/-- ecc(u) ≤ 3: every vertex is within distance 3 of the centre. -/
theorem guardedGraph_ecc_u_le {n m : ℕ} (F : Formula n m)
    (v : GVert n m) : (guardedGraph F).dist GVert.u v ≤ 3 := by
  obtain ⟨p, hp⟩ := exists_short_walk_from_u F v
  exact le_trans (SimpleGraph.dist_le p) hp

/-! ### Distance lower bounds

The radius bound needs the opposite of what T2.3 needed: a proof that
some vertex is *far*, i.e. that no short walk exists. Bipartiteness does
the heavy lifting — a common neighbour of `v` and `w` would put `v` and
`w` on the same side — so a witness only has to be non-adjacent and on
the other side of the bipartition, with no case analysis over
intermediate vertices. -/

/-- Two Booleans that each differ from a third are equal. This is the
whole content of "`v` and `w` have no common neighbour": both would have
to sit opposite the neighbour, and `Bool` has only two values. -/
theorem bool_eq_of_ne_ne {a b c : Bool} (h₁ : a ≠ b) (h₂ : b ≠ c) : a = c := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- `base F C j` is literally a `t` or an `f` vertex. Sharper than
`side_base` (which only records the side) and needed where a `base`
vertex has to be told apart from a `ballast`, which shares its side. -/
theorem base_eq_t_or_f {n m : ℕ} (F : Formula n m) (C : Fin m) (j : Fin 3) :
    GVert.base F C j = GVert.t (GVert.litAt F C j).1 ∨
      GVert.base F C j = GVert.f (GVert.litAt F C j).1 := by
  cases h : (GVert.litAt F C j).2 <;> simp [GVert.base, h]

/-- Non-adjacent endpoints on opposite sides of the bipartition are at
distance at least 3. A walk of length ≤ 2 has only three shapes: empty
(same vertex, excluded by the sides differing), one edge (excluded by
non-adjacency), or two edges through a common neighbour (excluded by
bipartiteness). The graph is connected, so a shortest walk exists to
case on. -/
theorem three_le_dist {n m : ℕ} (F : Formula n m) {v w : GVert n m}
    (hadj : ¬ (guardedGraph F).Adj v w) (hside : side v ≠ side w) :
    3 ≤ (guardedGraph F).dist v w := by
  by_contra hlt
  rw [Nat.not_le] at hlt
  obtain ⟨p, hp⟩ := (guardedGraph_connected F).exists_walk_length_eq_dist v w
  cases p with
  | nil => exact hside rfl
  | cons h q =>
    cases q with
    | nil => exact hadj h
    | cons h' q' =>
      cases q' with
      | nil =>
        -- `v ~ x ~ w`: each edge flips the side, so `v` and `w` agree.
        exact hside (bool_eq_of_ne_ne (guardedGraph_bipartite F _ _ h)
          (guardedGraph_bipartite F _ _ h'))
      | cons h'' q'' =>
        -- Three or more edges, contradicting `dist v w < 3`.
        simp only [SimpleGraph.Walk.length_cons] at hp
        omega

/-- Radius exactly 3: no vertex sees the whole graph within distance 2
(together with `guardedGraph_ecc_u_le` this pins the radius at 3). -/
theorem guardedGraph_radius_ge {n m : ℕ} (F : Formula n m)
    (v : GVert n m) : ∃ w, 3 ≤ (guardedGraph F).dist v w := by
  -- One witness per vertex family. Every witness is a vertex that exists
  -- for all `n, m` (`u`, `a`, `wa`, `killer`, `ballast true`,
  -- `wT true true`), so no case is empty-index-sensitive, and each is
  -- chosen on the opposite side of the bipartition from `v`.
  -- `rintro ⟨-, h | h⟩ <;> exact h` is the non-adjacency proof: neither
  -- direction of the edge list has a row for the pair, so both
  -- disjuncts reduce to `False`.
  cases v with
  | u =>
      exact ⟨GVert.killer, three_le_dist F (by rintro ⟨-, h | h⟩ <;> exact h) (by simp [side])⟩
  | q i =>
      exact ⟨GVert.a, three_le_dist F (by rintro ⟨-, h | h⟩ <;> exact h) (by simp [side])⟩
  | wa =>
      exact ⟨GVert.ballast true,
        three_le_dist F (by rintro ⟨-, h | h⟩ <;> exact h) (by simp [side])⟩
  | wp C j =>
      exact ⟨GVert.a, three_le_dist F (by rintro ⟨-, h | h⟩ <;> exact h) (by simp [side])⟩
  | wprime W =>
      exact ⟨GVert.a, three_le_dist F (by rintro ⟨-, h | h⟩ <;> exact h) (by simp [side])⟩
  | wT b s =>
      exact ⟨GVert.a, three_le_dist F (by rintro ⟨-, h | h⟩ <;> exact h) (by simp [side])⟩
  | a =>
      exact ⟨GVert.killer, three_le_dist F (by rintro ⟨-, h | h⟩ <;> exact h) (by simp [side])⟩
  | t i =>
      exact ⟨GVert.killer, three_le_dist F (by rintro ⟨-, h | h⟩ <;> exact h) (by simp [side])⟩
  | f i =>
      exact ⟨GVert.killer, three_le_dist F (by rintro ⟨-, h | h⟩ <;> exact h) (by simp [side])⟩
  | p C j =>
      exact ⟨GVert.killer, three_le_dist F (by rintro ⟨-, h | h⟩ <;> exact h) (by simp [side])⟩
  | guard W =>
      -- Not `a`: it is on the `true` side, same as `guard`, so
      -- `three_le_dist` would not even apply — and rightly so, since
      -- `guard (inr (inl ()))` and `a` share the neighbour `wa`.
      -- `wT true true` is on the other side and adjacent to no guard.
      exact ⟨GVert.wT true true,
        three_le_dist F (by rintro ⟨-, h | h⟩ <;> exact h) (by simp [side])⟩
  | ballast b =>
      exact ⟨GVert.wa, three_le_dist F (by rintro ⟨-, h | h⟩ <;> exact h) (by simp [side])⟩
  | gate i =>
      exact ⟨GVert.ballast true,
        three_le_dist F (by rintro ⟨-, h | h⟩ <;> exact h) (by simp [side])⟩
  | copy C j k =>
      -- The one pair where a direction of the edge list does fire: the
      -- `copy` row asks whether `ballast true` is `base F C j` or
      -- `p C j`, and it is neither.
      refine ⟨GVert.ballast true, three_le_dist F ?_ (by simp [side])⟩
      rintro ⟨-, h | h⟩
      · exact h
      · rcases h with h | h
        · rcases base_eq_t_or_f F C j with hb | hb <;> rw [hb] at h <;> simp at h
        · simp at h
  | clause C =>
      exact ⟨GVert.ballast true,
        three_le_dist F (by rintro ⟨-, h | h⟩ <;> exact h) (by simp [side])⟩
  | killer =>
      exact ⟨GVert.u, three_le_dist F (by rintro ⟨-, h | h⟩ <;> exact h) (by simp [side])⟩

/-! ## T3 — direction 1: a satisfying assignment gives a matching cut

This is §6(⇐) of the note composed with Lemma B'(⇐): the assignment
selects a set `B2` of L2 vertices, blue is `B2` together with the L3
vertices it touches, and every vertex's budget is then checked one
constructor at a time. Rather than count crosses, we name for each
vertex the ONE neighbour that is allowed to differ in colour
(`satCross`) and show any differing neighbour equals it — the budget
condition is stated as uniqueness, so this is exactly what it asks for.
-/

/-- Uniqueness form of the budget: if every vertex has a designated
neighbour that is the only one allowed to differ in colour, the
colouring is a matching-cut colouring. -/
theorem isMC_of_cross {G : SimpleGraph V} (c : V → Bool) (cross : V → V)
    (hb : ∃ v, c v = true) (hr : ∃ v, c v = false)
    (h : ∀ v w, G.Adj v w → c w ≠ c v → w = cross v) : IsMCColouring G c :=
  ⟨hb, hr, fun v w₁ w₂ h₁ h₂ hc₁ hc₂ => (h v w₁ h₁ hc₁).trans (h v w₂ h₂ hc₂).symm⟩

/-- The colouring induced by an assignment; `true` is the note's BLUE.
Blue is exactly `B2 ∪ (N(B2) ∩ L3)`: the anchor, one literal vertex per
variable (`t i` when `σ i` holds, `f i` otherwise), the proxies of true
positions, and the L3 vertices those touch — every gate (the anchor is
blue and sees them all), the copies of true positions, and the clause
vertices with at least one true position. Everything else, `u`
included, is red. -/
def satColour {n m : ℕ} (F : Formula n m) (σ : Fin n → Bool) :
    GVert n m → Bool
  | GVert.a => true
  | GVert.t i => σ i
  | GVert.f i => !σ i
  | GVert.p C j => evalLit σ (GVert.litAt F C j)
  | GVert.gate _ => true
  | GVert.copy C j _ => evalLit σ (GVert.litAt F C j)
  | GVert.clause C =>
      evalLit σ (GVert.litAt F C 0) || evalLit σ (GVert.litAt F C 1) ||
        evalLit σ (GVert.litAt F C 2)
  | _ => false

/-- The one neighbour of each vertex allowed to differ in colour. A
vertex with no differently-coloured neighbour is sent to itself (the
value is then never used). For a clause vertex the cross is its first
false position — under `Satisfies` a touched clause has at most one. -/
def satCross {n m : ℕ} (F : Formula n m) (σ : Fin n → Bool) :
    GVert n m → GVert n m
  | GVert.q i => if σ i then GVert.t i else GVert.f i
  | GVert.wa => GVert.a
  | GVert.wp C j => GVert.p C j
  | GVert.a => GVert.wa
  | GVert.t i => if σ i then GVert.q i else GVert.gate i
  | GVert.f i => if σ i then GVert.gate i else GVert.q i
  | GVert.p C j =>
      if evalLit σ (GVert.litAt F C j) then GVert.wp C j else GVert.clause C
  | GVert.gate i => if σ i then GVert.f i else GVert.t i
  | GVert.clause C =>
      if evalLit σ (GVert.litAt F C 0) then
        (if evalLit σ (GVert.litAt F C 1) then GVert.p C 2 else GVert.p C 1)
      else GVert.p C 0
  | v => v

/-- A base vertex carries its position's truth value as its colour. This
is what makes every copy edge monochromatic: `copy C j k` is coloured by
the same expression. -/
theorem satColour_base {n m : ℕ} (F : Formula n m) (σ : Fin n → Bool)
    (C : Fin m) (j : Fin 3) :
    satColour F σ (GVert.base F C j) = evalLit σ (GVert.litAt F C j) := by
  cases hl : (GVert.litAt F C j).2 <;> cases hs : σ (GVert.litAt F C j).1 <;>
    simp [GVert.base, evalLit, satColour, hl, hs]

/-- Case analysis on a position index, in a form whose `rfl` patterns
substitute the numerals `0, 1, 2` (which `litAt` reduces on). -/
theorem fin3_cases (j : Fin 3) : j = 0 ∨ j = 1 ∨ j = 2 := by revert j; decide

/-! ### The edge rows that are not monochromatic by inspection

One lemma per row of `edgeTo` whose two endpoints can differ in colour.
Each says the same thing: either the endpoints agree, or each is the
other's designated cross. Stating them separately keeps the case bash in
`satEdge_ok` free of index-name bookkeeping. -/

section Rows

variable {n m : ℕ} (F : Formula n m) (σ : Fin n → Bool)

theorem satEdge_q_t (i : Fin n) :
    satColour F σ (GVert.q i) = satColour F σ (GVert.t i) ∨
      (GVert.t i = satCross F σ (GVert.q i) ∧
        GVert.q i = satCross F σ (GVert.t i)) := by
  cases hs : σ i <;> simp [satColour, satCross, hs]

theorem satEdge_q_f (i : Fin n) :
    satColour F σ (GVert.q i) = satColour F σ (GVert.f i) ∨
      (GVert.f i = satCross F σ (GVert.q i) ∧
        GVert.q i = satCross F σ (GVert.f i)) := by
  cases hs : σ i <;> simp [satColour, satCross, hs]

theorem satEdge_wa_a :
    satColour F σ (GVert.wa : GVert n m) = satColour F σ (GVert.a : GVert n m) ∨
      (GVert.a = satCross F σ (GVert.wa : GVert n m) ∧
        GVert.wa = satCross F σ (GVert.a : GVert n m)) := by
  simp [satColour, satCross]

theorem satEdge_wp_p (C : Fin m) (j : Fin 3) :
    satColour F σ (GVert.wp C j) = satColour F σ (GVert.p C j) ∨
      (GVert.p C j = satCross F σ (GVert.wp C j) ∧
        GVert.wp C j = satCross F σ (GVert.p C j)) := by
  cases he : evalLit σ (GVert.litAt F C j) <;> simp [satColour, satCross, he]

theorem satEdge_t_gate (i : Fin n) :
    satColour F σ (GVert.t i) = satColour F σ (GVert.gate i) ∨
      (GVert.gate i = satCross F σ (GVert.t i) ∧
        GVert.t i = satCross F σ (GVert.gate i)) := by
  cases hs : σ i <;> simp [satColour, satCross, hs]

theorem satEdge_f_gate (i : Fin n) :
    satColour F σ (GVert.f i) = satColour F σ (GVert.gate i) ∨
      (GVert.gate i = satCross F σ (GVert.f i) ∧
        GVert.f i = satCross F σ (GVert.gate i)) := by
  cases hs : σ i <;> simp [satColour, satCross, hs]

/-- The only row that uses `Satisfies`. A clause vertex is blue iff some
position is true; its red neighbours are its false positions, and a
touched clause has `3 - t_C ≤ 1` of them because `t_C ≠ 1` forces
`t_C ∈ {2,3}` once `t_C ≥ 1`. -/
theorem satEdge_p_clause (hσ : Satisfies σ F) (C : Fin m) (j : Fin 3) :
    satColour F σ (GVert.p C j) = satColour F σ (GVert.clause C) ∨
      (GVert.clause C = satCross F σ (GVert.p C j) ∧
        GVert.p C j = satCross F σ (GVert.clause C)) := by
  -- `Satisfies` at `C`, restated on the three positions by `litAt`.
  have hs : cond (evalLit σ (GVert.litAt F C 0)) 1 0 +
      cond (evalLit σ (GVert.litAt F C 1)) 1 0 +
      cond (evalLit σ (GVert.litAt F C 2)) 1 0 ≠ 1 := hσ C
  rcases fin3_cases j with rfl | rfl | rfl <;>
    (cases e0 : evalLit σ (GVert.litAt F C 0) <;>
      cases e1 : evalLit σ (GVert.litAt F C 1) <;>
        cases e2 : evalLit σ (GVert.litAt F C 2) <;>
          simp_all [satColour, satCross])

end Rows

/-- Every edge is either monochromatic or a matched pair: each endpoint
is the other's designated cross. Proving the symmetric form here means
`hasMatchingCut_of_satisfies` needs no extra work for the two
orientations `fromRel` produces. -/
theorem satEdge_ok {n m : ℕ} (F : Formula n m) (σ : Fin n → Bool)
    (hσ : Satisfies σ F) (v w : GVert n m) (h : GVert.edgeTo F v w) :
    satColour F σ v = satColour F σ w ∨
      (w = satCross F σ v ∧ v = satCross F σ w) := by
  cases w
  case copy C j k =>
    -- Uniform in `v`: a copy's in-neighbours are `base F C j` and
    -- `p C j`, and both are coloured by the position's truth value —
    -- exactly the copy's own colour. Copy edges are never cut.
    left
    have key : v = GVert.base F C j ∨ v = GVert.p C j := by cases v <;> exact h
    rcases key with rfl | rfl
    · exact satColour_base F σ C j
    · rfl
  case clause C =>
    cases v
    case p C' j =>
      have h' : C' = C := h
      cases h'
      exact satEdge_p_clause F σ hσ _ _
    all_goals exact False.elim h
  case t i' =>
    cases v
    case q i => have h' : i = i' := h; cases h'; exact satEdge_q_t F σ _
    all_goals exact False.elim h
  case f i' =>
    cases v
    case q i => have h' : i = i' := h; cases h'; exact satEdge_q_f F σ _
    all_goals exact False.elim h
  case a =>
    cases v
    case wa => exact satEdge_wa_a F σ
    all_goals exact False.elim h
  case p C' j' =>
    cases v
    case wp C j =>
      obtain ⟨h₁, h₂⟩ : C = C' ∧ j = j' := h
      cases h₁; cases h₂
      exact satEdge_wp_p F σ _ _
    all_goals exact False.elim h
  case gate i' =>
    cases v
    case a => exact Or.inl rfl
    case t i => have h' : i = i' := h; cases h'; exact satEdge_t_gate F σ _
    case f i => have h' : i = i' := h; cases h'; exact satEdge_f_gate F σ _
    all_goals exact False.elim h
  -- The remaining columns have both endpoints red (`u`–L1, the guard and
  -- ballast rows, the killer rows), or no row at all.
  all_goals (cases v <;> first | exact False.elim h | exact Or.inl rfl)

/-- Direction 1 of T3: a satisfying assignment yields a matching cut. -/
theorem hasMatchingCut_of_satisfies {n m : ℕ} (F : Formula n m)
    (σ : Fin n → Bool) (hσ : Satisfies σ F) :
    HasMatchingCut (guardedGraph F) := by
  refine ⟨satColour F σ, isMC_of_cross _ (satCross F σ) ⟨GVert.a, rfl⟩
    ⟨GVert.u, rfl⟩ ?_⟩
  intro v w hadj hne
  -- `fromRel` gives the edge in one orientation or the other; the
  -- symmetric statement of `satEdge_ok` covers both.
  rcases hadj.2 with h | h
  · rcases satEdge_ok F σ hσ v w h with hc | ⟨h₁, -⟩
    · exact absurd hc.symm hne
    · exact h₁
  · rcases satEdge_ok F σ hσ w v h with hc | ⟨-, h₂⟩
    · exact absurd hc hne
    · exact h₂

/-! ## T3 — direction 2: a matching cut gives a satisfying assignment

This is §4–§6(⇒) of the note. The work is in ruling out the colourings
that have nothing to do with satisfiability: after normalizing `u` to
red (colour swap), the guard battery forces every L1 vertex red
(Claim 4.4, case B), and every L3 vertex having two neighbours rules out
a blue set confined to L3 (Claim 4.2, case A0). Only then does the
assignment read off.
-/

/-- Swapping the two colours preserves the matching-cut property — the
definition is colour-symmetric. This is what licenses "WLOG `u` is
red". -/
theorem IsMCColouring.compl {G : SimpleGraph V} {c : V → Bool}
    (h : IsMCColouring G c) : IsMCColouring G (fun v => !c v) := by
  obtain ⟨⟨v, hv⟩, ⟨w, hw⟩, huniq⟩ := h
  exact ⟨⟨w, by simp [hw]⟩, ⟨v, by simp [hv]⟩, fun v w₁ w₂ h₁ h₂ hc₁ hc₂ =>
    huniq v w₁ w₂ h₁ h₂ (fun e => hc₁ (congrArg Bool.not e))
      (fun e => hc₂ (congrArg Bool.not e))⟩

/-- Budget, freezing form: two distinct neighbours sharing a colour force
`v` to that colour. If `v` disagreed with both it would carry two
crosses. This is Claim 4.3 of the note, stated for any two neighbours
rather than for L1-witnesses specifically. -/
theorem IsMCColouring.freeze {G : SimpleGraph V} {c : V → Bool}
    (h : IsMCColouring G c) {v w₁ w₂ : V} (h₁ : G.Adj v w₁) (h₂ : G.Adj v w₂)
    (hne : w₁ ≠ w₂) (hcw : c w₁ = c w₂) : c v = c w₁ := by
  by_contra hcv
  exact hne (h.2.2 v w₁ w₂ h₁ h₂ (fun e => hcv e.symm)
    (fun e => hcv (hcw.trans e).symm))

/-- Budget, spending form: once one neighbour differs in colour, every
other neighbour agrees with `v`. -/
theorem IsMCColouring.other {G : SimpleGraph V} {c : V → Bool}
    (h : IsMCColouring G c) {v w₁ w₂ : V} (h₁ : G.Adj v w₁) (h₂ : G.Adj v w₂)
    (hne : w₁ ≠ w₂) (hc₁ : c w₁ ≠ c v) : c w₂ = c v := by
  by_contra hc₂
  exact hne (h.2.2 v w₁ w₂ h₁ h₂ hc₁ hc₂)

/-- WLOG `u` is red: a matching cut can always be presented with the
centre red. -/
theorem exists_mc_u_red {n m : ℕ} (F : Formula n m)
    (h : HasMatchingCut (guardedGraph F)) :
    ∃ c, IsMCColouring (guardedGraph F) c ∧ c GVert.u = false := by
  obtain ⟨c, hc⟩ := h
  cases hu : c GVert.u
  · exact ⟨c, hc, hu⟩
  · exact ⟨fun v => !c v, hc.compl, by simp [hu]⟩

/-! ### More of the edge list

T2 needed only one route from each vertex back to `u`; §4 argues about
the guard battery, so it needs the rows T2 left unstated. -/

section MoreAdjacency

variable {n m : ℕ} (F : Formula n m)

theorem adj_q_guard (i : Fin n) :
    (guardedGraph F).Adj (GVert.q i) (GVert.guard (Sum.inl i)) :=
  adj_of_edgeTo (by simp) rfl

theorem adj_wa_guard :
    (guardedGraph F).Adj GVert.wa (GVert.guard (Sum.inr (Sum.inl ()))) :=
  adj_of_edgeTo (by simp) rfl

theorem adj_wp_guard (C : Fin m) (j : Fin 3) :
    (guardedGraph F).Adj (GVert.wp C j) (GVert.guard (Sum.inr (Sum.inr (C, j)))) :=
  adj_of_edgeTo (by simp) rfl

theorem adj_guard_killer (W : BW n m) :
    (guardedGraph F).Adj (GVert.guard W) GVert.killer :=
  adj_of_edgeTo (by simp) trivial

theorem adj_t_gate (i : Fin n) :
    (guardedGraph F).Adj (GVert.t i) (GVert.gate i) :=
  adj_of_edgeTo (by simp) rfl

theorem adj_f_gate (i : Fin n) :
    (guardedGraph F).Adj (GVert.f i) (GVert.gate i) :=
  adj_of_edgeTo (by simp) rfl

/-- The left disjunct of the `copy` row. -/
theorem adj_base_copy (C : Fin m) (j : Fin 3) (k : Bool) :
    (guardedGraph F).Adj (GVert.base F C j) (GVert.copy C j k) := by
  -- `edgeTo` only reduces once its left endpoint is a constructor, and
  -- `base` is a stuck `if`; resolve it into `t`/`f` first.
  rcases base_eq_t_or_f F C j with h | h <;> rw [h] <;>
    exact adj_of_edgeTo (by simp) (Or.inl h.symm)

/-- `u` is not adjacent to a copy: the `copy` row would make it a base or
a proxy vertex. Needed because the copy row is the one place where a
non-adjacency is not immediate from the constructors. -/
theorem base_ne_p (C : Fin m) (j : Fin 3) (C' : Fin m) (j' : Fin 3) :
    GVert.base F C j ≠ GVert.p C' j' := by
  rcases base_eq_t_or_f F C j with h | h <;> rw [h] <;> simp

/-- The witness of a base vertex is the `q` of its literal's variable,
whichever sign the literal has. -/
theorem adj_q_base (C : Fin m) (j : Fin 3) :
    (guardedGraph F).Adj (GVert.q (GVert.litAt F C j).1) (GVert.base F C j) := by
  rcases base_eq_t_or_f F C j with h | h <;> rw [h]
  · exact adj_q_t F _
  · exact adj_q_f F _

theorem not_adj_u_copy (C : Fin m) (j : Fin 3) (k : Bool) :
    ¬ (guardedGraph F).Adj GVert.u (GVert.copy C j k) := by
  rintro ⟨-, h | h⟩
  · rcases h with h | h
    · rcases base_eq_t_or_f F C j with hb | hb <;> rw [hb] at h <;> simp at h
    · simp at h
  · exact h

end MoreAdjacency

/-- The L1 witness a guard shares with the vertex it guards: `q i`, `wa`
or `wp C j` according to `W`. Together with `wprime W` these are the
guard's two witnesses, which is what makes guards freeze. -/
def baseWitness {n m : ℕ} : BW n m → GVert n m
  | Sum.inl i => GVert.q i
  | Sum.inr (Sum.inl ()) => GVert.wa
  | Sum.inr (Sum.inr (C, j)) => GVert.wp C j

section GuardBattery

variable {n m : ℕ} (F : Formula n m)

theorem adj_baseWitness_guard (W : BW n m) :
    (guardedGraph F).Adj (baseWitness W) (GVert.guard W) := by
  rcases W with i | W'
  · exact adj_q_guard F i
  · rcases W' with ⟨⟩ | ⟨C, j⟩
    · exact adj_wa_guard F
    · exact adj_wp_guard F C j

theorem adj_u_baseWitness (W : BW n m) :
    (guardedGraph F).Adj GVert.u (baseWitness W) := by
  rcases W with i | W'
  · exact adj_u_q F i
  · rcases W' with ⟨⟩ | ⟨C, j⟩
    · exact adj_u_wa F
    · exact adj_u_wp F C j

theorem baseWitness_ne_wprime (W : BW n m) :
    baseWitness W ≠ (GVert.wprime W : GVert n m) := by
  rcases W with i | W'
  · simp [baseWitness]
  · rcases W' with ⟨⟩ | ⟨C, j⟩ <;> simp [baseWitness]

theorem baseWitness_ne_killer (W : BW n m) :
    baseWitness W ≠ (GVert.killer : GVert n m) := by
  rcases W with i | W'
  · simp [baseWitness]
  · rcases W' with ⟨⟩ | ⟨C, j⟩ <;> simp [baseWitness]

/-- A base witness is never a `wprime`, for ANY index — the case-B
branch on `wprime W` needs the two vertices distinguished without
knowing that the indices agree. -/
theorem baseWitness_ne_wprime' (W W' : BW n m) :
    baseWitness W ≠ (GVert.wprime W' : GVert n m) := by
  rcases W with i | W''
  · simp [baseWitness]
  · rcases W'' with ⟨⟩ | ⟨C, j⟩ <;> simp [baseWitness]

variable {F} {c : GVert n m → Bool} (hc : IsMCColouring (guardedGraph F) c)

include hc

/-- A ballast with two red witnesses is red (Claim 4.3). -/
theorem ballast_red (b : Bool) (h₁ : c (GVert.wT b true) = false)
    (h₂ : c (GVert.wT b false) = false) : c (GVert.ballast b) = false := by
  have := hc.freeze (adj_wT_ballast F b true).symm (adj_wT_ballast F b false).symm
    (by simp) (h₁.trans h₂.symm)
  simpa [h₁] using this

/-- A guard with two red witnesses is red (Claim 4.3). -/
theorem guard_red (W : BW n m) (h₁ : c (baseWitness W) = false)
    (h₂ : c (GVert.wprime W) = false) : c (GVert.guard W) = false := by
  have := hc.freeze (adj_baseWitness_guard F W).symm (adj_wprime_guard F W).symm
    (baseWitness_ne_wprime W) (h₁.trans h₂.symm)
  simpa [h₁] using this

/-- The killer cannot be blue while both ballasts are red: they are two
distinct red neighbours. -/
theorem killer_not_blue (h₁ : c (GVert.ballast true) = false)
    (h₂ : c (GVert.ballast false) = false)
    (hk : c (GVert.killer : GVert n m) = true) : False := by
  have := hc.2.2 GVert.killer (GVert.ballast true) (GVert.ballast false)
    (adj_ballast_killer F true).symm (adj_ballast_killer F false).symm
    (by simp [h₁, hk]) (by simp [h₂, hk])
  simp at this

/-- The same contradiction with one ballast and one guard — the shape
needed when the blue witness is itself a ballast witness. -/
theorem killer_not_blue' (b : Bool) (W : BW n m)
    (h₁ : c (GVert.ballast b) = false) (h₂ : c (GVert.guard W) = false)
    (hk : c (GVert.killer : GVert n m) = true) : False := by
  have := hc.2.2 GVert.killer (GVert.ballast b) (GVert.guard W)
    (adj_ballast_killer F b).symm (adj_guard_killer F W).symm
    (by simp [h₁, hk]) (by simp [h₂, hk])
  simp at this

end GuardBattery

/-- Claim 4.4: with `u` red, no neighbour of `u` is blue — case B is
impossible. Every branch runs the same way. The blue witness `b` has
already spent its budget on the cross to `u`, so the guard (or ballast)
next to it is forced blue; that vertex's *other* witness is red, which
spends its budget, so the killer is forced blue; but the killer then
sees two red neighbours, which is one too many. -/
theorem l1_red {n m : ℕ} {F : Formula n m} {c : GVert n m → Bool}
    (hc : IsMCColouring (guardedGraph F) c) (hu : c GVert.u = false)
    (x : GVert n m) (hx : (guardedGraph F).Adj GVert.u x) : c x = false := by
  by_contra hblue
  have hxt : c x = true := by cases h : c x <;> simp_all
  -- Claim 4.1: `x` is the only blue neighbour of `u`.
  have hred : ∀ y, (guardedGraph F).Adj GVert.u y → y ≠ x → c y = false := by
    intro y hy hne
    have := hc.other hx hy (Ne.symm hne) (by simp [hxt, hu])
    simpa [hu] using this
  -- `x`'s cross to `u` is spent, so all its other neighbours are blue.
  have hbl : ∀ y, (guardedGraph F).Adj x y → y ≠ GVert.u → c y = true := by
    intro y hy hne
    have := hc.other hx.symm hy (Ne.symm hne) (by simp [hxt, hu])
    simpa [hxt] using this
  -- The two ballast witnesses of `b` are red unless `x` is one of them.
  have hballast : ∀ b : Bool, (∀ s : Bool, GVert.wT b s ≠ x) →
      c (GVert.ballast b) = false := fun b h =>
    ballast_red hc b (hred _ (adj_u_wT F b true) (h true))
      (hred _ (adj_u_wT F b false) (h false))
  cases x
  case q i =>
    -- `G_{q_i}` is blue; its second witness `w'` is red; killer blue.
    have hg : c (GVert.guard (Sum.inl i)) = true :=
      hbl _ (adj_q_guard F i) (by simp)
    have hw : c (GVert.wprime (Sum.inl i)) = false :=
      hred _ (adj_u_wprime F (Sum.inl i)) (by simp)
    have hk : c (GVert.killer : GVert n m) = true := by
      have := hc.other (adj_wprime_guard F (Sum.inl i)).symm
        (adj_guard_killer F (Sum.inl i)) (by simp) (by simp [hw, hg])
      simpa [hg] using this
    exact killer_not_blue hc (hballast true (by simp)) (hballast false (by simp)) hk
  case wa =>
    have hg : c (GVert.guard (Sum.inr (Sum.inl ())) : GVert n m) = true :=
      hbl _ (adj_wa_guard F) (by simp)
    have hw : c (GVert.wprime (Sum.inr (Sum.inl ())) : GVert n m) = false :=
      hred _ (adj_u_wprime F (Sum.inr (Sum.inl ()))) (by simp)
    have hk : c (GVert.killer : GVert n m) = true := by
      have := hc.other (adj_wprime_guard F (Sum.inr (Sum.inl ()))).symm
        (adj_guard_killer F (Sum.inr (Sum.inl ()))) (by simp) (by simp [hw, hg])
      simpa [hg] using this
    exact killer_not_blue hc (hballast true (by simp)) (hballast false (by simp)) hk
  case wp C j =>
    have hg : c (GVert.guard (Sum.inr (Sum.inr (C, j)))) = true :=
      hbl _ (adj_wp_guard F C j) (by simp)
    have hw : c (GVert.wprime (Sum.inr (Sum.inr (C, j))) : GVert n m) = false :=
      hred _ (adj_u_wprime F (Sum.inr (Sum.inr (C, j)))) (by simp)
    have hk : c (GVert.killer : GVert n m) = true := by
      have := hc.other (adj_wprime_guard F (Sum.inr (Sum.inr (C, j)))).symm
        (adj_guard_killer F (Sum.inr (Sum.inr (C, j)))) (by simp) (by simp [hw, hg])
      simpa [hg] using this
    exact killer_not_blue hc (hballast true (by simp)) (hballast false (by simp)) hk
  case wprime W =>
    -- Here the blue witness is the guard's SECOND witness; the base
    -- witness plays the role of the red one.
    have hg : c (GVert.guard W) = true := hbl _ (adj_wprime_guard F W) (by simp)
    have hw : c (baseWitness W) = false :=
      hred _ (adj_u_baseWitness F W) (baseWitness_ne_wprime' W W)
    have hk : c (GVert.killer : GVert n m) = true := by
      have := hc.other (adj_baseWitness_guard F W).symm (adj_guard_killer F W)
        (baseWitness_ne_killer W) (by simp [hw, hg])
      simpa [hg] using this
    exact killer_not_blue hc (hballast true (by simp)) (hballast false (by simp)) hk
  case wT b s =>
    -- The ballast is blue; its other slot is red and spends its budget.
    have hbb : c (GVert.ballast b) = true := hbl _ (adj_wT_ballast F b s) (by simp)
    have hs : c (GVert.wT b (!s)) = false := by
      refine hred _ (adj_u_wT F b (!s)) ?_
      cases s <;> simp
    have hk : c (GVert.killer : GVert n m) = true := by
      have := hc.other (adj_wT_ballast F b (!s)).symm (adj_ballast_killer F b)
        (by simp) (by simp [hs, hbb])
      simpa [hbb] using this
    -- The OTHER ballast and any guard are still red: every one of their
    -- witnesses differs from `x`, so Claim 4.3 applies to both.
    refine killer_not_blue' hc (!b) (Sum.inr (Sum.inl ())) ?_ ?_ hk
    · exact hballast (!b) (by cases b <;> simp)
    · exact guard_red hc _ (hred _ (adj_u_wa F) (by simp [baseWitness]))
        (hred _ (adj_u_wprime F _) (by simp))
  -- A copy is the one non-L1 vertex whose non-adjacency to `u` is not
  -- immediate from the constructors — the `copy` row admits any left
  -- endpoint, so it has to be refuted through `base`.
  case copy C j k => exact absurd hx (not_adj_u_copy F C j k)
  -- Every other vertex is not adjacent to `u` at all.
  all_goals exact absurd hx (by rintro ⟨-, h | h⟩ <;> exact h)

/-! ### Reading the assignment off a colouring

With every L1 vertex red (`l1_red`), the rest of §4–§6(⇒) is a chain of
budget arguments: guards, ballasts and the killer are frozen red, so a
blue vertex must be in the literal/proxy machinery; that forces the
anchor blue; the anchor forces every gate blue, which selects exactly
one literal vertex per variable; and the clause budget is then the
`t_C ≠ 1` condition. -/

section Extraction

variable {n m : ℕ} {F : Formula n m} {c : GVert n m → Bool}
  (hc : IsMCColouring (guardedGraph F) c) (hu : c GVert.u = false)

include hc

/-- An L2 vertex that is blue has already spent its budget on its red L1
witness, so every other neighbour — in particular every L3 neighbour —
is blue too. This is the workhorse of §5's (⇒) direction. -/
theorem l3_blue_of_l2_blue (hu : c GVert.u = false) {v wit z : GVert n m}
    (hwit : (guardedGraph F).Adj GVert.u wit) (hvw : (guardedGraph F).Adj v wit)
    (hvz : (guardedGraph F).Adj v z) (hne : wit ≠ z) (hv : c v = true) :
    c z = true := by
  have hred : c wit = false := l1_red hc hu _ hwit
  have := hc.other hvw hvz hne (by simp [hred, hv])
  simpa [hv] using this

/-- Both literal vertices of a variable cannot be blue: they share the
witness `q i`, which would carry two crosses. Condition (α). -/
theorem not_both_blue (hu : c GVert.u = false) (i : Fin n)
    (h₁ : c (GVert.t i) = true) (h₂ : c (GVert.f i) = true) : False := by
  have hq : c (GVert.q i) = false := l1_red hc hu _ (adj_u_q F i)
  have := hc.2.2 (GVert.q i) (GVert.t i) (GVert.f i) (adj_q_t F i) (adj_q_f F i)
    (by simp [h₁, hq]) (by simp [h₂, hq])
  simp at this

theorem guard_isRed (hu : c GVert.u = false) (W : BW n m) :
    c (GVert.guard W) = false :=
  guard_red hc W (l1_red hc hu _ (adj_u_baseWitness F W))
    (l1_red hc hu _ (adj_u_wprime F W))

theorem ballast_isRed (hu : c GVert.u = false) (b : Bool) :
    c (GVert.ballast b) = false :=
  ballast_red hc b (l1_red hc hu _ (adj_u_wT F b true))
    (l1_red hc hu _ (adj_u_wT F b false))

/-- The killer is red: both ballasts are, and they are two distinct
neighbours. (With `l1_red` this is what kills case A0 for the killer.) -/
theorem killer_isRed (hu : c GVert.u = false) :
    c (GVert.killer : GVert n m) = false := by
  have h₁ := ballast_isRed hc hu true
  have h₂ := ballast_isRed hc hu false
  have := hc.freeze (adj_ballast_killer F true).symm
    (adj_ballast_killer F false).symm (by simp) (h₁.trans h₂.symm)
  simpa [h₁] using this

/-- §6(⇒) step 1: a selected proxy forces its base selected. The proxy
touches both copies of its position; a red base would then have two blue
neighbours. -/
theorem base_blue_of_p_blue (hu : c GVert.u = false) (C : Fin m) (j : Fin 3)
    (hp : c (GVert.p C j) = true) : c (GVert.base F C j) = true := by
  have h₀ : c (GVert.copy C j false) = true :=
    l3_blue_of_l2_blue hc hu (adj_u_wp F C j) (adj_wp_p F C j).symm
      (adj_p_copy F C j false) (by simp) hp
  have h₁ : c (GVert.copy C j true) = true :=
    l3_blue_of_l2_blue hc hu (adj_u_wp F C j) (adj_wp_p F C j).symm
      (adj_p_copy F C j true) (by simp) hp
  cases hb : c (GVert.base F C j)
  · have := hc.2.2 (GVert.base F C j) (GVert.copy C j false) (GVert.copy C j true)
      (adj_base_copy F C j false) (adj_base_copy F C j true)
      (by simp [h₀, hb]) (by simp [h₁, hb])
    simp at this
  · rfl

/-- §6(⇒) step 5: a selected base forces its proxies selected — the same
argument with the roles of base and proxy exchanged. -/
theorem p_blue_of_base_blue (hu : c GVert.u = false) (C : Fin m) (j : Fin 3)
    (hb : c (GVert.base F C j) = true) : c (GVert.p C j) = true := by
  have h₀ : c (GVert.copy C j false) = true :=
    l3_blue_of_l2_blue hc hu (adj_u_q F _) (adj_q_base F C j).symm
      (adj_base_copy F C j false) (by simp) hb
  have h₁ : c (GVert.copy C j true) = true :=
    l3_blue_of_l2_blue hc hu (adj_u_q F _) (adj_q_base F C j).symm
      (adj_base_copy F C j true) (by simp) hb
  cases hp : c (GVert.p C j)
  · have := hc.2.2 (GVert.p C j) (GVert.copy C j false) (GVert.copy C j true)
      (adj_p_copy F C j false) (adj_p_copy F C j true)
      (by simp [h₀, hp]) (by simp [h₁, hp])
    simp at this
  · rfl

theorem p_eq_base (hu : c GVert.u = false) (C : Fin m) (j : Fin 3) :
    c (GVert.p C j) = c (GVert.base F C j) := by
  cases hp : c (GVert.p C j) <;> cases hb : c (GVert.base F C j)
  · rfl
  · have := p_blue_of_base_blue hc hu C j hb; simp [hp] at this
  · have := base_blue_of_p_blue hc hu C j hp; simp [hb] at this
  · rfl

/-- §6(⇒) step 2: a selected literal vertex forces the anchor selected.
Its gate is blue, and the gate's other two neighbours cannot both be
red. -/
theorem a_blue_of_t_blue (hu : c GVert.u = false) (i : Fin n)
    (h : c (GVert.t i) = true) : c (GVert.a : GVert n m) = true := by
  have hgate : c (GVert.gate i) = true :=
    l3_blue_of_l2_blue hc hu (adj_u_q F i) (adj_q_t F i).symm (adj_t_gate F i)
      (by simp) h
  have hf : c (GVert.f i) = false := by
    cases hh : c (GVert.f i)
    · rfl
    · exact (not_both_blue hc hu i h hh).elim
  cases ha : c (GVert.a : GVert n m)
  · have := hc.freeze (adj_a_gate F i).symm (adj_f_gate F i).symm (by simp)
      (ha.trans hf.symm)
    simp [hgate, ha] at this
  · rfl

theorem a_blue_of_f_blue (hu : c GVert.u = false) (i : Fin n)
    (h : c (GVert.f i) = true) : c (GVert.a : GVert n m) = true := by
  have hgate : c (GVert.gate i) = true :=
    l3_blue_of_l2_blue hc hu (adj_u_q F i) (adj_q_f F i).symm (adj_f_gate F i)
      (by simp) h
  have ht : c (GVert.t i) = false := by
    cases hh : c (GVert.t i)
    · rfl
    · exact (not_both_blue hc hu i hh h).elim
  cases ha : c (GVert.a : GVert n m)
  · have := hc.freeze (adj_a_gate F i).symm (adj_t_gate F i).symm (by simp)
      (ha.trans ht.symm)
    simp [hgate, ha] at this
  · rfl

theorem a_blue_of_base_blue (hu : c GVert.u = false) (C : Fin m) (j : Fin 3)
    (hb : c (GVert.base F C j) = true) : c (GVert.a : GVert n m) = true := by
  rcases base_eq_t_or_f F C j with h | h <;> rw [h] at hb
  · exact a_blue_of_t_blue hc hu _ hb
  · exact a_blue_of_f_blue hc hu _ hb

/-- §6(⇒) step 3 together with Claim 4.2: the anchor is blue. Some
vertex is blue; guards, ballasts and the killer are frozen red, and
every remaining shape leads back to the anchor. This is where case A0
dies — a blue set confined to L3 cannot survive the L3 degrees. -/
theorem a_blue (hu : c GVert.u = false) : c (GVert.a : GVert n m) = true := by
  obtain ⟨v, hv⟩ := hc.1
  cases v
  case a => exact hv
  case t i => exact a_blue_of_t_blue hc hu i hv
  case f i => exact a_blue_of_f_blue hc hu i hv
  case p C j => exact a_blue_of_base_blue hc hu C j (base_blue_of_p_blue hc hu C j hv)
  case gate i =>
    -- A blue gate needs two blue neighbours among `a, t i, f i`, and the
    -- two literal vertices cannot both be blue.
    cases ha : c (GVert.a : GVert n m)
    · cases ht : c (GVert.t i)
      · have := hc.freeze (adj_a_gate F i).symm (adj_t_gate F i).symm (by simp)
          (ha.trans ht.symm)
        simp [hv, ha] at this
      · have := a_blue_of_t_blue hc hu i ht
        simp [ha] at this
    · rfl
  case copy C j k =>
    -- A blue copy needs its base or its proxy blue.
    cases hb : c (GVert.base F C j)
    · cases hp : c (GVert.p C j)
      · have := hc.freeze (adj_base_copy F C j k).symm (adj_p_copy F C j k).symm
          (base_ne_p F C j C j) (hb.trans hp.symm)
        simp [hv, hb] at this
      · exact a_blue_of_base_blue hc hu C j (base_blue_of_p_blue hc hu C j hp)
    · exact a_blue_of_base_blue hc hu C j hb
  case clause C =>
    -- A blue clause vertex needs at least two blue proxies; one is
    -- enough for us.
    cases h₀ : c (GVert.p C 0)
    · cases h₁ : c (GVert.p C 1)
      · have := hc.freeze (adj_p_clause F C 0).symm (adj_p_clause F C 1).symm
          (by simp) (h₀.trans h₁.symm)
        simp [hv, h₀] at this
      · exact a_blue_of_base_blue hc hu C 1 (base_blue_of_p_blue hc hu C 1 h₁)
    · exact a_blue_of_base_blue hc hu C 0 (base_blue_of_p_blue hc hu C 0 h₀)
  -- `u`, L1, the guards, the ballasts and the killer are all red.
  case u => simp [hu] at hv
  case q i => simp [l1_red hc hu _ (adj_u_q F i)] at hv
  case wa => simp [l1_red hc hu _ (adj_u_wa F)] at hv
  case wp C j => simp [l1_red hc hu _ (adj_u_wp F C j)] at hv
  case wprime W => simp [l1_red hc hu _ (adj_u_wprime F W)] at hv
  case wT b s => simp [l1_red hc hu _ (adj_u_wT F b s)] at hv
  case guard W => simp [guard_isRed hc hu W] at hv
  case ballast b => simp [ballast_isRed hc hu b] at hv
  case killer => simp [killer_isRed hc hu] at hv

/-- §6(⇒) step 4: with the anchor blue every gate is blue, so exactly
one of each variable's two literal vertices is blue. -/
theorem literal_blue (hu : c GVert.u = false)
    (ha : c (GVert.a : GVert n m) = true) (i : Fin n) :
    c (GVert.f i) = !c (GVert.t i) := by
  have hgate : c (GVert.gate i) = true :=
    l3_blue_of_l2_blue hc hu (adj_u_wa F) (adj_wa_a F).symm (adj_a_gate F i)
      (by simp) ha
  cases ht : c (GVert.t i) <;> cases hf : c (GVert.f i)
  · have := hc.freeze (adj_t_gate F i).symm (adj_f_gate F i).symm (by simp)
      (ht.trans hf.symm)
    simp [hgate, ht] at this
  · simp
  · simp
  · exact (not_both_blue hc hu i ht hf).elim

/-- The colour of a base vertex IS the truth value of its literal under
the extracted assignment — the step that turns colours into semantics. -/
theorem base_colour (hu : c GVert.u = false)
    (ha : c (GVert.a : GVert n m) = true) (C : Fin m) (j : Fin 3) :
    c (GVert.base F C j) =
      evalLit (fun i => c (GVert.t i)) (GVert.litAt F C j) := by
  have hlit := literal_blue hc hu ha (GVert.litAt F C j).1
  cases hl : (GVert.litAt F C j).2 <;>
    cases hct : c (GVert.t (GVert.litAt F C j).1) <;>
      simp_all [GVert.base, evalLit]

theorem p_colour (hu : c GVert.u = false) (ha : c (GVert.a : GVert n m) = true)
    (C : Fin m) (j : Fin 3) :
    c (GVert.p C j) = evalLit (fun i => c (GVert.t i)) (GVert.litAt F C j) :=
  (p_eq_base hc hu C j).trans (base_colour hc hu ha C j)

theorem clause_blue_of (hu : c GVert.u = false) (C : Fin m) (j : Fin 3)
    (h : c (GVert.p C j) = true) : c (GVert.clause C) = true :=
  l3_blue_of_l2_blue hc hu (adj_u_wp F C j) (adj_wp_p F C j).symm
    (adj_p_clause F C j) (by simp) h

theorem clause_red_of (C : Fin m) (j₁ j₂ : Fin 3) (hne : j₁ ≠ j₂)
    (h₁ : c (GVert.p C j₁) = false) (h₂ : c (GVert.p C j₂) = false) :
    c (GVert.clause C) = false := by
  have := hc.freeze (adj_p_clause F C j₁).symm (adj_p_clause F C j₂).symm
    (by simp [hne]) (h₁.trans h₂.symm)
  simpa [h₁] using this

/-- A clause vertex with exactly one blue proxy is impossible: the blue
proxy forces it blue, and the two red proxies then freeze it red. This
is the budget that makes `t_C ≠ 1`. -/
theorem not_exactly_one (hu : c GVert.u = false) (C : Fin m) (j₀ j₁ j₂ : Fin 3)
    (hne : j₁ ≠ j₂) (hb : c (GVert.p C j₀) = true)
    (h₁ : c (GVert.p C j₁) = false) (h₂ : c (GVert.p C j₂) = false) : False := by
  have hblue := clause_blue_of hc hu C j₀ hb
  have hred := clause_red_of hc C j₁ j₂ hne h₁ h₂
  simp [hblue] at hred

/-- §6(⇒) step 6: every clause has a true count other than 1. -/
theorem clause_ok (hu : c GVert.u = false) (ha : c (GVert.a : GVert n m) = true)
    (C : Fin m) : trueCount (fun i => c (GVert.t i)) (F C) ≠ 1 := by
  intro hcount
  have h₀ := p_colour hc hu ha C 0
  have h₁ := p_colour hc hu ha C 1
  have h₂ := p_colour hc hu ha C 2
  have hc' : cond (evalLit (fun i => c (GVert.t i)) (GVert.litAt F C 0)) 1 0 +
      cond (evalLit (fun i => c (GVert.t i)) (GVert.litAt F C 1)) 1 0 +
      cond (evalLit (fun i => c (GVert.t i)) (GVert.litAt F C 2)) 1 0 = 1 := hcount
  rw [← h₀, ← h₁, ← h₂] at hc'
  cases e₀ : c (GVert.p C 0) <;> cases e₁ : c (GVert.p C 1) <;>
    cases e₂ : c (GVert.p C 2)
  · simp [e₀, e₁, e₂] at hc'
  · exact not_exactly_one hc hu C 2 0 1 (by decide) e₂ e₀ e₁
  · exact not_exactly_one hc hu C 1 0 2 (by decide) e₁ e₀ e₂
  · simp [e₀, e₁, e₂] at hc'
  · exact not_exactly_one hc hu C 0 1 2 (by decide) e₀ e₁ e₂
  · simp [e₀, e₁, e₂] at hc'
  · simp [e₀, e₁, e₂] at hc'
  · simp [e₀, e₁, e₂] at hc'

end Extraction

/-- Direction 2 of T3: a matching cut yields a satisfying assignment. -/
theorem satisfies_of_hasMatchingCut {n m : ℕ} (F : Formula n m)
    (h : HasMatchingCut (guardedGraph F)) : ∃ σ, Satisfies σ F := by
  obtain ⟨c, hc, hu⟩ := exists_mc_u_red F h
  exact ⟨fun i => c (GVert.t i), fun C => clause_ok hc hu (a_blue hc hu) C⟩

/-! ## T3 — the equivalence -/

/-- The combinatorial core of the theorem: F is satisfiable iff the
guarded graph has a matching cut. (The polynomial-time bookkeeping is
not formalized; the reduction is visibly size-linear.) -/
theorem satisfiable_iff_hasMatchingCut {n m : ℕ} (F : Formula n m) :
    (∃ σ, Satisfies σ F) ↔ HasMatchingCut (guardedGraph F) :=
  ⟨fun ⟨σ, hσ⟩ => hasMatchingCut_of_satisfies F σ hσ,
    satisfies_of_hasMatchingCut F⟩

/-! ## Non-vacuousness witness

A kernel-checked iff would be worthless if both sides were always true.
The instance below is unsatisfiable (clause 1 forces the variable
false, clause 2 forces it true), so the equivalence transports the
`decide`-level unsatisfiability proof into a proof that its guarded
graph has NO matching cut. Together with any satisfiable instance, the
equivalence is exercised in both truth directions. Added by the head
session after reproducing the check independently. -/

/-- Clauses (x1, ¬x1, ¬x1) and (¬x1, x1, x1): jointly unsatisfiable. -/
def unsatWitnessF : Formula 1 2 := fun C =>
  if C = 0 then ((0, true), ((0, false), (0, false)))
  else ((0, false), ((0, true), (0, true)))

theorem unsatWitnessF_unsat : ¬ ∃ σ, Satisfies σ unsatWitnessF := by
  unfold Satisfies trueCount evalLit unsatWitnessF
  decide

/-- The guarded graph of an unsatisfiable formula provably has no
matching cut — the equivalence does real work on NO-instances. -/
theorem unsatWitnessF_noMatchingCut :
    ¬ HasMatchingCut (guardedGraph unsatWitnessF) := fun h =>
  unsatWitnessF_unsat ((satisfiable_iff_hasMatchingCut unsatWitnessF).mpr h)

end McRadius3
