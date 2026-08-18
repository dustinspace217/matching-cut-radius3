/-
McRadius3: statement-first skeleton for Phase 10.

Formalization target (plan.md Phase 10): the combinatorial core of
scratch/mc-radius3-theorem.md —
  T1  the guarded construction G(F) as a SimpleGraph;
  T2  structural lemmas (bipartite, connected, radius exactly 3);
  T3  the equivalence: G(F) has a matching cut ↔ F is satisfiable.

Status: all four T2 statements (bipartite, connected, ecc(u) ≤ 3, radius
≥ 3) are proved and kernel-checked — `#print axioms` on each shows only
propext / Classical.choice / Quot.sound, no `sorryAx`. T3
(`satisfiable_iff_hasMatchingCut`) is still `sorry`, and it is the whole
mathematical content of the reduction; T2 is scaffolding. The kernel is
the referee; a statement is not evidence until its own sorry is gone.

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

/-! ## T3 — the equivalence -/

/-- The combinatorial core of the theorem: F is satisfiable iff the
guarded graph has a matching cut. (The polynomial-time bookkeeping is
not formalized; the reduction is visibly size-linear.) -/
theorem satisfiable_iff_hasMatchingCut {n m : ℕ} (F : Formula n m) :
    (∃ σ, Satisfies σ F) ↔ HasMatchingCut (guardedGraph F) := by
  sorry

end McRadius3
