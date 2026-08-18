/-
McRadius3: statement-first skeleton for Phase 10.

Formalization target (plan.md Phase 10): the combinatorial core of
scratch/mc-radius3-theorem.md —
  T1  the guarded construction G(F) as a SimpleGraph;
  T2  structural lemmas (bipartite, connected, radius exactly 3);
  T3  the equivalence: G(F) has a matching cut ↔ F is satisfiable.

This file is the STATEMENT commit: all definitions elaborate, every
theorem is `sorry`. The kernel is the referee; nothing here is
evidence until the sorries are gone.

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

/-! ## T2 — structural statements -/

theorem guardedGraph_bipartite {n m : ℕ} (F : Formula n m) :
    ∀ v w, (guardedGraph F).Adj v w → side v ≠ side w := by
  sorry

theorem guardedGraph_connected {n m : ℕ} (F : Formula n m) :
    (guardedGraph F).Connected := by
  sorry

/-- ecc(u) ≤ 3: every vertex is within distance 3 of the centre. -/
theorem guardedGraph_ecc_u_le {n m : ℕ} (F : Formula n m)
    (v : GVert n m) : (guardedGraph F).dist GVert.u v ≤ 3 := by
  sorry

/-- Radius exactly 3: no vertex sees the whole graph within distance 2
(together with `guardedGraph_ecc_u_le` this pins the radius at 3). -/
theorem guardedGraph_radius_ge {n m : ℕ} (F : Formula n m)
    (v : GVert n m) : ∃ w, 3 ≤ (guardedGraph F).dist v w := by
  sorry

/-! ## T3 — the equivalence -/

/-- The combinatorial core of the theorem: F is satisfiable iff the
guarded graph has a matching cut. (The polynomial-time bookkeeping is
not formalized; the reduction is visibly size-linear.) -/
theorem satisfiable_iff_hasMatchingCut {n m : ℕ} (F : Formula n m) :
    (∃ σ, Satisfies σ F) ↔ HasMatchingCut (guardedGraph F) := by
  sorry

end McRadius3
